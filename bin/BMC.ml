open Base
open Printf
open Z3
open Z3_More
open Expr

module type System = sig
  (* A set of state variables and a predicate over them. *)
  val init: expr list * expr
  val pred: expr list * expr
  val invar: expr list * expr
  (* Three sets of of state variables and a predicate over them:
  - Pre
  - Auxiliary
  - Post
  *)
  val trans: expr list * expr list * expr list * expr
  val direct_simulation_opt: expr option
  val enlarge_cex: (expr * expr option) list -> expr
end

module BMC (System: System) (Context: Context) = struct
  let pre_vars = fst System.init
  let init = snd System.init
  let pred = snd System.pred
  let invar = snd System.invar
  let _, aux_vars, post_vars, trans = System.trans
  let direct_simulation_opt = System.direct_simulation_opt

  let ctxt = Context.context

  let index_var_of index expr =
    let err () = raise (Invalid_argument
      (sprintf "Can only reindex variable constant, not %s" (to_string expr))) in
    if not (is_const expr) then err () else
    let func_decl = get_func_decl expr in
    let symbol = FuncDecl.get_name func_decl
    and typ = FuncDecl.get_range func_decl in
    let name = Symbol.get_string symbol in
    let stripped = String.rstrip ~drop:(Char.equal '\'') name in (* XXX Hacky *)
    let index_name = stripped ^ "__" ^ (Int.to_string index) in
    mk_const_s ctxt index_name typ

  let reindex index vars expr =
    let reindexed = List.map vars ~f:(index_var_of index) in
    substitute expr vars reindexed

  let next_vars = aux_vars @ post_vars
  let invar_vars = aux_vars @ pre_vars

  let bmc bound = Solver.(
    let solver = mk_simple_solver ctxt in
    let rec loop i =
      if i > bound then
        "Bound exceeded"
      else
        let invar = reindex i invar_vars invar in
        let pred = reindex i pre_vars pred in
        let trans = reindex i next_vars trans |> reindex (i - 1) pre_vars in
        add solver [trans; invar];
        (* Caml.Format.printf "Pred %d: %a@." i pp_expr pred;
        Stdio.print_endline (to_string solver |> normalize_z3_sexps); *)
        match check solver [pred] with
        | SATISFIABLE -> sprintf "Reaching run of length: %d" i
        | _  -> loop (i + 1)
    in
    let init = reindex 0 invar_vars init in
    let invar = reindex 0 invar_vars invar in
    let pred = reindex 0 pre_vars pred in
    add solver [init; invar];
    (* Caml.Format.printf "Pred: %a@." pp_expr pred;
    Stdio.print_endline (to_string solver |> normalize_z3_sexps); *)
    match check solver [pred] with
    |  SATISFIABLE -> "Initial states satisfy predicate"
    | _ -> loop 1
  )

  let pp_opt pp_value ppf = function
  | None -> Caml.Format.fprintf ppf "none"
  | Some x -> pp_value ppf x

  let project_index_vars model index vars =
    let expr_of e = Model.eval model e true in
    List.map vars ~f:(fun e -> e, expr_of (index_var_of index e))

  let project_model model bound =
    let project i =
      Util.apply3 (pre_vars, aux_vars, post_vars)
        ~f:(project_index_vars model i)
    in
    List.map Util.(0--(bound+1)) ~f:project

  let print_projected interpretations =
    let open Caml.Format in
    let ppf = Caml.Format.std_formatter in
    let pp_interp_pair (e, interp) =
      fprintf ppf "@[%a:@ %a@]@ " pp_expr e (pp_print_option pp_expr) interp
    in
    let pp_interp_pairs description pairs =
      printf "@[%s:@ @[<v>" description;
      List.iter pairs ~f:pp_interp_pair;
      printf "@]@]\n@,";
    in
    let init, auxs, _ = List.hd_exn interpretations in
    pp_interp_pairs "Init" (init @ auxs);
    List.iteri (List.tl_exn interpretations) ~f:(fun i (_, auxs, posts) ->
      printf "@,@[@[Step:@ %d@]\n\n@," (i + 1);
      printf "@[Aux:@ @[<v>";
      List.iter auxs ~f:pp_interp_pair;
      printf "@]@]\n@,";
      printf "@[Post:@ @[<v>";
      List.iter posts ~f:pp_interp_pair;
      printf "@]@]";
      printf "@]@."
    )

  let k_induction bound =
    let open Solver in
    let printf = Caml.Format.printf in
    let mk_direct_simulations i =
      match direct_simulation_opt with
      | Some sim ->
        List.map Util.(0--i) ~f:(fun j ->
          reindex i pre_vars sim
          |> reindex j post_vars
          |> Boolean.mk_not ctxt)
      | None -> [] in
    let _mk_direct_simulations _i = [Boolean.mk_true ctxt] in
    let solver = mk_simple_solver ctxt in
    let print_model i = match get_model solver with
      | None -> printf "Failed to retrieve model"
      | Some model ->
        project_model model i |> print_projected
    in
    let init = reindex 0 invar_vars init in
    let rec loop i neg_preds =
      if i > bound then
        "Bound exceeded"
      else
        let invar = reindex i invar_vars invar in
        let pred = reindex i pre_vars pred in
        let trans = reindex i next_vars trans |> reindex (i - 1) pre_vars in
        add solver [trans; invar];
        (* Caml.Format.printf "Pred %d: %a@." i pp_expr pred;
        Stdio.print_endline (to_string solver |> normalize_z3_sexps); *)
        (* printf "New simulations: %a@."
          pp_expr_comma_list (mk_direct_simulations i); *)
        add solver (mk_direct_simulations i);
        match check solver [init; pred] with
        | SATISFIABLE ->
          printf "Model:\n@.";
          print_model i;
          sprintf "Reaching run of length: %d" i;
        | _  ->
          match check solver (pred :: neg_preds) with
          | UNSATISFIABLE -> sprintf "Invariant of diameter: %d" i
          | _ ->
            printf "k-CTI for k = %d:\n@." i;
            print_model i;
            loop (i + 1) (Boolean.mk_not ctxt pred :: neg_preds)
    in
    let invar = reindex 0 invar_vars invar in
    let pred = reindex 0 pre_vars pred in
    printf "@[Simulation:@ %a@]@." (pp_opt pp_expr) direct_simulation_opt;
    add solver [invar];
    match check solver [init; pred] with
    |  SATISFIABLE -> "Initial states satisfy predicate"
    | _ -> loop 1 [Boolean.mk_not ctxt pred]

let dest_conj e =
  if not (Boolean.is_and e) then
    raise (Invalid_argument
      (Caml.Format.asprintf "Not a conjunction: %a" pp_expr e))
  else
    get_args e

let is_sat = function
| Solver.SATISFIABLE -> true
| UNSATISFIABLE -> false
| _ -> raise (Invalid_argument "Unexpected solver status")

let k_ind ~enlarge_cex k frame0 phi =
  let open Caml.Format in
  let open Boolean in
  let open Solver in
  let solver = mk_simple_solver ctxt in
  let _generalize _frame c = mk_not ctxt c in
  let extract_predecessor model _s =
    let model = Option.value_exn model in
    let extracted_pre_vars = project_index_vars model 0 pre_vars in
    enlarge_cex extracted_pre_vars
  in
  let init = reindex 0 invar_vars init in
  let invar = reindex 0 invar_vars invar in
  let trans = reindex 1 next_vars trans |> reindex 0 pre_vars in
  (* consumes a vanilla conjunction, returns a non-indexed cube *)
  let generalize frame s =
    let open Boolean in
    let cube = simplify s None |> dest_conj |> List.map ~f:(mk_not ctxt) in
    (* let cube = simplify s None |> dest_conj in *)
    let gen_test c =
      let c0 = reindex 0 pre_vars c in
      let c1 = reindex 1 pre_vars c in
      (* printf "Try gen: %a@." pp_expr (mk_not ctxt c0 |> fun s -> simplify s None);
      printf "Init: %a@." pp_expr init; *)
      not (is_sat (check solver [frame; trans; c0; mk_not ctxt c1])
        || is_sat (check solver [init; mk_not ctxt c0]))
      (* is_sat (check solver [init; mk_not ctxt c0]) *)
    in
    let rec loop acc = function
      | [] -> mk_or ctxt (List.rev acc)
      | clause :: rest ->
        if gen_test (mk_or ctxt (acc @ rest)) then begin
          printf "@[Dropped clause:@ %a@]@." pp_expr clause;
          loop acc rest
        end
        else
          loop (clause :: acc) rest
    in
    loop [] cube
  in
  let rec loop frame g q =
    match q with
    | [] ->
      printf "@[Blocked. g:@ %a@ frame:@ %a@]@." pp_expr g pp_expr frame;
      `Blocked g
    | (s, f) :: q ->
      printf "@[\n\nf:%d@ s: %a@]@." f pp_expr s;
      if f = 0 then
        begin match check solver [init; invar; reindex 0 pre_vars s] with
        | SATISFIABLE   -> `Counterexample k
        | UNSATISFIABLE -> `KCTI k
        | _ -> raise (Invalid_argument "Unexpected solver status")
        end
      else
        let frame = mk_and ctxt [frame; mk_not ctxt (reindex 0 pre_vars s)] in
        let s' = reindex 1 pre_vars s in
        begin match check solver [frame; trans; s'] with
        | SATISFIABLE ->
          let model = get_model solver in
          let t = extract_predecessor model s in
          let () = assert (
            check solver [mk_not ctxt frame; reindex 0 pre_vars t]
            |> is_sat |> not) in
          printf "@[Extracted cex: %a@]@." pp_expr t;
          loop frame g ((t, f - 1) :: (s, f) :: q)
        | UNSATISFIABLE ->
          let c = generalize frame s in
          let frame = mk_and ctxt [frame; reindex 0 pre_vars c] in
          let g = mk_and ctxt [g; c] in
          printf "@[Cube blocked:@ %a@ Generalize:@ %a@]@." pp_expr s pp_expr c;
          loop frame g q
        | _ -> raise (Invalid_argument "Unexpected solver status")
        end
  in
  printf "\n\nk-ind for k=%d@." k;
  loop (mk_and ctxt [frame0; invar]) phi [mk_not ctxt phi, k]

let is_0_invariant phi =
  let pred0 = Boolean.mk_not ctxt phi |> reindex 0 pre_vars in
  let invar0 = reindex 0 invar_vars invar in
  let init0 = reindex 0 invar_vars init in
  let open Solver in
  let solver = mk_simple_solver ctxt in
  check solver [init0; invar0; pred0] |> is_sat |> not

let check_invariant phi =
  let pred0 = reindex 0 pre_vars pred in
  let invar0 = reindex 0 invar_vars invar in
  let invar1 = reindex 1 invar_vars invar in
  let trans01 = reindex 1 next_vars trans |> reindex 0 pre_vars in
  let phi0 = reindex 0 pre_vars phi in
  let phi1 = reindex 1 pre_vars phi in
  let open Solver in
  let solver = mk_simple_solver ctxt in
  if not (is_0_invariant phi) then
    "Base case violated"
  else if check solver [pred0; phi0] |> is_sat then
    "Invariant includes bad states"
  else if
    check solver [phi0; invar0; trans01; invar1; Boolean.mk_not ctxt phi1]
    |> is_sat
  then
    "Invariant is not invariant"
  else
    "Invariant is inductive"

let k_induction_wo_unrolling bound =
  (* 0 invariant *)
  let phi = Boolean.mk_not ctxt pred in
  let rec loop k =
    if k > bound then
      "Bound exceeded"
    else match k_ind ~enlarge_cex:System.enlarge_cex k phi phi with
    | `Counterexample k -> sprintf "Reaching run of length: %d" k;
    | `Blocked g ->
      Caml.Format.printf "Result of invariant check: %s@." (check_invariant g);
      sprintf "Invariant of diameter: %d" k
    | `KCTI _ ->
      loop (k + 1)
  in
  if not (is_0_invariant phi) then
    "Initial states satisfy predicate"
  else
    loop 0

end