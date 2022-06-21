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

  let k_induction bound = Solver.(
    let mk_direct_simulations i =
      match direct_simulation_opt with
      | Some sim ->
        List.map Util.(0--i) ~f:(fun j ->
          reindex i pre_vars sim
          |> reindex j post_vars
          |> Boolean.mk_not ctxt)
      | None -> [] in
    let solver = mk_simple_solver ctxt in
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
        add solver (mk_direct_simulations i);
        match check solver [init; pred] with
        | SATISFIABLE -> sprintf "Reaching run of length: %d" i
        | _  ->
          match check solver (pred :: neg_preds) with
          | UNSATISFIABLE -> sprintf "Invariant of diameter: %d" i
          | _ -> loop (i + 1) (Boolean.mk_not ctxt pred :: neg_preds)
    in
    let invar = reindex 0 invar_vars invar in
    let pred = reindex 0 pre_vars pred in
    add solver [invar];
    match check solver [init; pred] with
    |  SATISFIABLE -> "Initial states satisfy predicate"
    | _ -> loop 1 [Boolean.mk_not ctxt pred]
  )

end