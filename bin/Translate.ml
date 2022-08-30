open Base
open Printf
open Z3
open Expr
open Symta
open Z3_More
open JANI

(** Convert JANI timed automata models to SMT formulae.
  
  The backend used for the SMT formulae is Z3's OCaml interface.

  The translation proceeds modularly per automaton.

  A final step generates a single system fom the formulae representing
  the individual automata and the synchronization constraints.

  The translation fuses an action step followed by a delay step into a single
  transition relation.
*)

let printf = Caml.Format.printf

module type Model = sig
  val model: model
end


exception Invalid_Model of string

let invalid_expr_exn msg e =
  Invalid_Model (sprintf "%s: %s"
    msg
    (yojson_of_expression e |> Yojson.Safe.to_string)
  )

let invalid_exn msg s =
  Invalid_Model (sprintf "%s: %s" msg s)

(** This module provides convencience functions for constructing formulae. *)
module ContextUtils (Context: Context) = struct
let ctxt = Context.context

let int_sort = Arithmetic.Integer.mk_sort ctxt

let real_sort = Arithmetic.Real.mk_sort ctxt

let bool_sort = Boolean.mk_sort ctxt

let string_sort = Seq.mk_string_sort ctxt

let mk_int n = mk_numeral_int ctxt n int_sort
and mk_string x = Seq.mk_string ctxt x
and mk_float x = x |> Float.to_string |> Arithmetic.Real.mk_numeral_s ctxt
and mk_bool b = if b then Boolean.mk_true ctxt else Boolean.mk_false ctxt

end

(*** We use an internal type universe for the translation,
   since we want to use more than what is provided by JANI.

   The module also provides a number of derivied functionalities, notably for
   translating model expressions.
*)
type typ =
  Bounded of bounded_type
| Bool
| Clock
| String

type variable_declaration = {
  name : identifier;
  typ : typ;
  initial_value : expression option
}

let discrete_var_names_of =  List.filter_map ~f:(
  fun ({name; typ; _}: variable_declaration) ->
  match typ with
  | Clock -> None
  | _ -> Some name
)

let cast_typ = function
| TBounded x -> Bounded x
| TClock -> Clock
| TBool -> Bool

let cast_var_decl ({
  name;
  typ;
  initial_value;
  _
}: Symta.JANI.variable_declaration) =
{
  name;
  typ = cast_typ typ;
  initial_value;
}

(** Environments are a central to the translation.
  They keep track of the currently known model variables and allow to translate
  these to Z3 constants.
  *)
module Environment (Context: Context) (Vars: (
  sig val variable_declarations: variable_declaration list end
)) = struct

open ContextUtils (Context)

let sort_of_typ = function
| Bounded _ -> int_sort
| Clock -> real_sort
| Bool -> bool_sort
| String -> string_sort

let var_of_variable ({
  name;
  typ;
  _
}: variable_declaration) =
  mk_const_s ctxt name (sort_of_typ typ)

let next_name_of name = name ^ "'" 

let next_of_variable ({
  name;
  typ;
  _
}: variable_declaration) =
  mk_const_s ctxt (next_name_of name) (sort_of_typ typ)

let variable_declaration ({
  name;
  _
} as decl: variable_declaration) =
  name, var_of_variable decl

open Vars

let var_tab =
  Map.of_alist_exn (module String)
    (List.map variable_declarations ~f:variable_declaration)

let next_tab =
  Map.of_alist_exn (module String) (
    List.map variable_declarations
      ~f:(fun decl -> decl.name, next_of_variable decl)
  )

let var_typ_tab =
  Map.of_alist_exn (module String) (
    List.map variable_declarations
      ~f:(fun decl -> decl.name, decl.typ)
  )

let var_of_name x = match Map.find var_tab x with
| Some e -> e
| None -> raise (invalid_exn "Undeclared variable" x)

let next_of_name x = match Map.find next_tab x with
| Some e -> e
| None -> raise (invalid_exn "Undeclared variable" x)

let typ_of_name x = match Map.find var_typ_tab x with
| Some t -> t
| None -> raise (invalid_exn "Undeclared variable" x)

let expression ?(renamings=None) =
  let rec expression ~var_of_name = function
| Var x -> var_of_name x
| Const c -> (
  match c with
  | Real r -> mk_float r
  | Int i -> mk_int i
  | Bool b -> mk_bool b
)
| Unary {op; exp} -> let exp = expression ~var_of_name exp in
  begin match op with
  | "¬" -> Boolean.mk_not ctxt exp
  | op -> raise (invalid_exn "Unsupported operator" op)
  end
| Binary {op; left; right} ->
  let l, r = expression ~var_of_name left, expression~var_of_name  right in
  let open Arithmetic in
  let open Boolean in
  begin match op with
  | "*" -> mk_mul ctxt [l; r]
  | "+" -> mk_add ctxt [l; r]
  | "-" -> mk_sub ctxt [l; r]
  | "/" -> mk_div ctxt l r
  | "=" -> mk_eq ctxt l r
  | "<" -> mk_lt ctxt l r
  | "≤" -> mk_le ctxt l r
  | ">" -> mk_gt ctxt l r
  | "≥" -> mk_ge ctxt l r
  | "∧" -> mk_and ctxt [l; r]
  | "∨" -> mk_or ctxt [l; r]
  | _ -> raise (invalid_exn "Unsupported operator" op)
  end
| Local {name; exp} as e -> match renamings with
  | None -> raise (invalid_expr_exn "Property expression is not allowed here" e)
  | Some r -> let var_of_name = r name in
    expression ~var_of_name exp
in expression ~var_of_name
(* | e -> raise (invalid_expr_exn "Unsupported expression" e) *)

let unchanged_of_name var_name =
  Boolean.mk_eq ctxt (next_of_name var_name) (var_of_name var_name)

let only_change var_set changed = Util.(
  printf "[%a] - [%a]@."
    pp_string_comma_list var_set pp_string_comma_list changed;
  Boolean.mk_and ctxt (
    List.filter_map ~f:(fun x ->
      if List.mem ~equal:String.equal changed x then
        None
      else
        Some (unchanged_of_name x)
    ) var_set
  )
)

let delta_var_name = "delta"
let delta_var = mk_const_s ctxt delta_var_name real_sort

let init_of_var_decl {name; initial_value; typ; _} =
  let initial_value =
    match typ with
    | Clock -> delta_var
    | _ -> Option.value initial_value ~default:(Const (Int 0)) |> expression
  in
  Boolean.mk_eq ctxt (var_of_name name) initial_value

let discrete_var_names = discrete_var_names_of variable_declarations

let discrete_unchanged =
  List.map discrete_var_names ~f:unchanged_of_name |> Boolean.mk_and ctxt

end

(** This module contains the implementation of the main translation procedure.

  Preconditions:
  - The automata names in `elements` are a subset of the ones in `automata`.
*)
module Formula (Context: Context) (Model: Model) = struct

open ContextUtils (Context)
let model = Model.model


(* Given `[["x", e1; "z", e2], ["y", e3; "x", e4]]`,
   return ["x", e1 ∧ e4; "y", e3; "z", e2]
*)
let merge_reset_pairs pairs =
  let sorted =
    List.sort
      ~compare:(fun x y -> String.compare (fst x) (fst y))
      (List.concat pairs) in
  let rec merge last acc = function
  | [] -> [last, Boolean.mk_or ctxt acc]
  | (x, cond) :: xs -> if String.equal x last then
      merge x (cond :: (List.rev acc)) xs
    else
      (last, Boolean.mk_or ctxt (List.rev acc)) :: merge x [cond] xs
  in match sorted with
  | [] -> []
  | (x, cond) :: xs -> merge x [cond] xs

let select_var_name = "select"
let select_var = mk_const_s ctxt select_var_name int_sort
let sync_var_name = "sync"
let sync_var = mk_const_s ctxt sync_var_name string_sort
let pc_var_name = "pc"
let pc'_var_name = pc_var_name ^ "'"
let pc_var = mk_const_s ctxt pc_var_name string_sort
let pc'_var = mk_const_s ctxt pc'_var_name string_sort
let rename name x = name ^ "_" ^ x
let renamed_select_var name =
  mk_const_s ctxt (rename name select_var_name) int_sort
let renamed_sync_var name =
  mk_const_s ctxt (rename name sync_var_name) string_sort
let renamed_pc_var name =
  mk_const_s ctxt (rename name pc_var_name) string_sort
let renamed_pc'_var name =
  mk_const_s ctxt (rename name pc'_var_name) string_sort

let epsilon_snyc = mk_string "Eps" (* XXX Make this reserved keyword *)
let no_sync = mk_string "None"

let input_enabled_map =
  let elements = model.system.elements in
  let iteri ~f = List.iter elements
    ~f:(fun {automaton; input_enable; _} -> f ~key:automaton ~data:input_enable)
  in match Map.of_iteri (module String) ~iteri with
  | `Ok m -> m
  | `Duplicate_key k -> raise
    (invalid_exn "Automaton is duplicate in composition" k)

let is_input_enabled automaton_name action_name =
  let input_enabled = Map.find_multi input_enabled_map automaton_name in
  List.mem ~equal:String.equal input_enabled action_name

let mk_weak s = mk_string (s ^ "?")
let mk_strong s = mk_string (s ^ "!")

let sync_val_of_action automaton_name action = (match action with
| None -> epsilon_snyc
| Some s -> if is_input_enabled automaton_name s then
    mk_weak s
  else
    mk_strong s
)

let model_variables = List.map model.variables ~f:cast_var_decl

let var_set_global = discrete_var_names_of model_variables

let _ = if not (List.is_empty var_set_global) then raise (
  Invalid_Model "Global variables are not supported"
)

(** Procedure for translating a single automaton. *)
module Automaton (Automaton:(
  sig val automaton: automaton end
)) = struct

open Automaton

let automaton_variables = List.map automaton.variables ~f:cast_var_decl

let variable_declarations = model_variables @ automaton_variables

open Environment (Context: Context)
  (struct let variable_declarations = variable_declarations end)

let invar_location pc ({
  name;
  time_progress;
  _
}: location) = Boolean.(
  mk_implies ctxt
    (mk_eq ctxt pc (mk_string name))
    (expression time_progress.exp)
)

(** Generating the invariant predicate of the automaton.

  TODO:
  - Force automata within valid locations and variables within valid bounds
*)
let invar_automaton pc ({
  name;
  locations;
  _
}: automaton) = Boolean.(
  name,
  mk_and ctxt (List.map ~f:(invar_location pc) locations)
)

let invar_loc_in_bounds =
  let open Boolean in
  mk_or ctxt (List.map automaton.locations ~f:(
    fun location -> mk_eq ctxt pc_var (mk_string location.name)
  ))

let invalid_edge_exn msg e =
  Invalid_Model (sprintf "%s: %s"
    msg
    (yojson_of_edge e |> Yojson.Safe.to_string)
  )

let assignment ({
  ref;
  value;
  _
}: assignment) =
  Boolean.mk_eq ctxt (next_of_name ref) (expression value)

let is_reset ({
  ref;
  value;
  _
}: assignment) = (
  match typ_of_name ref with
    | Clock ->
      if Poly.(value = Const (Int 0)) then
        true
      else
        raise (Invalid_Model (sprintf "Reset value must be 0: %s = %s"
          ref
          (yojson_of_expression value |> Yojson.Safe.to_string)))
    | _ -> false
)

let edge var_set automaton_name edge_id pc pc' select sync ({
  location;
  action;
  guard;
  destinations;
  _
} as edge) =
  let destination = (match destinations with
    | [destination] -> destination
    | _ -> raise (invalid_edge_exn "Only one destination allowed" edge)
    )
  in let guard = expression guard.exp
  and loc_eq = Boolean.mk_eq ctxt pc (mk_string location)
  and sync_val = sync_val_of_action automaton_name action
  and edge_id = mk_int edge_id
  and resets, updates = List.partition_tf destination.assignments ~f:is_reset
  in let assignments = List.map ~f:assignment updates
  and assigned_vars = List.map ~f:(fun a -> a.ref) updates
  and reset_vars = List.map ~f:(fun a -> a.ref) resets
  in let assign =
    Boolean.mk_and ctxt (only_change var_set assigned_vars :: assignments)
  and loc'_eq = Boolean.mk_eq ctxt pc' (mk_string destination.location)
  (* XXX Is this subsumed by the global sync conds? *)
  and sync_cond = Boolean.mk_eq ctxt sync sync_val
  and select_cond = Boolean.mk_eq ctxt select edge_id
  in let enable = Boolean.(
    mk_implies ctxt
      select_cond
      (mk_and ctxt [loc_eq; sync_cond; guard])
  )
  and effect = Boolean.(
    mk_implies ctxt
      select_cond
      (mk_and ctxt [assign; loc'_eq])
  )
  and reset_pairs = List.map reset_vars ~f:(fun x -> (x, select_cond))
  in enable, effect, reset_pairs

let automaton_name = automaton.name

(** Generating the transition relation of the automaton.

  TODO:
  - weak synchronization ((\/ enabled i) --> (\/ select = i))
*)
let trans_automaton () = Boolean.(
  let edges = automaton.edges in
  let select_is i = mk_eq ctxt select_var (mk_int i)
  and var_set_local = discrete_var_names_of automaton_variables
  in let var_set = var_set_global @ var_set_local
  and eps_edges, strong_syncs, weak_syncs = Util.partition3_mapi edges ~f:(
    fun i edge ->
      match edge.action with
      | None -> `Fst i
      | Some name ->
        if is_input_enabled automaton_name name then
          `Trd (name, i)
        else
          `Snd (name, i)
  )
  and _: unit = printf "Computing edges@."
  in let enablers, effects, reset_pairs =
    List.mapi edges ~f:(
      fun i -> edge var_set automaton_name i pc_var pc'_var select_var sync_var
    )
    |> List.unzip3
  and _: unit = printf "Computed edges@."
  and select_eps = mk_implies ctxt
    (mk_eq ctxt sync_var epsilon_snyc)
    (mk_or ctxt (
      List.map eps_edges ~f:select_is))
  and _: unit = printf "Computing epsilon conditions@."
  and strong_by_name = Map.of_alist_multi (module String) strong_syncs
  and _: unit = printf "Computing strong sync conditions@."
  in let select_strong = mk_and ctxt (
    Map.fold strong_by_name ~init:[] ~f:(fun ~key ~data acc ->
      mk_implies ctxt
        (mk_eq ctxt sync_var (mk_strong key))
        (mk_or ctxt (List.map data ~f:select_is)) :: acc
    )
  )
  and sync_valid = mk_or ctxt (
    List.map ~f:(mk_eq ctxt sync_var)
      (epsilon_snyc :: no_sync ::
       List.map ~f:(fun x -> mk_strong (fst x)) strong_syncs @
       List.map ~f:(fun x -> mk_weak   (fst x)) weak_syncs
      )
  )
  and no_effect = mk_implies ctxt
    (mk_eq ctxt select_var (mk_int (-1)))
    (mk_and ctxt [only_change var_set []; mk_eq ctxt pc'_var pc_var])
  and select_none = mk_implies ctxt
      (mk_eq ctxt sync_var no_sync)
      (select_is (-1))
  and merged_reset_pairs = merge_reset_pairs reset_pairs
  in mk_and ctxt [
    mk_and ctxt enablers;
    mk_and ctxt (no_effect :: effects);
    select_strong;
    select_eps;
    select_none;
    sync_valid
  ], merged_reset_pairs)

(** Generating the initial state predicate of the automaton. *)
let init_automaton () =
  let pc_init =
    List.map automaton.initial_locations
      ~f:(fun s -> Boolean.mk_eq ctxt pc_var (mk_string s))
    |> Boolean.mk_or ctxt in
  pc_init :: List.map ~f:init_of_var_decl variable_declarations
  |> Boolean.mk_and ctxt

let local_var_decls_renamed =
  List.map automaton.variables ~f:(fun decl ->
    {(cast_var_decl decl) with name = rename automaton.name decl.name})

let pc_var_renamed_unchanged = Boolean.mk_eq ctxt
  (renamed_pc_var automaton.name) (renamed_pc'_var automaton.name) 

let var_set_local = discrete_var_names_of automaton_variables

(** We prodcue a renaming for each automaton from its local variables to
  globally unique names.

  This renaming will be used when building the final system.
*)
let var_renaming_of_automaton ({name; _}: automaton) =
  let local_renaming_pre = List.map var_set_local ~f:(
    fun x ->
      var_of_name x,
      mk_const_s ctxt (rename name x) (sort_of_typ (typ_of_name x))
  )
  and local_renaming_post = List.map var_set_local ~f:(
    fun x ->
      next_of_name x,
      mk_const_s ctxt
        (next_name_of x |> rename name)
        (sort_of_typ (typ_of_name x))
  )
  and static_renaming_pre = List.map ~f:(fun (e, f) -> e, f name)
    [pc_var, renamed_pc_var]
  and static_renaming_post = List.map ~f:(fun (e, f) -> e, f name)
    [pc'_var, renamed_pc'_var;
     select_var, renamed_select_var;
     sync_var, renamed_sync_var]
  in let local_renaming = local_renaming_pre @ local_renaming_post
  and static_renaming = static_renaming_pre @ static_renaming_post
  and pre_renaming = local_renaming_pre @ static_renaming_pre
  and post_renaming = local_renaming_post @ static_renaming_post
  in let local_renaming =
    local_renaming @ static_renaming in
  let pre_vars = List.map pre_renaming ~f:snd
  and post_vars = List.map post_renaming ~f:snd
  in local_renaming, (pre_vars, [], post_vars)

end

(** Global translation step *)

let renamings =
  List.map model.automata ~f:(fun automaton ->
    let module A = Automaton (struct let automaton = automaton end)
    in
    automaton.name, A.var_renaming_of_automaton automaton
  )

let var_of_names =
  List.map model.automata ~f:(fun automaton ->
    let module E = Environment
      (Context: Context)
      (
        struct
          let variable_declarations =
            List.map ~f:cast_var_decl automaton.variables
        end
      )
    in
    automaton.name, E.var_of_name
  )

let clk_vars_of = List.filter_map ~f:(
  fun ({name; typ; _}: variable_declaration) ->
  match typ with
  | Clock -> Some name
  | _ -> None
)

let true_expr = Boolean.mk_true ctxt
let false_expr = Boolean.mk_false ctxt

open Environment (Context)
  (struct let variable_declarations = model_variables end)

(** The delay condition.

  We fuse action and delay steps. Therefore, in each step,
  the effect on a clock is to either:
  - add the non-deterministically chosen value `delta` to the clock,
  - or to reset the clock, and thus setting the clock's value to `delta`.
  *)
let clock_effect reset_pairs =
  let clk_vars = clk_vars_of model_variables in
  let reset_pairs = merge_reset_pairs reset_pairs in
  let reset_conds = List.map clk_vars ~f:Boolean.(fun x ->
    let x_var = var_of_name x in
    let x_next = next_of_name x in
    let cond = (
      List.Assoc.find ~equal:String.equal reset_pairs x
      |> Option.value ~default:false_expr
    ) in
    mk_ite ctxt cond
      (mk_eq ctxt x_next delta_var)
      (mk_eq ctxt x_next (Arithmetic.mk_add ctxt [x_var; delta_var]))
  ) in
  Boolean.mk_and ctxt reset_conds

(** Composition *)
let global_sync_var_name = "Sync"
let global_sync_var = mk_const_s ctxt global_sync_var_name int_sort

let automata_names = List.map model.system.elements ~f:(fun x -> x.automaton)

let get_sync_var name = mk_const_s ctxt (
    rename name sync_var_name) string_sort

let sync_composition =
  let conds_of_sync sync = List.mapi sync ~f:Boolean.(fun i ->
    let automaton = List.nth_exn automata_names i in
    let sync_var = get_sync_var automaton in
    function
    | None -> mk_eq ctxt sync_var no_sync
    | Some name -> mk_eq ctxt sync_var (mk_strong name) (* XXX what about weak? *)
  ) |> Boolean.mk_and ctxt in
  let cond_of_syncs = List.map model.system.syncs
    ~f:(fun sync -> conds_of_sync sync.synchronise)
    |> Boolean.mk_or ctxt in
  cond_of_syncs

let eps_composition =
  let all_none_but not_none = List.filter_map automata_names ~f:(fun name ->
    if String.equal name not_none then
      None
    else
      Some (Boolean.mk_eq ctxt (get_sync_var name) no_sync)
  ) in
  let get_eps_sync not_none = Boolean.(
    mk_and ctxt
      (mk_eq ctxt (get_sync_var not_none) epsilon_snyc :: all_none_but not_none)
  ) in
  List.map automata_names ~f:get_eps_sync |> Boolean.mk_or ctxt

let all_composition =
  Boolean.mk_or ctxt [eps_composition; sync_composition]

let delta_constraint =
  Arithmetic.(mk_ge ctxt delta_var (Real.mk_numeral_i ctxt 0))

(** Clock invariant *)
let clocks_nonneg =
  let open Arithmetic in
  let clk_vars = clk_vars_of model_variables in
  List.map clk_vars
    ~f:(fun name -> mk_ge ctxt (var_of_name name) (Real.mk_numeral_i ctxt 0))
  |> Boolean.mk_and ctxt

(** The initial condition of the overall system *)
let global_init =
  List.map ~f:init_of_var_decl model_variables |> Boolean.mk_and ctxt

(** Sepcifying the sets of variables, on which the global system is defined. *)

let pre_vars, aux_vars, post_vars =
  List.map renamings
    ~f:(fun (_name, (_renaming, var_sets)) -> var_sets)
  |> List.unzip3
  |> fun (pre, aux, post) -> List.(concat pre, concat aux, concat post)

let global_var_sets =
  let var_names = List.map model.variables ~f:(fun x -> x.name) in
  let pre_vars = List.map var_names ~f:var_of_name
  and aux_vars = [delta_var]
  and post_vars = List.map var_names ~f:next_of_name
  in pre_vars, aux_vars, post_vars

let pre_vars, aux_vars, post_vars =
  let glob_pre_vars, glob_aux_vars, post_aux_vars = global_var_sets in
  pre_vars @ glob_pre_vars,
  aux_vars @ glob_aux_vars,
  post_vars @ post_aux_vars

(** Translating the model checking property. *)

module All_Environment = Environment (Context)
  (struct
    let variable_declarations =
      let decls = List.map model.automata
        ~f:(fun automaton ->
          let module A = Automaton (struct let automaton = automaton end) in
          let pc_var_decl = {
            typ = String;
            name = rename automaton.name pc_var_name;
            initial_value = None;
          } in
          pc_var_decl :: A.local_var_decls_renamed)
      in
      List.concat (model_variables :: decls)
  end)

let renamer_of automaton_name =
  let renaming, _var_sets =
    List.Assoc.find_exn ~equal:String.equal renamings automaton_name in
  let lhss, rhss = List.unzip renaming in
  fun e -> Expr.substitute e lhss rhss

let translate_property_expression ({
  op;
  exp;
}: property_expression) =
  let renamings name =
    let var_of_name =
      List.Assoc.find_exn ~equal:String.equal var_of_names name in
    let rename = renamer_of name in
    fun x -> rename (var_of_name x)
  in
  match op with
  | EF -> expression ~renamings:(Some renamings) exp

let translate_property property =
  translate_property_expression property.expression

(** Printing utilities. *)
let print_boxed = Caml.Format.printf "@[%t@]\n@."

let dprintf = Caml.Format.dprintf

(** Generating the overall system.

  The result is returned as an instance of `BMC.System`.

  For debugging purposes, the system description is also printed to stdout.
*)
let print_all () = Boolean.(
  let inits, invars, transs, reset_pairs =
    List.map model.automata ~f:(fun automaton ->
      let open Automaton (struct let automaton = automaton end) in
      dprintf "Automaton:@ %s" automaton.name |> print_boxed;
      let rename = renamer_of automaton.name in
      let init = init_automaton () in
      let init = rename init in
      dprintf "Init: %a" pp_expr init |> print_boxed;
      let invar = invar_automaton pc_var automaton |> snd |> rename in
      let invar = mk_and ctxt [invar; invar_loc_in_bounds |> rename] in
      dprintf "Invar: %a" pp_expr invar |> print_boxed;
      let trans, reset_pairs = trans_automaton () in
      let trans, reset_pairs =
        rename trans,
        List.map ~f:(fun (x, y) -> x, rename y) reset_pairs in
      dprintf "Trans:@ %a" pp_expr trans |> print_boxed;
      dprintf "Reset conds:@ @[%a@]"
        (
          Util.pp_newline_list
            (fun ppf (x, expr) ->
              Caml.Format.fprintf ppf "%s: %a" x pp_expr expr)
        )
        reset_pairs
      |> print_boxed;
      init, invar, trans, reset_pairs
    ) |> Util.unzip4 in
  let init, invar, trans =
    Util.apply3 ~f:(mk_and ctxt) (inits, invars, transs) in
  let invar = Boolean.mk_and ctxt [invar; clocks_nonneg] in
  let clock_effect = clock_effect reset_pairs in
  let init = mk_and ctxt [init; global_init; delta_constraint] in
  let trans = mk_and ctxt
    [
      trans;
      mk_or ctxt [sync_composition; eps_composition];
      clock_effect;
      delta_constraint
    ] in
  let prop = translate_property (List.hd_exn model.properties) in
  (* need special treatment for delays in prop check *)
  dprintf "Clock effect:@ %a" pp_expr clock_effect
  |> print_boxed;
  dprintf "Sync composition:@ %a" pp_expr sync_composition
  |> print_boxed;
  dprintf "Eps composition:@ %a" pp_expr eps_composition
  |> print_boxed;
  dprintf "Pre vars:@ %a" pp_expr_comma_list pre_vars |> print_boxed;
  dprintf "Aux vars:@ %a" pp_expr_comma_list aux_vars |> print_boxed;
  dprintf "Post vars:@ %a" pp_expr_comma_list post_vars |> print_boxed;
  dprintf "Init:@ %a" pp_expr init |> print_boxed;
  dprintf "Invar:@ %a" pp_expr invar |> print_boxed;
  dprintf "Trans:@ %a" pp_expr trans |> print_boxed;
  dprintf "Prop:@ %a" pp_expr prop |> print_boxed;
  let module System: BMC.System = struct
    let init = pre_vars, init
    let pred = post_vars, prop
    let invar = pre_vars, invar
    let trans = pre_vars, aux_vars, post_vars, trans
  end in
  (module System: BMC.System)
)

end

let print_all ?(property_name=None) ~bound model =
  let model = begin match property_name with
  | None -> model
  | Some name ->
    let property = List.find_exn
      ~f:(fun prop -> String.equal prop.name name) model.properties in
    {model with properties = [property]}
  end in
  let _: unit = Stdio.print_endline "Creating context" in
  let module Context = struct let context = mk_context [] end
  in let _: unit = Stdio.print_endline "Setting up model"
  in let module Model = struct let model = model end
  in let _: unit = Stdio.print_endline "Creating translation environment"
  in let module Formula = Formula (Context) (Model)
  in let module System = (val (Formula.print_all ()))
  in let module Checker = BMC.BMC (System) (Context) in
  let result = Checker.bmc bound in
  let _: unit = printf "Result of BMC for k = %d: %s@." bound result in
  ()