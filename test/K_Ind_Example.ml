open Symta
open Z3
open Expr
open Base

let ctx = mk_context []

let bool_sort = Boolean.mk_sort ctx

let x, a, b, c =
  Util.apply4 ~f:(fun name -> mk_const_s ctx name bool_sort)
    ("x", "a", "b", "c")

let x', a', b', c' =
  Util.apply4 ~f:(fun name -> mk_const_s ctx (name ^ "'") bool_sort)
    ("x", "a", "b", "c")

let init = Boolean.mk_and ctx [x; a; b; c]

let trans = Boolean.(
  mk_and ctx [
    mk_eq ctx x' (mk_or ctx [mk_not ctx x; a; b; c]);
    mk_eq ctx a' (mk_or ctx [a; b]);
    mk_eq ctx b' c;
    mk_eq ctx c' (mk_false ctx);
  ]
)

let invar = Boolean.mk_true ctx

let pre_vars = [x; a; b; c]
let aux_vars = []
let post_vars = [x'; a'; b'; c']
let enlarge_cex var_assignment =
  var_assignment
  |> List.filter_map ~f:(function
  | _, None -> None
  | e, Some v -> Some (Boolean.mk_eq ctx e v)
  )
  |> Boolean.mk_and ctx


let bad = Boolean.mk_not ctx x

module System: BMC.System = struct
  let init = pre_vars, init
  let pred = pre_vars, bad
  let invar = pre_vars, invar
  let trans = pre_vars, aux_vars, post_vars, trans
  let direct_simulation_opt = None
  let enlarge_cex = enlarge_cex

end

module BMC = BMC.BMC (System) (struct let context = ctx end)

let main () = BMC.k_induction_wo_unrolling 2