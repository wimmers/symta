open Z3
open Core

module type Context = sig
  val context: context
end

let pp_expr ppf e = Caml.Format.pp_print_string ppf (Expr.to_string e)
let pp_expr_comma_list = Util.pp_comma_list pp_expr

let normalize_z3_sexp s =
  Sexp.(of_string s |> to_string)

let normalize_z3_string z3_chars = Sexp.(
  let err () =
    raise (Invalid_argument (sprintf "Invalid Z3 string: %s"
      (List (Atom "str.++" :: z3_chars) |> to_string))) in
  let of_char = function
  | List [Atom "seq.unit"; List [Atom "_"; Atom "Char"; Atom x]] -> x
  | _ -> err () in
  let code_points = List.map z3_chars ~f:(fun x -> of_char x |> int_of_string) in
  let chars = List.map code_points ~f:Char.of_int_exn in
  let s = String.of_char_list chars in
  Atom (sprintf "'%s'" s)
)

let apply_normalize_z3_string = function
| Sexp.List (Atom "str.++" :: z3_chars) -> Some (normalize_z3_string z3_chars)
| _ -> None  

let rec apply_to_sexp ~f sexp =
  match f sexp with
  | Some sexp' -> sexp'
  | None ->
    match sexp with
    | Sexp.List xs -> Sexp.List (List.map xs ~f:(apply_to_sexp ~f))
    | atom -> atom

let normalize_z3_strings = apply_to_sexp ~f:apply_normalize_z3_string

let normalize_z3_sexps s = Sexp.(
  let buf = Stdlib.Lexing.from_string s in
  scan_sexps buf
  |> List.map ~f:normalize_z3_strings
  |> List.map ~f:to_string_hum
  |> String.concat ~sep:"\n"
)