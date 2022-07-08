open Base
module Format = Caml.Format

(* Maps *)

type 'a string_tab = (string, 'a, String.comparator_witness) Base.Map.t

let empty_string_tab = Map.empty(module String)


(* Pretty printing *)

let pp_comma_list: 'a. (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit =
  fun pp_val -> fun ppf ->
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.pp_print_text ppf ", ") pp_val ppf

let pp_string_comma_list = pp_comma_list Format.pp_print_text

let pp_cut_list =
  fun pp_val -> fun ppf -> Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_val ppf

let pp_newline_list: 'a. (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit =
  fun pp_val -> fun ppf -> Format.pp_print_list ~pp_sep:Format.pp_force_newline pp_val ppf

(* XXX Move? *)
let pp_option pp_value ppf = function
  | None -> ()
  | Some v -> pp_value ppf v


(* Lists *)

let split_at_first xs ~p =
  let rec loop acc = function
  | [] -> raise Caml.Not_found
  | x :: xs when p x -> (List.rev acc, x, xs)
  | x :: xs -> loop (x::acc) xs
in loop [] xs

let unzip4 list =
  let rec loop list l0 l1 l2 l3 =
    match list with
    | [] -> l0, l1, l2, l3
    | (w, x, y, z) :: tl -> loop tl (w :: l0) (x :: l1) (y :: l2) (z :: l3)
  in
  loop (List.rev list) [] [] [] []

let partition3_mapi xs ~f =
  let tagged = List.mapi ~f xs in
  List.filter_map tagged ~f:(function `Fst x -> Some x | _ -> None),
  List.filter_map tagged ~f:(function `Snd x -> Some x | _ -> None),
  List.filter_map tagged ~f:(function `Trd x -> Some x | _ -> None)

(* From https://stackoverflow.com/questions/243864/what-is-the-ocaml-idiom-equivalent-to-pythons-range-function *)
(* Returns a list of the integers in the range [i,j). *)
let (--) i j = 
    let rec aux n acc =
      if n < i then acc else aux (n-1) (n :: acc)
    in aux (j - 1) []

let repeat ~num ~v = List.map ~f:(fun _ -> v) (0 -- num)

let comb n xs =
  let rec loop k xs =
    if k >= List.length xs then
      [xs]
    else match xs with
    | [] -> assert false
    | x :: xs ->
      List.map ~f:(fun ys -> x :: ys) (loop (k - 1) xs)
      @ loop (k - 1) xs
  in
  if List.length xs < n then
    []
  else loop n xs

(* Optionals *)

let pair_with_option l = function Some r -> Some (l, r) | None -> None
let pair_option_with opt r = match opt with Some l -> Some (l, r) | None -> None

let apply_option ~f value_opt x =
  match value_opt with
  | None -> x
  | Some v -> f v x

(* Tuples *)

let apply2 ~f (x, y) = f x, f y

let apply3 ~f (x, y, z) = f x, f y, f z

let apply4 ~f (w, x, y, z) = f w, f x, f y, f z