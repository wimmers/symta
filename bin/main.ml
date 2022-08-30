open Core
open Ppx_yojson_conv_lib
open Symta
open Translate
open JANI

let print_all ?(property_name=None) ~bound model =
  let model = begin match property_name with
  | None -> model
  | Some name ->
    let property = List.find_exn
      ~f:(fun prop -> String.equal prop.name name) model.properties in
    {model with properties = [property]}
  end in
  let _: unit = Stdio.print_endline "Creating context" in
  let module Context = struct let context = Z3.mk_context [] end
  in let _: unit = Stdio.print_endline "Setting up model"
  in let module Model = struct let model = model end
  in let _: unit = Stdio.print_endline "Creating translation environment"
  in let module Formula = Formula (Context) (Model)
  in let module System = (val (Formula.print_all ()))
  in let module Checker = BMC.BMC (System) (Context) in
  let result = Checker.bmc bound in
  let _: unit = printf "Result of BMC for k = %d: %s@." bound result in
  ()

let jani_of_json_file s = JANI.model_of_yojson (Yojson.Safe.from_file s)

let do_it file_name property_name bound =
  try
    let jani = jani_of_json_file file_name
    in
      print_endline (JANI.jani_to_json_string jani);
      print_endline "=========================================";
      print_all ~property_name ~bound jani
  with Yojson_conv.Of_yojson_error (e, yojson) ->
    print_endline (Exn.to_string e);
    print_endline (Yojson.Safe.to_string yojson)

let command =
  Command.basic
    ~summary:"Read JANI model from JSON string"
    Command.Let_syntax.(
      let%map_open file_name = anon ("filename" %: Filename_unix.arg_type)
      and property_name = anon (maybe ("formula" %: string))
      and bound = flag "bound" (optional_with_default 5 int) ~doc:"BMC bound" in
      fun () ->
        do_it file_name property_name bound
    )

let () = Command_unix.run command