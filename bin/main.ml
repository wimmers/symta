open Core
open Ppx_yojson_conv_lib
open Symta
open Translate

let jani_of_json_file s = JANI.model_of_yojson (Yojson.Safe.from_file s)

let do_it file_name property_name =
  try
    let jani = jani_of_json_file file_name
    in
      print_endline (JANI.jani_to_json_string jani);
      print_endline "=========================================";
      print_all ~property_name jani
  with Yojson_conv.Of_yojson_error (e, yojson) ->
    print_endline (Exn.to_string e);
    print_endline (Yojson.Safe.to_string yojson)

let command =
  Command.basic
    ~summary:"Read JANI model from JSON string"
    Command.Let_syntax.(
      let%map_open file_name = anon ("filename" %: Filename_unix.arg_type)
      and property_name = anon (maybe ("formula" %: string)) in
      fun () ->
        do_it file_name property_name
    )

let () = Command_unix.run command