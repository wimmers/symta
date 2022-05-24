open Core
open Ppx_yojson_conv_lib

let jani_of_json_string s = JANI.model_of_yojson (Yojson.Safe.from_string s)
let jani_of_json_file s = JANI.model_of_yojson (Yojson.Safe.from_file s)
let jani_to_json_string jani = Yojson.Safe.to_string (JANI.yojson_of_model jani)

let do_it file_name =
  try
    let jani = jani_of_json_file file_name
    in print_endline (jani_to_json_string jani)
  with Yojson_conv.Of_yojson_error (e, yojson) ->
    print_endline (Exn.to_string e);
    print_endline (Yojson.Safe.to_string yojson)

let command =
  Command.basic
    ~summary:"Read JANI model from JSON string"
    Command.Let_syntax.(
      let%map_open file_name = anon ("filename" %: Filename.arg_type)
      in fun () -> do_it file_name
    )

let () = Command.run command