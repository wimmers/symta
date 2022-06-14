open Core
open Ppx_yojson_conv_lib

let muntax_of_json_file s = Muntax.model_of_yojson (Yojson.Safe.from_file s)

let do_it file_name =
  try
    let muntax = muntax_of_json_file file_name
    in
      (* print_endline (Muntax.muntax_to_json_string muntax);
      print_endline "========================================="; *)
      print_endline (
        Muntax.translate muntax
        |> JANI.jani_to_json_string
      )
  with Yojson_conv.Of_yojson_error (e, yojson) ->
    print_endline (Exn.to_string e);
    print_endline (Yojson.Safe.to_string yojson)

let command =
  Command.basic
    ~summary:"Convert Munta Simple Network Language model to JANI"
    Command.Let_syntax.(
      let%map_open file_name = anon ("filename" %: Filename_unix.arg_type)
      in fun () ->
        do_it file_name
    )

let () = Command_unix.run command