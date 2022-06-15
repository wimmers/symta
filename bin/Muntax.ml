open Core
open Ppx_yojson_conv_lib

type node = {
  name: string;
  id: int;
  invariant: string;
} [@@deriving yojson]

type edge = {
  source: int;
  target: int;
  label: string;
  update: string;
  guard: string;
} [@@deriving yojson] [@@yojson.allow_extra_fields]
(* These extra fields are for optional information label
  'source_name' & 'target_name' *)

type automaton = {
  name: string;
  nodes: node list;
  edges: edge list;
  initial: int;
  committed: int list [@default []] [@yojson_drop_default Poly.(=)];
  urgent: int list [@default []] [@yojson_drop_default Poly.(=)];
} [@@deriving yojson]

type model = {
  automata: automaton list;
  clocks: string;
  vars: string;
  formula: string;
  broadcast: string list [@default []] [@yojson_drop_default Poly.(=)];
} [@@deriving yojson]

let muntax_of_json_string s = model_of_yojson (Yojson.Safe.from_string s)
let muntax_to_json_string jani =
  Yojson.Safe.pretty_to_string (yojson_of_model jani)



exception ParseError of string

let err s = raise (ParseError s)

let parse_list s =
  match String.split ~on:',' s |> List.map ~f:String.strip with
  | [""] -> []
  | xs -> xs

let parse_clocks = parse_list

let re_var_decl_atom = Re2.create_exn
  "([a-zA-Z0-9_]+)\\[([\\-0-9]+):([\\-0-9]+)\\]"
let parse_var_decl s =
  Re2.find_first_exn re_var_decl_atom ~sub:(`Index 1) s,
  Re2.find_first_exn re_var_decl_atom ~sub:(`Index 2) s |> int_of_string,
  Re2.find_first_exn re_var_decl_atom ~sub:(`Index 3) s |> int_of_string

let parse_var_decls s = parse_list s |> List.map ~f:parse_var_decl

let parse_conj_list s =
 String.split_on_chars ~on:['&'] s
 |> List.filter ~f:(fun s -> not (String.is_empty s))

let re_expression_atom = Re2.create_exn
  "([a-zA-Z0-9_]+)\\s*(<|>|<=|>=|==|=)\\s*([0-9]+)"
let parse_expression_atom s = try
  Re2.find_first_exn re_expression_atom ~sub:(`Index 1) s,
  Re2.find_first_exn re_expression_atom ~sub:(`Index 2) s,
  Re2.find_first_exn re_expression_atom ~sub:(`Index 3) s |> int_of_string
with
  Re2.Exceptions.Regex_match_failed _ ->
  raise (err (sprintf "Failed to parse expression atom: '%s'" s))

let parse_expression s = try
  parse_conj_list s |> List.map ~f:parse_expression_atom
with
  ParseError _ ->
  raise (err (sprintf "Failed to parse expression: '%s'" s))

let re_update_atom = Re2.create_exn
  "([a-zA-Z0-9_]+)\\s*(:=|=)\\s*([0-9]+)"
let parse_update s = try
  Re2.find_first_exn re_update_atom ~sub:(`Index 1) s,
  Re2.find_first_exn re_update_atom ~sub:(`Index 3) s |> int_of_string
with
  Re2.Exceptions.Regex_match_failed _ ->
  raise (err (sprintf "Failed to parse update: %s" s))

let parse_updates s = parse_list s |> List.map ~f:parse_update


exception TranslationError of string

let err s = raise (TranslationError s)

let translate_op = function
| "<=" -> "≤"
| ">=" -> "≥"
| "==" -> "="
| "&" | "&&" -> "∧"
| "|" | "||" -> "∨"
| x -> x

let translate_expression_atom (lhs, op, rhs) = JANI.(
  let left = Var lhs in
  let right = Const (Int rhs) in
  let op = translate_op op in
  Binary {op; left; right}
)

let rec mk_conj = JANI.(function
| [] -> Const (Bool true)
| [x] -> x
| x :: xs ->
  let left = x in
  let right = mk_conj xs in
  Binary {op = "∧"; left; right}
)

let translate_expression e =
  if String.is_empty e then JANI.(Const (Bool true)) else
  let atoms = parse_expression e in
  List.map ~f:translate_expression_atom atoms |> mk_conj

let translate_update (lhs, rhs) = JANI.(
  let ref = lhs in
  let value = Const (Int rhs) in
  {ref; value; index = 0; comment = None}
)

let translate_updates s = parse_updates s |> List.map ~f:translate_update

let classify_label s =
  let open String in
  match chop_suffix s ~suffix:"?" with
  | Some s -> `Receive s
  | None ->
    match chop_suffix s ~suffix:"!" with
    | Some s -> `Send s
    | None -> `Internal s

let translate_label s =
  match classify_label s with
  | `Internal _s -> None
  | `Send s | `Receive s -> Some s

let translate_edge id_to_name ({
  source;
  target;
  label;
  update;
  guard;
}: edge) =
  JANI.{
    location = Int.to_string source;
    action = translate_label label;
    guard = {
      exp = translate_expression guard;
      comment = None;
    };
    destinations = [{
      location = Int.to_string target;
      probability = {exp = Const (Int 1); comment = None};
      assignments = translate_updates update;
      comment = None;
    }];
    comment = Some (
      sprintf "source: %s, target: %s" (id_to_name source) (id_to_name target));
  }

let translate_node ({
  name;
  id;
  invariant;
}: node) =
  JANI.{
    name = Int.to_string id;
    time_progress = {
      exp = translate_expression invariant;
      comment = None;
    };
    transient_values = [];
    comment = Some name;
  }

let translate_automaton ({
  name;
  nodes;
  edges;
  initial;
  committed;
  urgent;
}: automaton) =
  if not (List.is_empty committed) then
    raise (err (sprintf "Committed locations are not supported."))
  else if not (List.is_empty urgent) then
    raise (err (sprintf "Urgent locations are not supported."))
  else
    let id_to_name =
      List.map nodes ~f:(fun node -> node.id, node.name)
      |> List.Assoc.find_exn ~equal:Int.equal
    in
    JANI.{
      name = name;
      variables = [];
      locations = List.map nodes ~f:translate_node;
      initial_locations = [Int.to_string initial];
      edges = List.map edges ~f:(translate_edge id_to_name);
      comment = None;
    }

let partition_actions automaton =
  List.partition3_map automaton.edges ~f:(fun e ->
    match classify_label e.label with
    | `Internal s -> `Fst s
    | `Send s -> `Snd s
    | `Receive s -> `Trd s
  ) |> Util.apply3 ~f:(List.dedup_and_sort ~compare:String.compare)

let list_inter ~equal xs ys =
  List.filter ~f:(fun x -> List.exists ~f:(fun y -> equal x y) ys) xs

let input_enabled_of automaton broadcast =
  let _, _, receivers = partition_actions automaton in
  list_inter ~equal:String.equal receivers broadcast

let merge_assoc ~compare ~f xs ys =
  let rec merge acc xs0 ys0 = begin match xs0, ys0 with
  | (x, a) :: xs, (y, b) :: ys ->
    let cmp = compare x y in
    if cmp = 0 then merge ((x, f x (`Both (a, b))) :: acc) xs ys else
    if cmp < 0 then merge ((x, f x (`Fst a)) :: acc) xs ys0 else
    merge ((y, f y (`Snd b)) :: acc) xs0 ys
  | (x, a) :: xs, [] -> merge ((x, f x (`Fst a)) :: acc) xs []
  | [], (y, b) :: ys -> merge ((y, f y (`Snd b)) :: acc) [] ys
  | [], [] -> acc
  end in merge [] xs ys |> List.rev

let make_send_receive_pairs automata =
  let senders, receivers = List.map automata ~f:(fun a ->
    let _, send, receive = partition_actions a in
    List.map send ~f:(fun s -> s, a.name),
    List.map receive ~f:(fun s -> s, a.name)
  ) |> List.unzip
    |> Util.apply2 ~f:List.concat
    |> Util.apply2
        ~f:(List.sort ~compare:(fun (x, _) (y, _) -> String.compare x y))
    |> Util.apply2
        ~f:(List.group ~break:(fun (x, _) (y, _) -> not (String.equal x y)))
    |> Util.apply2 ~f:(
        List.map 
          ~f:(fun pairs -> fst (List.hd_exn pairs), List.map ~f:snd pairs))
    in
  let grouped_by_channel = merge_assoc senders receivers ~compare:String.compare
    ~f:(fun s -> function
    | `Fst _ -> None
      (* warn (sprintf "Sender without receiver: %s" s) *)
    | `Snd _ -> err (sprintf "Receiver without sender: %s" s)
    | `Both (s1, s2) -> Some (s1, s2)
    )
    |> List.filter_map ~f:(function _, None -> None | s, Some x -> Some (s, x))
  in
  let binary = List.concat_map grouped_by_channel
    ~f:(fun (channel, (senders, receivers)) ->
      List.cartesian_product senders receivers
      |> List.filter_map ~f:(fun (sender, receiver) ->
        if String.equal sender receiver then None else
        Some (channel, sender, receiver)
      )
    ) in
  let broadcast = List.concat_map grouped_by_channel
  ~f:(fun (channel, (senders, receivers)) ->
    List.map senders ~f:(fun sender ->
      channel,
      sender,
      List.filter receivers ~f:(fun x -> not (String.equal x sender))
    )
  ) in
  binary, broadcast

let make_syncs automata broadcast =
  let binary, broad = make_send_receive_pairs automata in
  let binary = List.filter binary ~f:(fun (channel, _, _) ->
    not (List.exists broadcast ~f:(String.equal channel))
  ) in
  let broad = List.filter broad ~f:(fun (channel, _, _) ->
    (List.exists broadcast ~f:(String.equal channel))
  ) in
  let name_to_index name = List.findi_exn automata
    ~f:(fun _ automaton -> String.equal automaton.name name) |> fst in
  let n = List.length automata in
  let binary_syncs = List.map binary ~f:(fun (channel, sender, receiver) ->
    let sender_index = name_to_index sender in
    let receiver_index = name_to_index receiver in
    JANI.{
      synchronise = List.init n ~f:(fun i ->
        if i = sender_index || i = receiver_index then Some channel else None
      );
      result = Some channel;
      comment = None;
    }
  ) in
  let broad_syncs = List.map broad ~f:(fun (channel, sender, receivers) ->
    let sender_index = name_to_index sender in
    let receiver_indeces = List.map ~f:name_to_index receivers in
    let indices = sender_index :: receiver_indeces in
    JANI.{
      synchronise = List.init n ~f:(fun i ->
        if List.mem ~equal:Int.equal indices i then Some channel else None
      );
      result = Some channel;
      comment = None;
    }
  ) in
  binary_syncs @ broad_syncs

let translate_variable_declaration (name, lower, upper) =
  JANI.{
    name = name;
    typ = TBounded {lower_bound = lower; upper_bound = upper};
    transient = false;
    initial_value = Some (Const (Int 0));
  }

let translate_vars s =
  parse_var_decls s |> List.map ~f:translate_variable_declaration

let translate_clocks s =
  let clock_names = parse_clocks s in
  List.map clock_names ~f:JANI.(fun x -> {
    name = x;
    typ = TClock;
    transient = false;
    initial_value = Some (Const (Int 0));
  })

let translate ({
  automata;
  clocks;
  vars;
  formula = _formula;
  broadcast;
}: model): JANI.model =
  let action_set = List.concat_map automata ~f:(fun automaton ->
    automaton.edges
    |> List.filter_map ~f:(fun edge ->
      match classify_label edge.label with
      | `Internal _s -> None
      | `Send s -> Some s
      | `Receive s -> Some s
    ) |> List.dedup_and_sort ~compare:String.compare
  ) in
  JANI.{
    jani_version = 1;
    name = "";
    typ = "ta";
    actions = List.map action_set ~f:(fun a -> JANI.{name = a; comment = None});
    variables = translate_vars vars @ translate_clocks clocks;
    automata = List.map automata ~f:translate_automaton;
    system = {
      elements = List.map automata ~f:(fun automaton -> {
        automaton = automaton.name;
        input_enable = input_enabled_of automaton broadcast;
        comment = None;
      });
      syncs = make_syncs automata broadcast;
      comment = None;
    };
    properties = [];
  }