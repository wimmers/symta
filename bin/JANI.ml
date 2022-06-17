open Ppx_yojson_conv_lib

type identifier = string [@@deriving yojson]

type lvalue = identifier [@@deriving yojson]

type element = {
  automaton : string;
  input_enable : identifier list [@default []] [@yojson_drop_default (=)];
  comment : string option [@default None] [@yojson_drop_default (=)];
} [@@deriving yojson]

type sync = {
  synchronise : identifier option list;
  result : identifier option [@default None] [@yojson_drop_default (=)];
    (* NB: we label transitions with ‹sync› not just ‹result› *)
  comment : string option [@default None] [@yojson_drop_default (=)];
} [@@deriving yojson]

type composition = {
  elements : element list;
  syncs : sync list [@default []] [@yojson_drop_default (=)];
  comment : string option [@default None] [@yojson_drop_default (=)];
} [@@deriving yojson]

type bounded_type = {
  lower_bound : int [@key "lower-bound"];
  upper_bound : int [@key "upper-bound"];
} [@@deriving yojson] [@@yojson.allow_extra_fields]

type typ =
  TBounded of bounded_type
| TBool  [@name "bool"]
| TClock [@name "clock"]
  [@@deriving yojson]

let typ_of_yojson yojson =
  match yojson with
  | `Assoc (
      ("base", `String "int") ::
      ("kind", `String "bounded") ::
      _
    )
  as assoc -> TBounded (bounded_type_of_yojson assoc)
  | `String s when s = "clock" -> TClock
  | `String s when s = "bool" -> TBool
  | x -> typ_of_yojson x

let yojson_of_typ = function
| TBool -> `String "bool"
| TClock -> `String "clock"
| TBounded {lower_bound; upper_bound} ->
  `Assoc [
    ("base", `String "int");
    ("kind", `String "bounded");
    ("lower-bound", `Int lower_bound);
    ("upper-bound", `Int upper_bound);
  ]

type constant_value =
| Real of float
| Int of int
| Bool of bool
[@@deriving yojson]

type expression =
| Var of identifier
| Const of constant_value
| Binary of {
    op : string;
    left: expression;
    right: expression;
  }
| Unary of {
    op : string;
    exp: expression;
  }
| Local of {
    name : identifier;
    exp : expression;
  }
[@@deriving yojson]

let is_mem = Core.List.Assoc.mem ~equal:String.equal
let get = Core.List.Assoc.find_exn ~equal:String.equal

let rec expression_of_yojson: (Yojson.Safe.t -> _) = function
| `String s -> Var s
| `Bool b -> Const (Bool b)
| `Int n -> Const (Int n)
| `Float n -> Const (Real n)
| `Assoc a when
    is_mem a "op" && is_mem a "left" && is_mem a "right" ->
    Binary {
      op = identifier_of_yojson (get a "op");
      left = expression_of_yojson (get a "left");
      right = expression_of_yojson (get a "right");
    }
| `Assoc
    [
      "name", `String s;
      "exp", a;
    ] -> Local {
      name = s;
      exp = expression_of_yojson a;
    }
| x ->
  Yojson_conv.of_yojson_error ("expression_of_yojson: maleformed expression") x

let rec yojson_of_expression = function
| Var s -> `String s
| Const (Bool b) -> `Bool b
| Const (Int n) -> `Int n
| Const (Real n) -> `Float n
| Binary {op; left; right} ->
  `Assoc [
    ("op", `String op);
    ("left", yojson_of_expression left);
    ("right", yojson_of_expression right);
  ]
| Unary {op; exp} ->
  `Assoc [
    ("op", `String op);
    ("exp", yojson_of_expression exp);
  ]
| Local {name; exp} ->
  `Assoc [
    ("name", `String name);
    ("exp", yojson_of_expression exp);
  ]

type variable_declaration = {
  name : identifier;
  typ : typ [@key "type"];
  transient : bool [@default false] [@yojson_drop_default (=)];
  initial_value : expression option [@key "initial-value"]
    [@default None] [@yojson_drop_default (=)];
} [@@deriving yojson]

type action = {
  name : identifier;
  comment : string option [@default None] [@yojson_drop_default (=)];
} [@@deriving yojson]

type transient_value = {
  ref : lvalue; (* what to set the value for *)
  value : expression; (* the value, must not contain references to transient variables or variables of type *)
                        (* clock" or "continuous *)
  comment : string option [@default None] [@yojson_drop_default (=)]; (* an optional comment *)
} [@@deriving yojson]

type commented_expression = {
  exp : expression;
  comment : string option [@default None] [@yojson_drop_default (=)];
} [@@deriving yojson]

let default_exp = {
  exp = Const (Bool true);
  comment = None;
}

type location = {
  name : identifier; (* the name of the location, unique among all locations of this automaton *)
  time_progress : (* the location's time progress condition, not allowed except TA, PTA, STA, HA, PHA and STA, *)
                        (* type bool; if omitted in TA, PTA, STA, HA, PHA or SHA, it is true *)
    commented_expression [@key "time-progress"] [@default default_exp] [@yojson_drop_default (=)];
  transient_values :
    transient_value list [@default []] [@yojson_drop_default (=)];
    (* values for transient variables in this location *)
  comment : string option[@default None] [@yojson_drop_default (=)];
} [@@deriving yojson]

type assignment = {
  ref : lvalue;
  value : expression;
  index : int [@default 0] [@yojson_drop_default (=)];
  comment : string option[@default None] [@yojson_drop_default (=)];
} [@@deriving yojson]

let default_prob = {
  exp = Const (Real 1.);
  comment = None;
}

type destination = {
  location : identifier;
  probability :
    commented_expression [@default default_prob] [@yojson_drop_default (=)];
  assignments : assignment list [@default []] [@yojson_drop_default (=)];
  comment : string option [@default None] [@yojson_drop_default (=)];
} [@@deriving yojson]

type edge = {
  location : identifier;
  action : identifier option [@default None] [@yojson_drop_default (=)];
  (* rate : unit option; *)
  guard : commented_expression [@default default_exp] [@yojson_drop_default (=)];
  destinations : destination list;
  comment : string option [@default None] [@yojson_drop_default (=)];
} [@@deriving yojson]

type automaton = {
  name : identifier;
  variables : variable_declaration list [@default []] [@yojson_drop_default (=)];
  (* restrict_initial : unit option; *)
  locations : location list;
  initial_locations : identifier list [@key "initial-locations"];
  edges : edge list;
  comment : string option [@default None] [@yojson_drop_default (=)];
} [@@deriving yojson]

type ctl_operator =
  EF

let ctl_operator_of_yojson: (Yojson.Safe.t -> _) = function
| `String "∃◇" -> EF
| x -> raise (Yojson_conv.of_yojson_error
    ("ctl_operator_of_yojson: malformed ctl_operator") x)

let yojson_of_ctl_operator = function
| EF -> `String "∃◇"

type property_expression = {
  op: ctl_operator;
  exp: expression;
}
[@@deriving yojson]

type property = {
  name: identifier;
  expression: property_expression;
  comment: string option [@default None] [@yojson_drop_default (=)];
}
[@@deriving yojson]

type model = {
  jani_version : int [@key "jani-version"];
  name : string;
  (* metadata : unit; *)
  typ : string [@key "type"];
  (* features : unit option; *)
  actions : action list [@default []] [@yojson_drop_default (=)];
  (* constants : unit list; Kill option for convenience *)
  variables : variable_declaration list [@default []] [@yojson_drop_default (=)];
  (* restrict_initial : unit option; *)
  automata : automaton list;
  system : composition;
  properties : property list;
} [@@deriving yojson] [@@yojson.allow_extra_fields]

let jani_of_json_string s = model_of_yojson (Yojson.Safe.from_string s)
let jani_to_json_string jani =
  Yojson.Safe.pretty_to_string (yojson_of_model jani)