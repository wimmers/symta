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
  | x -> typ_of_yojson x

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
    exp: expression option [@default None] [@yojson_drop_default (=)];
  }
[@@deriving yojson]

let is_mem = Core.List.Assoc.mem ~equal:String.equal
let get = Core.List.Assoc.find_exn ~equal:String.equal

let rec expression_of_yojson: (Yojson.Safe.t -> _) = function
| `String s -> Var s
| `Int n -> Const (Int n)
| `Float n -> Const (Real n)
| `Assoc a when
    is_mem a "op" && is_mem a "left" && is_mem a "right" ->
    Binary {
      op = identifier_of_yojson (get a "op");
      left = expression_of_yojson (get a "left");
      right = expression_of_yojson (get a "right");
    }
| x ->
  Yojson_conv.of_yojson_error ("expression_of_yojson: maleformed expression") x

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
    commented_expression [@default default_exp] [@yojson_drop_default (=)];
  transient_values :
    transient_value list [@default []] [@yojson_drop_default (=)];
    (* values for transient variables in this location *)
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
  (* properties : unit; Kill option for convenience *)
  automata : automaton list;
  system : composition;
} [@@deriving yojson] [@@yojson.allow_extra_fields]