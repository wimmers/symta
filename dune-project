(lang dune 2.8)
(name symta)

(generate_opam_files true)

(source
 (github wimmers/munta))

(authors "Simon Wimmer")

(maintainers "Simon Wimmer")

(license MIT)

(documentation https://github.com/wimmers/symta)

(package
 (name symta)
 (synopsis "Bounded model checking of timed automata")
 (description
  "Tranlsation of timed automata models specified with JANI to SMT formulae,
  enabling basic bounded model checking")
 (depends ocaml dune core yojson re2 z3)
 (tags
  ("timed automata" "model checking" "verification")))