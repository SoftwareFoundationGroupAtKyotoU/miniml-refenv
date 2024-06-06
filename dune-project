(lang dune 3.15)
(using menhir 2.0)

(name miniml_refenv)

(generate_opam_files true)

(source
 (github SoftwareFoundationGroupAtKyotoU/miniml-refenv))

(authors "Yuito Murase")

(maintainers "Yuito Murase")

(license MIT)

(documentation https://github.com/SoftwareFoundationGroupAtKyotoU/miniml-refenv/)

(package
 (name miniml_refenv)
 (synopsis "toy interpreter for miniml_refenv")
 (description "toy interpreter for a miniml-style staged language with refined environment classifiers")
 (depends ocaml dune)
 (tags ()))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
