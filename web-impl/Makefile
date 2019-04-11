default:
	ocamlbuild -use-menhir -use-ocamlfind -plugin-tag "package(js_of_ocaml.ocamlbuild)" -package js_of_ocaml-ppx -pkg js_of_ocaml subtype.js

native:
	ocamlbuild -use-menhir -use-ocamlfind -plugin-tag "package(js_of_ocaml.ocamlbuild)" -package js_of_ocaml-ppx -pkg js_of_ocaml subtype.native
	./subtype.native
