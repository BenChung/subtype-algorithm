open Ocamlbuild_js_of_ocaml
       
let _ = Ocamlbuild_plugin.dispatch Ocamlbuild_js_of_ocaml.dispatcher;;
print_string "Hello world\n"
