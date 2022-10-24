dpll: dpll.ml dimacs.ml
	ocamlfind ocamlopt -package str -linkpkg dimacs.ml dpll.ml -o dpll 

clean:
	rm -f *.cmi *.cmx *.o dpll
