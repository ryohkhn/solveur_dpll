dpll: dpll.ml dimacs.ml
	ocamlopt -o dpll -package str -linkpkg dimacs.ml dpll.ml

clean:
	rm -f *.cmi *.cmx *.o dpll
