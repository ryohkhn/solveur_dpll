open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* isX : a -> a List -> a List option
   Applique la simplification à une clause.
   Le litteral x est vrai donc on supprime la clause si on le trouve dedans.
   Cette fonction est un filtre (a utiliser avec filter_map) qui renvoie soit None, soit Some d'une clause qui ne comprend pas x *)
let isX x list =
  (* isXaux : a -> a List -> a List -> a List option 
     Si le litteral x est dans la clause -> None, sinon on renvoie la sauvegarde de la clause (listSave)*)
  let rec isXaux x list listSave =  
    match list with
    | [] -> Some listSave
    | h :: t -> if h == x then None else isXaux x t listSave
  in isXaux x list list
;;

(* isNotX : int -> int List -> int List option
   Applique la simplification a une clause.
   Le litteral x est vrai, donc on supprime tous les not(x) de la clause.
   Cette fonction est un filtre (a utiliser avec filter_map) qui renvoie soit None, soit Some d'une clause sans les not(x) *)
let isNotX x list =
  (* isNotXaux : int -> int List -> int List -> int List option 
     On renvoie l'accumulateur (acc) auquel on a ajouté tous les éléments de la clause, sauf not(x) *)
  let rec isNotXaux x list acc =
    match list with
    | [] -> Some acc
    | h :: t -> if h == -x then isNotXaux x t acc else isNotXaux x t (h::acc)
  in isNotXaux x list []
;;

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
let simplifie l clauses =
  filter_map (isNotX l) (filter_map (isX l) clauses)
;;

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)

let unitaire clauses = 
  if clauses = [] then raise Not_found else
    let rec unitaire_aux clauses = match clauses with
      | [x]::_ -> x
      | x::y -> unitaire_aux y
      | _ -> raise Not_found
    in unitaire_aux clauses
;;
    
(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)

(* Parcours de la liste de clauses et vérifie dans chaque sous liste si la valeur en argument est pure *)
let rec pur_parcours clauses value = match clauses with
  | [] -> Some value
  | x::y ->
    let result = List.mem (-value) x in
    if result then None else pur_parcours y value
;;

(* Parcours de la liste de liste et appelle pur_parcours sur chaque élément de la liste *)
let pur clauses =
  let rec pur_aux_2 = function
    | [] -> None
    | x::y ->
      let result = pur_parcours clauses x in
      if result <> None then result else pur_aux_2 y
  in
  let rec pur_aux = function
    | [] -> raise Not_found
    | l1::l2 ->
      let result = pur_aux_2 l1 in
      if result <> None then result else pur_aux l2
  in pur_aux clauses
;;


let int_from_option = function
  | Some x -> x
  | None -> failwith "no int in option result" ;;


(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  if clauses = [] then Some interpretation 
  else if mem [] clauses then None 
  else try let x = unitaire clauses in
      solveur_dpll_rec (simplifie x clauses) (x::interpretation)
      with Not_found -> 
        try let y = pur clauses in
        solveur_dpll_rec (simplifie (int_from_option y) clauses) ((int_from_option y)::interpretation)
        with Not_found ->
          let h = hd (hd clauses) in
            let branche = solveur_dpll_rec (simplifie h clauses) (h::interpretation) in
              match branche with
              | None -> solveur_dpll_rec (simplifie (-h) clauses) ((-h)::interpretation)
              | _    -> branche;;


(* tests *)
(*let () = print_modele (solveur_dpll_rec systeme [])
let () = print_modele (solveur_dpll_rec coloriage [])

let () = print_modele (solveur_split systeme [])
let () = print_modele (solveur_split coloriage [])

let () = print_modele (solveur_dpll_rec [[1;2;3];[1;-2;-3];[1;-4];[-2;-3;-4];[-1;-2;3];[5;6];[5;-6];[2;-5];[-3;-5]] [])
let () = print_modele (solveur_dpll_rec [[1;2;3];[1;-2;-3];[1;-4];[-2;-3;-4];[-1;-2;3];[5;6];[5;-6];[2;-5];[-3;-5];[1];[-1]] [])


let () = print_modele (solveur_dpll_rec [[]] [])
let () = print_modele (solveur_split [[]] [])
let () = print_modele (solveur_dpll_rec [[1]] [])
let () = print_modele (solveur_split [[1]] [])
let () = print_modele (solveur_dpll_rec [[1;-1]] [])
let () = print_modele (solveur_split [[1;-1]] [])
let () = print_modele (solveur_dpll_rec [[1];[-1]] [])
let () = print_modele (solveur_dpll_rec [[1];[-1]] [])
*)
let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])