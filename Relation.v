From LeapSecurity Require Export Core.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

Inductive relation: Type := 
 | pair (x y: text).

Definition relations := list relation.

Definition fst (r: relation) : text :=
	match r with 
	| pair x y => x
	end.

Definition snd (r: relation) : text :=
	match r with 
	| pair x y => y
	end.

(* For x, find all <x, *> pairs *)
Fixpoint get_children (l : relations) (x: text) : relations :=
	match l with
	| [] => []
	| h :: t =>
		if beq_text (fst h) x then h :: (get_children t x)
		else get_children t x
	end.

(* Remove duplicates from a list of text *)
Fixpoint remove_duplicates (l : list text) : list text :=
  match l with
  | [] => []
  | h :: t => 
    if existsb (beq_text h) t then remove_duplicates t 
    else h :: remove_duplicates t
  end.

(* Collect all nodes that appear in the first position of any pair, with duplicates removed *)
Fixpoint collect_fst (l : relations) : list text :=
  match l with
  | [] => []
  | h :: t => remove_duplicates (fst h :: collect_fst t)
  end.

(* Collect all nodes that appear in the second position of any pair, with duplicates removed *)
Fixpoint collect_snd (l : relations) : list text :=
  match l with
  | [] => []
  | h :: t => remove_duplicates (snd h :: collect_snd t)
  end.


(* Find the root nodes: those that appear in the first position but not in the second *)
Definition find_roots (l : relations) : list text :=
  let fst_nodes := collect_fst l in
  let snd_nodes := collect_snd l in
  filter (fun x => negb (existsb (beq_text x) snd_nodes)) fst_nodes.

(* Find the leaf nodes: those that appear in the second position but not in the first *)
Definition find_leaves (l : relations) : list text :=
  let fst_nodes := collect_fst l in
  let snd_nodes := collect_snd l in
  filter (fun x => negb (existsb (beq_text x) fst_nodes)) snd_nodes.  


Fixpoint list_length {A : Type} (l : list A) : nat :=
match l with
| [] => 0
| _ :: t => S (list_length t)
end.

(* Recursively search for all reachable leaf nodes, with a length parameter to ensure the recursion terminates *)
Fixpoint find_reachable_leaves_aux (l: relations) (x: text) (visited: list text) (fuel: nat) : list text :=
  match fuel with
  | 0 => [] 
  | S fuel' =>
      if existsb (beq_text x) visited then [] 
      else
        let children := get_children l x in
        let leaves := find_leaves l in
        let new_visited := x :: visited in
        fold_left (fun acc child => 
                     let child_node := snd child in
                     if existsb (beq_text child_node) leaves (*if child_node is leaf node then added to accept list*)
                     then child_node :: acc 
                     else (find_reachable_leaves_aux l child_node new_visited fuel') ++ acc) (*else recursively visit child_node*)
                  children []
  end.

Definition find_reachable_leaves (l: relations) (x: text) : list text :=
  remove_duplicates (find_reachable_leaves_aux l x [] (list_length l)).

(* Test definitions *)
Definition test_text1 := 1.
Definition test_text2 := 2.
Definition test_text3 := 3.
Definition test_text4 := 4.
Definition test_text5 := 5.
Definition test_text6 := 6.
Definition test_text7 := 7.
Definition test_text8 := 8.
Definition test_text9 := 9.
Definition test_text10 := 10.
Definition test_text11 := 11.
Definition test_text12 := 12.
Definition test_text13 := 13.
Definition test_text14 := 14.

Definition test_relations := [
  pair test_text1 test_text2;
  pair test_text1 test_text3;
  pair test_text2 test_text4;
  pair test_text2 test_text5;
  pair test_text3 test_text6;
  pair test_text3 test_text7;
  pair test_text4 test_text8;
  pair test_text5 test_text9;
  pair test_text6 test_text10;
  pair test_text7 test_text11;
  pair test_text8 test_text12;
  pair test_text9 test_text13;
  pair test_text10 test_text14
].

Eval compute in (get_children test_relations test_text1).
Eval compute in (find_roots test_relations).
Eval compute in (find_leaves test_relations).
Eval compute in (find_reachable_leaves test_relations test_text1).

Definition add_relation_2 (rel : relations) (x r: text) :=
  (pair x r) :: rel.

Definition add_relation_3 (rel : relations) (x y r: text) :=
  let rel1 := add_relation_2 rel x r in
  add_relation_2 rel1 y r.

Definition E_Sym_rel (rel : relations) (k t: text) :=
  let r := E_Sym k t in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel).

Definition D_Sym_rel (rel : relations) (k t: text) :=
  let r := D_Sym k t in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel).

Definition E_Asym_rel (rel : relations) (k t: text) :=
  let r := E_Asym k t in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel).

Definition D_Asym_rel (rel : relations) (k t: text) :=
  let r := D_Asym k t in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel).

Definition Hash_rel (rel : relations) (t: text) :=
  let r := Hash t in
  let new_rel := add_relation_2 rel t r in
  (r, new_rel).

Definition Kdf_rel (rel : relations) (pwd salt: text) :=
  let r := Kdf pwd salt in
  let new_rel := add_relation_3 rel pwd salt r in
  (r, new_rel).

Definition Sign_rel (rel : relations) (k t: text) :=
  let r := Sign k t in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel).

Definition Conc_rel (rel : relations) (w: wrapped) :=
  let r := Conc w in
  let rel1 := add_relation_2 rel (mek w) r in
  let rel2 := add_relation_2 rel1 (nonce w) r in
  (r, rel2).

Definition Splt_rel (rel : relations) (t: text) :=
  let r := Splt t in
  let rel1 := add_relation_2 rel t (mek r) in
  let rel2 := add_relation_2 rel1 t (nonce r) in
  (r, rel2).
