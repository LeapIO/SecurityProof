From LeapSecurity Require Export Definitions.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

Record text_with_id := {identity: nat;
                        content: text}.
Record wrapped_with_id := {mek_with_id: text_with_id;
                           nonce_with_id: text_with_id}.
Record key_pair_with_id := {pub_with_id: text_with_id;
                            pr_with_id: text_with_id}.

Definition beq_text_id (x y: text_with_id) : bool :=
  Nat.eqb (identity x) (identity y).

Definition beq_text_content (x y: text_with_id) : bool :=
  Nat.eqb (content x) (content y).

Inductive relation: Type := 
 | pair (x y: text_with_id).
Definition relations := list relation.

Definition fst (r: relation) : text_with_id :=
	match r with 
	| pair x y => x
	end.

Definition snd (r: relation) : text_with_id :=
	match r with 
	| pair x y => y
	end.

(* Check if two relations are equal *)
Definition eq_relation (r1 r2 : relation) : bool :=
  match r1, r2 with
  | pair x1 y1, pair x2 y2 =>
    (beq_text_content x1 x2) && (beq_text_content y1 y2)
  end.

(* Check if the fst and snd part of pair are equal *)
Definition id_pair (r: relation) : bool :=
  match r with
  | pair x y => (beq_text_id x y)
  end.

(* Check if a relation exists in a list of relations *)
Fixpoint in_list_relation (r: relation) (l: list relation) : bool :=
  match id_pair r with
  | true => true
  | false =>
    match l with
    | [] => false
    | h :: t => if eq_relation r h then true else in_list_relation r t
    end
  end.

(* Check if all elements of list a are in list b *)
Fixpoint all_in_relation (a b: list relation) : bool :=
  match a with
  | [] => true
  | h :: t => if in_list_relation h b then all_in_relation t b else false
  end.

(* Compare two lists of relations for content equality *)
Definition list_eq_relation (a b: list relation) : bool :=
  all_in_relation a b && all_in_relation b a.

(* For x, find all <x, *> pairs *)
Fixpoint get_children (l : relations) (x: text_with_id) : relations :=
	match l with
	| [] => []
	| h :: t =>
		if beq_text_id (fst h) x then h :: (get_children t x)
		else get_children t x
	end.

(* Collect all nodes that appear in the first position of any pair *)
Fixpoint collect_fst (l : relations) : list text_with_id :=
  match l with
  | [] => []
  | h :: t => (fst h :: collect_fst t)
  end.

(* Collect all nodes that appear in the second position of any pair *)
Fixpoint collect_snd (l : relations) : list text_with_id :=
  match l with
  | [] => []
  | h :: t => (snd h :: collect_snd t)
  end.

(* Find the root nodes: those that appear in the first position but not in the second *)
Definition find_roots (l : relations) : list text_with_id :=
  let fst_nodes := collect_fst l in
  let snd_nodes := collect_snd l in
  filter (fun x => negb (existsb (beq_text_id x) snd_nodes)) fst_nodes.

(* Find the leaf nodes: those that appear in the second position but not in the first *)
Definition find_leaves (l : relations) : list text_with_id :=
  let fst_nodes := collect_fst l in
  let snd_nodes := collect_snd l in
  filter (fun x => negb (existsb (beq_text_id x) fst_nodes)) snd_nodes.  

Fixpoint list_length {A : Type} (l : list A) : nat :=
match l with
| [] => 0
| _ :: t => S (list_length t)
end.

(* Recursively search for all reachable leaf nodes, with a length parameter to ensure the recursion terminates *)
Fixpoint find_reachable_leaves_aux (l: relations) (x: text_with_id) (visited: list text_with_id) (fuel: nat) : list text_with_id :=
  match fuel with
  | 0 => [] 
  | S fuel' =>
      if existsb (beq_text_id x) visited then [] 
      else
        let children := get_children l x in
        let leaves := find_leaves l in
        let new_visited := x :: visited in
        fold_left (fun acc child => 
                     let child_node := snd child in
                     if existsb (beq_text_id child_node) leaves (*if child_node is leaf node then added to accept list*)
                     then child_node :: acc 
                     else (find_reachable_leaves_aux l child_node new_visited fuel') ++ acc) (*else recursively visit child_node*)
                  children []
  end.

Definition find_reachable_leaves (l: relations) (x: text_with_id) : list text_with_id :=
  find_reachable_leaves_aux l x [] (list_length l).

(*
  Get all pairs <a,b>, where a is the root and b is the leaf.
*)
Definition get_root_leaf_pairs (l: relations) : list relation :=
  let roots := find_roots l in
  let leaves := find_leaves l in
  fold_left (fun acc root =>
               let reachable_leaves := find_reachable_leaves l root in
               fold_left (fun acc' leaf =>
                            if existsb (beq_text_id leaf) leaves then (pair root leaf) :: acc'
                            else acc') reachable_leaves acc)
            roots [].

(* Test definitions *)
Definition test_text1 := {|identity := 1; content := 0|}.
Definition test_text2 := {|identity := 2; content := 0|}.
Definition test_text3 := {|identity := 3; content := 0|}.
Definition test_text4 := {|identity := 4; content := 0|}.
Definition test_text5 := {|identity := 5; content := 0|}.
Definition test_text6 := {|identity := 6; content := 0|}.
Definition test_text7 := {|identity := 7; content := 0|}.
Definition test_text8 := {|identity := 8; content := 0|}.
Definition test_text9 := {|identity := 9; content := 0|}.
Definition test_text10 := {|identity := 10; content := 0|}.
Definition test_text11 := {|identity := 11; content := 0|}.
Definition test_text12 := {|identity := 12; content := 0|}.
Definition test_text13 := {|identity := 13; content := 0|}.
Definition test_text14 := {|identity := 14; content := 0|}.

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
Eval compute in (get_root_leaf_pairs test_relations).
Eval compute in (list_eq_relation test_relations  ((pair test_text3 test_text6) :: test_relations)).
Eval compute in (list_eq_relation test_relations  ((pair test_text3 test_text5) :: test_relations)).

Definition add_relation_2 (rel : relations) (x r: text_with_id) :=
  (pair x r) :: rel.

Definition add_relation_3 (rel : relations) (x y r: text_with_id) :=
  let rel1 := add_relation_2 rel x r in
  add_relation_2 rel1 y r.

Definition E_Sym_rel (k t: text_with_id) (rel : relations) (idcnt: nat) :=
  let r := {| identity := idcnt+1; content := E_Sym (content k) (content t) |} in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel, idcnt+1).

Definition D_Sym_rel (k t: text_with_id) (rel : relations) (idcnt: nat) :=
  let r := {| identity := idcnt+1; content := D_Sym (content k) (content t) |} in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel, idcnt+1).

Definition E_Asym_rel (k t: text_with_id) (rel : relations) (idcnt: nat) :=
  let r := {| identity := idcnt+1; content := E_Asym (content k) (content t) |} in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel, idcnt+1).

Definition D_Asym_rel (k t: text_with_id) (rel : relations) (idcnt: nat) :=
  let r := {| identity := idcnt+1; content := D_Asym (content k) (content t) |} in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel, idcnt+1).

Definition Hash_rel (t: text_with_id) (rel : relations) (idcnt: nat) :=
  let r := {| identity := idcnt+1; content := Hash (content t) |} in
  let new_rel := add_relation_2 rel t r in
  (r, new_rel, idcnt+1).

Definition Kdf_rel (pwd salt: text_with_id) (rel : relations) (idcnt: nat) :=
  let r := {| identity := idcnt+1; content := Kdf (content pwd) (content salt) |} in
  let new_rel := add_relation_3 rel pwd salt r in
  (r, new_rel, idcnt+1).

Definition Sign_rel (k t: text_with_id) (rel : relations) (idcnt: nat) :=
  let r := {| identity := idcnt+1; content := Sign (content k) (content t) |} in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel, idcnt+1).

Definition Conc_rel (w: wrapped_with_id) (rel : relations) (idcnt: nat) :=
  let tmp_w := {| mek := (content (mek_with_id w));
                  nonce := (content (nonce_with_id w)) |} in
  let r := {| identity := idcnt+1; content := Conc tmp_w |} in
  let rel1 := add_relation_2 rel (mek_with_id w) r in
  let rel2 := add_relation_2 rel1 (nonce_with_id w) r in
  (r, rel2, idcnt+1).

Definition Splt_rel (t: text_with_id) (rel : relations) (idcnt: nat) :=
  let tmp_r := Splt (content t) in
  let tmp_mek := {| identity := idcnt+1; content := mek tmp_r |} in
  let tmp_nonce := {| identity := idcnt+2; content := nonce tmp_r |} in
  let r := {| mek_with_id := tmp_mek; nonce_with_id := tmp_nonce |} in
  let rel1 := add_relation_2 rel t tmp_mek in
  let rel2 := add_relation_2 rel1 t tmp_nonce in
  (r, rel2, idcnt+2).
