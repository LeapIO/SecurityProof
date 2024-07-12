Require Import Coq.Sets.Ensembles.
From LeapSecurity Require Export Definitions.

Definition relation := Ensemble (text * text).

Definition add_relation_2 (rel : relation) (x y: text) : relation :=
  Union _ (Singleton _ (x, y)) (Union _ (Singleton _ (y, x)) rel).

Definition add_relation_3 (rel : relation) (x y r: text) : relation :=
  let rel1 := add_relation_2 rel x r in
  add_relation_2 rel1 x r.

Definition E_Sym_rel (rel : relation) (k t: text) :=
  let r := E_Sym k t in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel).

Definition D_Sym_rel (rel : relation) (k t: text) :=
  let r := D_Sym k t in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel).

Definition E_Asym_rel (rel : relation) (k t: text) :=
  let r := E_Asym k t in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel).

Definition D_Asym_rel (rel : relation) (k t: text) :=
  let r := D_Asym k t in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel).

Definition Hash_rel (rel : relation) (t: text) :=
  let r := Hash t in
  let new_rel := add_relation_2 rel t r in
  (r, new_rel).

Definition Kdf_rel (rel : relation) (pwd salt: text) :=
  let r := Kdf pwd salt in
  let new_rel := add_relation_3 rel pwd salt r in
  (r, new_rel).

Definition Sign_rel (rel : relation) (k t: text) :=
  let r := Sign k t in
  let new_rel := add_relation_3 rel k t r in
  (r, new_rel).

Definition Conc_rel (rel : relation) (w: wrapped) :=
  let r := Conc w in
  let rel1 := add_relation_2 rel (mek w) r in
  let rel2 := add_relation_2 rel1 (nonce w) r in
  (r, rel2).

Definition Splt_rel (rel : relation) (t: text) :=
  let r := Splt t in
  let rel1 := add_relation_2 rel t (mek r) in
  let rel2 := add_relation_2 rel1 t (nonce r) in
  (r, rel2).
