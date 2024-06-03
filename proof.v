Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Powerset_facts.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.EqNat.

Inductive difficulty : Type := Hard | Easy.
Inductive strength : Type := Strong | Weak.
Inductive safety : Type := Safe | Dangerous.

Definition text := nat.
Definition key := text.
Definition salt := text.
Definition password := text.
Definition ciphertext := text.
Definition textSet := Ensemble text.

Definition beq_text := Nat.eqb.

Parameter PWD: password.
Parameter Salt: salt.
Parameter MEK: key.

Parameter TextRelated: text -> text -> Prop.
Definition UnrelatedSet (l: textSet) (t: text) :=
  forall h, (In text l h) -> ~(TextRelated t h).

Parameter Guess: textSet -> text -> difficulty.
Axiom nilGuess: forall t, Guess (Empty_set text) t = Hard.
Axiom incHardGuess: forall t h l,
  (Guess l t = Hard) /\ ~(TextRelated t h) -> (Guess (Add text l h) t = Hard).

Lemma unrelatedGuess: forall uset t,
  Finite text uset -> UnrelatedSet uset t -> Guess uset t = Hard.
Proof.
  intros ll t l.
  induction l as [| l' l'f H m H0].
  - intro H1.
    apply nilGuess.
  - intro H1.
    apply incHardGuess.
    split.
    apply H.
    intros h H2.
    specialize (H1 h).
    specialize (Add_intro1 text l' m h) as H3.
    auto.
    specialize (H1 m).
    specialize (Add_intro2 text l' m) as H4.
    auto.
Qed.

Lemma unionTwoUnrelatedHardGuess: forall uset1 uset2 t, Finite text uset1 -> Finite text uset2 ->
  UnrelatedSet uset1 t /\ UnrelatedSet uset2 t -> Guess (Union text uset1 uset2) t = Hard.
Proof.
  intros ll1 ll2 t l1 l2 H.
  apply unrelatedGuess.
  apply Union_preserves_Finite.
  auto. auto.
  intros h H3.
  destruct H as [H1 H2].
  specialize (H1 h).
  specialize (H2 h).
  specialize (Union_inv text ll1 ll2 h) as H4.
  elim H4.
  auto. auto. auto.
Qed.

Lemma unionUnrelatedHardGuess: forall hset uset t, Finite text hset -> Finite text uset ->
  UnrelatedSet uset t -> Guess hset t = Hard -> Guess (Union text hset uset) t = Hard.
Proof.
  intros ll1 ll2 t l1 l2 H H0.
  induction l2 as [| l' l'f H1 m H2].
  - specialize (Empty_set_zero text ll1) as H1.
    specialize (Union_commutative text (Empty_set text) ll1) as H2.
    rewrite H2 in H1.
    rewrite H1.
    trivial.
  - specialize (Union_add text ll1 l' m) as H3.
    rewrite <- H3.
    apply incHardGuess.
    split.
    apply H1.
    assert (H4: UnrelatedSet (Add text l' m) t -> UnrelatedSet l' t).
    {
      unfold UnrelatedSet.
      intros A h.
      specialize (Add_intro1 text l' m h) as B.
      auto.
    }
    auto.
    assert (H5: UnrelatedSet (Add text l' m) t -> ~ TextRelated t m).
    {
      unfold UnrelatedSet.
      intros C.
      specialize (C m) as D.
      specialize (Add_intro2 text l' m) as E.
      auto.
    }
    auto.
Qed.

(*
Axiom incEasyGuess: forall t h l, (Guess l t <> Hard) -> (Guess (Add text l h) t <> Hard).
Lemma subsetHardGuess: forall l sl t, Finite text l -> Finite text sl ->
  (Guess l t = Hard) /\ (Included text sl l) -> (Guess sl t = Hard).
Proof.
  intros l' sl' t l sl H.
  induction sl as [|tail' tail H1 h H2].
  - apply nilGuess.
  - specialize (incEasyGuess t h tail') as HA.
    assert (T : Guess (InsertSet tail' h) t = Hard -> Guess tail' t = Hard).
    {
      intros HB.
      apply NNPP.
      intro HC.
      apply HA in HC.
      contradiction.
    }
Qed.
*)

Parameter TextStrength: text -> strength.

Parameter E_Sym D_Sym: text -> key -> text.
Axiom symEnDe: forall k t, D_Sym k (E_Sym k t) = t.
Axiom symDeEn: forall k t, D_Sym k (D_Sym k t) = t.
Axiom symTextSafety: forall k t, Guess (Singleton text (E_Sym k t)) t = Hard.

Record key_pair := {pub: key; pr: key}.
Axiom asymKeySafety: forall kp, Guess (Singleton text (pr kp)) (pub kp) = Hard.

Parameter E_Asym D_Asym: text -> key -> text.
Axiom asymEnDe: forall kp t, D_Asym (pub kp) (E_Asym (pr kp) t) = t.
Axiom asymDeEn: forall kp t, E_Asym (pr kp) (D_Asym (pub kp) t) = t.

Parameter Hash: text -> text.
Axiom rareConflictHash: forall t1 t2,
  Hash t1 = Hash t2 -> Guess (Singleton text (Hash t1)) t2 = Hard.
Theorem onewayHash: forall t, Guess (Singleton text (Hash t)) t = Hard.
Proof.
  intro t.
  apply rareConflictHash.
  trivial.
Qed.

Parameter Kdf: password -> salt -> key.
Axiom rareConflictKdf: forall p s,
  (forall p', Kdf p s = Kdf p' s -> Guess (Couple text s (Kdf p s)) p' = Hard) /\
  (forall s', Kdf p s = Kdf p s' -> Guess (Couple text p (Kdf p s)) s' = Hard).
(* TODO *)
Theorem saltyKdf: forall p s, Guess (Singleton text (p)) (Kdf p s) = Hard.

Axiom onewayKdf: forall p s, Guess (Singleton text (Kdf p s)) p = Hard.

Definition KEK := Kdf PWD Salt.
Definition KEK_MEK := E_Sym KEK MEK.
Definition H_MEK := Hash MEK.

Inductive r_option :=
  | Some (k : key)
  | Fail.

Definition Auth (PWD_t:password) :=
  let KEK_t := Kdf PWD_t Salt in
  let MEK_t := D_Sym KEK_t KEK_MEK in
  match beq_text (Hash MEK_t) H_MEK with
  | true => Some MEK_t
  | false => Fail
  end.

Parameter WeakSet: textSet.
(* TODO: Change to Definition *)
Axiom prioriLeaked: forall t, TextStrength t = Weak -> In text WeakSet t.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Pred_Type.

Axiom relationEquivalence: Equivalence TextRelated.


(*

Fixpoint SetStrength (l: list text) :=
  match l with
  | nil => Strong
  | h :: t => match (TextStrength h) with
    | Weak => Weak
    | Strong => SetStrength t
    end
  end.
*)