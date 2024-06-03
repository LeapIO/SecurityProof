Require Import Coq.Lists.List.
Import ListNotations.
Require Import Classical.


Inductive difficulty : Type := Hard | Easy.
Inductive strength : Type := Strong | Weak.
Inductive safety : Type := Safe | Dangerous.

Definition text := nat.
Definition key := text.
Definition salt := text.
Definition password := text.
Definition ciphertext := text.

Require Import Coq.Arith.EqNat.
Definition beq_text := Nat.eqb.

Parameter PWD: password.
Parameter Salt: salt.
Parameter MEK: key.

Parameter TextRelated: text -> text -> Prop.
Definition UnrelatedSet (l: list text) (t: text) :=
  forall h, (In h l) -> ~(TextRelated t h).

Parameter Guess: list text -> text -> difficulty.
Axiom nilGuess: forall t, Guess [] t = Hard.
Axiom incHardGuess: forall t h l,
  (Guess l t = Hard) /\ ~(TextRelated t h) -> (Guess (h::l) t = Hard).
Axiom incEasyGuess: forall t h l, (Guess l t <> Hard) -> (Guess (h::l) t <> Hard).

Lemma unrelatedGuess: forall l t,
  UnrelatedSet l t -> Guess l t = Hard.
Proof.
  intros l t.
  induction l as [| m l' H].
  - intro H1.
    apply nilGuess.
  - intro H1.
    apply incHardGuess.
    split.
    apply H.
    intros h H2.
    specialize (H1 h).
    specialize (in_cons m h l') as H3.
    auto.
    specialize (H1 m).
    specialize (in_eq m l') as H4.
    auto.
Qed.

Lemma unrelatedUnionHardGuess: forall l1 l2 t,
  UnrelatedSet l1 t /\ UnrelatedSet l2 t -> Guess (l1 ++ l2) t = Hard.
Proof.
  intros l1 l2 t H.
  apply unrelatedGuess.
  destruct H as [H1 H2].
  intros h H3.
  specialize (H1 h).
  specialize (H2 h).
  specialize (in_app_or l1 l2 h) as H4.
  elim H4.
  auto. auto. auto.
Qed.

Parameter TextStrength: text -> strength.

Parameter E_Sym D_Sym: text -> key -> text.
Axiom symEnDe: forall k t, D_Sym k (E_Sym k t) = t.
Axiom symDeEn: forall k t, D_Sym k (D_Sym k t) = t.
Axiom symTextSafety: forall k t, Guess [E_Sym k t] t = Hard.

Record key_pair := {pub: key; pr: key}.
Axiom asymKeySafety: forall kp, Guess [pr kp] (pub kp) = Hard.

Parameter E_Asym D_Asym: text -> key -> text.
Axiom asymEnDe: forall kp t, D_Asym (pub kp) (E_Asym (pr kp) t) = t.
Axiom asymDeEn: forall kp t, E_Asym (pr kp) (D_Asym (pub kp) t) = t.

Parameter Hash: text -> text.
Axiom rareConflictHash: forall t1 t2,
  Hash t1 = Hash t2 -> Guess [Hash t1] t2 = Hard.
Theorem onewayHash: forall t, Guess [Hash t] t = Hard.
Proof.
  intro t.
  apply rareConflictHash.
  trivial.
Qed.

Parameter Kdf: password -> salt -> key.
Axiom rareConflictKdf: forall p s,
  (forall p', Kdf p s = Kdf p' s -> Guess [s; Kdf p s] p' = Hard) /\
  (forall s', Kdf p s = Kdf p s' -> Guess [p; Kdf p s] s' = Hard).
Theorem saltyKdf: forall p s, Guess [p] (Kdf p s) = Hard.

Axiom onewayKdf: forall p s, Guess [Kdf p s] p = Hard.

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

Parameter WeakSet: list text.
(* TODO: Change to Definition *)
Axiom prioriLeaked: forall t, TextStrength t = Weak -> In t WeakSet.




Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Pred_Type.

Axiom relationEquivalence: Equivalence TextRelated.

Axiom inGuess: forall t, Guess [t] t = Easy.



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





