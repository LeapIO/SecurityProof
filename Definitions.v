Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Import ListNotations.

Definition text := nat.

Module ListEnsemble.
  Definition in_set := Ensembles.In.
  Definition add_set := Ensembles.Add.
End ListEnsemble.
Import ListEnsemble.

Definition key := text.
Definition salt := text.
Definition password := text.
Definition ciphertext := text.
Definition textSet := Ensemble text.
Definition beq_text := Nat.eqb.

Record key_pair := {pub: key; pr: key}.
Record wrapped := {mek: key; nonce: nat}.
Record pipeout := {data: text;
                   leaked: textSet}.
Record leapout := {final: key;
                   unsafe: textSet}.

Inductive auth_option :=
  | ASome (mek : key)
  | AFail.
Inductive wrap_option :=
  | WSome (e_mek : text)
  | WFail.
Inductive unwrap_option :=
  | USome (mek : text)
  | UFail.
Inductive leap_option :=
  | LSome (res : leapout)
  | LAuthFail (unsafe: textSet)
  | LWrapFail (unsafe: textSet)
  | LUnwrapFail (unsafe: textSet).

Parameter TextRelated: text -> text -> Prop.
Definition UnrelatedSet l t := forall h,
  (in_set text l h) -> ~(TextRelated t h).

Fixpoint as_set (l: list text) : textSet :=
  match l with
  | [] => Empty_set text
  | x :: xs => add_set text (as_set xs) x
  end.

Parameter Safe: textSet -> text -> Prop.
Parameter CrackSignature: Prop.
Parameter CrackHash: Prop.
Parameter E_Sym D_Sym:
  key -> text -> text.
Parameter E_Asym D_Asym:
  key -> text -> text.
Parameter Hash: text -> text.
Parameter Kdf: password -> salt -> key.
Parameter Sign: key -> text -> text.
Parameter Verify:
  key -> text -> text -> bool.
Parameter Conc: wrapped -> text.
Parameter Splt: text -> wrapped.

Axiom nilSafe: forall t, Safe (as_set []) t.
Axiom incSafe: forall t h l,
  (Safe l t) /\ ~(TextRelated t h) ->
  (Safe (add_set text l h) t).
Axiom symEnDe:
  forall k t, D_Sym k (E_Sym k t) = t.
Axiom symDeEn:
  forall k t, E_Sym k (D_Sym k t) = t.
Axiom symTextSafety: forall k t,
  Safe (as_set [E_Sym k t]) t .
Axiom asymKeySafety: forall kp,
  Safe (as_set [pr kp]) (pub kp) .
Axiom asymEnDe: forall kp t,
  D_Asym (pr kp) (E_Asym (pub kp) t) = t.
Axiom asymDeEn: forall kp t,
  E_Asym (pub kp) (D_Asym (pr kp) t) = t.
Axiom conflictHash: forall t1 t2,
  Hash t1 = Hash t2 ->
  (CrackHash /\ Safe (as_set [Hash t1]) t2).
Axiom signCorrect: forall kp t sig,
  sig = Sign (pr kp) t \/ CrackSignature <->
  Verify (pub kp) t sig = true.
Axiom SplitConcatenation:
  forall w, w = Splt (Conc w).