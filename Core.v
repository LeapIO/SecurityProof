From LeapSecurity Require Export Definitions.

Parameter PWD: password.
Parameter Salt: salt.
Parameter MEK: key.
Parameter MK DK: key_pair.

Definition KEK := Kdf PWD Salt.
Definition KEK_MEK := E_Sym KEK MEK.
Definition H_MEK := Hash MEK.

Definition MSign t := Sign (pr MK) t.
Definition MVerify t sig :=
  Verify (pub MK) t sig.
Definition SIG := MSign (pub DK).

Definition Auth (PWD_t:password) :=
  let KEK_t := Kdf PWD_t Salt in
  let MEK_t := D_Sym KEK_t KEK_MEK in
  if (beq_text (Hash MEK_t) H_MEK)
    then ASome MEK_t else AFail.

Definition Wrap mek k sig n :=
  if (MVerify k sig)
    then let w := {|mek := mek;
                  nonce := n|} in
    WSome (E_Asym k (Conc w))
    else WFail.

Definition Unwrap w n:=
  let uw :=
    Splt (D_Asym (pr DK) w) in
  if (beq_text (nonce uw) n)
    then USome (mek uw)
    else UFail.
