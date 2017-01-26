From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun.

Require Import AAC_tactics.AAC.

Require Import monoid_record.

Import MonoidScope.

Section CommutativeMonoid.

Variable mT : commMonoidType.

Instance aac_mulm_Assoc : Associative eq (@mulm mT) := @mulmA mT.

Instance aac_mulm_Unit : Unit eq (@mulm mT) 1 :=
{
  law_neutral_left := @mul1m mT ;
  law_neutral_right := @mulm1 mT
}.

Instance aac_mulg_Comm : Commutative eq (@mulm mT) := @mulmC mT.

Lemma aac_test_1 : 
  forall x y z : mT, x * y * z = 1 * y * z * 1 * x.
Proof.
move => x y z.
by aac_reflexivity.
Qed.

Lemma aac_test_2 : 
  forall x1 x2 x3 x4 x5 x6 x7 : mT, 
    x1 * x2 * x3 * x4 * x5 * x6 * x7 = (1 * x3) * (x7 * x2 * x1 * 1) * x6 * (x5 * x4).
Proof.
move => x1 x2 x3 x4 x5 x6 x7.
by aac_reflexivity.
Qed.

End CommutativeMonoid.
