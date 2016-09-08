Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.ssrbool.

(* needs v8.5 branch of https://github.com/coq-contribs/aac-tactics *)
Require Import AAC_tactics.AAC.

Require Import monoid_record.

Module Type CommutativeMonoid.
Parameter mT : monoidType.
Parameter mulC : @commutative mT _ (mul (mT := mT)).
End CommutativeMonoid.

Module CommutativeMonoidWork (Import CM : CommutativeMonoid).

Instance aac_mulg_Assoc : Associative eq (mul (mT := mT)) := mulA (U := mT).

Instance aac_mulg_Comm : Commutative eq (mul (mT := mT)) := mulC.

Instance aac_mulg_Unit : Unit eq (mul (mT := mT)) (unit mT) :=
{
  law_neutral_left := fun mT => _ ;
  law_neutral_right := fun mT =>  _;
}.
Proof.
- by rewrite l_mul_unit.
- by rewrite r_mul_unit.
Qed.

Lemma aac_test_1 : 
  forall x y z, x \* y \* z = (unit mT) \* y \* z \* (unit mT) \* x.
Proof.
move => x y z.
by aac_reflexivity.
Qed.

Lemma aac_test_2 : 
  forall x1 x2 x3 x4 x5 x6 x7, 
    x1 \* x2 \* x3 \* x4 \* x5 \* x6 \* x7 = ((unit mT) \* x3) \* (x7 \* x2 \* x1 \* (unit mT)) \* x6 \* (x5 \* x4).
Proof.
move => x1 x2 x3 x4 x5 x6 x7.
by aac_reflexivity.
Qed.

End CommutativeMonoidWork.
