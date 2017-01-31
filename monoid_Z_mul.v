From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import monoid_record.

Require Import ZArith.

Lemma mul1z : forall x : Z, (1 * x)%Z = x.
Proof. by auto with zarith. Qed.

Lemma mulz1 : forall x : Z, (x * 1)%Z = x.
Proof. by auto with zarith. Qed.

Definition Z_mul_monoidMixin := MonoidMixin Z.mul_assoc mul1z mulz1.
Canonical Z_mul_monoid := Eval hnf in MonoidType Z Z_mul_monoidMixin.

Definition Z_mul_commMonoidMixin := CommMonoidMixin Z.mul_comm.
Canonical Z_mul_commMonoid := Eval hnf in CommMonoidType Z_mul_monoid Z_mul_commMonoidMixin.
