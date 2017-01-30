From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun.

Require Import monoid_record.

Import MonoidScope.

Definition nat_add_monoidMixin := MonoidMixin addnA add0n addn0.
Canonical nat_add_monoid := MonoidType nat nat_add_monoidMixin.

Definition nat_add_commMonoidMixin := CommMonoidMixin addnC.
Canonical nat_add_commMonoid := CommMonoidType nat_add_monoid nat_add_commMonoidMixin.

(*
Definition nat_mul_monoidMixin := MonoidMixin mulnA mul1n muln1.
Canonical nat_mul_monoid := MonoidType nat nat_mul_monoidMixin.
*)

Require Import ZArith.

Lemma add0z : forall x : Z, (0 + x)%Z = x.
Proof. by []. Qed.

Lemma addz0 : forall x : Z, (x + 0)%Z = x.
Proof. by move => x; rewrite Z.add_comm. Qed.

Definition Z_add_monoidMixin := MonoidMixin Z.add_assoc add0z addz0.
Canonical Z_add_monoid := MonoidType Z Z_add_monoidMixin.

Definition Z_add_commMonoidMixin := CommMonoidMixin Z.add_comm.
Canonical Z_add_commMonoid := CommMonoidType Z_add_monoid Z_add_commMonoidMixin.
