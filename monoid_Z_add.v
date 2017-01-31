From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import monoid_record.

Require Import ZArith.

Lemma add0z : forall x : Z, (0 + x)%Z = x.
Proof. by []. Qed.

Lemma addz0 : forall x : Z, (x + 0)%Z = x.
Proof. by auto with zarith. Qed.

Definition Z_add_monoidMixin := MonoidMixin Z.add_assoc add0z addz0.
Canonical Z_add_monoid := Eval hnf in MonoidType _ Z_add_monoidMixin.

Definition Z_add_commMonoidMixin := CommMonoidMixin Z.add_comm.
Canonical Z_add_commMonoid := Eval hnf in CommMonoidType Z_add_monoid Z_add_commMonoidMixin.
