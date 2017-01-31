From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import monoid_record.

Definition nat_mul_monoidMixin := MonoidMixin mulnA mul1n muln1.
Canonical nat_mul_monoid := Eval hnf in MonoidType _ nat_mul_monoidMixin.

Definition nat_mul_commMonoidMixin := CommMonoidMixin mulnC.
Canonical nat_mul_commMonoid := Eval hnf in CommMonoidType _ nat_mul_commMonoidMixin.
