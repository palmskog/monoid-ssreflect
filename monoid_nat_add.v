From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import monoid_record.

Import MonoidScope.

Definition nat_add_monoidMixin := MonoidMixin addnA add0n addn0.
Canonical nat_add_monoid := Eval hnf in MonoidType _ nat_add_monoidMixin.

Definition nat_add_commMonoidMixin := CommMonoidMixin addnC.
Canonical nat_add_commMonoid := Eval hnf in CommMonoidType _ nat_add_commMonoidMixin.
