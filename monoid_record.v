From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module MDef.

Record mixin_of (T : Type) := Mixin {
    mul_op : T -> T -> T;
    unit_op : T;
    _ : associative mul_op;
    _ : left_id unit_op mul_op;
    _ : right_id unit_op mul_op;
}.

Section Packing.

Structure pack_type : Type := Pack {type : Type; _ : mixin_of type}.

Local Coercion type : pack_type >-> Sortclass.

Variable mT : pack_type.

Definition m_struct : mixin_of mT := 
    let: Pack _ c := mT return mixin_of mT in c.

Definition mul := mul_op m_struct.
Definition unit := unit_op m_struct.

End Packing.

Module Exports.

Notation monoidType := pack_type.
Notation MMixin := Mixin.
Notation M T mT := (@Pack T mT).

Notation "x \* y" := (mul x y) (at level 43, left associativity).
Notation unit := unit.
Notation mul := mul.

Coercion type : pack_type >-> Sortclass.

Section MLemmas.
Variable U : monoidType.

Lemma l_mul_unit (x : U) : (unit U) \* x = x.
Proof.
case: U x=>tp [v j Aj Lj Rj *]; apply: Lj.
Qed.

Lemma r_mul_unit (x : U) : x \* (unit U) = x.
Proof.
case: U x=>tp [v j Aj Lj Rj *]; apply: Rj.
Qed.

Lemma mulA (x y z : U) : x \* (y \* z) = x \* y \* z.
Proof. 
by case: U x y z=>tp [v j Aj *]; apply: Aj.
Qed.

End MLemmas.

End Exports.

End MDef.

Export MDef.Exports.
