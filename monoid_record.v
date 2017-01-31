From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope monoid_scope with m.

Module MonoidScope.
Open Scope monoid_scope.
End MonoidScope.
Import MonoidScope.

Module Monoid.

Structure mixin_of (T : Type) := Mixin {
  mul : T -> T -> T;
  one : T;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul
}.

Structure type : Type := Pack {
  sort : Type;
  _ : mixin_of sort
}.

Definition mixin T :=
  let: Pack _ m := T return mixin_of (sort T) in m.

Definition clone T :=
  fun mT & sort mT -> T =>
  fun m (mT' := @Pack T m) & phant_id mT' mT => mT'.

Module Import Exports.
Coercion sort : type >-> Sortclass.
Coercion mixin : type >-> mixin_of.
Bind Scope monoid_scope with sort.
Notation monoidType := type.
Notation MonoidMixin := Mixin.
Notation MonoidType T m := (@Pack T m).
Notation "[ 'monoidMixin' 'of' T ]" := (sort _ : mixin_of T)
  (at level 0, format "[ 'monoidMixin'  'of'  T ]") : form_scope.
Notation "[ 'monoidType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'monoidType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'monoidType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'monoidType'  'of'  T ]") : form_scope.
End Exports.

End Monoid.
Export Monoid.Exports.

Section ElementOps.

Variable T : monoidType.
Notation rT := (Monoid.sort T).

Definition onem : rT := Monoid.one T.
Definition mulm : T -> T -> rT := Monoid.mul T.
Definition expmn_rec (x : T) n : rT := iterop n mulm x onem.

End ElementOps.

Definition expmn := nosimpl expmn_rec.

Notation "1" := (onem _) : monoid_scope.
Notation "x1 * x2" := (mulm x1 x2) : monoid_scope.
Notation "x ^+ n" := (expmn x n) : monoid_scope.

Section MonoidIdentities.

Variable T : monoidType.
Implicit Types x y z : T.
Local Notation mulmT := (@mulm T).

Lemma mulmA : associative mulmT.  Proof. by case: T => ? []. Qed.
Lemma mul1m : left_id 1 mulmT.  Proof. by case: T => ? []. Qed.
Lemma mulm1 : right_id 1 mulmT. Proof. by case: T => ? []. Qed.

Canonical monoid_law := Monoid.Law mulmA mul1m mulm1.

Lemma expmnE x n : x ^+ n = expmn_rec x n. Proof. by []. Qed.
Lemma expm0 x : x ^+ 0 = 1. Proof. by []. Qed.
Lemma expm1 x : x ^+ 1 = x. Proof. by []. Qed.

Lemma expmS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //; rewrite mulm1. Qed.

Lemma expm1n n : 1 ^+ n = 1 :> T.
Proof. by elim: n => // n IHn; rewrite expmS mul1m. Qed.

Lemma expmD x n m : x ^+ (n + m) = x ^+ n * x ^+ m.
Proof. by elim: n => [|n IHn]; rewrite ?mul1m // !expmS IHn mulmA. Qed.

Lemma expmSr x n : x ^+ n.+1 = x ^+ n * x.
Proof. by rewrite -addn1 expmD expm1. Qed.

Lemma expmM x n m : x ^+ (n * m) = x ^+ n ^+ m.
Proof.
elim: m => [|m IHm]; first by rewrite muln0 expm0.
by rewrite mulnS expmD IHm expmS.
Qed.

Lemma expmAC x m n : x ^+ m ^+ n = x ^+ n ^+ m.
Proof. by rewrite -!expmM mulnC. Qed.

Definition commute x y := x * y = y * x.

Lemma commute_refl x : commute x x.
Proof. by []. Qed.

Lemma commute_sym x y : commute x y -> commute y x.
Proof. by []. Qed.

Lemma commute1 x : commute x 1.
Proof. by rewrite /commute mulm1 mul1m. Qed.

Lemma commuteM x y z : commute x y ->  commute x z ->  commute x (y * z).
Proof. by move=> cxy cxz; rewrite /commute -mulmA -cxz !mulmA cxy. Qed.

Lemma commuteX x y n : commute x y ->  commute x (y ^+ n).
Proof.
by move=> cxy; case: n; [apply: commute1 | elim=> // n; apply: commuteM].
Qed.

Lemma commuteX2 x y m n : commute x y -> commute (x ^+ m) (y ^+ n).
Proof. by move=> cxy; apply/commuteX/commute_sym/commuteX. Qed.

Lemma expmMn x y n : commute x y -> (x * y) ^+ n  = x ^+ n * y ^+ n.
Proof.
move=> cxy; elim: n => [|n IHn]; first by rewrite mulm1.
by rewrite !expmS IHn -mulmA (mulmA y) (commuteX _ (commute_sym cxy)) !mulmA.
Qed.

End MonoidIdentities.

Hint Rewrite mulm1 mul1m mulmA : msimpl.

Ltac msimpl := autorewrite with msimpl; try done.

Module CommutativeMonoid.

Structure mixin_of (mT : monoidType) := Mixin {
  _ : commutative (@mulm mT)
}.

Structure type : Type := Pack {
  sort : monoidType;
  _ : mixin_of sort
}.

Definition mixin T :=
  let: Pack _ m := T return mixin_of (sort T) in m.

Module Import Exports.
Coercion sort : type >-> monoidType.
Coercion mixin : type >-> mixin_of.
Bind Scope monoid_scope with sort.
Notation commMonoidType := type.
Notation CommMonoidMixin := Mixin.
Notation CommMonoidType T m := (@Pack T m).
End Exports.

End CommutativeMonoid.
Export CommutativeMonoid.Exports.

Section CommutativeMonoidIdentities.

Variable T : commMonoidType.
Implicit Types x y z : T.
Local Notation mulmT := (@mulm T).

Lemma mulmC : @commutative T _ mulmT.
Proof. by case: T => ? []. Qed.

End CommutativeMonoidIdentities.
