monoid-ssreflect
================

A Coq encoding of (commutative) monoids using ssreflect.

To reason abstractly about a commutative monoid:

```coq
Section CommutativeMonoid.

Variable mT : commMonoidType.

Instance aac_mulm_Assoc : Associative eq (@mulm mT) := @mulmA mT.

End CommutativeMonoid.
```
