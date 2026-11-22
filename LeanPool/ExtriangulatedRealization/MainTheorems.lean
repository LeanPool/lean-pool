/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.CD.Structure
public import LeanPool.ExtriangulatedRealization.Criterion.Bounds
public import LeanPool.ExtriangulatedRealization.Criterion.TheoremA
public import LeanPool.ExtriangulatedRealization.Criterion.TheoremB
public import LeanPool.ExtriangulatedRealization.InverseSystems.Injections
public import LeanPool.ExtriangulatedRealization.Realization.Subcategory

/-!
# The main theorems

The endpoints of `Statement.lean` are proved in the following places:

* `theoremA` (Theorem A = Theorem 4.5): `Criterion/TheoremA.lean`;
* `theoremB` (Theorem B = Theorem 3.1): `Criterion/TheoremB.lean`, with the necessity
  `theoremB_necessity` for targets in all universes in `Criterion/Necessity.lean`;
* `proposition_2_3` and `corollary_2_4`: `Realization/Subcategory.lean`, from the realization of
  `Realization/Proposition.lean` and the axioms of `Realization/Extriangulated.lean`;
* `proposition_4_4`: `CD/Structure.lean`;
* `proposition_4_6`: `Criterion/Bounds.lean`.

The nonembedding consequence of Example 4.2 is `Injections.example_4_2` in
`InverseSystems/Injections.lean`.
-/
