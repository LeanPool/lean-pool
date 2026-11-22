/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.CD.Heredity
public import LeanPool.ExtriangulatedRealization.CD.Idempotents
public import LeanPool.ExtriangulatedRealization.CD.Injectives

/-!
# Proposition 4.4: the structure of `C(D)`

`C(D)` is idempotent complete and Krull–Schmidt; its indecomposables are, up to isomorphism, the
pairwise nonisomorphic single objects `X`, `Y`, `A i`, `P i`, each with endomorphism ring `k`;
the extension spaces between them are given by (4.1); `C(D)` has enough injectives; and
`E² = 0`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Statement

universe u

/-- **Proposition 4.4.** -/
theorem proposition_4_4 : Proposition44.{u} := by
  intro k _ I _ _ _ D hD
  exact ⟨isIdempotentComplete_CD D, isKrullSchmidt_CD D,
    fun _ hX => exists_iso_single_of_isIndecomposable D hX, single_isIndecomposable D,
    fun _ _ ⟨e⟩ => eq_of_single_iso D e, single_existsUnique_smul D, rank_ext_single D,
    cd_hasEnoughInjectives D hD, cdData_isHereditary D⟩

end ExtriangulatedRealization
