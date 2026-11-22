/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Defs.Descent
public import LeanPool.RigidDescent.Foundations.Brown
public import Mathlib.CategoryTheory.Monoidal.Mon
public import LeanPool.RigidDescent.Paper.Sec4

/-!
# Theorem A

Braided extensions of Murphy's Theorem A (`thm:A`) and its split-mono variant. The upstream
formalization of the manuscript in preparation assumes a symmetric tensor product.

* `theoremA_of_splitMono`: for any map `η : 𝟙 ⟶ B` such that `B ⊗ η` is a split
  monomorphism. Remark 4.3 (`rem:unit-only`) observes that this is all the proofs use.
* `theoremA`: for a ring object (monoid object) `B`.

The implications follow the argument in the upstream formalization of §4.
(1) ⇒ (3) is Theorem 4.2 (`IsDescentType.isNilPure`),
(3) ⇒ (2) is Theorem 3.6 (`IsNilPure.isEffectiveDescentType`), (3) ⇔ (4) is Lemma 2.7
(`isNilPure_iff`), and (2) ⇒ (1) is `IsEffectiveDescentType.isDescentType`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

universe v u

namespace RigidDescent

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
  [MonoidalCategory T] [BraidedCategory T] [MonoidalClosed T] [TensorTriangulated T]
  [RigidlyCompactlyGenerated T]

/-- Braided extension of the split-mono variant of Theorem A (Remark 4.3) for a map
`η : 𝟙 ⟶ B` with `B ⊗ η` a split monomorphism.
Let `I →δ 𝟙 →η B → ΣI` be an exact triangle. The following are equivalent:
1. `B` is of descent type;
2. `B` is of effective descent type;
3. `B` is nil-pure;
4. there is a pure monomorphism `𝟙 ⟶ E` for some `E ∈ Thick^⊗(B)`. -/
theorem theoremA_of_splitMono {B I : T} (η : 𝟙_ T ⟶ B) [IsSplitMono (B ◁ η)]
    (δ : I ⟶ 𝟙_ T) (ε : B ⟶ I⟦(1 : ℤ)⟧) (hT : Triangle.mk δ η ε ∈ distTriang T) :
    List.TFAE [IsDescentType δ, IsEffectiveDescentType B, IsNilPure δ,
      ∃ (E : T) (j : 𝟙_ T ⟶ E), IsPureMono j ∧ (thickTensorIdeal B) E] := by
  tfae_have 1 → 3 := IsDescentType.isNilPure
  tfae_have 3 → 2 := IsNilPure.isEffectiveDescentType hT
  tfae_have 2 → 1 := IsEffectiveDescentType.isDescentType hT
  tfae_have 3 ↔ 4 := isNilPure_iff hT
  tfae_finish

/-- Braided extension of Theorem A. Let `B` be a ring object of a rigidly compactly generated
braided tensor-triangulated category `T`, and `I →δ 𝟙 →η B → ΣI` the exact triangle of its unit.
The following are equivalent:
1. `B` is of descent type;
2. `B` is of effective descent type;
3. `B` is nil-pure;
4. there is a pure monomorphism `𝟙 ⟶ E` for some `E ∈ Thick^⊗(B)`. -/
theorem theoremA {B I : T} [MonObj B] (δ : I ⟶ 𝟙_ T) (ε : B ⟶ I⟦(1 : ℤ)⟧)
    (hT : Triangle.mk δ MonObj.one ε ∈ distTriang T) :
    List.TFAE [IsDescentType δ, IsEffectiveDescentType B, IsNilPure δ,
      ∃ (E : T) (j : 𝟙_ T ⟶ E), IsPureMono j ∧ thickTensorIdeal B E] :=
  haveI : IsSplitMono (B ◁ (MonObj.one : 𝟙_ T ⟶ B)) :=
    IsSplitMono.mk' ⟨MonObj.mul ≫ (ρ_ B).inv, by
      rw [← Category.assoc, MonObj.mul_one, Iso.hom_inv_id]⟩
  theoremA_of_splitMono MonObj.one δ ε hT

end RigidDescent
