/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.TranslateFibers

/-! The bounded square-norm set is partitioned by integer translations.
This constructs a finite norm-curve family. The uniform estimate for the
number of translation classes is a separate lattice theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

/-- The quotient of `𝓞 K` by the additive subgroup of rational integers, whose classes are the
orbits under integer translation. -/
abbrev IntegerTranslationQuotient :=
  (𝓞 K) ⧸ AddSubgroup.zmultiples (1 : 𝓞 K)

/-- The finite set of integer-translation classes of the bounded square-norm integers
`boundedSquareNormIntegers K B`. -/
def boundedSquareNormTranslationClasses (B : ℝ) :
    Finset (IntegerTranslationQuotient K) := by
  classical
  exact (boundedSquareNormIntegers_finite K B).toFinset.image
    (fun α : 𝓞 K ↦ (α : IntegerTranslationQuotient K))

/-- There is an injective family of algebraic integers `β q` bounded by `B` at every infinite place,
indexed by the bounded square-norm translation classes, such that the number of bounded
square-norm integers is at most the total number of points of height at most
`max (2 * B) (√(B ^ n))` on the signed norm curves for `β q` with signs `±1`. -/
theorem exists_norm_curve_family (B : ℝ) :
    ∃ β : (boundedSquareNormTranslationClasses K B) → 𝓞 K,
      Function.Injective β ∧
      (∀ q, ∀ w : InfinitePlace K, w (β q : K) ≤ B) ∧
      (boundedSquareNormIntegers K B).ncard ≤
        ∑ q : boundedSquareNormTranslationClasses K B,
          (count (signedNormCurveLocus K (β q) 1)
            (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) +
          count (signedNormCurveLocus K (β q) (-1))
            (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K)))) := by
  classical
  let S := boundedSquareNormIntegers K B
  let sf := (boundedSquareNormIntegers_finite K B).toFinset
  let Q := boundedSquareNormTranslationClasses K B
  have hex (q : Q) : ∃ r : 𝓞 K, r ∈ S ∧
      (r : IntegerTranslationQuotient K) = q.val := by
    obtain ⟨r, hr, hq⟩ := Finset.mem_image.mp q.property
    exact ⟨r, (boundedSquareNormIntegers_finite K B).mem_toFinset.mp hr, hq⟩
  choose r hr hq using hex
  let β : Q → 𝓞 K := fun q ↦ -r q
  have hinj : Function.Injective β := by
    intro q t h
    have he : r q = r t := neg_injective h
    apply Subtype.ext
    rw [← hq q, ← hq t, he]
  have hb (q : Q) (w : InfinitePlace K) : w (β q : K) ≤ B := by
    change w.val (-((r q : 𝓞 K) : K)) ≤ B
    rw [AbsoluteValue.map_neg]
    exact (hr q).2.1 w
  refine ⟨β, hinj, hb, ?_⟩
  let tf (q : Q) := (squareNormTranslateFiber_finite K (β q) B).toFinset
  have hcover : sf ⊆ Finset.univ.biUnion tf := by
    intro α hα
    have hαS : α ∈ S := (boundedSquareNormIntegers_finite K B).mem_toFinset.mp hα
    let q : Q := ⟨(α : IntegerTranslationQuotient K),
      Finset.mem_image.mpr ⟨α, hα, rfl⟩⟩
    have he : (α : IntegerTranslationQuotient K) = (r q : IntegerTranslationQuotient K) :=
      (hq q).symm
    obtain ⟨x, hx⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (QuotientAddGroup.eq_iff_sub_mem.mp he)
    have hx' : (x : 𝓞 K) = α - r q := by simpa using hx
    apply Finset.mem_biUnion.mpr
    refine ⟨q, Finset.mem_univ q,
      (squareNormTranslateFiber_finite K (β q) B).mem_toFinset.mpr ⟨hαS, x, ?_⟩⟩
    change α = algebraMap ℤ (𝓞 K) x - -r q
    change (algebraMap ℤ (𝓞 K) x) = α - r q at hx'
    rw [hx']
    abel
  calc
    S.ncard = sf.card := Set.ncard_eq_toFinset_card _ _
    _ ≤ (Finset.univ.biUnion tf).card := Finset.card_le_card hcover
    _ ≤ ∑ q : Q, (tf q).card := Finset.card_biUnion_le
    _ = ∑ q : Q, (squareNormTranslateFiber K (β q) B).ncard := by
      apply Finset.sum_congr rfl
      intro q _
      exact (Set.ncard_eq_toFinset_card _ _).symm
    _ ≤ _ := Finset.sum_le_sum (fun q _ ↦ squareNormTranslateFiber_count_le K (β q) (hb q))

end
end CCDN
