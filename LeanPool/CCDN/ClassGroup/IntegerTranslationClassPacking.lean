/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.NormCurveReduction

/-! Integer translates pack each bounded square-norm translation class
into the full archimedean lattice box. This isolates the remaining geometric
lattice-point estimate from the already constructed norm-curve family. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

/-- The set of algebraic integers `α ∈ 𝓞 K` with `w α ≤ B` at every infinite place `w`. -/
def boundedArchimedeanIntegers (B : ℝ) : Set (𝓞 K) :=
  {α | ∀ w : InfinitePlace K, w (α : K) ≤ B}

/-- There are finitely many algebraic integers of `K` bounded by `B` at every infinite place. -/
lemma boundedArchimedeanIntegers_finite (B : ℝ) :
    (boundedArchimedeanIntegers K B).Finite := by
  apply Set.Finite.of_injOn (f := fun β : 𝓞 K ↦ (β : K))
    (t := {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B})
  · intro β hβ
    exact ⟨β.isIntegral_coe, fun φ ↦ hβ (InfinitePlace.mk φ)⟩
  · exact RingOfIntegers.coe_injective.injOn
  · exact Embeddings.finite_of_norm_le K ℂ B

/-- Translating representatives of the bounded square-norm translation classes by the integers in
`[-⌊R⌋, ⌊R⌋]` gives distinct algebraic integers bounded by `B + R` at every infinite place, so
the number of classes times `2 * ⌊R⌋ + 1` is at most the number of such integers. -/
theorem boundedSquareNormTranslationClasses_packing (B R : ℝ) :
    (boundedSquareNormTranslationClasses K B).card *
        (2 * ⌊R⌋ + 1).toNat ≤
      (boundedArchimedeanIntegers K (B + R)).ncard := by
  classical
  let Q := boundedSquareNormTranslationClasses K B
  let Z := Finset.Icc (-⌊R⌋) ⌊R⌋
  have hex (q : Q) : ∃ r : 𝓞 K, r ∈ boundedSquareNormIntegers K B ∧
      (r : IntegerTranslationQuotient K) = q.val := by
    obtain ⟨r, hr, hq⟩ := Finset.mem_image.mp q.property
    exact ⟨r, (boundedSquareNormIntegers_finite K B).mem_toFinset.mp hr, hq⟩
  choose r hr hq using hex
  have hzbound (z : Z) : |(z.val : ℝ)| ≤ R := by
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp z.property
    apply abs_le.mpr
    constructor
    · have hneg : -z.val ≤ ⌊R⌋ := by omega
      have h := Int.le_floor.mp hneg
      push_cast at h
      linarith
    · exact Int.le_floor.mp hu
  let a : Q × Z → 𝓞 K := fun t ↦ r t.1 + (t.2.val : 𝓞 K)
  have ha (t : Q × Z) : a t ∈ boundedArchimedeanIntegers K (B + R) := by
    intro w
    change w.val (((r t.1 : 𝓞 K) : K) + (t.2.val : K)) ≤ _
    calc
      _ ≤ w ((r t.1 : 𝓞 K) : K) + w (t.2.val : K) := w.val.add_le _ _
      _ = w ((r t.1 : 𝓞 K) : K) + |(t.2.val : ℝ)| := by
        rw [w.map_intCast, Int.norm_eq_abs]
      _ ≤ _ := add_le_add ((hr t.1).2.1 w) (hzbound t.2)
  have haQ (t : Q × Z) : (a t : IntegerTranslationQuotient K) = t.1.val := by
    have hz : ((t.2.val : 𝓞 K) : IntegerTranslationQuotient K) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr
        (AddSubgroup.intCast_mem_zmultiples_one t.2.val)
    change QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : 𝓞 K))
      (r t.1 + (t.2.val : 𝓞 K)) = _
    rw [map_add]
    change (r t.1 : IntegerTranslationQuotient K) +
      ((t.2.val : 𝓞 K) : IntegerTranslationQuotient K) = _
    rw [hz, add_zero, hq]
  have hi : Function.Injective a := by
    rintro ⟨q, z⟩ ⟨q', z'⟩ he
    have hqeq : q = q' := Subtype.ext (by
      rw [← haQ (q, z), ← haQ (q', z'), he])
    subst q'
    have hzeq : z = z' := by
      apply Subtype.ext
      exact Int.cast_injective (add_left_cancel he : (z.val : 𝓞 K) = (z'.val : 𝓞 K))
    subst z'
    rfl
  let ι : Q × Z → boundedArchimedeanIntegers K (B + R) := fun t ↦ ⟨a t, ha t⟩
  have hι : Function.Injective ι := fun s t h ↦ hi (congrArg Subtype.val h)
  let := (boundedArchimedeanIntegers_finite K (B + R)).fintype
  have hcard := Nat.card_le_card_of_injective ι hι
  have hZ : Z.card = (2 * ⌊R⌋ + 1).toNat := by
    simp only [Z, Int.card_Icc]
    congr 1
    omega
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe,
    Set.fintypeCard_eq_ncard, hZ] using hcard

end
end CCDN
