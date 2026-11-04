/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.IntegerTranslationClassPacking
import LeanPool.CCDN.ClassGroup.SeparatedIntegerPacking

/-! Bounded algebraic integers lying in an intermediate field
inject into the bounded integers of that field. Every archimedean place
of the subfield is obtained by restricting an ambient place. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

/-- The algebraic integers of `K` bounded by `B` at every infinite place that lie in the
intermediate field `L`. -/
def boundedIntegersInSubfield (L : IntermediateField ℚ K) (B : ℝ) : Set (𝓞 K) :=
  {β | β ∈ boundedArchimedeanIntegers K B ∧ (β : K) ∈ L}

/-- The set `boundedIntegersInSubfield K L B` is finite. -/
lemma boundedIntegersInSubfield_finite (L : IntermediateField ℚ K) (B : ℝ) :
    (boundedIntegersInSubfield K L B).Finite :=
  (boundedArchimedeanIntegers_finite K B).subset (fun _ h ↦ h.1)

/-- The map sending a bounded algebraic integer of `K` lying in `L` to the same element viewed as a
bounded algebraic integer of `L`; every infinite place of `L` is restricted from one of `K`. -/
def boundedIntegerToSubfield (L : IntermediateField ℚ K) (B : ℝ) :
    boundedIntegersInSubfield K L B → boundedArchimedeanIntegers L B := fun β ↦ by
  let γ : L := ⟨(β.val : K), β.property.2⟩
  have hγ : γ ∈ integralClosure ℤ L := by
    change IsIntegral ℤ γ
    apply (isIntegral_algebraMap_iff (R := ℤ) (A := L) (B := K)).mp
    exact β.val.isIntegral_coe
  let z : 𝓞 L := ⟨γ, hγ⟩
  refine ⟨z, ?_⟩
  intro w
  obtain ⟨v, rfl⟩ := InfinitePlace.comap_surjective (K := K) w
  rw [comap_apply]
  change v (algebraMap L K (z : L)) ≤ B
  rw [show (z : L) = γ from RingOfIntegers.coe_mk hγ]
  exact β.property.1 v

/-- The map `boundedIntegerToSubfield` does not change the underlying element of `K`. -/
@[simp] lemma boundedIntegerToSubfield_coe (L : IntermediateField ℚ K) (B : ℝ)
    (β : boundedIntegersInSubfield K L B) :
    (((boundedIntegerToSubfield K L B β).val : L) : K) = (β.val : K) := by
  rfl

private lemma boundedIntegerToSubfield_injective (L : IntermediateField ℚ K) (B : ℝ) :
    Function.Injective (boundedIntegerToSubfield K L B) := by
  intro x y h
  apply Subtype.ext
  apply RingOfIntegers.coe_injective
  simpa only [boundedIntegerToSubfield_coe] using
    congrArg (fun z : boundedArchimedeanIntegers L B ↦ ((z.val : L) : K)) h

private theorem boundedIntegersInSubfield_ncard_le (L : IntermediateField ℚ K) (B : ℝ) :
    (boundedIntegersInSubfield K L B).ncard ≤
      (boundedArchimedeanIntegers L B).ncard := by
  let := (boundedIntegersInSubfield_finite K L B).fintype
  let := (boundedArchimedeanIntegers_finite L B).fintype
  simpa only [Set.fintypeCard_eq_ncard] using
    Fintype.card_le_of_injective (boundedIntegerToSubfield K L B)
      (boundedIntegerToSubfield_injective K L B)

/-- For `B ≥ 0`, the number of algebraic integers of `K` bounded by `B` at every infinite place and
lying in `L` is at most `(2 * √m * B + 1) ^ m`, where `m = [L : ℚ]`. -/
theorem boundedIntegersInSubfield_count (L : IntermediateField ℚ K)
    {B : ℝ} (hB : 0 ≤ B) :
    ((boundedIntegersInSubfield K L B).ncard : ℝ) ≤
      (2 * Real.sqrt (Module.finrank ℚ L) * B + 1) ^ Module.finrank ℚ L :=
  (Nat.cast_le.mpr (boundedIntegersInSubfield_ncard_le K L B)).trans
    (boundedArchimedeanIntegers_separated_count L hB)

end
end CCDN
