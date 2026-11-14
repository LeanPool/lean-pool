/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.IntegerTranslationClassPacking
import LeanPool.CCDN.ClassGroup.SubfieldBoundedIntegers
import LeanPool.CCDN.ForMathlib.FieldTheory

/-! Parameters lying in intermediate fields of degree at most one
quarter of the ambient degree have a uniform fourth-root contribution
at the balanced discriminant radius. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField

private lemma small_dimension_packing_bound {m n : ℕ} (hm : 4 * m ≤ n)
    {B : ℝ} (hB : 1 ≤ B) :
    (2 * Real.sqrt (m : ℝ) * B + 1) ^ m ≤
      (2 * Real.sqrt (n : ℝ) + 1) ^ n * B ^ ((n : ℝ) / 4) := by
  have hmn : m ≤ n := by omega
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hsq : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (Nat.cast_le.mpr hmn)
  have hc : 1 ≤ 2 * Real.sqrt (n : ℝ) + 1 := by
    linarith [Real.sqrt_nonneg (n : ℝ)]
  have hbase : 2 * Real.sqrt (m : ℝ) * B + 1 ≤
      (2 * Real.sqrt (n : ℝ) + 1) * B := by nlinarith
  have hexp : (m : ℝ) ≤ (n : ℝ) / 4 := by
    have hh : 4 * (m : ℝ) ≤ n := by exact_mod_cast hm
    linarith
  calc
    _ ≤ ((2 * Real.sqrt (n : ℝ) + 1) * B) ^ m :=
      pow_le_pow_left₀ (by positivity) hbase m
    _ = (2 * Real.sqrt (n : ℝ) + 1) ^ m * B ^ m := mul_pow _ _ _
    _ ≤ (2 * Real.sqrt (n : ℝ) + 1) ^ n * B ^ ((n : ℝ) / 4) := by
      apply mul_le_mul (pow_le_pow_right₀ hc hmn) _ (by positivity) (by positivity)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hB hexp

variable (K : Type*) [Field K] [NumberField K]

/-- The algebraic integers of `K` bounded by `B` at every infinite place that lie in an intermediate
field `L` with `4 * [L : ℚ] ≤ [K : ℚ]`. -/
def boundedSmallSubfieldIntegers (B : ℝ) : Set (𝓞 K) :=
  {β | β ∈ boundedArchimedeanIntegers K B ∧
    ∃ L : IntermediateField ℚ K,
      4 * Module.finrank ℚ L ≤ Module.finrank ℚ K ∧ (β : K) ∈ L}

/-- The set `boundedSmallSubfieldIntegers K B` is finite. -/
lemma boundedSmallSubfieldIntegers_finite (B : ℝ) :
    (boundedSmallSubfieldIntegers K B).Finite :=
  (boundedArchimedeanIntegers_finite K B).subset (fun _ h ↦ h.1)

/-- The constant `2 ^ n * (2 * √n + 1) ^ n` in the count of bounded integers in small subfields of
a number field of degree `n`. -/
def smallSubfieldIntegerCountConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (2 * Real.sqrt (n : ℝ) + 1) ^ n

/-- The constant `smallSubfieldIntegerCountConstant n` is positive. -/
lemma smallSubfieldIntegerCountConstant_pos (n : ℕ) :
    0 < smallSubfieldIntegerCountConstant n := by
  unfold smallSubfieldIntegerCountConstant
  positivity

private theorem boundedSmallSubfieldIntegers_count {B : ℝ} (hB : 1 ≤ B) :
    ((boundedSmallSubfieldIntegers K B).ncard : ℝ) ≤
      smallSubfieldIntegerCountConstant (Module.finrank ℚ K) *
        B ^ ((Module.finrank ℚ K : ℝ) / 4) := by
  classical
  let T := {L : IntermediateField ℚ K //
    4 * Module.finrank ℚ L ≤ Module.finrank ℚ K}
  let : Finite (IntermediateField ℚ K) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ K
      (Field.exists_primitive_element ℚ K)
  let : Fintype (IntermediateField ℚ K) := Fintype.ofFinite _
  let : Fintype T := Fintype.ofFinite _
  let sf := (boundedSmallSubfieldIntegers_finite K B).toFinset
  let tf (L : T) := (boundedIntegersInSubfield_finite K L.val B).toFinset
  have hcover : sf ⊆ Finset.univ.biUnion tf := by
    intro β hβ
    have hh := (boundedSmallSubfieldIntegers_finite K B).mem_toFinset.mp hβ
    obtain ⟨L, hL, hβL⟩ := hh.2
    exact Finset.mem_biUnion.mpr ⟨⟨L, hL⟩, Finset.mem_univ _,
      (boundedIntegersInSubfield_finite K L B).mem_toFinset.mpr ⟨hh.1, hβL⟩⟩
  have hcard : Fintype.card T ≤ 2 ^ Module.finrank ℚ K := by
    calc
      _ ≤ Fintype.card (IntermediateField ℚ K) := Fintype.card_subtype_le _
      _ = Nat.card (IntermediateField ℚ K) := Nat.card_eq_fintype_card.symm
      _ ≤ _ := IntermediateField.card_le_two_pow_finrank ℚ K
  have hterm (L : T) :
      ((tf L).card : ℝ) ≤
        (2 * Real.sqrt (Module.finrank ℚ K : ℝ) + 1) ^ Module.finrank ℚ K *
          B ^ ((Module.finrank ℚ K : ℝ) / 4) := by
    have hh := (boundedIntegersInSubfield_count K L.val (zero_le_one.trans hB)).trans
      (small_dimension_packing_bound L.property hB)
    simpa only [tf, ← Set.ncard_eq_toFinset_card] using hh
  have hcount : (sf.card : ℝ) ≤ ∑ L : T, ((tf L).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  calc
    _ = (sf.card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ (boundedSmallSubfieldIntegers_finite K B)]
    _ ≤ _ := hcount
    _ ≤ ∑ _L : T,
        (2 * Real.sqrt (Module.finrank ℚ K : ℝ) + 1) ^ Module.finrank ℚ K *
          B ^ ((Module.finrank ℚ K : ℝ) / 4) :=
      Finset.sum_le_sum (fun L _ ↦ hterm L)
    _ = (Fintype.card T : ℝ) *
        ((2 * Real.sqrt (Module.finrank ℚ K : ℝ) + 1) ^ Module.finrank ℚ K *
          B ^ ((Module.finrank ℚ K : ℝ) / 4)) := by simp
    _ ≤ (2 : ℝ) ^ Module.finrank ℚ K *
        ((2 * Real.sqrt (Module.finrank ℚ K : ℝ) + 1) ^ Module.finrank ℚ K *
          B ^ ((Module.finrank ℚ K : ℝ) / 4)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = _ := by unfold smallSubfieldIntegerCountConstant; ring

/-- At the balanced radius `9 * D ^ (1 / n)` with `D ≥ 1` and `n = [K : ℚ]`, the number of bounded
integers in small subfields is at most a constant depending only on `n` times `D ^ (1 / 4)`. -/
theorem boundedSmallSubfieldIntegers_balanced_count {D : ℝ} (hD : 1 ≤ D) :
    ((boundedSmallSubfieldIntegers K
        (9 * D ^ (1 / (Module.finrank ℚ K : ℝ)))).ncard : ℝ) ≤
      (smallSubfieldIntegerCountConstant (Module.finrank ℚ K) *
        (9 : ℝ) ^ ((Module.finrank ℚ K : ℝ) / 4)) * D ^ (1 / 4 : ℝ) := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hB : 1 ≤ 9 * D ^ (1 / (Module.finrank ℚ K : ℝ)) := by
    have hh := Real.one_le_rpow hD (by positivity : 0 ≤ 1 / (Module.finrank ℚ K : ℝ))
    linarith
  have hh := boundedSmallSubfieldIntegers_count K hB
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) (Real.rpow_nonneg hD0.le _),
    ← Real.rpow_mul hD0.le] at hh
  have he : 1 / (Module.finrank ℚ K : ℝ) *
      ((Module.finrank ℚ K : ℝ) / 4) = 1 / 4 := by field_simp
  rw [he] at hh
  convert hh using 1
  ring

end
end CCDN
