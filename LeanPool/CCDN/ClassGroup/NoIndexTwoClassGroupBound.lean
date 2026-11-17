/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.NoIndexTwoClassGroupCounting
public import LeanPool.CCDN.ClassGroup.NumberFieldLatticeBox
import LeanPool.CCDN.ClassGroup.BalancedGenerator
import LeanPool.CCDN.ClassGroup.DiscriminantNumerics
import LeanPool.CCDN.ClassGroup.NumberFieldShortBasis

/-!
The logarithmic branch of CCDN Theorem 6 for number fields with no
index-two intermediate field. All ideal-class representatives, curves,
lattice points and exceptional subfields are constructed and counted.

Uniform finite-radius counts for the ring of integers and its
integer-translation classes. The required short basis is constructed,
and every coefficient depends only on the degree.
-/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- For a number field `K` of degree `n ≥ 2` and a radius `B ≥ max 1 (|discr K| ^ (1 / n))`, the
number of bounded square-norm translation classes times `√|discr K|` is at most a constant
depending only on `n` times `B ^ (n - 1)`. -/
theorem boundedSquareNormTranslationClasses_uniform_count
    (hn : 2 ≤ Module.finrank ℚ K) {B : ℝ} (hB1 : 1 ≤ B)
    (hB : |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) ≤ B) :
    ((boundedSquareNormTranslationClasses K B).card : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
      (numberFieldLatticeBoxConstant (Module.finrank ℚ K) ((Module.finrank ℚ K : ℝ) ^ 3) *
        (2 : ℝ) ^ Module.finrank ℚ K) * B ^ (Module.finrank ℚ K - 1) := by
  obtain ⟨b, hb, hnorm⟩ := exists_numberField_short_basis K hn
  apply boundedSquareNormTranslationClasses_count_of_relative_short_basis K b hb hB1
    (by positivity)
  exact fun i ↦ (hnorm i).trans (mul_le_mul_of_nonneg_left hB (by positivity))

end
end CCDN

namespace CCDN
noncomputable section
open NumberField

/-- The degree-dependent constant in the two-torsion class-group bound for number fields of degree
`n` without an intermediate field of index two. -/
def noIndexTwoClassGroupConstant (n : ℕ) : ℝ :=
  (noIndexTwoCurveContributionConstant n *
    (numberFieldLatticeBoxConstant n ((n : ℝ) ^ 3) * (2 : ℝ) ^ n) *
      (3 * (9 : ℝ) ^ (n - 1))) * (Real.log 9 + 2) +
    smallSubfieldIntegerCountConstant n * (9 : ℝ) ^ ((n : ℝ) / 4)

/-- The constant `noIndexTwoClassGroupConstant n` is positive. -/
lemma noIndexTwoClassGroupConstant_pos (n : ℕ) :
    0 < noIndexTwoClassGroupConstant n := by
  have hc := noIndexTwoCurveContributionConstant_nonneg n
  have hb := numberFieldLatticeBoxConstant_nonneg n
    (by positivity : 0 ≤ (n : ℝ) ^ 3)
  have he := smallSubfieldIntegerCountConstant_pos n
  have hl : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  unfold noIndexTwoClassGroupConstant
  positivity

private lemma balanced_radius_log_le {D : ℝ} (hD : 0 < D) (hlog : 1 ≤ Real.log D)
    {n : ℕ} (hn : 0 < n) :
    Real.log (9 * D ^ (1 / (n : ℝ))) + 1 ≤
      (Real.log 9 + 2) * Real.log D := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hn1
  have hl9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hD _).ne',
    Real.log_rpow hD]
  nlinarith

variable (K : Type*) [Field K] [NumberField K]

/-- For a number field `K` of degree `n ≥ 2` with no intermediate field `L` of index `[K : L] = 2`,
the two-torsion subgroup of the class group has order at most
`C(n) * |discr K| ^ (1 / 2 - 1 / (2 * n)) * log |discr K|`. -/
theorem no_index_two_classGroup_two_torsion_bound
    (hn : 2 ≤ Module.finrank ℚ K)
    (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2) :
    (classGroupTwoTorsionCard K : ℝ) ≤
      noIndexTwoClassGroupConstant (Module.finrank ℚ K) *
        |(discr K : ℝ)| ^
          (1 / 2 - 1 / (2 * (Module.finrank ℚ K : ℝ))) *
            Real.log |(discr K : ℝ)| := by
  let n := Module.finrank ℚ K
  let D := |(discr K : ℝ)|
  let B := 9 * D ^ (1 / (n : ℝ))
  let P := noIndexTwoCurveContributionConstant n
  let A := numberFieldLatticeBoxConstant n ((n : ℝ) ^ 3) * (2 : ℝ) ^ n
  let E := smallSubfieldIntegerCountConstant n * (9 : ℝ) ^ ((n : ℝ) / 4)
  let a := 1 / 2 - 1 / (2 * (n : ℝ))
  have hnpos : 0 < n := by dsimp [n]; omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hD3 : 3 ≤ D := three_le_abs_discr K hn
  have hD1 : 1 ≤ D := by linarith
  have hD : 0 < D := by linarith
  have hlog : 1 ≤ Real.log D := one_le_log_abs_discr K hn
  have hroot : 1 ≤ D ^ (1 / (n : ℝ)) := Real.one_le_rpow hD1 (by positivity)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hBroot : D ^ (1 / (n : ℝ)) ≤ B := by dsimp [B]; linarith
  have hP : 0 ≤ P := noIndexTwoCurveContributionConstant_nonneg n
  have hA : 0 ≤ A := mul_nonneg
    (numberFieldLatticeBoxConstant_nonneg n (by positivity)) (by positivity)
  have hE : 0 ≤ E := mul_nonneg (smallSubfieldIntegerCountConstant_pos n).le (by positivity)
  have hlogB : 0 ≤ Real.log B + 1 := by linarith [Real.log_nonneg hB]
  have hS := boundedSquareNormIntegers_no_index_two_count K hnoTwo hn hB
  have hQ := boundedSquareNormTranslationClasses_uniform_count K hn hB hBroot
  have hmain :
      P * (boundedSquareNormTranslationClasses K B).card * Real.sqrt B *
          (Real.log B + 1) ≤
        (P * A * (3 * (9 : ℝ) ^ (n - 1))) * D ^ a * (Real.log B + 1) := by
    have hm := mul_le_mul_of_nonneg_left hQ
      (mul_nonneg (mul_nonneg hP (Real.sqrt_nonneg B)) hlogB)
    have hpre :
        (P * (boundedSquareNormTranslationClasses K B).card * Real.sqrt B *
            (Real.log B + 1)) * Real.sqrt D ≤
          (P * A * (Real.log B + 1)) *
            (B ^ (n - 1) * Real.sqrt B) := by
      convert hm using 1 <;> ring
    have hh := classGroup_discriminant_bound_of_balanced_radius hD hnpos hpre
    convert hh using 1
    ring
  have hmain' :
      P * (boundedSquareNormTranslationClasses K B).card * Real.sqrt B *
          (Real.log B + 1) ≤
        (P * A * (3 * (9 : ℝ) ^ (n - 1)) * (Real.log 9 + 2)) *
          D ^ a * Real.log D := by
    apply hmain.trans
    have hh := mul_le_mul_of_nonneg_left (balanced_radius_log_le hD hlog hnpos)
      (show 0 ≤ (P * A * (3 * (9 : ℝ) ^ (n - 1))) * D ^ a by positivity)
    convert hh using 1
    ring
  have hexc :
      ((boundedSmallSubfieldIntegers K B).ncard : ℝ) ≤ E * D ^ a * Real.log D := by
    have hh := boundedSmallSubfieldIntegers_balanced_count K hD1
    have ha : (1 / 4 : ℝ) ≤ a := by
      have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ 2 * n by linarith)
      dsimp [a]
      linarith
    have hp := Real.rpow_le_rpow_of_exponent_le hD1 ha
    calc
      _ ≤ E * D ^ (1 / 4 : ℝ) := hh
      _ ≤ E * D ^ a := mul_le_mul_of_nonneg_left hp hE
      _ ≤ E * D ^ a * Real.log D := le_mul_of_one_le_right (by positivity) hlog
  have hcard : (classGroupTwoTorsionCard K : ℝ) ≤
      (boundedSquareNormIntegers K B).ncard := by
    dsimp only [B, D, n]
    exact_mod_cast classGroupTwoTorsionCard_le_boundedSquareNormIntegers K
  calc
    _ ≤ _ := hcard.trans hS
    _ ≤ E * D ^ a * Real.log D +
        (P * A * (3 * (9 : ℝ) ^ (n - 1)) * (Real.log 9 + 2)) *
          D ^ a * Real.log D := add_le_add hexc hmain'
    _ = _ := by unfold noIndexTwoClassGroupConstant; dsimp [E, P, A, n, D, a]; ring

end
end CCDN
