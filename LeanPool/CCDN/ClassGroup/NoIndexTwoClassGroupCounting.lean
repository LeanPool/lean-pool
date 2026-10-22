/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.SmallSubfieldIntegerCount
public import LeanPool.CCDN.Plane.AffineNonzeroConstant
import LeanPool.CCDN.ClassGroup.NormCurveExceptionalReduction
import LeanPool.CCDN.ClassGroup.OddDegreeClassGroupCounting
import LeanPool.CCDN.ClassGroup.OddDegreeNormCurveBaseChange
import LeanPool.CCDN.ClassGroup.SquareNormCurveIrreducibility
import LeanPool.CCDN.Plane.CurveCount

/-!
Counting the bounded square-norm integers in the absence of
an index-two subfield. Ordinary norm curves and small-subfield exceptions
are both counted by proved estimates.

Uniform counts for signed norm curves whose parameter generates a
subfield of odd index. The ambient field degree may be even.
-/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField IntermediateField

/-- The absolute constant in the count of integral points on signed norm curves whose parameter
generates a subfield of odd index. -/
def oddIndexNormCurveCountConstant : ℝ :=
  2 * Real.exp 1 * affineNonzeroConstantBound planeResidueConstant

private lemma oddIndexNormCurveCountConstant_pos : 0 < oddIndexNormCurveCountConstant :=
  mul_pos (by positivity) (affineNonzeroConstantBound_pos planeResidueConstant)

/-- If `[K : ℚ(β)]` is odd, `n = [K : ℚ] ≥ 2` and `ε ≠ 0`, then the signed norm curve
`y ^ 2 = ε * N(x - β)` has at most `C * n ^ 3 * B ^ (1 / n) * (log B + n)` integral points of
height at most `B ≥ 1`. -/
theorem signed_norm_curve_count_of_odd_subfield_index
    (K : Type*) [Field K] [NumberField K]
    (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hn : 2 ≤ Module.finrank ℚ K)
    (hindex : Odd (Module.finrank ℚ⟮(β : K)⟯ K))
    {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ)
      (signedNormCurvePolynomial K β ε))) B : ℝ) ≤
      oddIndexNormCurveCountConstant * (Module.finrank ℚ K : ℝ) ^ 3 *
        B ^ (1 / (Module.finrank ℚ K : ℝ)) *
          (Real.log B + Module.finrank ℚ K) := by
  have hεQ : (ε : ℚ) ≠ 0 := by exact_mod_cast hε
  have hd := signedNormCurvePolynomial_map_totalDegree K ℚ β hεQ hn
  have hir : AbsolutelyIrreducibleRat
      (MvPolynomial.map (Int.castRingHom ℚ) (signedNormCurvePolynomial K β ε)) :=
    (absolutelyIrreducibleRat_map_iff _).mpr
      (signedNormCurvePolynomial_absolute_irreducible_of_odd_subfield_index K β hε hindex)
  have h := count_rational_plane_of_residue_bound _ hir (by omega) hB
    planeResidueConstant_pos.le planeResidueBound
  rw [hd] at h
  simpa only [curveBound, oddIndexNormCurveCountConstant, mul_assoc] using h

end
end CCDN

namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace
open scoped IntermediateField

private lemma normCurveBoxHeight_log_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    Real.log (max (2 * B) (Real.sqrt (B ^ n))) + n ≤
      2 * (n : ℝ) * (Real.log B + 1) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hbase : 1 ≤ 2 * B := by linarith
  have hpow : 1 ≤ B ^ n := one_le_pow₀ hB
  have hH : max (2 * B) (Real.sqrt (B ^ n)) ≤ (2 * B) ^ n := by
    apply max_le
    · simpa using pow_le_pow_right₀ hbase (by omega : 1 ≤ n)
    · have hs : Real.sqrt (B ^ n) ≤ B ^ n :=
        (Real.sqrt_le_left (by positivity)).mpr (by nlinarith)
      exact hs.trans (pow_le_pow_left₀ hB0.le (by linarith) n)
  have hlog := Real.log_le_log (show 0 < max (2 * B) (Real.sqrt (B ^ n)) from
    lt_of_lt_of_le (by positivity) (le_max_left _ _)) hH
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hB0.ne'] at hlog
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hlogB := Real.log_nonneg hB
  nlinarith

/-- The degree-dependent constant bounding the contribution of one integer-translation class to the
bounded square-norm count for fields of degree `n` without an index-two subfield. -/
def noIndexTwoCurveContributionConstant (n : ℕ) : ℝ :=
  8 * oddIndexNormCurveCountConstant * (n : ℝ) ^ 4

/-- The constant `noIndexTwoCurveContributionConstant n` is nonnegative. -/
lemma noIndexTwoCurveContributionConstant_nonneg (n : ℕ) :
    0 ≤ noIndexTwoCurveContributionConstant n := by
  have := oddIndexNormCurveCountConstant_pos
  unfold noIndexTwoCurveContributionConstant
  positivity

variable (K : Type*) [Field K] [NumberField K]

/-- For a number field of degree `n ≥ 2` without an intermediate field of index two and `B ≥ 1`, the
number of bounded square-norm integers is at most the number of bounded integers in small
subfields plus `C(n)` times the number of translation classes times `√B * (log B + 1)`. -/
theorem boundedSquareNormIntegers_no_index_two_count
    (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2)
    (hn : 2 ≤ Module.finrank ℚ K) {B : ℝ} (hB : 1 ≤ B) :
    ((boundedSquareNormIntegers K B).ncard : ℝ) ≤
      (boundedSmallSubfieldIntegers K B).ncard +
      noIndexTwoCurveContributionConstant (Module.finrank ℚ K) *
        (boundedSquareNormTranslationClasses K B).card *
          Real.sqrt B * (Real.log B + 1) := by
  obtain ⟨β, _, _, hcover⟩ := exists_norm_curve_exception_split K hnoTwo B
  let n := Module.finrank ℚ K
  let H := max (2 * B) (Real.sqrt (B ^ n))
  have hH : 1 ≤ H := le_trans (by linarith) (le_max_left _ _)
  have hroot := normCurveBoxHeight_root_le hn hB
  have hlog := normCurveBoxHeight_log_le hn hB
  have hC : 0 ≤ oddIndexNormCurveCountConstant * (n : ℝ) ^ 3 := by
    have := oddIndexNormCurveCountConstant_pos
    positivity
  have hmain : 0 ≤ noIndexTwoCurveContributionConstant n *
      Real.sqrt B * (Real.log B + 1) :=
    mul_nonneg (mul_nonneg (noIndexTwoCurveContributionConstant_nonneg n)
      (Real.sqrt_nonneg B)) (by linarith [Real.log_nonneg hB])
  have hpair (q : boundedSquareNormTranslationClasses K B) :
      ((if Odd (Module.finrank ℚ⟮(β q : K)⟯ K) then
        count (signedNormCurveLocus K (β q) 1) H +
          count (signedNormCurveLocus K (β q) (-1)) H else 0 : ℕ) : ℝ) ≤
      noIndexTwoCurveContributionConstant n * Real.sqrt B * (Real.log B + 1) := by
    by_cases ho : Odd (Module.finrank ℚ⟮(β q : K)⟯ K)
    · simp only [ite_eq_left ho, Nat.cast_add]
      have hp := signed_norm_curve_count_of_odd_subfield_index K (β q)
        (ε := 1) (by norm_num) hn ho hH
      have hm := signed_norm_curve_count_of_odd_subfield_index K (β q)
        (ε := -1) (by norm_num) hn ho hH
      change (count (signedNormCurveLocus K (β q) 1) H : ℝ) ≤ _ at hp
      change (count (signedNormCurveLocus K (β q) (-1)) H : ℝ) ≤ _ at hm
      have hprod : H ^ (1 / (n : ℝ)) * (Real.log H + n) ≤
          (2 * Real.sqrt B) * (2 * (n : ℝ) * (Real.log B + 1)) :=
        mul_le_mul hroot hlog
          (by have hh := Real.log_nonneg hH; positivity) (by positivity)
      have hh := mul_le_mul_of_nonneg_left hprod (show
        0 ≤ 2 * (oddIndexNormCurveCountConstant * (n : ℝ) ^ 3) by positivity)
      calc
        _ ≤ 2 * (oddIndexNormCurveCountConstant * (n : ℝ) ^ 3) *
            (H ^ (1 / (n : ℝ)) * (Real.log H + n)) := by linarith
        _ ≤ _ := hh
        _ = _ := by unfold noIndexTwoCurveContributionConstant; ring
    · simpa only [ite_eq_right ho, Nat.cast_zero] using hmain
  have hcoverR :
      ((boundedSquareNormIntegers K B).ncard : ℝ) ≤
        (boundedSmallSubfieldIntegers K B).ncard +
          ∑ q : boundedSquareNormTranslationClasses K B,
            ((if Odd (Module.finrank ℚ⟮(β q : K)⟯ K) then
              count (signedNormCurveLocus K (β q) 1) H +
                count (signedNormCurveLocus K (β q) (-1)) H else 0 : ℕ) : ℝ) := by
    exact_mod_cast hcover
  calc
    _ ≤ _ := hcoverR
    _ ≤ (boundedSmallSubfieldIntegers K B).ncard +
        ∑ _q : boundedSquareNormTranslationClasses K B,
          noIndexTwoCurveContributionConstant n * Real.sqrt B * (Real.log B + 1) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun q _ ↦ hpair q))
    _ = _ := by simp; ring

end
end CCDN
