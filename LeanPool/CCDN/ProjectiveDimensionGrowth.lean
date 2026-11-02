/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Projection.ProjectiveProjectionGrowth
public import LeanPool.CCDN.Statements
import LeanPool.CCDN.Curve.ProjectiveHilbertCurveGrowth
import LeanPool.CCDN.Hilbert.EmptyProjectiveHilbertDimension
import LeanPool.CCDN.Hilbert.ProperHilbertDimension
import LeanPool.CCDN.Hypersurface.ProjectiveHypersurfaceDimensionGrowth
import LeanPool.CCDN.Hypersurface.ProjectiveVarietyDimensionGrowth
import LeanPool.CCDN.Projection.ZeroDimensionalProjectiveCount

/-! CCDN Theorem 1 in the homogeneous-coordinate-ideal formulation: uniform projective
dimension growth for every rational prime projective variety of degree at least five.
The Hilbert polynomial determines the degree and dimension. Zero-dimensional and empty
loci are included.

The bound is assembled once, in `projectiveGrowth_of_le`, for any degree exponent which
dominates the exponents of the zero-dimensional count, the curve bound, the hypersurface
bound and the projection bound. The degree exponent `2n² + 5n - 5` follows, and from it the
exponent `2n³`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Projective dimension growth with degree exponent `E` implies it with any larger exponent
`E'`. -/
theorem ProjectiveGrowth.mono {n E E' : ℕ} (h : ProjectiveGrowth n E) (hE : E ≤ E') :
    ProjectiveGrowth n E' := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun I hprime hI d hd hdegree B hB =>
    (hbound I hprime hI d hd hdegree B hB).trans ?_⟩
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  gcongr

/-- Theorem 1 holds with any degree exponent `E` which dominates, in `ℙⁿ`, the exponent
`n + 1` of the zero-dimensional count, the exponent `3(n+1) + 4` of the curve bound, the
exponent `18 + 3(n-2)` of the hypersurface bound, and the exponent of the projection bound
for every dimension `m + 1 ≥ 2` and codimension `k ≥ 2`. -/
theorem projectiveGrowth_of_le {n E : ℕ} (hpoint : 1 ≤ n → n + 1 ≤ E)
    (hcurve : 2 ≤ n → 3 * (n + 1) + 4 ≤ E)
    (hhyper : 3 ≤ n → 18 + 3 * (n - 2) ≤ E)
    (hproj : ∀ m k, m + k + 1 = n → 1 ≤ m → 2 ≤ k →
      projectionDegreeExponent m k ≤ E) :
    ProjectiveGrowth n E := by
  classical
  have hlt (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) (hI : I.IsPrime) (d : ℕ) (hd : 5 ≤ d)
      (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
      (filteredHilbertPolynomial I).natDegree < n + 1 := by
    simpa only [Fintype.card_fin] using
      hilbert_dimension_lt_ambient_of_degree_gt_one I hI.ne_top d (by omega) hdegree
  have hempty (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
      (h : (filteredHilbertPolynomial I).natDegree = 0) (B : ℝ) :
      projectiveCount (projectiveIdealZeroLocus I) B = 0 := by
    rw [projectiveIdealZeroLocus_eq_empty_of_hilbert_dimension_zero I h]
    simp [projectiveCount, projectivePoints]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_pos, fun I hprime _ d hd hdegree B _ => ?_⟩
    rw [hempty I (by have := hlt I hprime d hd hdegree; omega), Nat.cast_zero]
    positivity
  choose Cp _ hp using projective_variety_dimension_growth
  obtain ⟨T, hT⟩ := (((Set.finite_Iic n).prod (Set.finite_Iic n)).image
    fun p : ℕ × ℕ => Cp p.1 p.2).bddAbove
  obtain ⟨Cc, hCc, hc⟩ := projective_hilbert_curve_dimension_growth n hn
  choose Ch hCh hh using fun n => (projective_hypersurface_dimension_growth n).ideal
  let K : ℝ := max T 0 + Cc + Ch (n - 2) + 1
  have hTK : T ≤ K := by dsimp only [K]; linarith [le_max_left T 0, hCh (n - 2)]
  have h1K : 1 ≤ K := by dsimp only [K]; linarith [le_max_right T 0, hCh (n - 2)]
  have hCK : Cc ≤ K := by dsimp only [K]; linarith [le_max_right T 0, hCh (n - 2)]
  have hhK : Ch (n - 2) ≤ K := by dsimp only [K]; linarith [le_max_right T 0]
  refine ⟨K, by linarith, ?_⟩
  intro I hprime hI d hd hdegree B hB
  have : I.IsPrime := hprime
  -- Each dimension gives a bound with a constant at most `K` and an exponent at most `E`.
  suffices h : ∃ C : ℝ, C ≤ K ∧ ∃ e ≤ E,
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ e * B ^ ((filteredHilbertPolynomial I).natDegree - 1) by
    obtain ⟨C, hC, e, he, h⟩ := h
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (mul_le_mul_of_nonneg_right hC (by positivity)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd1 he) (by linarith))
  have hdim := hlt I hprime d hd hdegree
  obtain h0 | h1 | h2 | h3 : (filteredHilbertPolynomial I).natDegree = 0 ∨
      (filteredHilbertPolynomial I).natDegree = 1 ∨
      (filteredHilbertPolynomial I).natDegree = 2 ∨
      3 ≤ (filteredHilbertPolynomial I).natDegree := by omega
  · refine ⟨0, by linarith, 0, Nat.zero_le _, ?_⟩
    rw [hempty I h0, Nat.cast_zero, zero_mul, zero_mul]
  · refine ⟨1, h1K, n + 1, hpoint hn, ?_⟩
    have hbound := zero_dimensional_projective_count_le I d h1 (by
      simpa only [h1, Nat.factorial_one, Nat.cast_one, div_one] using hdegree) B
    rw [h1, Nat.sub_self, pow_zero, mul_one, one_mul]
    exact_mod_cast hbound
  · refine ⟨Cc, hCK, 3 * (n + 1) + 4, hcurve (by omega), ?_⟩
    rw [h2, show 2 - 1 = 1 from rfl, pow_one]
    exact hc I hprime hI d hd ⟨h2, by simpa only [h2] using hdegree⟩ B hB
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' h3
  obtain ⟨k, rfl⟩ : ∃ k, n = m + 1 + k + 1 := ⟨n - m - 2, by omega⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · -- A hypersurface.
    obtain rfl : k = 1 := by omega
    refine ⟨Ch (m + 1), by simpa using hhK, _, hhyper (by omega), ?_⟩
    rw [hm, show m + 1 + 1 + 1 - 2 = m + 1 by omega]
    exact hh (m + 1) I hprime hI d hd ⟨hm, by simpa only [hm] using hdegree⟩ B hB
  · -- Codimension at least two: the projection bound.
    have hmk : Cp (m + 1) k ≤ T := hT (Set.mem_image_of_mem (fun p : ℕ × ℕ => Cp p.1 p.2)
      (show (m + 1, k) ∈ Set.Iic _ ×ˢ Set.Iic _ from
        ⟨Set.mem_Iic.mpr (by omega), Set.mem_Iic.mpr (by omega)⟩))
    refine ⟨Cp (m + 1) k, hmk.trans hTK, _,
      hproj (m + 1) k rfl (by omega) hk, ?_⟩
    rw [hm]
    exact hp (m + 1) k I hprime hI d hd ⟨hm, by simpa only [hm] using hdegree⟩ B hB

/-- In `ℙⁿ` with `n = m + k + 1`, the projection exponent has the closed form
`2mn + 5m + 3n + 21`. For codimension `k ≥ 2` it is at most its value `2n² + 2n + 6` at
`k = 2`. -/
lemma projectiveProjectionDegreeExponent_le {m k n : ℕ} (h : m + k + 1 = n) (hk : 2 ≤ k) :
    projectionDegreeExponent m k ≤ 2 * n ^ 2 + 2 * n + 6 := by
  subst h
  unfold projectionDegreeExponent
  nlinarith

/-- The degree exponent `2n² + 5n - 5` of Theorem 1 in `ℙⁿ`. Its values `2` and `13` for
`n = 1, 2` are the exponents of the zero-dimensional count and of the curve bound. For
`n ≥ 4` it exceeds the projection exponent `2n² + 2n + 6` by `3n - 11`. -/
def projectiveGrowthExponent (n : ℕ) : ℕ := 2 * n ^ 2 + 5 * n - 5

/-- CCDN Theorem 1 with the degree exponent `2n² + 5n - 5` in every ambient projective
dimension `n`. -/
theorem projective_dimension_growth (n : ℕ) :
    ProjectiveGrowth n (projectiveGrowthExponent n) := by
  unfold projectiveGrowthExponent
  refine projectiveGrowth_of_le (fun hn => ?_) (fun hn => ?_) (fun hn => ?_)
    fun m k h hm hk => ?_
  · have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    omega
  · have : 4 ≤ n ^ 2 := by nlinarith
    omega
  · have : 9 ≤ n ^ 2 := by nlinarith
    omega
  · have := projectiveProjectionDegreeExponent_le h hk
    omega

end
end CCDN
