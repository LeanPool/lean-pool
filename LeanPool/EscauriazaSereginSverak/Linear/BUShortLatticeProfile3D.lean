/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortLatticeProfile
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortGaussianLattice3D
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# A fixed summable spatial lattice profile

The product reciprocal-square profile dominates Gaussian cell-center
weights at every dyadic scale.
-/

public section


noncomputable section

namespace ESS

/-- Product reciprocal-square profile on the three-dimensional grid. -/
@[expose] def buShortSpatialProfile (m : Fin 3 → ℤ) : ℝ :=
  buShortIntProfile (m 0) *
    (buShortIntProfile (m 1) * buShortIntProfile (m 2))

/-- The three-dimensional lattice profile is summable. -/
theorem bu_short_spatial_profile_summable : Summable buShortSpatialProfile := by
  have h := bu_short_int_profile_summable
  have h₁₂ : Summable (fun p : ℤ × ℤ =>
      buShortIntProfile p.1 * buShortIntProfile p.2) :=
    h.mul_of_nonneg h bu_short_int_profile_nonneg bu_short_int_profile_nonneg
  have h₀₁₂ : Summable (fun p : ℤ × (ℤ × ℤ) =>
      buShortIntProfile p.1 *
        (buShortIntProfile p.2.1 * buShortIntProfile p.2.2)) :=
    h.mul_of_nonneg h₁₂ bu_short_int_profile_nonneg
      (fun p => mul_nonneg (bu_short_int_profile_nonneg _)
        (bu_short_int_profile_nonneg _))
  have hcomp := h₀₁₂.comp_injective buShortIntTripleEquiv.injective
  apply hcomp.congr
  intro m
  rfl

/-- A half-integer Gaussian with width proportional to a dyadic scale
is controlled by the fixed profile and one inverse power of the scale. -/
theorem bu_short_scaled_half_gaussian_le_profile
    (a d : ℝ) (ha : 0 < a) (hd : 0 < d) (hd1 : d ≤ 1)
    (n : ℤ) :
    Real.exp (-(a * d * ((n : ℝ) + 1 / 2) ^ 2)) ≤
      (Real.exp (a / 4) * (a + 2) / (a * d)) *
        buShortIntProfile n := by
  have had : 0 < a * d := mul_pos ha hd
  have hbase := bu_short_half_gaussian_le_profile (a * d) had n
  have hexp : Real.exp (a * d / 4) ≤ Real.exp (a / 4) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hd1 ha.le]
  have hfactor : 1 + 2 / (a * d) ≤ (a + 2) / (a * d) := by
    apply (le_div_iff₀ had).mpr
    have h2 : (2 / (a * d)) * (a * d) = 2 := div_mul_cancel₀ 2 had.ne'
    nlinarith only [mul_le_mul_of_nonneg_left hd1 ha.le, h2]
  have hprod : Real.exp (a * d / 4) *
      (1 + 2 / (a * d)) ≤
      Real.exp (a / 4) * ((a + 2) / (a * d)) := by
    apply mul_le_mul hexp hfactor
    · positivity
    · exact Real.exp_nonneg _
  calc
    _ ≤ Real.exp (a * d / 4) *
        (1 + 2 / (a * d)) * buShortIntProfile n := hbase
    _ ≤ (Real.exp (a / 4) * (a + 2) / (a * d)) *
        buShortIntProfile n := by
          have h := mul_le_mul_of_nonneg_right hprod
            (bu_short_int_profile_nonneg n)
          simpa only [mul_div_assoc] using h

end ESS

noncomputable section

namespace ESS

/-- A separable dyadic Gaussian on three grid coordinates is bounded by
a fixed summable profile with a quadratic inverse-scale factor. -/
theorem bu_short_separable_gaussian_le_profile
    (a b d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) (hd1 : d ≤ 1) (m : Fin 3 → ℤ) :
    Real.exp (-(a * d * ((m 0 : ℝ) + 1 / 2) ^ 2)) *
        (Real.exp (-(a * d * ((m 1 : ℝ) + 1 / 2) ^ 2)) *
          Real.exp (-(b * ((m 2 : ℝ) + 1 / 2) ^ 2))) ≤
      ((Real.exp (a / 4) * (a + 2) / (a * d)) ^ 2 *
        (Real.exp (b / 4) * (1 + 2 / b))) *
          buShortSpatialProfile m := by
  let K := Real.exp (a / 4) * (a + 2) / (a * d)
  let L := Real.exp (b / 4) * (1 + 2 / b)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have h0 := bu_short_scaled_half_gaussian_le_profile a d ha hd hd1 (m 0)
  have h1 := bu_short_scaled_half_gaussian_le_profile a d ha hd hd1 (m 1)
  have h2 := bu_short_half_gaussian_le_profile b hb (m 2)
  have h12 : Real.exp (-(a * d * ((m 1 : ℝ) + 1 / 2) ^ 2)) *
      Real.exp (-(b * ((m 2 : ℝ) + 1 / 2) ^ 2)) ≤
      (K * buShortIntProfile (m 1)) *
        (L * buShortIntProfile (m 2)) := by
    exact mul_le_mul h1 h2 (Real.exp_nonneg _)
      (mul_nonneg hK (bu_short_int_profile_nonneg _))
  have h012 := mul_le_mul h0 h12
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    (mul_nonneg hK (bu_short_int_profile_nonneg _))
  calc
    _ ≤ (K * buShortIntProfile (m 0)) *
        ((K * buShortIntProfile (m 1)) *
          (L * buShortIntProfile (m 2))) := h012
    _ = _ := by
      dsimp [K, L, buShortSpatialProfile]
      ring

end ESS
