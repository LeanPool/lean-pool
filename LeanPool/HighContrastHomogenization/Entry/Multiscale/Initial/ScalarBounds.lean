/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.PositiveGapSupport
public import LeanPool.HighContrastHomogenization.Entry.Analysis.ReferenceComparison
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormFoundations
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedDomainLocality
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Entry.Annealed.Normalization
public import LeanPool.HighContrastHomogenization.Entry.Annealed.ReferenceNormalization
public import LeanPool.HighContrastHomogenization.Entry.Geometry.CanonicalMetricBounds
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.Geometry.ProjectiveMetric
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridComparison
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.DriftAdvance
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.SelectionExponentBounds
public import LeanPool.HighContrastHomogenization.Entry.Setup.SelectionData
public import LeanPool.HighContrastHomogenization.Entry.Source.AdaptedBound
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.PositiveGapClosure
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# High-contrast homogenization: Entry.Multiscale.Initial.ScalarBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Initialization: deterministic scalar, telescoping and block helpers

Deterministic arithmetic used by the initialization route for the fixed-grid scale
`HCPoly/Entry/Statements/InitialFixedGridScale.lean` (`p.initial.fixed.grid.scale`): logarithm and
`logb` comparisons, the `1 + t ≤ exp t` scalar decrement of `p.initial.fixed.grid.scale`, the
good-index extraction of `p.initial.fixed.grid.scale`, integer telescoping, geometric weight
sums, and the block trace and mean-penalty bounds under a Loewner scale bound.

No probability law and no annealed premise enters any statement of this file.
-/

open HCPolySupport.HighContrast (blockLogDet blockMatEntry_blockScale blockScale blockSub
  blockTrace blockVecDot_blockMatVecMul_eq_sum matSqrt normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-! ## A. Deterministic scalar and matrix helpers -/

/-- A1. The source threshold is monotone in the constant (`1 < K` gives `log₃(2K) ≥ 0`). -/
theorem ceil_source_threshold_le_of_le (K : ℝ) (hK : 1 < K) (a b : ℝ) (hab : a ≤ b) (j : ℤ)
    (hb : ⌈b * Real.logb 3 (2 * K)⌉ ≤ j) :
    ⌈a * Real.logb 3 (2 * K)⌉ ≤ j := by
  have h : 0 ≤ Real.logb 3 (2 * K) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hK])
  exact le_trans (Int.ceil_le_ceil (mul_le_mul_of_nonneg_right hab h)) hb

/-- A2. `log₃(2+Π) ≥ 1` whenever `2+Π ≥ 3` (`p.initial.fixed.grid.scale`). -/
theorem one_le_logb_three_of_three_le (x : ℝ) (hx : 3 ≤ x) : 1 ≤ Real.logb 3 x := by
  rw [Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 3) (by linarith only [hx] : (0:ℝ) < x)]
  simp only [Real.rpow_one]
  exact hx

/-- A3. `log(24Π) ≤ C log₃(2+Π)` with the printed-size constant. -/
theorem log_aspect_le_logb (Pi : ℝ) (hPi : 1 ≤ Pi) :
    Real.log (24 * Pi) ≤ (Real.log 24 + Real.log 3) * Real.logb 3 (2 + Pi) := by
  have hPi_pos : 0 < Pi := by linarith only [hPi]
  have log_3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have log_24_pos : 0 < Real.log 24 := Real.log_pos (by norm_num)
  have h3_le : Real.log 3 ≤ Real.log (2 + Pi) := Real.log_le_log (by norm_num) (by linarith only
    [hPi])
  have hPi_le : Real.log Pi ≤ Real.log (2 + Pi) := Real.log_le_log hPi_pos (by linarith only [])
  rw [Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) (by linarith only [hPi] : Pi ≠ 0)]
  unfold Real.logb
  rw [← mul_div_assoc, le_div_iff₀ log_3_pos]
  have t1 : Real.log 24 * Real.log 3 ≤ Real.log 24 * Real.log (2 + Pi) :=
    mul_le_mul_of_nonneg_left h3_le log_24_pos.le
  have t2 : Real.log Pi * Real.log 3 ≤ Real.log (2 + Pi) * Real.log 3 :=
    mul_le_mul_of_nonneg_right hPi_le log_3_pos.le
  calc (Real.log 24 + Real.log Pi) * Real.log 3
      = Real.log 24 * Real.log 3 + Real.log Pi * Real.log 3 := by ring
    _ ≤ Real.log 24 * Real.log (2 + Pi) + Real.log (2 + Pi) * Real.log 3 := add_le_add t1 t2
    _ = (Real.log 24 + Real.log 3) * Real.log (2 + Pi) := by ring

/-- A4. `½ log(24Π) ≤ log(2+4Π)` (the `24Π` normalization enters the entry radius). -/
theorem half_log_aspect_le (Pi : ℝ) (hPi : 1 ≤ Pi) :
    1 / 2 * Real.log (24 * Pi) ≤ Real.log (2 + 4 * Pi) := by
  have h1 : 0 < 24 * Pi := by nlinarith only [hPi]
  have h2 : 6 ≤ 2 + 4 * Pi := by linarith only [hPi]
  have h3 : 24 * Pi ≤ 6 * (2 + 4 * Pi) := by nlinarith only [hPi]
  have h4 : 0 < (6 : ℝ) := by norm_num
  have h5 : Real.log (24 * Pi) ≤ Real.log (6 * (2 + 4 * Pi)) :=
    Real.log_le_log h1 h3
  have h6 : (6 : ℝ) ≠ 0 := by norm_num
  have h7 : 2 + 4 * Pi ≠ 0 := by linarith only [hPi]
  rw [Real.log_mul h6 h7] at h5
  have h8 : Real.log 6 ≤ Real.log (2 + 4 * Pi) := Real.log_le_log h4 h2
  calc 1 / 2 * Real.log (24 * Pi)
    ≤ 1 / 2 * (Real.log 6 + Real.log (2 + 4 * Pi)) :=
      mul_le_mul_of_nonneg_left h5 (by norm_num)
    _ = 1 / 2 * Real.log 6 + 1 / 2 * Real.log (2 + 4 * Pi) := by ring
    _ ≤ 1 / 2 * Real.log (2 + 4 * Pi) + 1 / 2 * Real.log (2 + 4 * Pi) := by linarith only [h8]
    _ = Real.log (2 + 4 * Pi) := by ring

/-- A5. Polynomial bookkeeping in `Π`: `(cΠ)^k ≤ c^k (2+Π)^k`. -/
theorem aspect_pow_le_two_add_pow (Pi : ℝ) (hPi : 1 ≤ Pi) (c : ℝ) (hc : 1 ≤ c) (k : ℕ) :
    (c * Pi) ^ k ≤ c ^ k * (2 + Pi) ^ k := by
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_left₀ (by linarith only [hPi]) (by linarith only []) k
  · positivity

/-- A6. The elementary scalar calculation of `p.initial.fixed.grid.scale`. -/
theorem scalar_log_decrement (Q C₀ x x' y : ℝ) (hQ : 0 ≤ Q) (hC₀ : 0 ≤ C₀) (hx : 1 ≤ x)
    (hy : 0 ≤ y) (hx' : 0 ≤ x')
    (h : x' ≤ 1 / 8 * Real.exp (Q * y) * x + C₀ * (Real.exp (Q * y) - 1)) :
    Real.log (1 + x') ≤
      Real.log (1 + x) - Real.log (16 / 9) + (Q + 8 / 9 * C₀ * Q) * y := by
  have hQy : (0:ℝ) ≤ Q*y := mul_nonneg hQ hy
  have h1 : (1:ℝ) ≤ Real.exp (Q*y) := Real.one_le_exp hQy
  have h2 : (0:ℝ) ≤ Real.exp (Q*y) - 1 := by linarith only [h1]
  have h3 : (0:ℝ) ≤ C₀ * (Real.exp (Q*y) - 1) := mul_nonneg hC₀ h2
  have h4 : (0:ℝ) ≤ 1/8 * Real.exp (Q*y) * x := by positivity
  have h_x'_pos : 0 < 1 + x' := by linarith only [hx']
  have h_exp_bound : Real.exp (Q*y) - 1 ≤ Q*y * Real.exp (Q*y) := by
    have hA := Real.add_one_le_exp (-(Q*y))
    have hexp_pos := Real.exp_pos (Q*y)
    have hB : Real.exp (-(Q*y)) * Real.exp (Q*y) = 1 := by
      rw [← Real.exp_add]; simp
    have hC : (-(Q*y) + 1) * Real.exp (Q*y) ≤ Real.exp (-(Q*y)) * Real.exp (Q*y) :=
      mul_le_mul_of_nonneg_right hA hexp_pos.le
    have hC1 : (-(Q*y) + 1) * Real.exp (Q*y) ≤ 1 := hC.trans_eq hB
    nlinarith only [hC1]
  have h_C0 : C₀ * (Real.exp (Q*y) - 1) ≤ C₀ * (Q*y*Real.exp (Q*y)) :=
    mul_le_mul_of_nonneg_left h_exp_bound hC₀
  have h_mid : 1 + x' ≤ Real.exp (Q*y) * (1 + x/8) + C₀ * (Q*y*Real.exp (Q*y)) := by
    have h_one_add : 1 + 1/8 * Real.exp (Q*y) * x ≤ Real.exp (Q*y) * (1 + x/8) := by
      calc 1 + 1/8 * Real.exp (Q*y) * x
          ≤ Real.exp (Q*y) + 1/8 * Real.exp (Q*y) * x := add_le_add_left h1 _
        _ = Real.exp (Q*y) * (1 + x/8) := by ring
    calc 1 + x'
        ≤ 1 + (1/8 * Real.exp (Q*y) * x + C₀ * (Real.exp (Q*y) - 1)) := add_le_add_right h 1
      _ = (1 + 1/8 * Real.exp (Q*y) * x) + C₀ * (Real.exp (Q*y) - 1) := by ring
      _ ≤ Real.exp (Q*y) * (1 + x/8) + C₀ * (Q*y*Real.exp (Q*y)) :=
          add_le_add h_one_add h_C0
  have hfactor : (0:ℝ) ≤ (9/16)*(1+x) - (1+x/8) := by linarith only [hx]
  have h_ratio : Real.exp (Q*y) * (1+x/8) ≤ (9/16)*(1+x)*Real.exp (Q*y) := by
    have hle : 1 + x/8 ≤ (9/16)*(1+x) := by linarith only [hfactor]
    calc Real.exp (Q*y) * (1+x/8) = (1+x/8) * Real.exp (Q*y) := by ring
      _ ≤ (9/16)*(1+x) * Real.exp (Q*y) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos (Q*y)).le
  have hnn : (0:ℝ) ≤ C₀ * (Q*y*Real.exp (Q*y)) :=
    mul_nonneg hC₀ (mul_nonneg hQy (Real.exp_pos (Q*y)).le)
  have hxx : (1:ℝ) ≤ (1+x)/2 := by linarith only [hx]
  have h_C0term : C₀*(Q*y*Real.exp (Q*y)) ≤ (1+x)/2 * (C₀*(Q*y*Real.exp (Q*y))) :=
    le_mul_of_one_le_left hnn hxx
  have h_add_exp := Real.add_one_le_exp (8/9*C₀*Q*y)
  have h1x : (0:ℝ) ≤ 1+x := by linarith only [hx]
  have hpos3 : (0:ℝ) ≤ (9/16)*(1+x)*Real.exp (Q*y) :=
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 9/16) h1x) (Real.exp_pos (Q*y)).le
  have h_final_factor : (9/16)*(1+x)*Real.exp (Q*y) * (8/9*C₀*Q*y + 1) ≤
      (9/16)*(1+x)*Real.exp (Q*y) * Real.exp (8/9*C₀*Q*y) :=
    mul_le_mul_of_nonneg_left h_add_exp hpos3
  have h_key : 1 + x' ≤ (9/16 : ℝ) * (1 + x) * Real.exp (Q*y) * Real.exp (8/9*C₀*Q*y) := by
    have h_step1 : 1 + x' ≤
        (9/16)*(1+x)*Real.exp (Q*y) + (1+x)/2 * (C₀*(Q*y*Real.exp (Q*y))) := by
      linarith only [h_mid, h_ratio, h_C0term]
    have h_split : (9/16)*(1+x)*Real.exp (Q*y) + (1+x)/2 * (C₀*(Q*y*Real.exp (Q*y))) =
        (9/16)*(1+x)*Real.exp (Q*y) * (8/9*C₀*Q*y + 1) := by ring
    exact (h_step1.trans_eq h_split).trans h_final_factor
  have h_log := Real.log_le_log h_x'_pos h_key
  have hA0 : (9/16:ℝ) ≠ 0 := by norm_num
  have hB0 : (1+x:ℝ) ≠ 0 := by
    have : (0:ℝ) < 1+x := by linarith only [hx]
    exact this.ne'
  have hCexp0 : Real.exp (Q*y) ≠ 0 := (Real.exp_pos (Q*y)).ne'
  have hDexp0 : Real.exp (8/9*C₀*Q*y) ≠ 0 := (Real.exp_pos (8/9*C₀*Q*y)).ne'
  have hAB0 : (9/16:ℝ)*(1+x) ≠ 0 := mul_ne_zero hA0 hB0
  have hABC0 : (9/16:ℝ)*(1+x)*Real.exp (Q*y) ≠ 0 := mul_ne_zero hAB0 hCexp0
  have h_log_eq : Real.log ((9/16:ℝ) * (1 + x) * Real.exp (Q*y) * Real.exp (8/9*C₀*Q*y)) =
      Real.log (1+x) - Real.log (16/9) + (Q + 8/9*C₀*Q)*y := by
    rw [Real.log_mul hABC0 hDexp0, Real.log_mul hAB0 hCexp0, Real.log_mul hA0 hB0,
        Real.log_exp, Real.log_exp, show (9/16:ℝ) = (16/9)⁻¹ by norm_num, Real.log_inv]
    ring
  linarith only [h_log, h_log_eq]

/-- A7. The hitting-index argument of `p.initial.fixed.grid.scale`, abstractly. -/
theorem exists_good_index_of_decrement (W δ : ℕ → ℝ) (bad : ℕ → Prop) (Ksteps : ℕ)
    (a c : ℝ) (hW : ∀ ℓ, 0 ≤ W ℓ)
    (hdec : ∀ ℓ, ℓ < Ksteps → bad ℓ → W (ℓ + 1) ≤ W ℓ - a + c * δ ℓ)
    (hK : W 0 + c * ∑ ℓ ∈ Finset.range Ksteps, δ ℓ < (Ksteps : ℝ) * a) :
    ∃ ℓ, ℓ < Ksteps ∧ ¬ bad ℓ := by
  by_contra h
  push Not at h
  suffices ∀ k ≤ Ksteps, W k ≤ W 0 - (k : ℝ) * a + c * ∑ ℓ ∈ Finset.range k, δ ℓ by
    linarith only [this Ksteps (le_refl _), hW Ksteps, hK]
  intro k hk
  revert hk
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k ≤ Ksteps := by omega
    have hk_lt : k < Ksteps := by omega
    have ih' := ih hk'
    have dec := hdec k hk_lt (h k hk_lt)
    rw [Finset.sum_range_succ]
    push_cast
    linarith only [ih', dec]

/-- A8. Integer telescoping over `Finset.Icc (a+1) b`. -/
theorem sum_Icc_int_telescope (f : ℤ → ℝ) {a b : ℤ} (hab : a ≤ b) :
    (∑ j ∈ Finset.Icc (a + 1) b, (f (j - 1) - f j)) = f a - f b := by
  induction b, hab using Int.leInduction with
  | base =>
    have h : a < a + 1 := by omega
    rw [Finset.Icc_eq_empty_of_lt h, Finset.sum_empty]
    ring
  | succ b _hb ih =>
    have h_eq : Finset.Icc (a + 1) (b + 1) = insert (b + 1) (Finset.Icc (a + 1) b) := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have h_mem : b + 1 ∉ Finset.Icc (a + 1) b := by
      simp only [Finset.mem_Icc]
      omega
    rw [h_eq, Finset.sum_insert h_mem, ih]
    have hb1 : b + 1 - 1 = b := by ring
    rw [hb1]
    ring

/-- A9. The geometric weight sum over `Finset.Icc`. -/
theorem geometric_weight_sum_Icc_le (θ : ℝ) (hθ : 0 < θ) (a b : ℤ) :
    ∑ j ∈ Finset.Icc a b, (3 : ℝ) ^ (-θ * ((b : ℝ) - (j : ℝ))) ≤
      (1 - (3 : ℝ) ^ (-θ))⁻¹ := by
  have hr0 : (0:ℝ) ≤ (3:ℝ) ^ (-θ) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3:ℝ) ^ (-θ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hθ])
  have hpos : (0:ℝ) < 1 - (3:ℝ) ^ (-θ) := by linarith only [hr1]
  have key : ∀ b : ℤ, a - 1 ≤ b →
      ∑ j ∈ Finset.Icc a b, (3:ℝ) ^ (-θ * ((b:ℝ) - (j:ℝ))) ≤ (1 - (3:ℝ) ^ (-θ))⁻¹ := by
    intro b hb
    induction b, hb using Int.leInduction with
    | base =>
      have hempty : Finset.Icc a (a - 1) = (∅ : Finset ℤ) :=
        Finset.Icc_eq_empty_of_lt (by omega)
      rw [hempty, Finset.sum_empty]
      exact le_of_lt (inv_pos.mpr hpos)
    | succ b hb ih =>
      have hins : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : (b + 1) ∉ Finset.Icc a b := by
        simp only [Finset.mem_Icc]
        omega
      rw [hins, Finset.sum_insert hnotmem]
      push_cast
      simp only [sub_self, mul_zero, Real.rpow_zero]
      have hsplit : ∑ j ∈ Finset.Icc a b, (3:ℝ) ^ (-θ * (((b:ℝ) + 1) - (j:ℝ))) =
          (3:ℝ) ^ (-θ) * ∑ j ∈ Finset.Icc a b, (3:ℝ) ^ (-θ * ((b:ℝ) - (j:ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hexp : -θ * (((b:ℝ) + 1) - (j:ℝ)) = -θ + -θ * ((b:ℝ) - (j:ℝ)) := by ring
        rw [hexp, Real.rpow_add (by norm_num : (0:ℝ) < 3)]
      rw [hsplit]
      have hcancel : (1 - (3:ℝ) ^ (-θ)) * (1 - (3:ℝ) ^ (-θ))⁻¹ = 1 :=
        mul_inv_cancel₀ hpos.ne'
      have heq : (3:ℝ) ^ (-θ) * (1 - (3:ℝ) ^ (-θ))⁻¹ + 1 = (1 - (3:ℝ) ^ (-θ))⁻¹ := by
        linear_combination -hcancel
      have hmul : (3:ℝ) ^ (-θ) * (∑ j ∈ Finset.Icc a b, (3:ℝ) ^ (-θ * ((b:ℝ) - (j:ℝ)))) ≤
          (3:ℝ) ^ (-θ) * (1 - (3:ℝ) ^ (-θ))⁻¹ :=
        mul_le_mul_of_nonneg_left ih hr0
      linarith only [hmul, heq]
  rcases le_or_gt a b with hab | hab
  · exact key b (by omega)
  · rw [Finset.Icc_eq_empty_of_lt hab, Finset.sum_empty]
    exact le_of_lt (inv_pos.mpr hpos)

/-- A10. The geometric weight sum over `Finset.Ico`, in the mean-history shape. -/
theorem geometric_weight_sum_Ico_le (θ : ℝ) (hθ : 0 < θ) (a b : ℤ) :
    ∑ j ∈ Finset.Ico a b, (3 : ℝ) ^ (-θ * ((b : ℝ) - 1 - (j : ℝ))) ≤
      (1 - (3 : ℝ) ^ (-θ))⁻¹ := by
  have h_eq : Finset.Ico a b = Finset.Icc a (b - 1) := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [h_eq]
  have h_weight : ∀ j ∈ Finset.Icc a (b - 1),
      (3 : ℝ) ^ (-θ * ((b : ℝ) - 1 - (j : ℝ))) = (3 : ℝ) ^ (-θ * (((b - 1 : ℤ) : ℝ) - (j : ℝ)))
        := by
    intro j _
    push_cast
    ring
  have : ∑ j ∈ Finset.Icc a (b - 1), (3 : ℝ) ^ (-θ * ((b : ℝ) - 1 - (j : ℝ))) =
          ∑ j ∈ Finset.Icc a (b - 1), (3 : ℝ) ^ (-θ * (((b - 1 : ℤ) : ℝ) - (j : ℝ))) :=
    Finset.sum_congr rfl h_weight
  rw [this]
  exact geometric_weight_sum_Icc_le θ hθ a (b - 1)

/-- A12. Positive definiteness of the full matrix gives `BlockPosDef` (public restatement). -/
theorem blockPosDef_of_toFullBlockMat_posDef {d : ℕ} (A : BlockMat d)
    (hA : (toFullBlockMat A).PosDef) : Book.Ch02.BlockPosDef A := by
  intro X hX
  have hvec : toFullBlockVec X ≠ 0 := by
    intro h
    apply hX
    have h' := congrArg ofFullBlockVec h
    rw [ofFullBlockVec_toFullBlockVec] at h'
    simpa using! h'
  have h2 := hA.dotProduct_mulVec_pos hvec
  have hstar : star (toFullBlockVec X) = toFullBlockVec X := rfl
  rw [hstar, ← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec] at h2
  exact h2

/-- The flattened block basis vector is the standard basis vector of `BlockCoord d`. -/
private theorem toFullBlockVec_blockBasis {d : ℕ} (α : BlockCoord d) :
    toFullBlockVec (blockBasis α) = Pi.single α 1 := by
  funext β
  cases α <;> cases β <;> simp [blockBasis, toFullBlockVec, Pi.single_apply]

/-- A13. A block below `c·I` has `tr(M − I) ≤ 2d(c − 1)`. -/
theorem blockTrace_sub_identity_le_of_le_scale {d : ℕ} (M : BlockMat d) (c : ℝ)
    (hM : BlockMatLoewnerLE M (blockScale c (Book.Ch02.blockIdentity d))) :
    blockTrace (blockSub M (Book.Ch02.blockIdentity d)) ≤ 2 * (d : ℝ) * (c - 1) := by
  have key : ∀ α : BlockCoord d, blockMatEntry M α α ≤ c := by
    intro α
    have h := hM (blockBasis α)
    rw [blockVecDot_blockMatVecMul_eq_sum, blockVecDot_blockMatVecMul_eq_sum,
      toFullBlockVec_blockBasis] at h
    have hquad : ∀ A : BlockMat d,
        ∑ β : BlockCoord d, ∑ δ : BlockCoord d,
          (Pi.single α (1 : ℝ) : BlockCoord d → ℝ) β *
            (blockMatEntry A β δ * (Pi.single α (1 : ℝ) : BlockCoord d → ℝ) δ)
          = blockMatEntry A α α := by
      intro A
      rw [Finset.sum_eq_single α]
      · rw [Finset.sum_eq_single α]
        · simp
        · intro δ _ hδ; simp [hδ]
        · intro h; exact absurd (Finset.mem_univ α) h
      · intro β _ hβ; simp [Pi.single_apply, hβ]
      · intro h; exact absurd (Finset.mem_univ α) h
    rw [hquad, hquad] at h
    have hid : blockMatEntry (blockScale c (Book.Ch02.blockIdentity d)) α α = c := by
      rw [blockMatEntry_blockScale]
      cases α <;> simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, blockMatEntry]
    rw [hid] at h
    linarith only [h]
  have hid1 : ∀ α : BlockCoord d, blockMatEntry (Book.Ch02.blockIdentity d) α α = 1 := by
    intro α
    cases α <;> simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, blockMatEntry]
  have hexp : blockTrace (blockSub M (Book.Ch02.blockIdentity d))
      = ∑ α : BlockCoord d,
        (blockMatEntry M α α - blockMatEntry (Book.Ch02.blockIdentity d) α α) := by
    simp only [blockTrace, Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl ?_
    intro α _
    cases α <;> rfl
  rw [hexp]
  calc ∑ α : BlockCoord d,
        (blockMatEntry M α α - blockMatEntry (Book.Ch02.blockIdentity d) α α)
      ≤ ∑ _α : BlockCoord d, (c - 1) := by
        refine Finset.sum_le_sum ?_
        intro α _
        rw [hid1 α]
        linarith only [key α]
    _ = 2 * (d : ℝ) * (c - 1) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
          rw [show Fintype.card (BlockCoord d) = Fintype.card (Fin d) + Fintype.card (Fin d) from
            Fintype.card_sum, Fintype.card_fin]
          push_cast; ring
        rw [this]

/-- A14. The mean penalty of a block `I ≤ M ≤ c·I` (`p.initial.fixed.grid.scale`). -/
theorem meanPenalty_le_of_le_scale {d : ℕ} (Q : ℕ) (M : BlockMat d)
    (hM : IsSymmetricBlockMat M) (c : ℝ) (hc : 1 ≤ c)
    (hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M)
    (hMc : BlockMatLoewnerLE M (blockScale c (Book.Ch02.blockIdentity d))) :
    meanPenalty Q M ≤ (1 + 2 * (d : ℝ) * (c - 1)) ^ Q - 1 := by
  have h0 : 0 ≤ blockTrace (blockSub M (Book.Ch02.blockIdentity d)) :=
    Analysis.blockTrace_identity_sub_nonneg M hM hIM
  have h1 : blockTrace (blockSub M (Book.Ch02.blockIdentity d)) ≤ 2 * (d : ℝ) * (c - 1) :=
    blockTrace_sub_identity_le_of_le_scale M c hMc
  have hcnn : (0 : ℝ) ≤ c - 1 := sub_nonneg.mpr hc
  have h2 : (1 + blockTrace (blockSub M (Book.Ch02.blockIdentity d))) ^ Q
      ≤ (1 + 2 * (d : ℝ) * (c - 1)) ^ Q :=
    pow_le_pow_left₀ (by linarith only [h0]) (by linarith only [h1]) Q
  simpa [meanPenalty] using h2

/-- A15. The `Q`-th Schatten moment of a symmetric block sandwiched in `[−I, c·I]`. -/
theorem absSchattenNorm_pow_le_of_sandwich {d : ℕ} (Q : ℕ) (hQ : 1 ≤ Q) (H : BlockMat d)
    (hH : IsSymmetricBlockMat H) (c : ℝ) (hc : 1 ≤ c)
    (hlo : BlockMatLoewnerLE (blockScale (-1) (Book.Ch02.blockIdentity d)) H)
    (hhi : BlockMatLoewnerLE H (blockScale c (Book.Ch02.blockIdentity d))) :
    absSchattenNorm (Q : ℝ) H ^ Q ≤ 2 * (d : ℝ) * c ^ Q := by
  classical
  have hHfull : Matrix.IsHermitian (toFullBlockMat H) :=
    (HCPolySupport.HighContrast.Analysis.toFullBlockMat_isHermitian_iff H).mpr hH
  have hQreal : (1 : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast hQ
  have hspectral : absSchattenNorm (Q : ℝ) H ^ Q = ∑ i, |hHfull.eigenvalues i| ^ Q := by
    have h := HCPolySupport.HighContrast.Analysis.absSchattenNorm_rpow_eq_sum hHfull hQreal
    rw [Real.rpow_natCast] at h
    simpa [Real.rpow_natCast] using h
  have hscaleC :
      toFullBlockMat (blockScale c (Book.Ch02.blockIdentity d)) =
        c • (1 : FullBlockMat d) := by
    ext (i | i) (j | j) <;>
      simp [blockScale, Book.Ch02.blockIdentity, Book.Ch02.blockDiag,
        toFullBlockMat, Matrix.one_apply]
  have hscaleNeg :
      toFullBlockMat (blockScale (-1 : ℝ) (Book.Ch02.blockIdentity d)) =
        (-1 : ℝ) • (1 : FullBlockMat d) := by
    ext (i | i) (j | j) <;>
      simp [blockScale, Book.Ch02.blockIdentity, Book.Ch02.blockDiag,
        toFullBlockMat, Matrix.one_apply] <;>
      split <;> norm_num
  have hHermC :
      Matrix.IsHermitian (toFullBlockMat (blockScale c (Book.Ch02.blockIdentity d))) := by
    rw [hscaleC]
    simp [Matrix.IsHermitian]
  have hHermNeg :
      Matrix.IsHermitian
        (toFullBlockMat (blockScale (-1 : ℝ) (Book.Ch02.blockIdentity d))) := by
    rw [hscaleNeg]
    simp [Matrix.IsHermitian]
  have hloFull :
      (-1 : ℝ) • (1 : FullBlockMat d) ≤ toFullBlockMat H := by
    have hraw :
        toFullBlockMat (blockScale (-1 : ℝ) (Book.Ch02.blockIdentity d)) ≤
          toFullBlockMat H :=
      (HCPolySupport.HighContrast.Annealed.fullBlock_le_iff hHermNeg hHfull).mpr hlo
    simpa [hscaleNeg] using hraw
  have hhiFull :
      toFullBlockMat H ≤ c • (1 : FullBlockMat d) := by
    have hraw :
        toFullBlockMat H ≤
          toFullBlockMat (blockScale c (Book.Ch02.blockIdentity d)) :=
      (HCPolySupport.HighContrast.Annealed.fullBlock_le_iff hHfull hHermC).mpr hhi
    simpa [hscaleC] using hraw
  have hUpperOrder :
      toFullBlockMat H ≤ algebraMap ℝ (FullBlockMat d) c := by
    simpa [Algebra.algebraMap_eq_smul_one] using hhiFull
  have hLowerOrder :
      algebraMap ℝ (FullBlockMat d) (-1 : ℝ) ≤ toFullBlockMat H := by
    simpa [Algebra.algebraMap_eq_smul_one] using hloFull
  have hUpperSpec : ∀ x ∈ spectrum ℝ (toFullBlockMat H), x ≤ c :=
    (le_algebraMap_iff_spectrum_le (ha := hHfull)).mp hUpperOrder
  have hLowerSpec : ∀ x ∈ spectrum ℝ (toFullBlockMat H), (-1 : ℝ) ≤ x :=
    (algebraMap_le_iff_le_spectrum (ha := hHfull)).mp hLowerOrder
  have hspecRange :
      spectrum ℝ (toFullBlockMat H) = Set.range hHfull.eigenvalues :=
    Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hHfull
  have hterm :
      ∀ i ∈ (Finset.univ : Finset (BlockCoord d)),
        |hHfull.eigenvalues i| ^ Q ≤ c ^ Q := by
    intro i _
    have hmem : hHfull.eigenvalues i ∈ spectrum ℝ (toFullBlockMat H) := by
      rw [hspecRange]
      exact Set.mem_range_self i
    have habs : |hHfull.eigenvalues i| ≤ c := by
      rw [abs_le]
      exact ⟨le_trans (neg_le_neg hc) (hLowerSpec _ hmem), hUpperSpec _ hmem⟩
    exact pow_le_pow_left₀ (abs_nonneg _) habs Q
  calc
    absSchattenNorm (Q : ℝ) H ^ Q = ∑ i, |hHfull.eigenvalues i| ^ Q := hspectral
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) * c ^ Q := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul
          (Finset.univ : Finset (BlockCoord d))
          (fun i => |hHfull.eigenvalues i| ^ Q) (c ^ Q) hterm)
    _ = 2 * (d : ℝ) * c ^ Q := by
      change (Fintype.card (Fin d ⊕ Fin d) : ℝ) * c ^ Q = 2 * (d : ℝ) * c ^ Q
      rw [Fintype.card_sum]
      simp only [Fintype.card_fin]
      push_cast
      ring_nf

/-- A16. If `F` and `G` are positive definite, `0 < c`, and `F ≤ c • G` in the Loewner
order, then `normalizedBlock F G ≤ c • I` and `blockLogDet F - blockLogDet G ≤ 2 d log c`. -/
theorem normalizedBlock_le_scale_and_logDet_le {d : ℕ} (F G : BlockMat d)
    (hF : (toFullBlockMat F).PosDef) (hG : (toFullBlockMat G).PosDef)
    (c : ℝ) (hc : 0 < c) (hFG : BlockMatLoewnerLE F (blockScale c G)) :
    BlockMatLoewnerLE (normalizedBlock F G) (blockScale c (Book.Ch02.blockIdentity d)) ∧
      blockLogDet F - blockLogDet G ≤ 2 * (d : ℝ) * Real.log c := by
  have full_scale : ∀ (t : ℝ) (A : BlockMat d),
      toFullBlockMat (blockScale t A) = t • toFullBlockMat A := by
    intro t A
    ext (i | i) (j | j) <;> rfl
  have hS := HCPolySupport.HighContrast.Multiscale.matSqrt_inv_posDef_full hG
  have hN := HCPolySupport.HighContrast.Annealed.normalizedBlock_posDef F G hF hG
  have hscale : (toFullBlockMat (blockScale c G)).PosDef := by
    rw [full_scale]
    exact hG.smul hc
  have hAB : toFullBlockMat F ≤ toFullBlockMat (blockScale c G) :=
    (HCPolySupport.HighContrast.Annealed.fullBlock_le_iff hF.isHermitian hscale.isHermitian).mpr hFG
  have hu : matSqrt (toFullBlockMat G)⁻¹ * toFullBlockMat F * matSqrt (toFullBlockMat G)⁻¹ ≤
      matSqrt (toFullBlockMat G)⁻¹ * toFullBlockMat (blockScale c G) * matSqrt (toFullBlockMat
        G)⁻¹ := by
    apply Matrix.le_iff.mpr
    simpa only [hS.isHermitian.eq, mul_sub, sub_mul] using
      (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same (matSqrt (toFullBlockMat G)⁻¹)
  have hupper : toFullBlockMat (normalizedBlock F G) ≤ c • (1 : FullBlockMat d) := by
    simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat,
      full_scale, Matrix.mul_smul, Matrix.smul_mul,
      matSqrt_inv_conj hG] using hu
  have hI : toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
    ext (i | i) (j | j) <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]
  constructor
  · apply (HCPolySupport.HighContrast.Annealed.fullBlock_le_iff hN.isHermitian (by
      rw [full_scale, hI]
      exact (Matrix.PosDef.one.smul hc).isHermitian)).mp
    simpa only [full_scale, hI] using hupper
  · have heig : ∀ i, hN.isHermitian.eigenvalues i ≤ c := by
      intro i
      apply (le_algebraMap_iff_spectrum_le (a := toFullBlockMat (normalizedBlock F G))
        (r := c) (ha := hN.isHermitian)).mp
        (by simpa only [Algebra.algebraMap_eq_smul_one] using hupper)
      rw [hN.isHermitian.spectrum_real_eq_range_eigenvalues]
      exact Set.mem_range_self i
    have hdet : (toFullBlockMat (normalizedBlock F G)).det ≤ c ^ (2 * d) := by
      rw [hN.isHermitian.det_eq_prod_eigenvalues]
      simp only [RCLike.ofReal_real_eq_id, id_eq]
      have hp := Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) =>
          (hN.eigenvalues_pos i).le) (fun i (_ : i ∈ Finset.univ) => heig i)
      simpa only [Finset.prod_const, Finset.card_univ, BlockCoord,
        Fintype.card_sum, Fintype.card_fin, two_mul] using hp
    have hl := Real.log_le_log hN.det_pos hdet
    rw [HCPolySupport.HighContrast.Multiscale.det_normalizedBlock_eq_exp F G hF hG, Real.log_exp,
      Real.log_pow] at hl
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hl

end

end HCPolySupport.HighContrast.Multiscale
