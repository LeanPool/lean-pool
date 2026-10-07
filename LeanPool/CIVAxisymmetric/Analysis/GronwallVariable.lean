/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Analysis.SobolevSix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
### Integral Grönwall inequality with variable coefficient

If `φ` is continuous on `[a, b]`, `k` is continuous and nonnegative on `[a, b]`,
and `φ` has right derivative `φ'` on `[a, b)` satisfying `φ' ≤ k·φ`,
then `φ t ≤ φ a * exp(∫_a^t k s ds)` for all `t ∈ [a, b]`.

The proof defines `Φ(t) = φ(t) * exp(-∫_a^t k s ds)` and shows `Φ` is continuous on `[a, b]`
and has right derivative ≤ 0 on `[a, b)`. The fencing lemma
`image_le_of_deriv_right_le_deriv_boundary` then yields `Φ t ≤ Φ a = φ a`, and the
inequality follows by multiplying by `exp(∫_a^t k s ds)`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem le_mul_exp_integral_of_deriv_le {φ k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn φ (Set.Icc a b)) (hk : ContinuousOn k (Set.Icc a b))
    (hk0 : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hderiv : ∀ t ∈ Set.Ico a b, HasDerivWithinAt φ (deriv φ t) (Set.Ici t) t)
    (hineq : ∀ t ∈ Set.Ico a b, deriv φ t ≤ k t * φ t) :
    ∀ t ∈ Set.Icc a b, φ t ≤ φ a * Real.exp (∫ s in a..t, k s) := by
  -- Define Φ(t) = φ(t) * exp(-∫_a^t k(s) ds) and B(t) = φ(a) (constant)
  set Φ : ℝ → ℝ := fun x => φ x * Real.exp (-(∫ s in a..x, k s)) with hΦ_def
  set B : ℝ → ℝ := fun _ => φ a with hB_def
  have hΦa_le_Ba : Φ a ≤ B a := by
    simp [hΦ_def, hB_def]
  -- Φ is continuous on [a, b]
  have hΦ_cont : ContinuousOn Φ (Set.Icc a b) := by
    have h_int_cont : ContinuousOn (fun x => ∫ s in a..x, k s) (Set.Icc a b) := by
      have h_int_cont' : ContinuousOn (fun x => ∫ s in a..x, k s) (Set.uIcc a b) :=
        intervalIntegral.continuousOn_primitive_interval' (hk.intervalIntegrable_of_Icc hab)
          left_mem_uIcc
      rwa [Set.uIcc_of_le hab] at h_int_cont'
    have h_exp_cont : ContinuousOn
        (fun x => Real.exp (-(∫ s in a..x, k s))) (Set.Icc a b) :=
      Real.continuous_exp.comp_continuousOn (h_int_cont.neg)
    exact hcont.mul h_exp_cont
  -- Φ has right derivative on [a, b)
  have hΦ_deriv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt Φ
      (deriv φ x * Real.exp (-(∫ s in a..x, k s)) +
       φ x * (Real.exp (-(∫ s in a..x, k s)) * (-k x))) (Set.Ici x) x := by
    intro x hx
    have hx_mem_Icc : x ∈ Set.Icc a b := Set.mem_Icc_of_Ico hx
    -- derivative of the integral I(t) = ∫_a^t k(s) ds
    have h_int_deriv : HasDerivWithinAt (fun y => ∫ s in a..y, k s) (k x) (Set.Ici x) x := by
      have h_intble : IntervalIntegrable k volume a x :=
        (hk.mono (Set.Icc_subset_Icc_right hx_mem_Icc.2)).intervalIntegrable_of_Icc hx_mem_Icc.1
      have h_meas : StronglyMeasurableAtFilter k (𝓝[Set.Ioi x] x) volume :=
        (hk.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x).filter_mono
          (by
            have h_nhd : Set.Icc a b ∈ 𝓝[Set.Ioi x] x := by
              rw [mem_nhdsGT_iff_exists_Ioo_subset' hx.2]
              exact ⟨b, hx.2, fun y hy => ⟨hx_mem_Icc.1.trans hy.1.le, hy.2.le⟩⟩
            exact nhdsWithin_le_of_mem h_nhd)
      have h_cont : ContinuousWithinAt k (Set.Ioi x) x :=
        (hk.continuousWithinAt hx_mem_Icc).mono_of_mem_nhdsWithin
          (by
            rw [mem_nhdsGT_iff_exists_Ioo_subset' hx.2]
            exact ⟨b, hx.2, fun y hy => ⟨hx_mem_Icc.1.trans hy.1.le, hy.2.le⟩⟩)
      exact intervalIntegral.integral_hasDerivWithinAt_right h_intble h_meas h_cont
    -- derivative of -I(t)
    have h_neg_int_deriv : HasDerivWithinAt (fun y => -(∫ s in a..y, k s))
        (-(k x)) (Set.Ici x) x := h_int_deriv.neg
    -- derivative of exp(-I(t))
    have h_exp_deriv : HasDerivWithinAt (fun y => Real.exp (-(∫ s in a..y, k s)))
        (Real.exp (-(∫ s in a..x, k s)) * (-(k x))) (Set.Ici x) x := by
      simpa [mul_comm] using h_neg_int_deriv.exp
    -- derivative of φ(t) * exp(-I(t)) using product rule
    have h_deriv_φ : HasDerivWithinAt φ (deriv φ x) (Set.Ici x) x := hderiv x hx
    have h_deriv_Φ : HasDerivWithinAt Φ
        (deriv φ x * Real.exp (-(∫ s in a..x, k s)) +
         φ x * (Real.exp (-(∫ s in a..x, k s)) * (-(k x)))) (Set.Ici x) x :=
      h_deriv_φ.mul h_exp_deriv
    simpa [mul_add, add_comm, mul_comm, mul_left_comm, mul_assoc] using h_deriv_Φ
  -- The derivative of Φ is ≤ 0 on [a, b)
  have hΦ_deriv_nonpos : ∀ x ∈ Set.Ico a b,
      deriv φ x * Real.exp (-(∫ s in a..x, k s)) +
      φ x * (Real.exp (-(∫ s in a..x, k s)) * (-k x)) ≤ 0 := by
    intro x hx
    have h_exp_pos : 0 < Real.exp (-(∫ s in a..x, k s)) := Real.exp_pos _
    have h_ineq := hineq x hx
    have h_nonneg_k : 0 ≤ k x := hk0 x (Set.mem_Icc_of_Ico hx)
    have h := mul_le_mul_of_nonneg_right h_ineq h_exp_pos.le
    -- h : deriv φ x * E ≤ (k x * φ x) * E  where E = exp(...) > 0
    -- We need: deriv φ x * E + φ x * (E * (-k x)) ≤ 0
    -- = deriv φ x * E - φ x * E * k x = E * (deriv φ x - φ x * k x) ≤ 0
    -- since E > 0 and deriv φ x ≤ k x * φ x
    linarith only [h]
  -- B is constant, so its derivative is 0
  have hB_deriv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt B 0 (Set.Ici x) x := by
    intro x hx
    simp [hB_def, hasDerivWithinAt_const]
  -- Apply the fencing lemma: Φ t ≤ B t for all t ∈ [a, b]
  have hΦ_le_B : ∀ ⦃x⦄, x ∈ Set.Icc a b → Φ x ≤ B x :=
    image_le_of_deriv_right_le_deriv_boundary hΦ_cont hΦ_deriv hΦa_le_Ba
      continuousOn_const
      hB_deriv
      hΦ_deriv_nonpos
  intro t ht
  -- From Φ t ≤ B t = φ a, we get φ t * exp(-∫_a^t k) ≤ φ a
  have hΦt_le_φa : Φ t ≤ φ a := by
    simpa [hB_def] using hΦ_le_B ht
  -- Multiply both sides by exp(∫_a^t k) > 0 to get the desired inequality
  have h_exp_pos : 0 < Real.exp (∫ s in a..t, k s) := Real.exp_pos _
  have h_eq : φ t = Φ t * Real.exp (∫ s in a..t, k s) := by
    dsimp [Φ]
    calc
      φ t = φ t * 1 := by ring
      _ = φ t * (Real.exp (-(∫ s in a..t, k s)) * Real.exp (∫ s in a..t, k s)) := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      _ = (φ t * Real.exp (-(∫ s in a..t, k s))) * Real.exp (∫ s in a..t, k s) := by ring
  rw [h_eq]
  exact mul_le_mul_of_nonneg_right hΦt_le_φa h_exp_pos.le

end CIV
