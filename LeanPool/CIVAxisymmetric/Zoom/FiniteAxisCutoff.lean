/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteLiftEquation
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# A cutoff at the axis of the lifted variables, and the residual integrand

The residual of `eq:aniso:zoom:finite:limit` against a test function is split, in
the passage to the limit of Step 2 of the proof of `prop:aniso:small` (deviation D17), into a
part supported near the axis `X = 0` of the lifted variables
and a part supported off it. The splitting uses the smooth cutoff
`finAxisCutoff ε (X, Z, τ) = b(X / ε)`, with `b` a fixed bump equal to `1` on the unit ball and
vanishing outside the ball of radius `2` (sup norm on the four radial coordinates). Its `j`-th
derivative is `O(ε^{-j})` (`norm_iteratedFDeriv_finAxisCutoff_le`).

The residual integrand `-∂_τ ψ - B · ∇ψ - d ψ - Δ_X ψ` is bounded by the first two derivatives
of `ψ` (`abs_residualIntegrand_le`) and is additive in `ψ` (`residualIntegrand_add`).
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-! ### The cutoff -/

/-- The projection `(X, Z, τ) ↦ (X, 0)` onto the four radial coordinates. -/
@[expose] def finAxisProj : Vec 5 × ℝ →L[ℝ] Vec 5 :=
  ContinuousLinearMap.pi fun j : Fin 5 =>
    if j = 4 then 0 else (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Vec 5) ℝ)

theorem finAxisProj_apply (z : Vec 5 × ℝ) (j : Fin 5) :
    finAxisProj z j = if j = 4 then 0 else z.1 j := by
  unfold finAxisProj
  split_ifs <;> simp [*]

theorem norm_finAxisProj_apply_le (z : Vec 5 × ℝ) : ‖finAxisProj z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun j => ?_
  rw [finAxisProj_apply]
  split_ifs
  · simp
  · exact (norm_le_pi_norm z.1 j).trans (norm_fst_le z)

theorem norm_finAxisProj_le : ‖finAxisProj‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [one_mul]
    exact norm_finAxisProj_apply_le z

/-- The bump of the cutoff: `1` on the closed unit ball, `0` outside the open ball of radius
`2`. -/
@[expose] def finAxisBump : ContDiffBump (0 : Vec 5) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff `b(X / ε)` at scale `ε` near the axis of the lifted variables. -/
@[expose] def finAxisCutoff (ε : ℝ) (z : Vec 5 × ℝ) : ℝ := finAxisBump ((ε⁻¹ • finAxisProj) z)

theorem finAxisCutoff_eq_comp (ε : ℝ) :
    finAxisCutoff ε = (finAxisBump : Vec 5 → ℝ) ∘ (ε⁻¹ • finAxisProj) := rfl

theorem contDiff_finAxisCutoff (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (finAxisCutoff ε) :=
  finAxisBump.contDiff.comp (ε⁻¹ • finAxisProj).contDiff

theorem finAxisCutoff_nonneg (ε : ℝ) (z : Vec 5 × ℝ) : 0 ≤ finAxisCutoff ε z :=
  finAxisBump.nonneg

theorem finAxisCutoff_le_one (ε : ℝ) (z : Vec 5 × ℝ) : finAxisCutoff ε z ≤ 1 :=
  finAxisBump.le_one

/-- The cutoff is `1` where the rescaled radial part has norm at most one. -/
theorem finAxisCutoff_eq_one {ε : ℝ} {z : Vec 5 × ℝ} (hz : ‖(ε⁻¹ • finAxisProj) z‖ ≤ 1) :
    finAxisCutoff ε z = 1 :=
  finAxisBump.one_of_mem_closedBall (by simpa [finAxisBump] using hz)

/-- The cutoff vanishes where the rescaled radial part has norm at least two. -/
theorem finAxisCutoff_eq_zero {ε : ℝ} {z : Vec 5 × ℝ} (hz : 2 ≤ ‖(ε⁻¹ • finAxisProj) z‖) :
    finAxisCutoff ε z = 0 :=
  finAxisBump.zero_of_le_dist (by simpa [finAxisBump, dist_zero_right] using hz)

/-- Derivative bounds for the fixed bump. -/
theorem exists_norm_iteratedFDeriv_finAxisBump_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ 2 → ∀ y : Vec 5,
      ‖iteratedFDeriv ℝ j (finAxisBump : Vec 5 → ℝ) y‖ ≤ C := by
  have hb : ∀ j : ℕ, ∃ C : ℝ, ∀ y : Vec 5,
      ‖iteratedFDeriv ℝ j (finAxisBump : Vec 5 → ℝ) y‖ ≤ C := fun j =>
    (finAxisBump.hasCompactSupport.iteratedFDeriv j).exists_bound_of_continuous
      (finAxisBump.contDiff (n := (⊤ : ℕ∞)).continuous_iteratedFDeriv (by simp))
  obtain ⟨C0, h0⟩ := hb 0
  obtain ⟨C1, h1⟩ := hb 1
  obtain ⟨C2, h2⟩ := hb 2
  refine ⟨max (max C0 C1) (max C2 0), le_max_of_le_right (le_max_right _ _), ?_⟩
  intro j hj y
  interval_cases j
  · exact (h0 y).trans (le_max_of_le_left (le_max_left _ _))
  · exact (h1 y).trans (le_max_of_le_left (le_max_right _ _))
  · exact (h2 y).trans (le_max_of_le_right (le_max_left _ _))

/-- The `j`-th derivative of the cutoff at scale `ε` is `O(ε^{-j})`. -/
theorem norm_iteratedFDeriv_finAxisCutoff_le {C : ℝ}
    (hC : ∀ j : ℕ, j ≤ 2 → ∀ y : Vec 5, ‖iteratedFDeriv ℝ j (finAxisBump : Vec 5 → ℝ) y‖ ≤ C)
    {ε : ℝ} (hε : 0 < ε) {j : ℕ} (hj : j ≤ 2) (z : Vec 5 × ℝ) :
    ‖iteratedFDeriv ℝ j (finAxisCutoff ε) z‖ ≤ C * ε⁻¹ ^ j := by
  rw [finAxisCutoff_eq_comp, ContinuousLinearMap.iteratedFDeriv_comp_right _
    (finAxisBump.contDiff (n := (⊤ : ℕ∞))) z (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hA : ‖ε⁻¹ • finAxisProj‖ ≤ ε⁻¹ := by
    refine (norm_smul_le (ε⁻¹ : ℝ) finAxisProj).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    calc ε⁻¹ * ‖finAxisProj‖ ≤ ε⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left norm_finAxisProj_le (inv_pos.mpr hε).le
      _ = ε⁻¹ := mul_one _
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul (hC j hj _) (pow_le_pow_left₀ (norm_nonneg _) hA j) (by positivity)
    ((norm_nonneg _).trans (hC j hj ((ε⁻¹ • finAxisProj) z)))

/-- Where the cutoff is not identically one nearby, some radial coordinate has size at least
`ε`, so the lifted radius is at least `ε`. -/
theorem le_zoomLiftRadius_of_one_le_norm {ε : ℝ} (hε : 0 < ε) {z : Vec 5 × ℝ}
    (hz : 1 ≤ ‖(ε⁻¹ • finAxisProj) z‖) : ε ≤ zoomLiftRadius z.1 := by
  by_contra hnot
  have hlt : zoomLiftRadius z.1 < ε := not_le.mp hnot
  have hsmall : ‖(ε⁻¹ • finAxisProj) z‖ < 1 := by
    rw [show (ε⁻¹ • finAxisProj) z = ε⁻¹ • finAxisProj z from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hε)]
    have hP : ‖finAxisProj z‖ < ε := by
      refine (pi_norm_lt_iff hε).2 fun j => ?_
      rw [finAxisProj_apply]
      split_ifs with hj
      · simpa using hε
      · rw [Real.norm_eq_abs]
        exact (abs_le_zoomLiftRadius z.1 hj).trans_lt hlt
    calc ε⁻¹ * ‖finAxisProj z‖ < ε⁻¹ * ε := mul_lt_mul_of_pos_left hP (inv_pos.mpr hε)
      _ = 1 := inv_mul_cancel₀ hε.ne'
  exact absurd hz (not_le.mpr hsmall)

/-- Where the rescaled radial part has norm at most two, every radial coordinate is at most
`2ε`. -/
theorem abs_apply_le_of_norm_le_two {ε : ℝ} (hε : 0 < ε) {z : Vec 5 × ℝ}
    (hz : ‖(ε⁻¹ • finAxisProj) z‖ ≤ 2) {j : Fin 5} (hj : j ≠ 4) : |z.1 j| ≤ 2 * ε := by
  rw [show (ε⁻¹ • finAxisProj) z = ε⁻¹ • finAxisProj z from rfl, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hε)] at hz
  have hP : ‖finAxisProj z‖ ≤ 2 * ε := by
    have := mul_le_mul_of_nonneg_left hz hε.le
    rwa [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul, mul_comm] at this
  have hj' := (norm_le_pi_norm (finAxisProj z) j).trans hP
  simpa only [finAxisProj_apply, hj, ↓reduceIte, Real.norm_eq_abs] using hj'

/-! ### The residual integrand -/

/-- The integrand `-∂_τ ψ - v · ∇ψ - d ψ - Δ_X ψ` of the residual of
`eq:aniso:zoom:finite:limit`, bounded by the first two derivatives of `ψ`. -/
theorem abs_residualIntegrand_le {ψ : Vec 5 × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (z : Vec 5 × ℝ)
    (v : Vec 5) (d : ℝ) :
    |-(timeDeriv 5 ψ z) - gradPair 5 ψ z v - d * ψ z - partialLaplacian 5 4 ψ z|
      ≤ (1 + ‖v‖) * ‖iteratedFDeriv ℝ 1 ψ z‖ + |d| * ‖iteratedFDeriv ℝ 0 ψ z‖
        + 4 * ‖iteratedFDeriv ℝ 2 ψ z‖ := by
  have hd : ∀ w, DifferentiableAt ℝ ψ w := fun w => hψ.differentiable (by norm_num) w
  have hD1 : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
  rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_zero, ← norm_iteratedFDeriv_fderiv,
    norm_iteratedFDeriv_one, timeDeriv_eq_fderiv (hd z), gradPair_eq_fderiv (hd z),
    partialLaplacian_eq_fderiv hψ, sum_fin_five_ite_lt_four]
  have hb : ∀ i : Fin 5, ‖((basisVec i, 0) : Vec 5 × ℝ)‖ ≤ 1 := by
    intro i
    rw [Prod.norm_def]
    refine max_le ?_ (by simp)
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    show ‖basisVec i j‖ ≤ 1
    rw [basisVec_apply]
    split_ifs <;> simp
  have h2 : ∀ i : Fin 5, |fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec i, 0)) z (basisVec i, 0)|
      ≤ ‖fderiv ℝ (fderiv ℝ ψ) z‖ := by
    intro i
    have hh : HasFDerivAt (fun w => fderiv ℝ ψ w (basisVec i, 0))
        ((fderiv ℝ (fderiv ℝ ψ) z).flip (basisVec i, 0)) z := by
      have := (hD1.differentiable (by norm_num) z).hasFDerivAt.clm_apply
        (hasFDerivAt_const ((basisVec i, 0) : Vec 5 × ℝ) z)
      simpa using this
    rw [hh.fderiv, ContinuousLinearMap.flip_apply, ← Real.norm_eq_abs]
    calc ‖fderiv ℝ (fderiv ℝ ψ) z (basisVec i, 0) (basisVec i, 0)‖
        ≤ ‖fderiv ℝ (fderiv ℝ ψ) z (basisVec i, 0)‖ * ‖((basisVec i, 0) : Vec 5 × ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) z‖ * ‖((basisVec i, 0) : Vec 5 × ℝ)‖
            * ‖((basisVec i, 0) : Vec 5 × ℝ)‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) z‖ * 1 * 1 := by
          gcongr
          · exact hb i
          · exact hb i
      _ = ‖fderiv ℝ (fderiv ℝ ψ) z‖ := by ring
  have ht : |fderiv ℝ ψ z (0, 1)| ≤ ‖fderiv ℝ ψ z‖ := by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans_eq ?_
    simp [Prod.norm_def]
  have hv : |fderiv ℝ ψ z (v, 0)| ≤ ‖fderiv ℝ ψ z‖ * ‖v‖ := by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans_eq ?_
    simp [Prod.norm_def]
  have hψz : |d * ψ z| = |d| * ‖ψ z‖ := by rw [abs_mul, Real.norm_eq_abs]
  have e0 := h2 0
  have e1 := h2 1
  have e2 := h2 2
  have e3 := h2 3
  set a := fderiv ℝ ψ z (0, 1)
  set b := fderiv ℝ ψ z (v, 0)
  set N1 := ‖fderiv ℝ ψ z‖
  set N2 := ‖fderiv ℝ (fderiv ℝ ψ) z‖
  calc |-a - b - d * ψ z - (fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 0, 0)) z (basisVec 0, 0)
        + fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 1, 0)) z (basisVec 1, 0)
        + fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 2, 0)) z (basisVec 2, 0)
        + fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 3, 0)) z (basisVec 3, 0))|
      ≤ |a| + |b| + |d * ψ z|
        + (|fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 0, 0)) z (basisVec 0, 0)|
          + |fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 1, 0)) z (basisVec 1, 0)|
          + |fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 2, 0)) z (basisVec 2, 0)|
          + |fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 3, 0)) z (basisVec 3, 0)|) := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
          ((abs_sub _ _).trans (add_le_add (abs_neg a).le le_rfl)) le_rfl)) ?_)
        exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ N1 + N1 * ‖v‖ + |d| * ‖ψ z‖ + (N2 + N2 + N2 + N2) := by
        rw [hψz]
        gcongr
    _ = (1 + ‖v‖) * N1 + |d| * ‖ψ z‖ + 4 * N2 := by ring

/-- The residual integrand is additive in the test function. -/
theorem residualIntegrand_add {ψa ψb : Vec 5 × ℝ → ℝ} (ha : ContDiff ℝ 2 ψa)
    (hb : ContDiff ℝ 2 ψb) (z : Vec 5 × ℝ) (v : Vec 5) (d : ℝ) :
    -(timeDeriv 5 (fun y => ψa y + ψb y) z) - gradPair 5 (fun y => ψa y + ψb y) z v
        - d * (ψa z + ψb z) - partialLaplacian 5 4 (fun y => ψa y + ψb y) z
      = (-(timeDeriv 5 ψa z) - gradPair 5 ψa z v - d * ψa z - partialLaplacian 5 4 ψa z)
        + (-(timeDeriv 5 ψb z) - gradPair 5 ψb z v - d * ψb z - partialLaplacian 5 4 ψb z) := by
  have hab : ContDiff ℝ 2 (fun y => ψa y + ψb y) := ha.add hb
  have hda : ∀ w, DifferentiableAt ℝ ψa w := fun w => ha.differentiable (by norm_num) w
  have hdb : ∀ w, DifferentiableAt ℝ ψb w := fun w => hb.differentiable (by norm_num) w
  have h1 : ∀ w, fderiv ℝ (fun y => ψa y + ψb y) w = fderiv ℝ ψa w + fderiv ℝ ψb w :=
    fun w => fderiv_fun_add (hda w) (hdb w)
  have hD1a : ContDiff ℝ 1 (fderiv ℝ ψa) := ha.fderiv_right (by norm_num)
  have hD1b : ContDiff ℝ 1 (fderiv ℝ ψb) := hb.fderiv_right (by norm_num)
  have h2 : ∀ e : Vec 5 × ℝ,
      fderiv ℝ (fun w => fderiv ℝ (fun y => ψa y + ψb y) w e) z e
        = fderiv ℝ (fun w => fderiv ℝ ψa w e) z e + fderiv ℝ (fun w => fderiv ℝ ψb w e) z e := by
    intro e
    have hfun : (fun w => fderiv ℝ (fun y => ψa y + ψb y) w e)
        = fun w => fderiv ℝ ψa w e + fderiv ℝ ψb w e := by
      funext w
      rw [h1 w, add_apply]
    have hca : DifferentiableAt ℝ (fun w => fderiv ℝ ψa w e) z :=
      ((hD1a.clm_apply contDiff_const).differentiable (by norm_num)) z
    have hcb : DifferentiableAt ℝ (fun w => fderiv ℝ ψb w e) z :=
      ((hD1b.clm_apply contDiff_const).differentiable (by norm_num)) z
    rw [hfun, fderiv_fun_add hca hcb, add_apply]
  rw [timeDeriv_eq_fderiv (hab.differentiable (by norm_num) z), timeDeriv_eq_fderiv (hda z),
    timeDeriv_eq_fderiv (hdb z), gradPair_eq_fderiv (hab.differentiable (by norm_num) z),
    gradPair_eq_fderiv (hda z), gradPair_eq_fderiv (hdb z), partialLaplacian_eq_fderiv hab,
    partialLaplacian_eq_fderiv ha, partialLaplacian_eq_fderiv hb, sum_fin_five_ite_lt_four,
    sum_fin_five_ite_lt_four, sum_fin_five_ite_lt_four, h1 z, h2, h2, h2, h2]
  simp only [add_apply]
  ring

/-- Derivatives of a product up to order two, from derivative bounds on the factors. -/
theorem norm_iteratedFDeriv_mul_le_of_forall_le {φ χ : Vec 5 × ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {z : Vec 5 × ℝ} {A B : ℝ}
    (hA : ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j φ z‖ ≤ A)
    (hB : ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j χ z‖ ≤ B) {j : ℕ} (hj : j ≤ 2) :
    ‖iteratedFDeriv ℝ j (fun y => φ y * χ y) z‖ ≤ 4 * (A * B) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (by norm_num))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num))
  refine (norm_iteratedFDeriv_mul_le hφ hχ z (by exact_mod_cast le_top)).trans ?_
  calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ z‖
        * ‖iteratedFDeriv ℝ (j - i) χ z‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (A * B) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hA i (hi'.trans hj))
          (hB (j - i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _) hA0) (Nat.cast_nonneg _)
    _ = 2 ^ j * (A * B) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j
    _ ≤ 4 * (A * B) := by
        have h2 : (2 : ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hj
        have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
        nlinarith only [h2, hAB]

/-- Every derivative of order at most two of a compactly supported smooth function is bounded. -/
theorem exists_norm_iteratedFDeriv_le_of_hasCompactSupport {ψ : Vec 5 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j : ℕ, j ≤ 2 → ∀ z, ‖iteratedFDeriv ℝ j ψ z‖ ≤ A := by
  have hb : ∀ j : ℕ, ∃ C : ℝ, ∀ z, ‖iteratedFDeriv ℝ j ψ z‖ ≤ C := fun j =>
    (hψc.iteratedFDeriv j).exists_bound_of_continuous
      (hψ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  obtain ⟨C0, h0⟩ := hb 0
  obtain ⟨C1, h1⟩ := hb 1
  obtain ⟨C2, h2⟩ := hb 2
  refine ⟨max (max C0 C1) (max C2 0), le_max_of_le_right (le_max_right _ _), ?_⟩
  intro j hj z
  interval_cases j
  · exact (h0 z).trans (le_max_of_le_left (le_max_left _ _))
  · exact (h1 z).trans (le_max_of_le_left (le_max_right _ _))
  · exact (h2 z).trans (le_max_of_le_right (le_max_left _ _))

/-- The residual integrand vanishes off the support of the test function. -/
theorem residualIntegrand_eq_zero_of_notMem {ψ : Vec 5 × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {z : Vec 5 × ℝ} (hz : z ∉ tsupport ψ) (v : Vec 5) (d : ℝ) :
    -(timeDeriv 5 ψ z) - gradPair 5 ψ z v - d * ψ z - partialLaplacian 5 4 ψ z = 0 := by
  have h0 : ∀ j : ℕ, iteratedFDeriv ℝ j ψ z = 0 := fun j =>
    image_eq_zero_of_notMem_tsupport fun h => hz (tsupport_iteratedFDeriv_subset j h)
  have hb := abs_residualIntegrand_le hψ z v d
  simp only [h0, norm_zero, mul_zero, add_zero] at hb
  exact abs_nonpos_iff.mp hb

/-- Integrability of the pairing of a locally bounded scalar with the residual integrand of a
test function. -/
theorem integrable_mul_residualIntegrand {K : Set (Vec 5 × ℝ)} (hK : IsCompact K)
    {q d : Vec 5 × ℝ → ℝ} {b : Vec 5 × ℝ → Vec 5} {M : ℝ}
    (hq : AEStronglyMeasurable q (volume.restrict K))
    (hbm : AEStronglyMeasurable b (volume.restrict K))
    (hd : AEStronglyMeasurable d (volume.restrict K))
    (hbd : ∀ z ∈ K, |q z| ≤ M ∧ ‖b z‖ ≤ M ∧ |d z| ≤ M)
    {ψ : Vec 5 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψK : tsupport ψ ⊆ K) :
    Integrable (fun z => q z * (-(timeDeriv 5 ψ z) - gradPair 5 ψ z (b z) - d z * ψ z
      - partialLaplacian 5 4 ψ z)) := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hdψ : ∀ w, DifferentiableAt ℝ ψ w := fun w => hψ2.differentiable (by norm_num) w
  obtain ⟨A, hA0, hA⟩ := exists_norm_iteratedFDeriv_le_of_hasCompactSupport hψ hψc
  -- measurability of the integrand on `K`
  have hD : Continuous (fun p : (Vec 5 × ℝ) × (Vec 5 × ℝ) => fderiv ℝ ψ p.1 p.2) :=
    (hψ.continuous_fderiv (by simp)).comp continuous_fst |>.clm_apply
      continuous_snd
  have ht : Continuous (fun z => timeDeriv 5 ψ z) := by
    have : (fun z => timeDeriv 5 ψ z) = fun z => fderiv ℝ ψ z (0, 1) := by
      funext z
      exact timeDeriv_eq_fderiv (hdψ z)
    rw [this]
    exact hD.comp (continuous_id.prodMk continuous_const)
  have hl : Continuous (fun z => partialLaplacian 5 4 ψ z) := by
    have : (fun z => partialLaplacian 5 4 ψ z) = fun z => ∑ i : Fin 5, if (i : ℕ) < 4 then
        fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec i, 0)) z (basisVec i, 0) else 0 := by
      funext z
      exact partialLaplacian_eq_fderiv hψ2 z
    rw [this]
    refine continuous_finsetSum _ fun i _ => ?_
    split_ifs
    · exact (contDiff_fderiv_apply_top (contDiff_fderiv_apply_top hψ _) _).continuous
    · exact continuous_const
  have hg : AEStronglyMeasurable (fun z => gradPair 5 ψ z (b z)) (volume.restrict K) := by
    have : (fun z => gradPair 5 ψ z (b z)) = fun z => fderiv ℝ ψ z (b z, 0) := by
      funext z
      exact gradPair_eq_fderiv (hdψ z) _
    rw [this]
    exact hD.comp_aestronglyMeasurable
      (aestronglyMeasurable_id.prodMk (hbm.prodMk aestronglyMeasurable_const))
  have hmeas : AEStronglyMeasurable (fun z => q z * (-(timeDeriv 5 ψ z) - gradPair 5 ψ z (b z)
      - d z * ψ z - partialLaplacian 5 4 ψ z)) (volume.restrict K) :=
    hq.mul (((ht.aestronglyMeasurable.neg.sub hg).sub
      (hd.mul hψ.continuous.aestronglyMeasurable)).sub hl.aestronglyMeasurable)
  have hint : IntegrableOn (fun z => q z * (-(timeDeriv 5 ψ z) - gradPair 5 ψ z (b z)
      - d z * ψ z - partialLaplacian 5 4 ψ z)) K :=
    IntegrableOn.of_bound hK.measure_lt_top hmeas (M * ((1 + M) * A + M * A + 4 * A)) (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      obtain ⟨hqz, hbz, hdz⟩ := hbd z hz
      have hM : 0 ≤ M := (abs_nonneg _).trans hqz
      have hr := abs_residualIntegrand_le hψ2 z (b z) (d z)
      rw [Real.norm_eq_abs, abs_mul]
      have hr' : |-(timeDeriv 5 ψ z) - gradPair 5 ψ z (b z) - d z * ψ z
          - partialLaplacian 5 4 ψ z| ≤ (1 + M) * A + M * A + 4 * A := by
        refine hr.trans ?_
        gcongr
        · exact hA 1 (by norm_num) z
        · exact hA 0 (by norm_num) z
        · exact hA 2 (by norm_num) z
      exact mul_le_mul hqz hr' (abs_nonneg _) hM)
  refine hint.integrable_of_forall_notMem_eq_zero fun z hz => ?_
  rw [residualIntegrand_eq_zero_of_notMem hψ2 (fun h => hz (hψK h)), mul_zero]

end CIV
