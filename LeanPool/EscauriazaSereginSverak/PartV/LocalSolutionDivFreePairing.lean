/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionDivFreeSlice
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatWeighted

/-!
# The divergence pairing of the forced heat response at a fixed time

Fix a time `t` at which the weighted kernel integrals of a measurable tensor
`G` are finite. Pairing the forced heat response `Z_i = ∑_j ∂_j W₊ ⋆ G_ij` at
time `t` with `∂_i ψ` for a test function `ψ` and exchanging the integrals
writes the pairing as an integral over the kernel variable `(y, r)`; at every
kernel time `r > 0` for which the slice `G(·, t - r)` is square integrable and
double-divergence free, the inner integral vanishes by
`kernel_translate_pairing_sum_eq_zero`. This is the fixed-time step of the
divergence-free property of the forced heat response in
`prop:pv-local-solution`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A continuous compactly supported function on Vec3 is dominated by a
multiple of the weight `forcedHeatWeight`. -/
theorem abs_le_mul_forcedHeatWeight_of_vec3 {φ : Vec3 → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |φ x| ≤ c * forcedHeatWeight x := by
  obtain ⟨R, hR0, hRball⟩ := hφc.isCompact.isBounded.subset_closedBall_lt 0 (0 : Vec3)
  obtain ⟨B, hB⟩ := hφc.exists_bound_of_continuous hφ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have h1R : 0 < 1 + R := by linarith only [hR0]
  have h1R2 : 0 < (1 + R) ^ 2 := pow_pos h1R 2
  refine ⟨B * (1 + R) ^ 2, mul_nonneg hB0 h1R2.le, fun x => ?_⟩
  by_cases hx : φ x = 0
  · rw [hx, abs_zero]
    exact mul_nonneg (mul_nonneg hB0 h1R2.le) (forcedHeatWeight_pos _).le
  · have hmem := hRball (subset_tsupport φ hx)
    have hnorm : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hmem
    have hw : ((1 + R) ^ 2)⁻¹ ≤ forcedHeatWeight x := by
      unfold forcedHeatWeight
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith only [hnorm]) 2
    calc
      |φ x| ≤ B := by
        rw [← Real.norm_eq_abs]
        exact hB x
      _ = B * (1 + R) ^ 2 * ((1 + R) ^ 2)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ h1R2.ne', mul_one]
      _ ≤ B * (1 + R) ^ 2 * forcedHeatWeight x :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hB0 h1R2.le)

/-- At a time `t` where the weighted kernel integrals of a measurable tensor are
finite, and for which almost every earlier slice is square integrable and
double-divergence free, the forced heat response at time `t` is weakly
divergence free. -/
theorem forcedHeat_divergence_pairing_eq_zero {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hGm : ∀ i j, Measurable (G i j)) {t : ℝ}
    (hfin : ∀ i j, ∫⁻ x : Vec3, ENNReal.ofReal (forcedHeatWeight x) *
      ∫⁻ p : Vec3 × ℝ, ‖heatKernelSpaceDerivative p.1 p.2 j * G i j (x - p.1, t - p.2)‖ₑ < ∞)
    (hslice : ∀ᵐ s ∂(volume : Measure ℝ),
      (∀ i j, MemLp (fun y : Vec3 => G i j (y, s)) 2 volume) ∧
      ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Vec3, G i j (y, s) * CKN.mixedSecond φ i j y = 0)
    (ψ : CKN.WeakTestFunction (Set.univ : Set Vec3)) :
    ∫ x : Vec3, ∑ i : Fin 3, forcedHeat G (x, t) i * ψ.partialDeriv i x = 0 := by
  set d : Fin 3 → Vec3 → ℝ := fun i x => ψ.partialDeriv i x with hd_def
  have hdc (i : Fin 3) : Continuous (d i) :=
    (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds (i : Fin 3) : HasCompactSupport (d i) :=
    ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) _
  choose c hc0 hc using fun i => abs_le_mul_forcedHeatWeight_of_vec3 (hdc i) (hds i)
  set J : Fin 3 → Fin 3 → Vec3 × (Vec3 × ℝ) → ℝ := fun i j q =>
    heatKernelSpaceDerivative q.2.1 q.2.2 j * G i j (q.1 - q.2.1, t - q.2.2) * d i q.1
    with hJ_def
  have hJm (i j : Fin 3) : Measurable (J i j) := by
    have hshift : Measurable (fun q : Vec3 × (Vec3 × ℝ) =>
        ((q.1 - q.2.1, t - q.2.2) : Vec3 × ℝ)) := by fun_prop
    exact (((heatKernelSpaceDerivative_vecTime_measurable j).comp measurable_snd).mul
      ((hGm i j).comp hshift)).mul ((hdc i).measurable.comp measurable_fst)
  have hJ (i j : Fin 3) :
      Integrable (J i j) ((volume : Measure Vec3).prod (volume : Measure (Vec3 × ℝ))) := by
    refine ⟨(hJm i j).aestronglyMeasurable, ?_⟩
    have hpt (x : Vec3) : ∫⁻ p : Vec3 × ℝ, ‖J i j (x, p)‖ₑ ≤
        ENNReal.ofReal (c i) * (ENNReal.ofReal (forcedHeatWeight x) *
          ∫⁻ p : Vec3 × ℝ,
            ‖heatKernelSpaceDerivative p.1 p.2 j * G i j (x - p.1, t - p.2)‖ₑ) := by
      have hdx : ‖d i x‖ₑ ≤ ENNReal.ofReal (c i) * ENNReal.ofReal (forcedHeatWeight x) := by
        rw [← ENNReal.ofReal_mul (hc0 i), Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (hc i x)
      calc
        ∫⁻ p : Vec3 × ℝ, ‖J i j (x, p)‖ₑ = ∫⁻ p : Vec3 × ℝ,
            ‖heatKernelSpaceDerivative p.1 p.2 j * G i j (x - p.1, t - p.2)‖ₑ * ‖d i x‖ₑ := by
          congr 1
          funext p
          simp only [J]
          rw [enorm_mul]
        _ = (∫⁻ p : Vec3 × ℝ,
            ‖heatKernelSpaceDerivative p.1 p.2 j * G i j (x - p.1, t - p.2)‖ₑ) * ‖d i x‖ₑ :=
          lintegral_mul_const' _ _ enorm_ne_top
        _ ≤ (∫⁻ p : Vec3 × ℝ,
            ‖heatKernelSpaceDerivative p.1 p.2 j * G i j (x - p.1, t - p.2)‖ₑ) *
              (ENNReal.ofReal (c i) * ENNReal.ofReal (forcedHeatWeight x)) := by
          gcongr
        _ = _ := by ring
    change ∫⁻ q, ‖J i j q‖ₑ ∂((volume : Measure Vec3).prod (volume : Measure (Vec3 × ℝ))) < ∞
    rw [lintegral_prod _ (hJm i j).enorm.aemeasurable]
    calc
      ∫⁻ x : Vec3, ∫⁻ p : Vec3 × ℝ, ‖J i j (x, p)‖ₑ ≤
          ∫⁻ x : Vec3, ENNReal.ofReal (c i) * (ENNReal.ofReal (forcedHeatWeight x) *
            ∫⁻ p : Vec3 × ℝ,
              ‖heatKernelSpaceDerivative p.1 p.2 j * G i j (x - p.1, t - p.2)‖ₑ) :=
        lintegral_mono hpt
      _ = ENNReal.ofReal (c i) * ∫⁻ x : Vec3, ENNReal.ofReal (forcedHeatWeight x) *
            ∫⁻ p : Vec3 × ℝ,
              ‖heatKernelSpaceDerivative p.1 p.2 j * G i j (x - p.1, t - p.2)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin i j)
  have hZ (i : Fin 3) : ∀ᵐ x ∂(volume : Measure Vec3),
      forcedHeat G (x, t) i * d i x = ∑ j : Fin 3, ∫ p : Vec3 × ℝ, J i j (x, p) := by
    filter_upwards [ae_all_iff.2 fun j => (hJ i j).prod_right_ae] with x hx
    change (∫ p : Vec3 × ℝ, ∑ j : Fin 3,
        heatKernelSpaceDerivative p.1 p.2 j * G i j (x - p.1, t - p.2)) * d i x = _
    rw [← integral_mul_const, ← integral_finsetSum _ fun j _ => hx j]
    congr 1
    funext p
    simp only [J, Finset.sum_mul]
  have hint1 (i j : Fin 3) : Integrable (fun x : Vec3 => ∫ p : Vec3 × ℝ, J i j (x, p)) :=
    (hJ i j).integral_prod_left
  have hint2 (i j : Fin 3) : Integrable (fun p : Vec3 × ℝ => ∫ x : Vec3, J i j (x, p))
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) :=
    (hJ i j).integral_prod_right
  have hstep : ∫ x : Vec3, ∑ i : Fin 3, forcedHeat G (x, t) i * d i x =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ r : ℝ, ∫ y : Vec3, ∫ x : Vec3, J i j (x, (y, r)) := by
    calc
      ∫ x : Vec3, ∑ i : Fin 3, forcedHeat G (x, t) i * d i x =
          ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∫ p : Vec3 × ℝ, J i j (x, p) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.2 hZ] with x hx
        exact Finset.sum_congr rfl fun i _ => hx i
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3, ∫ p : Vec3 × ℝ, J i j (x, p) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint1 i j]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint1 i j
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ p : Vec3 × ℝ, ∫ x : Vec3, J i j (x, p) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        exact integral_integral_swap (hJ i j)
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ r : ℝ, ∫ y : Vec3, ∫ x : Vec3, J i j (x, (y, r)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        exact integral_prod_symm _ (hint2 i j)
  have hr_ae : ∀ᵐ r ∂(volume : Measure ℝ),
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Vec3, ∫ x : Vec3, J i j (x, (y, r)) = 0 := by
    have hq := ((volume : Measure ℝ).measurePreserving_sub_left t).quasiMeasurePreserving.ae
      hslice
    filter_upwards [hq] with r hr
    obtain ⟨hL2, hdd⟩ := hr
    by_cases hr0 : 0 < r
    · have hrew (i j : Fin 3) (y : Vec3) : ∫ x : Vec3, J i j (x, (y, r)) =
          heatKernelSpaceDerivative y r j * ∫ w : Vec3, G i j (w, t - r) * d i (w + y) := by
        have h1 : ∫ w : Vec3, G i j (w, t - r) * d i (w + y) =
            ∫ x : Vec3, G i j (x - y, t - r) * d i x := by
          have h := integral_add_right_eq_self (μ := (volume : Measure Vec3))
            (fun x : Vec3 => G i j (x - y, t - r) * d i x) y
          simpa only [add_sub_cancel_right] using h
        rw [h1, ← integral_const_mul]
        congr 1
        funext x
        simp only [J]
        ring
      simp only [hrew]
      exact kernel_translate_pairing_sum_eq_zero hr0 (g := fun i j y => G i j (y, t - r))
        hL2 hdd ψ.contDiff ψ.hasCompactSupport
    · have hzero (i j : Fin 3) (y : Vec3) : ∫ x : Vec3, J i j (x, (y, r)) = 0 := by
        simp [J, heatKernelSpaceDerivative, hr0]
      simp [hzero]
  rw [hstep]
  have hswap : ∑ i : Fin 3, ∑ j : Fin 3, ∫ r : ℝ, ∫ y : Vec3, ∫ x : Vec3, J i j (x, (y, r)) =
      ∫ r : ℝ, ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Vec3, ∫ x : Vec3, J i j (x, (y, r)) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint2 i j).integral_prod_right]
    exact Finset.sum_congr rfl fun i _ =>
      (integral_finsetSum _ fun j _ => (hint2 i j).integral_prod_right).symm
  rw [hswap]
  exact integral_eq_zero_of_ae hr_ae

end ESS

end
