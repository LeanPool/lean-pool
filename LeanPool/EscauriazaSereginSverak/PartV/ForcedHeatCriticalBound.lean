/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatCriticalSlice
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The critical estimate for the smooth forced heat response

Integrating the slice Gagliardo–Nirenberg estimate in time, letting the
regularization vanish, and applying Hölder's inequality to
`Y = ∫∫ |Z| |g|²` gives

`∫∫ |Z|⁵ ≤ C (∫∫ |g|^{5/2})²`, `sup_t ∫ |Z(t)|³ ≤ C (∫∫ |g|^{5/2})^{6/5}`,

the smooth-data form of `eq:pv-stokes-l5` in `lem:pv-stokes`, with an absolute
constant `C`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The absolute constant `9 κ² 27^{2/3}` of the critical estimate, with `κ` the
real Sobolev constant. -/
@[expose] def criticalGNConstant : ℝ :=
  9 * gagliardoNirenbergSobolevConstant.toReal ^ 2 * (27 : ℝ) ^ (2 / 3 : ℝ)

theorem criticalGNConstant_nonneg : 0 ≤ criticalGNConstant := by
  unfold criticalGNConstant
  positivity

/-- The regularized critical profile, integrated over a time window, is bounded
by `C Y^{5/3}` with `Y = ∫∫ |Z| |g|²`. -/
theorem response_critical_profile_window_le {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2}) {η : ℝ} (hη : 0 < η)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ p, |heatRegG η (responseVec g p)| ^ (10 / 3 : ℝ)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) ≤
      criticalGNConstant * (∫ p, vec3EuclideanNorm (responseVec g p) *
        ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)))) ^ (5 / 3 : ℝ) := by
  set μ := (volume : Measure Vec3).prod (volume.restrict (Ioc (0 : ℝ) τ))
  set Y : ℝ := ∫ p, vec3EuclideanNorm (responseVec g p) *
    ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2 ∂μ with hY
  set κ : ℝ := gagliardoNirenbergSobolevConstant.toReal
  have hY0 : 0 ≤ Y := integral_nonneg fun p => mul_nonneg (vec3EuclideanNorm_nonneg _)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  obtain ⟨hEY, hDY⟩ := response_critical_window_bounds hg hgc hgpos hη hτ
  obtain ⟨_, hF2, _⟩ := response_critical_integrable hg hgc hη 0 τ
  obtain ⟨M, hM, hq⟩ := response_sq_decay hg hgc
  have hT : ContDiff ℝ 1 (heatRegTest η) := (heatRegTest_contDiff hη).of_le (by simp)
  obtain ⟨hZc, _, _⟩ := response_continuity hg hgc hT
  let F : Vec3 × ℝ → ℝ := fun p => |heatRegG η (responseVec g p)| ^ (10 / 3 : ℝ)
  have hFc : Continuous F :=
    (((heatRegG_contDiff hη).continuous.comp hZc).abs.rpow_const fun _ => Or.inr (by norm_num))
  have hFb (p : Vec3 × ℝ) : F p ≤ (M ^ 2) ^ (3 / 2 : ℝ) * M /
      (1 + vec3EuclideanNorm p.1) ^ 6 := by
    obtain ⟨hG0, hGle⟩ := heatRegG_nonneg_le_rpow hη (responseVec g p)
    set q : ℝ := ∑ i : Fin 3, (responseVec g p i) ^ 2
    have hq0 : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hqM : q ≤ M ^ 2 := by
      have hn := (hq p).1
      have hsq := vec3EuclideanNorm_sq (responseVec g p)
      nlinarith only [hn, hsq, vec3EuclideanNorm_nonneg (responseVec g p)]
    calc
      F p ≤ (q ^ (3 / 4 : ℝ)) ^ (10 / 3 : ℝ) := by
        simp only [F]
        rw [abs_of_nonneg hG0]
        exact Real.rpow_le_rpow hG0 hGle (by norm_num)
      _ = q ^ (1 : ℝ) * q ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_mul hq0, ← Real.rpow_add' hq0 (by norm_num)]
        norm_num
      _ ≤ (M ^ 2) ^ (3 / 2 : ℝ) * (M / (1 + vec3EuclideanNorm p.1) ^ 6) := by
        rw [Real.rpow_one, mul_comm]
        exact mul_le_mul (Real.rpow_le_rpow hq0 hqM (by norm_num)) (hq p).2 hq0
          (by positivity)
      _ = _ := by ring
  have hFint : Integrable F μ :=
    integrable_window_of_decay (C := (M ^ 2) ^ (3 / 2 : ℝ) * M) hFc (by positivity)
    fun x t _ => by
      rw [abs_of_nonneg (by positivity)]
      exact hFb (x, t)
  let D : Vec3 × ℝ → ℝ := fun p => ∑ j : Fin 3, ∑ i : Fin 3,
    fderiv ℝ (heatRegTest η) (responseVec g p) (responseGrad g j p) i * responseGrad g j p i
  have hD0 (p : Vec3 × ℝ) : 0 ≤ D p :=
    Finset.sum_nonneg fun j _ => (mul_nonneg (sub_nonneg.mpr (heatReg_root_ge_eta hη _))
      (Finset.sum_nonneg fun i _ => sq_nonneg _)).trans (heatRegTest_dissipation_ge hη _ _)
  have hK0 : 0 ≤ κ ^ 2 * (27 * Y) ^ (2 / 3 : ℝ) * (9 / 2 : ℝ) := by positivity
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) τ)),
      ∫ x, F (x, t) ≤ (κ ^ 2 * (27 * Y) ^ (2 / 3 : ℝ) * (9 / 2 : ℝ)) * ∫ x, D (x, t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hgn := response_critical_slice_gn hg hgc hη t
    have hE := hEY t ⟨ht.1.le, ht.2⟩
    have hE0 : 0 ≤ ∫ x, heatRegEnergy η (responseVec g (x, t)) :=
      integral_nonneg fun x => heatRegEnergy_nonneg hη _
    have hDt0 : 0 ≤ ∫ x, D (x, t) := integral_nonneg fun x => hD0 (x, t)
    refine hgn.trans ?_
    have hmono : (27 * ∫ x, heatRegEnergy η (responseVec g (x, t))) ^ (2 / 3 : ℝ) ≤
        (27 * Y) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith only [hE]) (by norm_num)
    calc
      κ ^ 2 * (27 * ∫ x, heatRegEnergy η (responseVec g (x, t))) ^ (2 / 3 : ℝ) *
          ((9 / 2 : ℝ) * ∫ x, D (x, t)) ≤
          κ ^ 2 * (27 * Y) ^ (2 / 3 : ℝ) * ((9 / 2 : ℝ) * ∫ x, D (x, t)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (sq_nonneg _))
          (by positivity)
      _ = _ := by ring
  have hFslice := hFint.integral_prod_right
  have hDslice := hF2.integral_prod_right
  have hstep := integral_mono_ae hFslice (hDslice.const_mul _) hslice
  rw [integral_const_mul, ← integral_prod_symm _ hF2, ← integral_prod_symm _ hFint] at hstep
  change ∫ p, F p ∂μ ≤ _
  refine hstep.trans ?_
  have hY23 : (27 * Y) ^ (2 / 3 : ℝ) * Y = (27 : ℝ) ^ (2 / 3 : ℝ) * Y ^ (5 / 3 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hY0, mul_assoc]
    congr 1
    rw [show (5 / 3 : ℝ) = 2 / 3 + 1 by norm_num, Real.rpow_add' hY0 (by norm_num),
      Real.rpow_one]
  calc
    κ ^ 2 * (27 * Y) ^ (2 / 3 : ℝ) * (9 / 2 : ℝ) * ∫ p, D p ∂μ ≤
        κ ^ 2 * (27 * Y) ^ (2 / 3 : ℝ) * (9 / 2 : ℝ) * (2 * Y) :=
      mul_le_mul_of_nonneg_left hDY hK0
    _ = 9 * κ ^ 2 * ((27 * Y) ^ (2 / 3 : ℝ) * Y) := by ring
    _ = criticalGNConstant * Y ^ (5 / 3 : ℝ) := by
      rw [hY23, criticalGNConstant]
      ring

end ESS

end
