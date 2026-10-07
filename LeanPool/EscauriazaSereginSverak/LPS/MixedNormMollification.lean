/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSpaceTimeMollify
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Mixed norm convergence under spatial mollification

Spatial mollification converges in finite mixed Lebesgue norms on a finite
time slab. The spatial and temporal exponents may differ.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_eLpNorm_ofReal_rpow_eq {E : Type} [NormedAddCommGroup E]
    {f : Vec3 → E} {p : ℝ} (hp : 0 < p)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f (ENNReal.ofReal p) volume =
      (∫⁻ x, ‖f x‖ₑ ^ p ∂volume) ^ (1 / p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf,
    ENNReal.toReal_ofReal hp.le]

/-- Slice-wise spatial mollification converges in the mixed norm
`L^p_t L^q_x` when both exponents are finite and at least one. -/
theorem lps_mollify_mixed_norm_tendsto
    {T p q : ℝ} {f : ParabolicPoint → ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hfSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => f (x,t)) (ENNReal.ofReal q) volume)
    (hMoment : (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal q) volume ^ p) < ⊤) :
    Tendsto (fun n => ∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => serrinSM f n (x,t) - f (x,t))
        (ENNReal.ofReal q) volume ^ p) atTop (𝓝 0) := by
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod μt
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqtop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  let N : ℕ → ℝ → ℝ≥0∞ := fun n t =>
    eLpNorm (fun x : Vec3 => serrinSM f n (x,t) - f (x,t))
      (ENNReal.ofReal q) volume
  have hNmeas : ∀ n, AEMeasurable (N n) μt := by
    intro n
    have hfn : AEStronglyMeasurable
        (fun z : ParabolicPoint => serrinSM f n z - f z)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
      exact (serrinSM_aestronglyMeasurable hf n).sub hf
    have hfnProd : AEStronglyMeasurable (fun z : Vec3 × ℝ =>
        serrinSM f n z - f z) ν := by
      change AEStronglyMeasurable (fun z : ParabolicPoint => serrinSM f n z - f z)
        ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))
      rw [← serrin_slab_measure_eq T]
      exact hfn
    have hG : AEMeasurable (fun z : Vec3 × ℝ =>
        ‖serrinSM f n z - f z‖ₑ ^ q) ν := hfnProd.enorm.pow_const q
    have hlin : AEMeasurable (fun t : ℝ =>
        ∫⁻ x : Vec3, ‖serrinSM f n (x,t) - f (x,t)‖ₑ ^ q ∂volume) μt :=
      hG.lintegral_prod_left'
    have hpow := hlin.pow_const (1 / q)
    have hsmSliceAE : ∀ᵐ t ∂μt,
        AEStronglyMeasurable (fun x : Vec3 => serrinSM f n (x,t)) volume := by
      have hsmAll := serrinSM_aestronglyMeasurable hf n
      rw [serrin_slab_measure_eq T] at hsmAll
      exact hsmAll.prodMk_right
    have hEq : (fun t : ℝ => N n t) =ᵐ[μt] fun t =>
        (∫⁻ x : Vec3, ‖serrinSM f n (x,t) - f (x,t)‖ₑ ^ q ∂volume) ^ (1 / q) := by
      filter_upwards [hfSlice, hsmSliceAE] with t ht hsm
      have hformula := lps_eLpNorm_ofReal_rpow_eq hq0
        (hsm.sub ht.aestronglyMeasurable)
      exact hformula
    exact hpow.congr hEq.symm
  have hconstTop : (2 : ℝ≥0∞) ^ p < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num)
  have hdomInt : (∫⁻ t in Ioo 0 T,
      (2 : ℝ≥0∞) ^ p *
        eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal q) volume ^ p) < ⊤ := by
    rw [lintegral_const_mul' _ _ hconstTop.ne]
    exact ENNReal.mul_lt_top hconstTop hMoment
  have hDCT : Tendsto (fun n => ∫⁻ t : ℝ, N n t ^ p ∂μt) atTop
      (𝓝 (∫⁻ t : ℝ, (0 : ℝ≥0∞) ∂μt)) := by
    refine tendsto_lintegral_of_dominated_convergence'
      (fun t => (2 : ℝ≥0∞) ^ p *
        eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal q) volume ^ p)
      (fun n => (hNmeas n).pow_const p) ?_ ?_ ?_
    · intro n
      filter_upwards [hfSlice] with t ht
      have hmol := CKN.young_convolution_nonneg_integral_one_of_aemeasurable
        (d := 3) (p := ENNReal.ofReal q) (by exact ENNReal.one_le_ofReal.mpr hq)
        hqtop (CKN.mollifier_nonneg (serrinRadius_pos n))
        ((CKN.mollifier_contDiff (d := 3) (serrinRadius_pos n) (n := 0)).continuous
          |>.integrable_of_hasCompactSupport (CKN.mollifier_hasCompactSupport _))
        (CKN.mollifier_integral_one (serrinRadius_pos n))
        (CKN.mollifier_contDiff (d := 3) (serrinRadius_pos n) (n := 0)).continuous.measurable
        ht.aestronglyMeasurable.aemeasurable
      have hmol' : eLpNorm (fun x : Vec3 => serrinSM f n (x,t))
          (ENNReal.ofReal q) volume ≤
          eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal q) volume := by
        simpa [serrinSM, CKN.mollify, CKN.mollifier] using hmol
      have htri : N n t ≤ 2 *
          eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal q) volume := by
        calc
          N n t ≤ eLpNorm (fun x : Vec3 => serrinSM f n (x,t))
              (ENNReal.ofReal q) volume +
                eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal q) volume :=
            eLpNorm_sub_le (ENNReal.one_le_ofReal.mpr hq)
          _ ≤ _ := by rw [two_mul]; gcongr
      calc
        N n t ^ p ≤ (2 * eLpNorm (fun x : Vec3 => f (x,t))
            (ENNReal.ofReal q) volume) ^ p :=
          ENNReal.rpow_le_rpow htri (by positivity)
        _ = (2 : ℝ≥0∞) ^ p *
            eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal q) volume ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    · rw [lintegral_const_mul' _ _ hconstTop.ne]
      exact ENNReal.mul_ne_top hconstTop.ne hMoment.ne
    · filter_upwards [hfSlice] with t ht
      have hconv := CKN.tendsto_eLpNorm_sub_zero_mollify
        (p := ENNReal.ofReal q) (ENNReal.one_le_ofReal.mpr hq) hqtop ht
        serrinRadius_tendsto serrinRadius_pos
      have hconvN : Tendsto (fun n : ℕ => N n t) atTop (𝓝 0) := by
        simpa [N, serrinSM] using hconv
      have hcont : Continuous (fun a : ℝ≥0∞ => a ^ p) :=
        ENNReal.continuous_rpow_const
      have hpow := (hcont.tendsto 0).comp hconvN
      have hzero : (0 : ℝ≥0∞) = 0 ^ p :=
        (ENNReal.zero_rpow_of_pos (by positivity : 0 < p)).symm
      rw [hzero]
      exact hpow
  simpa [N, μt] using hDCT

end ESS

end
