/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProofVorticity
public import LeanPool.EscauriazaSereginSverak.Linear.BUAnyGrowth
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalWeak
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalDerivativeL2
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalAE
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Ess Local Proof Backward Uniqueness

Local endpoint regularity through vorticity estimates and backward uniqueness.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem essLocal_enorm_smul_sq_le (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) {V : Type*} [ENorm V] [SMul ℝ V] [ENormSMulClass ℝ V]
    (v : V) :
    ‖a • v‖ₑ ^ (2 : ℝ) ≤ ‖v‖ₑ ^ (2 : ℝ) := by
  have hscalar : ‖a‖ₑ ≤ 1 := by
    rw [Real.enorm_of_nonneg ha0]
    exact ENNReal.ofReal_le_one.mpr ha1
  have hnorm : ‖a • v‖ₑ ≤ ‖v‖ₑ := by
    rw [enorm_smul]
    calc
      ‖a‖ₑ * ‖v‖ₑ ≤ 1 * ‖v‖ₑ :=
        mul_le_mul_of_nonneg_right hscalar (by positivity)
      _ = ‖v‖ₑ := one_mul _
  exact ENNReal.rpow_le_rpow hnorm (by norm_num)

private theorem essLocal_backwardUniqueness_zero_firstSlab
    {C : ℝ} (hC : 0 ≤ C) (g : ParabolicPoint → Vec3)
    (dg : ParabolicPoint → Fin 3 → Vec3)
    (d2g : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (dtg : ParabolicPoint → Vec3)
    (hcont : ContinuousOn g
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ico (0 : ℝ) 1)))
    (hinit : ∀ y : Vec3, 0 < y 2 → g (y, 0) = 0)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1)
      g dg d2g dtg)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) +
        ‖dtg z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1))),
      vec3EuclideanNorm (fun i => dtg z i + ∑ j, d2g z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq g dg z) + vec3EuclideanNorm (g z)))
    (hbound : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1),
      vec3EuclideanNorm (g z) ≤ C) :
    ∀ y : Vec3, 0 < y 2 → ∀ s ∈ Ioo (0 : ℝ) 1, g (y, s) = 0 := by
  let a : ℝ := (C + 1)⁻¹
  have hApos : 0 < C + 1 := by linarith
  have ha : 0 < a := by dsimp [a]; exact inv_pos.mpr hApos
  have ha_le : a ≤ 1 := by
    dsimp [a]
    rw [inv_le_one₀ hApos]
    linarith
  have haC : a * C ≤ 1 := by
    calc
      a * C = C / (C + 1) := by simp [a, div_eq_mul_inv, mul_comm]
      _ ≤ 1 := (div_le_iff₀ hApos).2 (by linarith)
  let w : ParabolicPoint → Vec3 := fun z => a • g z
  let Dw : ParabolicPoint → Fin 3 → Vec3 := fun z i j => a * dg z i j
  let D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k => a * d2g z i j k
  let Dtw : ParabolicPoint → Vec3 := fun z i => a * dtg z i
  have hweakW : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1)
      w Dw D2w Dtw := by
    simpa only [w, Dw, D2w, Dtw] using essLocal_scale_weakDerivs a hweak
  have hinitW : ∀ y : Vec3, 0 < y 2 → w (y, 0) = 0 := by
    intro y hy
    simpa [w] using congrArg (fun v : Vec3 => a • v) (hinit y hy)
  have hboundW : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1),
      vec3EuclideanNorm (w z) ≤ Real.exp (0 * vec3EuclideanNorm z.1 ^ 2) := by
    intro z hz
    have hnorm : vec3EuclideanNorm (w z) = a * vec3EuclideanNorm (g z) := by
      simp [w, vec3EuclideanNorm_smul, abs_of_pos ha]
    rw [hnorm]
    calc
      a * vec3EuclideanNorm (g z) ≤ a * C :=
        mul_le_mul_of_nonneg_left (by simpa using hbound z hz) ha.le
      _ ≤ 1 := haC
      _ = Real.exp (0 * vec3EuclideanNorm z.1 ^ 2) := by simp
  have hineqW : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq w Dw z) + vec3EuclideanNorm (w z)) := by
    filter_upwards [hineq] with z hz
    have hheat : (fun i => Dtw z i + ∑ j, D2w z i j j) =
        a • (fun i => dtg z i + ∑ j, d2g z i j j) := by
      funext i
      simp [Dtw, D2w, Finset.mul_sum, mul_add]
    have hnorm : vec3EuclideanNorm (w z) = a * vec3EuclideanNorm (g z) := by
      simp [w, vec3EuclideanNorm_smul, abs_of_pos ha]
    have hgrad : spatialGradientSq w Dw z = a ^ 2 * spatialGradientSq g dg z := by
      simp [spatialGradientSq, Dw, mul_pow, ← Finset.mul_sum]
    have hsqrt : Real.sqrt (spatialGradientSq w Dw z) =
        a * Real.sqrt (spatialGradientSq g dg z) := by
      rw [hgrad, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
    rw [hheat, vec3EuclideanNorm_smul, abs_of_pos ha, hnorm, hsqrt]
    have h' := mul_le_mul_of_nonneg_left hz ha.le
    convert h' using 1 <;> ring
  have hL2W : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) +
        ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    intro S hS hSb
    have hpoint (z : ParabolicPoint) :
        ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ) ≤
          ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) + ‖dtg z‖ₑ ^ (2 : ℝ) := by
      dsimp [Dw, D2w, Dtw]
      exact add_le_add (add_le_add
        (essLocal_enorm_smul_sq_le a ha.le ha_le (dg z))
        (essLocal_enorm_smul_sq_le a ha.le ha_le (d2g z)))
        (essLocal_enorm_smul_sq_le a ha.le ha_le (dtg z))
    exact (lintegral_mono hpoint).trans_lt (hL2 S hS hSb)
  have hcontW : ContinuousOn w
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ico (0 : ℝ) 1)) := by
    change ContinuousOn ((fun _ : ParabolicPoint => a) • g) _
    exact continuousOn_const.smul hcont
  have hBU := backwardUniqueness_real_growth (C + 1) 0 (by linarith)
    w Dw D2w Dtw hcontW hinitW hweakW hL2W hineqW hboundW
  intro y hy s hs
  have hz := hBU (y, s) ⟨hy, ⟨hs.1, hs.2⟩⟩
  have hzero : a • g (y, s) = 0 := by simpa [w] using hz
  rcases smul_eq_zero.mp hzero with ha0 | hg0
  · exact False.elim (ne_of_gt ha ha0)
  · exact hg0

private theorem essLocal_continuousZero_at_one
    {V : Type*} [TopologicalSpace V] [T2Space V] (f : ℝ → V)
    (hcont : ContinuousOn f (Ico (0 : ℝ) 2))
    (hzero : ∀ s ∈ Ioo (0 : ℝ) 1, f s = 0) : f 1 = 0 := by
  let s : ℕ → ℝ := fun n => 1 - (1 / 2 : ℝ) ^ n
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hs : Tendsto s atTop (𝓝 1) := by
    simpa [s] using tendsto_const_nhds.sub hp
  have hseq : Tendsto (fun n : ℕ => f (s n)) atTop (𝓝 (f 1)) := by
    have hcont1 := hcont.continuousAt (by
      have hmem : (1 : ℝ) ∈ interior (Ico (0 : ℝ) 2) := by
        rw [interior_Ico]
        norm_num
      exact mem_interior_iff_mem_nhds.mp hmem)
    exact hcont1.tendsto.comp hs
  have hseqZero : ∀ᶠ n : ℕ in atTop, f (s n) = 0 := by
    have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n :=
      eventually_atTop.2 ⟨1, fun _ hn => hn⟩
    filter_upwards [hev] with n hn
    apply hzero (s n)
    dsimp [s]
    have hp0 : 0 < (1 / 2 : ℝ) ^ n := by positivity
    have hp1 : (1 / 2 : ℝ) ^ n < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    exact ⟨by linarith only [hp1], by linarith only [hp0]⟩
  have hseqZeroEq : (fun _ : ℕ => (0 : V)) =ᶠ[atTop] (fun n => f (s n)) := by
    filter_upwards [hseqZero] with n hn
    exact hn.symm
  have hseqZero' : Tendsto (fun n => f (s n)) atTop (𝓝 (0 : V)) :=
    tendsto_const_nhds.congr' hseqZeroEq
  exact tendsto_nhds_unique hseq hseqZero'

private theorem essLocal_reflectedDerivativeL2_finite
    {Ω Qsource Qtarget : Set ParabolicPoint}
    {ω : ParabolicPoint → Vec3} {Dω : ParabolicPoint → Fin 3 → Vec3}
    {D2ω : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtω : ParabolicPoint → Vec3}
    (e : ParabolicPoint ≃ₜ ParabolicPoint)
    (g : ParabolicPoint → Vec3) (dg : ParabolicPoint → Fin 3 → Vec3)
    (d2g : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (dtg : ParabolicPoint → Vec3)
    (hmp : MeasurePreserving e (volume : Measure ParabolicPoint)
      (volume : Measure ParabolicPoint))
    (hpointMap : ∀ z ∈ Qtarget, e z ∈ Qsource)
    (hEbounded : ∀ S : Set ParabolicPoint, Bornology.IsBounded S →
      Bornology.IsBounded (e '' S))
    (hderiv : HasSpaceTimeWeakDerivs Ω (Ioo (-2 : ℝ) 0) ω Dω D2ω Dtω)
    (hL2 : ∀ S : Set ParabolicPoint, S ⊆ Qsource → Bornology.IsBounded S →
      (∫⁻ z in S, ‖ω z‖ₑ ^ (2 : ℝ) + ‖Dω z‖ₑ ^ (2 : ℝ) +
        ‖D2ω z‖ₑ ^ (2 : ℝ) + ‖Dtω z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hg : ∀ z, g z = ω (e z))
    (hdg : ∀ z i j, dg z i j = Dω (e z) i j)
    (hd2g : ∀ z i j k, d2g z i j k = D2ω (e z) i j k)
    (hdtg : ∀ z i, dtg z i = -Dtω (e z) i) :
    ∀ S : Set ParabolicPoint, S ⊆ Qtarget → Bornology.IsBounded S →
      (∫⁻ z in S, ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) +
        ‖dtg z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  let F : ParabolicPoint → ℝ≥0∞ := fun z =>
    ‖Dω z‖ₑ ^ (2 : ℝ) + ‖D2ω z‖ₑ ^ (2 : ℝ) + ‖Dtω z‖ₑ ^ (2 : ℝ)
  have hsourceL2 : ∀ S : Set ParabolicPoint, S ⊆ Qtarget →
      Bornology.IsBounded S → (∫⁻ z in S, F (e z)) < ⊤ := by
    intro S hS hSb
    let T := e '' S
    have hTsub : T ⊆ Qsource := by
      rintro z ⟨y, hy, rfl⟩
      exact hpointMap y (hS hy)
    have hTbounded : Bornology.IsBounded T := hEbounded S hSb
    have htop := hL2 T hTsub hTbounded
    have hcomponent : (∫⁻ z in T, F z) < ⊤ := by
      refine (lintegral_mono fun z => ?_).trans_lt htop
      dsimp [F]
      have hωnonneg : (0 : ℝ≥0∞) ≤ ‖ω z‖ₑ ^ (2 : ℝ) := by positivity
      exact le_add_of_nonneg_left hωnonneg
    have hmapS : Measure.map e (volume.restrict S) = volume.restrict T :=
      (hmp.restrict_image_emb e.measurableEmbedding S).map_eq
    have hDmeas : AEStronglyMeasurable Dω (volume.restrict T) :=
      (hderiv.2.1.mono_set hTsub).aestronglyMeasurable
    have hD2meas : AEStronglyMeasurable D2ω (volume.restrict T) :=
      (hderiv.2.2.1.mono_set hTsub).aestronglyMeasurable
    have hDtmeas : AEStronglyMeasurable Dtω (volume.restrict T) :=
      (hderiv.2.2.2.1.mono_set hTsub).aestronglyMeasurable
    have hFmeas : AEMeasurable F (volume.restrict T) := by
      dsimp [F]
      exact ((ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hDmeas.enorm).add
        (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hD2meas.enorm)).add
          (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hDtmeas.enorm)
    have hFmap : AEMeasurable F (Measure.map e (volume.restrict S)) := by
      rw [hmapS]
      exact hFmeas
    have hchange := lintegral_map' hFmap e.measurable.aemeasurable
    rw [hmapS] at hchange
    rw [← hchange]
    exact hcomponent
  have hEq : (fun z => ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) +
      ‖dtg z‖ₑ ^ (2 : ℝ)) = fun z => F (e z) := by
    funext z
    rw [hg, hdg, hd2g, hdtg, enorm_neg]
  simpa only [hEq] using hsourceL2

private theorem essLocal_backwardUniqueness_affineSecondSlab
    (C : ℝ) (hC : 0 ≤ C)
    (g : ParabolicPoint → Vec3) (dg : ParabolicPoint → Fin 3 → Vec3)
    (d2g : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (dtg : ParabolicPoint → Vec3)
    (hweakG12 : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo (1 : ℝ) 2)
      g dg d2g dtg)
    (hGsumL2_12 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (1 : ℝ) 2) → Bornology.IsBounded S →
      (∫⁻ z in S, ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) +
        ‖dtg z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineqG12 : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (1 : ℝ) 2))),
      vec3EuclideanNorm (fun i => dtg z i + ∑ j, d2g z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq g dg z) + vec3EuclideanNorm (g z)))
    (hcontG2 : ContinuousOn (buAffineField 1 1 g)
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ico (0 : ℝ) 1)))
    (hinitG2 : ∀ y : Vec3, 0 < y 2 → buAffineField 1 1 g (y, 0) = 0)
    (hG2Bound : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1),
      vec3EuclideanNorm (buAffineField 1 1 g z) ≤ C) :
    ∀ y : Vec3, 0 < y 2 → ∀ s ∈ Ioo (0 : ℝ) 1, buAffineField 1 1 g (y, s) = 0 := by
  let H : Set Vec3 := {x | 0 < x 2}
  let g2 : ParabolicPoint → Vec3 := buAffineField 1 1 g
  let dg2 : ParabolicPoint → Fin 3 → Vec3 := buAffineDw 1 1 dg
  let d2g2 : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := buAffineD2w 1 1 d2g
  let dtg2 : ParabolicPoint → Vec3 := buAffineDtw 1 1 dtg
  have hI12 : Ioo (1 : ℝ) 2 ⊆ Ioo (0 : ℝ) 2 := by
    intro s hs
    exact ⟨by linarith only [hs.1], hs.2⟩
  have hweakG2 : HasSpaceTimeWeakDerivs H (Ioo (0 : ℝ) 1) g2 dg2 d2g2 dtg2 := by
    have hweakInput : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
        (Ioo (1 + 1 ^ 2 * 0) (1 + 1 ^ 2 * 1)) g dg d2g dtg := by
      convert hweakG12 using 1; norm_num [H]
    have h := bu_affine_weak_derivatives_interval 1 1 0 1 (by norm_num)
      g dg d2g dtg hweakInput
    convert h using 1
  have hL2G2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet H (Ioo (0 : ℝ) 1) → Bornology.IsBounded S →
      (∫⁻ z in S,
        ‖dg2 z‖ₑ ^ (2 : ℝ) + ‖d2g2 z‖ₑ ^ (2 : ℝ) + ‖dtg2 z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have hweakG12' : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
        (Ioo (1 : ℝ) 2) g dg d2g dtg := by simpa [H] using hweakG12
    have hGsumL2_12' : ∀ S : Set ParabolicPoint,
        S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (1 : ℝ) 2) →
        Bornology.IsBounded S →
        (∫⁻ z in S, ‖dg z‖ₑ ^ (2 : ℝ) +
          ‖d2g z‖ₑ ^ (2 : ℝ) + ‖dtg z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      simpa [H] using hGsumL2_12
    have hweakInput : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
        (Ioo (1 + 1 ^ 2 * 0) (1 + 1 ^ 2 * 1)) g dg d2g dtg := by
      convert hweakG12' using 1; norm_num
    have hL2Input : ∀ S : Set ParabolicPoint,
        S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo (1 + 1 ^ 2 * 0) (1 + 1 ^ 2 * 1)) →
        Bornology.IsBounded S →
        (∫⁻ z in S, ‖dg z‖ₑ ^ (2 : ℝ) +
          ‖d2g z‖ₑ ^ (2 : ℝ) + ‖dtg z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      intro S hS hSb
      apply hGsumL2_12'
      · convert hS using 1; norm_num
      · exact hSb
    have hAffine := bu_affine_derivative_l2_interval 1 1 0 1
      (by norm_num) (by norm_num) g dg d2g dtg hweakInput hL2Input
    intro S hS hSb
    have h := hAffine S hS hSb
    have hpoint (z : ParabolicPoint) :
        ‖dg2 z‖ₑ ^ (2 : ℝ) + ‖d2g2 z‖ₑ ^ (2 : ℝ) + ‖dtg2 z‖ₑ ^ (2 : ℝ) ≤
          ‖(buAffineDw 1 1 dg) z‖ₑ ^ (2 : ℝ) +
            ‖(buAffineD2w 1 1 d2g) z‖ₑ ^ (2 : ℝ) +
              ‖(buAffineDtw 1 1 dtg) z‖ₑ ^ (2 : ℝ) := by
      dsimp [dg2, d2g2, dtg2, buAffineDw, buAffineD2w, buAffineDtw]
      exact le_rfl
    exact (lintegral_mono hpoint).trans_lt h
  have hineqAffine : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet H (Ioo (0 : ℝ) 1))),
      vec3EuclideanNorm (fun i =>
        (buAffineDtw 1 1 dtg) z i + ∑ j, (buAffineD2w 1 1 d2g) z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq
          (buAffineField 1 1 g) (buAffineDw 1 1 dg) z) +
            vec3EuclideanNorm ((buAffineField 1 1 g) z)) := by
    have hineqG12' : ∀ᵐ z ∂(volume.restrict
        (spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo (1 + 1 ^ 2 * 0) (1 + 1 ^ 2 * 1)))),
        vec3EuclideanNorm (fun i => dtg z i + ∑ j, d2g z i j j) ≤
          (C + 1) * (Real.sqrt (spatialGradientSq g dg z) +
            vec3EuclideanNorm (g z)) := by
      convert hineqG12 using 1; norm_num [H]
    have hpull := bu_affine_ae_pullback_interval 1 1 0 1 (by norm_num)
      (fun z => vec3EuclideanNorm (fun i => dtg z i + ∑ j, d2g z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq g dg z) + vec3EuclideanNorm (g z)))
      hineqG12'
    filter_upwards [hpull] with z hz
    have hscaled := bu_affine_weak_heat_bound_scaled 1 1 (C + 1)
      (by norm_num) (by norm_num) (by linarith only [hC])
      g dg d2g dtg z hz
    change vec3EuclideanNorm
      (fun i => buAffineDtw 1 1 dtg z i +
        ∑ j, buAffineD2w 1 1 d2g z i j j) ≤ _ at hscaled
    simpa only [mul_one] using hscaled
  have hG2Ineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet H (Ioo (0 : ℝ) 1))),
      vec3EuclideanNorm (fun i => dtg2 z i + ∑ j, d2g2 z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq g2 dg2 z) + vec3EuclideanNorm (g2 z)) := by
    simpa [g2, dg2, d2g2, dtg2] using hineqAffine
  have hGzeroSecond := essLocal_backwardUniqueness_zero_firstSlab hC g2 dg2 d2g2 dtg2
    hcontG2 hinitG2 hweakG2 hL2G2 hG2Ineq hG2Bound
  exact hGzeroSecond

private theorem essLocal_reflectedHeatInequality
    {Ω H : Set Vec3} {Qsource Qtarget : Set ParabolicPoint}
    (C : ℝ) (hC : 0 ≤ C)
    (ω : ParabolicPoint → Vec3) (Dω : ParabolicPoint → Fin 3 → Vec3)
    (D2ω : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtω : ParabolicPoint → Vec3)
    (e : ParabolicPoint → ParabolicPoint)
    (g : ParabolicPoint → Vec3) (dg : ParabolicPoint → Fin 3 → Vec3)
    (d2g : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (dtg : ParabolicPoint → Vec3)
    (hωineq : ∀ᵐ z ∂(volume.restrict Qsource),
      vec3EuclideanNorm (fun i => Dtω z i - ∑ j, D2ω z i j j) ≤
        C * (vec3EuclideanNorm (ω z) + Real.sqrt (spatialGradientSq ω Dω z)))
    (hQsourceMeas : MeasurableSet Qsource)
    (hmp : MeasurePreserving e (volume : Measure ParabolicPoint) (volume : Measure ParabolicPoint))
    (hpointMap : ∀ z ∈ Qtarget, e z ∈ Qsource)
    (hQtargetHalfMeas : MeasurableSet (spaceTimeSet H (Ioo (0 : ℝ) 2)))
    (hsubset : spaceTimeSet H (Ioo (0 : ℝ) 2) ⊆ Qtarget)
    (hg : ∀ z, g z = ω (e z))
    (hdg : ∀ z i j, dg z i j = Dω (e z) i j)
    (hd2g : ∀ z i j k, d2g z i j k = D2ω (e z) i j k)
    (hdtg : ∀ z i, dtg z i = -Dtω (e z) i) :
    ∀ᵐ z ∂(volume.restrict (spaceTimeSet H (Ioo (0 : ℝ) 2))),
      vec3EuclideanNorm (fun i => dtg z i + ∑ j, d2g z i j j) ≤
        (C + 1) * (vec3EuclideanNorm (g z) +
          Real.sqrt (spatialGradientSq g dg z)) := by
    have hωineqGlobal : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
        z ∈ Qsource →
          vec3EuclideanNorm (fun i => Dtω z i - ∑ j, D2ω z i j j) ≤
            C * (vec3EuclideanNorm (ω z) +
              Real.sqrt (spatialGradientSq ω Dω z)) :=
      (ae_restrict_iff' hQsourceMeas).1 hωineq
    have hpull := hmp.quasiMeasurePreserving.ae hωineqGlobal
    have hsubset : spaceTimeSet H (Ioo (0 : ℝ) 2) ⊆ Qtarget := by
      rintro z ⟨hz, ht⟩
      exact ⟨hHsub hz, ht⟩
    have hrestricted : ∀ᵐ z ∂(volume.restrict
        (spaceTimeSet H (Ioo (0 : ℝ) 2))),
        vec3EuclideanNorm (fun i => Dtω (e z) i -
          ∑ j, D2ω (e z) i j j) ≤
            C * (vec3EuclideanNorm (ω (e z)) +
              Real.sqrt (spatialGradientSq ω Dω (e z))) := by
      apply (ae_restrict_iff' hQtargetHalfMeas).2
      filter_upwards [hpull] with z hz
      intro hzin
      exact hz (hpointMap z (hsubset hzin))
    filter_upwards [hrestricted] with z hz
    have hzineq := hz
    have hbase : vec3EuclideanNorm (fun i => dtg z i + ∑ j, d2g z i j j) ≤
        C * (vec3EuclideanNorm (g z) + Real.sqrt (spatialGradientSq g dg z)) := by
      have hheat : (fun i => dtg z i + ∑ j, d2g z i j j) =
          -(fun i => Dtω (e z) i - ∑ j, D2ω (e z) i j j) := by
        funext i
        simp [hdtg, hd2g]
        ring
      rw [hheat]
      have hnormneg : vec3EuclideanNorm
          (-(fun i => Dtω (e z) i - ∑ j, D2ω (e z) i j j)) =
          vec3EuclideanNorm
            (fun i => Dtω (e z) i - ∑ j, D2ω (e z) i j j) := by
        unfold vec3EuclideanNorm
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.neg_apply, neg_sq]
      rw [hnormneg]
      simpa only [hg, hdg, CKN.spatialGradientSq] using hzineq
    have hsumNonneg : 0 ≤ vec3EuclideanNorm (g z) +
        Real.sqrt (spatialGradientSq g dg z) :=
      add_nonneg (vec3EuclideanNorm_nonneg _) (Real.sqrt_nonneg _)
    exact hbase.trans (mul_le_mul_of_nonneg_right
      (by linarith only [hC]) hsumNonneg)
private theorem essLocal_backwardUniqueness_firstSlabFromTwoUnitData
    {C : ℝ} (hC : 0 ≤ C) (g : ParabolicPoint → Vec3)
    (dg : ParabolicPoint → Fin 3 → Vec3)
    (d2g : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (dtg : ParabolicPoint → Vec3)
    (hcont : ContinuousOn g
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ico (0 : ℝ) 2)))
    (hinit : ∀ y : Vec3, 0 < y 2 → g (y, 0) = 0)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 2)
      g dg d2g dtg)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 2) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) +
        ‖dtg z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 2))),
      vec3EuclideanNorm (fun i => dtg z i + ∑ j, d2g z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq g dg z) + vec3EuclideanNorm (g z)))
    (hbound : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 2),
      vec3EuclideanNorm (g z) ≤ C) :
    ∀ y : Vec3, 0 < y 2 → ∀ s ∈ Ioo (0 : ℝ) 1, g (y, s) = 0 := by
  have hcontFirst : ContinuousOn g
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ico (0 : ℝ) 1)) :=
    hcont.mono (fun _ hz => ⟨hz.1, ⟨hz.2.1, hz.2.2.trans (by norm_num)⟩⟩)
  have hweakFirst : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1)
      g dg d2g dtg := by
    have hI : Ioo (0 : ℝ) 1 ⊆ Ioo (0 : ℝ) 2 := fun _ ht =>
      ⟨ht.1, lt_trans ht.2 (by norm_num)⟩
    have hQmeas : MeasurableSet
        (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 2)) :=
      (isOpen_spaceTimeSet _ _ (isOpen_lt continuous_const
        (continuous_apply (2 : Fin 3))) isOpen_Ioo).measurableSet
    exact essLocal_weakDerivs_restrict (subset_rfl) hI hQmeas hweak
  have hL2First : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) +
        ‖dtg z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    intro S hS hSb
    exact hL2 S (fun z hz => ⟨hz.1, ⟨hz.2.1, lt_trans hz.2.2 (by norm_num)⟩⟩) hSb
  have hineqFirst : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1))),
      vec3EuclideanNorm (fun i => dtg z i + ∑ j, d2g z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq g dg z) + vec3EuclideanNorm (g z)) :=
    ae_restrict_of_ae_restrict_of_subset
      (fun z hz => ⟨hz.1, ⟨hz.2.1, lt_trans hz.2.2 (by norm_num)⟩⟩) hineq
  exact essLocal_backwardUniqueness_zero_firstSlab hC g dg d2g dtg
    hcontFirst hinit hweakFirst hL2First hineqFirst (fun z hz =>
      hbound z ⟨hz.1, ⟨hz.2.1, lt_trans hz.2.2 (by norm_num)⟩⟩)

private theorem essLocal_reflectedCylinderGeometry
    (c : Vec3) (Ω Ω' H : Set Vec3) (e : ParabolicPoint → ParabolicPoint)
    (hΩ'def : Ω' = {y | c + y ∈ Ω})
    (hHsub : H ⊆ Ω')
    (hEcoord : ∀ z : ParabolicPoint, e z = (c + z.1, -z.2)) :
    (∀ z ∈ spaceTimeSet Ω' (Ioo (0 : ℝ) 2),
      e z ∈ spaceTimeSet Ω (Ioo (-2 : ℝ) 0)) ∧
    (∀ S : Set ParabolicPoint, Bornology.IsBounded S →
      Bornology.IsBounded (e '' S)) ∧
    (∀ z ∈ spaceTimeSet H (Ico (0 : ℝ) 2),
      e z ∈ spaceTimeSet Ω (Ioc (-2 : ℝ) 0)) := by
  have hpointMap : ∀ z ∈ spaceTimeSet Ω' (Ioo (0 : ℝ) 2),
      e z ∈ spaceTimeSet Ω (Ioo (-2 : ℝ) 0) := by
    intro z hz
    rcases hz with ⟨hzspace, hztime⟩
    have hspace : c + z.1 ∈ Ω := by simpa [hΩ'def] using hzspace
    have htime : -z.2 ∈ Ioo (-2 : ℝ) 0 := by
      constructor <;> linarith only [hztime.1, hztime.2]
    rw [hEcoord]
    exact ⟨hspace, htime⟩
  have hEbounded : ∀ S : Set ParabolicPoint, Bornology.IsBounded S →
      Bornology.IsBounded (e '' S) := by
    intro S hS
    obtain ⟨B, hBpos, hB⟩ := hS.subset_ball_lt 0
      (show ParabolicPoint from ((0 : Vec3), (0 : ℝ)))
    apply Bornology.IsBounded.subset
      (Metric.isBounded_ball (x := e ((0 : Vec3), (0 : ℝ))) (r := B))
    rintro y ⟨z, hz, rfl⟩
    have hdist : dist (e z) (e ((0 : Vec3), (0 : ℝ))) =
        dist z ((0 : Vec3), (0 : ℝ)) := by
      rw [dist_eq_parabolicDist (e z) (e ((0 : Vec3), (0 : ℝ)))]
      rw [dist_eq_parabolicDist z ((0 : Vec3), (0 : ℝ))]
      rw [hEcoord z, hEcoord ((0 : Vec3), (0 : ℝ))]
      simp [parabolicDist, vec3EuclideanNorm]
    rw [Metric.mem_ball, hdist]
    exact hB hz
  have hspaceTimeMap : ∀ z ∈ spaceTimeSet H (Ico (0 : ℝ) 2),
      e z ∈ spaceTimeSet Ω (Ioc (-2 : ℝ) 0) := by
    intro z hz
    have hspace : c + z.1 ∈ Ω := by simpa [hΩ'def] using hHsub hz.1
    have htime : -z.2 ∈ Ioc (-2 : ℝ) 0 := by
      constructor <;> linarith only [hz.2.1, hz.2.2]
    rw [hEcoord]
    exact ⟨hspace, htime⟩
  exact ⟨hpointMap, hEbounded, hspaceTimeMap⟩

/-- The terminal vorticity extension vanishes on a fixed exterior half-space
throughout its two-unit past slab, by two applications of backward uniqueness. -/
theorem essLocal_exteriorVorticityZero_halfSpace
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C)
    (ω : ParabolicPoint → Vec3)
    (Dω : ParabolicPoint → Fin 3 → Vec3)
    (D2ω : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtω : ParabolicPoint → Vec3)
    (hωCont : ContinuousOn ω
      (spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x}
        (Ioc (-2 : ℝ) 0)))
    (hωtop : ∀ x : Vec3, R < vec3EuclideanNorm x → ω (x, 0) = 0)
    (hωbound : ∀ x : Vec3, R < vec3EuclideanNorm x → ∀ t ∈ Ioc (-2 : ℝ) 0,
      vec3EuclideanNorm (ω (x, t)) ≤ C)
    (hωderiv : HasSpaceTimeWeakDerivs
      {x : Vec3 | R < vec3EuclideanNorm x} (Ioo (-2 : ℝ) 0)
      ω Dω D2ω Dtω)
    (hωL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x}
        (Ioo (-2 : ℝ) 0) → Bornology.IsBounded S →
      (∫⁻ z in S,
        ‖ω z‖ₑ ^ (2 : ℝ) + ‖Dω z‖ₑ ^ (2 : ℝ) +
          ‖D2ω z‖ₑ ^ (2 : ℝ) + ‖Dtω z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hωineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x}
        (Ioo (-2 : ℝ) 0))),
      vec3EuclideanNorm
        (fun i => Dtω z i - ∑ j, D2ω z i j j) ≤
          C * (vec3EuclideanNorm (ω z) +
            Real.sqrt (spatialGradientSq ω Dω z))) :
    ∀ x : Vec3, R < x 2 → ∀ t ∈ Ioo (-2 : ℝ) 0, ω (x, t) = 0 := by
  let Ω : Set Vec3 := {x | R < vec3EuclideanNorm x}
  let H : Set Vec3 := {x | 0 < x 2}
  let c : Vec3 := fun i => if i = 2 then R else 0
  let Ω' : Set Vec3 := {y | c + y ∈ Ω}
  let Qsource : Set ParabolicPoint := spaceTimeSet Ω (Ioo (-2 : ℝ) 0)
  let Qtarget : Set ParabolicPoint := spaceTimeSet Ω' (Ioo (0 : ℝ) 2)
  let e : ParabolicPoint ≃ₜ ParabolicPoint :=
    essLocalTimeReflection.trans (essLocalSpatialTranslate c)
  let g : ParabolicPoint → Vec3 := fun z => ω (e z)
  let dg : ParabolicPoint → Fin 3 → Vec3 := fun z i j => Dω (e z) i j
  let d2g : ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
    fun z i j k => D2ω (e z) i j k
  let dtg : ParabolicPoint → Vec3 := fun z i => -Dtω (e z) i
  have hΩopen : IsOpen Ω := by
    dsimp [Ω]
    exact isOpen_lt continuous_const continuous_vec3EuclideanNorm
  have hΩ'open : IsOpen Ω' := by
    dsimp [Ω']
    exact hΩopen.preimage (continuous_const.add continuous_id)
  have hHopen : IsOpen H :=
    isOpen_lt continuous_const (continuous_apply (2 : Fin 3))
  have hHsub : H ⊆ Ω' := by
    intro y hy
    change R < vec3EuclideanNorm (c + y)
    have hy' : 0 < y 2 := by simpa [H] using hy
    have hcoord : R < (c + y) 2 := by
      rw [show (c + y) 2 = R + y 2 by simp [c]]
      linarith only [hy']
    have hnonneg : 0 ≤ (c + y) 2 := by linarith only [hR, hcoord]
    have hnorm := abs_apply_le_vec3EuclideanNorm (c + y) (2 : Fin 3)
    rw [abs_of_nonneg hnonneg] at hnorm
    exact hcoord.trans_le hnorm
  have htransWeak := essLocal_spatialTranslate_weakDerivs c hΩopen isOpen_Ioo hωderiv
  have hrefWeak := essLocal_timeReflection_weakDerivs hΩ'open htransWeak
  have hQtargetMeas : MeasurableSet Qtarget :=
    (isOpen_spaceTimeSet Ω' (Ioo (0 : ℝ) 2) hΩ'open isOpen_Ioo).measurableSet
  have hweakG : HasSpaceTimeWeakDerivs H (Ioo (0 : ℝ) 2) g dg d2g dtg := by
    have hrestr := essLocal_weakDerivs_restrict hHsub (subset_rfl)
      hQtargetMeas hrefWeak
    simpa [g, dg, d2g, dtg, e, essLocalTimeReflection,
      essLocalSpatialTranslate] using hrestr
  have hmp : MeasurePreserving e
      (volume : Measure ParabolicPoint) (volume : Measure ParabolicPoint) := by
    exact (essLocalSpatialTranslate_measurePreserving c).comp
      essLocalTimeReflection_measurePreserving
  have hEcoord (z : ParabolicPoint) : e z = (c + z.1, -z.2) := by
    change essLocalSpatialTranslate c (essLocalTimeReflection z) =
      (c + z.1, -z.2)
    rw [essLocalTimeReflection_apply]
    simpa only [Prod.fst, Prod.snd] using
      (essLocalSpatialTranslate_apply c (z.1, -z.2))
  have hQsourceMeas : MeasurableSet Qsource :=
    (isOpen_spaceTimeSet Ω (Ioo (-2 : ℝ) 0) hΩopen isOpen_Ioo).measurableSet
  have ⟨hpointMap, hEbounded, hspaceTimeMap⟩ :=
    essLocal_reflectedCylinderGeometry c Ω Ω' H e (by rfl) hHsub hEcoord
  have hGsumL2 := essLocal_reflectedDerivativeL2_finite
    e g dg d2g dtg hmp hpointMap hEbounded hωderiv hωL2
    (fun z => rfl) (fun z i j => rfl) (fun z i j k => rfl) (fun z i => rfl)
  have hΩpre : IsOpen Ω' := hΩ'open
  have heContinuous : Continuous e :=
    (essLocalSpatialTranslate c).continuous.comp essLocalTimeReflection.continuous
  have hGcont : ContinuousOn g (spaceTimeSet H (Ico (0 : ℝ) 2)) := by
    change ContinuousOn (fun z => ω (e z)) _
    exact hωCont.comp heContinuous.continuousOn hspaceTimeMap
  have hQtargetHalfMeas : MeasurableSet
      (spaceTimeSet H (Ioo (0 : ℝ) 2)) :=
    (isOpen_spaceTimeSet H (Ioo (0 : ℝ) 2) hHopen isOpen_Ioo).measurableSet
  have hGineq := essLocal_reflectedHeatInequality C hC ω Dω D2ω Dtω e g dg d2g dtg
    hωineq hQsourceMeas hmp hpointMap hQtargetHalfMeas hsubset
    (fun z => rfl) (fun z i j => rfl) (fun z i j k => rfl) (fun z i => rfl)
  let a : ℝ := (C + 1)⁻¹
  have hApos : 0 < C + 1 := by linarith only [hC]
  have ha : 0 < a := by dsimp [a]; exact inv_pos.mpr hApos
  have ha_le : a ≤ 1 := by
    dsimp [a]
    rw [inv_le_one₀ hApos]
    linarith only [hC]
  have haC : a * C ≤ 1 := by
    calc
      a * C = C / (C + 1) := by simp [a, div_eq_mul_inv, mul_comm]
      _ ≤ 1 := (div_le_iff₀ hApos).2 (by linarith only [hC])
  have hGfirstInit : ∀ y : Vec3, 0 < y 2 → g (y, 0) = 0 := by
    intro y hy
    have hxy : R < vec3EuclideanNorm (c + y) := hHsub (by simpa [H] using hy)
    change ω (e (y, 0)) = 0
    rw [hEcoord (y, 0)]
    exact hωtop (c + y) hxy
  have hGfirstBound : ∀ z ∈ spaceTimeSet H (Ioo (0 : ℝ) 2),
      vec3EuclideanNorm (g z) ≤ C := by
    intro z hz
    have htime : -z.2 ∈ Ioc (-2 : ℝ) 0 := by
      constructor <;> linarith only [hz.2.1, hz.2.2]
    have hbound := hωbound (c + z.1) (hHsub hz.1) (-z.2) htime
    change vec3EuclideanNorm (ω (e z)) ≤ C
    rw [hEcoord z]
    exact hbound
  have hfirstg := essLocal_backwardUniqueness_firstSlabFromTwoUnitData hC g dg d2g dtg
    hGcont hGfirstInit hweakG hGsumL2 hGineq hGfirstBound
  have hlineCont (y : Vec3) (hy : 0 < y 2) :
      ContinuousOn (fun s : ℝ => g (y, s)) (Ico (0 : ℝ) 2) := by
    have hline : Continuous (show ℝ → ParabolicPoint from fun s => (y, s)) :=
      continuous_prod_to_parabolicPoint.comp
        (continuous_const.prodMk continuous_id)
    have hmaps : ∀ s ∈ Ico (0 : ℝ) 2,
        (y, s) ∈ spaceTimeSet H (Ico (0 : ℝ) 2) := fun s hs => ⟨hy, hs⟩
    exact hGcont.comp hline.continuousOn hmaps
  have hzeroAtOne : ∀ y : Vec3, 0 < y 2 → g (y, 1) = 0 := by
    intro y hy
    exact essLocal_continuousZero_at_one (fun s => g (y, s))
      (hlineCont y hy) (hfirstg y hy)
  let g2 : ParabolicPoint → Vec3 := buAffineField 1 1 g
  let dg2 : ParabolicPoint → Fin 3 → Vec3 := buAffineDw 1 1 dg
  let d2g2 : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := buAffineD2w 1 1 d2g
  let dtg2 : ParabolicPoint → Vec3 := buAffineDtw 1 1 dtg
  have hI12 : Ioo (1 : ℝ) 2 ⊆ Ioo (0 : ℝ) 2 := by
    intro s hs
    exact ⟨by linarith only [hs.1], hs.2⟩
  have hweakG12 : HasSpaceTimeWeakDerivs H (Ioo (1 : ℝ) 2) g dg d2g dtg := by
    have hQmeas : MeasurableSet (spaceTimeSet H (Ioo (0 : ℝ) 2)) :=
      (isOpen_spaceTimeSet H (Ioo (0 : ℝ) 2) hHopen isOpen_Ioo).measurableSet
    exact essLocal_weakDerivs_restrict (subset_rfl) hI12 hQmeas hweakG
  have hGsumL2_12 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet H (Ioo (1 : ℝ) 2) → Bornology.IsBounded S →
      (∫⁻ z in S,
        ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) + ‖dtg z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    intro S hS hSb
    apply hGsumL2 S ?_ hSb
    intro z hz
    exact ⟨hHsub (hS hz).1, hI12 (hS hz).2⟩
  have hcontG2 : ContinuousOn g2 (spaceTimeSet H (Ico (0 : ℝ) 1)) := by
    change ContinuousOn (g ∘ buAffinePoint 1 1) _
    apply hGcont.comp (buAffinePoint_continuous 1 1).continuousOn
    intro z hz
    change z.1 ∈ H ∧ z.2 ∈ Ico (0 : ℝ) 1 at hz
    rcases hz with ⟨hzH, hzt⟩
    refine ⟨?_, ?_⟩
    · simpa [buAffinePoint, H] using hzH
    · have htime : 1 + z.2 ∈ Ico (0 : ℝ) 2 :=
        ⟨by linarith only [hzt.1], by linarith only [hzt.2]⟩
      simpa [buAffinePoint] using htime
  have hinitG2 : ∀ y : Vec3, 0 < y 2 → g2 (y, 0) = 0 := by
    intro y hy
    change g (buAffinePoint 1 1 (y, 0)) = 0
    simpa [buAffinePoint] using hzeroAtOne y hy
  have hQ12 : spaceTimeSet H (Ioo (1 : ℝ) 2) ⊆
      spaceTimeSet H (Ioo (0 : ℝ) 2) := by
    intro z hz
    exact ⟨hz.1, hI12 hz.2⟩
  have hineqG12 : ∀ᵐ z ∂(volume.restrict (spaceTimeSet H (Ioo (1 : ℝ) 2))),
      vec3EuclideanNorm (fun i => dtg z i + ∑ j, d2g z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq g dg z) + vec3EuclideanNorm (g z)) :=
    by
      have h := ae_restrict_of_ae_restrict_of_subset hQ12 hGineq
      simpa only [add_comm] using h
  have hG2Bound : ∀ z ∈ spaceTimeSet H (Ioo (0 : ℝ) 1),
      vec3EuclideanNorm (g2 z) ≤ C := by
    intro z hz
    have htime : -(1 + z.2) ∈ Ioc (-2 : ℝ) 0 := by
      constructor <;> dsimp at hz ⊢ <;> linarith only [hz.2.1, hz.2.2]
    have hbound := hωbound (c + z.1) (hHsub hz.1) (-(1 + z.2)) htime
    simpa [g2, buAffineField, buAffinePoint, g, hEcoord] using hbound
  have hGzeroSecond := essLocal_backwardUniqueness_affineSecondSlab C hC
    g dg d2g dtg hweakG12 hGsumL2_12 hineqG12 hcontG2 hinitG2 hG2Bound
  have hGzero : ∀ y : Vec3, 0 < y 2 → ∀ s ∈ Ioo (0 : ℝ) 2, g (y, s) = 0 := by
    intro y hy s hs
    by_cases hlt : s < 1
    · exact hfirstg y hy s ⟨hs.1, hlt⟩
    · by_cases heq : s = 1
      · simpa [heq] using hzeroAtOne y hy
      · have hgt : 1 < s := by
          rcases lt_trichotomy 1 s with h | h | h
          · exact h
          · exact False.elim (heq h.symm)
          · exact False.elim (hlt h)
        have hu : s - 1 ∈ Ioo (0 : ℝ) 1 := by
          constructor <;> linarith only [hgt, hs.2]
        have hz := hGzeroSecond y hy (s - 1) hu
        simpa [g2, buAffineField, buAffinePoint] using hz
  intro x hx t ht
  let y : Vec3 := x - c
  have hy : 0 < y 2 := by
    dsimp [y, c]
    simpa using hx
  have hs : -t ∈ Ioo (0 : ℝ) 2 := by
    constructor <;> linarith only [ht.1, ht.2]
  have hzero := hGzero y hy (-t) hs
  have heq : e (y, -t) = (x, t) := by
    rw [hEcoord (y, -t)]
    simp [y, c]
    rfl
  simpa [g, heq] using hzero

end ESS
