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
  have hpointMap : ∀ z ∈ Qtarget, e z ∈ Qsource := by
    intro z hz
    change z ∈ spaceTimeSet Ω' (Ioo (0 : ℝ) 2) at hz
    rcases hz with ⟨hzspace, hztime⟩
    have hspace : R < vec3EuclideanNorm (c + z.1) := by
      change c + z.1 ∈ Ω at hzspace
      exact hzspace
    have htime : -z.2 ∈ Ioo (-2 : ℝ) 0 := by
      constructor <;> linarith only [hztime.1, hztime.2]
    change e z ∈ spaceTimeSet Ω (Ioo (-2 : ℝ) 0)
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
  let F : ParabolicPoint → ℝ≥0∞ := fun z =>
    ‖Dω z‖ₑ ^ (2 : ℝ) + ‖D2ω z‖ₑ ^ (2 : ℝ) + ‖Dtω z‖ₑ ^ (2 : ℝ)
  have hsourceL2 : ∀ S : Set ParabolicPoint,
      S ⊆ Qtarget → Bornology.IsBounded S →
      (∫⁻ z in S, F (e z)) < ⊤ := by
    intro S hS hSb
    let T := e '' S
    have hTsub : T ⊆ Qsource := by
      rintro z ⟨y, hy, rfl⟩
      exact hpointMap y (hS hy)
    have hTbounded : Bornology.IsBounded T := hEbounded S hSb
    have htop := hωL2 T hTsub hTbounded
    have hcomponent : (∫⁻ z in T, F z) < ⊤ := by
      refine (lintegral_mono fun z => ?_).trans_lt htop
      dsimp [F]
      have hωnonneg : (0 : ℝ≥0∞) ≤ ‖ω z‖ₑ ^ (2 : ℝ) := by positivity
      have hsum :
          (‖Dω z‖ₑ ^ (2 : ℝ) + ‖D2ω z‖ₑ ^ (2 : ℝ) +
            ‖Dtω z‖ₑ ^ (2 : ℝ)) ≤
          ‖ω z‖ₑ ^ (2 : ℝ) +
            (‖Dω z‖ₑ ^ (2 : ℝ) + ‖D2ω z‖ₑ ^ (2 : ℝ) +
              ‖Dtω z‖ₑ ^ (2 : ℝ)) := le_add_of_nonneg_left hωnonneg
      simpa only [add_assoc] using hsum
    have hmapS : Measure.map e (volume.restrict S) =
        volume.restrict T := (hmp.restrict_image_emb e.measurableEmbedding S).map_eq
    have hDmeas : AEStronglyMeasurable Dω (volume.restrict T) :=
      (hωderiv.2.1.mono_set hTsub).aestronglyMeasurable
    have hD2meas : AEStronglyMeasurable D2ω (volume.restrict T) :=
      (hωderiv.2.2.1.mono_set hTsub).aestronglyMeasurable
    have hDtmeas : AEStronglyMeasurable Dtω (volume.restrict T) :=
      (hωderiv.2.2.2.1.mono_set hTsub).aestronglyMeasurable
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
  have hGsumL2 : ∀ S : Set ParabolicPoint,
      S ⊆ Qtarget → Bornology.IsBounded S →
      (∫⁻ z in S,
        ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) + ‖dtg z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    intro S hS hSb
    have hbase := hsourceL2 S hS hSb
    have hEq : (fun z =>
        ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) + ‖dtg z‖ₑ ^ (2 : ℝ)) =
        fun z => F (e z) := by
      funext z
      change ‖Dω (e z)‖ₑ ^ (2 : ℝ) + ‖D2ω (e z)‖ₑ ^ (2 : ℝ) +
          ‖-Dtω (e z)‖ₑ ^ (2 : ℝ) =
        ‖Dω (e z)‖ₑ ^ (2 : ℝ) + ‖D2ω (e z)‖ₑ ^ (2 : ℝ) +
          ‖Dtω (e z)‖ₑ ^ (2 : ℝ)
      rw [enorm_neg]
    simpa only [hEq] using hbase
  have hΩpre : IsOpen Ω' := hΩ'open
  have hspaceTimeMap : ∀ z ∈ spaceTimeSet H (Ico (0 : ℝ) 2),
      e z ∈ spaceTimeSet Ω (Ioc (-2 : ℝ) 0) := by
    intro z hz
    have hspace : R < vec3EuclideanNorm (c + z.1) := hHsub hz.1
    have htime : -z.2 ∈ Ioc (-2 : ℝ) 0 := by
      constructor <;> linarith only [hz.2.1, hz.2.2]
    rw [hEcoord]
    exact ⟨hspace, htime⟩
  have heContinuous : Continuous e :=
    (essLocalSpatialTranslate c).continuous.comp essLocalTimeReflection.continuous
  have hGcont : ContinuousOn g (spaceTimeSet H (Ico (0 : ℝ) 2)) := by
    change ContinuousOn (fun z => ω (e z)) _
    exact hωCont.comp heContinuous.continuousOn hspaceTimeMap
  have hGineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet H (Ioo (0 : ℝ) 2))),
      vec3EuclideanNorm (fun i => dtg z i + ∑ j, d2g z i j j) ≤
        (C + 1) * (vec3EuclideanNorm (g z) + Real.sqrt (spatialGradientSq g dg z)) := by
    have hQsourceMeas : MeasurableSet Qsource :=
      (isOpen_spaceTimeSet Ω (Ioo (-2 : ℝ) 0) hΩopen isOpen_Ioo).measurableSet
    have hωineqGlobal : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
        z ∈ Qsource →
          vec3EuclideanNorm (fun i => Dtω z i - ∑ j, D2ω z i j j) ≤
            C * (vec3EuclideanNorm (ω z) +
              Real.sqrt (spatialGradientSq ω Dω z)) :=
      (ae_restrict_iff' hQsourceMeas).1 hωineq
    have hpull := hmp.quasiMeasurePreserving.ae hωineqGlobal
    have hQtargetHalfMeas : MeasurableSet
        (spaceTimeSet H (Ioo (0 : ℝ) 2)) :=
      (isOpen_spaceTimeSet H (Ioo (0 : ℝ) 2) hHopen isOpen_Ioo).measurableSet
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
        simp [dtg, d2g]
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
      simpa only [g, dg, CKN.spatialGradientSq] using hzineq
    have hsumNonneg : 0 ≤ vec3EuclideanNorm (g z) +
        Real.sqrt (spatialGradientSq g dg z) :=
      add_nonneg (vec3EuclideanNorm_nonneg _) (Real.sqrt_nonneg _)
    exact hbase.trans (mul_le_mul_of_nonneg_right
      (by linarith only [hC]) hsumNonneg)
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
  let w : ParabolicPoint → Vec3 := fun z => a • g z
  let Dw : ParabolicPoint → Fin 3 → Vec3 := fun z i j => a * dg z i j
  let D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
    fun z i j k => a * d2g z i j k
  let Dtw : ParabolicPoint → Vec3 := fun z i => a * dtg z i
  have hweakW : HasSpaceTimeWeakDerivs H (Ioo (0 : ℝ) 2) w Dw D2w Dtw := by
    simpa only [w, Dw, D2w, Dtw] using essLocal_scale_weakDerivs a hweakG
  have hcontW : ContinuousOn w (spaceTimeSet H (Ico (0 : ℝ) 2)) := by
    change ContinuousOn (fun z => a • g z) _
    change ContinuousOn ((fun _ : ParabolicPoint => a) • g) _
    exact continuousOn_const.smul hGcont
  have hinitW : ∀ y : Vec3, 0 < y 2 → w (y, 0) = 0 := by
    intro y hy
    have hxy : R < vec3EuclideanNorm (c + y) :=
      hHsub (by simpa [H] using hy)
    have hzero := hωtop (c + y) hxy
    change a • ω (e (y, 0)) = 0
    rw [hEcoord (y, 0)]
    simpa [w, g] using congrArg (fun v : Vec3 => a • v) hzero
  have hboundW : ∀ z ∈ spaceTimeSet H (Ioo (0 : ℝ) 2),
      vec3EuclideanNorm (w z) ≤ Real.exp (0 * vec3EuclideanNorm z.1 ^ 2) := by
    intro z hz
    have hxy : R < vec3EuclideanNorm (c + z.1) := hHsub hz.1
    have ht : -z.2 ∈ Ioc (-2 : ℝ) 0 := by
      constructor <;> linarith only [hz.2.1, hz.2.2]
    have hbound := hωbound (c + z.1) hxy (-z.2) ht
    have hnorm : vec3EuclideanNorm (w z) = a * vec3EuclideanNorm (g z) := by
      simp [w, vec3EuclideanNorm_smul, abs_of_pos ha]
    rw [hnorm]
    have hle : a * vec3EuclideanNorm (g z) ≤ a * C :=
      mul_le_mul_of_nonneg_left (by simpa [g, e, hEcoord] using hbound) ha.le
    calc
      a * vec3EuclideanNorm (g z) ≤ a * C := hle
      _ ≤ 1 := haC
      _ = Real.exp (0 * vec3EuclideanNorm z.1 ^ 2) := by simp
  have hineqW : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet H (Ioo (0 : ℝ) 2))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq w Dw z) +
          vec3EuclideanNorm (w z)) := by
    filter_upwards [hGineq] with z hz
    have hheat : (fun i => Dtw z i + ∑ j, D2w z i j j) =
        a • (fun i => dtg z i + ∑ j, d2g z i j j) := by
      funext i
      simp [Dtw, D2w, Finset.mul_sum, mul_add]
    have hnorm : vec3EuclideanNorm (w z) = a * vec3EuclideanNorm (g z) := by
      simp [w, vec3EuclideanNorm_smul, abs_of_pos ha]
    have hgrad : spatialGradientSq w Dw z = a ^ 2 * spatialGradientSq g dg z := by
      simp [spatialGradientSq, Dw, dg, mul_pow, ← Finset.mul_sum]
    have hsqrt : Real.sqrt (spatialGradientSq w Dw z) =
        a * Real.sqrt (spatialGradientSq g dg z) := by
      rw [hgrad, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
        abs_of_pos ha]
    rw [hheat, vec3EuclideanNorm_smul, abs_of_pos ha, hnorm, hsqrt]
    have h' := mul_le_mul_of_nonneg_left hz ha.le
    convert h' using 1; ring
  have hQfirst : spaceTimeSet H (Ioo (0 : ℝ) 1) ⊆
      spaceTimeSet H (Ioo (0 : ℝ) 2) := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1, lt_trans hz.2.2 (by norm_num)⟩⟩
  have hL2Wfirst : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet H (Ioo (0 : ℝ) 1) → Bornology.IsBounded S →
      (∫⁻ z in S,
        ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    intro S hS hSb
    have hhalf : spaceTimeSet H (Ioo (0 : ℝ) 2) ⊆ Qtarget := by
      intro z hz
      exact ⟨hHsub hz.1, hz.2⟩
    have hSsubQ : S ⊆ Qtarget := by
      intro z hz
      exact hhalf (hQfirst (hS hz))
    have hbase := hGsumL2 S hSsubQ hSb
    have hpoint (z : ParabolicPoint) :
        ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ) ≤
          ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) + ‖dtg z‖ₑ ^ (2 : ℝ) := by
      dsimp [Dw, D2w, Dtw]
      exact add_le_add (add_le_add (by
        change ‖a • dg z‖ₑ ^ (2 : ℝ) ≤ ‖dg z‖ₑ ^ (2 : ℝ)
        exact essLocal_enorm_smul_sq_le a ha.le ha_le (dg z)) (by
        change ‖a • d2g z‖ₑ ^ (2 : ℝ) ≤ ‖d2g z‖ₑ ^ (2 : ℝ)
        exact essLocal_enorm_smul_sq_le a ha.le ha_le (d2g z))) (by
        change ‖a • dtg z‖ₑ ^ (2 : ℝ) ≤ ‖dtg z‖ₑ ^ (2 : ℝ)
        exact essLocal_enorm_smul_sq_le a ha.le ha_le (dtg z))
    exact (lintegral_mono hpoint).trans_lt hbase
  have hcontWfirst : ContinuousOn w
      (spaceTimeSet H (Ico (0 : ℝ) 1)) :=
    hcontW.mono (fun _ hz => ⟨hz.1, ⟨hz.2.1, hz.2.2.trans (by norm_num)⟩⟩)
  have hweakWfirst : HasSpaceTimeWeakDerivs H (Ioo (0 : ℝ) 1) w Dw D2w Dtw := by
    have hI : Ioo (0 : ℝ) 1 ⊆ Ioo (0 : ℝ) 2 := fun _ ht =>
      ⟨ht.1, lt_trans ht.2 (by norm_num)⟩
    have hQmeas : MeasurableSet
        (spaceTimeSet H (Ioo (0 : ℝ) 2)) :=
      (isOpen_spaceTimeSet H (Ioo (0 : ℝ) 2) hHopen isOpen_Ioo).measurableSet
    exact essLocal_weakDerivs_restrict (subset_rfl) hI hQmeas hweakW
  have hineqWfirst : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet H (Ioo (0 : ℝ) 1))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq w Dw z) +
          vec3EuclideanNorm (w z)) :=
    ae_restrict_of_ae_restrict_of_subset hQfirst hineqW
  have hboundWfirst : ∀ z ∈ spaceTimeSet H (Ioo (0 : ℝ) 1),
      vec3EuclideanNorm (w z) ≤ Real.exp (0 * vec3EuclideanNorm z.1 ^ 2) :=
    fun z hz => hboundW z (hQfirst hz)
  have hinitWfirst : ∀ y : Vec3, 0 < y 2 → w (y, 0) = 0 := hinitW
  have hBUfirst := backwardUniqueness_real_growth (C + 1) 0
    (by linarith only [hC]) w Dw D2w Dtw hcontWfirst hinitWfirst
    hweakWfirst hL2Wfirst hineqWfirst hboundWfirst
  have hfirstg : ∀ y : Vec3, 0 < y 2 → ∀ s ∈ Ioo (0 : ℝ) 1, g (y, s) = 0 := by
    intro y hy s hs
    have hz := hBUfirst (y, s) ⟨hy, hs⟩
    have hzero : a • g (y, s) = 0 := by simpa [w] using hz
    rcases smul_eq_zero.mp hzero with ha0 | hg0
    · exact False.elim (ne_of_gt ha ha0)
    · exact hg0
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
    let s : ℕ → ℝ := fun n => 1 - (1 / 2 : ℝ) ^ n
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hs : Tendsto s atTop (𝓝 1) := by
      simpa [s] using tendsto_const_nhds.sub hp
    have hseq : Tendsto (fun n : ℕ => g (y, s n)) atTop (𝓝 (g (y, 1))) := by
      have hcont := (hlineCont y hy).continuousAt (by
        have hmem : (1 : ℝ) ∈ interior (Ico (0 : ℝ) 2) := by
          rw [interior_Ico]
          norm_num
        exact mem_interior_iff_mem_nhds.mp hmem)
      exact hcont.tendsto.comp hs
    have hseqZero : ∀ᶠ n : ℕ in atTop, g (y, s n) = 0 := by
      have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n :=
        eventually_atTop.2 ⟨1, fun _ hn => hn⟩
      filter_upwards [hev] with n hn
      exact hfirstg y hy (s n) (by
        dsimp [s]
        have hp0 : 0 < (1 / 2 : ℝ) ^ n := by positivity
        have hp1 : (1 / 2 : ℝ) ^ n < 1 := by
          exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
        exact ⟨by linarith only [hp1], by linarith only [hp0]⟩)
    have hseqZeroEq : (fun n : ℕ => (0 : Vec3)) =ᶠ[atTop]
        (fun n : ℕ => g (y, s n)) := by
      filter_upwards [hseqZero] with n hn
      exact hn.symm
    have hseqZero' : Tendsto (fun n : ℕ => g (y, s n)) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' hseqZeroEq
    exact tendsto_nhds_unique hseq hseqZero'
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
  have hweakG2 : HasSpaceTimeWeakDerivs H (Ioo (0 : ℝ) 1) g2 dg2 d2g2 dtg2 := by
    have hweakInput : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
        (Ioo (1 + 1 ^ 2 * 0) (1 + 1 ^ 2 * 1)) g dg d2g dtg := by
      convert hweakG12 using 1; norm_num [H]
    have h := bu_affine_weak_derivatives_interval 1 1 0 1 (by norm_num)
      g dg d2g dtg hweakInput
    convert h using 1
  have hGsumL2_12 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet H (Ioo (1 : ℝ) 2) → Bornology.IsBounded S →
      (∫⁻ z in S,
        ‖dg z‖ₑ ^ (2 : ℝ) + ‖d2g z‖ₑ ^ (2 : ℝ) + ‖dtg z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    intro S hS hSb
    apply hGsumL2 S ?_ hSb
    intro z hz
    exact ⟨hHsub (hS hz).1, hI12 (hS hz).2⟩
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
  let w2 : ParabolicPoint → Vec3 := fun z => a • g2 z
  let Dw2 : ParabolicPoint → Fin 3 → Vec3 := fun z i j => a * dg2 z i j
  let D2w2 : ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
    fun z i j k => a * d2g2 z i j k
  let Dtw2 : ParabolicPoint → Vec3 := fun z i => a * dtg2 z i
  have hweakW2 : HasSpaceTimeWeakDerivs H (Ioo (0 : ℝ) 1) w2 Dw2 D2w2 Dtw2 := by
    simpa only [w2, Dw2, D2w2, Dtw2] using essLocal_scale_weakDerivs a hweakG2
  have hcontW2 : ContinuousOn w2 (spaceTimeSet H (Ico (0 : ℝ) 1)) := by
    change ContinuousOn (fun z => a • g2 z) _
    change ContinuousOn ((fun _ : ParabolicPoint => a) • g2) _
    exact continuousOn_const.smul hcontG2
  have hinitW2 : ∀ y : Vec3, 0 < y 2 → w2 (y, 0) = 0 := by
    intro y hy
    simp [w2, hinitG2 y hy]
  have hboundW2 : ∀ z ∈ spaceTimeSet H (Ioo (0 : ℝ) 1),
      vec3EuclideanNorm (w2 z) ≤ Real.exp (0 * vec3EuclideanNorm z.1 ^ 2) := by
    intro z hz
    have hsource : buAffinePoint 1 1 z ∈ spaceTimeSet H (Ioo (0 : ℝ) 2) := by
      have htime : 1 + z.2 ∈ Ioo (0 : ℝ) 2 := by
        constructor <;> linarith only [hz.2.1, hz.2.2]
      exact ⟨by simpa [buAffinePoint] using hz.1, by simpa [buAffinePoint] using htime⟩
    have hbase := hboundW (buAffinePoint 1 1 z) hsource
    simpa [w2, g2, buAffineField, buAffinePoint] using hbase
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
  have hineqW2 : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet H (Ioo (0 : ℝ) 1))),
      vec3EuclideanNorm (fun i => Dtw2 z i + ∑ j, D2w2 z i j j) ≤
        (C + 1) * (Real.sqrt (spatialGradientSq w2 Dw2 z) +
          vec3EuclideanNorm (w2 z)) := by
    filter_upwards [hineqAffine] with z hz
    have hheat : (fun i => Dtw2 z i + ∑ j, D2w2 z i j j) =
        a • (fun i => (buAffineDtw 1 1 dtg) z i +
          ∑ j, (buAffineD2w 1 1 d2g) z i j j) := by
      funext i
      simp [Dtw2, D2w2, dtg2, d2g2, buAffineDtw, buAffineD2w,
        Finset.mul_sum, mul_add]
    have hnorm : vec3EuclideanNorm (w2 z) =
        a * vec3EuclideanNorm ((buAffineField 1 1 g) z) := by
      simp [w2, g2, vec3EuclideanNorm_smul, abs_of_pos ha]
    have hgrad : spatialGradientSq w2 Dw2 z = a ^ 2 * spatialGradientSq
        (buAffineField 1 1 g) (buAffineDw 1 1 dg) z := by
      calc
        spatialGradientSq w2 Dw2 z = a ^ 2 * spatialGradientSq g2 dg2 z := by
          simp only [spatialGradientSq, Dw2]
          simp_rw [mul_pow]
          simp_rw [← Finset.mul_sum]
        _ = a ^ 2 * spatialGradientSq
            (buAffineField 1 1 g) (buAffineDw 1 1 dg) z := by rfl
    have hsqrt : Real.sqrt (spatialGradientSq w2 Dw2 z) =
        a * Real.sqrt (spatialGradientSq
          (buAffineField 1 1 g) (buAffineDw 1 1 dg) z) := by
      rw [hgrad, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
        abs_of_pos ha]
    rw [hheat, vec3EuclideanNorm_smul, abs_of_pos ha, hnorm, hsqrt]
    have h' := mul_le_mul_of_nonneg_left hz ha.le
    convert h' using 1; ring
  have hQsecond : spaceTimeSet H (Ioo (0 : ℝ) 1) ⊆
      spaceTimeSet H (Ioo (0 : ℝ) 2) := hQfirst
  have hL2Wsecond : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet H (Ioo (0 : ℝ) 1) → Bornology.IsBounded S →
      (∫⁻ z in S,
        ‖Dw2 z‖ₑ ^ (2 : ℝ) + ‖D2w2 z‖ₑ ^ (2 : ℝ) + ‖Dtw2 z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have hweakInput : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
        (Ioo (1 + 1 ^ 2 * 0) (1 + 1 ^ 2 * 1)) g dg d2g dtg := by
      convert hweakG12 using 1; norm_num [H]
    have hL2Input : ∀ S : Set ParabolicPoint,
        S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo (1 + 1 ^ 2 * 0) (1 + 1 ^ 2 * 1)) →
        Bornology.IsBounded S →
        (∫⁻ z in S, ‖dg z‖ₑ ^ (2 : ℝ) +
          ‖d2g z‖ₑ ^ (2 : ℝ) + ‖dtg z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      intro S hS hSb
      apply hGsumL2_12
      · convert hS using 1; norm_num [H]
      · exact hSb
    have hAffine := bu_affine_derivative_l2_interval 1 1 0 1
      (by norm_num) (by norm_num) g dg d2g dtg hweakInput hL2Input
    intro S hS hSb
    have h := hAffine S hS hSb
    have hpoint (z : ParabolicPoint) :
        ‖Dw2 z‖ₑ ^ (2 : ℝ) + ‖D2w2 z‖ₑ ^ (2 : ℝ) + ‖Dtw2 z‖ₑ ^ (2 : ℝ) ≤
          ‖(buAffineDw 1 1 dg) z‖ₑ ^ (2 : ℝ) +
            ‖(buAffineD2w 1 1 d2g) z‖ₑ ^ (2 : ℝ) +
              ‖(buAffineDtw 1 1 dtg) z‖ₑ ^ (2 : ℝ) := by
      dsimp [Dw2, D2w2, Dtw2]
      exact add_le_add (add_le_add (by
        change ‖a • (buAffineDw 1 1 dg) z‖ₑ ^ (2 : ℝ) ≤
          ‖(buAffineDw 1 1 dg) z‖ₑ ^ (2 : ℝ)
        exact essLocal_enorm_smul_sq_le a ha.le ha_le
          ((buAffineDw 1 1 dg) z)) (by
        change ‖a • (buAffineD2w 1 1 d2g) z‖ₑ ^ (2 : ℝ) ≤
          ‖(buAffineD2w 1 1 d2g) z‖ₑ ^ (2 : ℝ)
        exact essLocal_enorm_smul_sq_le a ha.le ha_le
          ((buAffineD2w 1 1 d2g) z))) (by
        change ‖a • (buAffineDtw 1 1 dtg) z‖ₑ ^ (2 : ℝ) ≤
          ‖(buAffineDtw 1 1 dtg) z‖ₑ ^ (2 : ℝ)
        exact essLocal_enorm_smul_sq_le a ha.le ha_le
          ((buAffineDtw 1 1 dtg) z))
    exact (lintegral_mono hpoint).trans_lt h
  have hinitW2' : ∀ y : Vec3, 0 < y 2 → w2 (y, 0) = 0 := hinitW2
  have hBUsecond := backwardUniqueness_real_growth (C + 1) 0
    (by linarith only [hC]) w2 Dw2 D2w2 Dtw2 hcontW2 hinitW2'
    hweakW2 hL2Wsecond hineqW2 hboundW2
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
        have hz := hBUsecond (y, s - 1) ⟨hy, hu⟩
        have hzero : a • g2 (y, s - 1) = 0 := by simpa [w2] using hz
        have hg2 : g2 (y, s - 1) = 0 := by
          rcases smul_eq_zero.mp hzero with ha0 | hg0
          · exact False.elim (ne_of_gt ha ha0)
          · exact hg0
        simpa [g2, buAffineField, buAffinePoint] using hg2
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
