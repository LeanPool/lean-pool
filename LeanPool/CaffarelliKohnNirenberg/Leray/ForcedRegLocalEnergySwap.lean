/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyAC

/-!
# The space-time energy identity of the mollified velocity

Integrating the time energy identity of the mollified forced regularized
velocity over all spatial points and exchanging the order of integration gives
`∫∫ w² ∂ₜψ = 2 ∫∫ w S ψ` on a bounded slab, for every smooth compactly
supported space-time test `ψ`. The exchanges are justified by joint
measurability and the uniform bounds of the mollified velocity and of its
source. This is the time part of `eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- A property holding for almost every time and every point holds almost
everywhere on the product. -/
theorem ae_prod_of_ae_forall {P : Vec3 × ℝ → Prop} {ν : Measure ℝ} [SFinite ν]
    (h : ∀ᵐ t ∂ν, ∀ x, P (x, t)) : ∀ᵐ z ∂((volume : Measure Vec3).prod ν), P z := by
  rw [ae_iff] at h ⊢
  obtain ⟨N, hsub, hNm, hN⟩ := exists_measurable_superset_of_null h
  refine measure_mono_null (t := (univ : Set Vec3) ×ˢ N) (fun z hz => ?_) ?_
  · refine ⟨mem_univ _, hsub ?_⟩
    intro hall
    exact hz (hall z.1)
  · rw [Measure.prod_prod, hN, mul_zero]

section Swap

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

theorem stronglyMeasurable_leW {η : Vec3 → ℝ} (hη : Continuous η) (k : Fin 3) :
    StronglyMeasurable fun p : Vec3 × ℝ => leW ρ ε hε ha hf η p.1 p.2 k := by
  have hm : StronglyMeasurable fun q : (Vec3 × ℝ) × Vec3 =>
      η (q.1.1 - q.2) * forcedRegRep ρ ε hε ha hf (q.2, q.1.2) k := by
    have h1 : Measurable fun q : (Vec3 × ℝ) × Vec3 => η (q.1.1 - q.2) :=
      hη.measurable.comp ((measurable_fst.comp measurable_fst).sub measurable_snd)
    have h2 : Measurable fun q : (Vec3 × ℝ) × Vec3 => forcedRegRep ρ ε hε ha hf (q.2, q.1.2) k :=
      (measurable_pi_apply k).comp ((forcedRegRep_stronglyMeasurable ρ ε hε ha hf).measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    exact (h1.mul h2).stronglyMeasurable
  exact hm.integral_prod_right'

theorem stronglyMeasurable_leSF {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (k : Fin 3) :
    StronglyMeasurable fun p : Vec3 × ℝ => leSF ρ ε hε ha hf η p.1 p.2 k := by
  have hs : Measurable fun q : (Vec3 × ℝ) × Vec3 => (q.2, q.1.2) :=
    measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  have hd : ∀ j : Fin 3, Measurable fun q : (Vec3 × ℝ) × Vec3 =>
      CKN.spatialDeriv η j (q.1.1 - q.2) := fun j =>
    (CKN.contDiff_spatialDeriv_smooth hη j).continuous.measurable.comp
      ((measurable_fst.comp measurable_fst).sub measurable_snd)
  have hP : Measurable fun z : Vec3 × ℝ => lePressure ρ ε hε ha hf z := by
    have h1 := (forcedQuadPressure_stronglyMeasurable ρ ε hε
      (continuous_forcedRegCurve ρ ε hε ha hf)).measurable
    have h2 : Measurable fun z : Vec3 × ℝ => forcePressure f hf z :=
      (Classical.choose_spec (exists_forcePressure f hf)).1.measurable
    exact h1.add h2
  have hm : StronglyMeasurable fun q : (Vec3 × ℝ) × Vec3 =>
      leKernelF ρ ε hε ha hf η q.1.1 k (q.2, q.1.2) := by
    unfold leKernelF
    refine Measurable.stronglyMeasurable ?_
    refine ((Finset.measurable_sum _ fun j _ =>
      ((stronglyMeasurable_leTensor ρ ε hε ha hf j k).measurable.comp hs).mul (hd j)).add
        ((hP.comp hs).mul (hd k))).sub ?_
    exact ((measurable_pi_apply k).comp ((forcedForceMod_stronglyMeasurable f hf).measurable.comp
      hs)).mul (hη.continuous.measurable.comp
        ((measurable_fst.comp measurable_fst).sub measurable_snd))
  exact hm.integral_prod_right'

theorem forcedRegRep_slice_bound (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ k : Fin 3,
      (eLpNorm (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) 2 volume).toReal ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_forcedRegCurve ρ ε hε ha hf).norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ht k => ?_⟩
  have hui : MemLp (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) 2 volume :=
    (forcedRegRep_memLp ρ ε hε ha hf t).eval k
  have h : eLpNorm (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) 2 volume ≤
      ENNReal.ofReal (max C 0) := by
    calc eLpNorm (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) 2 volume
        ≤ eLpNorm (fun y => forcedRegRep ρ ε hε ha hf (y, t)) 2 volume :=
          eLpNorm_mono hui.aestronglyMeasurable fun y => norm_le_pi_norm _ k
      _ = eLpNorm (realVectorL2Representative (forcedRegCurve ρ ε hε ha hf t)) 2 volume :=
          eLpNorm_congr_ae (forcedRegRep_slice ρ ε hε ha hf t)
      _ ≤ ENNReal.ofReal ‖forcedRegCurve ρ ε hε ha hf t‖ :=
          eLpNorm_realVectorL2Representative_le _
      _ ≤ ENNReal.ofReal (max C 0) := by
          refine ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans' ?_)
          have := hC t ht
          rwa [norm_norm] at this
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (le_max_right _ _)] at h'

theorem abs_leW_le {η : Vec3 → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (x : Vec3) (t : ℝ) (k : Fin 3) :
    |leW ρ ε hε ha hf η x t k| ≤ (eLpNorm η 2 volume).toReal *
      (eLpNorm (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) 2 volume).toReal := by
  have h := abs_integral_mul_reflect_le ((forcedRegRep_memLp ρ ε hε ha hf t).eval k)
    (hη.memLp_of_hasCompactSupport (p := 2) hηc) x
  unfold leW
  rw [show (∫ y, η (x - y) * forcedRegRep ρ ε hε ha hf (y, t) k) =
    ∫ y, forcedRegRep ρ ε hε ha hf (y, t) k * η (x - y) from
      integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)]
  exact h

theorem ae_abs_leSF_le {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin 3) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)), ∀ x,
      |leSF ρ ε hε ha hf η x t k| ≤ leSourceBound ρ ε hε ha hf η k t := by
  obtain ⟨M, hM0, hM⟩ := forcedRegTransport_bound ρ ε hε ha hf T
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_forcedRegGrad_slice ρ ε hε ha hf hT.le,
    ae_forcedForceMod_slice hf hT, ae_forcePressure_slice hf hT] with t ht hDu hFF hPF x
  obtain ⟨hF2, hFf⟩ := hFF
  obtain ⟨hpfl, hft, hpf⟩ := hPF
  have hA : ∀ j, MemLp (fun y => leTensor ρ ε hε ha hf j k (y, t)) 2 volume := by
    intro j
    have hu := (forcedRegRep_memLp ρ ε hε ha hf t).eval k
    have hJu : MemLp (fun y => regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf)
        (y, t) j * forcedRegRep ρ ε hε ha hf (y, t) k) 2 volume := by
      refine hu.of_le_mul (c := M) ?_ (Eventually.of_forall fun y => ?_)
      · exact (((measurable_forcedRegTransport ρ ε hε ha hf j).comp
          (measurable_id.prodMk measurable_const)).mul ((measurable_pi_apply k).comp
          ((forcedRegRep_stronglyMeasurable ρ ε hε ha hf).measurable.comp
            (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
      · rw [norm_mul]
        have h := hM (y, t) ⟨ht.1.le, ht.2.le⟩ j
        rw [← Real.norm_eq_abs] at h
        exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    exact hJu.sub (hDu k j)
  exact abs_leSF_le ρ ε hε ha hf hη hηc k hA hF2 hFf hft hpf hpfl x

theorem timePartial_eq_fderiv {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : Vec3 × ℝ) :
    CKN.timePartial ψ z = fderiv ℝ ψ z (0, 1) := by
  unfold CKN.timePartial
  have h : HasFDerivAt (fun s => ψ (z.1, s))
      ((fderiv ℝ ψ (z.1, z.2)).comp (ContinuousLinearMap.inr ℝ Vec3 ℝ)) z.2 :=
    ((hψ.differentiable (by simp)) (z.1, z.2)).hasFDerivAt.comp z.2
      (hasFDerivAt_prodMk_right z.1 z.2)
  rw [h.fderiv]
  rfl

theorem integrable_timePartial_prod {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (T : ℝ) :
    Integrable (fun z => CKN.timePartial ψ z)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  have heq : (fun z => CKN.timePartial ψ z) = fun z => fderiv ℝ ψ z (0, 1) :=
    funext (timePartial_eq_fderiv hψ)
  rw [heq]
  have hcontinuous : Continuous (fun z => fderiv ℝ ψ z (0, 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact hcontinuous.integrable_of_hasCompactSupport
    ((hψc.fderiv ℝ).comp_left (g := fun L : Vec3 × ℝ →L[ℝ] ℝ => L (0, 1)) (by simp))

/-- The space-time energy identity of the mollified velocity. -/
theorem integral_leW_sq_spaceTime {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (k : Fin 3) {T : ℝ} (hT : 0 < T) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) {c d : ℝ} (hc : 0 < c)
    (hcd : c < d) (hdT : d < T) (hψs : ∀ z ∈ tsupport ψ, z.2 ∈ Ioo c d) :
    ∫ t in Ioo 0 T, ∫ x, leW ρ ε hε ha hf η x t k ^ 2 * CKN.timePartial ψ (x, t) =
      2 * ∫ t in Ioo 0 T, ∫ x, leW ρ ε hε ha hf η x t k * leSF ρ ε hε ha hf η x t k *
        ψ (x, t) := by
  have hψ0 : ∀ x t, t ∉ Ioo c d → ψ (x, t) = 0 := fun x t ht =>
    image_eq_zero_of_notMem_tsupport fun h => ht (hψs _ h)
  have hSb := ae_abs_leSF_le ρ ε hε ha hf hη hηc k hT
  have hbi := integrableOn_leSourceBound ρ ε hε ha hf (η := η) k hT
  have hSi : ∀ x, IntegrableOn (fun t => leSF ρ ε hε ha hf η x t k) (Ioo 0 T) := by
    intro x
    refine Integrable.mono' hbi ?_ ?_
    · exact ((stronglyMeasurable_leSF ρ ε hε ha hf hη k).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · filter_upwards [hSb] with t ht
      rw [Real.norm_eq_abs]
      exact ht x
  have hx : ∀ x, ∫ t in Ioo 0 T, leW ρ ε hε ha hf η x t k ^ 2 * CKN.timePartial ψ (x, t) =
      2 * ∫ t in Ioo 0 T, leW ρ ε hε ha hf η x t k * leSF ρ ε hε ha hf η x t k * ψ (x, t) := by
    intro x
    exact integral_leW_sq_time ρ ε hε ha hf hη hηc x k hT
      (hψ.comp (contDiff_const.prodMk contDiff_id)) hc hcd hdT (hψ0 x) (hSi x)
  obtain ⟨Cu, hCu0, hCu⟩ := forcedRegRep_slice_bound ρ ε hε ha hf T
  set Cw := (eLpNorm η 2 volume).toReal * Cu with hCw
  have hCw0 : 0 ≤ Cw := mul_nonneg ENNReal.toReal_nonneg hCu0
  have hWb : ∀ x t, t ∈ Ioo 0 T → |leW ρ ε hε ha hf η x t k| ≤ Cw := fun x t ht =>
    (abs_leW_le ρ ε hε ha hf hη.continuous hηc x t k).trans
      (mul_le_mul_of_nonneg_left (hCu t ⟨ht.1.le, ht.2.le⟩ k) ENNReal.toReal_nonneg)
  have hWm := stronglyMeasurable_leW ρ ε hε ha hf hη.continuous k
  have hSm := stronglyMeasurable_leSF ρ ε hε ha hf hη k
  have hint1 : Integrable (Function.uncurry fun x t =>
      leW ρ ε hε ha hf η x t k ^ 2 * CKN.timePartial ψ (x, t))
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
    have h := (integrable_timePartial_prod hψ hψc T).bdd_mul (c := Cw ^ 2)
      (hWm.measurable.pow_const 2).aestronglyMeasurable (by
        filter_upwards [ae_mem_Ioo_prod T] with z hz
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hWb z.1 z.2 hz) 2)
    exact h
  obtain ⟨Mψ, hMψ⟩ := Continuous.bounded_above_of_compact_support hψ.continuous hψc
  set K : Set Vec3 := Prod.fst '' tsupport ψ with hK
  have hKc : IsCompact K := hψc.image continuous_fst
  have hind : Integrable (K.indicator fun _ => Mψ * Cw) volume :=
    (integrableOn_const hKc.measure_lt_top.ne).integrable_indicator hKc.measurableSet
  have hint2 : Integrable (Function.uncurry fun x t =>
      leW ρ ε hε ha hf η x t k * leSF ρ ε hε ha hf η x t k * ψ (x, t))
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
    refine Integrable.mono' (hind.mul_prod hbi) ?_ ?_
    · exact ((hWm.measurable.mul hSm.measurable).mul hψ.continuous.measurable).aestronglyMeasurable
    · have h1 := ae_prod_of_ae_forall (P := fun z => z.2 ∈ Ioo 0 T ∧
          |leSF ρ ε hε ha hf η z.1 z.2 k| ≤ leSourceBound ρ ε hε ha hf η k z.2)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioo, hSb] with t ht1 ht2 x
          exact ⟨ht1, ht2 x⟩)
      filter_upwards [h1] with z hz
      rcases z with ⟨x0, t0⟩
      obtain ⟨hzt, hzS⟩ := hz
      simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul]
      have hW := hWb x0 t0 hzt
      have hb0 : 0 ≤ leSourceBound ρ ε hε ha hf η k t0 := (abs_nonneg _).trans hzS
      by_cases hzK : x0 ∈ K
      · rw [indicator_of_mem hzK]
        have hψz := hMψ (x0, t0)
        rw [Real.norm_eq_abs] at hψz
        calc |leW ρ ε hε ha hf η x0 t0 k| * |leSF ρ ε hε ha hf η x0 t0 k| * |ψ (x0, t0)|
            ≤ Cw * leSourceBound ρ ε hε ha hf η k t0 * Mψ := by
              gcongr
          _ = Mψ * Cw * leSourceBound ρ ε hε ha hf η k t0 := by ring
      · have hz0 : ψ (x0, t0) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hzK ⟨(x0, t0), h, rfl⟩
        rw [hz0, abs_zero, mul_zero, indicator_of_notMem hzK, zero_mul]
  rw [← integral_integral_swap hint1, ← integral_integral_swap hint2, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall hx)

end Swap

end CKN.Leray

end
