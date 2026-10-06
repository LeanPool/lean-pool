/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyStageGradient
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyBounds
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSuitable
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitCompactSlice

/-!
# Stagewise bounds for the rescaled trace

For the blow-up sequence of `prop:blowup-limit` built from the trace
representative: a measurable choice of the source gradient, agreement of
the rescaled trace with the zero-extended rescaled velocity on fixed
cylinders, the local gradient energy bound from the local energy step, and
the uniform compact slice bound.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A field that is almost everywhere strongly measurable on the source
cylinder has a measurable version whose zero extension agrees almost
everywhere with its own. -/
theorem blowupLimitAssembly_exists_measurable_version
    {β : Type*} [TopologicalSpace β] [Zero β] [MeasurableSpace β] [BorelSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β]
    {F : ParabolicPoint → β}
    (hF : AEStronglyMeasurable F
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0)))) :
    ∃ Fm : ParabolicPoint → β, Measurable Fm ∧
      F =ᵐ[volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))] Fm ∧
      goodPointDomain.indicator Fm =ᵐ[volume] goodPointDomain.indicator F := by
  refine ⟨hF.mk F, hF.stronglyMeasurable_mk.measurable, hF.ae_eq_mk, ?_⟩
  have hD : MeasurableSet (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0)) :=
    (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo
  have h := (ae_restrict_iff' hD).1 hF.ae_eq_mk
  filter_upwards [h] with z hz
  by_cases hzD : z ∈ goodPointDomain
  · rw [indicator_of_mem hzD, indicator_of_mem hzD]
    exact (hz hzD).symm
  · rw [indicator_of_notMem hzD, indicator_of_notMem hzD]

/-- Almost-everywhere equal zero extensions have almost-everywhere equal
blow-up gradients. -/
theorem blowupLimitAssembly_blowupGradient_ae_eq
    {Du Dm : ParabolicPoint → Fin 3 → Vec3}
    (hDmEq : goodPointDomain.indicator Dm =ᵐ[volume] goodPointDomain.indicator Du)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    blowupGradient x₀ t₀ r Dm =ᵐ[volume] blowupGradient x₀ t₀ r Du := by
  have hset : spaceTimeSet (univ : Set Vec3) (univ : Set ℝ) = univ := univ_prod_univ
  have h : ∀ᵐ z ∂(volume.restrict (spaceTimeSet (univ : Set Vec3) (univ : Set ℝ))),
      goodPointDomain.indicator Dm z = goodPointDomain.indicator Du z := by
    rw [hset, Measure.restrict_univ]
    exact hDmEq
  have hpull := blowupLimitAssembly_ae_rescale_pullback x₀ t₀ r hr
    MeasurableSet.univ MeasurableSet.univ h
  have hset' : spaceTimeSet (rescaledSpace r x₀ univ) (rescaledTime r t₀ univ) =
      (univ : Set ParabolicPoint) := by
    simp only [rescaledSpace, rescaledTime, preimage_univ]
    exact univ_prod_univ
  rw [hset', Measure.restrict_univ] at hpull
  filter_upwards [hpull] with z hz
  funext i
  simp only [blowupGradient, parabolicRescaleGradient, hz]

/-- The rescaled trace agrees almost everywhere with the zero-extended
rescaled velocity on every fixed past cylinder at small scales. -/
theorem blowupLimitAssembly_trace_ae_eq_blowupVelocity
    {u um : ParabolicPoint → Vec3} (hum : Measurable um)
    (hu : u =ᵐ[volume.restrict
      (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))] um)
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3) (hW : Measurable W)
    (htrace : ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (fun x => W (x,⟨t,ht⟩)) =ᵐ[volume.restrict
          (vec3Ball (0 : Vec3) (3 / 4 : ℝ))] (fun x => u (x,t)))
    {x₀ : Vec3} (hx₀ : vec3EuclideanNorm x₀ ≤ 1 / 2) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0) {r R a : ℝ} (hr : 0 < r)
    (hrR : r * R < 1 / 4) (hra : r ^ 2 * (-a) < 1 / 4) :
    blowupLimitTraceRescaling W x₀ t₀ r =ᵐ[volume.restrict
      (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)] blowupVelocity x₀ t₀ r u := by
  have hZ := blowupLimitAssembly_traceZeroExtension_ae_eq hum hu W hW htrace
  have hpull := blowupLimitAssembly_ae_rescale_pullback x₀ t₀ r hr
    (isOpen_vec3Ball (0 : Vec3) (3 / 4 : ℝ)).measurableSet measurableSet_Ioo hZ
  have hsub : vec3Ball (0 : Vec3) R ×ˢ Ioo a 0 ⊆
      spaceTimeSet (rescaledSpace r x₀ (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))
        (rescaledTime r t₀ (Ioo (-(3 / 4 : ℝ) ^ 2) 0)) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨?_, ?_⟩
    · change x₀ + r • x ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ)
      rw [mem_vec3Ball, sub_zero]
      rw [mem_vec3Ball, sub_zero] at hx
      have htri := blowupLimitAssembly_vec3EuclideanNorm_add_le x₀ (r • x)
      rw [vec3EuclideanNorm_smul, abs_of_pos hr] at htri
      have hrx : r * vec3EuclideanNorm x < r * R := mul_lt_mul_of_pos_left hx hr
      linarith only [htri, hrx, hx₀, hrR]
    · change t₀ + r ^ 2 * t ∈ Ioo (-(3 / 4 : ℝ) ^ 2) 0
      have hr2 : 0 < r ^ 2 := by positivity
      have hlow : r ^ 2 * a < r ^ 2 * t := mul_lt_mul_of_pos_left ht.1 hr2
      have hup : r ^ 2 * t < 0 := mul_neg_of_pos_of_neg hr2 ht.2
      constructor
      · nlinarith only [hlow, ht₀.1, hra]
      · linarith only [hup, ht₀.2]
  have hpull' := ae_restrict_of_ae_restrict_of_subset hsub hpull
  have hdom : vec3Ball (0 : Vec3) R ×ˢ Ioo a 0 ⊆ blowupDomain x₀ t₀ r := by
    intro z hz
    have hz' := hsub hz
    refine ⟨?_, ?_⟩
    · have h := hz'.1
      change x₀ + r • z.1 ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ) at h
      change x₀ + r • z.1 ∈ vec3Ball (0 : Vec3) 1
      rw [mem_vec3Ball] at h ⊢
      linarith only [h]
    · have h := hz'.2
      change t₀ + r ^ 2 * z.2 ∈ Ioo (-(3 / 4 : ℝ) ^ 2) 0 at h
      change t₀ + r ^ 2 * z.2 ∈ Ioo (-1 : ℝ) 0
      exact ⟨by linarith only [h.1], h.2⟩
  have hmeas : MeasurableSet (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0) :=
    (isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioo
  filter_upwards [hpull', ae_restrict_mem hmeas] with z hz hzC
  rw [blowupVelocity_eq_of_mem x₀ t₀ r u z (hdom hzC)]
  simp only [blowupLimitTraceRescaling]
  rw [hz]

/-- The rescaled measurable gradient is measurable. -/
theorem measurable_blowupLimitAssembly_blowupGradient
    {Dm : ParabolicPoint → Fin 3 → Vec3} (hDm : Measurable Dm)
    (x₀ : Vec3) (t₀ r : ℝ) :
    Measurable (blowupGradient x₀ t₀ r Dm) := by
  have hind : Measurable (goodPointDomain.indicator Dm) :=
    hDm.indicator (((isOpen_vec3Ball (0 : Vec3) 1).measurableSet).prod
      measurableSet_Ioo)
  have hT : Measurable (fun z : ParabolicPoint =>
      parabolicTranslate x₀ t₀ (parabolicScale r z)) := by
    have h1 : Measurable (fun z : Vec3 × ℝ => x₀ + r • z.1) :=
      measurable_const.add (measurable_fst.const_smul r)
    have h2 : Measurable (fun z : Vec3 × ℝ => t₀ + r ^ 2 * z.2) :=
      measurable_const.add (measurable_const.mul measurable_snd)
    exact h1.prodMk h2
  apply measurable_pi_iff.mpr
  intro i
  exact ((measurable_pi_apply i).comp (hind.comp hT)).const_smul (r ^ 2)

/-- The local gradient energy of the rescaled measurable gradient on a
fixed ball and past time interval is bounded by the rescaled local energy
estimate. -/
theorem blowupLimitAssembly_trace_gradient_energy
    {u : ParabolicPoint → Vec3} {Du Dm : ParabolicPoint → Fin 3 → Vec3}
    (hDm : Measurable Dm)
    (hDmEq : goodPointDomain.indicator Dm =ᵐ[volume] goodPointDomain.indicator Du)
    {x₀ : Vec3} (hx₀ : vec3EuclideanNorm x₀ ≤ 1 / 2) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hrR : r * R < 1 / 4) (hrR2 : r ^ 2 * R < 3 / 4)
    (f : ParabolicPoint → Vec3) (C : ℝ)
    (hint : IntegrableOn (fun z => spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ r u) (parabolicRescaleGradient x₀ t₀ r Du) z)
      (spaceTimeSet (CKN.euclideanBall 0 R) (Ioo (-R) 0)) volume)
    (hbound : 2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo (-R) 0),
      spatialGradientSq (parabolicRescaleVelocity x₀ t₀ r u)
        (parabolicRescaleGradient x₀ t₀ r Du) z) ≤ C) :
    (∫⁻ t in Icc (-R) 0, ∫⁻ x in vec3Ball (0 : Vec3) R,
      ENNReal.ofReal (spatialGradientSq f (blowupGradient x₀ t₀ r Dm) (x,t))) ≤
      ENNReal.ofReal (C / 2) := by
  set B : Set Vec3 := vec3Ball (0 : Vec3) R
  set J : Set ℝ := Ioo (-R) 0
  have hDG := measurable_blowupLimitAssembly_blowupGradient hDm x₀ t₀ r
  have hF : Measurable (fun z : Vec3 × ℝ =>
      ENNReal.ofReal (spatialGradientSq f (blowupGradient x₀ t₀ r Dm) z)) :=
    ENNReal.measurable_ofReal.comp
      (blowupLimitAssembly_measurable_spatialGradientSq _ _ hDG)
  have hprod : (∫⁻ z in B ×ˢ J,
      ENNReal.ofReal (spatialGradientSq f (blowupGradient x₀ t₀ r Dm) z)) =
      ∫⁻ t in J, ∫⁻ x in B,
        ENNReal.ofReal (spatialGradientSq f (blowupGradient x₀ t₀ r Dm) (x,t)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod_symm _ hF.aemeasurable]
  have hBJ : MeasurableSet (B ×ˢ J) :=
    (isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioo
  have hae := blowupLimitAssembly_blowupGradient_ae_eq hDmEq x₀ t₀ r hr
  have heqOn := (blowupFields_eq_rescale_on_cylinder u Du (fun _ => 0) x₀ t₀ r R (-R)
    hx₀ ht₀ hr hrR (by linarith only [hrR2])).2.1
  have hcongr : (∫⁻ z in B ×ˢ J,
      ENNReal.ofReal (spatialGradientSq f (blowupGradient x₀ t₀ r Dm) z)) =
      ∫⁻ z in B ×ˢ J, ENNReal.ofReal (spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ r u) (parabolicRescaleGradient x₀ t₀ r Du) z) := by
    apply setLIntegral_congr_fun_ae hBJ
    filter_upwards [hae] with z hz hzBJ
    have hz' : blowupGradient x₀ t₀ r Dm z = parabolicRescaleGradient x₀ t₀ r Du z := by
      rw [hz]
      exact heqOn hzBJ
    unfold spatialGradientSq
    rw [hz']
  have hset : B ×ˢ J = spaceTimeSet (CKN.euclideanBall 0 R) (Ioo (-R) 0) := by
    rw [euclideanBall_eq_vec3Ball hR]
    rfl
  have hnn : 0 ≤ᵐ[volume.restrict (spaceTimeSet (CKN.euclideanBall 0 R) (Ioo (-R) 0))]
      (fun z => spatialGradientSq (parabolicRescaleVelocity x₀ t₀ r u)
        (parabolicRescaleGradient x₀ t₀ r Du) z) := by
    filter_upwards [] with z
    unfold spatialGradientSq
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  calc
    (∫⁻ t in Icc (-R) 0, ∫⁻ x in B,
        ENNReal.ofReal (spatialGradientSq f (blowupGradient x₀ t₀ r Dm) (x,t))) =
        ∫⁻ t in J, ∫⁻ x in B,
          ENNReal.ofReal (spatialGradientSq f (blowupGradient x₀ t₀ r Dm) (x,t)) :=
      setLIntegral_congr Ioo_ae_eq_Icc.symm
    _ = ∫⁻ z in B ×ˢ J,
          ENNReal.ofReal (spatialGradientSq f (blowupGradient x₀ t₀ r Dm) z) :=
      hprod.symm
    _ = ∫⁻ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo (-R) 0),
          ENNReal.ofReal (spatialGradientSq (parabolicRescaleVelocity x₀ t₀ r u)
            (parabolicRescaleGradient x₀ t₀ r Du) z) := by
      rw [hcongr, hset]
      rfl
    _ = ENNReal.ofReal (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo (-R) 0),
          spatialGradientSq (parabolicRescaleVelocity x₀ t₀ r u)
            (parabolicRescaleGradient x₀ t₀ r Du) z) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ ≤ ENNReal.ofReal (C / 2) :=
      ENNReal.ofReal_le_ofReal (by linarith only [hbound])

/-- Every rescaled trace slice has a uniform local L² bound on each compact
set, for all scales and all times. -/
theorem blowupLimitAssembly_trace_compact_slice_bound
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3) (M : ℝ)
    (hsource : ∀ t,
      MemLp ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
        (fun x => W (x,t))) 3 volume ∧
      eLpNorm (fun x => vec3EuclideanNorm
        ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
          (fun y => W (y,t)) x)) 3 volume ≤ ENNReal.ofReal M)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (C : Set Vec3) (hC : IsCompact C) :
    ∃ M' : ℝ≥0∞, M' < ⊤ ∧ ∀ n t,
      (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm
        (blowupLimitTraceRescaling W x₀ t₀ (r n) (x,t))) ^ (2 : ℝ)) ≤ M' := by
  refine ⟨(ENNReal.ofReal M * (volume C) ^ (1 / 6 : ℝ)) ^ (2 : ℝ), ?_, ?_⟩
  · have hC' : volume C < ⊤ := hC.measure_lt_top
    have h1 : (volume C) ^ (1 / 6 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC'.ne
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1).ne
  intro n t
  by_cases hτ : t₀ + (r n) ^ 2 * t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0
  · exact blowup_limit_rescaling_compact_slice_bound W M hsource x₀ t₀
      (fun _ => r n) (fun _ => hr n) C hC t t
      (fun _ s hs => by rw [le_antisymm hs.2 hs.1]; exact hτ) 0 t ⟨le_rfl, le_rfl⟩
  · have hzero : ∀ x : Vec3, blowupLimitTraceRescaling W x₀ t₀ (r n) (x,t) = 0 := by
      intro x
      simp [blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
        parabolicTranslate, parabolicScale, hτ]
    simp only [hzero, vec3EuclideanNorm_zero, ENNReal.ofReal_zero]
    rw [ENNReal.zero_rpow_of_pos (by norm_num), lintegral_zero]
    exact zero_le

end ESS

end
