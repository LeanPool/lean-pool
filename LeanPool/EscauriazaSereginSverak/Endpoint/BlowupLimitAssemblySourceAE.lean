/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitRepresentativeExtension
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupFields
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceWeak

/-!
# Almost-everywhere bookkeeping for the rescaled trace

The blow-up sequence of `prop:blowup-limit` is built from the jointly
measurable trace representative of `lem:weak-cont-L3`. These lemmas move
almost-everywhere statements between time slices and space-time, and pull
them back through the parabolic rescaling.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Almost every point of a product measure gives, for almost every second
coordinate, almost every first coordinate. -/
theorem blowupLimitAssembly_ae_ae_of_ae_prod_swap
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {p : α × β → Prop} (h : ∀ᵐ z ∂μ.prod ν, p z) :
    ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, p (x, y) := by
  have hswap : ∀ᵐ q ∂ν.prod μ, p q.swap :=
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod hswap

/-- A space-time almost-everywhere property on a product cylinder holds, for
almost every time, almost everywhere on the spatial slice. -/
theorem blowupLimitAssembly_ae_slices_of_ae_spaceTime
    {Ω : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → Prop}
    (h : ∀ᵐ z ∂(volume.restrict (spaceTimeSet Ω I)), p z) :
    ∀ᵐ t ∂(volume.restrict I), ∀ᵐ x ∂(volume.restrict Ω), p (x, t) := by
  have hprod : (volume : Measure ParabolicPoint).restrict (spaceTimeSet Ω I) =
      (volume.restrict Ω).prod (volume.restrict I) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    rfl
  rw [hprod] at h
  exact blowupLimitAssembly_ae_ae_of_ae_prod_swap (μ := volume.restrict Ω)
    (ν := volume.restrict I) (p := fun z : Vec3 × ℝ => p z) h

/-- Slicewise almost-everywhere equality of measurable fields is space-time
almost-everywhere equality. -/
theorem blowupLimitAssembly_ae_eq_of_ae_slices
    {Ω : Set Vec3} {I : Set ℝ} {F G : ParabolicPoint → Vec3}
    (hF : Measurable F) (hG : Measurable G)
    (h : ∀ᵐ t ∂(volume.restrict I), ∀ᵐ x ∂(volume.restrict Ω), F (x,t) = G (x,t)) :
    F =ᵐ[volume.restrict (spaceTimeSet Ω I)] G := by
  have hprod : (volume : Measure ParabolicPoint).restrict (spaceTimeSet Ω I) =
      (volume.restrict Ω).prod (volume.restrict I) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    rfl
  have hset : MeasurableSet {z : Vec3 × ℝ | F z = G z} :=
    measurableSet_eq_fun hF hG
  rw [hprod, Filter.EventuallyEq]
  change ∀ᵐ z : Vec3 × ℝ ∂((volume.restrict Ω).prod (volume.restrict I)), F z = G z
  rw [Measure.ae_prod_iff_ae_ae hset]
  exact (Measure.ae_ae_comm (p := fun x t => F (x,t) = G (x,t)) hset).2 h

/-- A space-time almost-everywhere property pulls back through a positive
parabolic rescaling. -/
theorem blowupLimitAssembly_ae_rescale_pullback (x₀ : Vec3) (t₀ r : ℝ)
    (hr : 0 < r) {Ω : Set Vec3} {I : Set ℝ} (hΩ : MeasurableSet Ω)
    (hI : MeasurableSet I) {p : ParabolicPoint → Prop}
    (h : ∀ᵐ z ∂(volume.restrict (spaceTimeSet Ω I)), p z) :
    ∀ᵐ z ∂(volume.restrict (spaceTimeSet (rescaledSpace r x₀ Ω)
        (rescaledTime r t₀ I))),
      p (parabolicTranslate x₀ t₀ (parabolicScale r z)) := by
  have hmap := map_scalingParabolic_restrict hr ((x₀, t₀) : ParabolicPoint) hΩ hI
  have hmeas : Measurable (scalingParabolic r ((x₀, t₀) : ParabolicPoint)) := by
    have h1 : Measurable (fun z : Vec3 × ℝ => x₀ + r • z.1) :=
      measurable_const.add (measurable_fst.const_smul r)
    have h2 : Measurable (fun z : Vec3 × ℝ => t₀ + r ^ 2 * z.2) :=
      measurable_const.add (measurable_const.mul measurable_snd)
    exact h1.prodMk h2
  have hpmap : ∀ᵐ w ∂Measure.map (scalingParabolic r ((x₀, t₀) : ParabolicPoint))
      (volume.restrict (spaceTimeSet (rescaledSpace r x₀ Ω)
        (rescaledTime r t₀ I))), p w := by
    rw [hmap]
    exact h.filter_mono Measure.smul_absolutelyContinuous.ae_le
  exact ae_of_ae_map hmeas.aemeasurable hpmap

/-- The spatial rescaling maps a centred ball onto a ball around the base
point. -/
theorem blowupLimitAssembly_scalingSpace_image_vec3Ball (x₀ : Vec3) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    scalingSpace r x₀ '' vec3Ball (0 : Vec3) R = vec3Ball x₀ (r * R) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_vec3Ball] at hx ⊢
    rw [sub_zero] at hx
    simp only [scalingSpace, add_sub_cancel_left, vec3EuclideanNorm_smul,
      abs_of_pos hr]
    exact mul_lt_mul_of_pos_left hx hr
  · intro hy
    refine ⟨r⁻¹ • (y - x₀), ?_, ?_⟩
    · rw [mem_vec3Ball] at hy ⊢
      rw [sub_zero, vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
      rw [inv_mul_lt_iff₀ hr]
      exact hy
    · simp only [scalingSpace, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
        add_sub_cancel]

/-- Weak partial derivatives are unchanged by almost-everywhere changes on
the domain. -/
theorem blowupLimitAssembly_hasWeakPartialDerivOn_congr
    {Ω : Set Vec3} {i : Fin 3} {u u' g g' : Vec3 → ℝ}
    (hu : u =ᵐ[volume.restrict Ω] u') (hg : g =ᵐ[volume.restrict Ω] g')
    (h : HasWeakPartialDerivOn Ω i u g) :
    HasWeakPartialDerivOn Ω i u' g' := by
  intro φ hφ hφc hφΩ
  have hmain := h φ hφ hφc hφΩ
  calc
    (∫ x in Ω, u' x * (fderiv ℝ φ x) (basisVec i)) =
        ∫ x in Ω, u x * (fderiv ℝ φ x) (basisVec i) := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx]
    _ = -∫ x in Ω, g x * φ x := hmain
    _ = -∫ x in Ω, g' x * φ x := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

/-- The zero-extended trace representative agrees almost everywhere with
the source velocity on the inner source cylinder. -/
theorem blowupLimitAssembly_traceZeroExtension_ae_eq
    {u um : ParabolicPoint → Vec3} (hum : Measurable um)
    (hu : u =ᵐ[volume.restrict
      (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))] um)
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3) (hW : Measurable W)
    (htrace : ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (fun x => W (x,⟨t,ht⟩)) =ᵐ[volume.restrict
          (vec3Ball (0 : Vec3) (3 / 4 : ℝ))] (fun x => u (x,t))) :
    blowupLimitTraceZeroExtension W =ᵐ[volume.restrict
      (spaceTimeSet (vec3Ball (0 : Vec3) (3 / 4 : ℝ))
        (Ioo (-(3 / 4 : ℝ) ^ 2) 0))] u := by
  have hsub : spaceTimeSet (vec3Ball (0 : Vec3) (3 / 4 : ℝ))
      (Ioo (-(3 / 4 : ℝ) ^ 2) 0) ⊆
      spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) := by
    intro z hz
    refine ⟨?_, ?_, hz.2.2⟩
    · have h := hz.1
      rw [mem_vec3Ball] at h ⊢
      linarith only [h]
    · have h := hz.2.1
      linarith only [h]
  have hu' := ae_restrict_of_ae_restrict_of_subset hsub hu
  have hslices := blowupLimitAssembly_ae_slices_of_ae_spaceTime hu'
  have hZ : ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
      ∀ᵐ x ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))),
        blowupLimitTraceZeroExtension W (x,t) = um (x,t) := by
    filter_upwards [htrace, hslices] with t ht hut
    obtain ⟨htI, hWu⟩ := ht
    filter_upwards [hWu, hut,
      ae_restrict_mem (isOpen_vec3Ball (0 : Vec3) (3 / 4 : ℝ)).measurableSet]
      with x h1 h2 hx
    have hZx : blowupLimitTraceZeroExtension W (x,t) = W (x,⟨t,htI⟩) := by
      simp [blowupLimitTraceZeroExtension, hx, htI]
    rw [hZx, h1, h2]
  have hZum := blowupLimitAssembly_ae_eq_of_ae_slices
    (measurable_blowupLimitTraceZeroExtension W hW) hum hZ
  filter_upwards [hZum, hu'] with z h1 h2
  rw [h1, h2]

end ESS

end
