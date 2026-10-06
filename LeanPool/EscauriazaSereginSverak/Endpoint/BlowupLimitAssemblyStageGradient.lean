/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblySourceAE
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTimeAE

/-!
# Weak gradients of the rescaled trace

On each fixed ball, and for all small scales, the rescaled trace
representative of the blow-up sequence in `prop:blowup-limit` has the
rescaled (measurable) source gradient as its weak spatial gradient on almost
every time slice.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The Euclidean norm on Vec3 satisfies the triangle inequality. -/
theorem blowupLimitAssembly_vec3EuclideanNorm_add_le (a b : Vec3) :
    vec3EuclideanNorm (a + b) ≤ vec3EuclideanNorm a + vec3EuclideanNorm b := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    WithLp.toLp_add]
  exact norm_add_le _ _

/-- The rescaled trace has the rescaled measurable source gradient as weak
spatial gradient on the ball of radius R, for almost every past time, once
the rescaled cylinder lies inside the inner source cylinder. -/
theorem blowupLimitAssembly_trace_hasWeakGradientOn
    {u : ParabolicPoint → Vec3} {Du Dm : ParabolicPoint → Fin 3 → Vec3}
    (hDm : Measurable Dm)
    (hDmEq : goodPointDomain.indicator Dm =ᵐ[volume] goodPointDomain.indicator Du)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x,t) i) (fun x => Du (x,t) i))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3) (hW : Measurable W)
    (htrace : ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (fun x => W (x,⟨t,ht⟩)) =ᵐ[volume.restrict
          (vec3Ball (0 : Vec3) (3 / 4 : ℝ))] (fun x => u (x,t)))
    {x₀ : Vec3} (hx₀ : vec3EuclideanNorm x₀ ≤ 1 / 2) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0) {r R : ℝ} (hr : 0 < r)
    (hrR : r * R < 1 / 4) (hrR2 : r ^ 2 * R < 1 / 4) :
    ∀ᵐ t ∂(volume.restrict (Ioo (-R) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) R)
        (fun x => blowupLimitTraceRescaling W x₀ t₀ r (x,t) i)
        (fun x => blowupGradient x₀ t₀ r Dm (x,t) i) := by
  set I : Set ℝ := Ioo (-(3 / 4 : ℝ) ^ 2) 0
  set B : Set Vec3 := vec3Ball (0 : Vec3) (3 / 4 : ℝ)
  set B₁ : Set Vec3 := vec3Ball (0 : Vec3) 1
  have hIsub : I ⊆ Ioo (-1) 0 := by
    intro t ht
    exact ⟨by linarith only [ht.1], ht.2⟩
  have hDslices : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure Vec3),
      goodPointDomain.indicator Dm (x,t) = goodPointDomain.indicator Du (x,t) := by
    have hprod : ∀ᵐ z ∂((volume : Measure Vec3).prod (volume : Measure ℝ)),
        goodPointDomain.indicator Dm z = goodPointDomain.indicator Du z := by
      rw [← Measure.volume_eq_prod]
      exact hDmEq
    exact blowupLimitAssembly_ae_ae_of_ae_prod_swap hprod
  let P : ℝ → Prop := fun τ =>
    (∃ hτ : τ ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
      (fun x => W (x,⟨τ,hτ⟩)) =ᵐ[volume.restrict B] (fun x => u (x,τ))) ∧
    (∀ i : Fin 3, HasWeakGradientOn B₁ (fun x => u (x,τ) i)
      (fun x => Du (x,τ) i)) ∧
    (∀ᵐ x ∂(volume : Measure Vec3),
      goodPointDomain.indicator Dm (x,τ) = goodPointDomain.indicator Du (x,τ))
  have hP : ∀ᵐ τ ∂(volume.restrict I), P τ := by
    filter_upwards [htrace, ae_restrict_of_ae_restrict_of_subset hIsub hgrad,
      ae_restrict_of_ae hDslices] with τ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hJ : Ioo (-R) 0 ⊆ rescaledTime r t₀ I := by
    intro t ht
    change t₀ + r ^ 2 * t ∈ I
    have hr2 : 0 < r ^ 2 := by positivity
    have hlow : -(r ^ 2 * R) < r ^ 2 * t := by nlinarith only [ht.1, hr2]
    have hup : r ^ 2 * t < 0 := mul_neg_of_pos_of_neg hr2 ht.2
    constructor
    · nlinarith only [hlow, ht₀.1, hrR2]
    · linarith only [hup, ht₀.2]
  have hpull := blowup_ae_time_pullback_on r t₀ hr I (Ioo (-R) 0)
    measurableSet_Ioo hJ P hP
  filter_upwards [hpull, ae_restrict_mem measurableSet_Ioo] with t ht htI
  obtain ⟨⟨hτ, hWu⟩, hgτ, hDτ⟩ := ht
  set τ : ℝ := scalingTime r t₀ t with hτdef
  have hτI : τ ∈ Ioo (-1 : ℝ) 0 := hIsub (hJ htI)
  set Ω : Set Vec3 := vec3Ball x₀ (r * R)
  have hΩopen : IsOpen Ω := isOpen_vec3Ball _ _
  have hΩB : Ω ⊆ B := by
    intro y hy
    rw [mem_vec3Ball] at hy ⊢
    rw [sub_zero]
    have htri := blowupLimitAssembly_vec3EuclideanNorm_add_le (y - x₀) x₀
    rw [sub_add_cancel] at htri
    linarith only [htri, hy, hx₀, hrR]
  have hBB₁ : B ⊆ B₁ := by
    intro y hy
    rw [mem_vec3Ball] at hy ⊢
    linarith only [hy]
  have hΩeq : Ω = scalingSpace r x₀ '' vec3Ball (0 : Vec3) R :=
    (blowupLimitAssembly_scalingSpace_image_vec3Ball x₀ hr R).symm
  intro i j
  let g : Vec3 → ℝ := fun y => blowupLimitTraceZeroExtension W (y, τ) i
  let dg : Vec3 → ℝ := fun y => goodPointDomain.indicator Dm (y, τ) i j
  have hgmeas : Measurable g :=
    (measurable_pi_apply i).comp
      ((measurable_blowupLimitTraceZeroExtension W hW).comp measurable_prodMk_right)
  have hdgmeas : Measurable dg := by
    have hind : Measurable (goodPointDomain.indicator Dm) :=
      hDm.indicator (((isOpen_vec3Ball (0 : Vec3) 1).measurableSet).prod
        measurableSet_Ioo)
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (hind.comp measurable_prodMk_right))
  have hsource : HasWeakPartialDerivOn Ω j (fun y => u (y,τ) i)
      (fun y => Du (y,τ) i j) :=
    (hgτ i j).restrict hΩopen (hΩB.trans hBB₁)
  have hgEq : (fun y => u (y,τ) i) =ᵐ[volume.restrict Ω] g := by
    have hWuΩ := ae_restrict_of_ae_restrict_of_subset hΩB hWu
    filter_upwards [hWuΩ, ae_restrict_mem hΩopen.measurableSet] with y hy hyΩ
    have hyB : y ∈ B := hΩB hyΩ
    have hyB' : vec3EuclideanNorm y < 3 / 4 := by
      have h := hyB
      rw [mem_vec3Ball, sub_zero] at h
      exact h
    have hZ : blowupLimitTraceZeroExtension W (y, τ) = W (y, ⟨τ, hτ⟩) := by
      simp [blowupLimitTraceZeroExtension, hyB', hτ]
    show u (y,τ) i = blowupLimitTraceZeroExtension W (y, τ) i
    rw [hZ]
    exact congrArg (fun v : Vec3 => v i) hy.symm
  have hdgEq : (fun y => Du (y,τ) i j) =ᵐ[volume.restrict Ω] dg := by
    filter_upwards [ae_restrict_of_ae hDτ, ae_restrict_mem hΩopen.measurableSet]
      with y hy hyΩ
    have hdom : ((y, τ) : ParabolicPoint) ∈ goodPointDomain :=
      ⟨hBB₁ (hΩB hyΩ), hτI⟩
    have e1 : goodPointDomain.indicator Dm ((y, τ) : ParabolicPoint) =
        Dm ((y, τ) : ParabolicPoint) := Set.indicator_of_mem hdom Dm
    have e2 : goodPointDomain.indicator Du ((y, τ) : ParabolicPoint) =
        Du ((y, τ) : ParabolicPoint) := Set.indicator_of_mem hdom Du
    change goodPointDomain.indicator Dm ((y, τ) : ParabolicPoint) =
      goodPointDomain.indicator Du ((y, τ) : ParabolicPoint) at hy
    rw [e1, e2] at hy
    show Du (y,τ) i j = goodPointDomain.indicator Dm ((y, τ) : ParabolicPoint) i j
    rw [e1, hy]
  have hΩweak : HasWeakPartialDerivOn Ω j g dg :=
    blowupLimitAssembly_hasWeakPartialDerivOn_congr hgEq hdgEq hsource
  have hscaled := hasWeakPartialDerivOn_scaling r hr x₀ hΩopen.measurableSet j
    hΩeq hΩweak hgmeas.aestronglyMeasurable hdgmeas.aestronglyMeasurable
  have hfun : (fun x => blowupLimitTraceRescaling W x₀ t₀ r (x,t) i) =
      fun x => r * g (scalingSpace r x₀ x) := by
    funext x
    simp [blowupLimitTraceRescaling, g, parabolicTranslate, parabolicScale,
      scalingSpace, hτdef, scalingTime]
  have hgradfun : (fun x => blowupGradient x₀ t₀ r Dm (x,t) i j) =
      fun x => r ^ 2 * dg (scalingSpace r x₀ x) := by
    funext x
    simp [blowupGradient, parabolicRescaleGradient, dg, parabolicTranslate,
      parabolicScale, scalingSpace, hτdef, scalingTime]
  change HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R) j
    (fun x => blowupLimitTraceRescaling W x₀ t₀ r (x,t) i)
    (fun x => blowupGradient x₀ t₀ r Dm (x,t) i j)
  rw [hfun, hgradfun]
  exact hscaled

end ESS

end
