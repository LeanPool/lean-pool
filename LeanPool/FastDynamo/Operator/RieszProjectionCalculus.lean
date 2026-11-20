/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.ResolventHolomorphy
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Conditional Riesz-projection calculus

This file develops the operator algebra that can be used once a common
resolvent annulus has been constructed.  It proves the separated-circle
kernel exchange by Bochner--Fubini, combines it with annular holomorphy to
obtain an idempotent normalized contour operator.  It also records the
restriction `HasResolventOn.mono` of a chosen resolver to a smaller parameter
set.
No spectral isolation or Ponomarenko-specific hypothesis is asserted here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex Metric Set

namespace HasResolventOn

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A B : DomainOperator X D} {S T : Set ℂ}

/-- Restrict a chosen resolvent to a smaller parameter set. -/
def mono (h : HasResolventOn A S) (hTS : T ⊆ S) : HasResolventOn A T where
  inv := h.inv
  left_inv z hz := h.left_inv z (hTS hz)
  right_inv z hz := h.right_inv z (hTS hz)
  continuousOn := h.continuousOn.mono hTS

/-- Restricting a resolver to a smaller parameter set keeps the same chosen domain-valued
inverse. -/
@[simp] theorem mono_inv (h : HasResolventOn A S) (hTS : T ⊆ S) :
    (h.mono hTS).inv = h.inv := rfl

/-- Restricting a resolver to a smaller parameter set keeps the same ambient state resolvent. -/
@[simp] theorem mono_stateResolvent (h : HasResolventOn A S) (hTS : T ⊆ S) :
    (h.mono hTS).stateResolvent = h.stateResolvent := rfl

/-- The resolvent product is the divided difference of the resolvent. -/
theorem stateResolvent_comp_eq_inv_smul_sub (h : HasResolventOn A S)
    {z q : ℂ} (hz : z ∈ S) (hq : q ∈ S) (hzq : q ≠ z) :
    (h.stateResolvent z).comp (h.stateResolvent q) =
      (q - z)⁻¹ • (h.stateResolvent z - h.stateResolvent q) := by
  rw [h.stateResolvent_sub_stateResolvent hz hq]
  simp [smul_smul, sub_ne_zero.mpr hzq]

end HasResolventOn

namespace circleIntegral

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A circle integral commutes with a continuous complex-linear map. -/
theorem map (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), L (f z)) = L (∮ z in C(c, R), f z) := by
  unfold circleIntegral
  rw [← L.intervalIntegral_comp_comm hf.out]
  apply intervalIntegral.integral_congr
  intro θ _
  exact (L.map_smul _ _).symm

end circleIntegral

namespace HasResolventOn

universe u v v'

variable {X : Type u} {D : Type v} {D' : Type v'}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup D'] [NormedSpace ℂ D']
  {A : DomainOperator X D} {B : DomainOperator X D'}

/-- Postcomposition by a fixed operator commutes with a circle integral. -/
theorem circleIntegral_comp_right {f : ℂ → (X →L[ℂ] X)} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (T : X →L[ℂ] X) :
    (∮ z in C(c, R), f z).comp T =
      ∮ z in C(c, R), (f z).comp T := by
  let L : (X →L[ℂ] X) →L[ℂ] (X →L[ℂ] X) :=
    (ContinuousLinearMap.compL ℂ X X X).flip T
  exact (circleIntegral.map L hf).symm

/-- Precomposition by a fixed operator commutes with a circle integral. -/
theorem circleIntegral_comp_left {f : ℂ → (X →L[ℂ] X)} {c : ℂ} {R : ℝ}
    (T : X →L[ℂ] X) (hf : CircleIntegrable f c R) :
    T.comp (∮ z in C(c, R), f z) =
      ∮ z in C(c, R), T.comp (f z) := by
  let L : (X →L[ℂ] X) →L[ℂ] (X →L[ℂ] X) :=
    ContinuousLinearMap.compL ℂ X X X T
  exact (circleIntegral.map L hf).symm

omit [CompleteSpace X] in
/-- Holomorphy on the open annulus makes the normalized contour operator
independent of the chosen radius. -/
theorem rieszProjection_eq_of_differentiableOn_annulus {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (h : HasResolventOn A (closedBall c R \ ball c r))
    (hdiff : ∀ z ∈ ball c R \ closedBall c r,
      DifferentiableAt ℂ h.stateResolvent z) :
    (h.mono (T := sphere c R) (by
      intro z hz
      have hzR : dist z c = R := mem_sphere.mp hz
      constructor
      · exact mem_closedBall.mpr hzR.le
      · exact fun hzr ↦ (not_lt_of_ge hrR) (hzR ▸ mem_ball.mp hzr))).rieszProjection =
    (h.mono (T := sphere c r) (by
      intro z hz
      have hzr : dist z c = r := mem_sphere.mp hz
      constructor
      · exact mem_closedBall.mpr (hzr ▸ hrR)
      · intro hzr'
        have hzlt := mem_ball.mp hzr'
        rw [hzr] at hzlt
        exact (lt_irrefl r) hzlt)).rieszProjection := by
  unfold rieszProjection
  congr 1
  exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR Set.countable_empty (h.continuousOn_stateResolvent) (by
      intro z hz
      exact hdiff z hz.1)

/-- The unnormalized iterated integral of the two resolvent contours. -/
def nestedStateResolventIntegral {c : ℂ} {r R : ℝ}
    (h : HasResolventOn A (sphere c R ∪ sphere c r)) : X →L[ℂ] X :=
  ∮ z in C(c, R), ∮ q in C(c, r),
    (h.stateResolvent z).comp (h.stateResolvent q)

/-- The explicit double-contour exchange needed below, as an equality. -/
def ResolventKernelCircleExchange {c : ℂ} {r R : ℝ}
    (h : HasResolventOn A (sphere c R ∪ sphere c r)) : Prop :=
  (∮ z in C(c, R), ∮ q in C(c, r),
      (q - z)⁻¹ • h.stateResolvent q) =
    ∮ q in C(c, r), ∮ z in C(c, R),
      (q - z)⁻¹ • h.stateResolvent q

/--
For `r < R`, a point of the closed inner disc and a point of the outer circle are distinct, so
the Cauchy kernel `(q - z)⁻¹` is defined throughout the double contour integral.
-/
private theorem ne_of_mem_closedBall_inner_of_mem_sphere_outer
    {c z q : ℂ} {r R : ℝ} (hrR : r < R)
    (hq : q ∈ closedBall c r) (hz : z ∈ sphere c R) : q ≠ z := by
  intro hqz
  subst q
  have hle := mem_closedBall.mp hq
  have heq := mem_sphere.mp hz
  rw [heq] at hle
  exact (not_le_of_gt hrR) hle

/--
For `z` on the outer circle of radius `R`, the Cauchy kernel `q ↦ (q - z)⁻¹` is holomorphic on
the closed inner disc, so its integral over the inner circle vanishes.
-/
private theorem inner_sub_inv_circleIntegral_eq_zero
    {c z : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hz : z ∈ sphere c R) :
    (∮ q in C(c, r), (q - z)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hr.le Set.countable_empty
  · intro q hq
    exact (((differentiableAt_id (𝕜 := ℂ)).sub_const z).inv
      (sub_ne_zero.mpr
        (ne_of_mem_closedBall_inner_of_mem_sphere_outer hrR hq hz))).continuousAt.continuousWithinAt
  · intro q hq
    exact ((differentiableAt_id (𝕜 := ℂ)).sub_const z).inv
      (sub_ne_zero.mpr
        (ne_of_mem_closedBall_inner_of_mem_sphere_outer hrR
          (mem_ball.mp hq.1).le hz))

/-- The same vanishing holds for the kernel multiplied by a constant operator `T`. -/
private theorem inner_constKernel_circleIntegral_eq_zero
    {c z : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hz : z ∈ sphere c R) (T : X →L[ℂ] X) :
    (∮ q in C(c, r), (q - z)⁻¹ • T) = 0 := by
  rw [circleIntegral.integral_smul_const,
    inner_sub_inv_circleIntegral_eq_zero hr hrR hz, zero_smul]

/--
For `q` on the inner circle, integrating `(q - z)⁻¹ • T` over the outer circle gives
`-(2π i) • T`, the residue at the enclosed pole `z = q`.
-/
private theorem outer_kernel_circleIntegral
    {c q : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hq : q ∈ sphere c r) (T : X →L[ℂ] X) :
    (∮ z in C(c, R), (q - z)⁻¹ • T) =
      -(2 * Real.pi * I : ℂ) • T := by
  have hqball : q ∈ ball c R := by
    apply mem_ball.mpr
    rw [mem_sphere.mp hq]
    exact hrR
  rw [circleIntegral.integral_smul_const]
  congr 1
  calc
    (∮ z in C(c, R), (q - z)⁻¹) =
        ∮ z in C(c, R), (-1 : ℂ) • (z - q)⁻¹ := by
      apply circleIntegral.integral_congr (hr.trans hrR).le
      intro z _
      change (q - z)⁻¹ = (-1 : ℂ) • (z - q)⁻¹
      calc
        (q - z)⁻¹ = (-(z - q))⁻¹ := by congr 1; abel
        _ = -(z - q)⁻¹ := inv_neg
        _ = (-1 : ℂ) • (z - q)⁻¹ := by simp
    _ = (-1 : ℂ) • ∮ z in C(c, R), (z - q)⁻¹ := by
      rw [circleIntegral.integral_smul]
    _ = -(2 * Real.pi * I : ℂ) := by
      rw [circleIntegral.integral_sub_inv_of_mem_ball hqball]
      simp

omit [CompleteSpace X] in
/-- For two separated circles the kernel exchange is a direct Bochner-Fubini
consequence of continuity of the chosen resolvent on the two circles. -/
theorem resolventKernelCircleExchange_of_separated
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (h : HasResolventOn A (sphere c R ∪ sphere c r)) :
    h.ResolventKernelCircleExchange := by
  let F : ℝ → ℝ → (X →L[ℂ] X) := fun θ φ ↦
    (circleMap 0 R θ * I) • ((circleMap 0 r φ * I) •
      ((circleMap c r φ - circleMap c R θ)⁻¹ •
        h.stateResolvent (circleMap c r φ)))
  have hinner : Continuous
      (fun φ : ℝ ↦ h.stateResolvent (circleMap c r φ)) :=
    h.continuousOn_stateResolvent.comp_continuous
      (continuous_circleMap c r) (fun φ ↦
        subset_union_right (circleMap_mem_sphere c hr.le φ))
  have hdenom_ne : ∀ p : ℝ × ℝ,
      circleMap c r p.2 - circleMap c R p.1 ≠ 0 := by
    intro p
    apply sub_ne_zero.mpr
    exact ne_of_mem_closedBall_inner_of_mem_sphere_outer hrR
      (mem_closedBall.mpr
        (mem_sphere.mp (circleMap_mem_sphere c hr.le p.2)).le)
      (circleMap_mem_sphere c (hr.trans hrR).le p.1)
  have hdenom : Continuous
      (fun p : ℝ × ℝ ↦
        (circleMap c r p.2 - circleMap c R p.1)⁻¹) :=
    (((continuous_circleMap c r).comp continuous_snd).sub
      ((continuous_circleMap c R).comp continuous_fst)).inv₀ hdenom_ne
  have hF : Continuous (Function.uncurry F) := by
    dsimp only [Function.uncurry, F]
    exact (((continuous_circleMap 0 R).comp continuous_fst).mul_const I).smul
      ((((continuous_circleMap 0 r).comp continuous_snd).mul_const I).smul
        (hdenom.smul (hinner.comp continuous_snd)))
  have hInt : MeasureTheory.IntegrableOn (Function.uncurry F)
      (uIoc 0 (2 * Real.pi) ×ˢ uIoc 0 (2 * Real.pi)) :=
    (ContinuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc) hF.continuousOn).mono_set
        (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap hInt
  unfold ResolventKernelCircleExchange circleIntegral
  simp only [deriv_circleMap]
  calc
    (∫ θ in 0..2 * Real.pi, (circleMap 0 R θ * I) •
        ∫ φ in 0..2 * Real.pi, (circleMap 0 r φ * I) •
          ((circleMap c r φ - circleMap c R θ)⁻¹ •
            h.stateResolvent (circleMap c r φ))) =
        ∫ θ in 0..2 * Real.pi, ∫ φ in 0..2 * Real.pi, F θ φ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact (intervalIntegral.integral_smul _ _).symm
    _ = ∫ φ in 0..2 * Real.pi, ∫ θ in 0..2 * Real.pi, F θ φ := hswap
    _ = ∫ φ in 0..2 * Real.pi, (circleMap 0 r φ * I) •
        ∫ θ in 0..2 * Real.pi, (circleMap 0 R θ * I) •
          ((circleMap c r φ - circleMap c R θ)⁻¹ •
            h.stateResolvent (circleMap c r φ)) := by
      apply intervalIntegral.integral_congr
      intro φ _
      change (∫ θ in 0..2 * Real.pi, F θ φ) =
        (circleMap 0 r φ * I) •
          ∫ θ in 0..2 * Real.pi, (circleMap 0 R θ * I) •
            ((circleMap c r φ - circleMap c R θ)⁻¹ •
              h.stateResolvent (circleMap c r φ))
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [F, smul_smul]
      congr 1
      ring

/-- The resolvent identity and one explicit Fubini exchange evaluate the
nested resolvent integral.  All scalar Cauchy integrals are discharged here. -/
theorem nestedStateResolventIntegral_eq {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (h : HasResolventOn A (sphere c R ∪ sphere c r))
    (hswap : h.ResolventKernelCircleExchange) :
    h.nestedStateResolventIntegral =
      (2 * Real.pi * I : ℂ) •
        ∮ q in C(c, r), h.stateResolvent q := by
  have hR : 0 ≤ R := (hr.trans hrR).le
  have hinnerCont : ContinuousOn h.stateResolvent (sphere c r) :=
    h.continuousOn_stateResolvent.mono subset_union_right
  have hinnerInt : CircleIntegrable h.stateResolvent c r :=
    hinnerCont.circleIntegrable hr.le
  have hkernel :
      h.nestedStateResolventIntegral =
        ∮ z in C(c, R), ∮ q in C(c, r),
          (q - z)⁻¹ • (h.stateResolvent z - h.stateResolvent q) := by
    unfold nestedStateResolventIntegral
    apply circleIntegral.integral_congr hR
    intro z hz
    apply circleIntegral.integral_congr hr.le
    intro q hq
    exact h.stateResolvent_comp_eq_inv_smul_sub
      (subset_union_left hz) (subset_union_right hq)
      (ne_of_mem_closedBall_inner_of_mem_sphere_outer hrR
        (mem_closedBall.mpr (mem_sphere.mp hq).le) hz)
  rw [hkernel]
  have hinnerEval : ∀ z ∈ sphere c R,
      (∮ q in C(c, r),
        (q - z)⁻¹ • (h.stateResolvent z - h.stateResolvent q)) =
      -(∮ q in C(c, r), (q - z)⁻¹ • h.stateResolvent q) := by
    intro z hz
    have hscalar : ContinuousOn (fun q : ℂ ↦ (q - z)⁻¹) (sphere c r) := by
      intro q hq
      exact (((differentiableAt_id (𝕜 := ℂ)).sub_const z).inv
        (sub_ne_zero.mpr
          (ne_of_mem_closedBall_inner_of_mem_sphere_outer hrR
            (mem_closedBall.mpr (mem_sphere.mp hq).le) hz))).continuousAt.continuousWithinAt
    have hconstInt : CircleIntegrable
        (fun q : ℂ ↦ (q - z)⁻¹ • h.stateResolvent z) c r :=
      (hscalar.smul continuousOn_const).circleIntegrable hr.le
    have hresInt : CircleIntegrable
        (fun q : ℂ ↦ (q - z)⁻¹ • h.stateResolvent q) c r :=
      (hscalar.smul hinnerCont).circleIntegrable hr.le
    rw [show (fun q : ℂ ↦
        (q - z)⁻¹ • (h.stateResolvent z - h.stateResolvent q)) =
        fun q ↦ (q - z)⁻¹ • h.stateResolvent z -
          (q - z)⁻¹ • h.stateResolvent q by
      funext q
      exact smul_sub _ _ _,
      circleIntegral.integral_sub hconstInt hresInt,
      inner_constKernel_circleIntegral_eq_zero hr hrR hz,
      zero_sub]
  calc
    (∮ z in C(c, R), ∮ q in C(c, r),
        (q - z)⁻¹ • (h.stateResolvent z - h.stateResolvent q)) =
        ∮ z in C(c, R),
          -(∮ q in C(c, r), (q - z)⁻¹ • h.stateResolvent q) := by
      apply circleIntegral.integral_congr hR hinnerEval
    _ = -(∮ z in C(c, R), ∮ q in C(c, r),
          (q - z)⁻¹ • h.stateResolvent q) := by
      calc
        (∮ z in C(c, R),
            -(∮ q in C(c, r), (q - z)⁻¹ • h.stateResolvent q)) =
            ∮ z in C(c, R), (-1 : ℂ) •
              (∮ q in C(c, r), (q - z)⁻¹ • h.stateResolvent q) := by
          apply circleIntegral.integral_congr hR
          intro z _
          simp
        _ = (-1 : ℂ) • (∮ z in C(c, R), ∮ q in C(c, r),
              (q - z)⁻¹ • h.stateResolvent q) := by
          rw [circleIntegral.integral_smul]
        _ = -(∮ z in C(c, R), ∮ q in C(c, r),
              (q - z)⁻¹ • h.stateResolvent q) := by simp
    _ = -(∮ q in C(c, r), ∮ z in C(c, R),
          (q - z)⁻¹ • h.stateResolvent q) := congrArg Neg.neg hswap
    _ = -(∮ q in C(c, r),
          -(2 * Real.pi * I : ℂ) • h.stateResolvent q) := by
      congr 1
      apply circleIntegral.integral_congr hr.le
      intro q hq
      exact outer_kernel_circleIntegral hr hrR hq _
    _ = (2 * Real.pi * I : ℂ) •
          ∮ q in C(c, r), h.stateResolvent q := by
      rw [circleIntegral.integral_smul]
      module

/-- The normalized operators on two nested circles satisfy the mixed
projection identity once the explicit kernel exchange is available. -/
theorem rieszProjection_outer_comp_inner {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (h : HasResolventOn A (sphere c R ∪ sphere c r))
    (hswap : h.ResolventKernelCircleExchange) :
    (h.mono (T := sphere c R) subset_union_left).rieszProjection.comp
      (h.mono (T := sphere c r) subset_union_right).rieszProjection =
    (h.mono (T := sphere c r) subset_union_right).rieszProjection := by
  let α : ℂ := 2 * Real.pi * I
  let Iouter : X →L[ℂ] X :=
    ∮ z in C(c, R), h.stateResolvent z
  let Iinner : X →L[ℂ] X :=
    ∮ q in C(c, r), h.stateResolvent q
  have houterInt : CircleIntegrable h.stateResolvent c R :=
    (h.continuousOn_stateResolvent.mono subset_union_left).circleIntegrable
      (hr.trans hrR).le
  have hinnerInt : CircleIntegrable h.stateResolvent c r :=
    (h.continuousOn_stateResolvent.mono subset_union_right).circleIntegrable hr.le
  have hproduct : Iouter.comp Iinner = h.nestedStateResolventIntegral := by
    rw [show Iouter = ∮ z in C(c, R), h.stateResolvent z from rfl,
      show Iinner = ∮ q in C(c, r), h.stateResolvent q from rfl,
      circleIntegral_comp_right houterInt]
    unfold nestedStateResolventIntegral
    apply circleIntegral.integral_congr (hr.trans hrR).le
    intro z _
    exact circleIntegral_comp_left (h.stateResolvent z) hinnerInt
  have hnested : h.nestedStateResolventIntegral = α • Iinner := by
    simpa [α, Iinner] using h.nestedStateResolventIntegral_eq hr hrR hswap
  change (α⁻¹ • Iouter).comp (α⁻¹ • Iinner) = α⁻¹ • Iinner
  calc
    (α⁻¹ • Iouter).comp (α⁻¹ • Iinner) =
        (α⁻¹ * α⁻¹) • Iouter.comp Iinner := by
      ext x
      simp [smul_smul]
    _ = (α⁻¹ * α⁻¹) • (α • Iinner) := by rw [hproduct, hnested]
    _ = α⁻¹ • Iinner := by
      have hα : α ≠ 0 := by simp [α, Real.pi_ne_zero]
      rw [smul_smul]
      congr 1
      field_simp

/-- If the inner and outer contour operators agree, the mixed identity makes
their common value idempotent. -/
theorem rieszProjection_isIdempotentElem_of_nested_circles_and_exchange
    {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (h : HasResolventOn A (sphere c R ∪ sphere c r))
    (hswap : h.ResolventKernelCircleExchange)
    (heq : (h.mono (T := sphere c R) subset_union_left).rieszProjection =
      (h.mono (T := sphere c r) subset_union_right).rieszProjection) :
    IsIdempotentElem
      (h.mono (T := sphere c r) subset_union_right).rieszProjection := by
  have hmixed := h.rieszProjection_outer_comp_inner hr hrR hswap
  rw [heq] at hmixed
  simpa only [IsIdempotentElem, ContinuousLinearMap.mul_def] using hmixed

/-- Equality of the contour operators on two separated nested circles is
enough for idempotence.  The required double-integral exchange is discharged
by `resolventKernelCircleExchange_of_separated`. -/
theorem rieszProjection_isIdempotentElem_of_equal_nested_contours
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (h : HasResolventOn A (sphere c R ∪ sphere c r))
    (heq : (h.mono (T := sphere c R) subset_union_left).rieszProjection =
      (h.mono (T := sphere c r) subset_union_right).rieszProjection) :
    IsIdempotentElem
      (h.mono (T := sphere c r) subset_union_right).rieszProjection :=
  h.rieszProjection_isIdempotentElem_of_nested_circles_and_exchange
    hr hrR (h.resolventKernelCircleExchange_of_separated hr hrR) heq

/--
For `r ≤ R` the union of the two spectral circles lies in the closed annulus
`closedBall c R \ ball c r`, so an annular resolver restricts to both contours.
-/
private theorem spectralCircles_subset_closedAnnulus
    {c : ℂ} {r R : ℝ} (hrR : r ≤ R) :
    sphere c R ∪ sphere c r ⊆ closedBall c R \ ball c r := by
  intro z hz
  rcases hz with hz | hz
  · have hzR := mem_sphere.mp hz
    exact ⟨mem_closedBall.mpr hzR.le,
      fun hzr ↦ (not_lt_of_ge hrR) (hzR ▸ mem_ball.mp hzr)⟩
  · have hzr := mem_sphere.mp hz
    refine ⟨mem_closedBall.mpr (hzr ▸ hrR), ?_⟩
    intro hzball
    have hzlt := mem_ball.mp hzball
    rw [hzr] at hzlt
    exact (lt_irrefl r) hzlt

/-- Annular differentiability gives equality of the two contours; the proved
separated-circle kernel exchange then yields an idempotent normalized contour
operator. -/
theorem rieszProjection_isIdempotentElem_of_differentiableOn_annulus
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (h : HasResolventOn A (closedBall c R \ ball c r))
    (hdiff : ∀ z ∈ ball c R \ closedBall c r,
      DifferentiableAt ℂ h.stateResolvent z) :
    IsIdempotentElem
      (h.mono (T := sphere c r) (by
        exact subset_trans subset_union_right
          (spectralCircles_subset_closedAnnulus hrR.le))).rieszProjection := by
  let hU := h.mono (T := sphere c R ∪ sphere c r)
    (spectralCircles_subset_closedAnnulus hrR.le)
  have heq :
      (hU.mono (T := sphere c R) subset_union_left).rieszProjection =
      (hU.mono (T := sphere c r) subset_union_right).rieszProjection := by
    simpa [hU, mono, rieszProjection, stateResolvent] using
      h.rieszProjection_eq_of_differentiableOn_annulus hr hrR.le hdiff
  have hidem := hU.rieszProjection_isIdempotentElem_of_equal_nested_contours
    hr hrR heq
  simpa [hU, mono, rieszProjection, stateResolvent] using hidem

omit [CompleteSpace X] in
/-- On a common open resolvent neighbourhood containing the closed annulus,
the normalized contour operators on its two boundary circles agree. -/
theorem rieszProjection_eq_of_isOpen_common_resolvent
    {U : Set ℂ} {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (h : HasResolventOn A U) (hU : IsOpen U)
    (hann : closedBall c R \ ball c r ⊆ U) :
    (h.mono (T := sphere c R) (by
      exact subset_trans subset_union_left
        (subset_trans (spectralCircles_subset_closedAnnulus hrR.le) hann))).rieszProjection =
    (h.mono (T := sphere c r) (by
      exact subset_trans subset_union_right
        (subset_trans (spectralCircles_subset_closedAnnulus hrR.le) hann))).rieszProjection := by
  let hAnn := h.mono (T := closedBall c R \ ball c r) hann
  have hdiff : ∀ z ∈ ball c R \ closedBall c r,
      DifferentiableAt ℂ hAnn.stateResolvent z := by
    intro z hz
    have hzAnn : z ∈ closedBall c R \ ball c r := by
      refine ⟨mem_closedBall.mpr (mem_ball.mp hz.1).le, ?_⟩
      intro hzr
      exact hz.2 (mem_closedBall.mpr (mem_ball.mp hzr).le)
    exact (h.stateResolvent_hasDerivAt hU (hann hzAnn)).differentiableAt
  simpa [hAnn, mono, rieszProjection, stateResolvent] using
    hAnn.rieszProjection_eq_of_differentiableOn_annulus hr hrR.le hdiff

/-- A common open resolvent neighbourhood containing a closed annulus gives
an idempotent normalized contour operator on the inner boundary circle.  The
resolvent identity supplies holomorphy and Bochner--Fubini supplies the
double-contour exchange. -/
theorem rieszProjection_isIdempotentElem_of_isOpen_common_resolvent
    {U : Set ℂ} {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (h : HasResolventOn A U) (hU : IsOpen U)
    (hann : closedBall c R \ ball c r ⊆ U) :
    IsIdempotentElem
      (h.mono (T := sphere c r) (by
        exact subset_trans subset_union_right
          (subset_trans (spectralCircles_subset_closedAnnulus hrR.le) hann))).rieszProjection := by
  let hAnn := h.mono (T := closedBall c R \ ball c r) hann
  have hdiff : ∀ z ∈ ball c R \ closedBall c r,
      DifferentiableAt ℂ hAnn.stateResolvent z := by
    intro z hz
    have hzAnn : z ∈ closedBall c R \ ball c r := by
      refine ⟨mem_closedBall.mpr (mem_ball.mp hz.1).le, ?_⟩
      intro hzr
      exact hz.2 (mem_closedBall.mpr (mem_ball.mp hzr).le)
    exact (h.stateResolvent_hasDerivAt hU (hann hzAnn)).differentiableAt
  have hidem := hAnn.rieszProjection_isIdempotentElem_of_differentiableOn_annulus
    hr hrR hdiff
  simpa [hAnn, mono, rieszProjection, stateResolvent] using hidem

/-- The outer boundary contour operator in the same common-open-set setting
is idempotent as well. -/
theorem rieszProjection_outer_isIdempotentElem_of_isOpen_common_resolvent
    {U : Set ℂ} {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (h : HasResolventOn A U) (hU : IsOpen U)
    (hann : closedBall c R \ ball c r ⊆ U) :
    IsIdempotentElem
      (h.mono (T := sphere c R) (by
        exact subset_trans subset_union_left
          (subset_trans (spectralCircles_subset_closedAnnulus hrR.le) hann))).rieszProjection := by
  rw [h.rieszProjection_eq_of_isOpen_common_resolvent hr hrR hU hann]
  exact h.rieszProjection_isIdempotentElem_of_isOpen_common_resolvent
    hr hrR hU hann

end HasResolventOn

end

end FastDynamo
