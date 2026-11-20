/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.Riesz

/-!
# Domain-valued Riesz calculus

The ambient Riesz projection is obtained by composing the chosen
domain-valued resolvent with the operator-domain embedding.  When the bundled
domain is complete, the resolvent itself can also be integrated around the
contour.  This file records that stronger contour operator and proves that it
is a lift of the ambient Riesz projection into the operator domain for
a nonnegative contour radius.

The same lift also identifies the action of the unbounded operator on the
Riesz range with the first resolvent moment.  Thus every vector in the
algebraic range of the ambient Riesz projection has a canonical representative
in the bundled domain; no closed-operator or semigroup API is needed.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex Metric Set

/-- Circle integration commutes with a continuous complex-linear map.  This
local bridge keeps the domain-valued calculus independent of the later
idempotence and rank-stability layer. -/
private theorem circleIntegral_map
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    circleIntegral (fun z ↦ L (f z)) c R =
      L (circleIntegral f c R) := by
  unfold circleIntegral
  rw [← L.intervalIntegral_comp_comm hf.out]
  apply intervalIntegral.integral_congr
  intro θ _hθ
  exact (L.map_smul _ _).symm

namespace HasResolventOn

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  {A : DomainOperator X D} {c : ℂ} {R : ℝ}

/-- The normalized contour integral of the domain-valued resolvent.

For a nonnegative radius, applying the domain embedding gives the ordinary
ambient Riesz projection. -/
def domainRieszProjection
    (h : HasResolventOn A (sphere c R)) : X →L[ℂ] D :=
  (2 * Real.pi * I : ℂ)⁻¹ • circleIntegral h.inv c R

/-- The first normalized moment of the ambient resolvent.  For a nonnegative
radius, this is the action of `A` on the canonical domain-valued lift of the
Riesz projection. -/
def rieszSpectralMoment
    (h : HasResolventOn A (sphere c R)) : X →L[ℂ] X :=
  (2 * Real.pi * I : ℂ)⁻¹ •
    circleIntegral (fun z ↦ z • h.stateResolvent z) c R

/-- Applying the domain embedding to the domain-valued contour integral gives
the ambient Riesz projection. -/
theorem embedding_comp_domainRieszProjection
    (h : HasResolventOn A (sphere c R)) (hR : 0 ≤ R) :
    A.embedding.comp h.domainRieszProjection = h.rieszProjection := by
  let L : (X →L[ℂ] D) →L[ℂ] (X →L[ℂ] X) :=
    ContinuousLinearMap.compL ℂ X D X A.embedding
  have hinv : CircleIntegrable h.inv c R :=
    h.continuousOn.circleIntegrable hR
  have hmap := circleIntegral_map L hinv
  unfold domainRieszProjection rieszProjection
  change L ((2 * Real.pi * I : ℂ)⁻¹ • circleIntegral h.inv c R) =
    (2 * Real.pi * I : ℂ)⁻¹ •
      circleIntegral h.stateResolvent c R
  rw [L.map_smul]
  congr 1
  change L (circleIntegral h.inv c R) =
    circleIntegral h.stateResolvent c R
  rw [← hmap]
  rfl

/-- Pointwise form of `embedding_comp_domainRieszProjection`. -/
theorem embedding_domainRieszProjection_apply
    (h : HasResolventOn A (sphere c R)) (hR : 0 ≤ R) (x : X) :
    A.embedding (h.domainRieszProjection x) = h.rieszProjection x := by
  exact DFunLike.congr_fun (h.embedding_comp_domainRieszProjection hR) x

omit [CompleteSpace X] [CompleteSpace D] in
/-- At a resolvent point, applying the operator after the domain-valued
inverse gives `z R(z) - 1`. -/
theorem op_comp_inv_eq
    (h : HasResolventOn A (sphere c R)) {z : ℂ} (hz : z ∈ sphere c R) :
    A.op.comp (h.inv z) =
      z • h.stateResolvent z - ContinuousLinearMap.id ℂ X := by
  apply ContinuousLinearMap.ext
  intro x
  have hright := congrArg (fun T : X →L[ℂ] X ↦ T x) (h.right_inv z hz)
  simp only [DomainOperator.pencil, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, sub_apply, smul_apply,
    stateResolvent] at hright ⊢
  apply (eq_sub_iff_add_eq).2
  rw [add_comm]
  exact (sub_eq_iff_eq_add.mp hright).symm

/--
The contour integral of a constant operator-valued function around a circle vanishes, since the
integral of `(z - c)^0` over a circle centered at `c` is zero.
-/
private theorem circleIntegral_const_id_eq_zero (hR : 0 ≤ R) :
    circleIntegral (fun _z : ℂ ↦ ContinuousLinearMap.id ℂ X) c R = 0 := by
  have hone : circleIntegral (fun z : ℂ ↦ (z - c) ^ (0 : ℤ)) c R = 0 :=
    circleIntegral.integral_sub_zpow_of_ne (by norm_num) c c R
  calc
    circleIntegral (fun _z : ℂ ↦ ContinuousLinearMap.id ℂ X) c R =
        circleIntegral
          (fun z : ℂ ↦ (z - c) ^ (0 : ℤ) •
            ContinuousLinearMap.id ℂ X) c R := by
      apply circleIntegral.integral_congr hR
      intro z _hz
      simp
    _ = circleIntegral (fun z : ℂ ↦ (z - c) ^ (0 : ℤ)) c R •
          ContinuousLinearMap.id ℂ X := by
      rw [circleIntegral.integral_smul_const]
    _ = 0 := by rw [hone, zero_smul]

/-- The unbounded operator applied to the domain-valued Riesz lift is exactly
the first normalized resolvent moment. -/
theorem op_comp_domainRieszProjection
    (h : HasResolventOn A (sphere c R)) (hR : 0 ≤ R) :
    A.op.comp h.domainRieszProjection = h.rieszSpectralMoment := by
  let L : (X →L[ℂ] D) →L[ℂ] (X →L[ℂ] X) :=
    ContinuousLinearMap.compL ℂ X D X A.op
  have hinv : CircleIntegrable h.inv c R :=
    h.continuousOn.circleIntegrable hR
  have hmap := circleIntegral_map L hinv
  have hmomentCont : ContinuousOn
      (fun z ↦ z • h.stateResolvent z) (sphere c R) := by
    exact continuousOn_id.smul h.continuousOn_stateResolvent
  have hmomentInt : CircleIntegrable
      (fun z ↦ z • h.stateResolvent z) c R :=
    hmomentCont.circleIntegrable hR
  have hconstInt : CircleIntegrable
      (fun _z : ℂ ↦ ContinuousLinearMap.id ℂ X) c R :=
    continuousOn_const.circleIntegrable hR
  have hintegral :
      circleIntegral (fun z ↦ A.op.comp (h.inv z)) c R =
        circleIntegral (fun z ↦ z • h.stateResolvent z) c R := by
    calc
      circleIntegral (fun z ↦ A.op.comp (h.inv z)) c R =
          circleIntegral (fun z ↦
            z • h.stateResolvent z - ContinuousLinearMap.id ℂ X) c R := by
        apply circleIntegral.integral_congr hR
        intro z hz
        exact h.op_comp_inv_eq hz
      _ = circleIntegral (fun z ↦ z • h.stateResolvent z) c R -
          circleIntegral
            (fun _z : ℂ ↦ ContinuousLinearMap.id ℂ X) c R := by
        rw [circleIntegral.integral_sub hmomentInt hconstInt]
      _ = circleIntegral (fun z ↦ z • h.stateResolvent z) c R := by
        rw [circleIntegral_const_id_eq_zero hR, sub_zero]
  unfold domainRieszProjection rieszSpectralMoment
  change L ((2 * Real.pi * I : ℂ)⁻¹ • circleIntegral h.inv c R) =
    (2 * Real.pi * I : ℂ)⁻¹ •
      circleIntegral (fun z ↦ z • h.stateResolvent z) c R
  rw [L.map_smul]
  congr 1
  change L (circleIntegral h.inv c R) =
    circleIntegral (fun z ↦ z • h.stateResolvent z) c R
  rw [← hmap]
  simpa only [L, ContinuousLinearMap.compL_apply] using hintegral

end HasResolventOn

end

end FastDynamo
