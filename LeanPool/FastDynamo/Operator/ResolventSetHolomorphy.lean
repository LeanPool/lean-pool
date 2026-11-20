/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.PointwiseResolvent
public import LeanPool.FastDynamo.Operator.DomainPencilFredholm
public import Mathlib.Analysis.Analytic.Constructions

/-!
# The resolvent is analytic on the resolvent set

For a bundled-domain operator `A : D → X` with complete ambient space `X`, the
domain-valued resolvent `z ↦ (z - A)⁻¹ : X → D` is analytic on the intrinsic
resolvent set `A.resolventSet`, which is open (`DomainOperator.isOpen_resolventSet`).

Near a resolvent point `z₁` with inverse `T₁`, the resolvent coincides with the
propagated inverse `T₁ (1 + (z - z₁) j T₁)⁻¹` of `Operator/ResolventPropagation.lean`,
the composite of a bounded linear map, the inversion of the Banach algebra `L(X)` (analytic
on its units) and an affine function of `z`: this is the Neumann-series argument.  The
result is bundled as a `HasResolventOn` witness on the whole resolvent set
(`DomainOperator.resolventSetResolvent`) whose inverse family is analytic
(`DomainOperator.analyticOnNhd_resolventSetResolvent_inv`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Topology

namespace DomainOperator

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

omit [CompleteSpace X] in
/-- Near a resolvent point the inverse of the pencil is the propagated inverse from that
point. -/
theorem inverse_pencil_eq_propagatedInverse (A : DomainOperator X D) {z₁ z : ℂ}
    (hz₁ : z₁ ∈ A.resolventSet) (hz : z ∈ A.resolventSet) :
    (A.pencil z).inverse =
      propagatedInverse (A.pencil z₁).inverse A.embedding z₁ z := by
  have h₁ : (A.pencil z₁).IsInvertible := hz₁
  have h : (A.pencil z).IsInvertible := hz
  have hunit := resolventCorrection_isUnit_of_pointwise_twoSidedInverse A z₁ z
    (A.pencil z₁).inverse (A.pencil z).inverse h₁.inverse_comp_self h₁.self_comp_inverse
    h.inverse_comp_self h.self_comp_inverse
  have hleft := propagatedInverse_left_inv A z₁ z (A.pencil z₁).inverse
    h₁.inverse_comp_self h₁.self_comp_inverse hunit
  calc (A.pencil z).inverse
      = ((propagatedInverse (A.pencil z₁).inverse A.embedding z₁ z).comp (A.pencil z)).comp
          (A.pencil z).inverse := by rw [hleft, ContinuousLinearMap.id_comp]
    _ = propagatedInverse (A.pencil z₁).inverse A.embedding z₁ z := by
      rw [ContinuousLinearMap.comp_assoc, h.self_comp_inverse, ContinuousLinearMap.comp_id]

variable [CompleteSpace D]

/-- **The resolvent is analytic on the resolvent set**: `z ↦ (z - A)⁻¹ : X → D` is analytic,
in operator norm, at every point of the (open) resolvent set. -/
theorem analyticOnNhd_inverse_pencil (A : DomainOperator X D) :
    AnalyticOnNhd ℂ (fun z => (A.pencil z).inverse) A.resolventSet := by
  intro z₁ hz₁
  have h₁ : (A.pencil z₁).IsInvertible := hz₁
  let T₁ : X →L[ℂ] D := (A.pencil z₁).inverse
  let M : X →L[ℂ] X := A.embedding.comp T₁
  have hC : AnalyticAt ℂ (resolventCorrection M z₁) z₁ := by
    unfold resolventCorrection
    exact analyticAt_const.add ((analyticAt_id.sub analyticAt_const).smul analyticAt_const)
  have hunit : IsUnit (resolventCorrection M z₁ z₁) :=
    resolventCorrection_isUnit_of_pointwise_twoSidedInverse A z₁ z₁ T₁ T₁
      h₁.inverse_comp_self h₁.self_comp_inverse h₁.inverse_comp_self h₁.self_comp_inverse
  have hinv : AnalyticAt ℂ (fun w => Ring.inverse (resolventCorrection M z₁ w)) z₁ := by
    have h := analyticAt_inverse (𝕜 := ℂ) hunit.unit
    rw [hunit.unit_spec] at h
    exact h.comp hC
  have hprop : AnalyticAt ℂ (propagatedInverse T₁ A.embedding z₁) z₁ :=
    (ContinuousLinearMap.compL ℂ X X D T₁).analyticAt _ |>.comp hinv
  refine hprop.congr ?_
  filter_upwards [A.isOpen_resolventSet.mem_nhds hz₁] with z hz
  exact (A.inverse_pencil_eq_propagatedInverse hz₁ hz).symm

/-- The resolvent on the whole resolvent set, `R(z) = (z - A)⁻¹ : X → D`. -/
def resolventSetResolvent (A : DomainOperator X D) : HasResolventOn A A.resolventSet where
  inv z := (A.pencil z).inverse
  left_inv _ hz := ContinuousLinearMap.IsInvertible.inverse_comp_self hz
  right_inv _ hz := ContinuousLinearMap.IsInvertible.self_comp_inverse hz
  continuousOn := A.analyticOnNhd_inverse_pencil.continuousOn

/-- The inverse family of `resolventSetResolvent` is analytic on the resolvent set. -/
theorem analyticOnNhd_resolventSetResolvent_inv (A : DomainOperator X D) :
    AnalyticOnNhd ℂ A.resolventSetResolvent.inv A.resolventSet :=
  A.analyticOnNhd_inverse_pencil

end DomainOperator

end

end FastDynamo
