/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.Domain
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Riesz projections for operators with a bundled domain

The local and global spectral arguments use resolvents as bounded maps from
the ambient `L²` space into the `H²` domain.  This module defines the associated
operator-valued contour integral without replacing that stronger resolvent by
an ambient-space inverse.

Idempotence and spectral-subspace theorems require the resolvent identity and
holomorphy on a neighbourhood of the contour.  They are not asserted here; the idempotence
calculus is developed in `FastDynamo/Operator/RieszProjectionCalculus.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex

namespace HasResolventOn

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D} {S : Set ℂ}
variable {c : ℂ} {R : ℝ}

/-- Composition with the domain embedding, as a bounded map between operator
spaces. -/
def stateResolventMap (A : DomainOperator X D) :
    (X →L[ℂ] D) →L[ℂ] (X →L[ℂ] X) :=
  ContinuousLinearMap.compL ℂ X D X A.embedding

omit [CompleteSpace X] in
/--
`stateResolventMap A` post-composes a domain-valued operator with the domain embedding, turning
the `D`-valued resolvent into an ambient `X`-valued one.
-/
@[simp] theorem stateResolventMap_apply
    (A : DomainOperator X D) (T : X →L[ℂ] D) :
    stateResolventMap A T = A.embedding.comp T := by
  rw [stateResolventMap, ContinuousLinearMap.compL_apply]

omit [CompleteSpace X] in
/-- Continuity of the ambient-space resolvent on every set on which the
chosen domain-valued resolvent is continuous. -/
theorem continuousOn_stateResolvent (h : HasResolventOn A S) :
    ContinuousOn h.stateResolvent S := by
  change ContinuousOn (fun z ↦ stateResolventMap A (h.inv z)) S
  exact (stateResolventMap A).continuous.comp_continuousOn' h.continuousOn

omit [CompleteSpace X] in
/-- The operator-valued resolvent is integrable around a spectral circle when
the chosen resolvent is continuous on that circle. -/
theorem circleIntegrable_stateResolvent
    (h : HasResolventOn A (Metric.sphere c R)) (hR : 0 ≤ R) :
    CircleIntegrable h.stateResolvent c R :=
  (continuousOn_stateResolvent h).circleIntegrable hR

/-- The Riesz contour operator associated with a chosen resolvent on a circle.

The normalization is the paper's `(2π i)⁻¹`.  This definition is meaningful
for the bundled domain resolvent because `stateResolvent` first embeds its
`D`-valued output into the ambient space. -/
def rieszProjection (h : HasResolventOn A (Metric.sphere c R)) : X →L[ℂ] X :=
  (2 * Real.pi * I : ℂ)⁻¹ •
    circleIntegral h.stateResolvent c R

end HasResolventOn

end

end FastDynamo
