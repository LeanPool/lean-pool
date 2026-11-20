/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.Riesz

/-!
# The resolvent identity for bundled-domain operators

The chosen inverse in `HasResolventOn` takes ambient states into the bundled
operator domain.  Its two inverse equations already imply the usual
two-parameter resolvent identity; no additional compatibility assumption
between the chosen inverses at different spectral parameters is needed.

The first theorem below retains the stronger ambient-to-domain codomain.  The
second applies the domain embedding and gives the ambient operator identity
used in the Riesz-projection calculus.
-/

@[expose] public section

namespace FastDynamo

namespace DomainOperator

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- The affine operator pencils at two parameters differ only in their
domain embedding term. -/
theorem pencil_sub_pencil (A : DomainOperator X D) (w z : ℂ) :
    A.pencil w - A.pencil z = (w - z) • A.embedding := by
  apply ContinuousLinearMap.ext
  intro d
  simp only [pencil, sub_apply, smul_apply]
  rw [sub_smul]
  module

end DomainOperator

namespace HasResolventOn

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D} {S : Set ℂ}

/-- Domain-valued resolvent identity.  This is stronger than the usual
ambient identity because its two sides map `X` continuously into `D`. -/
theorem inv_sub_inv (h : HasResolventOn A S) {z w : ℂ}
    (hz : z ∈ S) (hw : w ∈ S) :
    h.inv z - h.inv w =
      (w - z) • (h.inv z).comp (h.stateResolvent w) := by
  apply ContinuousLinearMap.ext
  intro x
  change h.inv z x - h.inv w x =
    (w - z) • h.inv z (A.embedding (h.inv w x))
  have hright : A.pencil w (h.inv w x) = x := by
    have hx := congrArg (fun T : X →L[ℂ] X ↦ T x) (h.right_inv w hw)
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hx
  have hleft : h.inv z (A.pencil z (h.inv w x)) = h.inv w x := by
    have hx := congrArg (fun T : D →L[ℂ] D ↦ T (h.inv w x))
      (h.left_inv z hz)
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hx
  calc
    h.inv z x - h.inv w x =
        h.inv z (A.pencil w (h.inv w x)) -
          h.inv z (A.pencil z (h.inv w x)) := by
      rw [hright, hleft]
    _ = h.inv z
          ((A.pencil w - A.pencil z) (h.inv w x)) := by
      simp only [sub_apply, map_sub]
    _ = h.inv z ((w - z) • A.embedding (h.inv w x)) := by
      rw [DomainOperator.pencil_sub_pencil]
      rfl
    _ = (w - z) • h.inv z (A.embedding (h.inv w x)) := by
      rw [map_smul]

/-- Ambient-space resolvent identity in the sign convention of the pencil
`z - A`: `R(z) - R(w) = (w - z) R(z) R(w)`. -/
theorem stateResolvent_sub_stateResolvent
    (h : HasResolventOn A S) {z w : ℂ}
    (hz : z ∈ S) (hw : w ∈ S) :
    h.stateResolvent z - h.stateResolvent w =
      (w - z) • (h.stateResolvent z).comp (h.stateResolvent w) := by
  apply ContinuousLinearMap.ext
  intro x
  have hdomain := congrArg (fun T : X →L[ℂ] D ↦ T x)
    (inv_sub_inv h hz hw)
  change A.embedding (h.inv z x) - A.embedding (h.inv w x) =
    (w - z) •
      A.embedding (h.inv z (A.embedding (h.inv w x)))
  simpa only [HasResolventOn.stateResolvent, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_sub, map_smul] using
      congrArg A.embedding hdomain

end HasResolventOn

end FastDynamo
