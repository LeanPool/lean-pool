/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.FormCoercivityConstants
public import LeanPool.FastDynamo.Operator.RieszResolventIdentity

/-!
# Propagating a resolvent from one point

For a bundled-domain operator, an inverse `T₀ : X → D` of the pencil at
`z₀` gives an inverse at `z` as soon as

`1 + (z-z₀) (j ∘ T₀)`

is invertible on the ambient Banach space.  This file carries out that
Neumann argument without discarding the domain-valued inverse.  In
particular, the propagated inverse satisfies both pencil inverse equations,
and on any set where all ambient corrections are units it gives a resolvent
(`hasResolventOnOfIsUnitResolventCorrection`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Set

universe u v

namespace DomainOperator

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- The ambient correction which transports an inverse at `z₀` to `z`. -/
def resolventCorrection (R₀ : X →L[ℂ] X) (z₀ z : ℂ) : X →L[ℂ] X :=
  ContinuousLinearMap.id ℂ X + (z - z₀) • R₀

omit [CompleteSpace X] in
/-- The ambient correction `1 + (z - z₀) R₀` depends continuously (indeed affinely) on `z`. -/
theorem continuous_resolventCorrection (R₀ : X →L[ℂ] X) (z₀ : ℂ) :
    Continuous (resolventCorrection R₀ z₀) := by
  unfold resolventCorrection
  fun_prop

/-- The canonical transported ambient-to-domain inverse.  `Ring.inverse`
is used so that this is a total function of `z`; on the open set where the
correction is a unit, it is the inverse. -/
def propagatedInverse (T₀ : X →L[ℂ] D) (j : D →L[ℂ] X)
    (z₀ z : ℂ) : X →L[ℂ] D :=
  T₀.comp (Ring.inverse (resolventCorrection (j.comp T₀) z₀ z))

omit [CompleteSpace X] in
/--
Composing the pencil at `z` with a right inverse at `z₀` yields exactly the ambient correction
`1 + (z - z₀) (j ∘ T₀)`; this is the identity that drives the whole Neumann transport.
-/
theorem pencil_comp_baseInverse
    (A : DomainOperator X D) (z₀ z : ℂ) (T₀ : X →L[ℂ] D)
    (hright : (A.pencil z₀).comp T₀ = ContinuousLinearMap.id ℂ X) :
    (A.pencil z).comp T₀ =
      resolventCorrection (A.embedding.comp T₀) z₀ z := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T : X →L[ℂ] X ↦ T x) hright
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hx ⊢
  have hp := congrArg (fun T : D →L[ℂ] X ↦ T (T₀ x))
    (pencil_sub_pencil A z z₀)
  simp only [sub_apply, smul_apply] at hp
  simp only [resolventCorrection, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  calc
    A.pencil z (T₀ x) =
        (z - z₀) • A.embedding (T₀ x) + A.pencil z₀ (T₀ x) :=
      eq_add_of_sub_eq hp
    _ = A.pencil z₀ (T₀ x) +
        (z - z₀) • A.embedding (T₀ x) := add_comm _ _
    _ = x + (z - z₀) • A.embedding (T₀ x) := by rw [hx]

omit [CompleteSpace X] in
/--
On the image of the domain embedding, the ambient correction is computed by the left inverse at
`z₀` applied to the pencil at `z`: `C (j d) = j (T₀ (A.pencil z d))`.
-/
theorem resolventCorrection_embedding_apply
    (A : DomainOperator X D) (z₀ z : ℂ) (T₀ : X →L[ℂ] D)
    (hleft : T₀.comp (A.pencil z₀) = ContinuousLinearMap.id ℂ D)
    (d : D) :
    resolventCorrection (A.embedding.comp T₀) z₀ z (A.embedding d) =
      A.embedding (T₀ (A.pencil z d)) := by
  have hd := congrArg (fun T : D →L[ℂ] D ↦ T d) hleft
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hd
  have hp := congrArg (fun T : D →L[ℂ] X ↦ T d)
    (pencil_sub_pencil A z z₀)
  simp only [sub_apply, smul_apply] at hp
  have hp' : A.pencil z d =
      A.pencil z₀ d + (z - z₀) • A.embedding d :=
    (eq_add_of_sub_eq hp).trans (add_comm _ _)
  simp only [resolventCorrection, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [hp', map_add, map_smul, hd, map_add, map_smul]

omit [CompleteSpace X] in
/-- If the ambient correction is a unit, the transported pencil is
injective.  The proof uses the left inverse at `z₀` and injectivity of the
domain embedding. -/
theorem pencil_injective_of_isUnit_resolventCorrection
    (A : DomainOperator X D) (z₀ z : ℂ) (T₀ : X →L[ℂ] D)
    (hleft : T₀.comp (A.pencil z₀) = ContinuousLinearMap.id ℂ D)
    (hunit : IsUnit (resolventCorrection (A.embedding.comp T₀) z₀ z)) :
    Function.Injective (A.pencil z) := by
  intro d e hde
  apply A.embedding_injective
  let C := resolventCorrection (A.embedding.comp T₀) z₀ z
  have hCe : C (A.embedding d) = C (A.embedding e) := by
    rw [resolventCorrection_embedding_apply A z₀ z T₀ hleft,
      resolventCorrection_embedding_apply A z₀ z T₀ hleft, hde]
  have hcancel := congrArg (fun T : X →L[ℂ] X ↦ T (A.embedding d - A.embedding e))
    (Ring.inverse_mul_cancel C hunit)
  have hker : C (A.embedding d - A.embedding e) = 0 := by
    simpa only [map_sub, sub_eq_zero] using hCe
  simp only [mul_apply_eq_comp, one_apply_eq_self,
    hker, map_zero] at hcancel
  exact sub_eq_zero.mp hcancel.symm

omit [CompleteSpace X] in
/--
If the ambient correction at `z` is a unit, the propagated inverse is a right inverse of
the pencil at `z`.
-/
theorem propagatedInverse_right_inv
    (A : DomainOperator X D) (z₀ z : ℂ) (T₀ : X →L[ℂ] D)
    (hright : (A.pencil z₀).comp T₀ = ContinuousLinearMap.id ℂ X)
    (hunit : IsUnit (resolventCorrection (A.embedding.comp T₀) z₀ z)) :
    (A.pencil z).comp (propagatedInverse T₀ A.embedding z₀ z) =
      ContinuousLinearMap.id ℂ X := by
  rw [propagatedInverse, ← ContinuousLinearMap.comp_assoc,
    pencil_comp_baseInverse A z₀ z T₀ hright]
  exact Ring.mul_inverse_cancel _ hunit

omit [CompleteSpace X] in
/--
If the ambient correction at `z` is a unit and `T₀` is a two-sided inverse at `z₀`, the
propagated inverse is also a left inverse of the pencil at `z`.
-/
theorem propagatedInverse_left_inv
    (A : DomainOperator X D) (z₀ z : ℂ) (T₀ : X →L[ℂ] D)
    (hleft : T₀.comp (A.pencil z₀) = ContinuousLinearMap.id ℂ D)
    (hright : (A.pencil z₀).comp T₀ = ContinuousLinearMap.id ℂ X)
    (hunit : IsUnit (resolventCorrection (A.embedding.comp T₀) z₀ z)) :
    (propagatedInverse T₀ A.embedding z₀ z).comp (A.pencil z) =
      ContinuousLinearMap.id ℂ D := by
  apply ContinuousLinearMap.ext
  intro d
  apply pencil_injective_of_isUnit_resolventCorrection A z₀ z T₀ hleft hunit
  have hright' := congrArg (fun T : X →L[ℂ] X ↦ T (A.pencil z d))
    (propagatedInverse_right_inv A z₀ z T₀ hright hunit)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hright'

/-- A simultaneous propagated resolvent on any set where all ambient
corrections are units.  The inverse remains ambient-to-domain valued and both
inverse equations are part of the result. -/
def hasResolventOnOfIsUnitResolventCorrection
    (A : DomainOperator X D) (z₀ : ℂ) (T₀ : X →L[ℂ] D)
    (hleft : T₀.comp (A.pencil z₀) = ContinuousLinearMap.id ℂ D)
    (hright : (A.pencil z₀).comp T₀ = ContinuousLinearMap.id ℂ X)
    (S : Set ℂ)
    (hunit : ∀ z ∈ S,
      IsUnit (resolventCorrection (A.embedding.comp T₀) z₀ z)) :
    HasResolventOn A S where
  inv := propagatedInverse T₀ A.embedding z₀
  left_inv z hz :=
    propagatedInverse_left_inv A z₀ z T₀ hleft hright (hunit z hz)
  right_inv z hz :=
    propagatedInverse_right_inv A z₀ z T₀ hright (hunit z hz)
  continuousOn := by
    intro z hz
    have hcorr : ContinuousAt
        (resolventCorrection (A.embedding.comp T₀) z₀) z :=
      (continuous_resolventCorrection (A.embedding.comp T₀) z₀).continuousAt
    have hinv : ContinuousAt
        (fun w ↦ Ring.inverse
          (resolventCorrection (A.embedding.comp T₀) z₀ w)) z := by
      have hu := hunit z hz
      have hinvAt : ContinuousAt Ring.inverse
          (resolventCorrection (A.embedding.comp T₀) z₀ z) := by
        simpa only [hu.unit_spec] using
          (NormedRing.inverse_continuousAt hu.unit)
      simpa [Function.comp_def] using hinvAt.comp hcorr
    have hout := (ContinuousLinearMap.compL ℂ X X D T₀).continuous.continuousAt.comp hinv
    change ContinuousWithinAt
      (fun w ↦ T₀.comp (Ring.inverse
        (resolventCorrection (A.embedding.comp T₀) z₀ w))) S z
    simpa [Function.comp_def] using hout.continuousWithinAt

end DomainOperator

end

end FastDynamo
