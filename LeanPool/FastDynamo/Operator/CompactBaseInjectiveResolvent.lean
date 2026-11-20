/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.DomainPencilFredholm
public import LeanPool.FastDynamo.Operator.ResolventPropagation

/-!
# Resolvents from a compact base resolvent and pencil injectivity

This module holds the generic Fredholm step used whenever a coercive lower
bound is available: if a domain operator has a resolvent at one base
point whose state resolvent is compact, then injectivity of its pencil at
another point already constructs a two-sided singleton resolver there.

No range hypothesis, adjoint resolver, or target-pencil inverse is assumed:
surjectivity is a consequence of compactness and injectivity.  The statement
is purely abstract operator theory on bundled-domain pencils, so it is
available to every concrete resolvent construction.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Set

namespace DomainOperator

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- The compact Fredholm alternative in the form needed below: an injective
compact perturbation of the identity is continuously invertible. -/
private theorem isInvertible_id_sub_of_isCompact_of_injective
    {K : X →L[ℂ] X} (hK : IsCompactOperator K)
    (hinj : Function.Injective (ContinuousLinearMap.id ℂ X - K)) :
    (ContinuousLinearMap.id ℂ X - K).IsInvertible := by
  have hid : (ContinuousLinearMap.id ℂ X).IsInvertible :=
    ⟨ContinuousLinearEquiv.refl ℂ X, rfl⟩
  apply CompactFactor.isInvertible_sub_of_not_hasEigenvalue_one hid hK
  rw [CompactAffinePencil.normalized_id]
  intro heig
  obtain ⟨x, hx⟩ := heig.exists_hasEigenvector
  have hxzero : (ContinuousLinearMap.id ℂ X - K) x = 0 := by
    have hxeq := hx.apply_eq_smul
    change x - (((K : X →L[ℂ] X) : Module.End ℂ X) x) = 0
    rw [show (((K : X →L[ℂ] X) : Module.End ℂ X) x) = x by
      simpa only [one_smul] using hxeq]
    exact sub_self x
  have hxzero' :
      (ContinuousLinearMap.id ℂ X - K) x =
        (ContinuousLinearMap.id ℂ X - K) 0 := by
    simpa only [map_zero] using hxzero
  have : x = 0 := hinj hxzero'
  exact hx.2 this

/-- If one point has a compact state resolvent, injectivity of the pencil at
another point already constructs a two-sided singleton resolver
there.  This is the Fredholm alternative for affine domain pencils, stated
without a range or adjoint hypothesis. -/
theorem hasResolventAt_of_compactStateResolvent_of_pencil_injective
    (A : DomainOperator X D) {z₀ z : ℂ}
    (h₀ : HasResolventOn A {z₀})
    (hcompact : IsCompactOperator (h₀.stateResolvent z₀))
    (hinj : Function.Injective (A.pencil z)) :
    Nonempty (HasResolventOn A {z}) := by
  let R₀ : X →L[ℂ] X := h₀.stateResolvent z₀
  let C : X →L[ℂ] X := resolventCorrection R₀ z₀ z
  let K : X →L[ℂ] X := (z₀ - z) • R₀
  have hright₀ :
      (A.pencil z₀).comp (h₀.inv z₀) = ContinuousLinearMap.id ℂ X :=
    h₀.right_inv z₀ (by simp)
  have hleft₀ :
      (h₀.inv z₀).comp (A.pencil z₀) = ContinuousLinearMap.id ℂ D :=
    h₀.left_inv z₀ (by simp)
  have hfactor : (A.pencil z).comp (h₀.inv z₀) = C := by
    simpa only [R₀, C, HasResolventOn.stateResolvent] using
      pencil_comp_baseInverse A z₀ z (h₀.inv z₀) hright₀
  have hCinj : Function.Injective C := by
    intro x y hxy
    have hxy' : A.pencil z (h₀.inv z₀ x) =
        A.pencil z (h₀.inv z₀ y) := by
      have := hxy
      rw [← hfactor] at this
      simpa only [ContinuousLinearMap.comp_apply] using this
    have hinvxy : h₀.inv z₀ x = h₀.inv z₀ y := hinj hxy'
    calc
      x = A.pencil z₀ (h₀.inv z₀ x) := by
        have hx := DFunLike.congr_fun hright₀ x
        simpa only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply] using hx.symm
      _ = A.pencil z₀ (h₀.inv z₀ y) := congrArg (A.pencil z₀) hinvxy
      _ = y := by
        have hy := DFunLike.congr_fun hright₀ y
        simpa only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply] using hy
  have hCeq : C = ContinuousLinearMap.id ℂ X - K := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [C, K, resolventCorrection, add_apply, sub_apply,
      smul_apply, ContinuousLinearMap.id_apply]
    module
  have hK : IsCompactOperator K := hcompact.smul (z₀ - z)
  have hCinv : C.IsInvertible := by
    rw [hCeq]
    exact isInvertible_id_sub_of_isCompact_of_injective hK (by
      rw [← hCeq]
      exact hCinj)
  have hCunit : IsUnit C :=
    ContinuousLinearMap.isInvertible_iff_isUnit.mp hCinv
  exact ⟨hasResolventOnOfIsUnitResolventCorrection
    A z₀ (h₀.inv z₀) hleft₀ hright₀ {z}
      (fun w hw ↦ by
        have hwz : w = z := by simpa only [mem_singleton_iff] using hw
        subst w
        simpa only [R₀, C, HasResolventOn.stateResolvent] using hCunit)⟩

end DomainOperator

end

end FastDynamo
