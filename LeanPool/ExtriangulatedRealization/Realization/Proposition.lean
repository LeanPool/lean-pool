/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Realizations
public import LeanPool.ExtriangulatedRealization.Complexes.Frobenius

/-!
# The algebraic-realization consequence of Proposition 2.3

Given `W` mapping compatibly and surjectively onto the `D_i`, `i ∈ J`, the realization functor
`C_J ⥤ K(Q)` with the maps `η` is a triangulated realization, and `K(Q)` is algebraic.
Here `K(Q)` is the homotopy category of all cochain complexes. The paper constructs its
realization in the bounded homotopy category.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject DerivedCategory
  Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard HasExt.standard

namespace RealizationData

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] {D : Iᵒᵖ ⥤ ModuleCat.{u} k}
  {J : Set I} (R : RealizationData D J) (hR : R.IsCompatible)

/-- The realization of `C_J` in `K(Q)` as an extriangulated functor. -/
noncomputable def extriangulatedFunctor :
    ExtriangulatedFunctor (dataJ (D := D) (J := J)) (HomotopyCategory R.Q (ComplexShape.up ℤ)) where
  F := R.realP hR
  additive := inferInstance
  η {C A} := R.eta hR C A
  η_push a δ := R.eta_push' hR a δ
  η_pull c δ := R.eta_pull' hR c δ
  distinguished h := R.realTriangle_distinguished hR h

lemma extriangulatedFunctor_isTriangulatedRealization :
    (R.extriangulatedFunctor hR).IsTriangulatedRealization :=
  ⟨⟨inferInstanceAs (R.realP hR).Full, inferInstanceAs (R.realP hR).Faithful⟩,
    fun C A => R.eta_bijective hR C A⟩

end RealizationData

/-- The algebraic-realization consequence of Proposition 2.3: compatible surjections
`W → D_i`, `i ∈ J`, give an algebraic realization of `C_J` in the homotopy category of all
cochain complexes. The cited proposition gives a realization in the bounded homotopy
category. -/
theorem hasAlgebraicRealization_subcatJ {k : Type u} [Field k] {I : Type u} [LinearOrder I]
    (D : Iᵒᵖ ⥤ ModuleCat.{u} k) (J : Set I) (W : ModuleCat.{u} k)
    (q : ∀ i ∈ J, W ⟶ D.obj (op i)) (hsurj : ∀ i (hi : i ∈ J), Function.Surjective (q i hi).hom)
    (hcomm : ∀ (i j : I) (hi : i ∈ J) (hj : j ∈ J) (h : i ≤ j),
      q j hj ≫ D.map (homOfLE h).op = q i hi) :
    ((cdData D).restrict (subcatJ D J)).HasAlgebraicRealization.{_, _, _, _, u, max 1 u} := by
  let R : RealizationData D J := ⟨W, q⟩
  have hR : R.IsCompatible := ⟨hsurj, hcomm⟩
  exact ⟨HomotopyCategory R.Q (ComplexShape.up ℤ), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    isAlgebraicTriangulated_homotopyCategory R.Q, R.extriangulatedFunctor hR,
    R.extriangulatedFunctor_isTriangulatedRealization hR⟩

end ExtriangulatedRealization
