/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Extriangulated
public import LeanPool.ExtriangulatedRealization.Criterion.Necessity

/-!
# Theorem B (= Theorem 3.1)

`C(D)` has a triangulated embedding if and only if every projection `lim D → D_i` is surjective,
if and only if `C(D)` has an algebraic realization. Necessity is `theoremB_necessity`.
Sufficiency uses the algebraic-realization consequence of Proposition 2.3 with `J = I`
and `W = lim D`, the module of compatible families,
since `C_I` is all of `C(D)`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel Pretriangulated

universe u

attribute [local instance] HasExt.standard

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-- The compatible families of an inverse system: the inverse limit `lim D`. -/
def compatibleFamilies : Submodule k (∀ j : I, D.obj (op j)) where
  carrier := {y | ∀ {j j' : I} (h : j ≤ j'), (D.map (homOfLE h).op).hom (y j') = y j}
  add_mem' := by
    intro y z hy hz j j' h
    simp [hy h, hz h]
  zero_mem' := by
    intro j j' h
    simp
  smul_mem' := by
    intro c y hy j j' h
    simp [hy h]

lemma mem_compatibleFamilies_iff (y : ∀ j : I, D.obj (op j)) :
    y ∈ compatibleFamilies D ↔
      ∀ {j j' : I} (h : j ≤ j'), (D.map (homOfLE h).op).hom (y j') = y j := Iff.rfl

/-- The projections `lim D → D_i`. -/
noncomputable def limProj (i : I) : ModuleCat.of k (compatibleFamilies D) ⟶ D.obj (op i) :=
  ModuleCat.ofHom ((LinearMap.proj i).comp (compatibleFamilies D).subtype)

/-- Every object of `C(D)` has its labels in `I`. -/
lemma subcatJ_univ : subcatJ D (Set.univ : Set I) = ⊤ := by
  ext M
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  intro i
  rcases M.X i with _ | _ | j | j <;> trivial

/-- A triangulated realization of the restriction of `E` to all objects is one of `E`. -/
lemma hasAlgebraicRealization_of_restrict_top {C : Type*} [Category C] [Preadditive C]
    {𝔼 : ExtriangulatedData.{u + 1} k C}
    (h : (𝔼.restrict ⊤).HasAlgebraicRealization.{_, _, _, _, u, max 1 u}) :
    𝔼.HasAlgebraicRealization.{_, _, _, _, u, max 1 u} := by
  obtain ⟨T, _, _, _, _, _, _, _, hT, Φ, ⟨⟨hfull, hfaith⟩, hη⟩⟩ := h
  let L : C ⥤ (⊤ : ObjectProperty C).FullSubcategory := (⊤ : ObjectProperty C).lift (𝟭 C)
    (fun _ => trivial)
  let Ψ : ExtriangulatedFunctor 𝔼 T :=
    { F := L ⋙ Φ.F
      additive := by
        have := Φ.additive
        have : L.Additive := ⟨fun {X Y f g} => rfl⟩
        infer_instance
      η {C' A} := Φ.η (C' := L.obj C') (A := L.obj A)
      η_push {C' A A'} a δ := Φ.η_push (C' := L.obj C') (L.map a) δ
      η_pull {C'' C' A} c δ := Φ.η_pull (A := L.obj A) (L.map c) δ
      distinguished h := Φ.distinguished h }
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hT, Ψ, ⟨⟨?_, ?_⟩, fun C' A => hη (L.obj C') (L.obj A)⟩⟩
  · exact Functor.Full.comp L Φ.F
  · exact Functor.Faithful.comp L Φ.F


/-- **Theorem B, (2) ⇒ (3).** -/
lemma hasAlgebraicRealization_of_projectionsSurjective
    (hP : ProjectionsSurjective D) :
    (cdData D).HasAlgebraicRealization.{_, _, _, _, u, max 1 u} := by
  apply hasAlgebraicRealization_of_restrict_top
  rw [← subcatJ_univ]
  refine hasAlgebraicRealization_subcatJ D Set.univ (ModuleCat.of k (compatibleFamilies D))
    (fun i _ => limProj D i) (fun i _ x => ?_) (fun i j _ _ h => ?_)
  · obtain ⟨y, hy, hyi⟩ := hP i x
    exact ⟨⟨y, (mem_compatibleFamilies_iff D y).mpr fun h => hy h⟩, hyi⟩
  · ext y
    exact (mem_compatibleFamilies_iff D y.1).mp y.2 h

/-- **Theorem B (= Theorem 3.1).** -/
theorem theoremB : TheoremB.{u} := by
  intro k _ I _ _ _ D hD
  have h₂₃ : ProjectionsSurjective D →
      (cdData D).HasAlgebraicRealization.{_, _, _, _, u, max 1 u} :=
    hasAlgebraicRealization_of_projectionsSurjective D
  have h₃₁ : (cdData D).HasAlgebraicRealization.{_, _, _, _, u, max 1 u} →
      (cdData D).HasTriangulatedEmbedding.{_, _, _, _, u, max 1 u} := by
    rintro ⟨T, i₁, i₂, i₃, i₄, i₅, i₆, i₇, -, Φ, hΦ, -⟩
    exact ⟨T, i₁, i₂, i₃, i₄, i₅, i₆, i₇, Φ, hΦ⟩
  have h₁₂ := theoremB_necessity.{u, u, max 1 u} k I D
  exact ⟨⟨h₁₂, fun h => h₃₁ (h₂₃ h)⟩, ⟨h₂₃, fun h => h₁₂ (h₃₁ h)⟩⟩

end ExtriangulatedRealization
