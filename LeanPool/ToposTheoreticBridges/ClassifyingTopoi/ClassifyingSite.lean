/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Homomorphisms

/-!
# Classifying sites and Morita equivalence

A small site `(C, J)` with a model `U` of a geometric theory `T` in `Sh(C, J)` *classifies* `T`
(`IsClassifyingSite T J U`) when, for every small site `(D, K)`, every model of `T` in
`Sh(D, K)` is isomorphic to the image of `U` under a left exact left adjoint
`Sh(C, J) ⥤ Sh(D, K)` (the inverse image of a geometric morphism), and evaluation at the carrier
of `U` is a bijection from natural transformations between two such functors onto the
homomorphisms between the image models.

## Main definitions

* `LeanPool.ClassifyingTopoi.IsClassifyingSite`: the universal property above;
* `LeanPool.ClassifyingTopoi.MoritaEquivalent`: two theories are Morita-equivalent when they
  have classifying sites with equivalent topoi of sheaves.

## Main results

* `LeanPool.ClassifyingTopoi.IsClassifyingSite.nonempty_iso`: two inverse images out of a
  classifying topos which map the generic model to isomorphic models are isomorphic;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_equivalence` (roadmap 2.4): two classifying
  sites of the same theory have equivalent topoi of sheaves, by an equivalence carrying one
  generic model to the other. This is the Yoneda argument: the two universal models give
  inverse images `F` and `G` in both directions, and `F ⋙ G` and `𝟭` both map the generic
  model to models isomorphic to it, hence are isomorphic by the second half of the universal
  property;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.moritaEquivalent_iff`: for theories with
  classifying sites, Morita equivalence is the equivalence of these topoi of sheaves, for any
  choice of classifying sites; Morita equivalence is symmetric and transitive
  (`MoritaEquivalent.symm`, `MoritaEquivalent.trans`) and reflexive on theories having a
  classifying site (`IsClassifyingSite.moritaEquivalent_refl`).

Reflexivity for all theories needs the existence of classifying sites (roadmap 2.3, the
syntactic site), which is not formalised here.
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅ u₆ u

open CategoryTheory CategoryTheory.Limits

namespace LeanPool.ClassifyingTopoi

attribute [local instance high] Sheaf.instHasColimitsOfShape

variable {L : FirstOrder.Language.{u₁, u₂}}

/-- `(C, J)` with the model `U` classifies `T`: for every small site `(D, K)`, every
model of `T` in `Sh(D, K)` is isomorphic to the image of `U` under a left exact left adjoint
`Sh(C, J) ⥤ Sh(D, K)`, and evaluation at the carrier of `U` is a bijection from natural
transformations between two such functors onto the homomorphisms between the image models. -/
def IsClassifyingSite (T : GeometricTheory.{u} L) {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (U : CatStructure L (Sheaf J (Type u))) : Prop :=
  U.IsModel T ∧ ∀ (D : Type u) [SmallCategory D] (K : GrothendieckTopology D),
    (∀ M : CatStructure L (Sheaf K (Type u)), M.IsModel T →
      ∃ (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) (_ : PreservesFiniteLimits F),
        F.IsLeftAdjoint ∧ M.Isomorphic (U.map F)) ∧
    ∀ (F G : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]
      [PreservesFiniteLimits G], F.IsLeftAdjoint → G.IsLeftAdjoint →
      Function.Injective (fun α : F ⟶ G => α.app U.carrier) ∧
      ∀ h : F.obj U.carrier ⟶ G.obj U.carrier,
        (U.map F).IsHom (U.map G) h ↔ ∃ α : F ⟶ G, α.app U.carrier = h

/-- Two geometric theories, possibly over different languages, are Morita-equivalent
when they have classifying sites whose topoi of sheaves are equivalent. -/
def MoritaEquivalent {L' : FirstOrder.Language.{u₃, u₄}} (T : GeometricTheory.{u} L)
    (T' : GeometricTheory.{u} L') : Prop :=
  ∃ (C C' : Type u) (_ : SmallCategory C) (_ : SmallCategory C') (J : GrothendieckTopology C)
    (J' : GrothendieckTopology C') (U : CatStructure L (Sheaf J (Type u)))
    (U' : CatStructure L' (Sheaf J' (Type u))),
    IsClassifyingSite T J U ∧ IsClassifyingSite T' J' U' ∧
      Nonempty (Sheaf J (Type u) ≌ Sheaf J' (Type u))

namespace IsClassifyingSite

variable {T : GeometricTheory.{u} L} {C : Type u} [SmallCategory C]
  {J : GrothendieckTopology C} {U : CatStructure L (Sheaf J (Type u))}

/-- The generic model of a classifying site is a model. -/
theorem isModel (hU : IsClassifyingSite T J U) : U.IsModel T :=
  hU.1

/-- Every model of the theory is, up to isomorphism, the image of the generic model under an
inverse image. -/
theorem exists_isomorphic (hU : IsClassifyingSite T J U) {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} {M : CatStructure L (Sheaf K (Type u))} (hM : M.IsModel T) :
    ∃ (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) (_ : PreservesFiniteLimits F),
      F.IsLeftAdjoint ∧ M.Isomorphic (U.map F) :=
  (hU.2 D K).1 M hM

/-- Two inverse images out of a classifying topos mapping the generic model to isomorphic
structures are isomorphic functors. -/
theorem nonempty_iso (hU : IsClassifyingSite T J U) {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} (F G : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (hF : F.IsLeftAdjoint)
    (hG : G.IsLeftAdjoint) (h : (U.map F).Isomorphic (U.map G)) : Nonempty (F ≅ G) := by
  obtain ⟨e, h₁, h₂⟩ := h
  obtain ⟨α, hα⟩ := (((hU.2 D K).2 F G hF hG).2 e.hom).1 h₁
  obtain ⟨β, hβ⟩ := (((hU.2 D K).2 G F hG hF).2 e.inv).1 h₂
  refine ⟨⟨α, β, ((hU.2 D K).2 F F hF hF).1 ?_, ((hU.2 D K).2 G G hG hG).1 ?_⟩⟩
  · change (α ≫ β).app U.carrier = (𝟙 F : F ⟶ F).app U.carrier
    rw [NatTrans.comp_app, hα, hβ]
    exact e.hom_inv_id
  · change (β ≫ α).app U.carrier = (𝟙 G : G ⟶ G).app U.carrier
    rw [NatTrans.comp_app, hα, hβ]
    exact e.inv_hom_id

/-- Two classifying sites of the same theory have equivalent topoi of sheaves, by an
equivalence carrying one generic model to the other. -/
theorem exists_equivalence {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
    {U' : CatStructure L (Sheaf J' (Type u))} (hU : IsClassifyingSite T J U)
    (hU' : IsClassifyingSite T J' U') :
    ∃ e : Sheaf J (Type u) ≌ Sheaf J' (Type u), (U.map e.functor).Isomorphic U' := by
  obtain ⟨F, _, hF, hUF⟩ := hU.exists_isomorphic hU'.isModel
  obtain ⟨G, _, hG, hUG⟩ := hU'.exists_isomorphic hU.isModel
  have hFG : (U.map (F ⋙ G)).Isomorphic (U.map (𝟭 _)) :=
    (U.isomorphic_map_comp F G).trans
      ((hUF.symm.map G).trans (hUG.symm.trans (U.isomorphic_map_id).symm))
  have hGF : (U'.map (G ⋙ F)).Isomorphic (U'.map (𝟭 _)) :=
    (U'.isomorphic_map_comp G F).trans
      ((hUG.symm.map F).trans (hUF.symm.trans (U'.isomorphic_map_id).symm))
  obtain ⟨η⟩ := hU.nonempty_iso (F ⋙ G) (𝟭 _) inferInstance inferInstance hFG
  obtain ⟨ε⟩ := hU'.nonempty_iso (G ⋙ F) (𝟭 _) inferInstance inferInstance hGF
  exact ⟨CategoryTheory.Equivalence.mk F G η.symm ε, hUF.symm⟩

/-- A theory with a classifying site is Morita-equivalent to itself. -/
theorem moritaEquivalent_refl (hU : IsClassifyingSite T J U) : MoritaEquivalent T T :=
  ⟨C, C, inferInstance, inferInstance, J, J, U, U, hU, hU, ⟨CategoryTheory.Equivalence.refl⟩⟩

/-- For theories with classifying sites, Morita equivalence is the equivalence of the topoi of
sheaves on any choice of classifying sites. -/
theorem moritaEquivalent_iff {L' : FirstOrder.Language.{u₃, u₄}} {T' : GeometricTheory.{u} L'}
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {U' : CatStructure L' (Sheaf K (Type u))} (hU : IsClassifyingSite T J U)
    (hU' : IsClassifyingSite T' K U') :
    MoritaEquivalent T T' ↔ Nonempty (Sheaf J (Type u) ≌ Sheaf K (Type u)) := by
  refine ⟨fun ⟨C₀, D₀, _, _, J₀, K₀, U₀, U₀', hU₀, hU₀', ⟨e⟩⟩ => ?_,
    fun ⟨e⟩ => ⟨C, D, inferInstance, inferInstance, J, K, U, U', hU, hU', ⟨e⟩⟩⟩
  obtain ⟨e₁, -⟩ := hU.exists_equivalence hU₀
  obtain ⟨e₂, -⟩ := hU₀'.exists_equivalence hU'
  exact ⟨e₁.trans (e.trans e₂)⟩

end IsClassifyingSite

/-- Morita equivalence is symmetric. -/
theorem MoritaEquivalent.symm {L' : FirstOrder.Language.{u₃, u₄}} {T : GeometricTheory.{u} L}
    {T' : GeometricTheory.{u} L'} (h : MoritaEquivalent T T') : MoritaEquivalent T' T :=
  let ⟨C, C', _, _, J, J', U, U', hU, hU', ⟨e⟩⟩ := h
  ⟨C', C, inferInstance, inferInstance, J', J, U', U, hU', hU, ⟨e.symm⟩⟩

/-- Morita equivalence is transitive. -/
theorem MoritaEquivalent.trans {L' : FirstOrder.Language.{u₃, u₄}}
    {L'' : FirstOrder.Language.{u₅, u₆}} {T : GeometricTheory.{u} L}
    {T' : GeometricTheory.{u} L'} {T'' : GeometricTheory.{u} L''} (h : MoritaEquivalent T T')
    (h' : MoritaEquivalent T' T'') : MoritaEquivalent T T'' := by
  obtain ⟨C, C', _, _, J, J', U, U', hU, hU', ⟨e⟩⟩ := h
  obtain ⟨D, D', _, _, K, K', V, V', hV, hV', ⟨e'⟩⟩ := h'
  obtain ⟨f, -⟩ := hU'.exists_equivalence hV
  exact ⟨C, D', inferInstance, inferInstance, J, K', U, V', hU, hV', ⟨e.trans (f.trans e')⟩⟩

end LeanPool.ClassifyingTopoi
