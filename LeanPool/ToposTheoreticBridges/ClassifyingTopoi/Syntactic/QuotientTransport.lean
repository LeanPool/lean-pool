/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Transport

/-!
# Transport of the correspondence between quotients and topologies

If two sites classify the same theory and the correspondence of roadmap 2.5 holds on one of them
(`IsClassifyingSite.HasQuotientTopologies`), it holds on the other
(`IsClassifyingSite.hasQuotientTopologies_of_isClassifyingSite`). A topology `J₁` finer than `J`
on the first site is transported along the equivalence `e : Sh(C, J) ≌ Sh(C₀, J₀)` of the
classifying topoi to a topology `K₁` finer than `J₀`, with the same sheaves; `e` restricts to an
equivalence `Sh(C, J₁) ≌ Sh(C₀, K₁)` (`sheafEquivOfIsSheafIff`), and the two sheafifications
correspond under it, by uniqueness of left adjoints. Hence the quotient classified by
`(C₀, K₁)` is classified by `(C, J₁)` (`IsClassifyingSite.of_equivalence`).
-/

@[expose] public section

universe u₁ u₂ u

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
  LeanPool.ToposTheoreticBridges

attribute [local instance high] Sheaf.instHasColimitsOfShape

variable {L : Language.{u₁, u₂}}

namespace IsClassifyingSite

variable {T : GeometricTheory.{u} L} {C C₀ : Type u} [SmallCategory C] [SmallCategory C₀]
  {J : GrothendieckTopology C} {J₀ : GrothendieckTopology C₀}
  {U : CatStructure L (Sheaf J (Type u))} {U₀ : CatStructure L (Sheaf J₀ (Type u))}

/-- **Transport of the converse of roadmap 2.5.** If the topologies finer than the topology of
one classifying site of `T` classify quotients of `T`, so do the topologies finer than the
topology of any other classifying site of `T`. -/
theorem exists_quotient_theory_of_isClassifyingSite (hU : IsClassifyingSite T J U)
    (hU₀ : IsClassifyingSite T J₀ U₀)
    (hQ : ∀ K₁ : GrothendieckTopology C₀, J₀ ≤ K₁ → ∃ T₁ : GeometricTheory.{u} L, T ⊆ T₁ ∧
      IsClassifyingSite T₁ K₁ (U₀.map (sheafToPresheaf J₀ (Type u) ⋙
        presheafToSheaf K₁ (Type u))))
    {J₁ : GrothendieckTopology C} (h : J ≤ J₁) :
    ∃ T₁ : GeometricTheory.{u} L, T ⊆ T₁ ∧
      IsClassifyingSite T₁ J₁
        (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))) := by
  obtain ⟨e, he⟩ := hU.exists_equivalence hU₀
  have k₁ := le_transportTopology e J₁
  have hsh : ∀ F : Sheaf J (Type u), Presheaf.IsSheaf J₁ F.obj ↔
      Presheaf.IsSheaf (transportTopology e J₁) (e.functor.obj F).obj :=
    isSheaf_iff_isSheaf_transportTopology e h
  obtain ⟨T₁, hT₁, hc⟩ := hQ _ k₁
  let Φ := sheafEquivOfIsSheafIff h k₁ e hsh
  have := isLeftAdjoint_sheafify h
  have := isLeftAdjoint_sheafify k₁
  let a₀ := sheafToPresheaf J₀ (Type u) ⋙ presheafToSheaf (transportTopology e J₁) (Type u)
  have adj₃ : e.functor ⋙ a₀ ⋙ Φ.inverse ⊣
      Φ.functor ⋙ sheafInclusion k₁ ⋙ e.inverse :=
    e.toAdjunction.comp ((sheafifyAdjunction k₁).comp Φ.symm.toAdjunction)
  have γ : Φ.functor ⋙ sheafInclusion k₁ ⋙ e.inverse ≅ sheafInclusion h :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (sheafEquivOfIsSheafIffCompIso h k₁ e hsh) e.inverse ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e.unitIso.symm ≪≫
          Functor.rightUnitor _
  have i := (sheafifyAdjunction h).leftAdjointUniq (adj₃.ofNatIsoRight γ)
  refine ⟨T₁, hT₁, hc.of_equivalence Φ.symm ?_⟩
  exact ((((U.isomorphic_map_of_iso i).trans (U.isomorphic_map_comp _ _)).trans
    (he.map (a₀ ⋙ Φ.inverse))).trans (U₀.isomorphic_map_comp a₀ Φ.inverse)).symm

/-- **Transport of roadmap 2.5.** The correspondence between quotients of a theory and topologies
finer than the classifying topology transfers from one classifying site to any other. -/
theorem hasQuotientTopologies_of_isClassifyingSite (hU : IsClassifyingSite T J U)
    (hU₀ : IsClassifyingSite T J₀ U₀) (hQ : HasQuotientTopologies T J₀ U₀) :
    HasQuotientTopologies T J U :=
  ⟨fun _ hT => hU.exists_quotient_topology hT,
    fun _ h => hU.exists_quotient_theory_of_isClassifyingSite hU₀ hQ.2 h⟩

end IsClassifyingSite

end LeanPool.ClassifyingTopoi
