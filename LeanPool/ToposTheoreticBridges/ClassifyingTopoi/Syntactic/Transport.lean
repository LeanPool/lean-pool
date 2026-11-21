/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Quotients
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Definability

/-!
# Transport of classifying sites along equivalences of topoi

* `LeanPool.ClassifyingTopoi.IsClassifyingSite.of_equivalence`: a site whose topos of sheaves is
  equivalent to a classifying topos, by an equivalence carrying the generic model to a given
  structure, is a classifying site with that structure;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.hasQuotientTopologies_of_isClassifyingSite`: the
  correspondence between quotients and finer topologies (roadmap 2.5) transfers from one
  classifying site of a theory to any other: a finer topology on the second site is transported
  along the equivalence of topoi (`ToposTheoreticBridges.transportTopology`), and the
  sheafifications on both sides correspond by uniqueness of left adjoints;
* `LeanPool.ClassifyingTopoi.CatStructure.Isomorphic.exists_interp_eq`: the definability of
  subobjects of powers transfers along isomorphisms of structures and along equivalences.
-/

@[expose] public section

universe w u₁ u₂ u

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
  LeanPool.ToposTheoreticBridges

attribute [local instance high] Sheaf.instHasColimitsOfShape

variable {L : Language.{u₁, u₂}}

namespace CatStructure

variable {E : Type*} [Category E] [HasFiniteLimits E] [HasImages E] [HasCoproducts.{w} E]

/-- The interpretations in isomorphic structures correspond by pulling back along the
isomorphism. -/
theorem Isomorphic.interp_eq_pullback {M N : CatStructure L E} {ε : M.carrier ≅ N.carrier}
    (h₁ : M.IsHom N ε.hom) (h₂ : N.IsHom M ε.inv) {n : ℕ} (χ : GeometricFormula.{w} L n) :
    N.interp χ = (Subobject.pullback (Limits.Pi.map fun _ : Fin n => ε.inv)).obj (M.interp χ) := by
  refine le_antisymm (h₂.interp_le χ) (((Subobject.pullback _).monotone
    (h₁.interp_le χ)).trans (le_of_eq ?_))
  rw [← Subobject.pullback_comp]
  have : (Limits.Pi.map fun _ : Fin n => ε.inv) ≫ (Limits.Pi.map fun _ => ε.hom) = 𝟙 _ := by
    ext
    simp
  rw [this, Subobject.pullback_id]

/-- Definability of the subobjects of the powers transfers along isomorphisms of structures. -/
theorem Isomorphic.exists_interp_eq {M N : CatStructure L E} (h : M.Isomorphic N)
    (hM : ∀ {n : ℕ} (S : Subobject (M.pow n)), ∃ ψ : GeometricFormula.{w} L n, M.interp ψ = S)
    {n : ℕ} (S : Subobject (N.pow n)) : ∃ ψ : GeometricFormula.{w} L n, N.interp ψ = S := by
  obtain ⟨ε, h₁, h₂⟩ := h
  obtain ⟨ψ, hψ⟩ := hM ((Subobject.pullback (Limits.Pi.map fun _ : Fin n => ε.hom)).obj S)
  refine ⟨ψ, ?_⟩
  rw [Isomorphic.interp_eq_pullback h₁ h₂, hψ, ← Subobject.pullback_comp]
  have : (Limits.Pi.map fun _ : Fin n => ε.inv) ≫ (Limits.Pi.map fun _ => ε.hom) = 𝟙 _ := by
    ext
    simp
  rw [this, Subobject.pullback_id]

end CatStructure

namespace IsClassifyingSite

variable {T : GeometricTheory.{u} L} {C C' : Type u} [SmallCategory C] [SmallCategory C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  {V : CatStructure L (Sheaf J (Type u))} {W : CatStructure L (Sheaf J' (Type u))}

/-- **Invariance of classifying sites.** If `(C, J, V)` classifies `T` and an equivalence
`Sh(C, J) ≌ Sh(C', J')` carries `V` to a structure isomorphic to `W`, then `(C', J', W)`
classifies `T`. -/
theorem of_equivalence (hV : IsClassifyingSite T J V) (e : Sheaf J (Type u) ≌ Sheaf J' (Type u))
    (hW : (V.map e.functor).Isomorphic W) : IsClassifyingSite T J' W := by
  refine ⟨hW.isModel (hV.isModel.map e.functor), fun D _ K => ⟨fun M hM => ?_,
    fun F G _ _ hF hG => ?_⟩⟩
  · obtain ⟨F, _, hF, hMF⟩ := hV.exists_isomorphic hM
    have := hF
    refine ⟨e.inverse ⋙ F, inferInstance, inferInstance, ?_⟩
    have i : F ≅ e.functor ⋙ e.inverse ⋙ F :=
      (Functor.leftUnitor F).symm ≪≫ Functor.isoWhiskerRight e.unitIso F ≪≫
        Functor.associator _ _ _
    exact hMF.trans ((V.isomorphic_map_of_iso i).trans ((V.isomorphic_map_comp _ _).trans
      (hW.map _)))
  · have := hF
    have := hG
    obtain ⟨ε, h₁, h₂⟩ := hW
    have he := (e.symm.congrLeft (E := Sheaf K (Type u))).fullyFaithfulFunctor
    obtain ⟨hinj, hhom⟩ := (hV.2 D K).2 (e.functor ⋙ F) (e.functor ⋙ G) inferInstance
      inferInstance
    have key : ∀ α : F ⟶ G, α.app (e.functor.obj V.carrier) =
        F.map ε.hom ≫ α.app W.carrier ≫ G.map ε.inv := fun α => by
      rw [α.naturality_assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id]
    refine ⟨fun α α' hαα' => ?_, fun h => ⟨fun hh => ?_, ?_⟩⟩
    · apply he.map_injective
      apply hinj
      change α.app (e.functor.obj V.carrier) = α'.app (e.functor.obj V.carrier)
      rw [key, key]
      exact congrArg _ (congrArg (· ≫ _) hαα')
    · have hk : (V.map (e.functor ⋙ F)).IsHom (V.map (e.functor ⋙ G))
          (F.map ε.hom ≫ h ≫ G.map ε.inv) := by
        rw [V.isHom_map_comp_iff]
        exact (h₁.map F).comp (hh.comp (h₂.map G))
      obtain ⟨α₀, hα₀⟩ := (hhom _).1 hk
      obtain ⟨α, rfl⟩ := he.map_surjective α₀
      refine ⟨α, ?_⟩
      change α.app (e.functor.obj V.carrier) = _ at hα₀
      rw [key] at hα₀
      have := congrArg (fun k => F.map ε.inv ≫ k ≫ G.map ε.hom) hα₀
      simpa [← F.map_comp_assoc, ← G.map_comp] using this
    · rintro ⟨α, rfl⟩
      exact W.isHom_map_app α

end IsClassifyingSite

end LeanPool.ClassifyingTopoi
