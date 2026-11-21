/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Extension
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.NatTrans
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Quotients

/-!
# Every geometric theory has a classifying site (roadmap 2.3)

The presheaf topos on the Horn category of `L`, that is the topos of sheaves for the trivial
topology `⊥`, with the generic structure `HornCat.genericSheaf L` (the structure of the Yoneda
embedding), classifies the empty theory over `L` (`HornCat.isClassifyingSite_hornCat`):

* every structure `M` in `Sh(D, K)` is the image of the generic structure under the left exact
  left adjoint `Sh(HornCat L, ⊥) ≃ Psh(HornCat L) ⥤ Psh(D) ⥤ Sh(D, K)`, the extension of the
  underlying presheaf structure of `M` (`LeanPool.ClassifyingTopoi.Syntactic.HornCat.extension`)
  followed by sheafification;
* natural transformations between left exact left adjoints out of the presheaf topos are
  determined by their restrictions along the Yoneda embedding (left Kan extensions), and these are
  the homomorphisms between the image structures (`HornCat.exists_natTrans_of_isHom`).

A geometric theory `T` over `L` is a quotient of the empty theory, hence is classified by the
topology `quotientTopology (genericSheaf L) T` on the Horn category, with the sheafified generic
structure (`IsClassifyingSite.quotient`, roadmap 2.5); this is
`HornCat.isClassifyingSite_genericModel` and roadmap 2.3, `exists_isClassifyingSite`, in the
universe `max u₁ u₂ u` of the language and of the theory's disjunctions.

## Deviation from the roadmap

The classifying site is not the geometric syntactic category of `T` (formulas in context and
provably functional relations, with the syntactic topology): it is the Horn category of `L` with
the topology classifying `T` as a quotient of the empty theory. The two sites have equivalent
topoi of sheaves (`IsClassifyingSite.exists_equivalence`). No proof theory is needed: the Horn
category is defined by validity in all structures, and the axioms of `T` enter only through the
quotient topology.
-/

@[expose] public section

universe u u₁ u₂

namespace LeanPool.ClassifyingTopoi.Syntactic

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits LeanPool.ClassifyingTopoi
  Opposite

attribute [local instance high] Sheaf.instHasColimitsOfShape

/-- Restriction along the Yoneda embedding is a bijection on natural transformations between
colimit-preserving functors out of a presheaf topos. -/
theorem bijective_whiskerLeft_yoneda {C : Type u} [SmallCategory C] {E : Type*} [Category.{u} E]
    [HasColimitsOfSize.{u, u} E] (F G : (Cᵒᵖ ⥤ Type u) ⥤ E) [PreservesColimitsOfSize.{u, u} F] :
    Function.Bijective (fun β : F ⟶ G => Functor.whiskerLeft yoneda β) := by
  let e : shrinkYoneda.{u} ⋙ F ≅ yoneda ⋙ F := Functor.isoWhiskerRight shrinkYonedaIsoYoneda F
  have := Presheaf.isLeftKanExtension_along_shrinkYoneda_of_preservesColimits e
  let Φ := F.homEquivOfIsLeftKanExtension e.inv G
  let ψ : (yoneda ⋙ F ⟶ shrinkYoneda.{u} ⋙ G) ≃ (yoneda ⋙ F ⟶ yoneda ⋙ G) :=
    Iso.homCongr (Iso.refl _) (Functor.isoWhiskerRight shrinkYonedaIsoYoneda G)
  have key : (fun β : F ⟶ G => Functor.whiskerLeft yoneda β) = ψ ∘ Φ := by
    funext β
    ext X
    change β.app (yoneda.obj X) = ((Iso.refl _).inv ≫ (e.inv ≫ Functor.whiskerLeft shrinkYoneda β) ≫
      (Functor.isoWhiskerRight shrinkYonedaIsoYoneda G).hom).app X
    simp only [e, Iso.refl_inv, Category.id_comp, NatTrans.comp_app,
      Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Category.assoc]
    rw [NatTrans.naturality_assoc, ← G.map_comp, Iso.inv_hom_id_app, G.map_id,
      Category.comp_id]
  rw [key]
  exact ψ.bijective.comp Φ.bijective

variable {L : Language.{u₁, u₂}}

namespace HornCat

variable (L) in
/-- The generic structure on the Horn category, in the topos of sheaves for the trivial
topology. -/
noncomputable abbrev genericSheaf :
    CatStructure L (Sheaf (⊥ : GrothendieckTopology (HornCat.{u} L)) (Type (max u₁ u₂ u))) :=
  (genericPsh L).map (sheafBotEquivalence (Type (max u₁ u₂ u))).inverse

variable {D : Type (max u₁ u₂ u)} [SmallCategory D] {K : GrothendieckTopology D}

/-- **Existence half.** Every structure in a topos of sheaves on a small site is the image of the
generic structure under a left exact left adjoint out of the presheaf topos on the Horn
category. -/
theorem exists_isomorphic_map (M : CatStructure L (Sheaf K (Type (max u₁ u₂ u)))) :
    ∃ (F : Sheaf (⊥ : GrothendieckTopology (HornCat.{u} L)) (Type (max u₁ u₂ u)) ⥤
        Sheaf K (Type (max u₁ u₂ u))) (_ : PreservesFiniteLimits F),
      F.IsLeftAdjoint ∧ M.Isomorphic ((genericSheaf.{u} L).map F) := by
  let P := M.map (sheafToPresheaf K (Type (max u₁ u₂ u)))
  let e := sheafBotEquivalence (C := HornCat.{u} L) (Type (max u₁ u₂ u))
  let a := presheafToSheaf K (Type (max u₁ u₂ u))
  have := isLeftAdjoint_extension_comp.{u} (K := K) P
  let F := e.functor ⋙ extension.{u} P ⋙ a
  refine ⟨F, inferInstance, inferInstance, ?_⟩
  have i₁ : extension.{u} P ⋙ a ≅ e.inverse ⋙ F :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e.counitIso.symm _ ≪≫
      Functor.associator _ _ _
  exact (CatStructure.isomorphic_map_sheafToPresheaf_map_presheafToSheaf M).trans
    ((((isomorphic_fibers.{u} P).symm.trans ((isomorphic_hornStructure_of_iso
      (yonedaCompExtensionIso.{u} P).symm).trans (isomorphic_comp_hornStructure _ _))).map a).trans
    (((genericPsh L).isomorphic_map_comp _ a).symm.trans
    (((genericPsh L).isomorphic_map_of_iso i₁).trans ((genericPsh L).isomorphic_map_comp _ _))))

variable (F G : Sheaf (⊥ : GrothendieckTopology (HornCat.{u} L)) (Type (max u₁ u₂ u)) ⥤
    Sheaf K (Type (max u₁ u₂ u))) [PreservesFiniteLimits F] [PreservesFiniteLimits G]

/-- Homomorphisms between the images of the generic structure are homomorphisms between the
structures of the restrictions along the Yoneda embedding. -/
theorem isHom_map_genericSheaf_iff
    (h : F.obj (genericSheaf.{u} L).carrier ⟶ G.obj (genericSheaf.{u} L).carrier) :
    ((genericSheaf.{u} L).map F).IsHom ((genericSheaf.{u} L).map G) h ↔
      (hornStructure (yoneda ⋙ (sheafBotEquivalence _).inverse ⋙ F)).IsHom
        (hornStructure (yoneda ⋙ (sheafBotEquivalence _).inverse ⋙ G)) h := by
  rw [← (genericPsh L).isHom_map_comp_iff]
  constructor
  · intro hh
    simpa using ((isHom_comp_hornStructure _ _).comp hh).comp (isHom_comp_hornStructure' _ _)
  · intro hh
    simpa using ((isHom_comp_hornStructure' _ _).comp hh).comp (isHom_comp_hornStructure _ _)

/-- **Homomorphism half.** Natural transformations between left exact left adjoints out of the
presheaf topos on the Horn category are determined by their component at the generic structure,
and these components are exactly the homomorphisms between the image structures. -/
theorem natTrans_app_genericSheaf (hF : F.IsLeftAdjoint) (hG : G.IsLeftAdjoint) :
    Function.Injective (fun α : F ⟶ G => α.app (genericSheaf.{u} L).carrier) ∧
      ∀ h : F.obj (genericSheaf.{u} L).carrier ⟶ G.obj (genericSheaf.{u} L).carrier,
        ((genericSheaf.{u} L).map F).IsHom ((genericSheaf.{u} L).map G) h ↔
          ∃ α : F ⟶ G, α.app (genericSheaf.{u} L).carrier = h := by
  let e := sheafBotEquivalence (C := HornCat.{u} L) (Type (max u₁ u₂ u))
  have he := (e.congrLeft (E := Sheaf K (Type (max u₁ u₂ u)))).fullyFaithfulFunctor
  have hy := bijective_whiskerLeft_yoneda (e.inverse ⋙ F) (e.inverse ⋙ G)
  refine ⟨fun α α' hαα' => ?_, fun h => ⟨fun hh => ?_, ?_⟩⟩
  · apply he.map_injective
    apply hy.1
    exact natTrans_ext _ _ hαα'
  · rw [isHom_map_genericSheaf_iff] at hh
    obtain ⟨γ, hγ⟩ := exists_natTrans_of_isHom hh
    obtain ⟨β, rfl⟩ := hy.2 γ
    exact ⟨he.preimage β, by
      rw [← hγ]
      exact congrArg (fun β : e.inverse ⋙ F ⟶ e.inverse ⋙ G => β.app (yoneda.obj (top 1)))
        (he.map_preimage β)⟩
  · rintro ⟨α, rfl⟩
    exact (genericSheaf.{u} L).isHom_map_app α

variable (L) in
/-- **The Horn site classifies the empty theory.** The presheaf topos on the Horn category, with
the generic structure, classifies the empty geometric theory over `L`. -/
theorem isClassifyingSite_hornCat :
    IsClassifyingSite (∅ : GeometricTheory.{max u₁ u₂ u} L)
      (⊥ : GrothendieckTopology (HornCat.{u} L)) (genericSheaf.{u} L) :=
  ⟨fun _ h => h.elim, fun _ _ _ => ⟨fun M _ => exists_isomorphic_map M,
    fun F G _ _ hF hG => natTrans_app_genericSheaf F G hF hG⟩⟩

end HornCat

end LeanPool.ClassifyingTopoi.Syntactic
