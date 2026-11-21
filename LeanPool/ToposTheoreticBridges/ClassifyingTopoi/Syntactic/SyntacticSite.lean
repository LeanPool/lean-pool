/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Definability
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Universal

/-!
# The Horn sites: definability of subobjects (roadmap 2.4)

For a topology `J` on the Horn category, `HornCat.genericModel J` is the sheafification of the
generic structure. Every subobject of one of its powers is the interpretation of a geometric
formula (`HornCat.exists_interp_genericModel_eq`), since every subobject of a sheafified presheaf
is the sheafification of a subobject of the presheaf (`exists_mapSubobject_eq`) and subobjects of
powers of the generic presheaf structure are definable (`HornCat.exists_interp_genericPsh_eq`).

Consequently the sheafified inclusions of sieves in representable presheaves are, as arrows, the
monomorphisms `[[φ ∧ ψ]] ⟶ [[φ]]` of sequents (`HornCat.sievesDefinable_genericModel`): the
sheafified representable `a(y X)` is the interpretation of the Horn formula `X`. With the topology
`quotientTopology (genericSheaf L) T` this is the classifying site of a geometric theory `T`
(`HornCat.isClassifyingSite_genericModel`), on which the correspondence between quotients of `T`
and topologies finer than the classifying topology holds (`HornCat.hasQuotientTopologies`).
-/

@[expose] public section

universe u u₁ u₂

namespace LeanPool.ClassifyingTopoi.Syntactic

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits LeanPool.ClassifyingTopoi
  Opposite

attribute [local instance high] Sheaf.instHasColimitsOfShape

variable {L : Language.{u₁, u₂}}

namespace HornCat

variable (J : GrothendieckTopology (HornCat.{u} L))

/-- The sheafification of the generic structure for a topology on the Horn category. -/
noncomputable abbrev genericModel : CatStructure L (Sheaf J (Type (max u₁ u₂ u))) :=
  (genericSheaf.{u} L).map (sheafToPresheaf (⊥ : GrothendieckTopology (HornCat.{u} L)) _ ⋙
    presheafToSheaf J (Type (max u₁ u₂ u)))

/-- The interpretations in the sheafified generic structure are the sheafifications of the
interpretations in the generic presheaf structure. -/
theorem interp_genericModel {n : ℕ} (ψ : GeometricFormula.{max u₁ u₂ u} L n) :
    (genericModel J).interp ψ =
      mapSubobject (presheafToSheaf J (Type (max u₁ u₂ u)))
        (piComparison _ fun _ : Fin n => (genericPsh.{u} L).carrier)
        ((genericPsh.{u} L).interp ψ) := by
  have h₁ := ((genericPsh.{u} L).isHom_map_comp_hom (sheafBotEquivalence _).inverse
    (sheafToPresheaf (⊥ : GrothendieckTopology (HornCat.{u} L)) _ ⋙
      presheafToSheaf J (Type (max u₁ u₂ u)))).interp_le ψ
  have h₂ := ((genericPsh.{u} L).isHom_map_comp_inv (sheafBotEquivalence _).inverse
    (sheafToPresheaf (⊥ : GrothendieckTopology (HornCat.{u} L)) _ ⋙
      presheafToSheaf J (Type (max u₁ u₂ u)))).interp_le ψ
  simp only [Limits.Pi.map_id, Subobject.pullback_id] at h₁ h₂
  exact (le_antisymm h₂ h₁).trans
    (CatStructure.interp_map (genericPsh.{u} L) (presheafToSheaf J (Type (max u₁ u₂ u))) ψ)

/-- **Definability (roadmap 2.4) on the Horn sites.** Every subobject of a power of the sheafified
generic structure is the interpretation of a geometric formula. -/
theorem exists_interp_genericModel_eq {n : ℕ} (S : Subobject ((genericModel J).pow n)) :
    ∃ ψ : GeometricFormula.{max u₁ u₂ u} L n, (genericModel J).interp ψ = S := by
  obtain ⟨Q, hQ⟩ := exists_mapSubobject_eq (sheafificationAdjunction J (Type (max u₁ u₂ u)))
    (piComparison _ fun _ : Fin n => (genericPsh.{u} L).carrier) S
  obtain ⟨ψ, hψ⟩ := exists_interp_genericPsh_eq Q
  exact ⟨ψ, by rw [interp_genericModel, hψ, hQ]⟩

/-- The interpretation of a Horn formula in the sheafified generic structure is the sheafified
representable presheaf. -/
theorem interp_toFormula_genericModel (X : HornCat.{u} L) :
    (genericModel J).interp X.toFormula =
      Subobject.mk ((presheafToSheaf J (Type (max u₁ u₂ u))).map
        (yoneda.map (ι X) ≫ (isoPow (yoneda : HornCat.{u} L ⥤ _) X.n).hom) ≫
          piComparison _ fun _ : Fin X.n => (genericPsh.{u} L).carrier) := by
  rw [interp_genericModel, interp_toFormula_genericPsh, mapSubobject_mk]

theorem _root_.LeanPool.ClassifyingTopoi.Syntactic.isoOfEq_hom_arrow {C : Type*} [Category C]
    {B : C} (X Y : Subobject B) (h : X = Y) : (Subobject.isoOfEq X Y h).hom ≫ Y.arrow = X.arrow :=
  Subobject.ofLE_arrow _

/-- **Definability of sieves on the Horn sites.** The sheafified inclusion of a sieve in a
representable presheaf is, as an arrow, the monomorphism `[[φ ∧ ψ]] ⟶ [[φ]]` of a sequent. -/
theorem sievesDefinable_genericModel : SievesDefinable (genericModel J) := by
  intro X S
  let f := (presheafToSheaf J (Type (max u₁ u₂ u))).map
    (yoneda.map (ι X) ≫ (isoPow (yoneda : HornCat.{u} L ⥤ _) X.n).hom) ≫
      piComparison (presheafToSheaf J (Type (max u₁ u₂ u))) fun _ : Fin X.n =>
        (genericPsh.{u} L).carrier
  have hI := interp_toFormula_genericModel J X
  have : Mono f := inferInstance
  have : Mono ((presheafToSheaf J (Type (max u₁ u₂ u))).map S.functorInclusion ≫ f) :=
    inferInstance
  let T := Subobject.mk ((presheafToSheaf J (Type (max u₁ u₂ u))).map S.functorInclusion ≫ f)
  obtain ⟨ψ, hψ⟩ := exists_interp_genericModel_eq J T
  refine ⟨⟨X.n, X.toFormula, ψ⟩, ⟨?_⟩⟩
  have hTI : T ≤ (genericModel J).interp X.toFormula := by
    rw [hI]
    exact Subobject.mk_le_mk_of_comm ((presheafToSheaf J (Type (max u₁ u₂ u))).map
      S.functorInclusion) rfl
  have hinf : (genericModel J).interp X.toFormula ⊓ (genericModel J).interp ψ = T := by
    rw [hψ]
    exact inf_eq_right.2 hTI
  refine Arrow.isoMk ((Subobject.underlyingIso
      ((presheafToSheaf J (Type (max u₁ u₂ u))).map S.functorInclusion ≫ f)).symm ≪≫
        Subobject.isoOfEq _ _ hinf.symm)
    ((Subobject.underlyingIso f).symm ≪≫ Subobject.isoOfEq _ _ hI.symm) ?_
  rw [← cancel_mono ((genericModel J).interp X.toFormula).arrow]
  simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, CatStructure.sequentMono,
    Category.assoc, Subobject.ofLE_arrow]
  erw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc,
    Category.assoc, isoOfEq_hom_arrow, isoOfEq_hom_arrow, Subobject.underlyingIso_arrow,
    Subobject.underlyingIso_arrow]
  rfl

end HornCat

variable (L) in
/-- The syntactic site of a geometric theory: the Horn category with the topology classifying the
theory as a quotient of the empty theory, with the sheafified generic structure, classifies it. -/
theorem HornCat.isClassifyingSite_genericModel (T : GeometricTheory.{max u₁ u₂ u} L) :
    IsClassifyingSite T (quotientTopology (HornCat.genericSheaf.{u} L) T)
      (HornCat.genericModel (quotientTopology (HornCat.genericSheaf.{u} L) T)) :=
  (HornCat.isClassifyingSite_hornCat L).quotient (Set.empty_subset T)

/-- On the syntactic site of a theory, the quotients of the theory correspond to the topologies
finer than the classifying topology (roadmap 2.5, both directions). -/
theorem HornCat.hasQuotientTopologies (T : GeometricTheory.{max u₁ u₂ u} L) :
    IsClassifyingSite.HasQuotientTopologies T (quotientTopology (HornCat.genericSheaf.{u} L) T)
      (HornCat.genericModel (quotientTopology (HornCat.genericSheaf.{u} L) T)) :=
  (HornCat.isClassifyingSite_genericModel L T).hasQuotientTopologies
    (HornCat.sievesDefinable_genericModel _)

end LeanPool.ClassifyingTopoi.Syntactic
