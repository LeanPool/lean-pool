/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Diaconescu

/-!
# Quotients of a theory and topologies on a classifying site (roadmap 2.5)

Let `(C, J)` with the generic model `U` classify a geometric theory `T`, and let `T₁ ⊇ T`. For an
axiom `φ ⊢ ψ` of `T₁`, the sequent holds in `U.map F` (for a left exact left adjoint `F`) iff `F`
inverts the monomorphism `[[φ ∧ ψ]]_U ⟶ [[φ]]_U` (`CatStructure.isModel_map_iff_isIso`). The
topology `quotientTopology U T₁` is the finest topology for which a `J`-sheaf is a sheaf as soon
as it is orthogonal to all pullbacks of these monomorphisms; it is the smallest topology `≥ J`
whose sheafification inverts them (Caramello, *Theories, Sites, Toposes*, 3.2). A left exact
left adjoint `F` out of `Sh(C, J)` maps `U` to a model of `T₁` iff `F` inverts these
monomorphisms and their pullbacks, iff its right adjoint takes values in sheaves for
`quotientTopology U T₁`, iff `F` factors through `Sh(C, quotientTopology U T₁)`
(`LeanPool.ClassifyingTopoi.exists_iso_sheafify_comp`, the localisation half of Diaconescu's
theorem). Hence `(C, quotientTopology U T₁)` with the sheafified generic model classifies `T₁`.

## Main definitions

* `LeanPool.ClassifyingTopoi.CatStructure.sequentMono`: the monomorphism
  `[[φ ∧ ψ]] ⟶ [[φ]]` of a sequent `φ ⊢ ψ`;
* `LeanPool.ClassifyingTopoi.quotientTopology U T₁`: the topology classifying a quotient;
* `LeanPool.ClassifyingTopoi.CatStructure.theory`: the sequents valid in a structure;
* `LeanPool.ClassifyingTopoi.SievesDefinable U`: the `J`-sheafified inclusions of sieves in
  representable presheaves are, as arrows, monomorphisms `[[φ ∧ ψ]]_U ⟶ [[φ]]_U`.

## Main results

* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_quotient_topology` (roadmap 2.5): a
  quotient of a theory classified by `(C, J)` is classified by a finer topology on `C`, with the
  sheafified generic model (`IsClassifyingSite.quotient`, with the topology
  `quotientTopology U T₁`);
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_quotient_theory_of_definable` (converse of
  roadmap 2.5, under definability): a topology `J₁ ≥ J` such that the sheafified inclusions of
  the `J₁`-covering sieves are monomorphisms `[[φ ∧ ψ]]_U ⟶ [[φ]]_U` classifies the theory of
  the sheafified generic model;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_orderEmbedding_quotients_ici`: the
  quotients of `T` embed, as an order, into the topologies finer than `J`;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_orderIso_quotients'`: bridges between
  Morita-equivalent theories, assuming only `SievesDefinable` on the two classifying sites
  instead of `HasQuotientTopologies`.

## Unconditional versions

`SievesDefinable` holds on the Horn sites of `Syntactic/` (`sievesDefinable_genericModel`), but
not on arbitrary classifying sites. The unconditional converse of roadmap 2.5
(`IsClassifyingSite.exists_quotient_theory`) and the unconditional bridges theorem
(`MoritaEquivalent.exists_orderIso_quotients`) are in `Unconditional.lean`: they transport the
topologies along the equivalence of topoi with a Horn site.
-/

@[expose] public section

universe w u₁ u₂ u₃ u₄ u

open CategoryTheory CategoryTheory.Limits LeanPool.ToposTheoreticBridges

namespace LeanPool.ClassifyingTopoi

attribute [local instance high] Sheaf.instHasColimitsOfShape

section Subobject

variable {E : Type*} [Category E]

/-- For monomorphisms `f` and `g`, `g` factors through `f ≫ g` iff `f` is an isomorphism. -/
theorem Subobject.mk_le_mk_comp_iff {A B X : E} (f : A ⟶ B) (g : B ⟶ X) [Mono f] [Mono g] :
    Subobject.mk g ≤ Subobject.mk (f ≫ g) ↔ IsIso f := by
  constructor
  · intro h
    have hk := Subobject.ofMkLEMk_comp h
    have h₁ : Subobject.ofMkLEMk _ _ h ≫ f = 𝟙 _ := by
      rw [← cancel_mono g, Category.assoc, hk, Category.id_comp]
    refine ⟨⟨Subobject.ofMkLEMk _ _ h, ?_, h₁⟩⟩
    rw [← cancel_mono f, Category.assoc, h₁, Category.comp_id, Category.id_comp]
  · intro
    exact (Subobject.mk_eq_mk_of_comm _ _ (asIso f).symm (by simp)).le

end Subobject

variable {L : FirstOrder.Language.{u₁, u₂}}

section Sequent

variable {E : Type*} [Category E] {E' : Type*} [Category E']

/-- `mapSubobject F c S ≤ mapSubobject F c T` for `T ≤ S` iff `F` inverts the inclusion
`T ⟶ S`. -/
theorem mapSubobject_le_iff_isIso {F : E ⥤ E'} [F.PreservesMonomorphisms] {X : E} {Y : E'}
    (c : F.obj X ⟶ Y) [IsIso c] {S T : Subobject X} (h : T ≤ S) :
    mapSubobject F c S ≤ mapSubobject F c T ↔ IsIso (F.map (Subobject.ofLE T S h)) := by
  have e : F.map T.arrow ≫ c = F.map (Subobject.ofLE T S h) ≫ F.map S.arrow ≫ c := by
    rw [← F.map_comp_assoc, Subobject.ofLE_arrow]
  rw [mapSubobject, mapSubobject, Subobject.mk_eq_mk_of_comm _ _ (Iso.refl _) (by simp [e] :
    𝟙 _ ≫ F.map (Subobject.ofLE T S h) ≫ F.map S.arrow ≫ c = F.map T.arrow ≫ c)]
  exact Subobject.mk_le_mk_comp_iff _ _

namespace CatStructure

/-- The monomorphism `[[φ ∧ ψ]] ⟶ [[φ]]` attached to a sequent `φ ⊢ ψ`: the sequent holds in
`M` iff it is an isomorphism, and it holds in `M.map F` iff `F` inverts it
(`isModel_map_iff_isIso`). -/
noncomputable def sequentMono [HasFiniteLimits E] [HasImages E] [HasCoproducts.{w} E]
    (M : CatStructure L E) (σ : Sequent.{w} L) :
    ((M.interp σ.lhs ⊓ M.interp σ.rhs : Subobject (M.pow σ.n)) : E) ⟶
      (M.interp σ.lhs : E) :=
  Subobject.ofLE _ _ inf_le_left

instance [HasFiniteLimits E] [HasImages E] [HasCoproducts.{w} E] (M : CatStructure L E)
    (σ : Sequent.{w} L) : Mono (M.sequentMono σ) := by
  unfold sequentMono
  infer_instance

variable [HasFiniteLimits E] [HasImages E] [HasCoproducts.{w} E] [HasFiniteLimits E']
  [HasImages E'] [HasCoproducts.{w} E'] [StrongEpiCategory E'] (M : CatStructure L E)
  (F : E ⥤ E') [PreservesFiniteLimits F] [F.PreservesEpimorphisms]
  [∀ ι : Type w, PreservesColimitsOfShape (Discrete ι) F]

/-- A sequent holds in `M.map F` iff `F` inverts the monomorphism `[[φ ∧ ψ]] ⟶ [[φ]]`. -/
theorem interp_map_le_iff_isIso (σ : Sequent.{w} L) :
    (M.map F).interp σ.lhs ≤ (M.map F).interp σ.rhs ↔ IsIso (F.map (M.sequentMono σ)) := by
  rw [interp_map, interp_map, sequentMono,
    ← mapSubobject_le_iff_isIso (piComparison F fun _ : Fin σ.n => M.carrier), mapSubobject_inf]
  exact ⟨fun h => le_inf le_rfl h, fun h => h.trans inf_le_right⟩

/-- `M.map F` is a model of `T` iff `F` inverts the monomorphisms `[[φ ∧ ψ]] ⟶ [[φ]]` of the
axioms `φ ⊢ ψ` of `T`. -/
theorem isModel_map_iff_isIso (T : GeometricTheory.{w} L) :
    (M.map F).IsModel T ↔ ∀ σ ∈ T, IsIso (F.map (M.sequentMono σ)) :=
  forall₂_congr fun σ _ => M.interp_map_le_iff_isIso F σ

end CatStructure

end Sequent

namespace CatStructure

section MapComp

variable {E : Type*} [Category E] {E' : Type*} [Category E'] {E'' : Type*} [Category E'']
  [HasFiniteProducts E] [HasFiniteProducts E'] [HasFiniteLimits E''] [HasImages E'']
  (M : CatStructure L E) (F : E ⥤ E') (G : E' ⥤ E'')
  [PreservesFiniteProducts F] [PreservesFiniteProducts G]

/-- Homomorphisms between the images of a structure under composite functors `F ⋙ G` and
`F ⋙ G'` are the homomorphisms between the iterated images. -/
theorem isHom_map_comp_iff (G' : E' ⥤ E'') [PreservesFiniteProducts G']
    (k : G.obj (F.obj M.carrier) ⟶ G'.obj (F.obj M.carrier)) :
    (M.map (F ⋙ G)).IsHom (M.map (F ⋙ G')) k ↔ ((M.map F).map G).IsHom ((M.map F).map G') k := by
  constructor
  · intro hk
    simpa using ((M.isHom_map_comp_inv F G).comp hk).comp (M.isHom_map_comp_hom F G')
  · intro hk
    simpa using ((M.isHom_map_comp_hom F G).comp hk).comp (M.isHom_map_comp_inv F G')

end MapComp

end CatStructure

section Quotient

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (U : CatStructure L (Sheaf J (Type u))) (T₁ : GeometricTheory.{u} L)

/-- The topology on `C` classifying the quotient `T₁` of a theory classified by `(C, J, U)`:
the finest topology for which every `J`-sheaf `G` is a sheaf as soon as all pullbacks of the
monomorphisms `[[φ ∧ ψ]]_U ⟶ [[φ]]_U`, for the axioms `φ ⊢ ψ` of `T₁`, are orthogonal to `G`.
Equivalently, the smallest topology finer than `J` for which these monomorphisms become
isomorphisms after sheafification (`isIso_sheafify_map_sequentMono`,
`isSheaf_rightAdjoint_of_isModel`). -/
def quotientTopology : GrothendieckTopology C :=
  topologyOfSheaves J fun G => ∀ σ ∈ T₁, IsDenseFor (fun X => X = G) (U.sequentMono σ)

/-- The topology classifying a quotient is finer than `J`. -/
theorem le_quotientTopology : J ≤ quotientTopology U T₁ :=
  le_topologyOfSheaves _

/-- Sheafification for `quotientTopology U T₁` inverts the monomorphisms
`[[φ ∧ ψ]]_U ⟶ [[φ]]_U` of the axioms `φ ⊢ ψ` of `T₁`. -/
theorem isIso_sheafify_map_sequentMono {σ : Sequent.{u} L} (hσ : σ ∈ T₁) :
    IsIso ((sheafToPresheaf J (Type u) ⋙ presheafToSheaf (quotientTopology U T₁) (Type u)).map
      (U.sequentMono σ)) := by
  refine isIso_of_forall_isOrthogonal _ fun Y => ?_
  rw [isOrthogonal_map_iff_of_adjunction (sheafifyAdjunction (le_quotientTopology U T₁))]
  have hY := (isLocalFor_iff_isSheaf J _ ((sheafInclusion (le_quotientTopology U T₁)).obj Y)).2
    Y.property
  exact hY _ ⟨inferInstance, fun _ _ t n a hp H hH => (hH σ hσ).2 t n a hp H rfl⟩

/-- The sheafified generic model is a model of `T₁` in `Sh(C, quotientTopology U T₁)`. -/
theorem isModel_sheafify_quotientTopology :
    (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf (quotientTopology U T₁) (Type u))).IsModel
      T₁ :=
  have := isLeftAdjoint_sheafify (le_quotientTopology U T₁)
  (U.isModel_map_iff_isIso _ T₁).2 fun _ hσ => isIso_sheafify_map_sequentMono U T₁ hσ

/-- If a left exact left adjoint `F` out of `Sh(C, J)` maps `U` to a model of `T₁`, its right
adjoint takes values in sheaves for `quotientTopology U T₁`. -/
theorem isSheaf_rightAdjoint_of_isModel {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteLimits F] [F.IsLeftAdjoint] (hF : (U.map F).IsModel T₁)
    (Y : Sheaf K (Type u)) :
    Presheaf.IsSheaf (quotientTopology U T₁) (F.rightAdjoint.obj Y).obj := by
  rw [isSheaf_iff_isSheaf_of_type]
  refine isSheaf_topologyOfSheaves fun σ hσ => ?_
  have := (U.isModel_map_iff_isIso F T₁).1 hF σ hσ
  exact (isDenseFor_of_isIso_map_of_adjunction (Adjunction.ofIsLeftAdjoint F) _).mono_class
    fun X hX => ⟨Y, hX⟩

/-- `quotientTopology U T₁` is the smallest topology `J₁ ≥ J` whose sheafification
`Sh(C, J) ⥤ Sh(C, J₁)` inverts the monomorphisms `[[φ ∧ ψ]]_U ⟶ [[φ]]_U` of the axioms
`φ ⊢ ψ` of `T₁`. -/
theorem quotientTopology_le_iff {J₁ : GrothendieckTopology C} (h : J ≤ J₁) :
    quotientTopology U T₁ ≤ J₁ ↔ ∀ σ ∈ T₁,
      IsIso ((sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)).map
        (U.sequentMono σ)) := by
  constructor
  · intro hle σ hσ
    refine isIso_of_forall_isOrthogonal _ fun Y => ?_
    rw [isOrthogonal_map_iff_of_adjunction (sheafifyAdjunction h)]
    have hY := (isLocalFor_iff_isSheaf J _ ((sheafInclusion h).obj Y)).2
      (Y.property.of_le hle)
    exact hY _ ⟨inferInstance, fun _ _ t n a hp H hH => (hH σ hσ).2 t n a hp H rfl⟩
  · intro hT
    refine (le_iff_forall_isSheaf h).2 fun G hG => (isSheaf_iff_isSheaf_of_type _ _).2
      (isSheaf_topologyOfSheaves fun σ hσ => ?_)
    have := hT σ hσ
    exact (isDenseFor_of_isIso_map_of_adjunction (sheafifyAdjunction h) _).mono_class
      fun X hX => ⟨⟨G.obj, hG⟩, hX⟩

end Quotient

namespace IsClassifyingSite

variable {T : GeometricTheory.{u} L} {C : Type u} [SmallCategory C]
  {J : GrothendieckTopology C} {U : CatStructure L (Sheaf J (Type u))}

/-- For `J ≤ J₁`, if `(C, J, U)` is a classifying site, natural transformations between two
inverse images out of `Sh(C, J₁)` are determined by their component at the sheafified
generic model, and these components are exactly the homomorphisms of the image models. -/
theorem sheafify_hom {J₁ : GrothendieckTopology C} (hU : IsClassifyingSite T J U)
    (h : J ≤ J₁) {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (F G : Sheaf J₁ (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]
    [PreservesFiniteLimits G] (hF : F.IsLeftAdjoint) (hG : G.IsLeftAdjoint) :
    Function.Injective (fun α : F ⟶ G =>
        α.app (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))).carrier) ∧
      ∀ k : F.obj (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))).carrier ⟶
          G.obj (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))).carrier,
        ((U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))).map F).IsHom
            ((U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))).map G) k ↔
          ∃ α : F ⟶ G, α.app
            (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))).carrier = k := by
  let a := sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)
  have hFa : (a ⋙ F).IsLeftAdjoint :=
    ((sheafifyAdjunction h).comp (Adjunction.ofIsLeftAdjoint F)).isLeftAdjoint
  have hGa : (a ⋙ G).IsLeftAdjoint :=
    ((sheafifyAdjunction h).comp (Adjunction.ofIsLeftAdjoint G)).isLeftAdjoint
  obtain ⟨hinj, hhom⟩ := (hU.2 D K).2 (a ⋙ F) (a ⋙ G) hFa hGa
  obtain ⟨hw₁, hw₂⟩ := bijective_whiskerLeft_sheafify h F G
  refine ⟨fun α β hαβ => hw₁ (hinj hαβ), fun k => ?_⟩
  rw [← U.isHom_map_comp_iff a F G, hhom k]
  constructor
  · rintro ⟨α, rfl⟩
    obtain ⟨β, rfl⟩ := hw₂ α
    exact ⟨β, rfl⟩
  · rintro ⟨α, rfl⟩
    exact ⟨Functor.whiskerLeft a α, rfl⟩

/-- A quotient `T₁` of a theory classified by `(C, J, U)` is classified by
`quotientTopology U T₁`, with the sheafified generic model. -/
theorem quotient {T₁ : GeometricTheory.{u} L} (hU : IsClassifyingSite T J U)
    (hT : T ⊆ T₁) :
    IsClassifyingSite T₁ (quotientTopology U T₁)
      (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf (quotientTopology U T₁) (Type u))) := by
  have h := le_quotientTopology U T₁
  refine ⟨isModel_sheafify_quotientTopology U T₁, fun D _ K => ⟨fun M hM => ?_,
    fun F G _ _ hF hG => hU.sheafify_hom h F G hF hG⟩⟩
  obtain ⟨F, _, hF, hMF⟩ := hU.exists_isomorphic fun σ hσ => hM σ (hT hσ)
  obtain ⟨F', _, hF', ⟨e⟩⟩ := exists_iso_sheafify_comp h F
    (isSheaf_rightAdjoint_of_isModel U T₁ F (hMF.isModel hM))
  exact ⟨F', inferInstance, hF',
    hMF.trans ((U.isomorphic_map_of_iso e).trans (U.isomorphic_map_comp _ _))⟩

/-- **Roadmap 2.5.** A quotient of a theory classified by `(C, J)` is classified by a finer
topology on `C`, with the sheafified generic model. -/
theorem exists_quotient_topology {T' : GeometricTheory.{u} L} (hT : T ⊆ T')
    (hU : IsClassifyingSite T J U) :
    ∃ J' : GrothendieckTopology C, J ≤ J' ∧
      IsClassifyingSite T' J' (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J' (Type u))) :=
  ⟨_, le_quotientTopology U T', hU.quotient hT⟩

end IsClassifyingSite

namespace CatStructure

variable {E : Type*} [Category E] [HasFiniteLimits E] [HasImages E] [HasCoproducts.{w} E]

/-- The geometric theory of a structure: the sequents valid in it. -/
def theory (M : CatStructure L E) : GeometricTheory.{w} L :=
  {σ | M.interp σ.lhs ≤ M.interp σ.rhs}

/-- A structure is a model of its theory. -/
theorem isModel_theory (M : CatStructure L E) : M.IsModel M.theory :=
  fun _ hσ => hσ

end CatStructure

section Converse

variable {T : GeometricTheory.{u} L} {C : Type u} [SmallCategory C]
  {J : GrothendieckTopology C} {U : CatStructure L (Sheaf J (Type u))}

/-- **Roadmap 2.5, converse, under definability.** Let `(C, J, U)` classify `T` and `J₁ ≥ J`.
Assume that, for every `J₁`-covering sieve `S`, the `J`-sheafification of the inclusion of `S`
in the representable presheaf is isomorphic, as an arrow, to the monomorphism
`[[φ ∧ ψ]]_U ⟶ [[φ]]_U` of some sequent `φ ⊢ ψ` (this holds on the syntactic site, by the
definability of subobjects of the generic model, roadmap 2.4). Then the topology classifying
the theory of the sheafified generic model is `J₁`. -/
theorem quotientTopology_theory_eq {J₁ : GrothendieckTopology C} (h : J ≤ J₁)
    (hdef : ∀ (X : C) (S : Sieve X), S ∈ J₁ X → ∃ σ : Sequent.{u} L,
      Nonempty (Arrow.mk ((presheafToSheaf J (Type u)).map S.functorInclusion) ≅
        Arrow.mk (U.sequentMono σ))) :
    quotientTopology U
      (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))).theory = J₁ := by
  have := isLeftAdjoint_sheafify h
  set T' := (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))).theory
  have hT' : ∀ σ, σ ∈ T' ↔
      IsIso ((sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)).map (U.sequentMono σ)) :=
    fun σ => U.interp_map_le_iff_isIso _ σ
  have h' := le_quotientTopology U T'
  apply le_antisymm
  · exact (quotientTopology_le_iff U T' h).2 fun σ hσ => (hT' σ).1 hσ
  · refine (le_iff_forall_isSheaf h').2 fun G hG => (isSheaf_iff_isSheaf_of_type _ _).2
      fun X S hS => ?_
    obtain ⟨σ, ⟨e⟩⟩ := hdef X S hS
    have hσ : σ ∈ T' := (hT' σ).2 (isIso_of_forall_isOrthogonal _ fun Y => by
      rw [isOrthogonal_map_iff_of_adjunction (sheafifyAdjunction h)]
      exact isOrthogonal_of_arrow_iso e (isOrthogonal_sheafify_functorInclusion h hS Y))
    have := isIso_sheafify_map_sequentMono U T' hσ
    have hG' : IsOrthogonal (U.sequentMono σ) G :=
      (isOrthogonal_map_iff_of_adjunction (sheafifyAdjunction h') _ ⟨G.obj, hG⟩).1
        (Subtopos.isOrthogonal_of_isIso _ _)
    have := isOrthogonal_of_arrow_iso e.symm hG'
    rw [isOrthogonal_map_iff_of_adjunction (sheafificationAdjunction J (Type u))] at this
    exact Presieve.isSheafFor_iff_yonedaSheafCondition.2 this

namespace IsClassifyingSite

/-- **Roadmap 2.5, converse, under definability.** Under the definability hypothesis of
`quotientTopology_theory_eq`, a topology `J₁ ≥ J` on a classifying site of `T` classifies a
quotient of `T` (the theory of the sheafified generic model), with the sheafified generic
model. -/
theorem exists_quotient_theory_of_definable (hU : IsClassifyingSite T J U)
    {J₁ : GrothendieckTopology C} (h : J ≤ J₁)
    (hdef : ∀ (X : C) (S : Sieve X), S ∈ J₁ X → ∃ σ : Sequent.{u} L,
      Nonempty (Arrow.mk ((presheafToSheaf J (Type u)).map S.functorInclusion) ≅
        Arrow.mk (U.sequentMono σ))) :
    ∃ T₁ : GeometricTheory.{u} L, T ⊆ T₁ ∧ IsClassifyingSite T₁ J₁
      (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))) := by
  have := isLeftAdjoint_sheafify h
  have hT : T ⊆ (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))).theory :=
    fun σ hσ => hU.isModel.map _ σ hσ
  have hc := hU.quotient hT
  rw [quotientTopology_theory_eq h hdef] at hc
  exact ⟨_, hT, hc⟩

end IsClassifyingSite

end Converse

section Bridges

variable {T : GeometricTheory.{u} L} {C : Type u} [SmallCategory C]
  {J : GrothendieckTopology C}

variable (U : CatStructure L (Sheaf J (Type u))) in
/-- Definability of sieves for a structure `U` in `Sh(C, J)`: for every sieve `S`, covering or
not, on an object of `C`, the `J`-sheafification of the inclusion of `S` in the representable
presheaf is isomorphic, as an arrow, to the monomorphism `[[φ ∧ ψ]]_U ⟶ [[φ]]_U` of some
sequent. This holds for the generic model on the Horn sites (`sievesDefinable_genericModel`), not
on every classifying site. -/
def SievesDefinable : Prop :=
  ∀ (X : C) (S : Sieve X), ∃ σ : Sequent.{u} L,
    Nonempty (Arrow.mk ((presheafToSheaf J (Type u)).map S.functorInclusion) ≅
      Arrow.mk (U.sequentMono σ))

namespace IsClassifyingSite

variable {U : CatStructure L (Sheaf J (Type u))}

/-- Under the definability of sieves, the correspondence of roadmap 2.5 holds on a classifying
site. -/
theorem hasQuotientTopologies (hU : IsClassifyingSite T J U) (hdef : SievesDefinable U) :
    HasQuotientTopologies T J U :=
  ⟨fun _ hT => hU.exists_quotient_topology hT,
    fun _ h => hU.exists_quotient_theory_of_definable h fun X S _ => hdef X S⟩

/-- The quotients of a theory with a classifying site `(C, J, U)` embed into the topologies
finer than `J`, each quotient being classified by the corresponding topology with the
sheafified generic model. -/
theorem exists_orderEmbedding_quotients_ici (hU : IsClassifyingSite T J U) :
    ∃ Φ : T.Quotients ↪o Set.Ici J, ∀ T₁ : T.QuotientTheory,
      IsClassifyingSite T₁.1 (Φ (toAntisymmetrization _ T₁)).1
        (U.map (sheafToPresheaf J (Type u) ⋙
          presheafToSheaf (Φ (toAntisymmetrization _ T₁)).1 (Type u))) := by
  obtain ⟨Φ, hΦ⟩ := hU.exists_orderEmbedding_of_isClassifyingSite
    (fun T₁ => quotientTopology U T₁.1) (fun T₁ => le_quotientTopology U T₁.1)
    fun T₁ => hU.quotient T₁.2
  exact ⟨Φ, fun T₁ => (hΦ T₁).2⟩

/-- **Bridges between theories, under definability.** Let `T` and `T'` be Morita-equivalent
theories, classified by `(C, J, U)` and `(D, K, U')` on which all sieves are definable
(`SievesDefinable`, true on syntactic sites). Then the quotients of `T` and of `T'` are order
isomorphic, by an isomorphism carrying each quotient of `T` to a Morita-equivalent quotient of
`T'`. -/
theorem exists_orderIso_quotients' {L' : FirstOrder.Language.{u₃, u₄}}
    {T' : GeometricTheory.{u} L'} {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {U' : CatStructure L' (Sheaf K (Type u))} (hU : IsClassifyingSite T J U)
    (hU' : IsClassifyingSite T' K U') (hdef : SievesDefinable U) (hdef' : SievesDefinable U')
    (h : MoritaEquivalent T T') :
    ∃ Ψ : T.Quotients ≃o T'.Quotients, ∀ (T₁ : T.QuotientTheory) (T₂ : T'.QuotientTheory),
      Ψ (toAntisymmetrization _ T₁) = toAntisymmetrization _ T₂ →
        MoritaEquivalent T₁.1 T₂.1 :=
  hU.exists_orderIso_quotients hU' (hU.hasQuotientTopologies hdef)
    (hU'.hasQuotientTopologies hdef') h

end IsClassifyingSite

end Bridges

end LeanPool.ClassifyingTopoi
