/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.ClassifyingSite
public import LeanPool.ToposTheoreticBridges.Sites
public import LeanPool.ToposTheoreticBridges.Subtopos
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Order.Antisymmetrization

/-!
# Quotients of a theory and topologies on a classifying site; bridges between theories

Let `(C, J)` with the generic model `U` classify a geometric theory `T`. For a topology
`J₁ ≥ J`, the sheafified model `U.map (sheafToPresheaf J _ ⋙ presheafToSheaf J₁ _)` lives in
`Sh(C, J₁)`. This file compares the quotients of `T` with the topologies `J₁ ≥ J`, assuming the
correspondence of roadmap 2.5 for the site (`IsClassifyingSite.HasQuotientTopologies`: every
quotient of `T` is classified by some finer topology with the sheafified model, and every finer
topology classifies some quotient), and deduces the bridges between Morita-equivalent theories.

## Main definitions

* `LeanPool.ClassifyingTopoi.sheafInclusion`: for `J ≤ J₁`, the inclusion of `J₁`-sheaves among
  `J`-sheaves, right adjoint to `sheafToPresheaf J _ ⋙ presheafToSheaf J₁ _`
  (`sheafifyAdjunction`);
* `LeanPool.ClassifyingTopoi.GeometricTheory.QuotientTheory T`: the theories containing `T`,
  preordered by `T₁ ≤ T₂` when every model of `T₂` in a sheaf topos is a model of `T₁`;
  `GeometricTheory.Quotients T` is its antisymmetrization, the quotients of `T` up to having the
  same models in every topos of sheaves on a small site;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.HasQuotientTopologies`: the conclusions of
  roadmap 2.5 (`IsClassifyingSite.exists_quotient_topology` and `exists_quotient_theory`) for a
  given classifying site.

## Main results

* `LeanPool.ClassifyingTopoi.IsClassifyingSite.le_iff_forall_isModel`: for topologies
  `J₁, J₂ ≥ J` classifying `T₁, T₂` with the sheafified generic model, `J₁ ≤ J₂` iff every model
  of `T₂` is a model of `T₁`. One direction composes sheafifications; the other uses the
  universal property to identify the sheafification functor to `J₂` with a functor factoring
  through `Sh(C, J₁)`, so that by uniqueness of right adjoints every `J₂`-sheaf is a `J₁`-sheaf;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_orderIso_quotients_ici`: under
  `HasQuotientTopologies`, the quotients of `T` are order isomorphic to `Set.Ici J`, each
  quotient being classified by the corresponding topology;
* `LeanPool.ClassifyingTopoi.nonempty_sheafEquiv_of_isSheaf_iff`: an equivalence
  `Sh(C, J) ≌ Sh(D, K)` matching the `J₁`-sheaves with the `K₁`-sheaves restricts to an
  equivalence `Sh(C, J₁) ≌ Sh(D, K₁)`;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_orderIso_quotients` (bridges between
  theories): if `T` and `T'` are Morita-equivalent, with classifying sites satisfying
  `HasQuotientTopologies`, their quotients are order isomorphic, by an isomorphism carrying each
  quotient to a Morita-equivalent quotient. It combines the above with
  `LeanPool.ToposTheoreticBridges.exists_orderIso_ici_of_sheafEquiv`.

## What is assumed

The hypothesis `HasQuotientTopologies` is roadmap 2.5 for the given site, a theorem of the
theory of classifying topoi (Caramello, *Theories, Sites, Toposes*, Theorem 3.2.5) whose proof
needs the syntactic site and Diaconescu's theorem; it is not proved here.
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u

open CategoryTheory CategoryTheory.Limits

namespace LeanPool.ClassifyingTopoi

attribute [local instance high] Sheaf.instHasColimitsOfShape

section Sheafification

variable {C : Type u} [SmallCategory C] {J J₁ : GrothendieckTopology C}

/-- For `J ≤ J₁`, the inclusion of the `J₁`-sheaves among the `J`-sheaves
(`LeanPool.ToposTheoreticBridges.sheafInclusionOfLE`). -/
abbrev sheafInclusion (h : J ≤ J₁) : Sheaf J₁ (Type u) ⥤ Sheaf J (Type u) :=
  ToposTheoreticBridges.sheafInclusionOfLE h

/-- For `J ≤ J₁`, sheafification of `J`-sheaves for `J₁` is left adjoint to the inclusion
(`LeanPool.ToposTheoreticBridges.sheafInclusionOfLEAdjunction`). -/
noncomputable abbrev sheafifyAdjunction (h : J ≤ J₁) :
    sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u) ⊣ sheafInclusion h :=
  ToposTheoreticBridges.sheafInclusionOfLEAdjunction h

/-- Sheafification of `J`-sheaves for `J₁ ≥ J` is the inverse image of a geometric morphism. -/
theorem isLeftAdjoint_sheafify (h : J ≤ J₁) :
    (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)).IsLeftAdjoint :=
  (sheafifyAdjunction h).isLeftAdjoint

end Sheafification

variable {L : FirstOrder.Language.{u₁, u₂}}

namespace GeometricTheory

/-- The theories containing `T`, to be considered up to having the same models. -/
def QuotientTheory (T : GeometricTheory.{u} L) : Type _ :=
  {T₁ : GeometricTheory.{u} L // T ⊆ T₁}

/-- `T₁ ≤ T₂` when every model of `T₂` in a topos of sheaves on a small site is a model of
`T₁`: `T₂` is a quotient of `T₁` up to equivalence. -/
instance (T : GeometricTheory.{u} L) : Preorder (QuotientTheory T) where
  le T₁ T₂ := ∀ (D : Type u) [SmallCategory D] (K : GrothendieckTopology D)
    (M : CatStructure L (Sheaf K (Type u))), M.IsModel T₂.1 → M.IsModel T₁.1
  le_refl _ _ _ _ _ h := h
  le_trans _ _ _ h₁ h₂ D _ K M h := h₁ D K M (h₂ D K M h)

/-- The quotients of `T`, up to having the same models in every topos of sheaves on a small
site. -/
abbrev Quotients (T : GeometricTheory.{u} L) : Type _ :=
  Antisymmetrization (QuotientTheory T) (· ≤ ·)

end GeometricTheory

namespace IsClassifyingSite

variable {T : GeometricTheory.{u} L} {C : Type u} [SmallCategory C]
  {J : GrothendieckTopology C} {U : CatStructure L (Sheaf J (Type u))}

/-- For topologies `J₁, J₂ ≥ J` classifying `T₁, T₂` with the sheafified generic model,
`J₁ ≤ J₂` iff every model of `T₂` is a model of `T₁`. -/
theorem le_iff_forall_isModel (hU : IsClassifyingSite T J U) {J₁ J₂ : GrothendieckTopology C}
    (h₁ : J ≤ J₁) (h₂ : J ≤ J₂) {T₁ T₂ : GeometricTheory.{u} L}
    (hU₁ : IsClassifyingSite T₁ J₁
      (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))))
    (hU₂ : IsClassifyingSite T₂ J₂
      (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₂ (Type u)))) :
    J₁ ≤ J₂ ↔ ∀ (D : Type u) [SmallCategory D] (K : GrothendieckTopology D)
      (M : CatStructure L (Sheaf K (Type u))), M.IsModel T₂ → M.IsModel T₁ := by
  have := isLeftAdjoint_sheafify h₁
  have := isLeftAdjoint_sheafify h₂
  constructor
  · intro hJ D _ K M hM
    have := isLeftAdjoint_sheafify hJ
    let P := sheafToPresheaf J₁ (Type u) ⋙ presheafToSheaf J₂ (Type u)
    have adj : (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)) ⋙ P ⊣
        sheafInclusion h₂ :=
      ((sheafifyAdjunction h₁).comp (sheafifyAdjunction hJ)).ofNatIsoRight
        (NatIso.ofComponents fun _ => Iso.refl _)
    have α := (sheafifyAdjunction h₂).leftAdjointUniq adj
    have hU₂₁ : (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₂ (Type u))).IsModel T₁ :=
      ((U.isomorphic_map_of_iso α).trans (U.isomorphic_map_comp _ P)).symm.isModel
        (hU₁.isModel.map P)
    obtain ⟨F, _, _, hMF⟩ := hU₂.exists_isomorphic hM
    exact hMF.symm.isModel (hU₂₁.map F)
  · intro hle
    obtain ⟨F, _, hF, hF'⟩ := hU₁.exists_isomorphic (hle C J₂ _ hU₂.isModel)
    obtain ⟨α⟩ := hU.nonempty_iso _ _ inferInstance inferInstance
      (hF'.trans (U.isomorphic_map_comp _ F).symm)
    have adj := ((sheafifyAdjunction h₁).comp (Adjunction.ofIsLeftAdjoint F)).ofNatIsoLeft α.symm
    have β := (sheafifyAdjunction h₂).rightAdjointUniq adj
    refine (LeanPool.ToposTheoreticBridges.le_iff_forall_isSheaf h₂).2 fun G hG => ?_
    let X : Sheaf J₂ (Type u) := ⟨G.obj, hG⟩
    exact (Presheaf.isSheaf_of_iso_iff (J := J₁)
      ((sheafToPresheaf J (Type u)).mapIso (β.app X))).2
      (F.rightAdjoint.obj X).property

/-- A topology finer than `J` classifying a theory with the sheafified generic model is
determined by the models of the theory. -/
theorem eq_iff_forall_isModel (hU : IsClassifyingSite T J U) {J₁ J₂ : GrothendieckTopology C}
    (h₁ : J ≤ J₁) (h₂ : J ≤ J₂) {T₁ T₂ : GeometricTheory.{u} L}
    (hU₁ : IsClassifyingSite T₁ J₁
      (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))))
    (hU₂ : IsClassifyingSite T₂ J₂
      (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₂ (Type u)))) :
    J₁ = J₂ ↔ ∀ (D : Type u) [SmallCategory D] (K : GrothendieckTopology D)
      (M : CatStructure L (Sheaf K (Type u))), M.IsModel T₁ ↔ M.IsModel T₂ := by
  rw [le_antisymm_iff, hU.le_iff_forall_isModel h₁ h₂ hU₁ hU₂,
    hU.le_iff_forall_isModel h₂ h₁ hU₂ hU₁]
  exact ⟨fun h D _ K M => ⟨h.2 D K M, h.1 D K M⟩,
    fun h => ⟨fun D _ K M => (h D K M).2, fun D _ K M => (h D K M).1⟩⟩

variable (T J U) in
/-- The correspondence of roadmap 2.5 for a classifying site: every quotient of `T` is
classified by a topology finer than `J` with the sheafified generic model, and every topology
finer than `J` classifies a quotient of `T` with the sheafified generic model. -/
def HasQuotientTopologies : Prop :=
  (∀ T₁ : GeometricTheory.{u} L, T ⊆ T₁ → ∃ J₁ : GrothendieckTopology C, J ≤ J₁ ∧
      IsClassifyingSite T₁ J₁ (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)))) ∧
    ∀ J₁ : GrothendieckTopology C, J ≤ J₁ → ∃ T₁ : GeometricTheory.{u} L, T ⊆ T₁ ∧
      IsClassifyingSite T₁ J₁ (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)))

/-- A choice, for each quotient `T₁` of `T`, of a topology `f T₁ ≥ J` classifying `T₁` with the
sheafified generic model descends to an order embedding of the quotients of `T` into the
topologies finer than `J` (by `le_iff_forall_isModel`), sending each quotient to the chosen
topology, which classifies it. -/
theorem exists_orderEmbedding_of_isClassifyingSite (hU : IsClassifyingSite T J U)
    (f : T.QuotientTheory → GrothendieckTopology C) (hf : ∀ T₁, J ≤ f T₁)
    (hfc : ∀ T₁ : T.QuotientTheory, IsClassifyingSite T₁.1 (f T₁)
      (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf (f T₁) (Type u)))) :
    ∃ Φ : T.Quotients ↪o Set.Ici J, ∀ T₁ : T.QuotientTheory,
      (Φ (toAntisymmetrization _ T₁)).1 = f T₁ ∧
        IsClassifyingSite T₁.1 (Φ (toAntisymmetrization _ T₁)).1
          (U.map (sheafToPresheaf J (Type u) ⋙
            presheafToSheaf (Φ (toAntisymmetrization _ T₁)).1 (Type u))) := by
  have key : ∀ T₁ T₂ : T.QuotientTheory, f T₁ ≤ f T₂ ↔ T₁ ≤ T₂ := fun T₁ T₂ =>
    hU.le_iff_forall_isModel (hf T₁) (hf T₂) (hfc T₁) (hfc T₂)
  let g : T.Quotients → Set.Ici J := fun q => ⟨f (ofAntisymmetrization _ q), hf _⟩
  have hg : ∀ T₁, g (toAntisymmetrization _ T₁) = ⟨f T₁, hf T₁⟩ := fun T₁ => by
    have h := (toAntisymmetrization_eq (· ≤ ·) _ _).1
      (toAntisymmetrization_ofAntisymmetrization (· ≤ ·) (toAntisymmetrization _ T₁))
    exact Subtype.ext (le_antisymm ((key _ _).2 h.1) ((key _ _).2 h.2))
  have hgle : ∀ a b, g a ≤ g b ↔ a ≤ b := fun a b => by
    induction a using Antisymmetrization.ind with | _ a
    induction b using Antisymmetrization.ind with | _ b
    rw [hg, hg, toAntisymmetrization_le_toAntisymmetrization_iff]
    exact key a b
  refine ⟨OrderEmbedding.ofMapLEIff g hgle, fun T₁ => ⟨congrArg Subtype.val (hg T₁), ?_⟩⟩
  have aux : ∀ X : Set.Ici J, X.1 = f T₁ → IsClassifyingSite T₁.1 X.1
      (U.map (sheafToPresheaf J (Type u) ⋙ presheafToSheaf X.1 (Type u))) := by
    rintro ⟨X, -⟩ (rfl : X = f T₁)
    exact hfc T₁
  exact aux _ (congrArg Subtype.val (hg T₁))

/-- Under the correspondence of roadmap 2.5, the quotients of `T` are order isomorphic to the
topologies finer than `J`, each quotient being classified by the corresponding topology with the
sheafified generic model. -/
theorem exists_orderIso_quotients_ici (hU : IsClassifyingSite T J U)
    (hQ : HasQuotientTopologies T J U) :
    ∃ Φ : T.Quotients ≃o Set.Ici J, ∀ T₁ : T.QuotientTheory,
      IsClassifyingSite T₁.1 (Φ (toAntisymmetrization _ T₁)).1
        (U.map (sheafToPresheaf J (Type u) ⋙
          presheafToSheaf (Φ (toAntisymmetrization _ T₁)).1 (Type u))) := by
  choose f hf hfc using fun T₁ : T.QuotientTheory => hQ.1 T₁.1 T₁.2
  obtain ⟨Φ, hΦ⟩ := hU.exists_orderEmbedding_of_isClassifyingSite f hf hfc
  have hs : Function.Surjective Φ := fun J₁ => by
    obtain ⟨T₁, hT₁, hc⟩ := hQ.2 J₁.1 J₁.2
    refine ⟨toAntisymmetrization _ (⟨T₁, hT₁⟩ : T.QuotientTheory), Subtype.ext ?_⟩
    exact (hΦ _).1.trans ((hU.eq_iff_forall_isModel (hf _) J₁.2 (hfc _) hc).2
      fun _ _ _ _ => Iff.rfl)
  exact ⟨OrderIso.ofSurjective Φ hs, fun T₁ => (hΦ T₁).2⟩

end IsClassifyingSite

section Restrict

variable {C D : Type u} [SmallCategory C] [SmallCategory D] {J J₁ : GrothendieckTopology C}
  {K K₁ : GrothendieckTopology D} (h₁ : J ≤ J₁) (k₁ : K ≤ K₁)
  (e : Sheaf J (Type u) ≌ Sheaf K (Type u))
  (he : ∀ F : Sheaf J (Type u),
    Presheaf.IsSheaf J₁ F.obj ↔ Presheaf.IsSheaf K₁ (e.functor.obj F).obj)

/-- The restriction of an equivalence of topoi of sheaves to the sheaves for finer topologies,
when it matches them. -/
noncomputable abbrev sheafEquivFunctor : Sheaf J₁ (Type u) ⥤ Sheaf K₁ (Type u) :=
  ObjectProperty.lift _ (sheafInclusion h₁ ⋙ e.functor ⋙ sheafToPresheaf K (Type u))
    fun X => (he _).1 X.property

include k₁ in
/-- The restriction of an equivalence of topoi of sheaves to the sheaves for finer topologies,
when it matches them, is an equivalence. -/
theorem isEquivalence_sheafEquivFunctor : (sheafEquivFunctor h₁ e he).IsEquivalence := by
  have : (sheafEquivFunctor h₁ e he).EssSurj := ⟨fun Y => by
    let G := e.inverse.obj ((sheafInclusion k₁).obj Y)
    have i : e.functor.obj G ≅ (sheafInclusion k₁).obj Y := e.counitIso.app _
    have hG : Presheaf.IsSheaf J₁ G.obj := (he G).2
      ((Presheaf.isSheaf_of_iso_iff ((sheafToPresheaf K (Type u)).mapIso i)).2 Y.property)
    exact ⟨⟨G.obj, hG⟩,
      ⟨(fullyFaithfulSheafToPresheaf K₁ (Type u)).preimageIso
        ((sheafToPresheaf K (Type u)).mapIso i)⟩⟩⟩
  exact { }

include k₁ in
/-- The restriction of an equivalence of topoi of sheaves to the sheaves for finer topologies. -/
noncomputable def sheafEquivOfIsSheafIff : Sheaf J₁ (Type u) ≌ Sheaf K₁ (Type u) :=
  have := isEquivalence_sheafEquivFunctor h₁ k₁ e he
  (sheafEquivFunctor h₁ e he).asEquivalence

/-- The restricted equivalence commutes with the inclusions of sheaves. -/
noncomputable def sheafEquivOfIsSheafIffCompIso :
    (sheafEquivOfIsSheafIff h₁ k₁ e he).functor ⋙ sheafInclusion k₁ ≅
      sheafInclusion h₁ ⋙ e.functor :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

end Restrict

/-- An equivalence of topoi of sheaves matching the `J₁`-sheaves with the `K₁`-sheaves restricts
to an equivalence between the topoi of `J₁`-sheaves and of `K₁`-sheaves. -/
theorem nonempty_sheafEquiv_of_isSheaf_iff {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J J₁ : GrothendieckTopology C} {K K₁ : GrothendieckTopology D} (h₁ : J ≤ J₁) (k₁ : K ≤ K₁)
    (e : Sheaf J (Type u) ≌ Sheaf K (Type u))
    (he : ∀ F : Sheaf J (Type u),
      Presheaf.IsSheaf J₁ F.obj ↔ Presheaf.IsSheaf K₁ (e.functor.obj F).obj) :
    Nonempty (Sheaf J₁ (Type u) ≌ Sheaf K₁ (Type u)) :=
  ⟨sheafEquivOfIsSheafIff h₁ k₁ e he⟩

namespace IsClassifyingSite

variable {T : GeometricTheory.{u} L} {C : Type u} [SmallCategory C]
  {J : GrothendieckTopology C} {U : CatStructure L (Sheaf J (Type u))}

/-- **Bridges between theories.** Let `T` and `T'` be Morita-equivalent theories, classified by
`(C, J, U)` and `(D, K, U')`, for which the correspondence of roadmap 2.5 holds. Then the
quotients of `T` and of `T'` (up to having the same models) are order isomorphic, by an
isomorphism carrying each quotient of `T` to a Morita-equivalent quotient of `T'`. -/
theorem exists_orderIso_quotients {L' : FirstOrder.Language.{u₃, u₄}}
    {T' : GeometricTheory.{u} L'} {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {U' : CatStructure L' (Sheaf K (Type u))} (hU : IsClassifyingSite T J U)
    (hU' : IsClassifyingSite T' K U') (hQ : HasQuotientTopologies T J U)
    (hQ' : HasQuotientTopologies T' K U') (h : MoritaEquivalent T T') :
    ∃ Ψ : T.Quotients ≃o T'.Quotients, ∀ (T₁ : T.QuotientTheory) (T₂ : T'.QuotientTheory),
      Ψ (toAntisymmetrization _ T₁) = toAntisymmetrization _ T₂ →
        MoritaEquivalent T₁.1 T₂.1 := by
  obtain ⟨e⟩ := (hU.moritaEquivalent_iff hU').1 h
  obtain ⟨Φ, hΦ⟩ := hU.exists_orderIso_quotients_ici hQ
  obtain ⟨Φ', hΦ'⟩ := hU'.exists_orderIso_quotients_ici hQ'
  obtain ⟨φ, hφ⟩ := LeanPool.ToposTheoreticBridges.exists_orderIso_ici_of_sheafEquiv J K e
  refine ⟨Φ.trans (φ.trans Φ'.symm), fun T₁ T₂ hT => ?_⟩
  have h₂ : Φ' (toAntisymmetrization _ T₂) = φ (Φ (toAntisymmetrization _ T₁)) := by
    rw [← hT]
    simp
  have c₂ := hΦ' T₂
  rw [h₂] at c₂
  obtain ⟨e₁⟩ := nonempty_sheafEquiv_of_isSheaf_iff (Φ (toAntisymmetrization _ T₁)).2
    (φ (Φ (toAntisymmetrization _ T₁))).2 e (hφ _)
  exact ⟨C, D, inferInstance, inferInstance, _, _, _, _, hΦ T₁, c₂, ⟨e₁⟩⟩

end IsClassifyingSite

end LeanPool.ClassifyingTopoi
