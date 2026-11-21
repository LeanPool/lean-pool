/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.DiaconescuExistence
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.LocallyFiltering
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.PullbackElements
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Diaconescu's theorem: the existence half for an arbitrary site

Let `(C, J)` and `(D, K)` be small sites. A functor `F : C ⥤ Sh(D, K)` which is flat in the
internal sense of `Sh(D, K)` (locally filtering, `LeanPool.ClassifyingTopoi.IsLocallyFiltering`)
and sends the `J`-covering sieves to epimorphic families extends to a left exact left adjoint
`Sh(C, J) ⥤ Sh(D, K)` (`LeanPool.ClassifyingTopoi.exists_leftAdjoint_of_isLocallyFiltering`).

The extension to presheaves is `P ↦ a_K (d ↦ P ⊗_C F(-)(d))`
(`LeanPool.ClassifyingTopoi.tensorExtension`). It preserves colimits; it preserves the terminal
object and pullbacks because the comparison maps of `d ↦ P ⊗_C F(-)(d)` are locally injective
and locally surjective, hence inverted by `K`-sheafification. Both properties are read on
elements: a pair of elements of tensor products with the same image comes locally from a single
element, and two triples with the same class have locally a common refinement
(`IsLocallyFiltering.locally_of_tensorι_eq`), so the tensor products behave locally like filtered
colimits. The descent from presheaves to `J`-sheaves then uses the continuity of `F`, as in the
left exact case (`exists_leftAdjoint_of_preservesFiniteLimits`).

## Main results

* `LeanPool.ClassifyingTopoi.preservesFiniteLimits_tensorExtension_comp`: for a locally
  filtering `F`, the functor `P ↦ a_K (d ↦ P ⊗_C F(-)(d))` is left exact;
* `LeanPool.ClassifyingTopoi.exists_leftAdjoint_of_isLocallyFiltering` (**existence half of
  Diaconescu's theorem**).

## References

* S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, VII.8 Theorem 2,
  VII.9 Corollary 2 and VII.10 Theorem 1.
* P. T. Johnstone, *Sketches of an Elephant*, B3.2.7 and C2.3.8.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite GrothendieckTopology

namespace LeanPool.ClassifyingTopoi

section Terminal

variable {E : Type u} [SmallCategory E]

/-- The terminal presheaf has exactly one element at each object. -/
noncomputable instance uniqueTerminalObj (e : Eᵒᵖ) : Unique ((⊤_ (Eᵒᵖ ⥤ Type u)).obj e) :=
  Types.isTerminalEquivUnique _ (terminalIsTerminal.isTerminalObj ((evaluation _ _).obj e) _)

end Terminal

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {K : GrothendieckTopology D} {F : C ⥤ (Dᵒᵖ ⥤ Type u)} (hF : IsLocallyFiltering K F)

section Comparison

variable {P Q R : Cᵒᵖ ⥤ Type u} (φ : P ⟶ R) (ψ : Q ⟶ R)

/-- The first projection of the pullback comparison of the extension. -/
theorem fst_pullbackComparison_app (d : Dᵒᵖ) (t : ((tensorExtension F).obj (pullback φ ψ)).obj d) :
    (pullback.fst ((tensorExtension F).map φ) ((tensorExtension F).map ψ)).app d
      ((pullbackComparison (tensorExtension F) φ ψ).app d t) =
        ((tensorExtension F).map (pullback.fst φ ψ)).app d t :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (pullbackComparison_comp_fst (tensorExtension F) φ ψ) d) t

/-- The second projection of the pullback comparison of the extension. -/
theorem snd_pullbackComparison_app (d : Dᵒᵖ) (t : ((tensorExtension F).obj (pullback φ ψ)).obj d) :
    (pullback.snd ((tensorExtension F).map φ) ((tensorExtension F).map ψ)).app d
      ((pullbackComparison (tensorExtension F) φ ψ).app d t) =
        ((tensorExtension F).map (pullback.snd φ ψ)).app d t :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (pullbackComparison_comp_snd (tensorExtension F) φ ψ) d) t

include hF in
/-- The pullback comparison of the extension is locally surjective. -/
theorem locally_surjective_pullbackComparison (d : D)
    (y : (pullback ((tensorExtension F).map φ) ((tensorExtension F).map ψ)).obj (op d)) :
    Locally K d fun _ g => ∃ t, (pullbackComparison (tensorExtension F) φ ψ).app _ t =
      (pullback ((tensorExtension F).map φ) ((tensorExtension F).map ψ)).map g.op y := by
  obtain ⟨c₁, a₁, p, hp⟩ := extι_surjective F _
    ((pullback.fst ((tensorExtension F).map φ) ((tensorExtension F).map ψ)).app _ y)
  obtain ⟨c₂, a₂, q, hq⟩ := extι_surjective F _
    ((pullback.snd ((tensorExtension F).map φ) ((tensorExtension F).map ψ)).app _ y)
  have hcond : extι R (op d) c₁ a₁ (φ.app _ p) = extι R (op d) c₂ a₂ (ψ.app _ q) := by
    rw [← tensorExtension_map_app_extι, ← tensorExtension_map_app_extι, hp, hq]
    exact pullback_condition_app _ _ y
  refine (hF.locally_of_tensorι_eq R hcond).mono fun d' g ⟨e, u, v, b, hu, hv, hpq⟩ => ?_
  obtain ⟨w, hw₁, hw₂⟩ := exists_pullback_app φ ψ (e := op e) (x := P.map u.op p)
    (y := Q.map v.op q) (by rw [NatTrans.naturality_apply, NatTrans.naturality_apply]; exact hpq)
  refine ⟨extι _ (op d') e b w, pullback_ext_app _ _ ?_ ?_⟩
  · rw [fst_pullbackComparison_app, tensorExtension_map_app_extι, hw₁, NatTrans.naturality_apply,
      ← hp, tensorExtension_map_extι]
    rw [← hu, extι_map]
  · rw [snd_pullbackComparison_app, tensorExtension_map_app_extι, hw₂, NatTrans.naturality_apply,
      ← hq, tensorExtension_map_extι]
    rw [← hv, extι_map]

include hF in
/-- The pullback comparison of the extension is locally injective. -/
theorem locally_injective_pullbackComparison (d : D)
    (t t' : ((tensorExtension F).obj (pullback φ ψ)).obj (op d))
    (h : (pullbackComparison (tensorExtension F) φ ψ).app _ t =
      (pullbackComparison (tensorExtension F) φ ψ).app _ t') :
    Locally K d fun _ g => ((tensorExtension F).obj (pullback φ ψ)).map g.op t =
      ((tensorExtension F).obj (pullback φ ψ)).map g.op t' := by
  obtain ⟨c₁, a₁, w₁, rfl⟩ := extι_surjective F _ t
  obtain ⟨c₂, a₂, w₂, rfl⟩ := extι_surjective F _ t'
  have h₁ := congrArg ((pullback.fst ((tensorExtension F).map φ)
    ((tensorExtension F).map ψ)).app _) h
  have h₂ := congrArg ((pullback.snd ((tensorExtension F).map φ)
    ((tensorExtension F).map ψ)).app _) h
  rw [fst_pullbackComparison_app, fst_pullbackComparison_app, tensorExtension_map_app_extι,
    tensorExtension_map_app_extι] at h₁
  rw [snd_pullbackComparison_app, snd_pullbackComparison_app, tensorExtension_map_app_extι,
    tensorExtension_map_app_extι] at h₂
  refine (hF.commonRefinement_and P (hF.locally_of_tensorι_eq P h₁)
    (hF.locally_of_tensorι_eq Q h₂)).mono fun d' g ⟨e, u, v, b, hu, hv, hp, hq⟩ => ?_
  have hw : (pullback φ ψ).map u.op w₁ = (pullback φ ψ).map v.op w₂ :=
    pullback_ext_app φ ψ (by rw [NatTrans.naturality_apply, NatTrans.naturality_apply]; exact hp)
      (by rw [NatTrans.naturality_apply, NatTrans.naturality_apply]; exact hq)
  rw [tensorExtension_map_extι, tensorExtension_map_extι, ← hu, ← hv, extι_map,
    extι_map, hw]

end Comparison

section TerminalComparison

include hF in
/-- The comparison map from the extension of the terminal presheaf is locally surjective. -/
theorem locally_nonempty_tensorExtension_terminal (d : D) :
    Locally K d fun d' _ =>
      Nonempty (((tensorExtension F).obj (⊤_ (Cᵒᵖ ⥤ Type u))).obj (op d')) :=
  (hF.nonempty d).mono fun _ _ ⟨c, ⟨a⟩⟩ => ⟨extι _ _ c a default⟩

include hF in
/-- Two elements of the extension of the terminal presheaf are locally equal. -/
theorem locally_eq_tensorExtension_terminal (d : D)
    (t t' : ((tensorExtension F).obj (⊤_ (Cᵒᵖ ⥤ Type u))).obj (op d)) :
    Locally K d fun _ g => ((tensorExtension F).obj (⊤_ (Cᵒᵖ ⥤ Type u))).map g.op t =
      ((tensorExtension F).obj (⊤_ (Cᵒᵖ ⥤ Type u))).map g.op t' := by
  obtain ⟨c₁, a₁, p₁, rfl⟩ := extι_surjective F _ t
  obtain ⟨c₂, a₂, p₂, rfl⟩ := extι_surjective F _ t'
  refine (hF.span d a₁ a₂).mono fun d' g ⟨e, u, v, y, hu, hv⟩ => ?_
  rw [tensorExtension_map_extι, tensorExtension_map_extι, ← hu, ← hv, extι_map,
    extι_map, Subsingleton.elim ((⊤_ (Cᵒᵖ ⥤ Type u)).map u.op p₁)
      ((⊤_ (Cᵒᵖ ⥤ Type u)).map v.op p₂)]

end TerminalComparison

section LeftExact

/-- A property holding locally gives a covering sieve contained in a given sieve. -/
theorem mem_of_locally {d : D} {S : Sieve d} (h : Locally K d fun _ g => S g) : S ∈ K d :=
  let ⟨_, hT, hTS⟩ := h
  K.superset_covering (fun _ g hg => hTS g hg) hT

variable {P Q R : Cᵒᵖ ⥤ Type u} (φ : P ⟶ R) (ψ : Q ⟶ R)

include hF in
theorem isLocallySurjective_pullbackComparison :
    Presheaf.IsLocallySurjective K (pullbackComparison (tensorExtension F) φ ψ) where
  imageSieve_mem y := mem_of_locally (locally_surjective_pullbackComparison hF φ ψ _ y)

include hF in
theorem isLocallyInjective_pullbackComparison :
    Presheaf.IsLocallyInjective K (pullbackComparison (tensorExtension F) φ ψ) where
  equalizerSieve_mem t t' h := mem_of_locally (locally_injective_pullbackComparison hF φ ψ _ t t' h)

include hF in
theorem isLocallySurjective_terminalFrom :
    Presheaf.IsLocallySurjective K
      (terminal.from ((tensorExtension F).obj (⊤_ (Cᵒᵖ ⥤ Type u)))) where
  imageSieve_mem _ := mem_of_locally ((locally_nonempty_tensorExtension_terminal hF _).mono
    fun _ _ ⟨t⟩ => ⟨t, Subsingleton.elim _ _⟩)

include hF in
theorem isLocallyInjective_terminalFrom :
    Presheaf.IsLocallyInjective K
      (terminal.from ((tensorExtension F).obj (⊤_ (Cᵒᵖ ⥤ Type u)))) where
  equalizerSieve_mem t t' _ := mem_of_locally (locally_eq_tensorExtension_terminal hF _ t t')

include hF in
/-- **Left exactness.** For a locally filtering `F`, the functor
`P ↦ a_K (d ↦ P ⊗_C F(-)(d))` preserves finite limits. -/
theorem preservesFiniteLimits_tensorExtension_comp :
    PreservesFiniteLimits (tensorExtension F ⋙ presheafToSheaf K (Type u)) := by
  let a := presheafToSheaf K (Type u)
  have : PreservesLimit (Functor.empty.{0} (Cᵒᵖ ⥤ Type u)) (tensorExtension F ⋙ a) := by
    have := isLocallySurjective_terminalFrom hF
    have := isLocallyInjective_terminalFrom hF
    have hW := (K.W_iff _).1 (K.W_of_isLocallyBijective
      (terminal.from ((tensorExtension F).obj (⊤_ (Cᵒᵖ ⥤ Type u)))))
    have hT : IsTerminal ((tensorExtension F ⋙ a).obj (⊤_ (Cᵒᵖ ⥤ Type u))) :=
      (terminalIsTerminal.isTerminalObj a _).ofIso (asIso (a.map (terminal.from _))).symm
    exact preservesLimit_of_preserves_limit_cone terminalIsTerminal
      ((isLimitMapConeEmptyConeEquiv _ _).symm hT)
  have hpb : ∀ {P Q R : Cᵒᵖ ⥤ Type u} (φ : P ⟶ R) (ψ : Q ⟶ R),
      PreservesLimit (cospan φ ψ) (tensorExtension F ⋙ a) := by
    intro P Q R φ ψ
    have := isLocallySurjective_pullbackComparison hF φ ψ
    have := isLocallyInjective_pullbackComparison hF φ ψ
    have : IsIso (a.map (pullbackComparison (tensorExtension F) φ ψ)) :=
      (K.W_iff _).1 (K.W_of_isLocallyBijective _)
    have : IsIso (pullbackComparison (tensorExtension F ⋙ a) φ ψ) := by
      rw [pullbackComparison_comp]
      infer_instance
    exact PreservesPullback.of_iso_comparison _
  have : PreservesLimitsOfShape WalkingCospan (tensorExtension F ⋙ a) :=
    ⟨fun {G} => preservesLimit_of_iso_diagram _ (diagramIsoCospan G).symm⟩
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (tensorExtension F ⋙ a)
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

end LeftExact

section Existence

variable {J : GrothendieckTopology C}

/-- **Existence half of Diaconescu's theorem.** Let `(C, J)` and `(D, K)` be small sites. A
functor `F : C ⥤ Sh(D, K)` which is flat in the internal sense of `Sh(D, K)` (its underlying
presheaf-valued functor is locally filtering) and sends the `J`-covering sieves to epimorphic
families extends to a left exact left adjoint `G : Sh(C, J) ⥤ Sh(D, K)`: the composite of `G`
with the sheafified Yoneda embedding is isomorphic to `F`. -/
theorem exists_leftAdjoint_of_isLocallyFiltering (F : C ⥤ Sheaf K (Type u))
    (hF : IsLocallyFiltering K (F ⋙ sheafToPresheaf K (Type u)))
    (hc : MapsCoversToEpimorphicFamilies (J := J) F) :
    ∃ (G : Sheaf J (Type u) ⥤ Sheaf K (Type u)) (_ : PreservesFiniteLimits G), G.IsLeftAdjoint ∧
      Nonempty (yoneda ⋙ presheafToSheaf J (Type u) ⋙ G ≅ F) := by
  let F' := F ⋙ sheafToPresheaf K (Type u)
  let G₀ := tensorExtension F' ⋙ presheafToSheaf K (Type u)
  have : PreservesFiniteLimits G₀ := preservesFiniteLimits_tensorExtension_comp hF
  have : (tensorExtension F').IsLeftAdjoint := Presheaf.isLeftAdjoint_of_preservesColimits _
  have : (presheafToSheaf K (Type u)).IsLeftAdjoint :=
    (sheafificationAdjunction K (Type u)).isLeftAdjoint
  let es : shrinkYoneda.{u} ⋙ G₀ ≅ F := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (shrinkYonedaCompTensorExtensionIso F') _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction K (Type u)).counit) ≪≫
    Functor.rightUnitor F
  obtain ⟨G, hG, hG', ⟨e'⟩⟩ := exists_presheafToSheaf_comp_iso (J := J) G₀
    (isIso_map_shrinkFunctor_ι F hc G₀ es)
  exact ⟨G, hG, hG', ⟨Functor.isoWhiskerLeft yoneda e' ≪≫
    Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm G₀ ≪≫ es⟩⟩

end Existence

end LeanPool.ClassifyingTopoi
