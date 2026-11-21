/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.Torsors
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.DiaconescuGeneral
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.SheafSemantics
public import LeanPool.ToposTheoreticBridges.Morita

/-!
# `G`-sets classify `G`-torsors (roadmap 3.3)

The presheaf topos on `SingleObj G` (the topos of right `G`-sets), with the generic torsor,
classifies the theory of `G`-torsors (`LeanPool.ClassifyingTopoi.isClassifyingSite_genericTorsor`).

* **Existence.** A torsor `M` in `Sh(D, K)` defines a functor `SingleObj G ⥤ Sh(D, K)`, the
  carrier with the action (`Torsor.torsorFunctor`). It is locally filtering: locally the carrier
  is inhabited (two elements are locally related by the action, by transitivity), and two
  elements of `G` acting in the same way on a section are locally equal, by freeness; these are
  read on sections through the local Kripke–Joyal semantics
  (`CatStructure.IsModel.locally_realize`). By the existence half of Diaconescu's theorem
  (`exists_leftAdjoint_of_isLocallyFiltering`) it extends to a left exact left adjoint, which maps
  the generic torsor to `M`.
* **Homomorphisms.** A natural transformation between left exact left adjoints out of the
  presheaf topos is determined by its restriction along the Yoneda embedding of `SingleObj G`,
  that is by its component at the generic torsor, and these components are exactly the
  equivariant morphisms, the homomorphisms of the image structures.
* **Morita equivalence** (`LeanPool.ClassifyingTopoi.moritaEquivalent_torsorTheory_iff`): the
  theories of `G`-torsors and `H`-torsors are Morita equivalent exactly when `G ≃* H`. Their
  classifying topoi `Psh(SingleObj G)` and `Psh(SingleObj H)` are then equivalent, hence so are the
  Karoubi envelopes (`moritaEquivalentCat_iff_karoubi`), which are `SingleObj G` and
  `SingleObj H` since a group has no idempotent besides `1`.

## References

* S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, VIII.2 (`G`-sets classify
  `G`-torsors).
* O. Caramello, *Theories, Sites, Toposes*, 2.1.
-/

@[expose] public section

universe u

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance high] Sheaf.instHasColimitsOfShape

namespace Torsor

variable {G : Type u}

section Action

variable {E : Type*} [Category E] [HasFiniteProducts E]

/-- The action of `g` on the carrier of a structure in the language of `G`-sets. -/
noncomputable def actMor (S : CatStructure (torsorLanguage G) E) (g : G) :
    S.carrier ⟶ S.carrier :=
  Pi.lift (fun _ : Fin 1 => 𝟙 S.carrier) ≫ S.funMap (torsorSymbol g)

omit [HasFiniteProducts E] in
theorem π_comp_lift_id (X : E) :
    Pi.π (fun _ : Fin 1 => X) 0 ≫ Pi.lift (fun _ : Fin 1 => 𝟙 X) = 𝟙 _ := by
  refine Pi.hom_ext _ _ fun i => ?_
  rw [Fin.fin_one_eq_zero i]
  simp

/-- The function symbol of `g` is the action of `g` on the unique coordinate. -/
theorem funMap_eq_π_comp_actMor (S : CatStructure (torsorLanguage G) E) (g : G) :
    S.funMap (torsorSymbol g) = Pi.π _ 0 ≫ actMor S g := by
  rw [actMor, ← Category.assoc, π_comp_lift_id, Category.id_comp]

variable [HasFiniteLimits E] [HasImages E]

/-- A morphism of carriers is a homomorphism of structures in the language of `G`-sets exactly
when it is equivariant. -/
theorem isHom_iff (S S' : CatStructure (torsorLanguage G) E) (h : S.carrier ⟶ S'.carrier) :
    S.IsHom S' h ↔ ∀ g : G, actMor S g ≫ h = h ≫ actMor S' g := by
  constructor
  · intro hh g
    have := hh.funMap (torsorSymbol g)
    rw [funMap_eq_π_comp_actMor, funMap_eq_π_comp_actMor, Category.assoc, Limits.Pi.map_π_assoc]
      at this
    simpa using congrArg (Pi.lift (fun _ : Fin 1 => 𝟙 S.carrier) ≫ ·) this
  · intro hh
    refine ⟨fun {k} f => ?_, fun R => PEmpty.elim R⟩
    match k, f with
    | 0, f => exact PEmpty.elim f
    | 1, g =>
      change S.funMap (torsorSymbol (show G from g)) ≫ h =
        _ ≫ S'.funMap (torsorSymbol (show G from g))
      rw [funMap_eq_π_comp_actMor, funMap_eq_π_comp_actMor, Category.assoc, hh,
        Limits.Pi.map_π_assoc]
    | _ + 2, f => exact PEmpty.elim f

/-- Two structures in the language of `G`-sets with an equivariant isomorphism of carriers are
isomorphic. -/
theorem isomorphic_of_iso (S S' : CatStructure (torsorLanguage G) E) (e : S.carrier ≅ S'.carrier)
    (he : ∀ g : G, actMor S g ≫ e.hom = e.hom ≫ actMor S' g) : S.Isomorphic S' := by
  refine ⟨e, (isHom_iff S S' e.hom).2 he, (isHom_iff S' S e.inv).2 fun g => ?_⟩
  rw [← cancel_epi e.hom, ← Category.assoc, ← he g, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

variable {E' : Type*} [Category E'] [HasFiniteProducts E']

omit [HasFiniteLimits E] [HasImages E] in
/-- The action in the image of a structure under a functor preserving finite products. -/
theorem actMor_map (S : CatStructure (torsorLanguage G) E) (F : E ⥤ E')
    [PreservesFiniteProducts F] (g : G) : actMor (S.map F) g = F.map (actMor S g) := by
  change Pi.lift (fun _ : Fin 1 => 𝟙 _) ≫ inv (piComparison F fun _ => S.carrier) ≫
    F.map (S.funMap (torsorSymbol g)) = _
  have hπ : inv (piComparison F fun _ : Fin 1 => S.carrier) ≫ F.map (Pi.π _ 0) = Pi.π _ 0 :=
    (IsIso.inv_comp_eq _).2 (piComparison_comp_π F _ 0).symm
  rw [funMap_eq_π_comp_actMor, F.map_comp, ← Category.assoc (inv _), hπ]
  simp

end Action

section Fibers

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  (M : CatStructure (torsorLanguage G) (Sheaf K (Type u)))

/-- The action of `g` on a section of the carrier of a structure in `Sh(D, K)`. -/
noncomputable abbrev smul {d : D} (g : G)
    (x : (M.map (sheafToPresheaf K (Type u))).carrier.obj (op d)) :
    (M.map (sheafToPresheaf K (Type u))).carrier.obj (op d) :=
  ((M.map (sheafToPresheaf K (Type u))).fiberStr (op d)).funMap (torsorSymbol g) fun _ => x

/-- The action of `g` on sections is that of the action morphism. -/
theorem actMor_app (g : G) {d : D} (x : (M.map (sheafToPresheaf K (Type u))).carrier.obj (op d)) :
    ((sheafToPresheaf K (Type u)).map (actMor M g)).app (op d) x = smul M g x := by
  rw [← actMor_map]
  change ((M.map (sheafToPresheaf K (Type u))).funMap (torsorSymbol g)).app (op d)
    (NatTrans.app (Pi.lift (fun _ : Fin 1 => 𝟙 (M.map (sheafToPresheaf K (Type u))).carrier))
      (op d) x) = _
  unfold smul
  rw [CatStructure.fiberStr_funMap]
  congr 1
  rw [Equiv.eq_symm_apply]
  funext i
  rw [Syntactic.secEquiv_apply, ← NatTrans.comp_app_apply]
  simp

/-- The action commutes with restriction. -/
theorem smul_map (g : G) {d d' : D} (k : d' ⟶ d)
    (x : (M.map (sheafToPresheaf K (Type u))).carrier.obj (op d)) :
    smul M g ((M.map (sheafToPresheaf K (Type u))).carrier.map k.op x) =
      (M.map (sheafToPresheaf K (Type u))).carrier.map k.op (smul M g x) := by
  rw [← actMor_app, ← actMor_app, NatTrans.naturality_apply]

/-- The term `g · t`, in a structure on a type. -/
theorem realize_torsorAct_apply {N : Type*} [(torsorLanguage G).Structure N] {n : ℕ} (g : G)
    (t : (torsorLanguage G).Term (Fin n)) (v : Fin n → N) :
    (torsorAct g t).realize v = Structure.funMap (torsorSymbol g) fun _ => t.realize v := by
  change Term.realize v (Functions.apply₁ (torsorSymbol g) t) = _
  rw [Term.realize_functions_apply₁]
  congr 1
  funext i
  rw [Fin.fin_one_eq_zero i]
  rfl

/-- Two morphisms of sheaves of types agreeing on all sections are equal. -/
theorem sheafHom_ext {F F' : Sheaf K (Type u)} {f f' : F ⟶ F'}
    (h : ∀ (d : D) (x : F.obj.obj (op d)),
      ((sheafToPresheaf K (Type u)).map f).app (op d) x =
        ((sheafToPresheaf K (Type u)).map f').app (op d) x) : f = f' := by
  apply (sheafToPresheaf K (Type u)).map_injective
  refine NatTrans.ext (funext fun ⟨d⟩ => ?_)
  ext x
  exact h d x

/-- Sections of a sheaf of types that are locally equal are equal. -/
theorem eq_of_locally {F : Sheaf K (Type u)} {d : D} {x y : F.obj.obj (op d)}
    (h : Locally K d fun _ g => F.obj.map g.op x = F.obj.map g.op y) : x = y := by
  obtain ⟨S, hS, h⟩ := h
  exact ((isSheaf_iff_isSheaf_of_type K F.obj).1 F.property S hS).isSeparatedFor.ext
    fun _ g hg => h g hg

end Fibers

section Axioms

variable [Group G] {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  {M : CatStructure (torsorLanguage G) (Sheaf K (Type u))} (hM : M.IsModel (torsorTheory G))
include hM

/-- In a torsor, `1` acts trivially on sections. -/
theorem one_smul (d : D) (x : (M.map (sheafToPresheaf K (Type u))).carrier.obj (op d)) :
    smul M 1 x = x := by
  apply eq_of_locally (F := M.carrier)
  refine (hM.locally_realize one_mem_torsorTheory d (fun _ => x) trivial).mono fun d' k hk => ?_
  simp only [GeometricFormula.Realize, realize_torsorAct_apply, Term.realize_var] at hk
  exact (smul_map M 1 k x).symm.trans hk

/-- In a torsor, the action on sections is an action. -/
theorem mul_smul (g h : G) (d : D)
    (x : (M.map (sheafToPresheaf K (Type u))).carrier.obj (op d)) :
    smul M (g * h) x = smul M g (smul M h x) := by
  apply eq_of_locally (F := M.carrier)
  refine (hM.locally_realize (mul_mem_torsorTheory g h) d (fun _ => x) trivial).mono
    fun d' k hk => ?_
  simp only [GeometricFormula.Realize, realize_torsorAct_apply, Term.realize_var] at hk
  exact (smul_map M (g * h) k x).symm.trans (hk.trans ((congrArg (smul M g)
    (smul_map M h k x)).trans (smul_map M g k _)))

/-- A torsor is locally inhabited. -/
theorem locally_nonempty (d : D) :
    Locally K d fun d' _ => Nonempty ((M.map (sheafToPresheaf K (Type u))).carrier.obj (op d')) :=
  (hM.locally_realize nonempty_mem_torsorTheory d Fin.elim0 trivial).mono fun _ _ ⟨a, _⟩ => ⟨a⟩

/-- In a torsor, two sections are locally related by the action. -/
theorem locally_exists_smul_eq (d : D)
    (x y : (M.map (sheafToPresheaf K (Type u))).carrier.obj (op d)) :
    Locally K d fun _ k => ∃ g : G,
      smul M g ((M.map (sheafToPresheaf K (Type u))).carrier.map k.op x) =
        (M.map (sheafToPresheaf K (Type u))).carrier.map k.op y := by
  refine (hM.locally_realize transitive_mem_torsorTheory d ![x, y] trivial).mono
    fun d' k ⟨g, hg⟩ => ⟨g, ?_⟩
  simp only [GeometricFormula.Realize, realize_torsorAct_apply, Term.realize_var] at hg
  exact hg

/-- In a torsor, two distinct elements of `G` never act in the same way on a section, except
on the empty covering. -/
theorem locally_false_of_smul_eq {g h : G} (hne : g ≠ h) (d : D)
    (x : (M.map (sheafToPresheaf K (Type u))).carrier.obj (op d))
    (hx : smul M g x = smul M h x) : Locally K d fun _ _ => False := by
  refine (hM.locally_realize (free_mem_torsorTheory hne) d (fun _ => x) ?_).mono fun d' k hk => ?_
  · let := (M.map (sheafToPresheaf K (Type u))).fiberStr (op d)
    simp only [GeometricFormula.Realize, realize_torsorAct_apply, Term.realize_var]
    exact hx
  · let := (M.map (sheafToPresheaf K (Type u))).fiberStr (op d')
    exact GeometricFormula.realize_bot _ hk

end Axioms

section Functor

variable [Group G] {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  (M : CatStructure (torsorLanguage G) (Sheaf K (Type u))) (hM : M.IsModel (torsorTheory G))

include hM in
/-- The functor `SingleObj G ⥤ Sh(D, K)` of a torsor: its carrier, with the action of `G`. -/
noncomputable def torsorFunctor : AsSmall.{u} (SingleObj G) ⥤ Sheaf K (Type u) where
  obj _ := M.carrier
  map f := actMor M (AsSmall.down.map f : G)
  map_id _ := sheafHom_ext fun d x => by
    rw [actMor_app]
    exact (one_smul hM d x).trans (by simp)
  map_comp f f' := sheafHom_ext fun d x => by
    have h₁ := actMor_app M (AsSmall.down.map (f ≫ f') : G) x
    have h₂ := actMor_app M (AsSmall.down.map f' : G) (smul M (AsSmall.down.map f : G) x)
    have h₃ := actMor_app M (AsSmall.down.map f : G) x
    rw [h₁, (sheafToPresheaf K (Type u)).map_comp, NatTrans.comp_app, ConcreteCategory.comp_apply,
      h₃, h₂]
    exact mul_smul hM _ _ d x

/-- The action of a morphism of `SingleObj G` in the functor of a torsor, on sections. -/
theorem torsorFunctor_map_app (f : AsSmall.up.obj (SingleObj.star G) ⟶
    AsSmall.up.obj (SingleObj.star G)) {d : D}
    (x : (M.map (sheafToPresheaf K (Type u))).carrier.obj (op d)) :
    ((torsorFunctor M hM ⋙ sheafToPresheaf K (Type u)).map f).app (op d) x =
      smul M (AsSmall.down.map f : G) x :=
  actMor_app M _ x

/-- The functor of a torsor is locally filtering: it is flat in the internal sense of
`Sh(D, K)`. -/
theorem isLocallyFiltering_torsorFunctor :
    IsLocallyFiltering K (torsorFunctor M hM ⋙ sheafToPresheaf K (Type u)) where
  nonempty d := (locally_nonempty hM d).mono fun _ _ h => ⟨AsSmall.up.obj (SingleObj.star G), h⟩
  span d c₁ c₂ x₁ x₂ := (locally_exists_smul_eq hM d x₁ x₂).mono fun d' k ⟨g, hg⟩ =>
    ⟨c₁, 𝟙 c₁, AsSmall.up.map (show SingleObj.star G ⟶ SingleObj.star G from g),
      (M.map (sheafToPresheaf K (Type u))).carrier.map k.op x₁,
      by rw [CategoryTheory.Functor.map_id]; rfl,
      (torsorFunctor_map_app M hM _ _).trans hg⟩
  equalize d c c' u v x h := by
    by_cases huv : u = v
    · subst huv
      exact Locally.of_forall fun d' k =>
        ⟨c, 𝟙 c, (M.map (sheafToPresheaf K (Type u))).carrier.map k.op x, rfl,
          by rw [CategoryTheory.Functor.map_id]; rfl⟩
    · have hne : (AsSmall.down.map u : G) ≠ AsSmall.down.map v :=
        fun e => huv (ULift.ext e)
      exact (locally_false_of_smul_eq hM hne d x ((torsorFunctor_map_app M hM u x).symm.trans
        (h.trans (torsorFunctor_map_app M hM v x)))).mono fun _ _ h => h.elim

/-- The functor of a torsor is continuous for the trivial topology. -/
theorem mapsCoversToEpimorphicFamilies_torsorFunctor :
    MapsCoversToEpimorphicFamilies (J := (⊥ : GrothendieckTopology (AsSmall.{u} (SingleObj G))))
      (torsorFunctor M hM) := by
  intro X S hS Z g h hgh
  rw [GrothendieckTopology.bot_covering] at hS
  subst hS
  simpa using hgh (𝟙 X) trivial

end Functor

section Classification

variable [Group G] {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}

variable (G) in
/-- The inclusion of presheaves as sheaves for the trivial topology is sheafification. -/
noncomputable def sheafBotInverseIso :
    (sheafBotEquivalence (C := AsSmall.{u} (SingleObj G)) (Type u)).inverse ≅
      presheafToSheaf ⊥ (Type u) :=
  (sheafBotEquivalence (Type u)).symm.toAdjunction.leftAdjointUniq
    (sheafificationAdjunction ⊥ (Type u))

/-- The action on the generic torsor is the Yoneda embedding of `SingleObj G`. -/
theorem actMor_genericTorsor (g : G) :
    actMor (genericTorsor G) g = (torsorYoneda G).map (hom g) := by
  change Pi.lift _ ≫ (Pi.π (fun _ : Fin 1 => (torsorYoneda G).obj (SingleObj.star G)) 0 ≫
    (torsorYoneda G).map (hom g)) = _
  rw [← Category.assoc, limit.lift_π]
  exact Category.id_comp _

/-- **Existence.** Every torsor in a sheaf topos is the image of the generic torsor under a left
exact left adjoint out of the topos of `G`-sets. -/
theorem exists_isomorphic_map (M : CatStructure (torsorLanguage G) (Sheaf K (Type u)))
    (hM : M.IsModel (torsorTheory G)) :
    ∃ (F : Sheaf (⊥ : GrothendieckTopology (AsSmall.{u} (SingleObj G))) (Type u) ⥤
        Sheaf K (Type u)) (_ : PreservesFiniteLimits F),
      F.IsLeftAdjoint ∧ M.Isomorphic ((genericTorsor G).map F) := by
  obtain ⟨F, hF, hF', ⟨e⟩⟩ := exists_leftAdjoint_of_isLocallyFiltering
    (J := (⊥ : GrothendieckTopology (AsSmall.{u} (SingleObj G)))) (torsorFunctor M hM)
    (isLocallyFiltering_torsorFunctor M hM) (mapsCoversToEpimorphicFamilies_torsorFunctor M hM)
  refine ⟨F, hF, hF', ?_⟩
  let ι := sheafBotInverseIso G
  let star := AsSmall.up.obj (SingleObj.star G)
  let c : ((genericTorsor G).map F).carrier ≅ M.carrier :=
    F.mapIso (ι.app (yoneda.obj star)) ≪≫ e.app star
  refine (isomorphic_of_iso _ _ c fun g => ?_).symm
  rw [actMor_map, actMor_genericTorsor]
  have h₁ := ι.hom.naturality (yoneda.map (AsSmall.up.map (hom g)))
  have h₂ := e.hom.naturality (AsSmall.up.map (hom g))
  change F.map ((sheafBotEquivalence (Type u)).inverse.map (yoneda.map (AsSmall.up.map (hom g)))) ≫
    F.map (ι.hom.app _) ≫ e.hom.app star = (F.map (ι.hom.app _) ≫ e.hom.app star) ≫ _
  rw [← Category.assoc, ← F.map_comp, h₁, F.map_comp, Category.assoc]
  exact congrArg (F.map (ι.hom.app _) ≫ ·) h₂

variable (F F' : Sheaf (⊥ : GrothendieckTopology (AsSmall.{u} (SingleObj G))) (Type u) ⥤
    Sheaf K (Type u)) [PreservesFiniteLimits F] [PreservesFiniteLimits F']

/-- **Homomorphisms.** Natural transformations between left exact left adjoints out of the topos
of `G`-sets are determined by their component at the generic torsor, and these components are
exactly the homomorphisms between the image torsors. -/
theorem natTrans_app_genericTorsor (hF : F.IsLeftAdjoint) (_hF' : F'.IsLeftAdjoint) :
    Function.Injective (fun α : F ⟶ F' => α.app (genericTorsor G).carrier) ∧
      ∀ h : F.obj (genericTorsor G).carrier ⟶ F'.obj (genericTorsor G).carrier,
        ((genericTorsor G).map F).IsHom ((genericTorsor G).map F') h ↔
          ∃ α : F ⟶ F', α.app (genericTorsor G).carrier = h := by
  let e := sheafBotEquivalence (C := AsSmall.{u} (SingleObj G)) (Type u)
  have he := (e.congrLeft (E := Sheaf K (Type u))).fullyFaithfulFunctor
  have hy := Syntactic.bijective_whiskerLeft_yoneda (e.inverse ⋙ F) (e.inverse ⋙ F')
  refine ⟨fun α α' hαα' => ?_, fun h => ⟨fun hh => ?_, ?_⟩⟩
  · apply he.map_injective
    apply hy.1
    exact NatTrans.ext (funext fun _ => hαα')
  · rw [isHom_iff] at hh
    let γ : yoneda ⋙ e.inverse ⋙ F ⟶ yoneda ⋙ e.inverse ⋙ F' :=
      { app _ := h
        naturality X Y f := by
          have := hh (AsSmall.down.map f : G)
          rw [actMor_map, actMor_map, actMor_genericTorsor] at this
          exact this }
    obtain ⟨β, hβ⟩ := hy.2 γ
    refine ⟨he.preimage β, ?_⟩
    have := congrArg (fun β : e.inverse ⋙ F ⟶ e.inverse ⋙ F' =>
      β.app (yoneda.obj (AsSmall.up.obj (SingleObj.star G)))) (he.map_preimage β)
    exact this.trans (congrArg (fun δ => δ.app (AsSmall.up.obj (SingleObj.star G))) hβ)
  · rintro ⟨α, rfl⟩
    exact (genericTorsor G).isHom_map_app α

end Classification

end Torsor

/-- **`G`-sets classify `G`-torsors (roadmap 3.3).** The presheaf topos on `SingleObj G`, the topos
of right `G`-sets, with the generic torsor (the representable presheaf, `G` acting on the left),
classifies the geometric theory of `G`-torsors. -/
theorem isClassifyingSite_genericTorsor (G : Type u) [Group G] :
    IsClassifyingSite (torsorTheory G) (⊥ : GrothendieckTopology (AsSmall.{u} (SingleObj G)))
      (genericTorsor G) :=
  ⟨isModel_genericTorsor G, fun _ _ _ => ⟨fun M hM => Torsor.exists_isomorphic_map M hM,
    fun F F' _ _ hF hF' => Torsor.natTrans_app_genericTorsor F F' hF hF'⟩⟩

section Morita

namespace Torsor

variable {G H : Type u} [Group G] [Group H]

/-- The one-object category of a group is idempotent complete: its only idempotent is the
identity. -/
instance isIdempotentComplete_asSmall_singleObj :
    IsIdempotentComplete (AsSmall.{u} (SingleObj G)) where
  idempotents_split X p hp := by
    have h₁ : (p.down : G) * p.down = p.down := congrArg ULift.down hp
    have hp₁ : p = 𝟙 X := ULift.ext (mul_left_cancel (h₁.trans (mul_one _).symm))
    exact ⟨X, 𝟙 X, 𝟙 X, Category.id_comp _, by rw [hp₁, Category.id_comp]⟩

/-- An equivalence between the one-object categories of two groups gives an isomorphism of the
groups: the action of the functor on endomorphisms of the unique object. -/
noncomputable def mulEquivOfEquivalence
    (e : AsSmall.{u} (SingleObj G) ≌ AsSmall.{u} (SingleObj H)) : G ≃* H :=
  let φ : G →* H :=
    { toFun g := (e.functor.map (AsSmall.up.map (hom g))).down
      map_one' := by
        change (e.functor.map (𝟙 _)).down = 1
        rw [CategoryTheory.Functor.map_id]
        rfl
      map_mul' g h := by
        change (e.functor.map (AsSmall.up.map (hom h) ≫ AsSmall.up.map (hom g))).down = _
        rw [CategoryTheory.Functor.map_comp]
        rfl }
  MulEquiv.ofBijective φ
    ⟨fun g g' hgg' => congrArg ULift.down (e.functor.map_injective (ULift.ext hgg')),
      fun y => ⟨(e.functor.preimage (⟨y⟩ : e.functor.obj (AsSmall.up.obj (SingleObj.star G)) ⟶
        e.functor.obj (AsSmall.up.obj (SingleObj.star G)))).down,
        congrArg ULift.down (e.functor.map_preimage _)⟩⟩

end Torsor

/-- **3.3, converse.** Morita-equivalent theories of torsors come from isomorphic groups: the
classifying topoi `Psh(SingleObj G)` and `Psh(SingleObj H)` are equivalent, hence so are the
Karoubi envelopes of `SingleObj G` and `SingleObj H` (`moritaEquivalentCat_iff_karoubi`), which
are these categories themselves. -/
theorem nonempty_mulEquiv_of_moritaEquivalent {G H : Type u} [Group G] [Group H]
    (h : MoritaEquivalent (torsorTheory G) (torsorTheory H)) : Nonempty (G ≃* H) := by
  obtain ⟨C, C', _, _, J, J', U, U', hU, hU', ⟨E⟩⟩ := h
  obtain ⟨e₁, -⟩ := (isClassifyingSite_genericTorsor G).exists_equivalence hU
  obtain ⟨e₂, -⟩ := hU'.exists_equivalence (isClassifyingSite_genericTorsor H)
  have hm : ToposTheoreticBridges.MoritaEquivalentCat (AsSmall.{u} (SingleObj G))
      (AsSmall.{u} (SingleObj H)) :=
    ⟨(sheafBotEquivalence (Type u)).symm.trans
      (e₁.trans (E.trans (e₂.trans (sheafBotEquivalence (Type u)))))⟩
  obtain ⟨k⟩ := (ToposTheoreticBridges.moritaEquivalentCat_iff_karoubi _ _).1 hm
  exact ⟨Torsor.mulEquivOfEquivalence ((Idempotents.toKaroubi _).asEquivalence.trans
    (k.trans (Idempotents.toKaroubi _).asEquivalence.symm))⟩

/-- **3.3.** The theories of `G`-torsors and of `H`-torsors are Morita equivalent exactly when
the groups `G` and `H` are isomorphic. -/
theorem moritaEquivalent_torsorTheory_iff {G H : Type u} [Group G] [Group H] :
    MoritaEquivalent (torsorTheory G) (torsorTheory H) ↔ Nonempty (G ≃* H) :=
  ⟨nonempty_mulEquiv_of_moritaEquivalent, fun ⟨e⟩ => moritaEquivalent_torsorTheory_of_mulEquiv e⟩

end Morita

end LeanPool.ClassifyingTopoi
