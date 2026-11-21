/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.NormalFormSemantics
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Unconditional

/-!
# Torsors (roadmap 3.3)

The language of `G`-sets (`LeanPool.ClassifyingTopoi.torsorLanguage`, one unary function symbol
for each element of `G`), the theory of `G`-torsors (`LeanPool.ClassifyingTopoi.torsorTheory`)
and the generic torsor (`LeanPool.ClassifyingTopoi.genericTorsor`), the representable presheaf on
`SingleObj G` with `G` acting by postcomposition.

## Main results

* `LeanPool.ClassifyingTopoi.isModel_genericTorsor`: the generic torsor is a model of the theory
  of `G`-torsors. In the presheaf topos the interpretation is computed fiberwise
  (`CatStructure.isModel_of_forall_fiberStr`, from the Kripke–Joyal semantics of
  `Syntactic.mem_range_interp_app_iff`), and each fiber is `G` with left multiplication;
* `LeanPool.ClassifyingTopoi.moritaEquivalent_torsorTheory_of_mulEquiv`: isomorphic groups have
  Morita-equivalent theories of torsors. Along `e : G ≃* H` the reduct of a structure
  (`CatStructure.reduct`, with `CatStructure.interp_reduct` for the translated formulas
  `GeometricFormula.onLHom`) maps models of the theory of `H`-torsors to models of the theory of
  `G`-torsors, so the reduct of the generic model of a classifying site of `G`-torsors classifies
  `H`-torsors (`Torsor.isClassifyingSite_reduct`).

The classification of torsors by the presheaf topos on `SingleObj G`
(`isClassifyingSite_genericTorsor`) and the converse of the Morita criterion
(`moritaEquivalent_torsorTheory_iff`) are in
`LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.TorsorClassification`.
-/

@[expose] public section

universe u u₁ u₂

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance high] Sheaf.instHasColimitsOfShape

/-- **3.3.** The function symbols of the language of `G`-sets: one unary symbol for each element
of `G`. -/
def torsorFunctions (G : Type u) : ℕ → Type u
  | 1 => G
  | _ => PEmpty

/-- **3.3.** The language of `G`-sets. -/
def torsorLanguage (G : Type u) : FirstOrder.Language.{u, u} :=
  ⟨torsorFunctions G, fun _ => PEmpty⟩

/-- **3.3.** The unary function symbol of an element of `G`. -/
def torsorSymbol {G : Type u} (g : G) : (torsorLanguage G).Functions 1 :=
  g

/-- **3.3.** The term `g · t`. -/
def torsorAct {G : Type u} {n : ℕ} (g : G) (t : (torsorLanguage G).Term (Fin n)) :
    (torsorLanguage G).Term (Fin n) :=
  FirstOrder.Language.Functions.apply₁ (g : (torsorLanguage G).Functions 1) t

/-- **3.3.** The theory of `G`-torsors: a left action (`1 · x = x`,
`(g * h) · x = g · (h · x)`), inhabited (`⊢ ∃ x, ⊤`), transitive (`⊢ ⋁_g g · x = y`) and free
(`g · x = h · x ⊢ ⊥` for `g ≠ h`). -/
def torsorTheory (G : Type u) [Group G] : GeometricTheory.{u} (torsorLanguage G) :=
  {⟨1, .top, .equal (torsorAct 1 (.var 0)) (.var 0)⟩} ∪
  Set.range (fun gh : G × G => ⟨1, .top,
    .equal (torsorAct (gh.1 * gh.2) (.var 0)) (torsorAct gh.1 (torsorAct gh.2 (.var 0)))⟩) ∪
  {⟨0, .top, .ex .top⟩} ∪
  {⟨2, .top, .iSup fun g : G => .equal (torsorAct g (.var 0)) (.var 1)⟩} ∪
  {σ | ∃ g h : G, g ≠ h ∧
    σ = ⟨1, .equal (torsorAct g (.var 0)) (torsorAct h (.var 0)), .bot⟩}

section TorsorAxioms

variable {G : Type u} [Group G]

/-- The axiom `⊢ 1 · x = x` of `torsorTheory`. -/
theorem one_mem_torsorTheory :
    (⟨1, .top, .equal (torsorAct 1 (.var 0)) (.var 0)⟩ : Sequent _) ∈ torsorTheory G :=
  Or.inl (Or.inl (Or.inl (Or.inl rfl)))

/-- The axiom `⊢ (g * h) · x = g · (h · x)` of `torsorTheory`. -/
theorem mul_mem_torsorTheory (g h : G) :
    (⟨1, .top, .equal (torsorAct (g * h) (.var 0)) (torsorAct g (torsorAct h (.var 0)))⟩ :
      Sequent _) ∈ torsorTheory G :=
  Or.inl (Or.inl (Or.inl (Or.inr ⟨(g, h), rfl⟩)))

/-- The axiom `⊢ ∃ x, ⊤` of `torsorTheory`. -/
theorem nonempty_mem_torsorTheory : (⟨0, .top, .ex .top⟩ : Sequent _) ∈ torsorTheory G :=
  Or.inl (Or.inl (Or.inr rfl))

/-- The axiom `⊢ ⋁_g g · x = y` of `torsorTheory`. -/
theorem transitive_mem_torsorTheory :
    (⟨2, .top, .iSup fun g : G => .equal (torsorAct g (.var 0)) (.var 1)⟩ : Sequent _) ∈
      torsorTheory G :=
  Or.inl (Or.inr rfl)

/-- The axiom `g · x = h · x ⊢ ⊥` of `torsorTheory`, for `g ≠ h`. -/
theorem free_mem_torsorTheory {g h : G} (hne : g ≠ h) :
    (⟨1, .equal (torsorAct g (.var 0)) (torsorAct h (.var 0)), .bot⟩ : Sequent _) ∈
      torsorTheory G :=
  Or.inr ⟨g, h, hne, rfl⟩

end TorsorAxioms

/-- **3.3.** The Yoneda embedding of `SingleObj G` into the topos of right `G`-sets. -/
noncomputable abbrev torsorYoneda (G : Type u) [Group G] :
    SingleObj G ⥤ Sheaf (⊥ : GrothendieckTopology (AsSmall.{u} (SingleObj G))) (Type u) :=
  AsSmall.up ⋙ yoneda ⋙ (sheafBotEquivalence (Type u)).inverse

/-- **3.3.** The generic `G`-torsor: `G` as a right `G`-set, the representable presheaf, with
`G` acting on the left by multiplication. -/
noncomputable def genericTorsor (G : Type u) [Group G] :
    CatStructure (torsorLanguage G)
      (Sheaf (⊥ : GrothendieckTopology (AsSmall.{u} (SingleObj G))) (Type u)) where
  carrier := (torsorYoneda G).obj (SingleObj.star G)
  funMap {k} f := match k, f with
    | 1, g => Pi.π (fun _ : Fin 1 => (torsorYoneda G).obj (SingleObj.star G)) 0 ≫
        (torsorYoneda G).map (g : SingleObj.star G ⟶ SingleObj.star G)
  relMap R := PEmpty.elim R

/-- A structure in a presheaf topos whose fibers are all set-models of `T` is a model of `T`. -/
theorem CatStructure.isModel_of_forall_fiberStr {L : Language.{u₁, u₂}} {D : Type u}
    [SmallCategory D] {T : GeometricTheory.{u} L} (P : CatStructure L (D ⥤ Type u))
    (h : ∀ d, letI := P.fiberStr d; T.IsSetModel (P.carrier.obj d)) : P.IsModel T := by
  intro σ hσ
  rw [Syntactic.le_iff_range_app_subset]
  intro d z hz
  rw [Syntactic.mem_range_interp_app_iff] at hz ⊢
  exact h d σ hσ _ hz

namespace Torsor

variable (G : Type u) [Group G]

/-- The generic torsor as a structure in the presheaf topos: the representable presheaf, with
`g` acting by postcomposition. -/
noncomputable abbrev genericPsh : CatStructure (torsorLanguage G)
    ((AsSmall.{u} (SingleObj G))ᵒᵖ ⥤ Type u) where
  carrier := yoneda.obj (AsSmall.up.obj (SingleObj.star G))
  funMap {k} f := match k, f with
    | 1, g => Pi.π (fun _ : Fin 1 => yoneda.obj (AsSmall.up.obj (SingleObj.star G))) 0 ≫
        yoneda.map (AsSmall.up.map (g : SingleObj.star G ⟶ SingleObj.star G))
  relMap R := PEmpty.elim R

variable {G}

/-- The endomorphism of the object of `SingleObj G` given by an element. -/
abbrev hom (g : G) : SingleObj.star G ⟶ SingleObj.star G :=
  g

/-- The action on the fibers of the generic torsor is composition, that is, left
multiplication. -/
theorem fiberStr_funMap (d : (AsSmall.{u} (SingleObj G))ᵒᵖ) (g : G)
    (x : Fin 1 → (genericPsh G).carrier.obj d) :
    ((genericPsh G).fiberStr d).funMap (torsorSymbol g) x =
      x 0 ≫ AsSmall.up.map (hom g) := by
  rw [CatStructure.fiberStr_funMap]
  change (yoneda.map _).app d ((Pi.π (fun _ : Fin 1 => (genericPsh G).carrier) 0).app d
    ((Syntactic.secEquiv _ 1 d).symm x)) = _
  rw [← Syntactic.secEquiv_apply, Equiv.apply_symm_apply]
  rfl

/-- The action of `G` on a fiber of the generic torsor: composition, that is, left
multiplication. -/
def act {d : (AsSmall.{u} (SingleObj G))ᵒᵖ} (g : G) (h : (genericPsh G).carrier.obj d) :
    (genericPsh G).carrier.obj d :=
  h ≫ AsSmall.up.map (hom g)

/-- The action on the fibers of the generic torsor. -/
theorem realize_torsorAct (d : (AsSmall.{u} (SingleObj G))ᵒᵖ) {n : ℕ} (g : G)
    (t : (torsorLanguage G).Term (Fin n)) (x : Fin n → (genericPsh G).carrier.obj d) :
    @Term.realize _ _ ((genericPsh G).fiberStr d) _ x (torsorAct g t) =
      act g (@Term.realize _ _ ((genericPsh G).fiberStr d) _ x t) :=
  fiberStr_funMap d g _

/-- The action of `G` on a fiber is left multiplication. -/
theorem down_act {d : (AsSmall.{u} (SingleObj G))ᵒᵖ} (g : G) (h : (genericPsh G).carrier.obj d) :
    (act g h).down = g * (show G from h.down) :=
  rfl

/-- Two elements of a fiber with the same element of `G` are equal. -/
theorem ext_fiber {d : (AsSmall.{u} (SingleObj G))ᵒᵖ} {h h' : (genericPsh G).carrier.obj d}
    (e : (show G from h.down) = (show G from h'.down)) : h = h' :=
  ULift.ext e

/-- The fibers of the generic torsor are `G`-torsors. -/
theorem isSetModel_fiberStr (d : (AsSmall.{u} (SingleObj G))ᵒᵖ) :
    letI := (genericPsh G).fiberStr d
    (torsorTheory G).IsSetModel ((genericPsh G).carrier.obj d) := by
  let := (genericPsh G).fiberStr d
  rintro σ ((((h | ⟨gh, rfl⟩) | h) | h) | ⟨g, h, hne, rfl⟩)
  · rw [Set.mem_singleton_iff] at h
    subst h
    intro x _
    change (torsorAct 1 (Term.var 0)).realize x = (Term.var 0).realize x
    rw [realize_torsorAct]
    exact ULift.ext (one_mul _)
  · intro (x : Fin 1 → (genericPsh G).carrier.obj d) _
    change (torsorAct _ _).realize x = (torsorAct _ (torsorAct _ _)).realize x
    rw [realize_torsorAct, realize_torsorAct, realize_torsorAct]
    exact ULift.ext (mul_assoc _ _ _)
  · rw [Set.mem_singleton_iff] at h
    subst h
    intro x _
    exact ⟨⟨(1 : G)⟩, trivial⟩
  · rw [Set.mem_singleton_iff] at h
    subst h
    intro (x : Fin 2 → (genericPsh G).carrier.obj d) _
    refine ⟨(show G from (x 1).down) * (show G from (x 0).down)⁻¹, ?_⟩
    change (torsorAct _ _).realize x = (Term.var 1).realize x
    rw [realize_torsorAct]
    exact ULift.ext (inv_mul_cancel_right _ _)
  · intro (x : Fin 1 → (genericPsh G).carrier.obj d) hx
    change (torsorAct _ _).realize x = (torsorAct _ _).realize x at hx
    rw [realize_torsorAct, realize_torsorAct] at hx
    exact (hne (mul_right_cancel (congrArg ULift.down hx))).elim

/-- The generic torsor in the presheaf topos is a model of the theory of torsors. -/
theorem isModel_genericPsh : (genericPsh G).IsModel (torsorTheory G) :=
  CatStructure.isModel_of_forall_fiberStr _ isSetModel_fiberStr

/-- The function symbols of the generic torsor, through the inclusion of presheaves as
sheaves. -/
theorem genericPsh_map_funMap_torsorSymbol (g : G) :
    ((genericPsh G).map (sheafBotEquivalence (Type u)).inverse).funMap (torsorSymbol g) =
      (genericTorsor G).funMap (torsorSymbol g) := by
  refine (IsIso.inv_comp_eq _).2 (((sheafBotEquivalence (Type u)).inverse.map_comp _ _).trans ?_)
  exact (congrArg (· ≫ (torsorYoneda G).map (hom g)) (piComparison_comp_π
    (sheafBotEquivalence (Type u)).inverse
    (fun _ : Fin 1 => yoneda.obj (AsSmall.up.obj (SingleObj.star G))) 0)).symm.trans
    (Category.assoc _ _ _)

/-- The function symbols of the generic torsor, through the inclusion of presheaves as
sheaves. -/
theorem genericPsh_map_funMap {k : ℕ} (f : (torsorLanguage G).Functions k) :
    ((genericPsh G).map (sheafBotEquivalence (Type u)).inverse).funMap f =
      (genericTorsor G).funMap f :=
  match k, f with
  | 0, f => PEmpty.elim f
  | 1, g => genericPsh_map_funMap_torsorSymbol (G := G) g
  | _ + 2, f => PEmpty.elim f

end Torsor

/-- **3.3.** The generic torsor is a model of the theory of `G`-torsors. -/
theorem isModel_genericTorsor (G : Type u) [Group G] :
    (genericTorsor G).IsModel (torsorTheory G) := by
  have h := (Torsor.isModel_genericPsh (G := G)).map_of_preserves
    (sheafBotEquivalence (Type u)).inverse
  refine (show ((Torsor.genericPsh G).map (sheafBotEquivalence (Type u)).inverse).Isomorphic
    (genericTorsor G) from ⟨Iso.refl _, ⟨fun f => ?_, fun R => PEmpty.elim R⟩,
      ⟨fun f => ?_, fun R => PEmpty.elim R⟩⟩).isModel h
  · exact (Category.comp_id _).trans ((Torsor.genericPsh_map_funMap f).trans
      ((Category.id_comp _).symm.trans (congrArg (· ≫ _) Limits.Pi.map_id.symm)))
  · exact (Category.comp_id _).trans ((Torsor.genericPsh_map_funMap f).symm.trans
      ((Category.id_comp _).symm.trans (congrArg (· ≫ _) Limits.Pi.map_id.symm)))


section Reduct

variable {L L' : Language.{u, u}} {E : Type*} [Category E] [HasFiniteProducts E]

/-- The translation of a geometric formula along a map of languages. -/
def GeometricFormula.onLHom (ϕ : L' →ᴸ L) : {n : ℕ} → GeometricFormula.{u} L' n →
    GeometricFormula.{u} L n
  | _, .top => .top
  | _, .and φ ψ => .and (φ.onLHom ϕ) (ψ.onLHom ϕ)
  | _, .iSup φ => .iSup fun i => (φ i).onLHom ϕ
  | _, .equal t₁ t₂ => .equal (ϕ.onTerm t₁) (ϕ.onTerm t₂)
  | _, .rel R ts => .rel (ϕ.onRelation R) fun i => ϕ.onTerm (ts i)
  | _, .ex φ => .ex (φ.onLHom ϕ)

/-- The reduct of a structure along a map of languages. -/
def CatStructure.reduct (ϕ : L' →ᴸ L) (M : CatStructure L E) : CatStructure L' E where
  carrier := M.carrier
  funMap f := M.funMap (ϕ.onFunction f)
  relMap R := M.relMap (ϕ.onRelation R)

/-- Terms in a reduct are interpreted by their translations. -/
theorem CatStructure.termMap_reduct (ϕ : L' →ᴸ L) (M : CatStructure L E) {n : ℕ}
    (t : L'.Term (Fin n)) : (M.reduct ϕ).termMap t = M.termMap (ϕ.onTerm t) := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    change Pi.lift (fun j => (M.reduct ϕ).termMap (ts j)) ≫ _ =
      Pi.lift (fun j => M.termMap (ϕ.onTerm (ts j))) ≫ _
    simp only [ih]
    rfl

/-- Formulas in a reduct are interpreted by their translations. -/
theorem CatStructure.interp_reduct [HasFiniteLimits E] [HasImages E] [HasCoproducts.{u} E]
    (ϕ : L' →ᴸ L) (M : CatStructure L E) {n : ℕ} (φ : GeometricFormula.{u} L' n) :
    (M.reduct ϕ).interp φ = M.interp (φ.onLHom ϕ) := by
  induction φ with
  | top => rfl
  | and φ ψ ihφ ihψ => exact congrArg₂ (· ⊓ ·) ihφ ihψ
  | @iSup n ι φ ih =>
    have key : ∀ S S' : ι → Subobject (M.pow n), S = S' →
        imageSubobject (Sigma.desc fun i => (S i).arrow) =
          imageSubobject (Sigma.desc fun i => (S' i).arrow) := by
      rintro S _ rfl
      rfl
    exact key _ _ (funext ih)
  | @equal m t₁ t₂ =>
    have key : ∀ f f' g g' : M.pow m ⟶ M.carrier, f = f' → g = g' →
        equalizerSubobject f g = equalizerSubobject f' g' := by
      rintro f _ g _ rfl rfl
      rfl
    exact key _ _ _ _ (termMap_reduct ϕ M t₁) (termMap_reduct ϕ M t₂)
  | @rel m k R ts =>
    have key : ∀ (f f' : M.pow m ⟶ ∏ᶜ fun _ : Fin k => M.carrier) (S : Subobject _),
        f = f' → (Subobject.pullback f).obj S = (Subobject.pullback f').obj S := by
      rintro f _ S rfl
      rfl
    exact key _ _ _ (by simp only [termMap_reduct]; rfl)
  | ex φ ih =>
    change (Subobject.exists _).obj _ = (Subobject.exists _).obj _
    rw [ih]
    rfl

/-- Homomorphisms are homomorphisms of the reducts. -/
theorem CatStructure.IsHom.reduct [HasFiniteLimits E] [HasImages E] (ϕ : L' →ᴸ L)
    {M N : CatStructure L E} {h : M.carrier ⟶ N.carrier} (hh : M.IsHom N h) :
    (M.reduct ϕ).IsHom (N.reduct ϕ) h :=
  ⟨fun f => hh.funMap (ϕ.onFunction f), fun R => hh.relMap (ϕ.onRelation R)⟩

/-- Isomorphic structures have isomorphic reducts. -/
theorem CatStructure.Isomorphic.reduct [HasFiniteLimits E] [HasImages E] (ϕ : L' →ᴸ L)
    {M N : CatStructure L E} (h : M.Isomorphic N) : (M.reduct ϕ).Isomorphic (N.reduct ϕ) :=
  let ⟨e, h₁, h₂⟩ := h
  ⟨e, h₁.reduct ϕ, h₂.reduct ϕ⟩

end Reduct

namespace Torsor

variable {G H : Type u} [Group G] [Group H]

/-- The map of languages of `G`-sets and `H`-sets induced by a map `G → H`. -/
def lHom (φ : G → H) : torsorLanguage G →ᴸ torsorLanguage H where
  onFunction {k} f := match k, f with
    | 1, g => torsorSymbol (φ g)
  onRelation _ R := PEmpty.elim R

omit [Group G] [Group H] in
/-- The translation of `g · t` is `φ g · t`. -/
theorem onTerm_torsorAct (φ : G → H) {n : ℕ} (g : G) (t : (torsorLanguage G).Term (Fin n)) :
    (lHom φ).onTerm (torsorAct g t) = torsorAct (φ g) ((lHom φ).onTerm t) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  rw [Subsingleton.elim i 0]
  rfl

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}

/-- A sequent holds in a structure when a sequent with the same realizations in all structures
on types holds. -/
theorem interp_le_of_realize_iff {L : Language.{u, u}} (M : CatStructure L (Sheaf K (Type u)))
    {n : ℕ} {φ ψ φ' ψ' : GeometricFormula.{u} L n} (h : M.interp φ' ≤ M.interp ψ')
    (h₁ : ∀ (N : Type u) [L.Structure N] (x : Fin n → N), φ.Realize x ↔ φ'.Realize x)
    (h₂ : ∀ (N : Type u) [L.Structure N] (x : Fin n → N), ψ.Realize x ↔ ψ'.Realize x) :
    M.interp φ ≤ M.interp ψ := by
  rw [CatStructure.interp_eq_of_realize_iff h₁, CatStructure.interp_eq_of_realize_iff h₂]
  exact h

/-- Along an isomorphism of groups, the reduct of a model of the theory of `H`-torsors is a
model of the theory of `G`-torsors. -/
theorem isModel_reduct (e : G ≃* H) {M : CatStructure (torsorLanguage H) (Sheaf K (Type u))}
    (hM : M.IsModel (torsorTheory H)) : (M.reduct (lHom e)).IsModel (torsorTheory G) := by
  rintro σ ((((h | ⟨gh, rfl⟩) | h) | h) | ⟨g, g', hne, rfl⟩) <;>
    rw [CatStructure.interp_reduct, CatStructure.interp_reduct]
  · rw [Set.mem_singleton_iff] at h
    subst h
    simp only [GeometricFormula.onLHom, onTerm_torsorAct, LHom.onTerm, map_one]
    exact hM _ one_mem_torsorTheory
  · simp only [GeometricFormula.onLHom, onTerm_torsorAct, LHom.onTerm, map_mul]
    exact hM _ (mul_mem_torsorTheory (e gh.1) (e gh.2))
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact hM _ nonempty_mem_torsorTheory
  · rw [Set.mem_singleton_iff] at h
    subst h
    refine interp_le_of_realize_iff M (hM _ transitive_mem_torsorTheory) (fun _ _ _ => Iff.rfl)
      fun N _ x => ?_
    simp only [GeometricFormula.onLHom, onTerm_torsorAct, LHom.onTerm]
    exact ⟨fun ⟨g, hg⟩ => ⟨e g, hg⟩, fun ⟨h, hh⟩ => ⟨e.symm h, by simpa using hh⟩⟩
  · refine interp_le_of_realize_iff M (hM _ (free_mem_torsorTheory (e.injective.ne hne)))
      (fun _ _ _ => ?_) fun _ _ _ => ?_
    · simp only [GeometricFormula.onLHom, onTerm_torsorAct, LHom.onTerm]
    · exact ⟨fun ⟨i, _⟩ => i.elim, fun ⟨i, _⟩ => i.elim⟩

/-- Reducing along an isomorphism of groups and back does not change the function symbols. -/
theorem funMap_reduct_reduct (e : G ≃* H) {E : Type*} [Category E] [HasFiniteProducts E]
    (M : CatStructure (torsorLanguage H) E) (h : H) :
    ((M.reduct (lHom e)).reduct (lHom e.symm)).funMap (torsorSymbol h) =
      M.funMap (torsorSymbol h) := by
  change M.funMap (torsorSymbol (e (e.symm h))) = M.funMap (torsorSymbol h)
  rw [MulEquiv.apply_symm_apply]

/-- Reducing along an isomorphism of groups and back does not change the function symbols. -/
theorem funMap_reduct_reduct' (e : G ≃* H) {E : Type*} [Category E] [HasFiniteProducts E]
    (M : CatStructure (torsorLanguage H) E) {k : ℕ} (f : (torsorLanguage H).Functions k) :
    ((M.reduct (lHom e)).reduct (lHom e.symm)).funMap f = M.funMap f :=
  match k, f with
  | 0, f => PEmpty.elim f
  | 1, h => funMap_reduct_reduct (H := H) e M h
  | _ + 2, f => PEmpty.elim f

/-- The identity is a homomorphism to the reduct along an isomorphism of groups and back. -/
theorem isHom_reduct_reduct (e : G ≃* H) {E : Type*} [Category E] [HasFiniteLimits E]
    [HasImages E] (M : CatStructure (torsorLanguage H) E) :
    M.IsHom ((M.reduct (lHom e)).reduct (lHom e.symm)) (𝟙 _) := by
  refine ⟨fun f => ?_, fun R => PEmpty.elim R⟩
  rw [funMap_reduct_reduct']
  exact (Category.comp_id _).trans ((Category.id_comp _).symm.trans
    (congrArg (· ≫ _) Limits.Pi.map_id.symm))

/-- The identity is a homomorphism from the reduct along an isomorphism of groups and back. -/
theorem isHom_reduct_reduct' (e : G ≃* H) {E : Type*} [Category E] [HasFiniteLimits E]
    [HasImages E] (M : CatStructure (torsorLanguage H) E) :
    ((M.reduct (lHom e)).reduct (lHom e.symm)).IsHom M (𝟙 _) := by
  refine ⟨fun f => ?_, fun R => PEmpty.elim R⟩
  rw [funMap_reduct_reduct']
  exact (Category.comp_id _).trans ((Category.id_comp _).symm.trans
    (congrArg (· ≫ _) Limits.Pi.map_id.symm))

/-- Reducing along an isomorphism of groups and back gives an isomorphic structure. -/
theorem isomorphic_reduct_reduct (e : G ≃* H) {E : Type*} [Category E] [HasFiniteLimits E]
    [HasImages E] (M : CatStructure (torsorLanguage H) E) :
    M.Isomorphic ((M.reduct (lHom e)).reduct (lHom e.symm)) :=
  ⟨Iso.refl _, isHom_reduct_reduct e M, isHom_reduct_reduct' e M⟩

/-- Reducts along a map of languages commute with the image under a functor. -/
theorem reduct_map {L L' : Language.{u, u}} (ϕ : L' →ᴸ L) {E E' : Type*} [Category E]
    [Category E'] [HasFiniteProducts E] [HasFiniteProducts E'] (M : CatStructure L E) (F : E ⥤ E')
    [PreservesFiniteProducts F] : (M.map F).reduct ϕ = (M.reduct ϕ).map F :=
  rfl

omit [SmallCategory D] in
/-- Along an isomorphism of groups, a classifying site of the theory of `G`-torsors classifies
the theory of `H`-torsors, with the reduct of its generic model. -/
theorem isClassifyingSite_reduct (e : G ≃* H) {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {U : CatStructure (torsorLanguage G) (Sheaf J (Type u))}
    (hU : IsClassifyingSite (torsorTheory G) J U) :
    IsClassifyingSite (torsorTheory H) J (U.reduct (lHom e.symm)) := by
  refine ⟨isModel_reduct e.symm hU.isModel, fun D _ K => ⟨fun M hM => ?_,
    fun F F' _ _ hF hF' => ?_⟩⟩
  · obtain ⟨F, hFl, hF, hMF⟩ := hU.exists_isomorphic (isModel_reduct e hM)
    exact ⟨F, hFl, hF, (isomorphic_reduct_reduct e M).trans (hMF.reduct _)⟩
  · obtain ⟨hinj, hhom⟩ := (hU.2 D K).2 F F' hF hF'
    refine ⟨hinj, fun h => ⟨fun hh => (hhom h).1 ?_, fun hh => ((hhom h).2 hh).reduct _⟩⟩
    have := ((isHom_reduct_reduct e.symm (U.map F)).comp (hh.reduct (lHom e))).comp
      (isHom_reduct_reduct' e.symm (U.map F'))
    refine (congrArg (fun k : F.obj U.carrier ⟶ F'.obj U.carrier =>
      (U.map F).IsHom (U.map F') k) ?_).mpr this
    exact (Category.id_comp h).symm.trans (Category.comp_id _).symm

end Torsor

/-- **3.3, one direction.** Isomorphic groups have Morita-equivalent theories of torsors. -/
theorem moritaEquivalent_torsorTheory_of_mulEquiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) : MoritaEquivalent (torsorTheory G) (torsorTheory H) := by
  obtain ⟨C, _, J, U, hU⟩ := exists_isClassifyingSite.{u, u, u} (torsorTheory G)
  exact ⟨C, C, inferInstance, inferInstance, J, J, U, _, hU, Torsor.isClassifyingSite_reduct e hU,
    ⟨CategoryTheory.Equivalence.refl⟩⟩

end LeanPool.ClassifyingTopoi
