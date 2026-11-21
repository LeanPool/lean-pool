/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Unconditional
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Diaconescu
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Provability
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-!
# Theories of presheaf type: Horn theories (roadmap 3.1)

A geometric theory is *of presheaf type* (`LeanPool.ClassifyingTopoi.IsOfPresheafType`) when it
has a classifying site with the trivial topology, that is, when it is classified by a presheaf
topos. This file proves that Horn theories are of presheaf type
(`LeanPool.ClassifyingTopoi.isOfPresheafType_of_isHorn`).

## Construction

* `LeanPool.ClassifyingTopoi.GeometricTheory.Entails`: semantic consequence, validity of a sequent
  in every model of `T` in a topos of sheaves on a small site; it is closed under the rules used
  below (cut, conjunction, substitution, sequents valid in all structures on types).
* `LeanPool.ClassifyingTopoi.Syntactic.HornTheoryCat T`: the Horn category of `T`, with the Horn
  formulas in context as objects and the tuples of terms `σ` with `T ⊨ X ⊢ Y[σ]` as morphisms
  `X ⟶ Y`, up to entailed equality. For a Horn theory this is the cartesian syntactic category,
  equivalent to the opposite of the finitely presented models.
* The identity on objects `HornTheoryCat.quotientFunctor T : HornCat L ⥤ HornTheoryCat T` is cover
  dense, locally full and locally faithful for the trivial topology (one adds the atoms of the
  target, or the equalities of two tuples, to the source formula). By the comparison lemma
  (Mathlib's `Functor.IsDenseSubsite.sheafEquiv`), the topos of sheaves on the Horn category for
  the induced topology `HornCat.theoryTopology T` is equivalent to the presheaf topos on
  `HornTheoryCat T`.
* `HornCat.theoryTopology_le_quotientTopology`: for every theory, the induced topology is coarser
  than the topology `quotientTopology (genericSheaf L) T` classifying `T`: a left exact left
  adjoint mapping the generic structure to a model of `T` inverts the inclusion of every covering
  sieve, which contains a morphism split up to entailment (`HornCat.isIso_map_functorInclusion`).
* `HornCat.quotientTopology_le_theoryTopology`: for a Horn theory, the sheafification for the
  induced topology makes the generic structure a model of `T`, since an axiom `φ ⊢ ψ` becomes the
  inclusion of the Horn formula `φ ∧ ψ` in `φ`, which generates a covering sieve.
* Hence the two topologies agree for Horn theories (`HornCat.theoryTopology_eq`), the Horn category
  with the induced topology classifies `T`, and transporting along the comparison equivalence
  (`IsClassifyingSite.of_equivalence`) the presheaf topos on `HornTheoryCat T` classifies `T`
  (`Syntactic.HornTheoryCat.isClassifyingSite`).

The construction works in the universe `max u₁ u₂ u` of the language and of the theory's
disjunctions, as the classifying sites of `LeanPool.ClassifyingTopoi.Unconditional`. The generic
model on `HornTheoryCat T` is the image of the sheafified generic structure under the comparison
equivalence; it is not identified with the Yoneda embedding.
-/

@[expose] public section

universe u u₁ u₂

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance high] Sheaf.instHasColimitsOfShape

variable {L : Language.{u₁, u₂}}

namespace GeometricTheory

/-- Semantic consequence: `φ ⊢ ψ` holds in every model of `T` in a topos of sheaves on a small
site. -/
def Entails (T : GeometricTheory.{u} L) {n : ℕ} (φ ψ : GeometricFormula.{u} L n) : Prop :=
  ∀ (D : Type u) [SmallCategory D] (K : GrothendieckTopology D)
    (M : CatStructure L (Sheaf K (Type u))), M.IsModel T → M.interp φ ≤ M.interp ψ

namespace Entails

variable {T : GeometricTheory.{u} L} {n : ℕ} {φ ψ χ : GeometricFormula.{u} L n}

/-- Semantic consequence is transitive. -/
theorem trans (h : T.Entails φ ψ) (h' : T.Entails ψ χ) : T.Entails φ χ :=
  fun D _ K M hM => (h D K M hM).trans (h' D K M hM)

/-- A sequent valid in every structure on a type is a semantic consequence. -/
theorem of_realize (h : ∀ (N : Type u) [L.Structure N] (x : Fin n → N), φ.Realize x → ψ.Realize x) :
    T.Entails φ ψ :=
  fun _ _ _ M _ => M.interp_le_of_realize h

/-- The axioms of `T` are semantic consequences. -/
theorem of_mem {σ : Sequent.{u} L} (h : σ ∈ T) : T.Entails σ.lhs σ.rhs :=
  fun _ _ _ _ hM => hM σ h

/-- Introduction of a conjunction. -/
theorem and_intro (h : T.Entails φ ψ) (h' : T.Entails φ χ) : T.Entails φ (.and ψ χ) :=
  fun D _ K M hM => le_inf (h D K M hM) (h' D K M hM)

/-- Semantic consequence is stable under substitution. -/
theorem subst (h : T.Entails φ ψ) {m : ℕ} (σ : Fin n → L.Term (Fin m)) :
    T.Entails (φ.subst σ) (ψ.subst σ) := fun D _ K M hM => by
  rw [M.interp_subst, M.interp_subst]
  exact (Subobject.pullback _).monotone (h D K M hM)

/-- The conjunction of a list of semantic consequences. -/
theorem foldr {l : List (GeometricFormula.{u} L n)} (h : ∀ ψ ∈ l, T.Entails φ ψ) :
    T.Entails φ (l.foldr .and .top) := by
  induction l with
  | nil => exact fun _ _ _ _ _ => le_top
  | cons ψ l ih =>
    exact and_intro (h ψ List.mem_cons_self) (ih fun χ hχ => h χ (List.mem_cons_of_mem _ hχ))

/-- The realization of a conjunction of a list of formulas. -/
theorem _root_.LeanPool.ClassifyingTopoi.GeometricFormula.realize_foldr_and {N : Type*}
    [L.Structure N] (l : List (GeometricFormula.{u} L n)) (x : Fin n → N) :
    (l.foldr GeometricFormula.and GeometricFormula.top).Realize x ↔ ∀ ψ ∈ l, ψ.Realize x := by
  induction l with
  | nil => simp [GeometricFormula.Realize]
  | cons ψ l ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp, ← ih]
    rfl

/-- A formula entailed by a list of semantic consequences in every structure on a type is a
semantic consequence. -/
theorem of_forall_mem (l : List (GeometricFormula.{u} L n)) (h : ∀ ψ ∈ l, T.Entails φ ψ)
    (hχ : ∀ (N : Type u) [L.Structure N] (x : Fin n → N), (∀ ψ ∈ l, ψ.Realize x) → χ.Realize x) :
    T.Entails φ χ :=
  (foldr h).trans (of_realize fun N _ x hx =>
    hχ N x ((GeometricFormula.realize_foldr_and l x).1 hx))

end Entails

end GeometricTheory

namespace Syntactic

/-- The Horn category of a theory `T`: the Horn formulas in context, with the tuples of terms
`σ` such that `X ⊢ Y[σ]` is a semantic consequence of `T`, two tuples being identified when
`T` entails their equality on `X`. For a Horn theory its presheaf topos classifies `T`. -/
structure HornTheoryCat (T : GeometricTheory.{max u₁ u₂ u} L) : Type (max u₁ u₂ u) where
  /-- The underlying Horn formula in context. -/
  obj : HornCat.{u} L

namespace HornTheoryCat

variable {T : GeometricTheory.{max u₁ u₂ u} L}

variable (T) in
/-- A tuple of terms is a morphism `X ⟶ Y` of the Horn category of `T` when `T` entails
`X ⊢ Y[σ]`. -/
def IsMor (X Y : HornCat.{u} L) (σ : Fin Y.n → L.Term (Fin X.n)) : Prop :=
  T.Entails X.toFormula (Y.toFormula.subst σ)

variable (T) in
/-- Two morphisms are identified when `T` entails the equality of their terms. -/
def homSetoid (X Y : HornCat.{u} L) : Setoid {σ // IsMor T X Y σ} where
  r σ τ := ∀ i, T.Entails X.toFormula (.equal (σ.1 i) (τ.1 i))
  iseqv :=
    { refl := fun _ _ => GeometricTheory.Entails.of_realize fun _ _ _ _ => rfl
      symm := fun h i => (h i).trans (GeometricTheory.Entails.of_realize fun _ _ _ hx =>
        Eq.symm hx)
      trans := fun h h' i => ((h i).and_intro (h' i)).trans
        (GeometricTheory.Entails.of_realize fun _ _ _ hx => Eq.trans hx.1 hx.2) }

/-- The realization of a substituted Horn formula. -/
theorem realize_toFormula_subst {N : Type*} [L.Structure N] (X : HornCat.{u} L) {m : ℕ}
    (σ : Fin X.n → L.Term (Fin m)) (x : Fin m → N) :
    ((X.toFormula : GeometricFormula.{max u₁ u₂ u} L X.n).subst σ).Realize x ↔
      X.Holds fun i => (σ i).realize x := by
  rw [GeometricFormula.realize_subst, HornCat.realize_toFormula]

/-- The identity tuple is a morphism. -/
theorem isMor_id (X : HornCat.{u} L) : IsMor T X X fun i => Term.var i :=
  GeometricTheory.Entails.of_realize fun _ _ x hx => by
    rw [realize_toFormula_subst]
    exact (HornCat.realize_toFormula X x).1 hx

/-- Composition of tuples of terms is a morphism. -/
theorem isMor_comp {X Y Z : HornCat.{u} L} {σ : Fin Y.n → L.Term (Fin X.n)}
    {τ : Fin Z.n → L.Term (Fin Y.n)} (hσ : IsMor T X Y σ) (hτ : IsMor T Y Z τ) :
    IsMor T X Z fun i => (τ i).subst σ :=
  hσ.trans ((hτ.subst σ).trans (GeometricTheory.Entails.of_realize fun _ _ x hx => by
    rw [GeometricFormula.realize_subst, realize_toFormula_subst] at hx
    rw [realize_toFormula_subst]
    simpa [Term.realize_subst] using hx))

/-- Substitution of terms entailed to be equal. -/
theorem entails_equal_subst {X : HornCat.{u} L} {m : ℕ} {σ σ' : Fin m → L.Term (Fin X.n)}
    (h : ∀ i, T.Entails X.toFormula (.equal (σ i) (σ' i))) (t : L.Term (Fin m)) :
    T.Entails X.toFormula (.equal (t.subst σ) (t.subst σ')) :=
  GeometricTheory.Entails.of_forall_mem (List.ofFn fun i => .equal (σ i) (σ' i))
    (by simpa using h) fun _ _ x hx => by
      simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff] at hx
      change (t.subst σ).realize x = (t.subst σ').realize x
      rw [Term.realize_subst, Term.realize_subst]
      congr 1
      funext i
      exact hx i

/-- Transitivity of entailed equalities. -/
theorem entails_equal_trans {X : HornCat.{u} L} {t₁ t₂ t₃ : L.Term (Fin X.n)}
    (h : T.Entails X.toFormula (.equal t₁ t₂)) (h' : T.Entails X.toFormula (.equal t₂ t₃)) :
    T.Entails X.toFormula (.equal t₁ t₃) :=
  (h.and_intro h').trans (GeometricTheory.Entails.of_realize fun _ _ _ hx => Eq.trans hx.1 hx.2)

/-- Morphisms of the Horn category of `T`: tuples of terms up to entailed equality. -/
structure Hom (X Y : HornTheoryCat.{u} T) : Type (max u₁ u₂ u) where
  /-- The underlying class of tuples of terms. -/
  q : Quotient (homSetoid T X.obj Y.obj)

instance : Category (HornTheoryCat.{u} T) where
  Hom := Hom
  id X := ⟨⟦⟨_, isMor_id X.obj⟩⟧⟩
  comp f g := ⟨Quotient.map₂ (fun σ τ => ⟨_, isMor_comp σ.2 τ.2⟩)
    (fun σ σ' hσ τ τ' hτ j => entails_equal_trans (σ.2.trans ((hτ j).subst σ.1))
      (entails_equal_subst hσ (τ'.1 j))) f.q g.q⟩
  id_comp f := by
    obtain ⟨f⟩ := f
    induction f using Quotient.ind
    exact congrArg Hom.mk (Quotient.sound fun i => GeometricTheory.Entails.of_realize
      fun _ _ _ _ => by simp [GeometricFormula.Realize, Term.realize_subst])
  comp_id f := by
    obtain ⟨f⟩ := f
    induction f using Quotient.ind
    exact congrArg Hom.mk (Quotient.sound fun i => GeometricTheory.Entails.of_realize
      fun _ _ _ _ => by simp [GeometricFormula.Realize])
  assoc f g h := by
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    obtain ⟨h⟩ := h
    induction f using Quotient.ind
    induction g using Quotient.ind
    induction h using Quotient.ind
    exact congrArg Hom.mk (Quotient.sound fun i => GeometricTheory.Entails.of_realize
      fun _ _ _ _ => by simp [GeometricFormula.Realize, Term.realize_subst])

/-- The morphism of the Horn category of `T` given by a tuple of terms. -/
def mor {X Y : HornCat.{u} L} (σ : Fin Y.n → L.Term (Fin X.n)) (hσ : IsMor T X Y σ) :
    (⟨X⟩ : HornTheoryCat.{u} T) ⟶ ⟨Y⟩ :=
  ⟨⟦⟨σ, hσ⟩⟧⟩

/-- Every morphism of the Horn category of `T` is given by a tuple of terms. -/
theorem exists_eq_mor {X Y : HornTheoryCat.{u} T} (f : X ⟶ Y) :
    ∃ (σ : Fin Y.obj.n → L.Term (Fin X.obj.n)) (hσ : IsMor T X.obj Y.obj σ), f = mor σ hσ := by
  obtain ⟨f⟩ := f
  induction f using Quotient.ind with | _ σ => exact ⟨σ.1, σ.2, rfl⟩

/-- Equality of morphisms of the Horn category of `T`. -/
theorem mor_eq_mor_iff {X Y : HornCat.{u} L} {σ τ : Fin Y.n → L.Term (Fin X.n)}
    (hσ : IsMor T X Y σ) (hτ : IsMor T X Y τ) :
    mor σ hσ = mor τ hτ ↔ ∀ i, T.Entails X.toFormula (.equal (σ i) (τ i)) :=
  ⟨fun h => Quotient.exact (congrArg Hom.q h), fun h => congrArg Hom.mk (Quotient.sound h)⟩

/-- Composition is substitution. -/
theorem mor_comp_mor {X Y Z : HornCat.{u} L} {σ : Fin Y.n → L.Term (Fin X.n)}
    {τ : Fin Z.n → L.Term (Fin Y.n)} (hσ : IsMor T X Y σ) (hτ : IsMor T Y Z τ) :
    mor σ hσ ≫ mor τ hτ = mor (fun i => (τ i).subst σ) (isMor_comp hσ hτ) :=
  rfl

/-- The identity is the tuple of variables. -/
theorem id_eq_mor (X : HornCat.{u} L) :
    𝟙 (⟨X⟩ : HornTheoryCat.{u} T) = mor (fun i => Term.var i) (isMor_id X) :=
  rfl

/-- A morphism of the Horn category of the language is a morphism of the Horn category of `T`. -/
theorem isMor_of_isMor {X Y : HornCat.{u} L} {σ : Fin Y.n → L.Term (Fin X.n)}
    (hσ : HornCat.IsMor X Y σ) : IsMor T X Y σ :=
  GeometricTheory.Entails.of_realize fun N _ x hx => by
    rw [realize_toFormula_subst]
    exact hσ N x ((HornCat.realize_toFormula X x).1 hx)

variable (T) in
/-- The functor from the Horn category of the language to the Horn category of `T`. -/
abbrev quotientFunctor : HornCat.{u} L ⥤ HornTheoryCat.{u} T where
  obj X := ⟨X⟩
  map {X Y} f := Quotient.lift (s := HornCat.homSetoid X Y)
    (fun σ => mor σ.1 (isMor_of_isMor σ.2))
    (fun σ τ h => (mor_eq_mor_iff _ _).2 fun i => GeometricTheory.Entails.of_realize
      fun N _ x hx => h N x ((HornCat.realize_toFormula X x).1 hx) i) f.q
  map_id _ := rfl
  map_comp f g := by
    obtain ⟨σ, hσ, rfl⟩ := HornCat.exists_eq_mor f
    obtain ⟨τ, hτ, rfl⟩ := HornCat.exists_eq_mor g
    rfl

/-- The image of a morphism given by a tuple of terms. -/
theorem quotientFunctor_map_mor {X Y : HornCat.{u} L} (σ : Fin Y.n → L.Term (Fin X.n))
    (hσ : HornCat.IsMor X Y σ) :
    (quotientFunctor T).map (HornCat.mor σ hσ) = mor σ (isMor_of_isMor hσ) :=
  rfl

/-- An equality valid in every structure on a type is entailed. -/
theorem entails_equal_of_realize {n : ℕ} {φ : GeometricFormula.{max u₁ u₂ u} L n}
    {t₁ t₂ : L.Term (Fin n)}
    (h : ∀ (N : Type (max u₁ u₂ u)) [L.Structure N] (x : Fin n → N), t₁.realize x = t₂.realize x) :
    T.Entails φ (.equal t₁ t₂) :=
  GeometricTheory.Entails.of_realize fun N _ x _ => h N x

/-- Adding the atoms of a list to a Horn formula entailed by it gives a morphism of the Horn
category of `T` back from the formula. -/
theorem isMor_addAtoms {X : HornCat.{u} L} {l : List (Atom.{u} L X.n)}
    (h : ∀ a ∈ l, T.Entails X.toFormula a.toFormula) :
    IsMor T X ⟨X.n, X.atoms ++ l⟩ fun i => Term.var i :=
  GeometricTheory.Entails.of_forall_mem (X.toFormula :: l.map Atom.toFormula)
    (by
      simp only [List.mem_cons, List.mem_map, forall_eq_or_imp, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      exact ⟨GeometricTheory.Entails.of_realize fun _ _ _ hx => hx, h⟩)
    fun N _ x hx => by
      simp only [List.mem_cons, List.mem_map, forall_eq_or_imp, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Atom.realize_toFormula, HornCat.realize_toFormula] at hx
      rw [realize_toFormula_subst]
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hx.1 a ha
      · exact hx.2 a ha

/-- The inclusion of a Horn formula with added atoms. -/
def _root_.LeanPool.ClassifyingTopoi.Syntactic.HornCat.addAtomsι (X : HornCat.{u} L)
    (l : List (Atom.{u} L X.n)) : (⟨X.n, X.atoms ++ l⟩ : HornCat.{u} L) ⟶ X :=
  HornCat.mor (fun i => Term.var i) fun _ _ _ hx a ha => hx a (List.mem_append_left _ ha)

/-- Substitution of terms in an atomic formula. -/
def _root_.LeanPool.ClassifyingTopoi.Syntactic.Atom.subst {n m : ℕ}
    (σ : Fin n → L.Term (Fin m)) : Atom.{u} L n → Atom.{u} L m
  | .equal t₁ t₂ => .equal (t₁.subst σ) (t₂.subst σ)
  | .rel R ts => .rel R fun i => (ts i).subst σ

/-- Satisfaction of a substituted atomic formula. -/
@[simp]
theorem _root_.LeanPool.ClassifyingTopoi.Syntactic.Atom.realize_subst {N : Type*}
    [L.Structure N] {n m : ℕ} (σ : Fin n → L.Term (Fin m)) (a : Atom.{u} L n) (x : Fin m → N) :
    (a.subst σ).Realize x ↔ a.Realize fun i => (σ i).realize x := by
  cases a <;> simp [Atom.subst, Atom.Realize, Term.realize_subst]

/-- The morphism back from a Horn formula to the formula with added entailed atoms is a section
of the inclusion. -/
theorem mor_comp_map_addAtomsι {X : HornCat.{u} L} {l : List (Atom.{u} L X.n)}
    (hl : ∀ a ∈ l, T.Entails X.toFormula a.toFormula) :
    mor (X := X) (Y := ⟨X.n, X.atoms ++ l⟩) (fun i => Term.var i) (isMor_addAtoms hl) ≫
      (quotientFunctor T).map (HornCat.addAtomsι X l) = 𝟙 (⟨X⟩ : HornTheoryCat.{u} T) :=
  (mor_eq_mor_iff _ _).2 fun _ => entails_equal_of_realize.{u} fun _ _ _ => rfl

instance : (quotientFunctor.{u} T).IsCoverDense ⊥ where
  is_cover U := GrothendieckTopology.bot_covering.2
    (Sieve.id_mem_iff_eq_top.1 ⟨⟨U.obj, 𝟙 _, 𝟙 _, Category.id_comp _⟩⟩)

instance : (quotientFunctor.{u} T).IsLocallyFull ⊥ where
  functorPushforward_imageSieve_mem {U V} f := by
    obtain ⟨σ, hσ, rfl⟩ : ∃ σ hσ, f = mor (X := U) (Y := V) σ hσ := exists_eq_mor f
    let l := V.atoms.map (Atom.subst σ)
    have hl : ∀ a ∈ l, T.Entails U.toFormula a.toFormula := by
      simp only [l, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro a ha
      exact hσ.trans (GeometricTheory.Entails.of_realize fun _ _ x hx => by
        rw [realize_toFormula_subst] at hx
        simpa using hx a ha)
    have hW : HornCat.IsMor ⟨U.n, U.atoms ++ l⟩ V σ := fun _ _ x hx a ha =>
      (Atom.realize_subst σ a x).1 (hx _ (List.mem_append_right _ (List.mem_map_of_mem ha)))
    have key : (quotientFunctor T).map (HornCat.mor (X := ⟨U.n, U.atoms ++ l⟩) σ hW) =
        (quotientFunctor T).map (HornCat.addAtomsι U l) ≫ mor σ hσ :=
      (mor_eq_mor_iff _ _).2 fun _ => entails_equal_of_realize.{u} fun _ _ _ => by
        dsimp only
        rw [Term.realize_subst]
        rfl
    exact GrothendieckTopology.bot_covering.2 (Sieve.id_mem_iff_eq_top.1
      ⟨_, HornCat.addAtomsι U l, _, ⟨HornCat.mor σ hW, key⟩, (mor_comp_map_addAtomsι hl).symm⟩)

instance : (quotientFunctor.{u} T).IsLocallyFaithful ⊥ where
  functorPushforward_equalizer_mem {U V} f₁ f₂ h := by
    obtain ⟨σ₁, hσ₁, rfl⟩ := HornCat.exists_eq_mor f₁
    obtain ⟨σ₂, hσ₂, rfl⟩ := HornCat.exists_eq_mor f₂
    have h' := (mor_eq_mor_iff _ _).1 h
    have hl : ∀ a ∈ List.ofFn (fun i => Atom.equal (σ₁ i) (σ₂ i)),
        T.Entails U.toFormula a.toFormula := by
      simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
      exact h'
    have heq : HornCat.addEqsι U σ₁ σ₂ ≫ HornCat.mor σ₁ hσ₁ =
        HornCat.addEqsι U σ₁ σ₂ ≫ HornCat.mor σ₂ hσ₂ := by
      refine (HornCat.mor_eq_mor_iff _ _).2 fun N _ x hx i => ?_
      simp only [Term.realize_subst]
      exact ((HornCat.holds_addEqs U σ₁ σ₂ x).1 hx).2 i
    exact GrothendieckTopology.bot_covering.2 (Sieve.id_mem_iff_eq_top.1
      ⟨_, HornCat.addAtomsι U _, _, heq, (mor_comp_map_addAtomsι hl).symm⟩)

end HornTheoryCat

namespace HornCat

open HornTheoryCat

variable {T : GeometricTheory.{max u₁ u₂ u} L}

variable (T) in
/-- The topology on the Horn category induced by the trivial topology on the Horn category of
`T`: a sieve covers when it contains a morphism split by a morphism of the Horn category of
`T`. -/
abbrev theoryTopology : GrothendieckTopology (HornCat.{u} L) :=
  (quotientFunctor.{u} T).inducedTopology ⊥

/-- The covering sieves of the induced topology. -/
theorem mem_theoryTopology_iff {X : HornCat.{u} L} (S : Sieve X) :
    S ∈ theoryTopology.{u} T X ↔ ∃ (W : HornCat.{u} L) (f : W ⟶ X)
      (g : (quotientFunctor T).obj X ⟶ (quotientFunctor T).obj W),
        S f ∧ g ≫ (quotientFunctor T).map f = 𝟙 _ := by
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, GrothendieckTopology.bot_covering,
    ← Sieve.id_mem_iff_eq_top]
  constructor
  · rintro ⟨W, f, g, hf, e⟩
    exact ⟨W, f, g, hf, e.symm⟩
  · rintro ⟨W, f, g, hf, e⟩
    exact ⟨W, f, g, hf, e.symm⟩

/-- The inclusion of a Horn formula with added atoms is a monomorphism. -/
instance (X : HornCat.{u} L) (l : List (Atom.{u} L X.n)) : Mono (addAtomsι X l) :=
  have : addAtomsι X l ≫ ι X = ι ⟨X.n, X.atoms ++ l⟩ := rfl
  mono_of_mono_fac this

section Entailment

variable {D : Type (max u₁ u₂ u)} [SmallCategory D] {K : GrothendieckTopology D}
  (F' : ((HornCat.{u} L)ᵒᵖ ⥤ Type (max u₁ u₂ u)) ⥤ Sheaf K (Type (max u₁ u₂ u)))
  [PreservesFiniteLimits F'] [F'.PreservesEpimorphisms]
  [∀ ι : Type (max u₁ u₂ u), PreservesColimitsOfShape (Discrete ι) F']

/-- If the structure of `yoneda ⋙ F'` is a model of `T`, then `F'` inverts the inclusions of
Horn formulas with added atoms entailed by `T`. -/
theorem isIso_map_yoneda_map_addAtomsι (hM : (hornStructure (yoneda ⋙ F')).IsModel T)
    {X : HornCat.{u} L} {l : List (Atom.{u} L X.n)}
    (hl : ∀ a ∈ l, T.Entails X.toFormula a.toFormula) :
    IsIso (F'.map (yoneda.map (addAtomsι X l))) := by
  let M := hornStructure (yoneda ⋙ F')
  have h := isMor_addAtoms hl _ _ M hM
  have h₂ : M.interp ((HornCat.toFormula ⟨X.n, X.atoms ++ l⟩).subst fun i => Term.var i) =
      M.interp (HornCat.toFormula ⟨X.n, X.atoms ++ l⟩) :=
    CatStructure.interp_eq_of_realize_iff (fun _ _ x => by
      rw [realize_toFormula_subst, realize_toFormula]
      rfl) M
  rw [h₂, interp_toFormula_yoneda_comp, interp_toFormula_yoneda_comp] at h
  have e : (yoneda ⋙ F').map (ι (⟨X.n, X.atoms ++ l⟩ : HornCat.{u} L)) =
      F'.map (yoneda.map (addAtomsι X l)) ≫ (yoneda ⋙ F').map (ι X) := by
    rw [Functor.comp_map, Functor.comp_map, ← F'.map_comp, ← yoneda.map_comp]
    rfl
  have h₃ : Subobject.mk ((yoneda ⋙ F').map (ι (⟨X.n, X.atoms ++ l⟩ : HornCat.{u} L)) ≫
      (isoPow (yoneda ⋙ F') X.n).hom) = Subobject.mk (F'.map (yoneda.map (addAtomsι X l)) ≫
        (yoneda ⋙ F').map (ι X) ≫ (isoPow (yoneda ⋙ F') X.n).hom) :=
    Subobject.mk_eq_mk_of_comm _ _ (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp, e,
      Category.assoc])
  rw [h₃] at h
  exact (Subobject.mk_le_mk_comp_iff _ _).1 h

/-- A morphism of a sieve factors through its inclusion in the representable presheaf. -/
theorem exists_comp_functorInclusion {X W : HornCat.{u} L} {S : Sieve X} {f : W ⟶ X} (hf : S f) :
    ∃ s : yoneda.obj W ⟶ S.functor, s ≫ S.functorInclusion = yoneda.map f := by
  refine ⟨S.toFunctor f hf, ?_⟩
  ext Z g
  rfl

/-- If the structure of `yoneda ⋙ F'` is a model of `T`, then `F'` inverts the inclusions of the
sieves covering for the topology induced by the Horn category of `T`. -/
theorem isIso_map_functorInclusion (hM : (hornStructure (yoneda ⋙ F')).IsModel T)
    {X : HornCat.{u} L} {S : Sieve X} (hS : S ∈ theoryTopology.{u} T X) :
    IsIso (F'.map S.functorInclusion) := by
  obtain ⟨W, f, g, hf, e⟩ := (mem_theoryTopology_iff S).1 hS
  obtain ⟨σ, hσ, rfl⟩ := HornCat.exists_eq_mor f
  obtain ⟨ρ, hρ, rfl⟩ : ∃ ρ hρ, g = HornTheoryCat.mor (X := X) (Y := W) ρ hρ :=
    HornTheoryCat.exists_eq_mor g
  have e' := (HornTheoryCat.mor_eq_mor_iff (HornTheoryCat.isMor_comp hρ (isMor_of_isMor hσ))
    (HornTheoryCat.isMor_id X)).1 e
  let l := W.atoms.map (Atom.subst ρ) ++ List.ofFn fun i => Atom.equal ((σ i).subst ρ) (Term.var i)
  have hl : ∀ a ∈ l, T.Entails X.toFormula a.toFormula := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact hρ.trans (GeometricTheory.Entails.of_realize fun _ _ x hx => by
        rw [realize_toFormula_subst] at hx
        simpa using hx b hb)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact e' i
  have hk : HornCat.IsMor ⟨X.n, X.atoms ++ l⟩ W ρ := fun _ _ x hx b hb =>
    (Atom.realize_subst ρ b x).1 (hx _ (List.mem_append_right _
      (List.mem_append_left _ (List.mem_map_of_mem hb))))
  have hkf : HornCat.mor (X := ⟨X.n, X.atoms ++ l⟩) ρ hk ≫ HornCat.mor σ hσ = addAtomsι X l := by
    refine (HornCat.mor_eq_mor_iff _ _).2 fun N _ x hx i => ?_
    exact hx _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_ofFn.2 ⟨i, rfl⟩)))
  obtain ⟨s, hs⟩ := exists_comp_functorInclusion hf
  have := isIso_map_yoneda_map_addAtomsι F' hM hl
  have hsplit : (inv (F'.map (yoneda.map (addAtomsι X l))) ≫
      F'.map (yoneda.map (HornCat.mor (X := ⟨X.n, X.atoms ++ l⟩) ρ hk)) ≫ F'.map s) ≫
        F'.map S.functorInclusion = 𝟙 _ := by
    rw [Category.assoc, Category.assoc, ← F'.map_comp, hs, ← F'.map_comp, ← yoneda.map_comp, hkf,
      IsIso.inv_hom_id]
  have : IsSplitEpi (F'.map S.functorInclusion) := ⟨⟨_, hsplit⟩⟩
  exact isIso_of_mono_of_isSplitEpi _

end Entailment

/-- The sheafification for the trivial topology is the inclusion of presheaves as sheaves. -/
noncomputable def presheafToSheafBotIso :
    presheafToSheaf (⊥ : GrothendieckTopology (HornCat.{u} L)) (Type (max u₁ u₂ u)) ≅
      (sheafBotEquivalence (Type (max u₁ u₂ u))).inverse :=
  (sheafificationAdjunction _ _).leftAdjointUniq (sheafBotEquivalence _).symm.toAdjunction

/-- The topology induced by the Horn category of `T` is coarser than the topology classifying
`T` as a quotient of the empty theory. -/
theorem theoryTopology_le_quotientTopology :
    theoryTopology.{u} T ≤ quotientTopology (genericSheaf.{u} L) T := by
  have hle := le_quotientTopology (genericSheaf.{u} L) T
  let G := sheafToPresheaf (⊥ : GrothendieckTopology (HornCat.{u} L)) (Type (max u₁ u₂ u)) ⋙
    presheafToSheaf (quotientTopology (genericSheaf.{u} L) T) (Type (max u₁ u₂ u))
  have : G.IsLeftAdjoint := isLeftAdjoint_sheafify hle
  let F' := presheafToSheaf (⊥ : GrothendieckTopology (HornCat.{u} L)) (Type (max u₁ u₂ u)) ⋙ G
  have hM : (hornStructure (yoneda ⋙ F')).IsModel T := by
    suffices h0 : ((genericPsh.{u} L).map F').IsModel T from fun σ hσ => by
      rw [interp_hornStructure_yoneda_comp, interp_hornStructure_yoneda_comp]
      exact h0 σ hσ
    refine ((genericPsh.{u} L).isomorphic_map_comp _ G).symm.isModel ?_
    refine (((genericPsh.{u} L).isomorphic_map_of_iso presheafToSheafBotIso).map G).symm.isModel ?_
    exact (isClassifyingSite_genericModel.{u} L T).isModel
  have key := (isSheaf_rightAdjoint_iff bot_le G).2 fun X S hS =>
    isIso_map_functorInclusion F' hM hS
  refine (ToposTheoreticBridges.le_iff_forall_isSheaf hle).2 fun P hP => ?_
  let Y : Sheaf (quotientTopology (genericSheaf.{u} L) T) (Type (max u₁ u₂ u)) := ⟨P.obj, hP⟩
  have i := ((Adjunction.ofIsLeftAdjoint G).rightAdjointUniq (sheafifyAdjunction hle)).app Y
  exact (Presheaf.isSheaf_of_iso_iff ((sheafToPresheaf _ _).mapIso i)).1 (key Y)

/-- The atoms of a geometric formula, as a list: for a Horn formula, the formula is their
conjunction. -/
def _root_.LeanPool.ClassifyingTopoi.GeometricFormula.hornAtoms :
    {n : ℕ} → GeometricFormula.{max u₁ u₂ u} L n → List (Atom.{u} L n)
  | _, .top => []
  | _, .and φ ψ => φ.hornAtoms ++ ψ.hornAtoms
  | _, .iSup _ => []
  | _, .equal t₁ t₂ => [.equal t₁ t₂]
  | _, .rel R ts => [.rel R ts]
  | _, .ex _ => []

/-- A Horn formula holds exactly where its atoms hold. -/
theorem _root_.LeanPool.ClassifyingTopoi.GeometricFormula.realize_iff_hornAtoms {N : Type*}
    [L.Structure N] {n : ℕ} {φ : GeometricFormula.{max u₁ u₂ u} L n} (hφ : φ.IsHorn)
    (x : Fin n → N) : φ.Realize x ↔ ∀ a ∈ φ.hornAtoms.{u}, a.Realize x := by
  induction φ with
  | top => simp [GeometricFormula.Realize, GeometricFormula.hornAtoms]
  | and φ ψ ihφ ihψ =>
    simp only [GeometricFormula.hornAtoms, List.mem_append]
    rw [show (GeometricFormula.and φ ψ).Realize x ↔ φ.Realize x ∧ ψ.Realize x from Iff.rfl,
      ihφ hφ.1, ihψ hφ.2]
    exact ⟨fun h a ha => ha.elim (h.1 a) (h.2 a), fun h => ⟨fun a ha => h a (.inl ha),
      fun a ha => h a (.inr ha)⟩⟩
  | iSup φ => exact hφ.elim
  | equal t₁ t₂ => simp [GeometricFormula.Realize, GeometricFormula.hornAtoms, Atom.Realize]
  | rel R ts => simp [GeometricFormula.Realize, GeometricFormula.hornAtoms, Atom.Realize]
  | ex φ => exact hφ.elim

/-- Sheafification for the induced topology inverts the inclusion of a Horn formula with added
atoms entailed by `T`. -/
theorem isIso_presheafToSheaf_map_yoneda_map_addAtomsι {X : HornCat.{u} L}
    {l : List (Atom.{u} L X.n)} (hl : ∀ a ∈ l, T.Entails X.toFormula a.toFormula) :
    IsIso ((presheafToSheaf (theoryTopology.{u} T) (Type (max u₁ u₂ u))).map
      (yoneda.map (addAtomsι X l))) := by
  let S := Sieve.generate (Presieve.singleton (addAtomsι X l))
  have hS : S ∈ theoryTopology.{u} T X := (mem_theoryTopology_iff S).2
    ⟨_, addAtomsι X l, _, Sieve.le_generate _ _ _ (Presieve.singleton_self _),
      mor_comp_map_addAtomsι hl⟩
  rw [← GrothendieckTopology.W_iff]
  have : Presheaf.IsLocallyInjective (theoryTopology.{u} T) (yoneda.map (addAtomsι X l)) :=
    Presheaf.isLocallyInjective_of_injective _ _ fun Z g g' h => by
      simpa using (cancel_mono (addAtomsι X l)).1 (by simpa using h)
  have : Presheaf.IsLocallySurjective (theoryTopology.{u} T) (yoneda.map (addAtomsι X l)) :=
    ⟨fun {U} g => (theoryTopology.{u} T).superset_covering (fun Z h hh => by
      obtain ⟨W, a, b, ⟨⟩, e⟩ := hh
      exact ⟨a, by simpa using e⟩) ((theoryTopology.{u} T).pullback_stable g hS)⟩
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

/-- For a Horn theory, the topology classifying `T` as a quotient of the empty theory is coarser
than the topology induced by the Horn category of `T`. -/
theorem quotientTopology_le_theoryTopology (hT : T.IsHorn) :
    quotientTopology (genericSheaf.{u} L) T ≤ theoryTopology.{u} T := by
  rw [quotientTopology_le_iff _ _ bot_le]
  intro σ hσ
  have : (sheafToPresheaf (⊥ : GrothendieckTopology (HornCat.{u} L)) (Type (max u₁ u₂ u)) ⋙
      presheafToSheaf (theoryTopology.{u} T) (Type (max u₁ u₂ u))).IsLeftAdjoint :=
    isLeftAdjoint_sheafify bot_le
  rw [← CatStructure.interp_map_le_iff_isIso]
  change (genericModel (theoryTopology.{u} T)).interp σ.lhs ≤
    (genericModel (theoryTopology.{u} T)).interp σ.rhs
  obtain ⟨n, φ, ψ⟩ := σ
  obtain ⟨hφ, hψ⟩ := hT _ hσ
  let X : HornCat.{u} L := ⟨n, φ.hornAtoms⟩
  let l := ψ.hornAtoms.{u}
  have hX : ∀ (N : Type (max u₁ u₂ u)) [L.Structure N] (x : Fin n → N),
      φ.Realize x ↔ (X.toFormula : GeometricFormula.{max u₁ u₂ u} L n).Realize x := fun N _ x => by
    rw [HornCat.realize_toFormula, GeometricFormula.realize_iff_hornAtoms.{u} hφ]
    rfl
  have hl : ∀ a ∈ l, T.Entails X.toFormula a.toFormula := fun a ha =>
    (GeometricTheory.Entails.of_realize fun N _ x hx => (hX N x).2 hx).trans
      ((GeometricTheory.Entails.of_mem hσ).trans (GeometricTheory.Entails.of_realize
        fun N _ x hx => by
          rw [Atom.realize_toFormula]
          exact (GeometricFormula.realize_iff_hornAtoms.{u} hψ x).1 hx a ha))
  have := isIso_presheafToSheaf_map_yoneda_map_addAtomsι (T := T) (X := X) (l := l) hl
  let a := presheafToSheaf (theoryTopology.{u} T) (Type (max u₁ u₂ u))
  have hle : (genericModel (theoryTopology.{u} T)).interp X.toFormula ≤
      (genericModel (theoryTopology.{u} T)).interp (HornCat.toFormula ⟨X.n, X.atoms ++ l⟩) := by
    rw [interp_toFormula_genericModel, interp_toFormula_genericModel]
    refine Subobject.mk_le_mk_of_comm (inv (a.map (yoneda.map (addAtomsι X l)))) ?_
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← a.map_comp, ← Category.assoc, ← yoneda.map_comp]
    rfl
  calc (genericModel (theoryTopology.{u} T)).interp φ
      = (genericModel (theoryTopology.{u} T)).interp X.toFormula :=
        CatStructure.interp_eq_of_realize_iff hX _
    _ ≤ _ := hle
    _ ≤ (genericModel (theoryTopology.{u} T)).interp ψ :=
        CatStructure.interp_le_of_realize _ fun N _ x hx => by
          rw [HornCat.realize_toFormula] at hx
          refine (GeometricFormula.realize_iff_hornAtoms.{u} hψ x).2 fun a ha => hx a ?_
          exact List.mem_append_right _ ha

/-- For a Horn theory, the topology induced by the Horn category of `T` is the topology
classifying `T`. -/
theorem theoryTopology_eq (hT : T.IsHorn) :
    theoryTopology.{u} T = quotientTopology (genericSheaf.{u} L) T :=
  le_antisymm theoryTopology_le_quotientTopology (quotientTopology_le_theoryTopology hT)

/-- For a Horn theory, the Horn category with the topology induced by the Horn category of `T`
classifies `T`. -/
theorem isClassifyingSite_theoryTopology (hT : T.IsHorn) :
    IsClassifyingSite T (theoryTopology.{u} T : GrothendieckTopology (HornCat.{u} L))
      (genericModel (theoryTopology.{u} T)) := by
  rw [theoryTopology_eq hT]
  exact isClassifyingSite_genericModel.{u} L T

end HornCat

/-- **Horn theories are of presheaf type**: the presheaf topos on the Horn category of a Horn
theory `T` classifies `T`. -/
theorem HornTheoryCat.isClassifyingSite {T : GeometricTheory.{max u₁ u₂ u} L} (hT : T.IsHorn) :
    ∃ U : CatStructure L (Sheaf (⊥ : GrothendieckTopology (HornTheoryCat.{u} T))
      (Type (max u₁ u₂ u))), IsClassifyingSite T ⊥ U :=
  ⟨_, (HornCat.isClassifyingSite_theoryTopology.{u} hT).of_equivalence
    (Functor.IsDenseSubsite.sheafEquiv (HornCat.theoryTopology.{u} T) ⊥
      (HornTheoryCat.quotientFunctor.{u} T) (Type (max u₁ u₂ u))) (CatStructure.Isomorphic.refl _)⟩



end Syntactic

/-- **3.1.** A geometric theory is of presheaf type when it is classified by a small category
with the trivial topology, that is by a presheaf topos. -/
def IsOfPresheafType (T : GeometricTheory.{u} L) : Prop :=
  ∃ (C : Type u) (_ : SmallCategory C)
    (U : CatStructure L (Sheaf (⊥ : GrothendieckTopology C) (Type u))), IsClassifyingSite T ⊥ U

/-- **3.1.** Horn theories are of presheaf type, with a site in the universe of the language
and of the theory's disjunctions. -/
theorem isOfPresheafType_of_isHorn (T : GeometricTheory.{max u₁ u₂ u} L) (hT : T.IsHorn) :
    IsOfPresheafType T :=
  let ⟨U, hU⟩ := Syntactic.HornTheoryCat.isClassifyingSite.{u} hT
  ⟨_, inferInstance, U, hU⟩

end LeanPool.ClassifyingTopoi
