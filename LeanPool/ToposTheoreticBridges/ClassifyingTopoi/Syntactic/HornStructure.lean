/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Horn
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Homomorphisms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Structures from functors out of the Horn category

In the Horn category, the context `⊤` in `n` variables is the `n`-th power of the context `⊤`
in one variable (`HornCat.isLimitFanTop`). Hence a functor `A : HornCat L ⥤ E` preserving these
powers defines an `L`-structure `A.hornStructure` in `E`: its carrier is `A (⊤₁)`, a function
symbol `f` of arity `k` is interpreted by `A` of the tuple `f(x₀, …, x_{k-1}) : ⊤ₖ ⟶ ⊤₁`, and a
relation symbol `R` by `A` of the inclusion `{x. R(x)} ⟶ ⊤ₖ`.

## Main results

* `LeanPool.ClassifyingTopoi.Syntactic.HornCat.termMap_hornStructure`: a term `t` is interpreted
  by `A` of the tuple `t : ⊤ₙ ⟶ ⊤₁`;
* `LeanPool.ClassifyingTopoi.Syntactic.HornCat.isomorphic_comp_hornStructure`: the structure of
  `A ⋙ F` is the image under `F` of the structure of `A`;
* `LeanPool.ClassifyingTopoi.Syntactic.HornCat.isomorphic_hornStructure_of_iso`: isomorphic
  functors give isomorphic structures.
-/

@[expose] public section

universe u u₁ u₂ v v'

namespace LeanPool.ClassifyingTopoi.Syntactic

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits LeanPool.ClassifyingTopoi

variable {L : Language.{u₁, u₂}}

namespace HornCat

/-- Every tuple of terms is a morphism into a context `⊤`. -/
theorem isMor_top (X : HornCat.{u} L) {k : ℕ} (σ : Fin k → L.Term (Fin X.n)) :
    IsMor X (top k) σ :=
  fun _ _ _ _ => holds_top _

/-- The morphism into the context `⊤` given by a tuple of terms. -/
def toTop (X : HornCat.{u} L) {k : ℕ} (σ : Fin k → L.Term (Fin X.n)) : X ⟶ top k :=
  mor σ (isMor_top X σ)

/-- The term of a morphism into the context `⊤` in one variable. -/
noncomputable def term {X : HornCat.{u} L} (f : X ⟶ top 1) : L.Term (Fin X.n) :=
  (exists_eq_mor f).choose 0

/-- A morphism into the context `⊤` in one variable is given by its term. -/
theorem eq_toTop_term {X : HornCat.{u} L} (f : X ⟶ top 1) : f = toTop X fun _ => term f := by
  refine (exists_eq_mor f).choose_spec.choose_spec.trans ?_
  change mor _ _ = mor (fun _ => (exists_eq_mor f).choose 0) _
  congr 1
  funext i
  rw [Subsingleton.elim i 0]

/-- Two morphisms into a context `⊤` are equal iff their terms agree on the assignments
satisfying the source. -/
theorem toTop_eq_toTop_iff {X : HornCat.{u} L} {k : ℕ} {σ τ : Fin k → L.Term (Fin X.n)} :
    toTop X σ = toTop X τ ↔ ∀ (M : Type (max u₁ u₂ u)) [L.Structure M]
      (x : Fin X.n → M), X.Holds x → ∀ i, (σ i).realize x = (τ i).realize x :=
  mor_eq_mor_iff _ _

/-- Composition with a morphism into a context `⊤`. -/
theorem mor_comp_toTop {X Y : HornCat.{u} L} (σ : Fin Y.n → L.Term (Fin X.n)) (hσ : IsMor X Y σ)
    {k : ℕ} (τ : Fin k → L.Term (Fin Y.n)) :
    mor σ hσ ≫ toTop Y τ = toTop X fun i => (τ i).subst σ :=
  rfl

/-- The `i`-th projection `⊤ₙ ⟶ ⊤₁`. -/
def proj (n : ℕ) (i : Fin n) : top.{u} (L := L) n ⟶ top 1 :=
  toTop _ fun _ => Term.var i

/-- The context `⊤ₙ` as a fan over `n` copies of `⊤₁`. -/
def fanTop (n : ℕ) : Fan fun _ : Fin n => top.{u} (L := L) 1 :=
  Fan.mk (top n) (proj n)

/-- The context `⊤ₙ` is the `n`-th power of `⊤₁`. -/
noncomputable def isLimitFanTop (n : ℕ) : IsLimit (fanTop.{u} (L := L) n) :=
  Fan.IsLimit.mk _ (fun s => toTop s.pt fun i => term (s.proj i))
    (fun s j => by
      conv_rhs => rw [eq_toTop_term (s.proj j)]
      rfl)
    (fun s m hm => by
      obtain ⟨ρ, hρ, rfl⟩ := exists_eq_mor m
      refine (mor_eq_mor_iff _ _).2 fun M _ x hx i => ?_
      have h := hm i
      rw [eq_toTop_term (s.proj i)] at h
      exact (toTop_eq_toTop_iff.1 h) M x hx 0)

/-- The tuple `f(x₀, …, x_{k-1}) : ⊤ₖ ⟶ ⊤₁` of a function symbol. -/
def funMor {k : ℕ} (f : L.Functions k) : top.{u} (L := L) k ⟶ top 1 :=
  toTop _ fun _ => Term.func f fun i => Term.var i

/-- The Horn formula `R(x₀, …, x_{k-1})` of a relation symbol. -/
abbrev relObj {k : ℕ} (R : L.Relations k) : HornCat.{u} L :=
  ⟨k, [Atom.rel R fun i => Term.var i]⟩

/-- The inclusion of a Horn formula in the context `⊤` with the same variables. -/
def ι (X : HornCat.{u} L) : X ⟶ top X.n :=
  toTop X fun i => Term.var i

/-- The inclusion of a Horn formula in the context `⊤` is a monomorphism. -/
instance (X : HornCat.{u} L) : Mono (ι X) where
  right_cancellation {Z} g g' h := by
    obtain ⟨ρ, hρ, rfl⟩ := exists_eq_mor g
    obtain ⟨ρ', hρ', rfl⟩ := exists_eq_mor g'
    exact (mor_eq_mor_iff _ _).2 (toTop_eq_toTop_iff.1 h)

section Structure

variable {E : Type v} [Category.{v'} E] [HasFiniteProducts E] (A : HornCat.{u} L ⥤ E)
  [∀ n : ℕ, PreservesLimit (Discrete.functor fun _ : Fin n => top.{u} (L := L) 1) A]

/-- The image of `⊤ₙ` under a functor preserving powers is the `n`-th power of the image
of `⊤₁`. -/
noncomputable def isoPow (n : ℕ) : A.obj (top n) ≅ ∏ᶜ fun _ : Fin n => A.obj (top 1) :=
  IsLimit.conePointUniqueUpToIso (isLimitFanMkObjOfIsLimit A _ _ (isLimitFanTop n))
    (productIsProduct _)

/-- The components of `isoPow` are the images of the projections. -/
@[reassoc (attr := simp)]
theorem isoPow_hom_π (n : ℕ) (i : Fin n) :
    (isoPow A n).hom ≫ Pi.π _ i = A.map (proj n i) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i)

/-- The projections of a power, through `isoPow`. -/
@[reassoc]
theorem isoPow_inv_map_proj (n : ℕ) (i : Fin n) :
    (isoPow A n).inv ≫ A.map (proj n i) = Pi.π _ i := by
  rw [← isoPow_hom_π, Iso.inv_hom_id_assoc]

/-- A tuple of terms, through the power isomorphisms. -/
theorem piLift_isoPow_inv_map {n k : ℕ} (σ : Fin k → L.Term (Fin n)) :
    (Pi.lift fun j => (isoPow A n).inv ≫ A.map (toTop (top n) fun _ => σ j)) =
      (isoPow A n).inv ≫ A.map (toTop (top n) σ) ≫ (isoPow A k).hom := by
  ext j
  rw [limit.lift_π, Category.assoc, Category.assoc, isoPow_hom_π, ← A.map_comp]
  rfl

/-- The structure defined by a functor out of the Horn category preserving powers. -/
noncomputable abbrev hornStructure : CatStructure L E where
  carrier := A.obj (top 1)
  funMap f := (isoPow A _).inv ≫ A.map (funMor f)
  relMap R := Over.mk (A.map (ι (relObj R)) ≫ (isoPow A _).hom)

/-- The carrier of the structure of a functor. -/
@[simp]
theorem hornStructure_carrier : (hornStructure A).carrier = A.obj (top 1) :=
  rfl

/-- Terms are interpreted in the structure of `A` by `A` of the corresponding tuples. -/
theorem termMap_hornStructure {n : ℕ} (t : L.Term (Fin n)) :
    (hornStructure A).termMap t = (isoPow A n).inv ≫ A.map (toTop _ fun _ => t) := by
  induction t with
  | var i => exact (isoPow_inv_map_proj A n i).symm
  | @func k f ts ih =>
    change Pi.lift (fun j => (hornStructure A).termMap (ts j)) ≫ (isoPow A k).inv ≫
      A.map (funMor f) = _
    simp only [ih]
    have h : (toTop (top n) fun _ => Term.func f ts) = toTop (top n) ts ≫ funMor f := rfl
    rw [piLift_isoPow_inv_map, h, A.map_comp]
    simp

/-- The interpretation of a tuple of terms in the structure of `A`. -/
theorem piLift_termMap_hornStructure {n k : ℕ} (σ : Fin k → L.Term (Fin n)) :
    Pi.lift (fun i => (hornStructure A).termMap (σ i)) =
      (isoPow A n).inv ≫ A.map (toTop _ σ) ≫ (isoPow A k).hom := by
  simp only [termMap_hornStructure]
  exact piLift_isoPow_inv_map A σ

variable {E' : Type*} [Category E'] [HasFiniteProducts E'] (F : E ⥤ E')
  [PreservesFiniteProducts F]

instance (n : ℕ) : PreservesLimit (Discrete.functor fun _ : Fin n => top.{u} (L := L) 1)
    (A ⋙ F) :=
  inferInstance

/-- The power isomorphism of a composite functor. -/
theorem isoPow_comp_hom (n : ℕ) :
    (isoPow (A ⋙ F) n).hom =
      F.map (isoPow A n).hom ≫ piComparison F fun _ : Fin n => A.obj (top 1) := by
  ext i
  rw [isoPow_hom_π, Category.assoc]
  erw [piComparison_comp_π]
  rw [← F.map_comp, isoPow_hom_π]
  rfl

/-- The inverse of the power isomorphism of a composite functor. -/
theorem isoPow_comp_inv (n : ℕ) :
    (isoPow (A ⋙ F) n).inv =
      inv (piComparison F fun _ : Fin n => A.obj (top 1)) ≫ F.map (isoPow A n).inv := by
  rw [← cancel_epi (isoPow (A ⋙ F) n).hom, Iso.hom_inv_id, isoPow_comp_hom]
  simp [← F.map_comp]

/-- The identity is a homomorphism from the structure of `A ⋙ F` to the image under `F` of the
structure of `A`. -/
theorem isHom_comp_hornStructure [HasFiniteLimits E'] [HasImages E'] :
    (hornStructure (A ⋙ F)).IsHom ((hornStructure A).map F) (𝟙 _) := by
  refine ⟨fun f => ?_, fun R => ?_⟩
  · change ((isoPow (A ⋙ F) _).inv ≫ F.map (A.map (funMor f))) ≫ 𝟙 _ =
      _ ≫ inv (piComparison F _) ≫ F.map ((isoPow A _).inv ≫ A.map (funMor f))
    rw [isoPow_comp_inv]
    simp
  · refine imageSubobject_le_pullback _ _ _ (𝟙 _) ?_
    change (F.map (A.map (ι (relObj R))) ≫ (isoPow (A ⋙ F) _).hom) ≫ _ =
      𝟙 _ ≫ F.map (A.map (ι (relObj R)) ≫ (isoPow A _).hom) ≫ piComparison F _
    rw [isoPow_comp_hom]
    simp

/-- The identity is a homomorphism from the image under `F` of the structure of `A` to the
structure of `A ⋙ F`. -/
theorem isHom_comp_hornStructure' [HasFiniteLimits E'] [HasImages E'] :
    ((hornStructure A).map F).IsHom (hornStructure (A ⋙ F)) (𝟙 _) := by
  refine ⟨fun f => ?_, fun R => ?_⟩
  · change (inv (piComparison F _) ≫ F.map ((isoPow A _).inv ≫ A.map (funMor f))) ≫ 𝟙 _ =
      _ ≫ (isoPow (A ⋙ F) _).inv ≫ F.map (A.map (funMor f))
    rw [isoPow_comp_inv]
    simp
  · refine imageSubobject_le_pullback _ _ _ (𝟙 _) ?_
    change (F.map (A.map (ι (relObj R)) ≫ (isoPow A _).hom) ≫ piComparison F _) ≫ _ =
      𝟙 _ ≫ F.map (A.map (ι (relObj R))) ≫ (isoPow (A ⋙ F) _).hom
    rw [isoPow_comp_hom]
    simp

/-- The structure of `A ⋙ F` is isomorphic, by the identity, to the image under `F` of the
structure of `A`. -/
theorem isomorphic_comp_hornStructure [HasFiniteLimits E'] [HasImages E'] :
    (hornStructure (A ⋙ F)).Isomorphic ((hornStructure A).map F) :=
  ⟨Iso.refl _, isHom_comp_hornStructure A F, isHom_comp_hornStructure' A F⟩

variable {A} {B : HornCat.{u} L ⥤ E}
  [∀ n : ℕ, PreservesLimit (Discrete.functor fun _ : Fin n => top.{u} (L := L) 1) B]

/-- The power isomorphisms are natural in the functor. -/
@[reassoc]
theorem isoPow_hom_naturality (α : A ⟶ B) (n : ℕ) :
    α.app (top n) ≫ (isoPow B n).hom =
      (isoPow A n).hom ≫ Limits.Pi.map fun _ => α.app (top 1) := by
  ext i
  simp

/-- A natural transformation induces a homomorphism between the structures of functors. -/
theorem isHom_hornStructure_app [HasFiniteLimits E] [HasImages E] (α : A ⟶ B) :
    (hornStructure A).IsHom (hornStructure B) (α.app (top 1)) where
  funMap f := by
    change ((isoPow A _).inv ≫ A.map (funMor f)) ≫ α.app _ =
      _ ≫ (isoPow B _).inv ≫ B.map (funMor f)
    rw [Category.assoc, α.naturality, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [Iso.inv_comp_eq, ← isoPow_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  relMap R := by
    refine imageSubobject_le_pullback _ _ _ (α.app (relObj R)) ?_
    change (A.map (ι (relObj R)) ≫ (isoPow A _).hom) ≫ _ =
      α.app _ ≫ B.map (ι (relObj R)) ≫ (isoPow B _).hom
    rw [Category.assoc, ← isoPow_hom_naturality, ← Category.assoc, ← Category.assoc,
      α.naturality]

/-- Isomorphic functors give isomorphic structures. -/
theorem isomorphic_hornStructure_of_iso [HasFiniteLimits E] [HasImages E] (e : A ≅ B) :
    (hornStructure A).Isomorphic (hornStructure B) :=
  ⟨e.app (top 1), isHom_hornStructure_app e.hom, isHom_hornStructure_app e.inv⟩

end Structure

end HornCat

end LeanPool.ClassifyingTopoi.Syntactic
