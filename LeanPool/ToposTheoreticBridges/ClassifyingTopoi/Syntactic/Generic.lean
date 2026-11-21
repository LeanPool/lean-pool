/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.HornStructure
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Presheaf

/-!
# The generic structure on the Horn category

The Yoneda embedding of the Horn category preserves powers, hence defines a structure
`HornCat.genericPsh L` in the presheaf topos on `HornCat L`. At an object `c`, its fiber structure
is the *term model* of `c`: its elements are the morphisms `c ⟶ ⊤₁`, that is the terms in the
context of `c` up to agreement on the assignments satisfying `c`, and an atomic formula holds at a
tuple of terms iff it holds after substitution at every assignment satisfying `c`
(`HornCat.genericPsh_realize_atom`). Hence the interpretation of a Horn formula `X` in the
generic structure is the representable subobject `y X ⟶ y ⊤ₙ`
(`HornCat.interp_toFormula_genericPsh`).
-/

@[expose] public section

universe u w u₁ u₂

namespace LeanPool.ClassifyingTopoi.Syntactic

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits LeanPool.ClassifyingTopoi
  Opposite

variable {L : Language.{u₁, u₂}}

namespace HornCat

section Pow

/-- The tuple of a section of `A (⊤ₙ)`, through the power isomorphism. -/
theorem secEquiv_isoPow_hom {D : Type*} [Category D] (A : HornCat.{u} L ⥤ (D ⥤ Type w))
    [∀ n : ℕ, PreservesLimit (Discrete.functor fun _ : Fin n => top.{u} (L := L) 1) A]
    {n : ℕ} (d : D) (z : (A.obj (top n)).obj d) :
    secEquiv _ n d ((isoPow A n).hom.app d z) = fun i => (A.map (proj n i)).app d z := by
  funext i
  rw [secEquiv_apply, ← NatTrans.comp_app_apply, isoPow_hom_π]

end Pow

variable (L) in
/-- The generic structure on the Horn category, in its presheaf topos: the structure of the
Yoneda embedding. -/
noncomputable abbrev genericPsh :
    CatStructure L ((HornCat.{u} L)ᵒᵖ ⥤ Type (max u₁ u₂ u)) :=
  hornStructure (yoneda : HornCat.{u} L ⥤ _)

/-- The class of a term in the context of `c`, an element of the term model of `c`. -/
def cls (c : HornCat.{u} L) (t : L.Term (Fin c.n)) : c ⟶ top 1 :=
  toTop c fun _ => t

/-- Every element of the term model is the class of a term. -/
theorem exists_eq_cls {c : HornCat.{u} L} (g : c ⟶ top 1) : ∃ t, g = cls c t :=
  ⟨term g, eq_toTop_term g⟩

/-- Equality in the term model. -/
theorem cls_eq_cls_iff {c : HornCat.{u} L} {t t' : L.Term (Fin c.n)} :
    cls c t = cls c t' ↔ ∀ (M : Type (max u₁ u₂ u)) [L.Structure M]
      (x : Fin c.n → M), c.Holds x → t.realize x = t'.realize x := by
  rw [cls, cls, toTop_eq_toTop_iff]
  exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => ⟨fun h => h 0, fun h _ => h⟩

/-- The section of `y ⊤ₙ` at `c` whose tuple is a tuple of classes. -/
theorem secEquiv_symm_cls (c : HornCat.{u} L) {n : ℕ} (σ : Fin n → L.Term (Fin c.n)) :
    (secEquiv (genericPsh L).carrier n (op c)).symm (fun i => cls c (σ i)) =
      (isoPow (yoneda : HornCat.{u} L ⥤ _) n).hom.app (op c) (toTop c σ) := by
  rw [Equiv.symm_apply_eq, secEquiv_isoPow_hom]
  rfl

/-- Function symbols in the term model. -/
theorem genericPsh_funMap (c : HornCat.{u} L) {k : ℕ} (f : L.Functions k)
    (σ : Fin k → L.Term (Fin c.n)) :
    ((genericPsh L).fiberStr (op c)).funMap f (fun i => cls c (σ i)) =
      cls c (Term.func f σ) := by
  refine (CatStructure.fiberStr_funMap (genericPsh L) (op c) f _).trans ?_
  rw [secEquiv_symm_cls, NatTrans.comp_app, types_comp_apply,
    ← types_comp_apply ((isoPow (yoneda : HornCat.{u} L ⥤ _) k).hom.app (op c)),
    ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app, types_id_apply]
  rfl

/-- Terms in the term model are realized by substitution. -/
theorem genericPsh_realize_term (c : HornCat.{u} L) {n : ℕ} (σ : Fin n → L.Term (Fin c.n))
    (t : L.Term (Fin n)) :
    @Term.realize L _ ((genericPsh L).fiberStr (op c)) _ (fun i => cls c (σ i)) t =
      cls c (t.subst σ) := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    change ((genericPsh L).fiberStr (op c)).funMap f (fun i => @Term.realize L _
      ((genericPsh L).fiberStr (op c)) _ (fun i => cls c (σ i)) (ts i)) = _
    simp only [ih]
    exact genericPsh_funMap c f _

/-- Relation symbols in the term model. -/
theorem genericPsh_relMap (c : HornCat.{u} L) {k : ℕ} (R : L.Relations k)
    (σ : Fin k → L.Term (Fin c.n)) :
    ((genericPsh L).fiberStr (op c)).RelMap R (fun i => cls c (σ i)) ↔
      ∀ (M : Type (max u₁ u₂ u)) [L.Structure M] (x : Fin c.n → M), c.Holds x →
        Structure.RelMap R fun i => (σ i).realize x := by
  refine (CatStructure.fiberStr_relMap (genericPsh L) (op c) R _).trans ?_
  rw [secEquiv_symm_cls]
  have inj : Function.Injective ((isoPow (yoneda : HornCat.{u} L ⥤ _) k).hom.app (op c)) :=
    fun a b h => by
      simpa using congrArg ((isoPow (yoneda : HornCat.{u} L ⥤ _) k).inv.app (op c)) h
  constructor
  · rintro ⟨g, hg⟩ M _ x hx
    obtain ⟨ρ, hρ, rfl⟩ := exists_eq_mor g
    have h₁ : mor ρ hρ ≫ ι (relObj R) = toTop c σ := inj hg
    have h₂ := toTop_eq_toTop_iff.1 h₁ M x hx
    have := hρ M x hx _ (List.mem_singleton_self _)
    simp only [Atom.Realize, Term.realize_var] at this
    convert this using 2
    exact (h₂ _).symm
  · intro h
    refine ⟨mor σ fun M _ x hx a ha => ?_, rfl⟩
    rw [List.mem_singleton] at ha
    subst ha
    exact h M x hx

/-- Atomic formulas in the term model: an atom holds at a tuple of terms iff it holds after
substitution at every assignment satisfying the context. -/
theorem genericPsh_realize_atom (c : HornCat.{u} L) {n : ℕ} (σ : Fin n → L.Term (Fin c.n))
    (a : Atom.{u} L n) :
    @Atom.Realize L _ ((genericPsh L).fiberStr (op c)) n a (fun i => cls c (σ i)) ↔
      ∀ (M : Type (max u₁ u₂ u)) [L.Structure M] (x : Fin c.n → M), c.Holds x →
        a.Realize fun i => (σ i).realize x := by
  cases a with
  | equal t₁ t₂ =>
    change @Term.realize L _ ((genericPsh L).fiberStr (op c)) _ (fun i => cls c (σ i)) t₁ =
      @Term.realize L _ ((genericPsh L).fiberStr (op c)) _ (fun i => cls c (σ i)) t₂ ↔ _
    rw [genericPsh_realize_term, genericPsh_realize_term, cls_eq_cls_iff]
    simp only [Term.realize_subst]
    rfl
  | rel R ts =>
    change ((genericPsh L).fiberStr (op c)).RelMap R (fun i => @Term.realize L _
      ((genericPsh L).fiberStr (op c)) _ (fun i => cls c (σ i)) (ts i)) ↔ _
    have e : (fun i => @Term.realize L _ ((genericPsh L).fiberStr (op c)) _
        (fun i => cls c (σ i)) (ts i)) = fun i => cls c ((ts i).subst σ) :=
      funext fun i => genericPsh_realize_term c σ (ts i)
    refine (Iff.of_eq (congrArg _ e)).trans ((genericPsh_relMap c R _).trans ?_)
    simp only [Term.realize_subst]
    rfl

/-- Horn formulas in the term model: a Horn formula holds at a tuple of terms iff the tuple is
a morphism. -/
theorem genericPsh_holds (c : HornCat.{u} L) (X : HornCat.{u} L)
    (σ : Fin X.n → L.Term (Fin c.n)) :
    @Holds L X _ ((genericPsh L).fiberStr (op c)) (fun i => cls c (σ i)) ↔ IsMor c X σ := by
  constructor
  · intro h M _ x hx a ha
    exact (genericPsh_realize_atom c σ a).1 (h a ha) M x hx
  · intro h a ha
    exact (genericPsh_realize_atom c σ a).2 fun M _ x hx => h M x hx a ha

/-- The interpretation of a Horn formula in the generic structure is the representable
subobject `y X ⟶ y ⊤ₙ`. -/
theorem interp_toFormula_genericPsh (X : HornCat.{u} L) :
    (genericPsh L).interp X.toFormula =
      Subobject.mk (yoneda.map (ι X) ≫ (isoPow (yoneda : HornCat.{u} L ⥤ _) X.n).hom) := by
  refine le_antisymm ?_ ?_ <;> rw [le_iff_range_app_subset] <;> intro c <;>
    induction c using Opposite.rec with | op c => ?_
  · rw [range_app_mk]
    rintro z hz
    rw [mem_range_interp_app_iff, realize_toFormula] at hz
    obtain ⟨w, rfl⟩ : ∃ w, (isoPow (yoneda : HornCat.{u} L ⥤ _) X.n).hom.app (op c) w = z :=
      ⟨(isoPow (yoneda : HornCat.{u} L ⥤ _) X.n).inv.app (op c) z, by simp⟩
    obtain ⟨σ, hσ, rfl⟩ := exists_eq_mor w
    rw [secEquiv_isoPow_hom] at hz
    have hX : IsMor c X σ := (genericPsh_holds c X σ).1 hz
    exact ⟨mor σ hX, rfl⟩
  · rw [range_app_mk]
    rintro _ ⟨g, rfl⟩
    obtain ⟨σ, hσ, rfl⟩ := exists_eq_mor g
    rw [mem_range_interp_app_iff, realize_toFormula]
    change @Holds L X _ ((genericPsh L).fiberStr (op c)) (secEquiv _ X.n (op c)
      ((isoPow (yoneda : HornCat.{u} L ⥤ _) X.n).hom.app (op c) (toTop c σ)))
    rw [secEquiv_isoPow_hom]
    exact (genericPsh_holds c X σ).2 hσ

end HornCat

end LeanPool.ClassifyingTopoi.Syntactic
