/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Universal
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Transport
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The object classifier (roadmap 3.2)

The theory of objects `LeanPool.ClassifyingTopoi.objectTheory`, the empty theory over the empty
language, is classified by the topos of functors from finite sets to sets, with the generic object
the inclusion of finite sets into sets
(`LeanPool.ClassifyingTopoi.isClassifyingSite_genericObject`).

## Proof

The presheaf topos on the Horn category of the empty language classifies the empty theory
(`Syntactic.HornCat.isClassifyingSite_hornCat`). The functor
`Syntactic.HornCat.ofSkeleton : FintypeCat.Skeletonᵒᵖ ⥤ HornCat Language.empty`, sending `n` to
the context `⊤` in `n` variables, is an equivalence: it is fully faithful since the terms of the
empty language are variables, and every Horn formula, a list of equations between variables, is
isomorphic to the context `⊤` in its classes of equal variables (`HornCat.isoTop`). Transporting
along the induced equivalence of presheaf topoi (`IsClassifyingSite.of_equivalence`), the generic
structure, the Yoneda embedding of `⊤₁`, becomes the inclusion of finite sets
(`HornCat.ofSkeletonCompYonedaIso`); for the empty language an isomorphism of carriers is an
isomorphism of structures.
-/

@[expose] public section

universe u

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance high] Sheaf.instHasColimitsOfShape

/-- **3.2.** The theory of objects: the empty theory over the empty language. -/
def objectTheory : GeometricTheory.{u} FirstOrder.Language.empty := ∅

/-- **3.2.** The generic object: the inclusion of finite sets into sets, as a presheaf on the
opposite of the skeleton of finite sets. -/
noncomputable def genericObject :
    CatStructure FirstOrder.Language.empty
      (Sheaf (⊥ : GrothendieckTopology FintypeCat.Skeleton.{u}ᵒᵖ) (Type u)) where
  carrier := (sheafBotEquivalence (Type u)).inverse.obj
    (unopUnop _ ⋙ FintypeCat.Skeleton.incl ⋙ FintypeCat.incl)
  funMap f := Empty.elim f
  relMap R := Empty.elim R

namespace Syntactic.HornCat

/-- The variable of a term of the empty language. -/
def termVar {α : Type*} : Language.empty.Term α → α
  | .var a => a
  | .func f _ => Empty.elim f

/-- Every term of the empty language is a variable. -/
theorem var_termVar {α : Type*} (t : Language.empty.Term α) : Term.var (termVar t) = t := by
  cases t with
  | var a => rfl
  | func f _ => exact Empty.elim f

/-- The functor from the opposite of the skeleton of finite sets to the Horn category of the
empty language: `n` goes to the context `⊤` in `n` variables, a map of finite sets to the tuple of
variables it defines. -/
def ofSkeleton : FintypeCat.Skeleton.{u}ᵒᵖ ⥤ HornCat.{u} Language.empty where
  obj X := top X.unop.len
  map f := toTop _ fun i => Term.var (f.unop ⟨i⟩).down
  map_id _ := rfl
  map_comp _ _ := rfl

instance : ofSkeleton.{u}.Faithful where
  map_injective {X Y} f g h := by
    let : Language.empty.Structure (ULift.{u} (Fin X.unop.len)) := Language.emptyStructure
    apply Quiver.Hom.unop_inj
    funext i
    have := toTop_eq_toTop_iff.1 h (ULift.{u} (Fin X.unop.len)) ULift.up (holds_top _) i.down
    exact ULift.ext (ULift.up_injective this)

instance : ofSkeleton.{u}.Full where
  map_surjective {X Y} f := by
    obtain ⟨σ, hσ, rfl⟩ := exists_eq_mor f
    refine ⟨Quiver.Hom.op fun i => ⟨termVar (σ i.down)⟩, ?_⟩
    change toTop _ _ = toTop _ σ
    congr 1
    funext i
    exact var_termVar _

/-- Two variables of a Horn formula of the empty language are equivalent when they are equal at
every assignment satisfying the formula. -/
def varSetoid (X : HornCat.{u} Language.empty) : Setoid (Fin X.n) where
  r i j := ∀ (M : Type u) [Language.empty.Structure M] (x : Fin X.n → M), X.Holds x → x i = x j
  iseqv :=
    { refl := fun _ _ _ _ _ => rfl
      symm := fun h M _ x hx => (h M x hx).symm
      trans := fun h h' M _ x hx => (h M x hx).trans (h' M x hx) }

/-- The equations of a Horn formula of the empty language identify equivalent variables. -/
theorem holds_comp_mk {X : HornCat.{u} Language.empty} {M : Type*}
    [Language.empty.Structure M] (y : Quotient X.varSetoid → M) : X.Holds (y ∘ Quotient.mk _) := by
  intro a ha
  cases a with
  | equal t₁ t₂ =>
    change t₁.realize (y ∘ Quotient.mk _) = t₂.realize (y ∘ Quotient.mk _)
    rw [← var_termVar t₁, ← var_termVar t₂]
    refine congrArg y (Quotient.sound fun N _ x hx => ?_)
    have := hx _ ha
    change t₁.realize x = t₂.realize x at this
    rwa [← var_termVar t₁, ← var_termVar t₂] at this
  | rel R _ => exact Empty.elim R

/-- Every Horn formula of the empty language is isomorphic to a context `⊤`, in as many variables
as classes of equivalent variables. -/
noncomputable def isoTop (X : HornCat.{u} Language.empty) :
    top.{u} (Nat.card (Quotient X.varSetoid)) ≅ X :=
  let e := Finite.equivFin (Quotient X.varSetoid)
  { hom := mor (fun i => Term.var (e ⟦i⟧)) fun _ _ y _ => holds_comp_mk (y ∘ e)
    inv := toTop X fun j => Term.var (e.symm j).out
    hom_inv_id := (mor_eq_mor_iff _ _).2 fun _ _ _ _ j => by
      simp
    inv_hom_id := (mor_eq_mor_iff _ _).2 fun M _ x hx i => by
      simpa [Term.realize_subst] using Quotient.mk_out (s := X.varSetoid) i M x hx }

instance : ofSkeleton.{u}.EssSurj where
  mem_essImage X := ⟨op (FintypeCat.Skeleton.mk _), ⟨isoTop X⟩⟩

instance : ofSkeleton.{u}.IsEquivalence where

/-- The morphisms from the context `⊤` in `n` variables to the context `⊤` in one variable are
the variables. -/
noncomputable def homTopEquiv (n : FintypeCat.Skeleton.{u}) :
    (top.{u} (L := Language.empty) n.len ⟶ top 1) ≃ ULift.{u} (Fin n.len) where
  toFun g :=
    (ofSkeleton.preimage (X := op n) (Y := op (FintypeCat.Skeleton.mk 1)) g).unop
      (⟨0⟩ : ULift (Fin 1))
  invFun a := toTop _ fun _ => Term.var a.down
  left_inv g := by
    conv_rhs => rw [← ofSkeleton.map_preimage (X := op n) (Y := op (FintypeCat.Skeleton.mk 1)) g]
    change toTop _ _ = toTop _ _
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  right_inv a := by
    change (ofSkeleton.preimage (ofSkeleton.map (Quiver.Hom.op (fun _ => a) :
      op n ⟶ op (FintypeCat.Skeleton.mk 1)))).unop (⟨0⟩ : ULift (Fin 1)) = a
    rw [Functor.preimage_map]
    rfl

/-- The variables of the context `⊤` are natural in the finite set of variables. -/
theorem homTopEquiv_comp {m n : FintypeCat.Skeleton.{u}} (h : op m ⟶ op n)
    (g : top.{u} (L := Language.empty) n.len ⟶ top 1) :
    homTopEquiv m (ofSkeleton.map h ≫ g) = h.unop (homTopEquiv n g) := by
  apply (homTopEquiv m).symm.injective
  rw [Equiv.symm_apply_apply]
  conv_lhs => rw [← (homTopEquiv n).symm_apply_apply g]
  rfl

/-- The generic presheaf of the Horn category of the empty language, restricted to the skeleton
of finite sets, is the inclusion of finite sets into sets. -/
noncomputable def ofSkeletonCompYonedaIso :
    ofSkeleton.{u}.op ⋙ yoneda.obj (top 1) ≅
      unopUnop _ ⋙ FintypeCat.Skeleton.incl ⋙ FintypeCat.incl :=
  NatIso.ofComponents (fun Z => (homTopEquiv Z.unop.unop).toIso) fun f => by
    ext g
    exact homTopEquiv_comp f.unop g

end Syntactic.HornCat

open Syntactic Syntactic.HornCat in
/-- **3.2.** The topos of functors from finite sets to sets classifies objects. -/
theorem isClassifyingSite_genericObject :
    IsClassifyingSite objectTheory.{u} ⊥ genericObject.{u} := by
  let e : Sheaf (⊥ : GrothendieckTopology (HornCat.{u} Language.empty)) (Type u) ≌
      Sheaf (⊥ : GrothendieckTopology FintypeCat.Skeleton.{u}ᵒᵖ) (Type u) :=
    (sheafBotEquivalence (Type u)).trans (ofSkeleton.{u}.asEquivalence.op.symm.congrLeft.trans
      (sheafBotEquivalence (Type u)).symm)
  refine (isClassifyingSite_hornCat.{u} Language.empty).of_equivalence e ?_
  refine ⟨(sheafBotEquivalence (Type u)).inverse.mapIso ofSkeletonCompYonedaIso,
    ⟨fun f => Empty.elim f, fun R => Empty.elim R⟩, ⟨fun f => Empty.elim f, fun R => Empty.elim R⟩⟩

end LeanPool.ClassifyingTopoi
