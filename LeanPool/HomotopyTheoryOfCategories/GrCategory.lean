/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.Abel

/-!
# Gr-categories and two-term complexes

A *gr-category* is a monoidal groupoid in which every object has a tensor inverse
up to isomorphism. In the two-term example below, Mathlib's `Skeleton` represents
the monoid of isomorphism classes.

For an additive map `d : K⁻¹ →+ K⁰` we define the symmetric monoidal groupoid `TwoTerm d`
(`ch(d)` of Deligne, SGA 4 XVIII, §1.4): objects the elements of `K⁰`, morphisms `x ⟶ y` the
labels `k : K⁻¹` with `x + d k = y`, tensor `+` and `0`-labelled structure isomorphisms, and we
prove

* `nonempty_skeletonTwoTerm_mulEquiv`: `π₀ ch(d) ≃* coker d`;
* `nonempty_autUnitTwoTerm_mulEquiv`: `π₁ ch(d) = Aut (𝟙_) ≃* ker d`.

We also define `IsStrictlyCommutative`. Sính's classification by `(π₀, π₁, k)`, crossed modules,
Picard groupoids and Deligne's equivalence (roadmap 12.2–12.6 beyond these, Layer 13) are not
formalised.

This is Layer 12 of the roadmap *Homotopy theory of small categories*.
-/

@[expose] public section

universe v u

namespace LeanPool.HomotopyTheoryOfCategories

open CategoryTheory MonoidalCategory

/-- **Layer 12.6.** Strict commutativity of a symmetric monoidal category (Deligne, SGA 4 XVIII,
§1.4): the symmetry of `X ⊗ X` is the identity. -/
def IsStrictlyCommutative (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] : Prop :=
  ∀ X : C, (β_ X X).hom = 𝟙 (X ⊗ X)

/-- **Layer 12.6.** `ch(d)`: objects the elements of `K⁰`, morphisms `x ⟶ y` the `k : K⁻¹`
with `x + d k = y`. -/
structure TwoTerm {K₁ K₀ : Type u} [AddCommGroup K₁] [AddCommGroup K₀] (d : K₁ →+ K₀) where
  /-- The underlying element of `K⁰`. -/
  val : K₀

namespace TwoTerm

variable {K₁ K₀ : Type u} [AddCommGroup K₁] [AddCommGroup K₀] {d : K₁ →+ K₀}

/-- **Layer 12.6.** A morphism `x ⟶ y` of `ch(d)`: a label `k : K⁻¹` with `x + d k = y`. -/
@[ext]
structure Hom (x y : TwoTerm d) where
  /-- The label in `K⁻¹`. -/
  label : K₁
  /-- The label carries `x` to `y`. -/
  w : x.val + d label = y.val

/-- **Layer 12.6.** The groupoid `ch(d)`: composition adds labels, inversion negates them. -/
instance : Groupoid.{u} (TwoTerm d) where
  Hom := Hom
  id x := ⟨0, by simp⟩
  comp f g := ⟨f.label + g.label, by rw [map_add, ← add_assoc, f.w, g.w]⟩
  id_comp f := Hom.ext (zero_add _)
  comp_id f := Hom.ext (add_zero _)
  assoc f g h := Hom.ext (add_assoc _ _ _)
  inv f := ⟨-f.label, by rw [map_neg, ← f.w]; abel⟩
  inv_comp f := Hom.ext (neg_add_cancel _)
  comp_inv f := Hom.ext (add_neg_cancel _)

/-- **Layer 12.6.** Labels add under composition (a proof obligation of the instances below). -/
@[simp]
theorem comp_label {x y z : TwoTerm d} (f : x ⟶ y) (g : y ⟶ z) :
    Hom.label (f ≫ g) = Hom.label f + Hom.label g :=
  rfl

/-- **Layer 12.6.** The morphism of `ch(d)` labelled `0` between objects with equal values. -/
def eqHom {x y : TwoTerm d} (h : x.val = y.val) : x ⟶ y :=
  (⟨0, by rw [map_zero, add_zero, h]⟩ : Hom x y)

/-- **Layer 12.6.** The isomorphism of `ch(d)` labelled `0` between objects with equal values. -/
def eqIso {x y : TwoTerm d} (h : x.val = y.val) : x ≅ y where
  hom := eqHom h
  inv := eqHom h.symm
  hom_inv_id := Hom.ext (add_zero (0 : K₁))
  inv_hom_id := Hom.ext (add_zero (0 : K₁))

/-- **Layer 12.6.** The isomorphisms `eqIso` are labelled `0` (a proof obligation of the
instances below). -/
@[simp]
theorem eqIso_hom_label {x y : TwoTerm d} (h : x.val = y.val) : Hom.label (eqIso h).hom = 0 :=
  rfl

/-- **Layer 12.6.** The inverses of the isomorphisms `eqIso` are labelled `0` (a proof
obligation of the instances below). -/
@[simp]
theorem eqIso_inv_label {x y : TwoTerm d} (h : x.val = y.val) : Hom.label (eqIso h).inv = 0 :=
  rfl

/-- **Layer 12.6.** The monoidal structure of `ch(d)`: tensor `+` on objects and on labels,
with `0`-labelled structure isomorphisms. -/
instance : MonoidalCategory (TwoTerm d) where
  tensorObj x y := ⟨x.val + y.val⟩
  whiskerLeft x _ _ f := (⟨Hom.label f, by
    change x.val + _ + d (Hom.label f) = x.val + _; rw [add_assoc, Hom.w f]⟩ : Hom _ _)
  whiskerRight f y := (⟨Hom.label f, by
    change _ + y.val + d (Hom.label f) = _ + y.val; rw [add_right_comm, Hom.w f]⟩ : Hom _ _)
  tensorHom f g := (⟨Hom.label f + Hom.label g, by
    change _ + _ + d (Hom.label f + Hom.label g) = _ + _
    rw [map_add, ← Hom.w f, ← Hom.w g]; abel⟩ : Hom _ _)
  tensorUnit := ⟨0⟩
  associator x y z := eqIso (add_assoc x.val y.val z.val)
  leftUnitor x := eqIso (zero_add x.val)
  rightUnitor x := eqIso (add_zero x.val)
  tensorHom_def f g := Hom.ext (by simp only [comp_label])
  id_tensorHom_id x y := Hom.ext (add_zero (0 : K₁))
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := Hom.ext (by simp only [comp_label]; abel)
  whiskerLeft_id x y := Hom.ext rfl
  id_whiskerRight x y := Hom.ext rfl
  associator_naturality f₁ f₂ f₃ := Hom.ext (by
    simp only [comp_label, eqIso_hom_label]; abel)
  leftUnitor_naturality f := Hom.ext (by simp only [comp_label, eqIso_hom_label]; abel)
  rightUnitor_naturality f := Hom.ext (by simp only [comp_label, eqIso_hom_label]; abel)
  pentagon w x y z := Hom.ext (by simp only [comp_label, eqIso_hom_label]; abel)
  triangle x y := Hom.ext (by simp only [comp_label, eqIso_hom_label]; abel)

/-- **Layer 12.6.** The symmetry of `ch(d)`, labelled `0`. -/
instance : SymmetricCategory (TwoTerm d) where
  braiding x y := eqIso (add_comm x.val y.val)
  braiding_naturality_right x y z f := Hom.ext (by
    simp only [comp_label, eqIso_hom_label]; abel)
  braiding_naturality_left f z := Hom.ext (by
    simp only [comp_label, eqIso_hom_label]; abel)
  hexagon_forward x y z := Hom.ext rfl
  hexagon_reverse x y z := Hom.ext rfl
  symmetry x y := Hom.ext (add_zero (0 : K₁))

end TwoTerm

variable {K₁ K₀ : Type u} [AddCommGroup K₁] [AddCommGroup K₀] (d : K₁ →+ K₀)

namespace TwoTerm

variable {d}

/-- Two objects of `ch(d)` are isomorphic iff they have the same class in `coker d`. -/
lemma nonempty_iso_iff (x y : TwoTerm d) :
    Nonempty (x ≅ y) ↔ (QuotientAddGroup.mk x.val : K₀ ⧸ d.range) = QuotientAddGroup.mk y.val := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨e⟩
    exact ⟨Hom.label e.hom, by rw [← Hom.w e.hom]; abel⟩
  · rintro ⟨k, hk⟩
    exact ⟨asIso (⟨k, by rw [hk]; abel⟩ : Hom x y)⟩

/-- The class in `coker d` of an element of `π₀ ch(d)`. -/
noncomputable def skeletonToCoker (s : Skeleton (TwoTerm d)) : K₀ ⧸ d.range :=
  QuotientAddGroup.mk ((fromSkeleton (TwoTerm d)).obj s).val

/-- The class in `coker d` of the component of `x` is the class of `x.val`. -/
lemma skeletonToCoker_toSkeleton (x : TwoTerm d) :
    skeletonToCoker (toSkeleton x) = QuotientAddGroup.mk x.val :=
  (nonempty_iso_iff _ _).1 ⟨fromSkeletonToSkeletonIso x⟩

end TwoTerm

/-- **Layer 12.6.** `π₀ ch(d) = coker d`, as monoids. -/
theorem nonempty_skeletonTwoTerm_mulEquiv :
    Nonempty (Skeleton (TwoTerm d) ≃* Multiplicative (K₀ ⧸ d.range)) := by
  let φ : Skeleton (TwoTerm d) →* Multiplicative (K₀ ⧸ d.range) :=
    { toFun s := Multiplicative.ofAdd (TwoTerm.skeletonToCoker s)
      map_one' := by
        rw [Skeleton.one_eq, TwoTerm.skeletonToCoker_toSkeleton]
        rfl
      map_mul' s t := by
        rw [Skeleton.mul_eq, TwoTerm.skeletonToCoker_toSkeleton]
        rfl }
  refine ⟨MulEquiv.ofBijective φ ⟨fun s t h ↦ ?_, fun c ↦ ?_⟩⟩
  · rw [← toSkeleton_fromSkeleton_obj s, ← toSkeleton_fromSkeleton_obj t]
    exact toSkeleton_eq_toSkeleton_iff.2 ((TwoTerm.nonempty_iso_iff _ _).2 h)
  · induction c using QuotientAddGroup.induction_on with | H v => ?_
    exact ⟨toSkeleton ⟨v⟩, TwoTerm.skeletonToCoker_toSkeleton _⟩

/-- **Layer 12.6.** `π₁ ch(d) = ker d`, as groups. -/
theorem nonempty_autUnitTwoTerm_mulEquiv :
    Nonempty (Aut (𝟙_ (TwoTerm d)) ≃* Multiplicative d.ker) := by
  have hk : ∀ f : 𝟙_ (TwoTerm d) ⟶ 𝟙_ (TwoTerm d), d (TwoTerm.Hom.label f) = 0 := fun f ↦ by
    simpa using TwoTerm.Hom.w f
  let auto (k : d.ker) : 𝟙_ (TwoTerm d) ≅ 𝟙_ (TwoTerm d) :=
    { hom := (⟨k.1, by simpa using AddMonoidHom.mem_ker.1 k.2⟩ : TwoTerm.Hom _ _)
      inv := (⟨-k.1, by simpa using AddMonoidHom.mem_ker.1 k.2⟩ : TwoTerm.Hom _ _)
      hom_inv_id := TwoTerm.Hom.ext (add_neg_cancel _)
      inv_hom_id := TwoTerm.Hom.ext (neg_add_cancel _) }
  exact ⟨
    { toFun σ := Multiplicative.ofAdd ⟨TwoTerm.Hom.label σ.asIso.hom, hk _⟩
      invFun k := .of (auto k.toAdd)
      left_inv σ := Aut.ext (Iso.ext (TwoTerm.Hom.ext rfl))
      right_inv _ := rfl
      map_mul' σ τ := by
        apply Multiplicative.toAdd.injective
        ext
        exact add_comm _ _ }⟩

end LeanPool.HomotopyTheoryOfCategories
