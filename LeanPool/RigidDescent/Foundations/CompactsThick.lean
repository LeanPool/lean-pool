/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Foundations.Neeman
public import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Compact objects: `T^ω = Thick(G)`, and they are essentially small

Let `T` be a compactly generated triangulated category, and let `Thick(G)` (`thickGen`) be the
smallest triangulated subcategory closed under retracts containing the generators (mathlib's
`triangEnvelope`; we add `0` to the generators so that this is right also when there are no
generators).

* `compacts_eq_thickGen`: the compact objects are exactly `Thick(G)`.
* `essentiallySmall_compacts`: the compact objects are essentially small; `compactObj` is a
  small family of compact objects with every compact object isomorphic to a member.

`Thick(G) ⊆ T^ω` because the compact objects form a thick subcategory. For the converse, let
`K` be compact and take the cellular tower of `Hom(-, K)` (`Foundations/Neeman.lean`), so
`X∞ ≅ K`. By compactness, `K ⟶ X∞` factors through some `Xₙ`, so it suffices that every map
from a compact object to `Xₙ` factors through an object of `Thick(G)`
(`CellularTower.factorsThroughThick`); then `K` is a retract of that object. This is proved by
induction on `n`, using that a map from a compact object to a coproduct of generators is a
finite sum, and, for the induction step along a triangle `C → Xₙ → Xₙ₊₁ → C⟦1⟧`, two
applications of TR3.

Essential smallness of `Thick(G)` follows from that of the generators, since each closure
operation in `triangEnvelope` preserves essential smallness (`essentiallySmall_triangEnvelope`).
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated ObjectProperty
open scoped ZeroObject

universe v u

namespace RigidDescent

/-! ### Essential smallness of `triangEnvelope` -/

section Small

variable {C : Type u} [Category.{v} C]

/-- `P` is essentially small if every object with `P` is isomorphic to a member of a family
indexed by a type in `Type v`. -/
lemma essentiallySmall_of_forall_iso {P : ObjectProperty C} {α : Type v} (F : α → C)
    (h : ∀ X, P X → ∃ a, Nonempty (X ≅ F a)) : ObjectProperty.EssentiallySmall.{v} P where
  exists_small_le' := ⟨ofObj F, inferInstance, fun X hX => by
    obtain ⟨a, ⟨e⟩⟩ := h X hX
    exact ⟨F a, ofObj_apply F a, ⟨e⟩⟩⟩

/-- If `P` is essentially small, every object with `P` is isomorphic to a member of a family
indexed by a type in `Type v`. -/
lemma exists_iso_of_essentiallySmall (P : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{v} P] :
    ∃ (α : Type v) (F : α → C), ∀ X, P X → ∃ a, Nonempty (X ≅ F a) := by
  obtain ⟨Q, _, hQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le' P
  obtain ⟨α, F, rfl⟩ := ObjectProperty.Small.exists_eq_ofObj.{v} Q
  refine ⟨α, F, fun X hX => ?_⟩
  obtain ⟨Y, hY, ⟨e⟩⟩ := hQ X hX
  obtain ⟨a⟩ := hY
  exact ⟨a, ⟨e⟩⟩

instance essentiallySmall_shiftClosure [HasShift C ℤ] (P : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{v} P] :
    ObjectProperty.EssentiallySmall.{v} (P.shiftClosure ℤ) := by
  obtain ⟨α, F, hF⟩ := exists_iso_of_essentiallySmall P
  refine essentiallySmall_of_forall_iso (fun p : α × ℤ => (F p.1)⟦p.2⟧) ?_
  rintro X ⟨Y, n, e, hY⟩
  obtain ⟨a, ⟨e'⟩⟩ := hF Y hY
  exact ⟨(a, n), ⟨e ≪≫ (shiftFunctor C n).mapIso e'⟩⟩

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Extensions of objects of two essentially small properties form an essentially small
property: an extension `Y → X → Z → Y⟦1⟧` is determined up to isomorphism by `Z → Y⟦1⟧`. -/
instance essentiallySmall_extensionProduct (P Q : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{v} P] [ObjectProperty.EssentiallySmall.{v} Q] :
    ObjectProperty.EssentiallySmall.{v} (extensionProduct P Q) := by
  obtain ⟨α, F, hF⟩ := exists_iso_of_essentiallySmall P
  obtain ⟨β, F', hF'⟩ := exists_iso_of_essentiallySmall Q
  refine essentiallySmall_of_forall_iso
    (fun p : Σ (a : α) (b : β), F' b ⟶ (F a)⟦(1 : ℤ)⟧ =>
      (distinguished_cocone_triangle₂ p.2.2).choose) ?_
  rintro X ⟨Y, Z, f, g, h, hT, hY, hZ⟩
  obtain ⟨a, ⟨eY⟩⟩ := hF Y hY
  obtain ⟨b, ⟨eZ⟩⟩ := hF' Z hZ
  let h' : F' b ⟶ (F a)⟦(1 : ℤ)⟧ := eZ.inv ≫ h ≫ (shiftFunctor C (1 : ℤ)).map eY.hom
  refine ⟨⟨a, b, h'⟩, ?_⟩
  obtain ⟨f', g', hT'⟩ := (distinguished_cocone_triangle₂ h').choose_spec
  have hT₁ : Triangle.mk (eY.inv ≫ f) (g ≫ eZ.hom) h' ∈ distTriang C :=
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ eY.symm (Iso.refl _) eZ.symm
      (by simp) (by simp) (by simp [h', ← Functor.map_comp]))
  obtain ⟨e, -⟩ := exists_iso_of_arrow_iso _ _ (rot_of_distTriang _ (rot_of_distTriang _ hT₁))
    (rot_of_distTriang _ (rot_of_distTriang _ hT')) (Iso.refl _)
  exact ⟨(shiftFunctor C (1 : ℤ)).preimageIso (Triangle.π₃.mapIso e)⟩

instance essentiallySmall_extensionProductIter (P : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{v} P] (n : ℕ) :
    ObjectProperty.EssentiallySmall.{v} (P.extensionProductIter n) := by
  induction n with
  | zero => rw [extensionProductIter_zero]; infer_instance
  | succ n ih => rw [extensionProductIter_succ]; infer_instance

/-- The triangulated envelope (closure under shifts, finite sums, extensions and retracts) of
an essentially small property is essentially small. -/
instance essentiallySmall_triangEnvelope (P : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{v} P] :
    ObjectProperty.EssentiallySmall.{v} P.triangEnvelope := by
  unfold triangEnvelope
  infer_instance

end Small

/-! ### The compact objects form a thick subcategory -/

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

section Compacts

variable [HasCoproducts.{v} T]

variable (T) in
/-- The compact objects, as a property of objects. -/
abbrev compacts : ObjectProperty T := fun K => IsCompactObj K

instance : (compacts T).IsStableUnderRetracts where
  of_retract r h := IsCompactObj.of_retract h r.i r.r r.retract

instance : (compacts T).IsTriangulated where
  exists_zero := ⟨0, isZero_zero T, isCompactObj_of_isZero (isZero_zero T)⟩
  isStableUnderShiftBy n := ⟨fun _ hK => IsCompactObj.shift hK n⟩
  ext₂' Tr hTr h₁ h₃ := le_isoClosure _ _ (isCompactObj₂_of_distTriang Tr hTr h₁ h₃)

end Compacts

/-! ### `Thick(G)` -/

variable [CompactlyGenerated T]

open CompactlyGenerated

namespace CompactlyGenerated

variable (T) in
/-- The generators, together with `0`. -/
noncomputable def genZero (o : Option (GenIndex T)) : T := o.elim 0 (gen T)

end CompactlyGenerated

variable (T) in
/-- `Thick(G)`: the smallest triangulated subcategory closed under retracts that contains the
generators (and `0`). -/
abbrev thickGen : ObjectProperty T := (ofObj (genZero T)).triangEnvelope

/-- `Thick(G) ⊆ T^ω`. -/
lemma thickGen_le_compacts : thickGen T ≤ compacts T := by
  refine (triangEnvelope_le_iff _).2 ((ofObj_le_iff _ _).2 ?_)
  rintro (_ | i)
  · exact isCompactObj_of_isZero (isZero_zero T)
  · exact isCompactObj_gen i

lemma thickGen_shiftedGen (p : GenIndex T × ℤ) : thickGen T (shiftedGen T p) :=
  (thickGen T).le_shift p.2 _ (le_triangEnvelope _ _ (ofObj_apply (genZero T) (some p.1)))

/-- `f` factors through an object of `Thick(G)`. -/
def FactorsThroughThick {K Y : T} (f : K ⟶ Y) : Prop :=
  ∃ (S : T) (_ : thickGen T S) (a : K ⟶ S) (b : S ⟶ Y), f = a ≫ b

namespace FactorsThroughThick

variable {K Y : T}

lemma of_thick {S : T} (hS : thickGen T S) (a : K ⟶ S) (b : S ⟶ Y) :
    FactorsThroughThick (a ≫ b) :=
  ⟨S, hS, a, b, rfl⟩

lemma neg {f : K ⟶ Y} (h : FactorsThroughThick f) : FactorsThroughThick (-f) := by
  obtain ⟨S, hS, a, b, rfl⟩ := h
  exact ⟨S, hS, a, -b, by simp⟩

lemma comp_right {f : K ⟶ Y} (h : FactorsThroughThick f) {Y' : T} (y : Y ⟶ Y') :
    FactorsThroughThick (f ≫ y) := by
  obtain ⟨S, hS, a, b, rfl⟩ := h
  exact ⟨S, hS, a, b ≫ y, by simp⟩

variable [IsTriangulated T]

lemma zero (K Y : T) : FactorsThroughThick (0 : K ⟶ Y) := by
  obtain ⟨Z, -, hZ⟩ := ContainsZero.exists_zero (P := thickGen T)
  exact ⟨Z, hZ, 0, 0, by simp⟩

lemma add {f f' : K ⟶ Y} (h : FactorsThroughThick f) (h' : FactorsThroughThick f') :
    FactorsThroughThick (f + f') := by
  obtain ⟨S, hS, a, b, rfl⟩ := h
  obtain ⟨S', hS', a', b', rfl⟩ := h'
  refine ⟨S ⊞ S', ?_, biprod.lift a a', biprod.desc b b', by simp⟩
  exact (thickGen T).ext_of_isTriangulatedClosed₂ _
    (binaryBiproductTriangle_distinguished S S') hS hS'

lemma sub {f f' : K ⟶ Y} (h : FactorsThroughThick f) (h' : FactorsThroughThick f') :
    FactorsThroughThick (f - f') := by
  rw [sub_eq_add_neg]
  exact h.add h'.neg

lemma sum {J : Type*} (F : Finset J) (f : J → (K ⟶ Y))
    (h : ∀ j ∈ F, FactorsThroughThick (f j)) : FactorsThroughThick (∑ j ∈ F, f j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using zero K Y
  | insert j F hj ih =>
    rw [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end FactorsThroughThick

variable [IsTriangulated T]

/-- A map from a compact object to a coproduct of objects of `Thick(G)` factors through an
object of `Thick(G)`. -/
lemma factorsThroughThick_of_sigma {K : T} (hK : IsCompactObj K) {J : Type*} [Small.{v} J]
    {Y : J → T} [HasCoproduct Y] (hY : ∀ j, thickGen T (Y j)) (k : K ⟶ ∐ Y) :
    FactorsThroughThick k := by
  obtain ⟨F, a, rfl⟩ := hK.isFiniteSum_of_small k
  exact FactorsThroughThick.sum F _ fun j _ => .of_thick (hY j) (a j) (Sigma.ι Y j)

/-- In a cellular tower with respect to the shifted generators, every map from a compact object
to a stage `Xₙ` factors through an object of `Thick(G)`. -/
lemma CellularTower.factorsThroughThick {H : Tᵒᵖ ⥤ AddCommGrpCat.{v}}
    (ct : CellularTower H (shiftedGen T)) (n : ℕ) {L : T} (hL : IsCompactObj L)
    (k : L ⟶ ct.X n) : FactorsThroughThick k := by
  induction n generalizing L with
  | zero =>
    obtain ⟨J, j, ⟨e⟩⟩ := ct.zero
    have := (factorsThroughThick_of_sigma hL (fun i => thickGen_shiftedGen (j i))
      (k ≫ e.hom)).comp_right e.inv
    simpa using this
  | succ n ih =>
    obtain ⟨J, j, f, δ, hT⟩ := ct.succ n
    -- `k ≫ δ = a ≫ t⟦1⟧'` with `t : F ⟶ ∐ gⱼ`, `F ∈ Thick(G)`
    obtain ⟨y, hy⟩ := (shiftFunctor T (1 : ℤ)).map_surjective
      ((shiftNegShift L (1 : ℤ)).hom ≫ k ≫ δ)
    obtain ⟨F, hF, a', t, rfl⟩ := factorsThroughThick_of_sigma (hL.shift (-1))
      (fun i => thickGen_shiftedGen (j i)) y
    let a : L ⟶ F⟦(1 : ℤ)⟧ := (shiftNegShift L (1 : ℤ)).inv ≫ a'⟦(1 : ℤ)⟧'
    have hka : k ≫ δ = a ≫ t⟦(1 : ℤ)⟧' := by
      rw [Functor.map_comp] at hy
      simp only [a, Category.assoc, hy, Iso.inv_hom_id_assoc]
    -- the triangle `F → L'' → L → F⟦1⟧`
    obtain ⟨L'', c, b, hT'⟩ := distinguished_cocone_triangle₂ a
    have hL'' : IsCompactObj L'' :=
      isCompactObj₂_of_distTriang _ hT' (thickGen_le_compacts _ hF) hL
    have hcb : c ≫ b = 0 := comp_distTriang_mor_zero₁₂ _ hT'
    have hba : b ≫ a = 0 := comp_distTriang_mor_zero₂₃ _ hT'
    -- `b ≫ k = k'' ≫ xₙ`
    obtain ⟨k'', hk''⟩ := Triangle.coyoneda_exact₃ _ hT (b ≫ k) (by
      dsimp
      rw [Category.assoc, hka, ← Category.assoc, hba, Limits.zero_comp])
    dsimp at hk''
    obtain ⟨S', hS', s, t', rfl⟩ := ih hL'' k''
    -- `c ≫ s ≫ t' = e ≫ f`
    obtain ⟨e, he⟩ := Triangle.coyoneda_exact₂ _ hT (c ≫ s ≫ t') (by
      dsimp
      rw [Category.assoc, Category.assoc, ← Category.assoc s, ← hk'', ← Category.assoc, hcb,
        Limits.zero_comp])
    dsimp at he
    -- `Q`, the cone of `c ≫ s`, is in `Thick(G)`
    obtain ⟨Q, q, r, hQ⟩ := distinguished_cocone_triangle (c ≫ s)
    have hQS : thickGen T Q := (thickGen T).ext_of_isTriangulatedClosed₃ _ hQ hF hS'
    obtain ⟨φ, hφ, -⟩ := complete_distinguished_triangle_morphism _ _ hT' hQ (𝟙 F) s
      (by simp)
    obtain ⟨ψ, hψ, -⟩ := complete_distinguished_triangle_morphism _ _ hQ hT e t'
      (by simpa using he)
    dsimp at hφ hψ
    -- `b ≫ (φ ≫ ψ - k) = 0`, so `φ ≫ ψ - k` factors through `a`
    obtain ⟨ρ, hρ⟩ := Triangle.yoneda_exact₃ _ hT' ((φ ≫ ψ : L ⟶ ct.X (n + 1)) - k) (by
      dsimp
      rw [Preadditive.comp_sub, ← Category.assoc, hφ, Category.assoc, hψ, hk'',
        Category.assoc, sub_self])
    dsimp at hρ
    have hk : k = (φ ≫ ψ : L ⟶ ct.X (n + 1)) - a ≫ ρ := by rw [← hρ, sub_sub_cancel]
    rw [hk]
    exact (FactorsThroughThick.of_thick hQS φ ψ).sub
      (.of_thick ((thickGen T).le_shift 1 _ hF) a ρ)

/-- `T^ω ⊆ Thick(G)`. -/
theorem compacts_le_thickGen : compacts T ≤ thickGen T := by
  intro K hK
  obtain ⟨ct⟩ := CellularTower.nonempty_yoneda K
  have := ct.isIso_hom
  obtain ⟨n, k', hk'⟩ := ct.tel.exists_factor hK (inv ct.hom)
  obtain ⟨S, hS, a, b, rfl⟩ := ct.factorsThroughThick n hK k'
  refine (thickGen T).prop_of_retract ⟨a, b ≫ ct.tel.ι n ≫ ct.hom, ?_⟩ hS
  rw [← Category.assoc, ← Category.assoc, ← hk', IsIso.inv_hom_id]

/-- `T^ω = Thick(G)`: the compact objects are exactly the objects of the smallest triangulated
subcategory closed under retracts containing the generators. -/
theorem compacts_eq_thickGen : compacts T = thickGen T :=
  le_antisymm compacts_le_thickGen thickGen_le_compacts

/-- The compact objects are essentially small. -/
instance essentiallySmall_compacts : ObjectProperty.EssentiallySmall.{v} (compacts T) :=
  ObjectProperty.EssentiallySmall.of_le compacts_le_thickGen

lemma exists_compactModel :
    ∃ (α : Type v) (F : α → T), compacts T = (ofObj F).isoClosure :=
  ObjectProperty.EssentiallySmall.exists_eq_isoClosure_ofObj.{v} (compacts T)

variable (T) in
/-- The index type of a small model of the compact objects. -/
def CompactIndex : Type v := (exists_compactModel (T := T)).choose

variable (T) in
/-- A small family of compact objects such that every compact object is isomorphic to a
member (`exists_iso_compactObj`). -/
noncomputable def compactObj : CompactIndex T → T :=
  (exists_compactModel (T := T)).choose_spec.choose

lemma compacts_eq_isoClosure : compacts T = (ofObj (compactObj T)).isoClosure :=
  (exists_compactModel (T := T)).choose_spec.choose_spec

lemma isCompactObj_compactObj (i : CompactIndex T) : IsCompactObj (compactObj T i) := by
  have : compacts T (compactObj T i) := by
    rw [compacts_eq_isoClosure]
    exact le_isoClosure _ _ (ofObj_apply _ i)
  exact this

lemma exists_iso_compactObj {K : T} (hK : IsCompactObj K) :
    ∃ i, Nonempty (K ≅ compactObj T i) := by
  have : compacts T K := hK
  rw [compacts_eq_isoClosure] at this
  obtain ⟨Y, hY, ⟨e⟩⟩ := this
  obtain ⟨i⟩ := hY
  exact ⟨i, ⟨e⟩⟩

end RigidDescent
