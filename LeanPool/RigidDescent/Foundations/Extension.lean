/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Foundations.Neeman
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Extending isomorphisms from the generators

Let `θ : F ⟶ G` be a natural transformation between functors `T ⥤ AddCommGrpCat` (or
`Tᵒᵖ ⥤ AddCommGrpCat`) that are homological (cohomological) and compatible with coproducts.
If `θ` is an isomorphism at every shifted generator `G i⟦n⟧`, it is an isomorphism at every
object (`NatTrans.isIso_app_of_homological`, `NatTrans.isIso_app_of_cohomological`).

The objects `X` at which `θ` is an isomorphism at all shifts `X⟦n⟧` are closed under
isomorphisms, shifts, extensions (by the additive-group five lemma) and
coproducts, and contain the generators; Neeman's theorem (`prop_of_localizing`) concludes.

For covariant functors, compatibility with coproducts is the condition that every element of
`F(∐ Y)` is a finite sum of elements coming from the summands (`SpannedBySummands`), which
holds when `F` preserves coproducts (`spannedBySummands_of_preserves`).
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated ObjectProperty
open scoped ZeroObject

universe v u

namespace RigidDescent

/-- The additive-group five lemma for diagrams in `AddCommGrpCat`. -/
private lemma bijective_of_five {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : AddCommGrpCat.{v}}
    {f₁ : A₁ ⟶ A₂} {f₂ : A₂ ⟶ A₃} {f₃ : A₃ ⟶ A₄} {f₄ : A₄ ⟶ A₅}
    {g₁ : B₁ ⟶ B₂} {g₂ : B₂ ⟶ B₃} {g₃ : B₃ ⟶ B₄} {g₄ : B₄ ⟶ B₅}
    {v₁ : A₁ ⟶ B₁} {v₂ : A₂ ⟶ B₂} {v₃ : A₃ ⟶ B₃} {v₄ : A₄ ⟶ B₄} {v₅ : A₅ ⟶ B₅}
    (c₁ : f₁ ≫ v₂ = v₁ ≫ g₁) (c₂ : f₂ ≫ v₃ = v₂ ≫ g₂) (c₃ : f₃ ≫ v₄ = v₃ ≫ g₃)
    (c₄ : f₄ ≫ v₅ = v₄ ≫ g₄)
    (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃) (hf₃ : Function.Exact f₃ f₄)
    (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃) (hg₃ : Function.Exact g₃ g₄)
    (hv₁ : Function.Surjective v₁) (hv₂ : Function.Bijective v₂) (hv₄ : Function.Bijective v₄)
    (hv₅ : Function.Injective v₅) : Function.Bijective v₃ :=
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁.hom f₂.hom f₃.hom f₄.hom g₁.hom g₂.hom g₃.hom g₄.hom
    v₁.hom v₂.hom v₃.hom v₄.hom v₅.hom
    (congrArg AddCommGrpCat.Hom.hom c₁.symm) (congrArg AddCommGrpCat.Hom.hom c₂.symm)
    (congrArg AddCommGrpCat.Hom.hom c₃.symm) (congrArg AddCommGrpCat.Hom.hom c₄.symm)
    hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hv₁ hv₂ hv₄ hv₅

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-! ### Homological functors -/

private lemma homological_exact {H : T ⥤ AddCommGrpCat.{v}} (hH : H.IsHomological)
    (triangle : Triangle T) (distinguished : triangle ∈ distTriang T) :
    Function.Exact (H.map triangle.mor₁) (H.map triangle.mor₂) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (hH.exact triangle distinguished)

/-- A natural transformation between homological functors is an isomorphism at the middle
vertex of a distinguished triangle if it is one at the other vertices and their shifts. -/
lemma NatTrans.isIso_app_obj₂_of_homological {F G : T ⥤ AddCommGrpCat.{v}}
    (hF : F.IsHomological) (hG : G.IsHomological) (θ : F ⟶ G)
    (Tr : Triangle T) (hTr : Tr ∈ distTriang T)
    (h₁ : IsIso (θ.app (Tr.obj₁⟦(1 : ℤ)⟧))) (h₁' : IsIso (θ.app Tr.obj₁))
    (h₃ : IsIso (θ.app Tr.obj₃)) (h₃' : IsIso (θ.app (Tr.obj₃⟦(-1 : ℤ)⟧))) :
    IsIso (θ.app Tr.obj₂) := by
  rw [ConcreteCategory.isIso_iff_bijective] at h₁ h₁' h₃ h₃' ⊢
  have hrot := rot_of_distTriang _ hTr
  have hinv := inv_rot_of_distTriang _ hTr
  let first : Tr.obj₃⟦(-1 : ℤ)⟧ ⟶ Tr.obj₁ := Tr.invRotate.mor₁
  exact bijective_of_five
    (f₁ := F.map first) (f₂ := F.map Tr.mor₁) (f₃ := F.map Tr.mor₂)
    (f₄ := F.map Tr.mor₃)
    (g₁ := G.map first) (g₂ := G.map Tr.mor₁) (g₃ := G.map Tr.mor₂)
    (g₄ := G.map Tr.mor₃)
    (θ.naturality _) (θ.naturality _) (θ.naturality _) (θ.naturality _)
    (homological_exact hF _ hinv) (homological_exact hF _ hTr) (homological_exact hF _ hrot)
    (homological_exact hG _ hinv) (homological_exact hG _ hTr) (homological_exact hG _ hrot)
    h₃'.2 h₁' h₃ h₁.1

/-- Every element of `F(∐ Y)` is a finite sum of elements coming from the summands. -/
def SpannedBySummands [HasCoproducts.{v} T] (F : T ⥤ AddCommGrpCat.{v}) : Prop :=
  ∀ (J : Type v) (Y : J → T) (x : F.obj (∐ Y)),
    ∃ (S : Finset J) (a : ∀ j, F.obj (Y j)), x = ∑ j ∈ S, F.map (Sigma.ι Y j) (a j)

omit [Preadditive T] [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] in
/-- A functor preserving coproducts is spanned by summands. -/
lemma spannedBySummands_of_preserves [HasCoproducts.{v} T] (F : T ⥤ AddCommGrpCat.{v})
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F] : SpannedBySummands F := by
  intro J Y x
  obtain ⟨S, a, h⟩ := AddCommGrpCat.exists_eq_sum_of_isColimit
    (isColimitOfHasCoproductOfPreservesColimit F Y) x
  exact ⟨S, a, h⟩

omit [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] in
/-- A natural transformation between functors spanned by summands is an isomorphism at a
coproduct if it is one at every summand. -/
lemma NatTrans.isIso_app_sigma_of_spanned [HasCoproducts.{v} T] {F G : T ⥤ AddCommGrpCat.{v}}
    [F.Additive] (hF : SpannedBySummands F) (hG : SpannedBySummands G) (θ : F ⟶ G)
    {J : Type v} (Y : J → T) (h : ∀ j, IsIso (θ.app (Y j))) : IsIso (θ.app (∐ Y)) := by
  classical
  simp only [ConcreteCategory.isIso_iff_bijective] at h ⊢
  have nat : ∀ {X X' : T} (f : X ⟶ X') (x : F.obj X),
      θ.app X' (F.map f x) = G.map f (θ.app X x) :=
    fun f x => by simp
  have hii : ∀ i (x : F.obj (Y i)), F.map (Sigma.π Y i) (F.map (Sigma.ι Y i) x) = x := by
    intro i x
    rw [← ConcreteCategory.comp_apply, ← F.map_comp]
    simp
  have hij : ∀ i j, j ≠ i → ∀ x : F.obj (Y j), F.map (Sigma.π Y i) (F.map (Sigma.ι Y j) x) = 0 := by
    intro i j hj x
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, Sigma.ι_π_of_ne _ hj, F.map_zero]
    rfl
  refine ⟨(injective_iff_map_eq_zero (ConcreteCategory.hom (θ.app (∐ Y)))).2 fun x hx => ?_,
    fun y => ?_⟩
  · obtain ⟨S, a, rfl⟩ := hF J Y x
    have ha : ∀ i ∈ S, a i = 0 := by
      intro i hi
      apply (injective_iff_map_eq_zero (ConcreteCategory.hom (θ.app (Y i)))).1 (h i).1
      have := congrArg (G.map (Sigma.π Y i)) hx
      rw [map_zero, ← nat, map_sum, map_sum, Finset.sum_eq_single i] at this
      · rwa [hii] at this
      · intro j _ hj
        rw [hij i j hj, map_zero]
      · intro hi'
        exact absurd hi hi'
    exact Finset.sum_eq_zero fun i hi => by rw [ha i hi, map_zero]
  · obtain ⟨S, b, rfl⟩ := hG J Y y
    choose a ha using fun j => (h j).2 (b j)
    refine ⟨∑ j ∈ S, F.map (Sigma.ι Y j) (a j), ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [nat, ha]

/-! ### Cohomological functors -/

private lemma cohomological_exact {H : Tᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive]
    (hH : IsCohomological H) (triangle : Triangle T) (distinguished : triangle ∈ distTriang T) :
    Function.Exact (H.map triangle.mor₂.op) (H.map triangle.mor₁.op) := by
  have zero_composite : H.map triangle.mor₂.op ≫ H.map triangle.mor₁.op = 0 := by
    rw [← H.map_comp, ← op_comp, comp_distTriang_mor_zero₁₂ _ distinguished, op_zero, H.map_zero]
  exact (ShortComplex.ab_exact_iff_function_exact (ShortComplex.mk _ _ zero_composite)).1
    ((ShortComplex.ab_exact_iff (ShortComplex.mk _ _ zero_composite)).2 (hH triangle distinguished))

/-- A natural transformation between cohomological functors is an isomorphism at the middle
vertex of a distinguished triangle if it is one at the other vertices and their shifts. -/
lemma NatTrans.isIso_app_obj₂_of_cohomological {F G : Tᵒᵖ ⥤ AddCommGrpCat.{v}} [F.Additive]
    [G.Additive] (hF : IsCohomological F) (hG : IsCohomological G) (θ : F ⟶ G)
    (Tr : Triangle T) (hTr : Tr ∈ distTriang T)
    (h₁ : IsIso (θ.app (op (Tr.obj₁⟦(1 : ℤ)⟧)))) (h₁' : IsIso (θ.app (op Tr.obj₁)))
    (h₃ : IsIso (θ.app (op Tr.obj₃))) (h₃' : IsIso (θ.app (op (Tr.obj₃⟦(-1 : ℤ)⟧)))) :
    IsIso (θ.app (op Tr.obj₂)) := by
  rw [ConcreteCategory.isIso_iff_bijective] at h₁ h₁' h₃ h₃' ⊢
  have hrot := rot_of_distTriang _ hTr
  have hinv := inv_rot_of_distTriang _ hTr
  let first : Tr.obj₃⟦(-1 : ℤ)⟧ ⟶ Tr.obj₁ := Tr.invRotate.mor₁
  exact bijective_of_five
    (f₁ := F.map Tr.mor₃.op) (f₂ := F.map Tr.mor₂.op) (f₃ := F.map Tr.mor₁.op)
    (f₄ := F.map first.op)
    (g₁ := G.map Tr.mor₃.op) (g₂ := G.map Tr.mor₂.op) (g₃ := G.map Tr.mor₁.op)
    (g₄ := G.map first.op)
    (θ.naturality _) (θ.naturality _) (θ.naturality _) (θ.naturality _)
    (cohomological_exact hF _ hrot) (cohomological_exact hF _ hTr) (cohomological_exact hF _ hinv)
    (cohomological_exact hG _ hrot) (cohomological_exact hG _ hTr) (cohomological_exact hG _ hinv)
    h₁.2 h₃ h₁' h₃'.1

omit [Preadditive T] [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] in
/-- A natural transformation between functors sending coproducts to products is an isomorphism
at a coproduct if it is one at every summand. -/
lemma NatTrans.isIso_app_sigma_of_sendsCoproductsToProducts [HasCoproducts.{v} T]
    {F G : Tᵒᵖ ⥤ AddCommGrpCat.{v}} (hF : SendsCoproductsToProducts F)
    (hG : SendsCoproductsToProducts G) (θ : F ⟶ G) {J : Type v} (Y : J → T)
    (h : ∀ j, IsIso (θ.app (op (Y j)))) : IsIso (θ.app (op (∐ Y))) := by
  simp only [ConcreteCategory.isIso_iff_bijective] at h ⊢
  have nat : ∀ {X X' : T} (f : X ⟶ X') (x : F.obj (op X')),
      θ.app (op X) (F.map f.op x) = G.map f.op (θ.app (op X') x) :=
    fun f x => by simp
  refine ⟨fun x x' hx => (hF J Y).1 (funext fun j => (h j).1 ?_), fun y => ?_⟩
  · dsimp only
    rw [nat, nat, hx]
  · choose a ha using fun j => (h j).2 (G.map (Sigma.ι Y j).op y)
    obtain ⟨x, hx⟩ := (hF J Y).2 a
    refine ⟨x, (hG J Y).1 (funext fun j => ?_)⟩
    have hxj : F.map (Sigma.ι Y j).op x = a j := congrFun hx j
    dsimp only
    rw [← nat, hxj, ha]

/-! ### Extension from the generators -/

variable [CompactlyGenerated T]

open CompactlyGenerated

/-- Neeman's theorem with its hypotheses spelled out: a property of objects that is closed
under isomorphisms, shifts, extensions and coproducts, holds for `0` and for every generator,
holds for every object. -/
lemma prop_of_localizing' (P : ObjectProperty T) (hiso : ∀ {X Y : T}, (X ≅ Y) → P X → P Y)
    (hzero : P 0) (hshift : ∀ (X : T) (n : ℤ), P X → P (X⟦n⟧))
    (hext : ∀ Tr ∈ distTriang T, P Tr.obj₁ → P Tr.obj₃ → P Tr.obj₂)
    (hcoprod : IsClosedUnderCoproducts P) (hG : ∀ i, P (gen T i)) (X : T) : P X := by
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h => hiso e h⟩
  have : P.IsTriangulated :=
    { exists_zero := ⟨0, isZero_zero T, hzero⟩
      isStableUnderShiftBy := fun n => ⟨fun X h => hshift X n h⟩
      ext₂' := fun Tr hTr h₁ h₃ => le_isoClosure _ _ (hext Tr hTr h₁ h₃) }
  exact prop_of_localizing P hcoprod hG X

/-- A natural transformation between additive homological functors spanned by summands which
is an isomorphism at every shifted generator `G i⟦n⟧` is an isomorphism. -/
theorem NatTrans.isIso_app_of_homological {F G : T ⥤ AddCommGrpCat.{v}}
    (hF : F.IsHomological) (hG : G.IsHomological) (hFc : SpannedBySummands F)
    (hGc : SpannedBySummands G) (θ : F ⟶ G)
    (h : ∀ (i : GenIndex T) (n : ℤ), IsIso (θ.app ((gen T i)⟦n⟧))) (X : T) :
    IsIso (θ.app X) := by
  let := hF
  let := hG
  let P : ObjectProperty T := fun X => ∀ n : ℤ, IsIso (θ.app (X⟦n⟧))
  have hiso : ∀ {X Y : T}, (X ≅ Y) → P X → P Y := fun e hX n =>
    (NatTrans.isIso_app_iff_of_iso θ ((shiftFunctor T n).mapIso e)).1 (hX n)
  have hshift : ∀ (X : T) (m : ℤ), P X → P (X⟦m⟧) := fun X m hX n =>
    (NatTrans.isIso_app_iff_of_iso θ ((shiftFunctorAdd' T m n (m + n) rfl).app X)).1 (hX _)
  have hP : P X := by
    refine prop_of_localizing' P hiso (fun n => ?_) hshift ?_ ?_ h X
    · have hz : IsZero ((0 : T)⟦n⟧) := (shiftFunctor T n).map_isZero (isZero_zero T)
      exact ⟨⟨(G.map_isZero hz).to_ _, (F.map_isZero hz).eq_of_src _ _,
        (G.map_isZero hz).eq_of_src _ _⟩⟩
    · intro Tr hTr h₁ h₃ n
      exact NatTrans.isIso_app_obj₂_of_homological hF hG θ _
        (Triangle.shift_distinguished Tr hTr n) (hshift _ n h₁ 1) (h₁ n) (h₃ n)
        (hshift _ n h₃ (-1))
    · intro J Y hY n
      refine (NatTrans.isIso_app_iff_of_iso θ
        (PreservesCoproduct.iso (shiftFunctor T n) Y)).2 ?_
      exact NatTrans.isIso_app_sigma_of_spanned hFc hGc θ _ fun j => hY j n
  exact (NatTrans.isIso_app_iff_of_iso θ ((shiftFunctorZero T ℤ).app X)).1 (hP 0)

/-- A natural transformation between additive cohomological functors sending coproducts to
products which is an isomorphism at every shifted generator `G i⟦n⟧` is an isomorphism. -/
theorem NatTrans.isIso_app_of_cohomological {F G : Tᵒᵖ ⥤ AddCommGrpCat.{v}} [F.Additive]
    [G.Additive] (hF : IsCohomological F) (hG : IsCohomological G)
    (hFc : SendsCoproductsToProducts F) (hGc : SendsCoproductsToProducts G) (θ : F ⟶ G)
    (h : ∀ (i : GenIndex T) (n : ℤ), IsIso (θ.app (op ((gen T i)⟦n⟧)))) (X : T) :
    IsIso (θ.app (op X)) := by
  let P : ObjectProperty T := fun X => ∀ n : ℤ, IsIso (θ.app (op (X⟦n⟧)))
  have hiso : ∀ {X Y : T}, (X ≅ Y) → P X → P Y := fun e hX n =>
    (NatTrans.isIso_app_iff_of_iso θ ((shiftFunctor T n).mapIso e).op).2 (hX n)
  have hshift : ∀ (X : T) (m : ℤ), P X → P (X⟦m⟧) := fun X m hX n =>
    (NatTrans.isIso_app_iff_of_iso θ ((shiftFunctorAdd' T m n (m + n) rfl).app X).op).2 (hX _)
  have hP : P X := by
    refine prop_of_localizing' P hiso (fun n => ?_) hshift ?_ ?_ h X
    · have hz : IsZero (op ((0 : T)⟦n⟧)) :=
        ((shiftFunctor T n).map_isZero (isZero_zero T)).op
      exact ⟨⟨(G.map_isZero hz).to_ _, (F.map_isZero hz).eq_of_src _ _,
        (G.map_isZero hz).eq_of_src _ _⟩⟩
    · intro Tr hTr h₁ h₃ n
      exact NatTrans.isIso_app_obj₂_of_cohomological hF hG θ _
        (Triangle.shift_distinguished Tr hTr n) (hshift _ n h₁ 1) (h₁ n) (h₃ n)
        (hshift _ n h₃ (-1))
    · intro J Y hY n
      refine (NatTrans.isIso_app_iff_of_iso θ
        (PreservesCoproduct.iso (shiftFunctor T n) Y).op).1 ?_
      exact NatTrans.isIso_app_sigma_of_sendsCoproductsToProducts hFc hGc θ _ fun j => hY j n
  exact (NatTrans.isIso_app_iff_of_iso θ ((shiftFunctorZero T ℤ).app X).op).2 (hP 0)

end RigidDescent
