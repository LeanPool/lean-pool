/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Shadow
public import LeanPool.ExtriangulatedRealization.Categories.MapBijective

/-!
# `Γ` is bijective on the morphisms computing extensions in `C_J`

For objects `C, A` of `C_J`, the shadow functor `Γ : K(Q) ⥤ D(Rep k I)` is bijective on
`K(Q)(F C, (F A)⟦1⟧)`. By additivity it suffices to treat indecomposables. Morphisms out of
`L[-1]` into `(F A)⟦1⟧`, and from the resolution of an interval into `L[-1]⟦1⟧ = L`, vanish for
degree reasons or because `Q(interval, L) = 0`; on both sides of `Γ` these sets are zero. Between
resolutions of intervals, `Γ` restricts to `G`, which is bijective since the shifted resolutions
are K-injective.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject DerivedCategory

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

attribute [local instance] HasDerivedCategory.standard

instance isKInjective_resRep_shift (l : IntervalCat k I) (n : ℤ) :
    CochainComplex.IsKInjective ((ι₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((resC l)⟦n⟧)) :=
  have : CochainComplex.IsKInjective ((resRep l)⟦n⟧) := inferInstance
  CochainComplex.isKInjective_of_iso (L₁ := (resRep l)⟦n⟧)
    (((ι₀.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).app (resC l)).symm

lemma map_bijective_of_subsingleton {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [Preadditive 𝒞]
    (H : 𝒞 ⥤ 𝒟) {X Y : 𝒞} [Subsingleton (X ⟶ Y)] (hY : Subsingleton (H.obj X ⟶ H.obj Y)) :
    Function.Bijective (H.map : (X ⟶ Y) → (H.obj X ⟶ H.obj Y)) :=
  ⟨fun a b _ => Subsingleton.elim a b, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

namespace RealizationData

variable {D : Iᵒᵖ ⥤ ModuleCat.{u} k} {J : Set I} (R : RealizationData D J)

lemma subsingleton_hom_Xc_shift {Z : CochainComplex R.Q ℤ} (hZ : IsZero (Z.X 2)) :
    Subsingleton ((HomotopyCategory.quotient _ _).obj R.Xc ⟶
      ((HomotopyCategory.quotient _ _).obj Z)⟦(1 : ℤ)⟧) := by
  let e := ((HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app Z
  suffices h : ∀ φ : (HomotopyCategory.quotient _ _).obj R.Xc ⟶
      (HomotopyCategory.quotient _ _).obj (Z⟦(1 : ℤ)⟧), φ = 0 by
    constructor
    intro f g
    rw [← cancel_mono e.inv, h (f ≫ e.inv), h (g ≫ e.inv)]
  intro φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
  have : φ = 0 := HomologicalComplex.from_single_hom_ext (IsZero.eq_of_tgt hZ _ _)
  rw [this, Functor.map_zero]

lemma eq_zero_of_e₀ {M : Q₀ k I} (f : R.e₀.obj M ⟶ R.Lobj) : f = 0 := by
  funext i j
  exact Subsingleton.elim (α := PUnit) _ _

lemma subsingleton_hom_resCQ_Xc_shift (l : IntervalCat k I) :
    Subsingleton ((HomotopyCategory.quotient _ _).obj (R.resCQ l) ⟶
      ((HomotopyCategory.quotient _ _).obj R.Xc)⟦(1 : ℤ)⟧) := by
  let e := ((HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app R.Xc
  suffices h : ∀ φ : (HomotopyCategory.quotient _ _).obj (R.resCQ l) ⟶
      (HomotopyCategory.quotient _ _).obj (R.Xc⟦(1 : ℤ)⟧), φ = 0 by
    constructor
    intro f g
    rw [← cancel_mono e.inv, h (f ≫ e.inv), h (g ≫ e.inv)]
  intro φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
  have : φ = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    by_cases hn : n = 0
    · subst hn
      let s := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1 R.Lobj
      have h0 : φ.f 0 ≫ s.hom = 0 := R.eq_zero_of_e₀ _
      rw [HomologicalComplex.zero_f]
      exact (cancel_mono s.hom).mp (h0.trans zero_comp.symm)
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 1 R.Lobj _
        (by lia)).eq_of_tgt _ _
  rw [this, Functor.map_zero]

variable (hR : R.IsCompatible)

lemma shadow_bijective_F₁ (x y : IndJ J D) :
    Function.Bijective (R.shadow.map : ((R.F₁ hR).obj x ⟶ ((R.F₁ hR).obj y)⟦(1 : ℤ)⟧) → _) := by
  rcases x with _ | a
  · have hs : Subsingleton (R.shadow.obj ((R.F₁ hR).obj none) ⟶
        R.shadow.obj (((R.F₁ hR).obj y)⟦(1 : ℤ)⟧)) :=
      ⟨fun _ _ => R.isZero_shadow_Xc.eq_of_src _ _⟩
    rcases y with _ | b
    · exact @map_bijective_of_subsingleton _ _ _ _ _ R.shadow _ _
        (R.subsingleton_hom_Xc_shift (Z := R.Xc)
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia))) hs
    · exact @map_bijective_of_subsingleton _ _ _ _ _ R.shadow _ _
        (R.subsingleton_hom_Xc_shift (Z := R.resCQ b.obj)
          (R.e₀.map_isZero (HomologicalComplex.isZero_double_X _ _ 2 (by lia) (by lia)))) hs
  rcases y with _ | b
  · have hz : IsZero (R.shadow.obj (((R.F₁ hR).obj none)⟦(1 : ℤ)⟧)) :=
      IsZero.of_iso ((shiftFunctor _ (1 : ℤ)).map_isZero R.isZero_shadow_Xc)
        ((R.shadow.commShiftIso (1 : ℤ)).app _)
    exact @map_bijective_of_subsingleton _ _ _ _ _ R.shadow _ _
      (R.subsingleton_hom_resCQ_Xc_shift a.obj) ⟨fun _ _ => hz.eq_of_tgt _ _⟩
  · let X : HomotopyCategory (Q₀ k I) (ComplexShape.up ℤ) := resK a.obj
    let L := (resC (k := k) b.obj)⟦(1 : ℤ)⟧
    let e₀K := R.e₀.mapHomotopyCategory (ComplexShape.up ℤ)
    let e' : (e₀K.obj (resK b.obj))⟦(1 : ℤ)⟧ ≅ e₀K.obj ((HomotopyCategory.quotient _ _).obj L) :=
      ((e₀K.commShiftIso (1 : ℤ)).app (resK b.obj)).symm ≪≫
        e₀K.mapIso (((HomotopyCategory.quotient _ _).commShiftIso (1 : ℤ)).app (resC b.obj)).symm
    refine map_bijective_of_iso R.shadow (Iso.refl (e₀K.obj X)) e' ?_
    have he : Function.Bijective (e₀K.map : (X ⟶ (HomotopyCategory.quotient _ _).obj L) → _) :=
      ⟨e₀K.map_injective, e₀K.map_surjective⟩
    refine (Function.Bijective.of_comp_iff _ he).mp ?_
    have hcomp : R.shadow.map ∘ (e₀K.map : (X ⟶ (HomotopyCategory.quotient _ _).obj L) → _) =
        (Gfun k I).map := funext fun φ => R.e₀_comp_shadow_map φ
    rw [hcomp]
    exact @Gfun_map_bijective_of_isKInjective _ _ _ _ X L (isKInjective_resRep_shift b.obj 1)

/-- `Γ` is bijective on `K(Q)(F C, (F A)⟦1⟧)` for `C, A ∈ C_J`. -/
lemma shadow_bijective_realF (C A : CDJ J D) :
    Function.Bijective (R.shadow.map : ((R.realF hR).obj C ⟶ ((R.realF hR).obj A)⟦(1 : ℤ)⟧) →
      _) :=
  map_bijective_of_iso R.shadow (Iso.refl _)
    ((shiftFunctor _ (1 : ℤ)).mapBiproduct (fun j => (R.F₁ hR).obj (A.X j)))
    (map_bijective_biproduct R.shadow _ _ fun _ _ => R.shadow_bijective_F₁ hR _ _)

end RealizationData

end ExtriangulatedRealization
