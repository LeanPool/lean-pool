/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Complexes

/-!
# Comparing `K(Q₀)` with the derived category of `Rep k I`

The functor `G : K(Q₀) ⥤ D(Rep k I)` is `ι₀` on complexes followed by the localization. It is
bijective on morphisms into the resolution complexes (their images are K-injective), and
`G(resC l) ≅ l` in the derived category through the quasi-isomorphism `qmap l`. Lifting the
inclusion of the interval category into `D(Rep k I)` along `G` gives the functor `resFunctor`
which sends an interval to its resolution (Step 1 of the proof of Proposition 2.3).
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject DerivedCategory

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

attribute [local instance] HasDerivedCategory.standard

variable (k I) in
/-- The functor `G : K(Q₀) ⥤ D(Rep k I)`. -/
noncomputable def Gfun : HomotopyCategory (Q₀ k I) (ComplexShape.up ℤ) ⥤
    DerivedCategory (Rep k I) :=
  ι₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh

/-- The resolution of an interval as an object of `K(Q₀)`. -/
noncomputable abbrev resK (l : IntervalCat k I) : HomotopyCategory (Q₀ k I) (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient _ _).obj (resC l)

/-- `G(resC l) ≅ l` in the derived category. -/
noncomputable def eIso (l : IntervalCat k I) :
    (Gfun k I).obj (resK l) ≅ (singleFunctor (Rep k I) 0).obj (l.rep k) :=
  (quotientCompQhIso (Rep k I)).app (resRep l) ≪≫ (asIso (Q.map (qmap l))).symm

lemma Gfun_map_bijective (K : HomotopyCategory (Q₀ k I) (ComplexShape.up ℤ))
    (l : IntervalCat k I) :
    Function.Bijective ((Gfun k I).map : (K ⟶ resK l) → _) := by
  have h₁ : Function.Bijective ((ι₀.mapHomotopyCategory (ComplexShape.up ℤ)).map :
      (K ⟶ resK l) → _) :=
    ⟨(ι₀.mapHomotopyCategory _).map_injective, (ι₀.mapHomotopyCategory _).map_surjective⟩
  exact (CochainComplex.IsKInjective.Qh_map_bijective _ (resRep l)).comp h₁

/-- The lift of `l ↦ l` along `G`: the resolution functor on the interval category. -/
noncomputable def resFunctor : IntervalCat k I ⥤ HomotopyCategory (Q₀ k I) (ComplexShape.up ℤ) where
  obj := resK
  map {l l'} φ := Function.surjInv (Gfun_map_bijective (resK l) l').2
    ((eIso l).hom ≫ (singleFunctor (Rep k I) 0).map φ.hom ≫ (eIso l').inv)
  map_id l := by
    apply (Gfun_map_bijective (resK l) l).1
    rw [Function.surjInv_eq (Gfun_map_bijective (resK l) l).2, CategoryTheory.Functor.map_id]
    change _ ≫ (singleFunctor (Rep k I) 0).map (𝟙 _) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  map_comp {l l' l''} φ ψ := by
    apply (Gfun_map_bijective (resK l) l'').1
    rw [Function.surjInv_eq (Gfun_map_bijective (resK l) l'').2, Functor.map_comp,
      Function.surjInv_eq (Gfun_map_bijective (resK l) l').2,
      Function.surjInv_eq (Gfun_map_bijective (resK l') l'').2]
    change _ ≫ (singleFunctor (Rep k I) 0).map (φ.hom ≫ ψ.hom) ≫ _ = _
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

lemma Gfun_map_resFunctor {l l' : IntervalCat k I} (φ : l ⟶ l') :
    (Gfun k I).map (resFunctor.map φ) =
      (eIso l).hom ≫ (singleFunctor (Rep k I) 0).map φ.hom ≫ (eIso l').inv :=
  Function.surjInv_eq (Gfun_map_bijective (resK l) l').2 _

lemma Gfun_map_resFunctor_comp_eIso {l l' : IntervalCat k I} (φ : l ⟶ l') :
    (Gfun k I).map (resFunctor.map φ) ≫ (eIso l').hom =
      (eIso l).hom ≫ (singleFunctor (Rep k I) 0).map φ.hom := by
  exact ((Iso.comp_inv_eq _).mp ((Category.assoc _ _ _).trans (Gfun_map_resFunctor φ).symm)).symm

instance Gfun_additive : (Gfun k I).Additive := by
  unfold Gfun
  infer_instance

instance resFunctor_additive : (resFunctor (k := k) (I := I)).Additive where
  map_add {l l'} φ ψ := by
    apply (Gfun_map_bijective (resK l) l').1
    change (Gfun k I).map (resFunctor.map (φ + ψ)) =
      (Gfun k I).map (resFunctor.map φ + resFunctor.map ψ)
    rw [(Gfun k I).map_add, Gfun_map_resFunctor, Gfun_map_resFunctor, Gfun_map_resFunctor]
    change _ ≫ (singleFunctor (Rep k I) 0).map (φ.hom + ψ.hom) ≫ _ = _
    rw [(singleFunctor (Rep k I) 0).map_add, Preadditive.add_comp, Preadditive.comp_add]
    rfl

/-! ### The canonical maps `a_{ji}` on resolutions -/

lemma pQ_comp_cQ {i j : I} (h : i ≤ j) :
    (Mat_.embedding (IntervalCat k I)).map (show IntervalCat.objP (k := k) j ⟶
        IntervalCat.objP i from ⟨pMap h⟩) ≫
      (Mat_.embedding (IntervalCat k I)).map (show IntervalCat.objP (k := k) i ⟶
        IntervalCat.objY from ⟨cMap i⟩) =
    (Mat_.embedding (IntervalCat k I)).map (show IntervalCat.objP (k := k) j ⟶
        IntervalCat.objY from ⟨cMap j⟩) := by
  rw [← Functor.map_comp]
  congr 1
  exact InducedCategory.hom_ext (pMap_comp_cMap h)

/-- The chain map `(p_{ji}, 1_Y) : (P j → Y) ⟶ (P i → Y)` lifting `a_{ji}`. -/
noncomputable def aChain {i j : I} (h : i ≤ j) : resC (k := k) (A j) ⟶ resC (A i) :=
  HomologicalComplex.mkHomFromDouble rel01 (by lia)
    ((Mat_.embedding (IntervalCat k I)).map (show IntervalCat.objP (k := k) j ⟶
        IntervalCat.objP i from ⟨pMap h⟩) ≫
      (HomologicalComplex.doubleXIso₀ (resd (A i)) rel01).inv)
    (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).inv
    (by
      rw [HomologicalComplex.double_d _ _ (by lia), Category.assoc, Iso.inv_hom_id_assoc,
        ← Category.assoc]
      congr 1
      exact pQ_comp_cQ h)
    (by
      intro k' hk'
      rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by lia), comp_zero])

lemma qmap_comp_aChain {i j : I} (h : i ≤ j) :
    qmap (A j) ≫ (ι₀.mapHomologicalComplex _).map (aChain (k := k) h) =
      (HomologicalComplex.single (Rep k I) (ComplexShape.up ℤ) 0).map (aMap h) ≫ qmap (A i) := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, qmap_f₀, qmap_f₀,
    HomologicalComplex.single_map_f_self]
  change _ ≫ _ ≫ ι₀.map _ ≫ ι₀.map ((aChain h).f 0) = _
  rw [aChain, HomologicalComplex.mkHomFromDouble_f₀]
  simp only [Category.assoc, Functor.map_comp, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc ι₀ (HomologicalComplex.doubleXIso₀ (resd (A j)) rel01).inv,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  congr 1
  change (bMap j ≫ (ι₀Iso (P j)).inv) ≫ _ = aMap h ≫ (bMap i ≫ (ι₀Iso (P i)).inv) ≫ _
  rw [Category.assoc, ← Category.assoc (ι₀Iso (P j)).inv, ι₀Iso_inv_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (bMap j), ← Category.assoc (aMap h)]
  congr 1
  change bMap j ≫ pMap h = aMap h ≫ bMap i
  rw [aMap_comp_bMap, bMap_comp_pMap]

/-- `a_{ji}` as a morphism of the interval category. -/
noncomputable def aHom {i j : I} (h : i ≤ j) :
    IntervalCat.objA (k := k) j ⟶ IntervalCat.objA i := ⟨aMap h⟩

/-- The comparison isomorphism `G(K) ≅ Q(ι₀ K)` for a complex `K` over `Q₀`. -/
noncomputable def GQIso (K : CochainComplex (Q₀ k I) ℤ) :
    (Gfun k I).obj ((HomotopyCategory.quotient _ _).obj K) ≅
      Q.obj ((ι₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (quotientCompQhIso (Rep k I)).app _

lemma Gfun_map_quotient {K L : CochainComplex (Q₀ k I) ℤ} (f : K ⟶ L) :
    (Gfun k I).map ((HomotopyCategory.quotient _ _).map f) =
      (GQIso K).hom ≫ Q.map ((ι₀.mapHomologicalComplex _).map f) ≫ (GQIso L).inv := by
  rw [← cancel_mono (GQIso L).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  exact quotientCompQhIso_hom_naturality _

lemma eIso_hom (l : IntervalCat k I) :
    (eIso l).hom = (GQIso (resC l)).hom ≫ inv (Q.map (qmap l)) := rfl

lemma eIso_inv (l : IntervalCat k I) :
    (eIso l).inv = Q.map (qmap l) ≫ (GQIso (resC l)).inv := rfl

/-- A chain map between resolutions lifting `g` is sent by `G` to `g`. -/
lemma Gfun_map_quotient_of_comm {l l' : IntervalCat k I} (f : resC l ⟶ resC l')
    (g : l.rep k ⟶ l'.rep k)
    (h : qmap l ≫ (ι₀.mapHomologicalComplex _).map f =
      (HomologicalComplex.single (Rep k I) (ComplexShape.up ℤ) 0).map g ≫ qmap l') :
    (Gfun k I).map ((HomotopyCategory.quotient _ _).map f) =
      (eIso l).hom ≫ (singleFunctor (Rep k I) 0).map g ≫ (eIso l').inv := by
  rw [Gfun_map_quotient, eIso_hom, eIso_inv]
  simp only [Category.assoc]
  congr 1
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  rw [IsIso.eq_inv_comp, ← Functor.map_comp, h, Functor.map_comp]
  rfl

/-- `a_{ji}` goes to the class of `(p_{ji}, 1_Y)`. -/
lemma resFunctor_map_aMap {i j : I} (h : i ≤ j) :
    resFunctor.map (aHom (k := k) h) = (HomotopyCategory.quotient _ _).map (aChain h) := by
  apply (Gfun_map_bijective (resK (A j)) (A i)).1
  refine (Gfun_map_resFunctor _).trans ?_
  exact (Gfun_map_quotient_of_comm (aChain h) (aMap h) (qmap_comp_aChain h)).symm

end ExtriangulatedRealization
