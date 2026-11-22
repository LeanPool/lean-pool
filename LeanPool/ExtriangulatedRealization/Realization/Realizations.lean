/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Triangles
public import LeanPool.ExtriangulatedRealization.Categories.Biproduct
public import LeanPool.ExtriangulatedRealization.Intervals.Ext

/-!
# Realizations go to distinguished triangles: splitting off the `X`-parts

A realization `A → B → C` of `δ` in `C_J` decomposes, through `B ≅ N ⊞ (X_A ⊞ X_C)`, as the
direct sum of the realization `A_B → N → C_B` between interval parts and the split sequence
`X_A → X_A ⊞ X_C → X_C`. The first goes to a distinguished triangle by the `X`-free case, the
second to a split triangle, and the image of the realization is isomorphic to their direct sum.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject DerivedCategory
  Pretriangulated

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

attribute [local instance] HasDerivedCategory.standard HasExt.standard

variable {D : Iᵒᵖ ⥤ ModuleCat.{u} k} {J : Set I}

/-! ### Interval and `X`-parts in `C_J` -/

/-- The interval part of an object of `C_J`. -/
abbrev bPartJ (M : (labelsIn D J).FullSubcategory) : (labelsIn D J).FullSubcategory :=
  ⟨bPart D M.obj, labelIn_bPart D M.property⟩

/-- The `X`-part of an object of `C_J`. -/
abbrev xPartJ (M : (labelsIn D J).FullSubcategory) : (labelsIn D J).FullSubcategory :=
  ⟨xPart D M.obj, fun i => M.property i.1⟩

namespace RealizationData

variable (R : RealizationData D J) (hR : R.IsCompatible)

/-- The realization functor on morphisms of `C(D)` between objects of `C_J`. -/
noncomputable def realMap {M N : (labelsIn D J).FullSubcategory} (f : M.obj ⟶ N.obj) :
    (R.realP hR).obj M ⟶ (R.realP hR).obj N :=
  (R.realP hR).map (ObjectProperty.homMk f)

lemma realMap_comp {M N L : (labelsIn D J).FullSubcategory} (f : M.obj ⟶ N.obj)
    (g : N.obj ⟶ L.obj) : R.realMap hR (f ≫ g) = R.realMap hR f ≫ R.realMap hR g :=
  (R.realP hR).map_comp (ObjectProperty.homMk f) (ObjectProperty.homMk g)

lemma realMap_comp_eq {M N L : (labelsIn D J).FullSubcategory} {f : M.obj ⟶ N.obj}
    {g : N.obj ⟶ L.obj} {h : M.obj ⟶ L.obj} (e : f ≫ g = h) :
    R.realMap hR f ≫ R.realMap hR g = R.realMap hR h := by
  rw [← e, R.realMap_comp hR]

lemma realMap_comp₃_eq {M N L K : (labelsIn D J).FullSubcategory} {f : M.obj ⟶ N.obj}
    {g : N.obj ⟶ L.obj} {g' : L.obj ⟶ K.obj} {h : M.obj ⟶ K.obj} (e : f ≫ g ≫ g' = h) :
    R.realMap hR f ≫ R.realMap hR g ≫ R.realMap hR g' = R.realMap hR h := by
  rw [← e, R.realMap_comp hR, R.realMap_comp hR]

lemma realMap_id (M : (labelsIn D J).FullSubcategory) : R.realMap hR (𝟙 M.obj) = 𝟙 _ :=
  (R.realP hR).map_id M

lemma realMap_homMk {M N : (labelsIn D J).FullSubcategory} (f : M.obj ⟶ N.obj) :
    (R.realP hR).map (ObjectProperty.homMk f) = R.realMap hR f := rfl

lemma realMap_hom {M N : (labelsIn D J).FullSubcategory} (f : M ⟶ N) :
    (R.realP hR).map f = R.realMap hR f.hom := rfl

lemma realMap_add {M N : (labelsIn D J).FullSubcategory} (f g : M.obj ⟶ N.obj) :
    R.realMap hR (f + g) = R.realMap hR f + R.realMap hR g :=
  (R.realP hR).map_add (f := ObjectProperty.homMk f) (g := ObjectProperty.homMk g)

lemma realMap_zero (M N : (labelsIn D J).FullSubcategory) :
    R.realMap hR (0 : M.obj ⟶ N.obj) = 0 :=
  (R.realP hR).map_zero M N

/-- The interval part of a realization goes to a distinguished triangle. -/
lemma bPart_realTriangle_distinguished {A B C : (labelsIn D J).FullSubcategory} {x : A ⟶ B}
    {y : B ⟶ C} {δ : (dataJ (D := D) (J := J)).Ext C A} (w : x.hom ≫ y.hom = 0)
    (hS : (ShortComplex.mk ((rho D).map x.hom) ((rho D).map y.hom)
      (by rw [← Functor.map_comp, w, Functor.map_zero])).ShortExact) (hcls : hS.extClass = δ)
    {N : CD D} (hN : XFree D N) (hNP : labelsIn D J N)
    (θ : B.obj ≅ N ⊞ (xPart D A.obj ⊞ xPart D C.obj)) (x' : A.obj ⟶ N) (y' : N ⟶ C.obj)
    (h2 : x.hom ≫ θ.hom = biprod.lift x' (biprod.lift (xProj D A.obj) 0))
    (h3 : θ.hom ≫ biprod.desc y' (biprod.desc 0 (xIncl D C.obj)) = y.hom) :
    R.realTriangle hR (A := bPartJ A) (B := ⟨N, hNP⟩) (C := bPartJ C)
      (ObjectProperty.homMk (bIncl D A.obj ≫ x')) (ObjectProperty.homMk (y' ≫ bProj D C.obj))
      ((dataJ (D := D) (J := J)).pull (ObjectProperty.homMk (bIncl D C.obj))
        ((dataJ (D := D) (J := J)).push (ObjectProperty.homMk (bProj D A.obj)) δ)) ∈
      distTriang _ := by
  have hx : x.hom = biprod.lift x' (biprod.lift (xProj D A.obj) 0) ≫ θ.inv := by
    rw [← h2, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hx'y' : x' ≫ y' = 0 := by
    have h := w
    rw [hx, ← h3, Category.assoc, Iso.inv_hom_id_assoc, biprod.lift_desc, biprod.lift_desc] at h
    simpa using h
  have hy'x : y' ≫ xProj D C.obj = 0 := hom_xFree_xPart_eq_zero D hN _
  have hρ : ∀ (f : B.obj ⟶ B.obj), f = θ.hom ≫ biprod.snd ≫ biprod.inr ≫ θ.inv →
      (rho D).map f = 0 := by
    rintro f rfl
    rw [Functor.map_comp, Functor.map_comp,
      (isZero_rho_biprod_xParts D A.obj C.obj).eq_of_src ((rho D).map (biprod.inr ≫ θ.inv)) 0]
    · simp
  have w₁ : (bIncl D A.obj ≫ x') ≫ (y' ≫ bProj D C.obj) = 0 := by
    rw [Category.assoc, ← Category.assoc x', hx'y', zero_comp, comp_zero]
  let e₂ : (rho D).obj N ≅ (rho D).obj B.obj :=
    { hom := (rho D).map (biprod.inl ≫ θ.inv)
      inv := (rho D).map (θ.hom ≫ biprod.fst)
      hom_inv_id := by
        rw [← Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_fst,
          CategoryTheory.Functor.map_id]
      inv_hom_id := by
        rw [← Functor.map_comp]
        have : θ.hom ≫ biprod.fst ≫ biprod.inl ≫ θ.inv =
            𝟙 B.obj - θ.hom ≫ biprod.snd ≫ biprod.inr ≫ θ.inv := by
          rw [eq_sub_iff_add_eq, ← Preadditive.comp_add, ← Category.assoc biprod.fst,
            ← Category.assoc biprod.snd, ← Preadditive.add_comp, biprod.total, Category.id_comp,
            Iso.hom_inv_id]
        rw [Category.assoc, this, Functor.map_sub, CategoryTheory.Functor.map_id, hρ _ rfl,
          sub_zero] }
  let e : ShortComplex.mk ((rho D).map (bIncl D A.obj ≫ x')) ((rho D).map (y' ≫ bProj D C.obj))
      (by rw [← Functor.map_comp, w₁, Functor.map_zero]) ≅
      ShortComplex.mk ((rho D).map x.hom) ((rho D).map y.hom)
        (by rw [← Functor.map_comp, w, Functor.map_zero]) :=
    ShortComplex.isoMk (rhoBPartIso D A.obj) e₂ (rhoBPartIso D C.obj)
      (by
        dsimp [e₂, rhoBPartIso]
        rw [← Functor.map_comp, ← Functor.map_comp, hx]
        congr 1
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        apply biprod.hom_ext
        · simp
        · simp [biprod.lift_eq, ← Category.assoc, bIncl_xProj])
      (by
        dsimp [e₂, rhoBPartIso]
        rw [← Functor.map_comp, ← Functor.map_comp, ← h3, Category.assoc, Iso.inv_hom_id_assoc,
          biprod.inl_desc, Category.assoc]
        have : bProj D C.obj ≫ bIncl D C.obj = 𝟙 _ - xProj D C.obj ≫ xIncl D C.obj := by
          rw [eq_sub_iff_add_eq, bProj_bIncl_add]
        rw [this, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hy'x, zero_comp,
          sub_zero])
  have hS₁ := ShortComplex.shortExact_of_iso e.symm hS
  refine R.realTriangle_distinguished_of_xFree hR _ _ _ (xFree_bPart D _) hN (xFree_bPart D _)
    (R.shadow_realTriangle_distinguished hR w₁ hS₁ ?_)
  have hnat := hS₁.extClass_naturality hS e.hom
  change hS₁.extClass.comp (Abelian.Ext.mk₀ ((rho D).map (bIncl D A.obj))) (add_zero 1) =
    (Abelian.Ext.mk₀ ((rho D).map (bIncl D C.obj))).comp hS.extClass (zero_add 1) at hnat
  change hS₁.extClass = (Abelian.Ext.mk₀ ((rho D).map (bIncl D C.obj))).comp
    ((δ : Abelian.Ext.{u + 1} ((rho D).obj C.obj) ((rho D).obj A.obj) 1).comp
      (Abelian.Ext.mk₀ ((rho D).map (bProj D A.obj))) (add_zero 1)) (zero_add 1)
  calc hS₁.extClass
      = hS₁.extClass.comp (Abelian.Ext.mk₀ ((rho D).map (bIncl D A.obj) ≫
          (rho D).map (bProj D A.obj))) (add_zero 1) := by
        rw [show (rho D).map (bIncl D A.obj) ≫ (rho D).map (bProj D A.obj) = 𝟙 _ by
          rw [← Functor.map_comp, bIncl_bProj, CategoryTheory.Functor.map_id],
          Abelian.Ext.comp_mk₀_id]
    _ = (hS₁.extClass.comp (Abelian.Ext.mk₀ ((rho D).map (bIncl D A.obj))) (add_zero 1)).comp
          (Abelian.Ext.mk₀ ((rho D).map (bProj D A.obj))) (add_zero 1) := by
        rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
    _ = _ := by
        rw [hnat, hcls]
        exact Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _

/-- An object of `C_J` goes to the direct sum of the images of its interval and `X`-parts. -/
noncomputable def splitIso (M : (labelsIn D J).FullSubcategory) :
    (R.realP hR).obj M ≅ (R.realP hR).obj (bPartJ M) ⊞ (R.realP hR).obj (xPartJ M) :=
  isoBiprodOfTotal (R.realMap hR (M := bPartJ M) (N := M) (bIncl D M.obj))
    (R.realMap hR (M := xPartJ M) (N := M) (xIncl D M.obj))
    (R.realMap hR (M := M) (N := bPartJ M) (bProj D M.obj))
    (R.realMap hR (M := M) (N := xPartJ M) (xProj D M.obj))
    ((R.realMap_comp hR _ _).symm.trans
      ((congrArg (R.realMap hR) (bIncl_bProj D _)).trans (R.realMap_id hR _)))
    ((R.realMap_comp hR _ _).symm.trans
      ((congrArg (R.realMap hR) (xIncl_xProj D _)).trans (R.realMap_id hR _)))
    ((R.realMap_comp hR _ _).symm.trans
      ((congrArg (R.realMap hR) (bIncl_xProj D _)).trans (R.realMap_zero hR _ _)))
    ((R.realMap_comp hR _ _).symm.trans
      ((congrArg (R.realMap hR) (xIncl_bProj D _)).trans (R.realMap_zero hR _ _)))
    ((congrArg₂ (· + ·) (R.realMap_comp hR _ _).symm (R.realMap_comp hR _ _).symm).trans
      ((R.realMap_add hR _ _).symm.trans
        ((congrArg (R.realMap hR) (bProj_bIncl_add D _)).trans (R.realMap_id hR _))))

omit [Field k] [LinearOrder I] in
lemma biprod_total₃ {𝒯 : Type*} [Category 𝒯] [Preadditive 𝒯] [HasBinaryBiproducts 𝒯]
    {Z N X Y : 𝒯} (θ : Z ≅ N ⊞ (X ⊞ Y)) :
    θ.hom ≫ biprod.fst ≫ biprod.inl ≫ θ.inv +
      (θ.hom ≫ biprod.snd ≫ biprod.fst ≫ biprod.inl ≫ biprod.inr ≫ θ.inv +
        θ.hom ≫ biprod.snd ≫ biprod.snd ≫ biprod.inr ≫ biprod.inr ≫ θ.inv) = 𝟙 Z := by
  have h : biprod.fst ≫ (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.inr +
      biprod.snd ≫ (biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.inr =
      (biprod.inr : X ⊞ Y ⟶ N ⊞ (X ⊞ Y)) := by
    rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, biprod.total,
      Category.id_comp]
  calc _ = θ.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫
        (biprod.fst ≫ biprod.inl ≫ biprod.inr + biprod.snd ≫ biprod.inr ≫ biprod.inr)) ≫
          θ.inv := by
        simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    _ = 𝟙 Z := by rw [h, biprod.total, Category.id_comp, Iso.hom_inv_id]

/-- The middle term of a realization goes to the direct sum of the images of the interval part
`N` and the two `X`-parts. -/
noncomputable def splitIsoMid {A B C : (labelsIn D J).FullSubcategory} {N : CD D}
    (hNP : labelsIn D J N) (θ : B.obj ≅ N ⊞ (xPart D A.obj ⊞ xPart D C.obj)) :
    (R.realP hR).obj B ≅ (R.realP hR).obj ⟨N, hNP⟩ ⊞
      ((R.realP hR).obj (xPartJ A) ⊞ (R.realP hR).obj (xPartJ C)) :=
  isoBiprodOfTotal
    (R.realMap hR (M := ⟨N, hNP⟩) (N := B) (biprod.inl ≫ θ.inv))
    (biprod.desc (R.realMap hR (M := xPartJ A) (N := B) (biprod.inl ≫ biprod.inr ≫ θ.inv))
      (R.realMap hR (M := xPartJ C) (N := B) (biprod.inr ≫ biprod.inr ≫ θ.inv)))
    (R.realMap hR (M := B) (N := ⟨N, hNP⟩) (θ.hom ≫ biprod.fst))
    (biprod.lift (R.realMap hR (M := B) (N := xPartJ A) (θ.hom ≫ biprod.snd ≫ biprod.fst))
      (R.realMap hR (M := B) (N := xPartJ C) (θ.hom ≫ biprod.snd ≫ biprod.snd)))
    ((R.realMap_comp_eq hR (h := 𝟙 _) (by simp)).trans (R.realMap_id hR _))
    (by
      apply biprod.hom_ext' <;> apply biprod.hom_ext
      · simp only [biprod.inl_desc_assoc, Category.assoc, biprod.lift_fst, Category.id_comp,
          biprod.inl_fst]
        exact (R.realMap_comp_eq hR (h := 𝟙 _) (by simp)).trans (R.realMap_id hR _)
      · simp only [biprod.inl_desc_assoc, Category.assoc, biprod.lift_snd, Category.id_comp,
          biprod.inl_snd]
        exact (R.realMap_comp_eq hR (h := 0) (by simp)).trans (R.realMap_zero hR _ _)
      · simp only [biprod.inr_desc_assoc, Category.assoc, biprod.lift_fst, Category.id_comp,
          biprod.inr_fst]
        exact (R.realMap_comp_eq hR (h := 0) (by simp)).trans (R.realMap_zero hR _ _)
      · simp only [biprod.inr_desc_assoc, Category.assoc, biprod.lift_snd, Category.id_comp,
          biprod.inr_snd]
        exact (R.realMap_comp_eq hR (h := 𝟙 _) (by simp)).trans (R.realMap_id hR _))
    (by
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.lift_fst, zero_comp]
        exact (R.realMap_comp_eq hR (h := 0) (by simp)).trans (R.realMap_zero hR _ _)
      · simp only [Category.assoc, biprod.lift_snd, zero_comp]
        exact (R.realMap_comp_eq hR (h := 0) (by simp)).trans (R.realMap_zero hR _ _))
    (by
      apply biprod.hom_ext'
      · simp only [biprod.inl_desc_assoc, comp_zero]
        exact (R.realMap_comp_eq hR (h := 0) (by simp)).trans (R.realMap_zero hR _ _)
      · simp only [biprod.inr_desc_assoc, comp_zero]
        exact (R.realMap_comp_eq hR (h := 0) (by simp)).trans (R.realMap_zero hR _ _))
    (by
      rw [biprod.lift_desc, R.realMap_comp_eq hR rfl, R.realMap_comp_eq hR rfl,
        R.realMap_comp_eq hR rfl, ← R.realMap_add, ← R.realMap_add]
      exact (congrArg (R.realMap hR) (by simpa only [Category.assoc] using biprod_total₃ θ)).trans
        (R.realMap_id hR _))

lemma eta_eq_zero_of_isZero_left {M A : (labelsIn D J).FullSubcategory}
    (hM : IsZero ((rho D).obj M.obj)) (δ : (dataJ (D := D) (J := J)).Ext M A) :
    R.eta hR M A δ = 0 := by
  rw [show δ = 0 from ExtriangulatedRealization.Ext.eq_zero_of_isZero_source hM δ, map_zero]

lemma eta_eq_zero_of_isZero_right {M A : (labelsIn D J).FullSubcategory}
    (hA : IsZero ((rho D).obj A.obj)) (δ : (dataJ (D := D) (J := J)).Ext M A) :
    R.eta hR M A δ = 0 := by
  rw [show δ = 0 from ExtriangulatedRealization.Ext.eq_zero_of_isZero_target hA δ, map_zero]

omit R hR in
lemma dataJ_push_pull {C'' C A A' : (labelsIn D J).FullSubcategory} (c : C'' ⟶ C) (a : A ⟶ A')
    (δ : (dataJ (D := D) (J := J)).Ext C A) :
    (dataJ (D := D) (J := J)).push a ((dataJ (D := D) (J := J)).pull c δ) =
      (dataJ (D := D) (J := J)).pull c ((dataJ (D := D) (J := J)).push a δ) := by
  change ((Abelian.Ext.mk₀ ((rho D).map c.hom)).comp
      (δ : Abelian.Ext.{u + 1} ((rho D).obj C.obj) ((rho D).obj A.obj) 1) (zero_add 1)).comp
      (Abelian.Ext.mk₀ ((rho D).map a.hom)) (add_zero 1) =
    (Abelian.Ext.mk₀ ((rho D).map c.hom)).comp
      ((δ : Abelian.Ext.{u + 1} ((rho D).obj C.obj) ((rho D).obj A.obj) 1).comp
        (Abelian.Ext.mk₀ ((rho D).map a.hom)) (add_zero 1)) (zero_add 1)
  exact Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _

private lemma splitIso_comm_mor₁ {A B C : (labelsIn D J).FullSubcategory} {N : CD D}
    (hNP : labelsIn D J N) (θ : B.obj ≅ N ⊞ (xPart D A.obj ⊞ xPart D C.obj))
    (x : A ⟶ B) (x' : A.obj ⟶ N) (h1 : xIncl D A.obj ≫ x' = 0)
    (h2 : x.hom ≫ θ.hom = biprod.lift x' (biprod.lift (xProj D A.obj) 0)) :
    R.realMap hR x.hom ≫ (R.splitIsoMid hR hNP θ).hom =
      (R.splitIso hR A).hom ≫ biprod.map
        (R.realMap hR (M := bPartJ A) (N := ⟨N, hNP⟩) (bIncl D A.obj ≫ x')) biprod.inl := by
  let N' : (labelsIn D J).FullSubcategory := ⟨N, hNP⟩
  change R.realMap hR x.hom ≫ biprod.lift (R.realMap hR (M := B) (N := N') (θ.hom ≫ biprod.fst))
      (biprod.lift (R.realMap hR (M := B) (N := xPartJ A) (θ.hom ≫ biprod.snd ≫ biprod.fst))
        (R.realMap hR (M := B) (N := xPartJ C) (θ.hom ≫ biprod.snd ≫ biprod.snd))) =
    biprod.lift (R.realMap hR (M := A) (N := bPartJ A) (bProj D A.obj))
      (R.realMap hR (M := A) (N := xPartJ A) (xProj D A.obj)) ≫
      biprod.map (R.realMap hR (M := bPartJ A) (N := N') (bIncl D A.obj ≫ x')) biprod.inl
  have hx : x.hom ≫ θ.hom = biprod.lift x' (biprod.lift (xProj D A.obj) 0) := h2
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
    have e₁ := R.realMap_comp_eq hR (M := A) (N := B) (L := N') (f := x.hom)
      (g := θ.hom ≫ biprod.fst) (h := x')
      (by rw [← Category.assoc, hx]; exact biprod.lift_fst _ _)
    have e₂ := R.realMap_comp_eq hR (M := A) (N := bPartJ A) (L := N') (f := bProj D A.obj)
      (g := bIncl D A.obj ≫ x') (h := x') ?_
    · exact e₁.trans e₂.symm
    rw [← Category.assoc, show bProj D A.obj ≫ bIncl D A.obj =
        𝟙 _ - xProj D A.obj ≫ xIncl D A.obj by rw [eq_sub_iff_add_eq, bProj_bIncl_add],
      Preadditive.sub_comp, Category.id_comp, Category.assoc]
    erw [h1, comp_zero, sub_zero]
  · apply biprod.hom_ext
    · rw [Category.assoc, Category.assoc, biprod.lift_snd_assoc, biprod.lift_fst,
        Category.assoc, Category.assoc, biprod.map_snd_assoc, biprod.lift_snd_assoc,
        biprod.inl_fst, Category.comp_id]
      exact R.realMap_comp_eq hR (by
        rw [← Category.assoc, hx]
        erw [biprod.lift_snd_assoc, biprod.lift_fst])
    · rw [Category.assoc, Category.assoc, biprod.lift_snd_assoc, biprod.lift_snd,
        Category.assoc, Category.assoc, biprod.map_snd_assoc, biprod.inl_snd, comp_zero]
      exact (R.realMap_comp_eq hR (h := 0) (by
        rw [← Category.assoc, hx]
        erw [biprod.lift_snd_assoc, biprod.lift_snd])).trans
        ((R.realMap_zero hR _ _).trans comp_zero.symm)

private lemma splitIso_comm_mor₂ {A B C : (labelsIn D J).FullSubcategory} {N : CD D}
    (hNP : labelsIn D J N) (θ : B.obj ≅ N ⊞ (xPart D A.obj ⊞ xPart D C.obj))
    (y : B ⟶ C) (y' : N ⟶ C.obj) (hy'x : y' ≫ xProj D C.obj = 0)
    (h3 : θ.hom ≫ biprod.desc y' (biprod.desc 0 (xIncl D C.obj)) = y.hom) :
    R.realMap hR y.hom ≫ (R.splitIso hR C).hom =
      (R.splitIsoMid hR hNP θ).hom ≫ biprod.map
        (R.realMap hR (M := ⟨N, hNP⟩) (N := bPartJ C) (y' ≫ bProj D C.obj)) biprod.snd := by
  let N' : (labelsIn D J).FullSubcategory := ⟨N, hNP⟩
  have hyN : biprod.inl ≫ θ.inv ≫ y.hom = y' := by
    rw [← h3, Iso.inv_hom_id_assoc, biprod.inl_desc]
  have hyA : biprod.inl ≫ biprod.inr ≫ θ.inv ≫ y.hom = 0 := by
    rw [← h3, Iso.inv_hom_id_assoc, biprod.inr_desc, biprod.inl_desc]
  have hyC : biprod.inr ≫ biprod.inr ≫ θ.inv ≫ y.hom = xIncl D C.obj := by
    rw [← h3, Iso.inv_hom_id_assoc, biprod.inr_desc, biprod.inr_desc]
  refine (cancel_epi (R.splitIsoMid hR hNP θ).inv).mp ?_
  erw [Iso.inv_hom_id_assoc]
  change biprod.desc (R.realMap hR (M := N') (N := B) (biprod.inl ≫ θ.inv))
      (biprod.desc (R.realMap hR (M := xPartJ A) (N := B) (biprod.inl ≫ biprod.inr ≫ θ.inv))
        (R.realMap hR (M := xPartJ C) (N := B) (biprod.inr ≫ biprod.inr ≫ θ.inv))) ≫
      R.realMap hR y.hom ≫ biprod.lift (R.realMap hR (M := C) (N := bPartJ C) (bProj D C.obj))
        (R.realMap hR (M := C) (N := xPartJ C) (xProj D C.obj)) =
    biprod.map (R.realMap hR (M := N') (N := bPartJ C) (y' ≫ bProj D C.obj)) biprod.snd
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, biprod.inl_map]
    apply biprod.hom_ext
    · rw [Category.assoc, Category.assoc, biprod.lift_fst, Category.assoc, biprod.inl_fst,
        Category.comp_id]
      exact R.realMap_comp₃_eq hR (M := N') (N := B) (L := C) (K := bPartJ C)
        (h := y' ≫ bProj D C.obj)
        (by
          have e := (reassoc_of% hyN) (bProj D C.obj)
          exact (Category.assoc _ _ _).trans e)
    · rw [Category.assoc, Category.assoc, biprod.lift_snd, Category.assoc, biprod.inl_snd,
        comp_zero]
      exact (R.realMap_comp₃_eq hR (M := N') (N := B) (L := C) (K := xPartJ C) (h := 0)
        (by
          have e := (reassoc_of% hyN) (xProj D C.obj)
          exact (Category.assoc _ _ _).trans (e.trans hy'x))).trans
        (R.realMap_zero hR _ _)
  · rw [biprod.inr_desc_assoc, biprod.inr_map]
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, biprod.inl_snd_assoc, zero_comp]
      apply biprod.hom_ext
      · rw [Category.assoc, Category.assoc, biprod.lift_fst, zero_comp]
        refine (R.realMap_comp₃_eq hR (M := xPartJ A) (N := B) (L := C) (K := bPartJ C)
          (h := 0) ?_).trans (R.realMap_zero hR _ _)
        have e := (reassoc_of% hyA) (bProj D C.obj)
        simp only [Category.assoc, zero_comp] at e ⊢
        exact e
      · rw [Category.assoc, Category.assoc, biprod.lift_snd, zero_comp]
        refine (R.realMap_comp₃_eq hR (M := xPartJ A) (N := B) (L := C) (K := xPartJ C)
          (h := 0) ?_).trans (R.realMap_zero hR _ _)
        have e := (reassoc_of% hyA) (xProj D C.obj)
        simp only [Category.assoc, zero_comp] at e ⊢
        exact e
    · rw [biprod.inr_desc_assoc, biprod.inr_snd_assoc]
      apply biprod.hom_ext
      · rw [Category.assoc, Category.assoc, biprod.lift_fst, biprod.inr_fst]
        refine (R.realMap_comp₃_eq hR (M := xPartJ C) (N := B) (L := C) (K := bPartJ C)
          (h := 0) ?_).trans (R.realMap_zero hR _ _)
        have e := (reassoc_of% hyC) (bProj D C.obj)
        simp only [Category.assoc] at e ⊢
        exact e.trans (xIncl_bProj D _)
      · rw [Category.assoc, Category.assoc, biprod.lift_snd, biprod.inr_snd]
        refine (R.realMap_comp₃_eq hR (M := xPartJ C) (N := B) (L := C) (K := xPartJ C)
          (h := 𝟙 _) ?_).trans (R.realMap_id hR _)
        have e := (reassoc_of% hyC) (xProj D C.obj)
        simp only [Category.assoc] at e ⊢
        exact e.trans (xIncl_xProj D _)

private lemma splitIso_comm_mor₃ {A C : (labelsIn D J).FullSubcategory}
    (δ : (dataJ (D := D) (J := J)).Ext C A) :
    R.eta hR C A δ ≫ (R.splitIso hR A).hom⟦(1 : ℤ)⟧' =
      (R.splitIso hR C).hom ≫ biprod.desc
        (R.eta hR (bPartJ C) (bPartJ A) ((dataJ (D := D) (J := J)).pull
          (ObjectProperty.homMk (bIncl D C.obj))
          ((dataJ (D := D) (J := J)).push (ObjectProperty.homMk (bProj D A.obj)) δ)) ≫
          biprod.inl⟦(1 : ℤ)⟧')
        (0 ≫ biprod.inr⟦(1 : ℤ)⟧') := by
  refine (cancel_epi (R.splitIso hR C).inv).mp ?_
  erw [Iso.inv_hom_id_assoc]
  change biprod.desc (R.realMap hR (M := bPartJ C) (N := C) (bIncl D C.obj))
      (R.realMap hR (M := xPartJ C) (N := C) (xIncl D C.obj)) ≫ R.eta hR C A δ ≫
        (biprod.lift (R.realMap hR (M := A) (N := bPartJ A) (bProj D A.obj))
          (R.realMap hR (M := A) (N := xPartJ A) (xProj D A.obj)))⟦(1 : ℤ)⟧' =
    biprod.desc (R.eta hR (bPartJ C) (bPartJ A) ((dataJ (D := D) (J := J)).pull
        (ObjectProperty.homMk (bIncl D C.obj))
        ((dataJ (D := D) (J := J)).push (ObjectProperty.homMk (bProj D A.obj)) δ)) ≫
        (biprod.inl : (R.realP hR).obj (bPartJ A) ⟶ _ ⊞ (R.realP hR).obj (xPartJ A))⟦(1 : ℤ)⟧')
      ((0 : (R.realP hR).obj (xPartJ C) ⟶ ((R.realP hR).obj (xPartJ A))⟦(1 : ℤ)⟧) ≫
        (biprod.inr : (R.realP hR).obj (xPartJ A) ⟶ (R.realP hR).obj (bPartJ A) ⊞ _)⟦(1 : ℤ)⟧')
  have hpull : ∀ {M : (labelsIn D J).FullSubcategory} (c : M.obj ⟶ C.obj),
      R.realMap hR c ≫ R.eta hR C A δ =
        R.eta hR M A ((dataJ (D := D) (J := J)).pull (ObjectProperty.homMk c) δ) :=
    fun c => (R.eta_pull' hR (ObjectProperty.homMk c) δ).symm
  have hpush : ∀ {M : (labelsIn D J).FullSubcategory} (a : A.obj ⟶ M.obj)
      (δ' : (dataJ (D := D) (J := J)).Ext (bPartJ C) A),
      R.eta hR (bPartJ C) A δ' ≫ (R.realMap hR a)⟦(1 : ℤ)⟧' =
        R.eta hR (bPartJ C) M ((dataJ (D := D) (J := J)).push (ObjectProperty.homMk a) δ') :=
    fun a δ' => (R.eta_push' hR (ObjectProperty.homMk a) δ').symm
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, biprod.inl_desc, ← Category.assoc, hpull (M := bPartJ C)]
    have hpp := dataJ_push_pull (C'' := bPartJ C) (C := C) (A := A) (A' := bPartJ A)
      (ObjectProperty.homMk (bIncl D C.obj)) (ObjectProperty.homMk (bProj D A.obj)) δ
    have hz : ∀ δ' : (dataJ (D := D) (J := J)).Ext (bPartJ C) (xPartJ A),
        R.eta hR (bPartJ C) (xPartJ A) δ' = 0 :=
      fun δ' => R.eta_eq_zero_of_isZero_right hR (isZero_rho_xPart D A.obj) δ'
    rw [comp_shift_biprod_lift]
    rw [hpush (M := bPartJ A) (bProj D A.obj)]
    have hX := hpush (M := xPartJ A) (xProj D A.obj)
      ((dataJ (D := D) (J := J)).pull (ObjectProperty.homMk (bIncl D C.obj)) δ)
    rw [hz] at hX
    rw [hX, zero_comp, add_zero]
    exact congrArg (fun z => R.eta hR (bPartJ C) (bPartJ A) z ≫ _) hpp
  · have hz : ∀ δ' : (dataJ (D := D) (J := J)).Ext (xPartJ C) A,
        R.eta hR (xPartJ C) A δ' = 0 :=
      fun δ' => R.eta_eq_zero_of_isZero_left hR (isZero_rho_xPart D C.obj) δ'
    rw [biprod.inr_desc_assoc, biprod.inr_desc, ← Category.assoc, hpull (M := xPartJ C), hz,
      zero_comp, zero_comp]

/-- **Realizations go to distinguished triangles** (Proposition 2.3, Step 4). -/
theorem realTriangle_distinguished {A B C : (labelsIn D J).FullSubcategory} {x : A ⟶ B}
    {y : B ⟶ C} {δ : (dataJ (D := D) (J := J)).Ext C A}
    (h : (dataJ (D := D) (J := J)).Realizes δ x y) :
    R.realTriangle hR x y δ ∈ distTriang _ := by
  obtain ⟨w, ⟨hS, hcls⟩, N, hN, θ, x', y', h1, h2, h3⟩ := h
  have hNP : labelsIn D J N :=
    labelsIn_of_retract D (biprod.inl ≫ θ.inv) (θ.hom ≫ biprod.fst) (by simp) B.property
  have hT₁ := R.bPart_realTriangle_distinguished hR w hS hcls hN hNP θ x' y' h2 h3
  have hy'x : y' ≫ xProj D C.obj = 0 := hom_xFree_xPart_eq_zero D hN _
  have hTX := binaryBiproductTriangle_distinguished ((R.realP hR).obj (xPartJ A))
    ((R.realP hR).obj (xPartJ C))
  refine isomorphic_distinguished _ (triangleBiprod_distinguished _ _ hT₁ hTX) _
    (Triangle.isoMk _ _ (R.splitIso hR A) (R.splitIsoMid hR hNP θ) (R.splitIso hR C)
      (splitIso_comm_mor₁ R hR hNP θ x x' h1 h2)
      (splitIso_comm_mor₂ R hR hNP θ y y' hy'x h3) (splitIso_comm_mor₃ R hR δ))

end RealizationData

end ExtriangulatedRealization
