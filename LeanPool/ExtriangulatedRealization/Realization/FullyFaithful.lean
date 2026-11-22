/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Functor

/-!
# The realization functor is fully faithful (Proposition 2.3, Step 2)

On intervals this is the full faithfulness of the lift along `G` together with the full
faithfulness of the single functor into the derived category. Morphisms out of `L[-1]` are
computed by (2.4): `K(Q)(L[-1], A i) ≅ W / K_i ≅ D_i`, `K(Q)(L[-1], L[-1]) ≅ k`, and all other
morphism spaces involving `L[-1]` vanish for degree reasons or because `Q(-, L) = 0` on intervals.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject DerivedCategory

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

attribute [local instance] HasDerivedCategory.standard

/-! ### The resolution functor is fully faithful -/

instance resFunctor_faithful : (resFunctor (k := k) (I := I)).Faithful where
  map_injective {l l'} φ ψ h := by
    have h' := congrArg (Gfun k I).map h
    rw [Gfun_map_resFunctor, Gfun_map_resFunctor] at h'
    have h'' : (singleFunctor (Rep k I) 0).map φ.hom = (singleFunctor (Rep k I) 0).map ψ.hom :=
      (cancel_mono (eIso l').inv).mp ((cancel_epi (eIso l).hom).mp h')
    exact InducedCategory.hom_ext ((singleFunctor (Rep k I) 0).map_injective h'')

instance resFunctor_full : (resFunctor (k := k) (I := I)).Full where
  map_surjective {l l'} f := by
    obtain ⟨g, hg⟩ := (singleFunctor (Rep k I) 0).map_surjective
      ((eIso l).inv ≫ (Gfun k I).map f ≫ (eIso l').hom)
    refine ⟨⟨g⟩, (Gfun_map_bijective (resK l) l').1 ?_⟩
    refine (Gfun_map_resFunctor _).trans ?_
    change (eIso l).hom ≫ (singleFunctor (Rep k I) 0).map g ≫ (eIso l').inv = _
    rw [hg]
    simp only [Iso.hom_inv_id_assoc, Category.assoc]
    exact (Category.assoc _ _ _).trans ((congrArg _ (Iso.hom_inv_id _)).trans
      (Category.comp_id _))

/-! ### Morphisms involving `L[-1]` -/

namespace RealizationData

variable {D : Iᵒᵖ ⥤ ModuleCat.{u} k} {J : Set I} (R : RealizationData D J)

lemma homotopy_f₁ {E : CochainComplex R.Q ℤ} {f g : R.Xc ⟶ E} (h : Homotopy f g) :
    f.f 1 = h.hom 1 0 ≫ E.d 0 1 + g.f 1 := by
  have := h.comm 1
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 1 2 by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp)] at this
  rw [this]
  change ((HomologicalComplex.single R.Q (ComplexShape.up ℤ) 1).obj R.Lobj).d 1 2 ≫ _ + _ + _ = _
  rw [HomologicalComplex.single_obj_d, zero_comp, zero_add]

lemma embedding_map_scalar (c : k) :
    (Mat_.embedding R.QInd).map (show R.qX ⟶ R.qX from c) = c • 𝟙 R.Lobj := by
  funext i j
  have : Subsingleton R.Lobj.ι := inferInstanceAs (Subsingleton PUnit)
  obtain rfl : i = j := Subsingleton.elim _ _
  change c = c • (𝟙 R.Lobj : Mat_.Hom R.Lobj R.Lobj) i i
  rw [Mat_.id_apply_self]
  exact (mul_one c).symm

lemma sc_surj (f : (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj R.Xc ⟶
    (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj R.Xc) : ∃ c : k, c • 𝟙 _ = f := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).map_surjective f
  obtain ⟨c, hc⟩ := (Mat_.embedding R.QInd).map_surjective
    ((HomologicalComplex.singleObjXSelf _ 1 R.Lobj).inv ≫ g.f 1 ≫
      (HomologicalComplex.singleObjXSelf _ 1 R.Lobj).hom)
  refine ⟨(show k from c), ?_⟩
  have hg : g = (show k from c) • 𝟙 R.Xc := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
    have h1 : g.f 1 = (HomologicalComplex.singleObjXSelf _ 1 R.Lobj).hom ≫
        (Mat_.embedding R.QInd).map c ≫ (HomologicalComplex.singleObjXSelf _ 1 R.Lobj).inv := by
      rw [hc]
      simp
    rw [h1, R.embedding_map_scalar (show k from c), Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Iso.hom_inv_id]
  rw [hg, Functor.map_smul, CategoryTheory.Functor.map_id]

lemma sc_inj {c c' : k} (h : c • 𝟙 ((HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj R.Xc) =
    c' • 𝟙 _) : c = c' := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, ← Functor.map_smul] at h
  have hh := R.homotopy_f₁ (HomotopyCategory.homotopyOfEq _ _ h)
  rw [show R.Xc.d 0 1 = 0 from
    HomologicalComplex.single_obj_d (c := ComplexShape.up ℤ) 1 R.Lobj 0 1,
    comp_zero, zero_add,
    HomologicalComplex.smul_f_apply, HomologicalComplex.smul_f_apply,
    HomologicalComplex.id_f] at hh
  have h2 : (Mat_.embedding R.QInd).map (show R.qX ⟶ R.qX from c) =
      (Mat_.embedding R.QInd).map (show R.qX ⟶ R.qX from c') := by
    rw [R.embedding_map_scalar, R.embedding_map_scalar]
    have := congrArg (fun φ => (HomologicalComplex.singleObjXSelf _ 1 R.Lobj).inv ≫ φ ≫
      (HomologicalComplex.singleObjXSelf _ 1 R.Lobj).hom) hh
    simpa [Linear.smul_comp, Linear.comp_smul] using this
  exact (Mat_.embedding R.QInd).map_injective h2

lemma xChain_f₁ (i : I) (w : R.W) : (R.xChain i w).f 1 =
    (HomologicalComplex.singleObjXSelf _ 1 R.Lobj).hom ≫ R.wHom w ≫
      R.e₀.map (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).inv :=
  HomologicalComplex.mkHomFromSingle_f _ _

lemma ιA_surj (hR : R.IsCompatible) (i : I) (hi : i ∈ J)
    (f : (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj R.Xc ⟶
      (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj (R.resCQ (A i))) :
    ∃ d, R.xLin hR i hi d = f := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).map_surjective f
  obtain ⟨w, hw⟩ := (Mat_.embedding R.QInd).map_surjective
    (show R.Lobj ⟶ (Mat_.embedding R.QInd).obj (R.qI IntervalCat.objY) from
      (HomologicalComplex.singleObjXSelf _ 1 R.Lobj).inv ≫ g.f 1 ≫
        R.e₀.map (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).hom)
  let w' : R.W := w
  refine ⟨(R.q i hi).hom w', ?_⟩
  rw [R.xLin_q hR i hi w']
  change (HomotopyCategory.quotient _ _).map (R.xChain i w') = _
  congr 1
  apply HomologicalComplex.from_single_hom_ext
  rw [xChain_f₁]
  change _ ≫ (Mat_.embedding R.QInd).map w ≫ _ = _
  rw [hw]
  have e : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1 R.Lobj).hom ≫
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1 R.Lobj).inv ≫ g.f 1 ≫
        R.e₀.map (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).hom) ≫
      R.e₀.map (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).inv = g.f 1 := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  exact e

lemma ιA_inj (hR : R.IsCompatible) (i : I) (hi : i ∈ J) (d : D.obj (op i))
    (h : R.xLin hR i hi d = 0) : d = 0 := by
  obtain ⟨w, rfl⟩ := hR.surj i hi d
  rw [R.xLin_q hR i hi w, xMor, ← Functor.map_zero (HomotopyCategory.quotient R.Q _)
    R.Xc (R.resCQ (A i))] at h
  have hh := R.homotopy_f₁ (HomotopyCategory.homotopyOfEq _ _ h)
  rw [HomologicalComplex.zero_f, add_zero, xChain_f₁, R.resCQ_d01] at hh
  obtain ⟨w', hw'⟩ := (Mat_.embedding R.QInd).map_surjective
    (show R.Lobj ⟶ (Mat_.embedding R.QInd).obj (R.qI (IntervalCat.objP i)) from
      (HomologicalComplex.singleObjXSelf _ 1 R.Lobj).inv ≫
        (HomotopyCategory.homotopyOfEq _ _ h).hom 1 0 ≫
          R.e₀.map (HomologicalComplex.doubleXIso₀ (resd (A i)) rel01).hom)
  let w'' : R.K i := w'
  have hh' : R.wHom w = ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1 R.Lobj).inv ≫
      (HomotopyCategory.homotopyOfEq _ _ h).hom 1 0 ≫
        R.e₀.map (HomologicalComplex.doubleXIso₀ (resd (A i)) rel01).hom) ≫
      R.e₀.map (resd (A i)) := by
    calc R.wHom w = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1 R.Lobj).inv ≫
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1 R.Lobj).hom ≫ R.wHom w ≫
            R.e₀.map (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).inv) ≫
          R.e₀.map (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).hom := by
          simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
            CategoryTheory.Functor.map_id, Category.comp_id]
      _ = _ := by
          rw [hh]
          simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
            Category.comp_id]
  have hw : R.wHom w = R.wHom (w'' : R.W) := by
    rw [← R.kHom_comp_c, hh']
    change _ = (Mat_.embedding R.QInd).map w' ≫ _
    rw [hw']
    rfl
  have hw2 : w = (w'' : R.W) := (Mat_.embedding R.QInd).map_injective hw
  have hmem : w ∈ R.K i := hw2 ▸ w''.2
  rw [hR.K_eq_ker i hi] at hmem
  exact hmem

lemma hom_res_Xc_eq_zero (l : IntervalCat k I)
    (f : (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj (R.resCQ l) ⟶
      (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj R.Xc) : f = 0 := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).map_surjective f
  have : g = 0 := by
    apply HomologicalComplex.to_single_hom_ext
    rw [HomologicalComplex.zero_f]
    rcases l with _ | i | i
    · refine (R.e₀.map_isZero (IsZero.of_iso (isZero_zero _)
        (HomologicalComplex.doubleXIso₁ _ rel01 (by lia)))).eq_of_src _ _
    · obtain ⟨x, hx⟩ := (Mat_.embedding R.QInd).map_surjective
        (show (Mat_.embedding R.QInd).obj (R.qI IntervalCat.objY) ⟶ R.Lobj from
          R.e₀.map (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).inv ≫ g.f 1 ≫
            (HomologicalComplex.singleObjXSelf _ 1 R.Lobj).hom)
      have hx0 : x = 0 := Subsingleton.elim (α := PUnit) _ _
      rw [hx0, Functor.map_zero] at hx
      have key : R.e₀.map (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).inv ≫
          g.f 1 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1 R.Lobj).hom = 0 :=
        hx.symm
      have e : g.f 1 = R.e₀.map (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).hom ≫
          (R.e₀.map (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).inv ≫
            g.f 1 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1 R.Lobj).hom) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1 R.Lobj).inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, ← Functor.map_comp_assoc,
          CategoryTheory.Functor.map_id, Category.id_comp]
      rw [e, key, zero_comp, comp_zero]
    · refine (R.e₀.map_isZero (IsZero.of_iso (isZero_zero _)
        (HomologicalComplex.doubleXIso₁ _ rel01 (by lia)))).eq_of_src _ _
  rw [this, Functor.map_zero]

instance FB_full : (R.FB (J := J)).Full := by
  unfold FB
  infer_instance

instance FB_faithful : (R.FB (J := J)).Faithful := by
  unfold FB
  infer_instance

variable (hR : R.IsCompatible)

instance F₁_faithful : (R.F₁ hR).Faithful where
  map_injective {X Y} f g h := by
    rcases X with _ | a <;> rcases Y with _ | b
    · exact R.sc_inj h
    · rcases b with ⟨_ | i | i, hb⟩
      · exact Subsingleton.elim (α := PUnit) _ _
      · let f' : D.obj (op i) := f
        let g' : D.obj (op i) := g
        have h' : R.xLin hR i hb (f' - g') = 0 := by
          rw [map_sub, sub_eq_zero]
          exact h
        have e : f' = g' := sub_eq_zero.mp (R.ιA_inj hR i hb _ h')
        exact e
      · exact Subsingleton.elim (α := PUnit) _ _
    · exact Subsingleton.elim (α := PUnit) _ _
    · exact (R.FB).map_injective h

instance F₁_full : (R.F₁ hR).Full where
  map_surjective {X Y} f := by
    rcases X with _ | a <;> rcases Y with _ | b
    · exact R.sc_surj f
    · rcases b with ⟨_ | i | i, hb⟩
      · exact ⟨(0 : PUnit), (R.hom_Xc_eq_zero (l := Y) trivial f).symm⟩
      · exact R.ιA_surj hR i hb f
      · exact ⟨(0 : PUnit), (R.hom_Xc_eq_zero (l := P i) trivial f).symm⟩
    · exact ⟨PUnit.unit, (R.hom_res_Xc_eq_zero _ f).symm⟩
    · exact (R.FB).map_surjective f

instance realF_full : (R.realF hR).Full := by
  unfold realF
  infer_instance

instance realF_faithful : (R.realF hR).Faithful := by
  unfold realF
  infer_instance

end RealizationData

end ExtriangulatedRealization
