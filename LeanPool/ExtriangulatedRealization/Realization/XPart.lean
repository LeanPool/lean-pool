/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Comparison
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# The object `L[-1]` and the morphisms `X → A i` in `K(Q)`

The adjoined object `X` of `C(D)` is realized by the stalk complex `L[-1]` of `L` in degree `1`.
A vector `w ∈ W = Q(L, Y)` gives a chain map `L[-1] → (P i → Y)` with degree-`1` component `w`;
it is null-homotopic when `w ∈ K_i = Q(L, P i)`, since then `w` factors through `c_i`
(Step 2 of the proof of Proposition 2.3, (2.4)).
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject DerivedCategory

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] {D : Iᵒᵖ ⥤ ModuleCat.{u} k}
  {J : Set I} (R : RealizationData D J)

namespace RealizationData

/-- The object `L` of `QInd`. -/
abbrev qX : R.QInd := none

/-- The object of `QInd` attached to an interval. -/
abbrev qI (l : IntervalCat k I) : R.QInd := some l

/-- The object `L` of `Q`. -/
noncomputable abbrev Lobj : R.Q := (Mat_.embedding R.QInd).obj R.qX

/-- The stalk complex `L[-1]` (the object `L` in degree `1`). -/
noncomputable abbrev Xc : CochainComplex R.Q ℤ := (CochainComplex.singleFunctor R.Q 1).obj R.Lobj

/-- The resolution complexes, as complexes over `Q`. -/
noncomputable abbrev resCQ (l : IntervalCat k I) : CochainComplex R.Q ℤ :=
  (R.e₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj (resC l)

/-- `w ∈ W` as a morphism `L ⟶ Y` of `QInd`. -/
def toHomW (w : R.W) : R.qX ⟶ R.qI (IntervalCat.objY (k := k)) := w

/-- `w ∈ K_i` as a morphism `L ⟶ P i` of `QInd`. -/
def toHomK (i : I) (w : R.K i) : R.qX ⟶ R.qI (IntervalCat.objP (k := k) i) := w

/-- The morphism `L ⟶ Y` of `Q` given by `w ∈ W`. -/
noncomputable def wHom (w : R.W) : R.Lobj ⟶ R.e₀.obj (q₀ Y) :=
  (Mat_.embedding R.QInd).map (R.toHomW w)

/-- The morphism `L ⟶ P i` of `Q` given by `w ∈ K_i`. -/
noncomputable def kHom (i : I) (w : R.K i) : R.Lobj ⟶ R.e₀.obj (q₀ (P i)) :=
  (Mat_.embedding R.QInd).map (R.toHomK i w)

lemma kHom_comp_c (i : I) (w : R.K i) :
    R.kHom i w ≫ R.e₀.map ((Mat_.embedding _).map
      (show IntervalCat.objP (k := k) i ⟶ IntervalCat.objY from ⟨cMap i⟩)) = R.wHom (w : R.W) := by
  rw [kHom, wHom]
  change (Mat_.embedding R.QInd).map (R.toHomK i w) ≫
    (Mat_.embedding R.QInd).map (show R.qI (IntervalCat.objP (k := k) i) ⟶
      R.qI IntervalCat.objY from (⟨cMap i⟩ : IntervalCat.objP (k := k) i ⟶ IntervalCat.objY)) = _
  rw [← (Mat_.embedding R.QInd).map_comp]
  congr 1
  change (R.phiMap (show IntervalCat.objP (k := k) i ⟶ IntervalCat.objY from ⟨cMap i⟩)).hom w = _
  change (coeffBot _ _ (cMap i) • ModuleCat.ofHom (R.K i).subtype).hom w = _
  have : coeffBot (show HasBot (P i) from trivial) (show HasBot Y from trivial)
      (cMap (k := k) i) = 1 := by
    exact (intervalMap_app_apply (k := k) _ _ _ ⊥ _ _).trans (dite_eq_left (Set.mem_Iic.mpr bot_le))
  rw [this, one_smul]
  rfl

lemma resCQ_d01 (l : IntervalCat k I) : (R.resCQ l).d 0 1 =
    R.e₀.map (HomologicalComplex.doubleXIso₀ (resd l) rel01).hom ≫ R.e₀.map (resd l) ≫
      R.e₀.map (HomologicalComplex.doubleXIso₁ (resd l) rel01 (by lia)).inv := by
  change R.e₀.map ((resC l).d 0 1) = _
  rw [HomologicalComplex.double_d _ _ (by lia), Functor.map_comp, Functor.map_comp]

lemma resCQ_d12 (l : IntervalCat k I) : (R.resCQ l).d 1 2 = 0 := by
  change R.e₀.map ((resC l).d 1 2) = 0
  rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by lia), Functor.map_zero]

/-- The degree-`1` component of the chain map `L[-1] → (P i → Y)` given by `w ∈ W`. -/
noncomputable def xComp (i : I) (w : R.W) : R.Lobj ⟶ (R.resCQ (A i)).X 1 :=
  R.wHom w ≫ R.e₀.map (HomologicalComplex.doubleXIso₁ (resd (A i)) rel01 (by lia)).inv

/-- The chain map `L[-1] → (P i → Y)` given by `w ∈ W`. -/
noncomputable def xChain (i : I) (w : R.W) : R.Xc ⟶ R.resCQ (A i) :=
  HomologicalComplex.mkHomFromSingle (R.xComp i w) (by
    intro j hj
    obtain rfl : j = 2 := by simp at hj; lia
    rw [resCQ_d12, comp_zero])

lemma ofHom_xChain (i : I) (w : R.W) :
    CochainComplex.HomComplex.Cochain.ofHom (R.xChain i w) =
      CochainComplex.HomComplex.Cochain.fromSingleMk (R.xComp i w)
        (show (1 : ℤ) + 0 = 1 by lia) := by
  refine CochainComplex.HomComplex.Cochain.ext _ _ (fun p q hpq => ?_)
  obtain rfl : p = q := by lia
  by_cases hp : p = 1
  · subst hp
    rw [CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.fromSingleMk_v]
    exact HomologicalComplex.mkHomFromSingle_f _ _
  · rw [CochainComplex.HomComplex.Cochain.fromSingleMk_v_eq_zero _ _ _ _ _ hp]
    exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

/-- The class of `xChain` in `K(Q)`. -/
noncomputable def xMor (i : I) (w : R.W) :
    (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj R.Xc ⟶
      (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj (R.resCQ (A i)) :=
  (HomotopyCategory.quotient _ _).map (R.xChain i w)

/-- **(2.4), vanishing on `K_i`.** If `w ∈ K_i`, the chain map given by `w` is
null-homotopic. -/
lemma xMor_eq_zero (i : I) (w : R.K i) : R.xMor i (w : R.W) = 0 := by
  let z := CochainComplex.HomComplex.Cochain.fromSingleMk (K := R.resCQ (A i))
    (R.kHom i w ≫ R.e₀.map (HomologicalComplex.doubleXIso₀ (resd (A i)) rel01).inv)
    (show (1 : ℤ) + -1 = 0 by lia)
  have hz : CochainComplex.HomComplex.Cochain.ofHom (R.xChain i w) =
      CochainComplex.HomComplex.δ (-1) 0 z + CochainComplex.HomComplex.Cochain.ofHom 0 := by
    rw [CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero, ofHom_xChain,
      CochainComplex.HomComplex.Cochain.δ_fromSingleMk _ _ 0 1 (by lia)]
    congr 1
    rw [resCQ_d01, xComp, ← R.kHom_comp_c i w]
    have e1 : R.e₀.map (HomologicalComplex.doubleXIso₀ (resd (A i)) rel01).inv ≫
        R.e₀.map (HomologicalComplex.doubleXIso₀ (resd (A i)) rel01).hom = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    simp only [Category.assoc]
    erw [reassoc_of% e1]
  have h := (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm ⟨z, hz⟩
  rw [xMor, HomotopyCategory.eq_of_homotopy _ _ h, Functor.map_zero]

lemma xChain_comp_aChain {i j : I} (h : i ≤ j) (w : R.W) :
    R.xChain j w ≫ (R.e₀.mapHomologicalComplex _).map (aChain h) = R.xChain i w := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, xChain, xChain, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.mkHomFromSingle_f, Category.assoc]
  congr 1
  change R.xComp j w ≫ R.e₀.map ((aChain h).f 1) = R.xComp i w
  rw [aChain, HomologicalComplex.mkHomFromDouble_f₁, xComp, xComp, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_assoc]

lemma xMor_comp_aMap {i j : I} (h : i ≤ j) (w : R.W) :
    R.xMor j w ≫ (R.e₀.mapHomotopyCategory _).map (resFunctor.map (aHom h)) = R.xMor i w := by
  rw [resFunctor_map_aMap, xMor, xMor]
  change (HomotopyCategory.quotient _ _).map (R.xChain j w) ≫
    (HomotopyCategory.quotient _ _).map ((R.e₀.mapHomologicalComplex _).map (aChain h)) = _
  rw [← Functor.map_comp, xChain_comp_aChain]

lemma wHom_add (w w' : R.W) : R.wHom (w + w') = R.wHom w + R.wHom w' := rfl

lemma wHom_smul (c : k) (w : R.W) : R.wHom (c • w) = c • R.wHom w := rfl

lemma xChain_add (i : I) (w w' : R.W) : R.xChain i (w + w') = R.xChain i w + R.xChain i w' := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.add_f_apply, xChain, xChain, xChain,
    HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.mkHomFromSingle_f, ← Preadditive.comp_add]
  congr 1
  rw [xComp, xComp, xComp, ← Preadditive.add_comp, wHom_add]

lemma xChain_smul (i : I) (c : k) (w : R.W) : R.xChain i (c • w) = c • R.xChain i w := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.smul_f_apply, xChain, xChain, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.mkHomFromSingle_f, ← Linear.comp_smul]
  congr 1
  rw [xComp, xComp, ← Linear.smul_comp, wHom_smul]

/-- `w ↦ [xChain i w]` as a linear map. -/
noncomputable def xMorLin (i : I) : R.W →ₗ[k]
    ((HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj R.Xc ⟶
      (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj (R.resCQ (A i))) where
  toFun := R.xMor i
  map_add' w w' := by rw [xMor, xMor, xMor, xChain_add, Functor.map_add]
  map_smul' c w := by
    rw [xMor, xMor, xChain_smul, RingHom.id_apply, Functor.map_smul]

/-- The hypotheses of Proposition 2.3: the `q_i` are surjective and compatible. -/
structure IsCompatible : Prop where
  surj : ∀ (i : I) (hi : i ∈ J), Function.Surjective (R.q i hi).hom
  comm : ∀ (i j : I) (hi : i ∈ J) (hj : j ∈ J) (h : i ≤ j),
    R.q j hj ≫ D.map (homOfLE h).op = R.q i hi

variable {R}

lemma IsCompatible.K_eq_ker (hR : R.IsCompatible) (i : I) (hi : i ∈ J) :
    R.K i = LinearMap.ker (R.q i hi).hom := by
  apply le_antisymm
  · exact iInf_le_of_le i (iInf_le_of_le hi (iInf_le_of_le le_rfl le_rfl))
  · simp only [K, le_iInf_iff]
    intro j hj hji w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [← hR.comm j i hj hi hji, ModuleCat.hom_comp, LinearMap.comp_apply, hw, map_zero]

variable (R)

/-- The linear map `D_i → K(Q)(L[-1], A i)`, `q_i(w) ↦ [xChain i w]` (2.4). -/
noncomputable def xLin (hR : R.IsCompatible) (i : I) (hi : i ∈ J) : D.obj (op i) →ₗ[k]
    ((HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj R.Xc ⟶
      (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj (R.resCQ (A i))) :=
  (R.K i).liftQ (R.xMorLin i) (fun w hw => R.xMor_eq_zero i ⟨w, hw⟩) ∘ₗ
    (Submodule.quotEquivOfEq _ _ (hR.K_eq_ker i hi).symm).toLinearMap ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _ (hR.surj i hi)).symm.toLinearMap

lemma xLin_q (hR : R.IsCompatible) (i : I) (hi : i ∈ J) (w : R.W) :
    R.xLin hR i hi ((R.q i hi).hom w) = R.xMor i w := by
  have : (LinearMap.quotKerEquivOfSurjective _ (hR.surj i hi)).symm ((R.q i hi).hom w) =
      Submodule.Quotient.mk w :=
    (LinearMap.quotKerEquivOfSurjective _ (hR.surj i hi)).symm_apply_eq.mpr rfl
  simp only [xLin, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this]
  rfl

lemma xLin_comp_aMap (hR : R.IsCompatible) {i j : I} (hi : i ∈ J) (hj : j ∈ J) (h : i ≤ j)
    (d : D.obj (op j)) :
    R.xLin hR j hj d ≫ (R.e₀.mapHomotopyCategory _).map (resFunctor.map (aHom h)) =
      R.xLin hR i hi ((D.map (homOfLE h).op).hom d) := by
  obtain ⟨w, rfl⟩ := hR.surj j hj d
  rw [xLin_q, xMor_comp_aMap, ← ModuleCat.comp_apply, hR.comm i j hi hj h, xLin_q]

end RealizationData

end ExtriangulatedRealization
