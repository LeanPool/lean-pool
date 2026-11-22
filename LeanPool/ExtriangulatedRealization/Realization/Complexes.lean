/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Functors
public import LeanPool.ExtriangulatedRealization.Intervals.Exact
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Injective resolutions of the interval representations in `K(Q₀)`

Each interval `l` has a resolution `I⁰(l) → I¹(l)` by objects of `Q₀`: `Y → 0`, `P i → 0`, and
`P i → Y` for `A i` (Step 1 of the proof of Proposition 2.3). The resolution complex is the
two-term complex `double`; its image under `ι₀` is a bounded complex of injective
representations, hence K-injective.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

/-- The object of `Q₀` attached to a label. -/
noncomputable abbrev q₀ (l : IntervalCat k I) : Q₀ k I := (Mat_.embedding _).obj l

/-- The value of `ι₀` on a label. -/
noncomputable def ι₀Iso (l : IntervalCat k I) : ι₀.obj (q₀ l) ≅ l.rep k :=
  (Mat_.embeddingLiftIso (𝟭 (Rep k I))).app (l.rep k)

/-- `I⁰` of the resolution. -/
noncomputable abbrev res₀ : IntervalCat k I → Q₀ k I
  | Y => q₀ Y
  | A i => q₀ (P i)
  | P i => q₀ (P i)

/-- `I¹` of the resolution. -/
noncomputable abbrev res₁ : IntervalCat k I → Q₀ k I
  | Y => 0
  | A _ => q₀ Y
  | P _ => 0

/-- The differential of the resolution. -/
noncomputable abbrev resd : ∀ l : IntervalCat k I, res₀ l ⟶ res₁ l
  | Y => 0
  | A i => (Mat_.embedding _).map (show IntervalCat.objP (k := k) i ⟶ IntervalCat.objY from
      ⟨cMap i⟩)
  | P _ => 0

lemma rel01 : (ComplexShape.up ℤ).Rel 0 1 := rfl

/-- The resolution complex of an interval, in degrees `0` and `1`. -/
noncomputable abbrev resC (l : IntervalCat k I) : CochainComplex (Q₀ k I) ℤ :=
  HomologicalComplex.double (resd l) rel01

lemma injective_ι₀_q₀ (l : IntervalCat k I) (hl : HasBot l) : Injective (ι₀.obj (q₀ l)) := by
  rcases l with _ | i | i
  · exact Injective.of_iso (ι₀Iso Y).symm injective_Y
  · exact absurd hl id
  · exact Injective.of_iso (ι₀Iso (P i)).symm (injective_P i)

lemma injective_ι₀_res₀ (l : IntervalCat k I) : Injective (ι₀.obj (res₀ l)) := by
  rcases l with _ | i | i
  · exact injective_ι₀_q₀ Y trivial
  · exact injective_ι₀_q₀ (P i) trivial
  · exact injective_ι₀_q₀ (P i) trivial

lemma injective_ι₀_res₁ (l : IntervalCat k I) : Injective (ι₀.obj (res₁ l)) := by
  rcases l with _ | i | i
  · exact (ι₀.map_isZero (isZero_zero _)).injective
  · exact injective_ι₀_q₀ Y trivial
  · exact (ι₀.map_isZero (isZero_zero _)).injective

/-- The image of a resolution complex in `Rep k I`. -/
noncomputable abbrev resRep (l : IntervalCat k I) : CochainComplex (Rep k I) ℤ :=
  (ι₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj (resC l)

instance resRep_isKInjective (l : IntervalCat k I) : (resRep l).IsKInjective := by
  have h0 : (resRep l).IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact ι₀.map_isZero (HomologicalComplex.isZero_double_X _ _ i (by lia) (by lia))
  have hinj : ∀ n, Injective ((resRep l).X n) := by
    intro n
    change Injective (ι₀.obj ((resC l).X n))
    by_cases h0 : n = 0
    · subst h0
      exact Injective.of_iso (ι₀.mapIso (HomologicalComplex.doubleXIso₀ _ _)).symm
        (injective_ι₀_res₀ l)
    · by_cases h1 : n = 1
      · subst h1
        exact Injective.of_iso (ι₀.mapIso (HomologicalComplex.doubleXIso₁ _ _ (by lia))).symm
          (injective_ι₀_res₁ l)
      · exact (ι₀.map_isZero (HomologicalComplex.isZero_double_X _ _ n h0 h1)).injective
  exact CochainComplex.isKInjective_of_injective _ 0

/-! ### Coaugmentations and quasi-isomorphisms -/

/-- The coaugmentation `l → I⁰(l)`. -/
noncomputable def coaug : ∀ l : IntervalCat k I, l.rep k ⟶ ι₀.obj (res₀ l)
  | Y => (ι₀Iso Y).inv
  | A i => bMap i ≫ (ι₀Iso (P i)).inv
  | P i => (ι₀Iso (P i)).inv

lemma ι₀_map_q₀ {l l' : IntervalCat k I} (f : l ⟶ l') :
    ι₀.map ((Mat_.embedding _).map f) ≫ (ι₀Iso l').hom = (ι₀Iso l).hom ≫ f.hom :=
  (Mat_.embeddingLiftIso (𝟭 (Rep k I))).hom.naturality f.hom

lemma ι₀Iso_inv_naturality {l l' : IntervalCat k I} (f : l ⟶ l') :
    (ι₀Iso l).inv ≫ ι₀.map ((Mat_.embedding _).map f) = f.hom ≫ (ι₀Iso l').inv := by
  rw [← cancel_mono (ι₀Iso l').hom, Category.assoc, ι₀_map_q₀, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma coaug_resd (l : IntervalCat k I) : coaug l ≫ ι₀.map (resd l) = 0 := by
  rcases l with _ | i | i
  · exact (ι₀.map_isZero (isZero_zero _)).eq_of_tgt _ _
  · change (bMap i ≫ (ι₀Iso (P i)).inv) ≫ ι₀.map ((Mat_.embedding _).map
      (show IntervalCat.objP (k := k) i ⟶ IntervalCat.objY from ⟨cMap i⟩)) = 0
    rw [Category.assoc, ι₀Iso_inv_naturality, ← Category.assoc]
    change (bMap i ≫ cMap i) ≫ _ = 0
    rw [bMap_comp_cMap, zero_comp]
  · exact (ι₀.map_isZero (isZero_zero _)).eq_of_tgt _ _

/-- The sequence `l → I⁰(l) → I¹(l)`. -/
noncomputable def coaugSeq (l : IntervalCat k I) : ShortComplex (Rep k I) :=
  ShortComplex.mk (coaug l) (ι₀.map (resd l)) (coaug_resd l)

lemma shortExact_of_isIso_zero {X X' Z : Rep k I} (e : X ⟶ X') [IsIso e] (hZ : IsZero Z)
    (g : X' ⟶ Z) : (ShortComplex.mk e g (hZ.eq_of_tgt _ _)).ShortExact :=
  ShortComplex.Splitting.shortExact
    { r := inv e
      s := 0
      f_r := IsIso.hom_inv_id e
      s_g := hZ.eq_of_src _ _
      id := by
        change inv e ≫ e + g ≫ 0 = 𝟙 X'
        rw [IsIso.inv_hom_id, comp_zero, add_zero] }

lemma coaugSeq_shortExact (l : IntervalCat k I) : (coaugSeq l).ShortExact := by
  rcases l with _ | i | i
  · have : IsIso (coaug (k := k) (I := I) Y) := inferInstanceAs (IsIso (ι₀Iso Y).inv)
    exact shortExact_of_isIso_zero (coaug Y) (ι₀.map_isZero (isZero_zero _)) _
  · refine ShortComplex.shortExact_of_iso ?_ (intervalSeq_shortExact (k := k) i)
    refine ShortComplex.isoMk (Iso.refl _) (ι₀Iso (P i)).symm (ι₀Iso Y).symm ?_ ?_
    · change 𝟙 _ ≫ (bMap i ≫ (ι₀Iso (P i)).inv) = bMap i ≫ (ι₀Iso (P i)).inv
      rw [Category.id_comp]
    · change (ι₀Iso (P i)).inv ≫ ι₀.map ((Mat_.embedding _).map
        (show IntervalCat.objP (k := k) i ⟶ IntervalCat.objY from ⟨cMap i⟩)) =
        cMap i ≫ (ι₀Iso Y).inv
      rw [ι₀Iso_inv_naturality]
  · have : IsIso (coaug (k := k) (I := I) (P i)) := inferInstanceAs (IsIso (ι₀Iso (P i)).inv)
    exact shortExact_of_isIso_zero (coaug (P i)) (ι₀.map_isZero (isZero_zero _)) _

lemma resRep_d01 (l : IntervalCat k I) : (resRep l).d 0 1 =
    ι₀.map (HomologicalComplex.doubleXIso₀ (resd l) rel01).hom ≫ ι₀.map (resd l) ≫
      ι₀.map (HomologicalComplex.doubleXIso₁ (resd l) rel01 (by lia)).inv := by
  change ι₀.map ((resC l).d 0 1) = _
  rw [HomologicalComplex.double_d _ _ (by lia), Functor.map_comp, Functor.map_comp]

/-- The comparison map from the stalk complex of `l` to its resolution. -/
noncomputable def qmap (l : IntervalCat k I) :
    (HomologicalComplex.single (Rep k I) (ComplexShape.up ℤ) 0).obj (l.rep k) ⟶ resRep l :=
  HomologicalComplex.mkHomFromSingle
    (coaug l ≫ ι₀.map (HomologicalComplex.doubleXIso₀ (resd l) rel01).inv) (by
      intro j hj
      obtain rfl : j = 1 := by simp at hj; lia
      rw [resRep_d01]
      simp only [Category.assoc]
      rw [← Functor.map_comp_assoc ι₀ (HomologicalComplex.doubleXIso₀ (resd l) rel01).inv,
        Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc,
        coaug_resd, zero_comp])

lemma qmap_f₀ (l : IntervalCat k I) : (qmap l).f 0 =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (l.rep k)).hom ≫ coaug l ≫
      ι₀.map (HomologicalComplex.doubleXIso₀ (resd l) rel01).inv :=
  HomologicalComplex.mkHomFromSingle_f _ _

lemma resRep_isZero (l : IntervalCat k I) {n : ℤ} (h0 : n ≠ 0) (h1 : n ≠ 1) :
    IsZero ((resRep l).X n) :=
  ι₀.map_isZero (HomologicalComplex.isZero_double_X _ _ n h0 h1)

instance qmap_quasiIso (l : IntervalCat k I) : QuasiIso (qmap l) := by
  rw [quasiIso_iff]
  intro n
  by_cases h0 : n = 0
  · subst h0
    rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
    rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp) (by simp)
      ((resRep_isZero l (by lia) (by lia)).eq_of_src _ _)]
    have hmono := (coaugSeq_shortExact l).mono_f
    change Mono (coaug l) at hmono
    constructor
    · refine (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (l.rep k))
        (ι₀.mapIso (HomologicalComplex.doubleXIso₀ (resd l) rel01))
        (ι₀.mapIso (HomologicalComplex.doubleXIso₁ (resd l) rel01 (by lia))) ?_ ?_)).mpr
        (coaugSeq_shortExact l).exact
      · change _ ≫ coaug l = (qmap l).f 0 ≫ _
        rw [qmap_f₀]
        simp only [Category.assoc, Functor.mapIso_hom]
        rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
      · change _ ≫ ι₀.map (resd l) = (resRep l).d 0 1 ≫ _
        rw [resRep_d01]
        simp only [Category.assoc, Functor.mapIso_hom, ← Functor.map_comp, Iso.inv_hom_id,
          Category.comp_id]
    · change Mono ((qmap l).f 0)
      rw [qmap_f₀]
      infer_instance
  · by_cases h1 : n = 1
    · subst h1
      rw [quasiIsoAt_iff_exactAt _ _ (HomologicalComplex.exactAt_single_obj _ _ _ _ (by lia))]
      rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
      rw [ShortComplex.exact_iff_epi _ ((resRep_isZero l (by lia) (by lia)).eq_of_tgt _ _)]
      change Epi ((resRep l).d 0 1)
      rw [resRep_d01]
      have := (coaugSeq_shortExact l).epi_g
      change Epi (ι₀.map (resd l)) at this
      have : IsIso (ι₀.map (HomologicalComplex.doubleXIso₀ (resd l) rel01).hom) := inferInstance
      have : IsIso (ι₀.map (HomologicalComplex.doubleXIso₁ (resd l) rel01 (by lia)).inv) :=
        inferInstance
      infer_instance
    · rw [quasiIsoAt_iff_exactAt _ _ (HomologicalComplex.exactAt_single_obj _ _ _ _ h0)]
      exact HomologicalComplex.ExactAt.of_isZero (resRep_isZero l h0 h1)

end ExtriangulatedRealization
