/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.GalerkinOptimizerReadout
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ResponseFieldSize

/-!
# High-contrast homogenization: Entry.Response.Core.SubcellCoefficientGluing

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Gluing the recentred coefficient across slices and subcells

This file glues the per-slice optimizer readouts into the recentred coefficients `a_-`/`a_+` on
the parent adapted cell, and performs the same construction on each aligned adapted subcell,
keeping the raw field definitionally equal to `respCoeffMinus`/`respCoeffPlus`. It proves the
resulting measurability of the coefficient carriers, and the cell-energy layer: the metric square
of the canonical state's average on a cell is controlled by the cell's response size and the
actual state energy there. A short addendum records the integrability, on its own subcell, of the
recentred child field the diagonal weak-norm estimate's cell-average step consumes. This is the
gluing and cell-energy layer of the response transfer `p.response.transfer`.
-/

section
/-!
## Gluing optimizer readouts across quantitative slices
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Quantitative slices cover each transformed regular response field on an adapted cell. -/
theorem exists_responseSlice_of_ellipticRepresentative
    {U : Set (Vec d)} (hU : MeasurableSet U) (A : RegCoeffField d)
    {lam Lam : ℝ} {f : CoeffField d} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U f)
    (hae : A.toFun =ᵐ[volumeMeasureOn U] f) :
    ∃ k : ℕ, AEEQuantitativeEllipticSlice U k A.toFun := by
  have hAEE : IsAEEllipticFieldOn lam Lam U A.toFun := by
    refine ⟨hU, ?_, ?_⟩
    · intro i j
      exact aestronglyMeasurable_restrictCoeffField_carrier U hU A i j
    · filter_upwards [hae, (IsAEEllipticFieldOn.of_isEllipticFieldOn hEll).2.2]
        with x hx hxf
      simpa [hx] using hxf
  exact AEEQuantitativeEllipticSlice.exists_of_aeeEllipticOn hlam hAEE

/-- Choose a Chapter-2 coefficient object from the first quantitative slice containing a regular
field.  Its raw representative remains exactly the input field. -/
@[expose]
def responseCoeffOnFromSliceCover (U : Book.Ch02.Domain d) (A : RegCoeffField d)
    (hcover : ∃ k : ℕ, AEEQuantitativeEllipticSlice (U : Set (Vec d)) k A.toFun) :
    Book.Ch02.CoeffOn U :=
  responseCoeffOnOfSlice U A (Classical.choose_spec hcover)

@[simp] theorem responseCoeffOnFromSliceCover_toFun (U : Book.Ch02.Domain d)
    (A : RegCoeffField d)
    (hcover : ∃ k : ℕ, AEEQuantitativeEllipticSlice (U : Set (Vec d)) k A.toFun) :
    (responseCoeffOnFromSliceCover U A hcover).toCoeffField = A.toFun := rfl

/-- Glue the fixed-slice weighted-readout theorem across a measurable countable slice cover. -/
theorem measurable_canonicalOptimizerStateReadout_of_sliceCover
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Book.Ch02.Domain d}
    (hUopen : IsOpen (U : Set (Vec d))) (hUfin : volume (U : Set (Vec d)) ≠ ⊤)
    (hvol : 0 < (volume (U : Set (Vec d))).toReal) {A : Om → RegCoeffField d}
    (hcover : ∀ w : Om, ∃ k : ℕ,
      AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (U : Set (Vec d)) →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (aU : Om → Book.Ch02.CoeffOn U) (haU : ∀ w, (aU w).toCoeffField = (A w).toFun)
    (p q : Vec d) (α : BlockCoord d) {η : Vec d → ℝ}
    (hη : MemScalarL2 (U : Set (Vec d)) η) :
    Measurable fun w : Om ↦ canonicalOptimizerStateReadout U (aU w) p q α η := by
  classical
  let slice : ℕ → Set Om := fun k ↦
    {w | AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (A w).toFun}
  have hsliceMeas : ∀ k, MeasurableSet (slice k) := by
    intro k
    apply Annealed.measurableSet_aeeSlice_of_entryTest_response A hUopen
    intro i j φ hφ
    exact hEntry i j hφ.contDiff hφ.hasCompactSupport hφ.tsupport_subset
  have hslices : ⋃ k : ℕ, slice k = Set.univ := by
    ext w
    constructor
    · exact fun _ ↦ Set.mem_univ w
    · intro _
      obtain ⟨k, hk⟩ := hcover w
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
  let f : (k : ℕ) → slice k → ℝ := fun k w ↦
    canonicalOptimizerStateReadout U (responseCoeffOnOfSlice U (A w.1) w.2) p q α η
  have hagree : ∀ (i j : ℕ) (w : Om) (hwi : w ∈ slice i) (hwj : w ∈ slice j),
      f i ⟨w, hwi⟩ = f j ⟨w, hwj⟩ := by
    intro i j w hwi hwj
    apply canonicalOptimizerStateReadout_congr
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hfmeas : ∀ k : ℕ, Measurable (f k) := by
    intro k
    exact measurable_integral_weighted_canonicalOptimizerBlockState hUopen hUfin hvol
      (A := fun w : slice k ↦ A w.1) (fun w ↦ w.2)
      (fun i j φ hφ hc hs ↦ (hEntry i j hφ hc hs).comp measurable_subtype_coe)
      (fun w ↦ responseCoeffOnOfSlice U (A w.1) w.2) (fun _ ↦ rfl) p q α hη
  have heq : (fun w : Om ↦ canonicalOptimizerStateReadout U (aU w) p q α η) =
      Set.liftCover slice f hagree hslices := by
    funext w
    obtain ⟨k, hk⟩ := hcover w
    rw [Set.liftCover_of_mem (S := slice) (f := f) (hf := hagree) (hS := hslices)
      (i := k) hk]
    apply canonicalOptimizerStateReadout_congr
    filter_upwards with x
    exact congrFun (haU w) x
  rw [heq]
  exact measurable_liftCover slice hsliceMeas f hfmeas hagree hslices

/-! ## The actual transformed coefficient fields -/

/-- The minus transformed coefficient lies in some quantitative slice on every adapted cell. -/
theorem exists_responseSlice_selectionRespCoeffMinusReg
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ k : ℕ, AEEQuantitativeEllipticSlice (HighContrast.adaptedCell q t) k
      (selectionRespCoeffMinusReg F a).toFun := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  exact exists_responseSlice_of_ellipticRepresentative
    (measurableSet_of_isEllipticFieldOn hEll) (selectionRespCoeffMinusReg F a)
    hlam hEll (by simpa only [selectionRespCoeffMinusReg_toFun] using hae)

/-- The plus transformed coefficient lies in some quantitative slice on every adapted cell. -/
theorem exists_responseSlice_selectionRespCoeffPlusReg
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ k : ℕ, AEEQuantitativeEllipticSlice (HighContrast.adaptedCell q t) k
      (selectionRespCoeffPlusReg F a).toFun := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  exact exists_responseSlice_of_ellipticRepresentative
    (measurableSet_of_isEllipticFieldOn hEll) (selectionRespCoeffPlusReg F a)
    hlam hEll (by simpa only [selectionRespCoeffPlusReg_toFun] using hae)

/-- Canonical Chapter-2 coefficient object for the minus transformed response field. -/
@[expose]
def canonicalRespCoeffMinusOn (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) : Book.Ch02.CoeffOn (adaptedDomain q hq t) :=
  responseCoeffOnFromSliceCover (adaptedDomain q hq t) (selectionRespCoeffMinusReg F a)
    (exists_responseSlice_selectionRespCoeffMinusReg q hq t F a)

@[simp] theorem canonicalRespCoeffMinusOn_toFun
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    (canonicalRespCoeffMinusOn q hq t F a).toCoeffField = respCoeffMinus F a := by
  change (selectionRespCoeffMinusReg F a).toFun = respCoeffMinus F a
  exact selectionRespCoeffMinusReg_toFun F a

/-- Canonical Chapter-2 coefficient object for the plus transformed response field. -/
@[expose]
def canonicalRespCoeffPlusOn (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) : Book.Ch02.CoeffOn (adaptedDomain q hq t) :=
  responseCoeffOnFromSliceCover (adaptedDomain q hq t) (selectionRespCoeffPlusReg F a)
    (exists_responseSlice_selectionRespCoeffPlusReg q hq t F a)

@[simp] theorem canonicalRespCoeffPlusOn_toFun
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    (canonicalRespCoeffPlusOn q hq t F a).toCoeffField = respCoeffPlus F a := by
  change (selectionRespCoeffPlusReg F a).toFun = respCoeffPlus F a
  exact selectionRespCoeffPlusReg_toFun F a

/-- Adapted cells have positive real volume, in the exact form used by the Galerkin selector. -/
theorem adaptedCell_volume_toReal_pos
    (q : Mat d) (hq : IsUnit q) (t : ℤ) :
    0 < (volume (HighContrast.adaptedCell q t)).toReal := by
  have hset : HighContrast.adaptedCell q t =
      translateSet 0 (matVecMul q '' openCubeSet (originCube d t)) := by
    rw [← Annealed.adaptedCellTranslate_eq_cg_affine q t 0]
    simp [HighContrast.adaptedCellTranslate]
  rw [hset]
  exact volume_affine_openCube_toReal_pos q hq t 0

/-- Every weighted coordinate readout of the canonical minus optimizer is measurable in the
coefficient sample. -/
theorem measurable_canonicalRespCoeffMinusReadout
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d)
    (p r : Vec d) (alpha : BlockCoord d) {η : Vec d → ℝ}
    (hη : MemScalarL2 (HighContrast.adaptedCell q t) η) :
    Measurable fun a : CoeffSpace d ↦
      canonicalOptimizerStateReadout (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r alpha η := by
  apply measurable_canonicalOptimizerStateReadout_of_sliceCover
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen
    (adaptedCell_isOpenBoundedConvexDomain q hq t).volume_lt_top.ne
    (adaptedCell_volume_toReal_pos q hq t)
    (fun a ↦ exists_responseSlice_selectionRespCoeffMinusReg q hq t F a)
    (fun i j φ hφ hcpt _hs ↦ measurable_entryTest_selectionRespCoeffMinusReg F i j hφ hcpt)
    (fun a ↦ canonicalRespCoeffMinusOn q hq t F a) (fun _ ↦ rfl) p r alpha hη

/-- Every weighted coordinate readout of the canonical plus optimizer is measurable in the
coefficient sample. -/
theorem measurable_canonicalRespCoeffPlusReadout
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d)
    (p r : Vec d) (alpha : BlockCoord d) {η : Vec d → ℝ}
    (hη : MemScalarL2 (HighContrast.adaptedCell q t) η) :
    Measurable fun a : CoeffSpace d ↦
      canonicalOptimizerStateReadout (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r alpha η := by
  apply measurable_canonicalOptimizerStateReadout_of_sliceCover
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen
    (adaptedCell_isOpenBoundedConvexDomain q hq t).volume_lt_top.ne
    (adaptedCell_volume_toReal_pos q hq t)
    (fun a ↦ exists_responseSlice_selectionRespCoeffPlusReg q hq t F a)
    (fun i j φ hφ hcpt _hs ↦ measurable_entryTest_selectionRespCoeffPlusReg F i j hφ hcpt)
    (fun a ↦ canonicalRespCoeffPlusOn q hq t F a) (fun _ ↦ rfl) p r alpha hη

/-- Restricting the readout weight by an indicator realizes a localized volume average. -/
theorem volumeAverage_weighted_canonicalOptimizerBlockState
    {U : Book.Ch02.Domain d} (aU : Book.Ch02.CoeffOn U) (p r : Vec d)
    (alpha : BlockCoord d) {V : Set (Vec d)} (hV : MeasurableSet V)
    (hVU : V ⊆ (U : Set (Vec d))) (eta : Vec d → ℝ) :
    volumeAverage V (fun x ↦ eta x *
        toFullBlockVec (canonicalOptimizerBlockState U aU p r x) alpha) =
      (volume V).toReal⁻¹ *
        canonicalOptimizerStateReadout U aU p r alpha (V.indicator eta) := by
  unfold volumeAverage canonicalOptimizerStateReadout
  congr 1
  rw [← integral_indicator hV]
  rw [← integral_indicator U.isDomain.isOpen.measurableSet]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ V
  · simp [hx, hVU hx]
  · by_cases hxu : x ∈ (U : Set (Vec d)) <;> simp [hx, hxu]

/-- Localized weighted averages of the canonical minus optimizer are measurable. -/
theorem measurable_volumeAverage_weighted_canonicalRespCoeffMinus
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d)
    (p r : Vec d) (alpha : BlockCoord d) {V : Set (Vec d)}
    (hV : MeasurableSet V) (hVU : V ⊆ HighContrast.adaptedCell q t)
    {eta : Vec d → ℝ}
    (heta : MemScalarL2 (HighContrast.adaptedCell q t) (V.indicator eta)) :
    Measurable fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x) alpha) := by
  have heq : (fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x) alpha)) =
      fun a ↦ (volume V).toReal⁻¹ *
        canonicalOptimizerStateReadout (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r alpha (V.indicator eta) := by
    funext a
    exact volumeAverage_weighted_canonicalOptimizerBlockState
      (canonicalRespCoeffMinusOn q hq t F a) p r alpha hV hVU eta
  rw [heq]
  exact (measurable_canonicalRespCoeffMinusReadout q hq t F p r alpha heta).const_mul _

/-- Localized weighted averages of the canonical plus optimizer are measurable. -/
theorem measurable_volumeAverage_weighted_canonicalRespCoeffPlus
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d)
    (p r : Vec d) (alpha : BlockCoord d) {V : Set (Vec d)}
    (hV : MeasurableSet V) (hVU : V ⊆ HighContrast.adaptedCell q t)
    {eta : Vec d → ℝ}
    (heta : MemScalarL2 (HighContrast.adaptedCell q t) (V.indicator eta)) :
    Measurable fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x) alpha) := by
  have heq : (fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x) alpha)) =
      fun a ↦ (volume V).toReal⁻¹ *
        canonicalOptimizerStateReadout (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r alpha (V.indicator eta) := by
    funext a
    exact volumeAverage_weighted_canonicalOptimizerBlockState
      (canonicalRespCoeffPlusOn q hq t F a) p r alpha hV hVU eta
  rw [heq]
  exact (measurable_canonicalRespCoeffPlusReadout q hq t F p r alpha heta).const_mul _

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The Chapter-2 coefficient object on an aligned adapted subcell

`SubcellCoefficientGluing.lean` attaches to the parent adapted cell `⋄_t^q` a Chapter-2 coefficient
object whose raw field is the recentred response coefficient `a_- = a - g` (resp.
`a_+ = aᵀ + g`), and keeps that raw field definitionally equal to `respCoeffMinus` (resp.
`respCoeffPlus`).  This module performs the same construction on each aligned adapted subcell
`adaptedCellAtCenter q k w`, the per-`w` child carrier of the aligned subdivision.

The elliptic input on the subcell is obtained from
`Annealed.exists_elliptic_representative_adapted`, which covers every translated adapted cell
`adaptedCellTranslate q k y`, hence in particular `adaptedCellAtCenter q k w`.  The quantitative
slice
cover then follows from `exists_responseSlice_of_ellipticRepresentative`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The elliptic representative on an aligned subcell -/

/-- The minus transformed coefficient `a_- = a - g` has, on the aligned adapted subcell
`adaptedCellAtCenter q k w`, an a.e.-equal representative that is uniformly elliptic there.  The
constants depend on the sample and on the cell only and enter no estimate. -/
theorem exists_elliptic_representative_respCoeffMinusAt (q : Mat d) (hq : IsUnit q)
    (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (adaptedCellAtCenter q k w) f ∧
        respCoeffMinus F a =ᵐ[volumeMeasureOn (adaptedCellAtCenter q k w)] f := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => f x - respg F, hlam, ?_,
    isEllipticFieldOn_sub_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0 : ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith only [hlam, hle, hn]
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffMinus, hx]

/-- The plus transformed coefficient `a_+ = aᵀ + g` has, on the aligned adapted subcell
`adaptedCellAtCenter q k w`, an a.e.-equal representative that is uniformly elliptic there. -/
theorem exists_elliptic_representative_respCoeffPlusAt (q : Mat d) (hq : IsUnit q)
    (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (adaptedCellAtCenter q k w) f ∧
        respCoeffPlus F a =ᵐ[volumeMeasureOn (adaptedCellAtCenter q k w)] f := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => matTranspose (f x) + respg F, hlam, ?_,
    isEllipticFieldOn_transpose_add_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0 : ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith only [hlam, hle, hn]
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffPlus, hx]

/-! ## The quantitative slice covers on the subcell -/

/-- The minus transformed coefficient lies in some quantitative slice on every aligned adapted
subcell. -/
theorem exists_responseSlice_selectionRespCoeffMinusRegAt
    (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ j : ℕ, AEEQuantitativeEllipticSlice (adaptedCellAtCenter q k w) j
      (selectionRespCoeffMinusReg F a).toFun := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinusAt q hq k w F a
  exact exists_responseSlice_of_ellipticRepresentative
    (measurableSet_of_isEllipticFieldOn hEll) (selectionRespCoeffMinusReg F a)
    hlam hEll (by simpa only [selectionRespCoeffMinusReg_toFun] using hae)

/-- The plus transformed coefficient lies in some quantitative slice on every aligned adapted
subcell. -/
theorem exists_responseSlice_selectionRespCoeffPlusRegAt
    (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ j : ℕ, AEEQuantitativeEllipticSlice (adaptedCellAtCenter q k w) j
      (selectionRespCoeffPlusReg F a).toFun := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlusAt q hq k w F a
  exact exists_responseSlice_of_ellipticRepresentative
    (measurableSet_of_isEllipticFieldOn hEll) (selectionRespCoeffPlusReg F a)
    hlam hEll (by simpa only [selectionRespCoeffPlusReg_toFun] using hae)

/-! ## The canonical subcell coefficient objects -/

/-- Canonical Chapter-2 coefficient object for the minus transformed response field on the aligned
adapted subcell `adaptedCellAtCenter q k w`. -/
@[expose]
def canonicalRespCoeffMinusOnAt (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    Book.Ch02.CoeffOn (adaptedDomainAt q hq k w) :=
  responseCoeffOnFromSliceCover (adaptedDomainAt q hq k w) (selectionRespCoeffMinusReg F a)
    (exists_responseSlice_selectionRespCoeffMinusRegAt q hq k w F a)

@[simp] theorem canonicalRespCoeffMinusOnAt_toFun (q : Mat d) (hq : IsUnit q)
    (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    (canonicalRespCoeffMinusOnAt q hq k w F a).toCoeffField = respCoeffMinus F a := by
  change (selectionRespCoeffMinusReg F a).toFun = respCoeffMinus F a
  exact selectionRespCoeffMinusReg_toFun F a

/-- Canonical Chapter-2 coefficient object for the plus transformed response field on the aligned
adapted subcell `adaptedCellAtCenter q k w`. -/
@[expose]
def canonicalRespCoeffPlusOnAt (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    Book.Ch02.CoeffOn (adaptedDomainAt q hq k w) :=
  responseCoeffOnFromSliceCover (adaptedDomainAt q hq k w) (selectionRespCoeffPlusReg F a)
    (exists_responseSlice_selectionRespCoeffPlusRegAt q hq k w F a)

@[simp] theorem canonicalRespCoeffPlusOnAt_toFun (q : Mat d) (hq : IsUnit q)
    (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    (canonicalRespCoeffPlusOnAt q hq k w F a).toCoeffField = respCoeffPlus F a := by
  change (selectionRespCoeffPlusReg F a).toFun = respCoeffPlus F a
  exact selectionRespCoeffPlusReg_toFun F a

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Integrability of the recentred child field on its own subcell

The cell-average head of the diagonal weak-norm estimate consumes an `AHarmonicFunction` that
already lives on an aligned adapted child `adaptedCellAtCenter q k w`, not on the parent
`HighContrast.adaptedCell q t`.  This module records, for the recentred coefficients
`respCoeffMinus F a` and `respCoeffPlus F a`, the three input facts on that child: integrability
of both slots of the doubled optimizer field, integrability of the scalar energy density, and
nonnegativity of its volume average.

The proofs are the parent-cell arguments re-instantiated at the child.  The elliptic
representative is the one already attached to the child
(`exists_elliptic_representative_respCoeffMinusAt`,
`exists_elliptic_representative_respCoeffPlusAt`),
so the restriction of an ellipticity statement from the parent is not needed; the generic
transport engines over an a.e. representative do all the work.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The recentred coefficient `a_- = respCoeffMinus F a` on its child -/

omit [NeZero d] in
/-- **Integrability of both slots of the doubled optimizer field on the child, for
`respCoeffMinus F a`.**  For an invertible grid `q` and an aligned adapted child
`adaptedCellAtCenter q k w`, both slots of the doubled optimizer field of an arbitrary
`AHarmonicFunction` attached to `respCoeffMinus F a` on that child are integrable there.  The
gradient slot needs no ellipticity; the flux slot uses the a.e.-elliptic representative on the
child. -/
theorem integrableOn_optimizerField_respCoeffMinus_at (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (v : AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter q k w)) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) v x).1 j) (adaptedCellAtCenter q
      k w) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) v x).2 j) (adaptedCellAtCenter
        q k w) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinusAt q hq k w F a
  have hVfin : volume (adaptedCellAtCenter q k w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top q k w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q k w)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w).isFiniteMeasure_restrict_volume
  have hflux : MemVectorL2 (adaptedCellAtCenter q k w)
      (fun x => matVecMul ((respCoeffMinus F a) x) (v.toH1.grad x)) :=
    memVectorL2_optimizerField_flux_of_aeEq subset_rfl hEll hae v
  refine ⟨integrableOn_optimizerField_fst_pub subset_rfl hVfin (respCoeffMinus F a) v j, ?_⟩
  have hmem : MemLp (fun x => (optimizerField (respCoeffMinus F a) v x).2 j) 2
      (volumeMeasureOn (adaptedCellAtCenter q k w)) := by
    simpa [optimizerField] using (MeasureTheory.memLp_pi_iff.mp hflux) j
  exact MemLp.integrable (by norm_num) hmem

/-! ## The transposed recentred coefficient `a_+ = respCoeffPlus F a` on its child -/

omit [NeZero d] in
/-- **Integrability of both slots of the doubled optimizer field on the child, for
`respCoeffPlus F a`.**  The transposed twin of
`integrableOn_optimizerField_respCoeffMinus_at`. -/
theorem integrableOn_optimizerField_respCoeffPlus_at (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (v : AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter q k w)) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) v x).1 j) (adaptedCellAtCenter q
      k w) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) v x).2 j) (adaptedCellAtCenter
        q k w) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlusAt q hq k w F a
  have hVfin : volume (adaptedCellAtCenter q k w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top q k w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q k w)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w).isFiniteMeasure_restrict_volume
  have hflux : MemVectorL2 (adaptedCellAtCenter q k w)
      (fun x => matVecMul ((respCoeffPlus F a) x) (v.toH1.grad x)) :=
    memVectorL2_optimizerField_flux_of_aeEq subset_rfl hEll hae v
  refine ⟨integrableOn_optimizerField_fst_pub subset_rfl hVfin (respCoeffPlus F a) v j, ?_⟩
  have hmem : MemLp (fun x => (optimizerField (respCoeffPlus F a) v x).2 j) 2
      (volumeMeasureOn (adaptedCellAtCenter q k w)) := by
    simpa [optimizerField] using (MeasureTheory.memLp_pi_iff.mp hflux) j
  exact MemLp.integrable (by norm_num) hmem

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cell energy layer

The metric square of the canonical state's average on one cell is controlled by the cell's
response size and the actual state energy there.  That is the statement proved below for an
arbitrary Chapter-2 cell; the aligned-subcell instance is its specialization.

## How the statement is expressed

The conclusion is stated with the `blockSqrt (respM0 F)` congruence
`blockVecDot (R v) (R v)` for the metric square, and with the two Loewner inputs `k` and `e`
for the two sizes `blockSize (adaptedResponse q k w a) E` and `diagonalWeakMetricFactor m E ^ 2`.
So the only genuinely new content at this layer is the STATE side:

1. the doubled optimizer state `X = (∇u, a∇u)` of `ResponseBlockObjects.lean` is a Chapter-2 doubled
  RESPONSE field;
2. its Chapter-2 energy density is exactly TWICE the optimizer energy density used here; the
  factor `2` is the doubled form `X · 𝐀 X = 2 ∇u · a ∇u`, and the same `2` relates
   `average … (blockVecDot state (𝐀 state))` to
   `diagonalWeakEnergy ^ 2 = variationEnergyValue` (`DiagonalWeakNormState.lean`);
3. `Book.Ch02.averageVec` and `cellAverage` (`ResponseBlockObjects.lean`) are the same
  function (`rfl`).

**The definitions `adaptedDomainAt`, `alignedIndex`, `coe_alignedIndex` and
`exists_restrict_solution_adaptedCellAtCenter` are NOT needed to state or prove the cell energy
bound**, because it is stated over an ARBITRARY `Book.Ch02.Domain d`.  They reappear only in
the aligned-subcell instance, where the subcell domain and the restriction do the work, and
where the geometric alignment fact `adaptedCellAtCenter q k w ⊆ adaptedCell q t` is taken as a
HYPOTHESIS rather than re-derived.

## No new definition

**This module introduces NO definition.**  The one definition it needs, `adaptedDomainAt` — the
per-`w` Chapter-2 domain of an aligned adapted subcell, the twin of `adaptedDomain`
 — is supplied by the imported
`ResponseFieldSize.lean`, together with its explicit `∃`
satisfiability witness, which therefore sits ABOVE every consumer here in import order.
That definition selects no constant: its two fields are the
INEQUALITY-free structural obligations `IsOpenBoundedConvexDomain` and `Nonempty`, both of which
are already proved for every `adaptedCellAtCenter`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open HCPolySupport.Book.Ch02
open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The doubled energy density of an optimizer state -/

omit [NeZero d] in
/-- `Book.Ch02.blockMatrixField` is the pointwise `blockMatrixOfCoeff` of the
representative — the two definitions (`Book/Ch02/Block.lean` and
`CoarseGraining/BlockFormalism/Structures.lean`) have identical bodies. -/
theorem blockMatrixField_apply {U : Domain d} (a : CoeffOn U) (x : Vec d) :
    blockMatrixField a x = blockMatrixOfCoeff (a.toCoeffField x) := rfl

omit [NeZero d] in
/-- **The doubled energy density of a primal state.**  On the doubled state `(ξ, Aξ)` the
Chapter-2 block form collapses to TWICE the scalar energy density:
`(ξ, Aξ) · 𝐀 (ξ, Aξ) = 2 ξ · Aξ`.

`blockMatVecMul_blockMatrixOfCoeff_primal_of_isUnit_det_symmPart`
(`CoarseGraining/BlockFormalism/MatrixIdentities.lean`) gives `𝐀 (ξ, Aξ) = (Aξ, ξ)` on the
nose; the rest is `blockVecDot`'s definition. -/
theorem blockEnergyDensity_primal {A : Mat d} (hdet : IsUnit (symmPart A).det) (ξ : Vec d) :
    blockVecDot ((ξ, matVecMul A ξ) : BlockVec d)
        (blockMatVecMul (blockMatrixOfCoeff A) ((ξ, matVecMul A ξ) : BlockVec d)) =
      2 * vecDot ξ (matVecMul A ξ) := by
  rw [blockMatVecMul_blockMatrixOfCoeff_primal_of_isUnit_det_symmPart A hdet ξ]
  change vecDot ξ (matVecMul A ξ) + vecDot (matVecMul A ξ) ξ = _
  rw [vecDot_comm (matVecMul A ξ) ξ]
  ring

/-! ## The state side — restriction, and membership in the doubled response space -/

omit [NeZero d] in
/-- **The doubled optimizer state lies in the cell's response space.**  Taking the adjoint
solution to be zero in `𝒮(U;a) = {(∇u + ∇u*, a∇u - aᵗ∇u*)}` gives `X = (∇u, a∇u) ∈ 𝒮(U;a)`. -/
theorem isDoubledResponseField_optimizerField {U : Domain d} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (u : Solution U a) :
    IsDoubledResponseField U a
      { potential := u.toH1.grad
        flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) } := by
  have h := Internal.Ch02.BookCh02.doubledFieldOfSolutions_mem_responseField_of_isEllipticFieldOn
    U a hEll u (zeroSolution U a.transpose)
  have hfield : doubledFieldOfSolutions a u (zeroSolution U a.transpose) =
      { potential := u.toH1.grad
        flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) } := by
    unfold doubledFieldOfSolutions
    have hzero : (zeroSolution U a.transpose).toH1.grad = 0 := rfl
    rw [hzero]
    congr 1
    · funext x
      show u.toH1.grad x + (0 : Vec d → Vec d) x = u.toH1.grad x
      simp
    · funext x
      show matVecMul (a.toCoeffField x) (u.toH1.grad x) -
          matVecMul (a.transpose.toCoeffField x) ((0 : Vec d → Vec d) x) =
        matVecMul (a.toCoeffField x) (u.toH1.grad x)
      rw [show ((0 : Vec d → Vec d) x) = (0 : Vec d) from rfl, matVecMul_zero, sub_zero]
  rwa [hfield] at h

/-! ## The carrier bridges — energy, and the cell average -/

omit [NeZero d] in
/-- **The Chapter-2 energy of an optimizer state is TWICE the scalar one.**  The doubled field
`Y = (∇u, a∇u)` has `⨍_U (Y · 𝐀 Y) = 2 ⨍_U ∇u · a∇u`, and the right-hand average is exactly the
integrand of `weakOptimizerEnergy` (`DiagonalDefectCarriers.lean`).

The pointwise step is the doubled energy identity above; it holds at every `x ∈ U` because
`hEll` makes `a(x)` elliptic there, and it is lifted to the average by
`Book.Ch02.average_eq_of_ae_eq` (`Book/Ch02/Dilation.lean`) along `ae_restrict_mem`. -/
theorem average_blockEnergyDensity_optimizerField {U : Domain d} (a : CoeffOn U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    (u : Solution U a) {Y : DoubledField d} (hpot : Y.potential = u.toH1.grad)
    (hflux : Y.flux = fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x)) :
    Book.Ch02.average U (fun x =>
        blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField a x) (Y.eval x))) =
      2 * volumeAverage (U : Set (Vec d))
        (fun x => vecDot (optimizerField a.toCoeffField u x).1
          (optimizerField a.toCoeffField u x).2) := by
  have hpt : Book.Ch02.average U (fun x =>
        blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField a x) (Y.eval x))) =
      Book.Ch02.average U (fun x =>
        2 * vecDot (optimizerField a.toCoeffField u x).1
          (optimizerField a.toCoeffField u x).2) := by
    refine Book.Ch02.average_eq_of_ae_eq ?_
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    have hdet : IsUnit (symmPart (a.toCoeffField x)).det :=
      isUnit_det_symmPart_of_isEllipticMatrix (hEll.2 x hx)
    have hY : Y.eval x =
        ((u.toH1.grad x, matVecMul (a.toCoeffField x) (u.toH1.grad x)) : BlockVec d) := by
      change (Y.potential x, Y.flux x) = _
      rw [hpot, hflux]
    rw [hY, blockMatrixField_apply a x,
      blockEnergyDensity_primal hdet (u.toH1.grad x)]
    rfl
  rw [hpt]
  change (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ x in (U : Set (Vec d)), 2 * vecDot (optimizerField a.toCoeffField u x).1
        (optimizerField a.toCoeffField u x).2 ∂MeasureTheory.volume = _
  rw [MeasureTheory.integral_const_mul]
  change _ = 2 * ((MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ * _)
  ring

omit [NeZero d] in
/-- `weakOptimizerEnergy` squared is the average it is the square root of, as soon as
that average is nonnegative. -/
theorem weakOptimizerEnergy_sq {V : Set (Vec d)} {b : CoeffField d}
    (u : AHarmonicFunction b V)
    (hnn : 0 ≤ volumeAverage V (fun x => vecDot (optimizerField b u x).1
      (optimizerField b u x).2)) :
    weakOptimizerEnergy V b u ^ 2 =
      volumeAverage V (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2) :=
  Real.sq_sqrt hnn

omit [NeZero d] in
/-- **The cell average IS the Chapter-2 pair of vector averages.**  `cellAverage`
(`ResponseBlockObjects.lean`) and `Book.Ch02.averageVec` (`Book/Ch02/Response.lean`) have identical
bodies once `Book.Ch02.average` is unfolded to `volumeAverage`, so this is `rfl` after the two
field rewrites. -/
theorem averageVec_pair_eq_cellAverage {U : Domain d} {b : CoeffField d}
    (u : AHarmonicFunction b (U : Set (Vec d))) {Y : DoubledField d}
    (hpot : Y.potential = u.toH1.grad)
    (hflux : Y.flux = fun x => matVecMul (b x) (u.toH1.grad x)) :
    ((Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux) : BlockVec d) =
      cellAverage (U : Set (Vec d)) (optimizerField b u) := by
  rw [hpot, hflux]
  rfl

/-! ## The cell-energy bound on an arbitrary Chapter-2 cell -/

omit [NeZero d] in
/-- **The cell energy bound.**  *"The metric square of the canonical state's average on one
cell is controlled by the cell's response size and the actual state energy there."*

It is stated over an ARBITRARY Chapter-2 cell `U`, so that both the parent cell
`adaptedDomain q hq t` and every aligned subcell are
instances.

The three encodings it replaces:

* `metricBlockNormSq m (…)` becomes the `blockSqrt (respM0 F)` congruence
  `blockVecDot (R v) (R v)` (`RecentScaleEnergyRoute.lean`);
* `diagonalWeakMetricFactor m E ^ 2` becomes the Loewner input `k`
  (`SharpOrderEnergyMap.lean`);
* `blockSize (adaptedResponse q k w a) E` becomes the Loewner input `e`.

The `2` is the doubled quadratic form: the average identity above shows
`⨍_U (X · 𝐀 X) = 2 ⨍_U ∇u · a∇u`, and `weakOptimizerEnergy ^ 2` is the second average.  The
same `2` relates `average … (blockVecDot state (𝐀 state))` to
`diagonalWeakEnergy ^ 2 = variationEnergyValue` (`DiagonalWeakNormState.lean`). -/
theorem blockSq_cellAverage_optimizerField_le {U : Domain d} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (u : Solution U a)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef)
    {E : BlockMat d} (hE : (toFullBlockMat E).PosDef) {k e : ℝ} (hk : 0 < k) (he : 0 < e)
    (hEM : toFullBlockMat E ≤ k • toFullBlockMat (respM0 F))
    (hAE : toFullBlockMat (Book.Ch02.coarseBlockMatrix U a) ≤ e • toFullBlockMat E) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (U : Set (Vec d)) (optimizerField a.toCoeffField u)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (U : Set (Vec d)) (optimizerField a.toCoeffField u))) ≤
      (k * e) * (2 * weakOptimizerEnergy (U : Set (Vec d)) a.toCoeffField u ^ 2) := by
  have hY : IsDoubledResponseField U a
      { potential := u.toH1.grad
        flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) } :=
    isDoubledResponseField_optimizerField a hEll u
  have hmain := energy_map_respM0_le_coarseStarred a hEll hY hm hE hk he hEM hAE
  rw [averageVec_pair_eq_cellAverage (U := U) (b := a.toCoeffField) u
        (Y := { potential := u.toH1.grad
                flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) }) rfl rfl,
    average_blockEnergyDensity_optimizerField a hEll u
      (Y := { potential := u.toH1.grad
              flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) }) rfl rfl] at hmain
  have hnn : 0 ≤ volumeAverage (U : Set (Vec d))
      (fun x => vecDot (optimizerField a.toCoeffField u x).1
        (optimizerField a.toCoeffField u x).2) := by
    have hlhs := blockVecDot_nonneg
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (U : Set (Vec d)) (optimizerField a.toCoeffField u)))
    have hke : 0 < k * e := mul_pos hk he
    nlinarith only [hlhs, hmain, hke]
  rw [weakOptimizerEnergy_sq u hnn]
  exact hmain

/-! ## The aligned-subcell instance

The cell energy bound above is stated over an arbitrary Chapter-2 cell, so the only thing an
aligned subcell needs is its Chapter-2 domain, `adaptedDomainAt`.  **That definition is NOT
introduced here.**  It and its satisfiability witness live in
`ResponseFieldSize.lean`, which this module imports, so
the witness sits strictly ABOVE every consumer in import order.

The copy of `adaptedDomainAt` that stood here has been deleted as a duplicate.  The two copies
were signature-identical and differed only in how the `Nonempty` field was proved, which is a
`Prop`.  **This module now introduces NO definition of its own.** -/

omit [NeZero d] in
/-- **The cell energy bound on an aligned adapted subcell, for the PARENT optimizer.**  The
left-hand side is the cell average of the PARENT state
`X_t = (∇u, a∇u)` over the subcell, and the right-hand side is the actual state energy THERE,
carried by the restricted solution `z` (`hz : z.grad = u.grad`).

The `obtain ⟨z, hz⟩ := exists_restrict_solution_adaptedCellAtCenter …` step is exactly `hz` here.
The geometric alignment fact `adaptedCellAtCenter q k w ⊆ adaptedCell q t` is NOT re-derived here:
it is taken as a hypothesis, and this statement does not need it at all, because `hz` already
carries its consequence. -/
theorem blockSq_cellAverage_optimizerField_adaptedCellAtCenter_le
    {q : Mat d} {hq : IsUnit q} {k : ℤ} {w : Fin d → ℤ}
    (a : CoeffOn (adaptedDomainAt q hq k w))
    (hEll : IsEllipticFieldOn a.lam a.Lam (adaptedCellAtCenter q k w) a.toCoeffField)
    {V : Set (Vec d)} (u : AHarmonicFunction a.toCoeffField V)
    (z : Solution (adaptedDomainAt q hq k w) a) (hz : z.toH1.grad = u.toH1.grad)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef)
    {E : BlockMat d} (hE : (toFullBlockMat E).PosDef) {c e : ℝ} (hc : 0 < c) (he : 0 < e)
    (hEM : toFullBlockMat E ≤ c • toFullBlockMat (respM0 F))
    (hAE : toFullBlockMat
        (Book.Ch02.coarseBlockMatrix (adaptedDomainAt q hq k w) a) ≤ e • toFullBlockMat E) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter q k w) (optimizerField a.toCoeffField u)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter q k w) (optimizerField a.toCoeffField u))) ≤
      (c * e) *
        (2 * weakOptimizerEnergy (adaptedCellAtCenter q k w) a.toCoeffField z ^ 2) := by
  have hfield : optimizerField a.toCoeffField z = optimizerField a.toCoeffField u := by
    funext x
    change (z.toH1.grad x, matVecMul (a.toCoeffField x) (z.toH1.grad x)) = _
    rw [hz]
    rfl
  have h := blockSq_cellAverage_optimizerField_le a hEll z hm hE hc he hEM hAE
  rwa [hfield] at h

end

end HCPolySupport.HighContrast.Multiscale
end
