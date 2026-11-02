/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.Assembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.MatrixNorms
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.W1Infinity
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.GradientW1Infinity
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure

/-!
# UnitCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Lipschitz representatives at the frozen unit-cube `W^{2,∞}` carrier

The carrier of `Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity` is the
*open* unit triadic cube `cubeDomain (originCube d 0)`, which is a bounded open
convex domain, so the bridge of
`Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.Assembly` applies
directly.  This module discharges its hypotheses from the frozen fields and
records the two consumer corollaries:

* `exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value`: every entry of the
  matrix field has a globally `d * h.w1Infinity`-Lipschitz representative;
* `exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_firstDeriv`: every entry of the
  first-derivative field has a globally `d * h.gradientW1Infinity`-Lipschitz
  representative.

Both are stated pointwise (an oscillation bound valid for every pair of points
and an a.e. identification with the frozen entry function), which is the form
the `D_h`-bound assembly and the Besov estimates consume.

The `L^∞` finiteness that gives `w1Infinity` and `gradientW1Infinity` their
meaning is *derived* here from the entrywise `L^∞` memberships stored in the
frozen structure, via `MatrixNorms`; it is never assumed.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz

open HCPolySupport HCPolySupport.Book.Ch02 Algsuperdiff.Frozen.Section24 MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

variable {d : ℕ}

/-! ## `L^∞` bookkeeping -/

/-- An a.e. uniform bound on an a.e. strongly measurable function makes the
essential supremum finite. -/
theorem eLpNorm_top_ne_top_of_ae_abs_le {μ : Measure (Vec d)} {F : Vec d → ℝ} {C : ℝ}
    (hFm : AEStronglyMeasurable F μ)
    (hF : ∀ᵐ x ∂μ, |F x| ≤ C) : eLpNorm F ∞ μ ≠ ⊤ := by
  rw [MeasureTheory.eLpNorm_exponent_top hFm]
  exact (MeasureTheory.eLpNormEssSup_lt_top_of_ae_bound (C := C)
    (by simpa [Real.norm_eq_abs] using hF)).ne

/-- A finite essential supremum is an a.e. pointwise bound. -/
theorem ae_abs_le_toReal_eLpNorm_top {μ : Measure (Vec d)} {F : Vec d → ℝ}
    (hfin : eLpNorm F ∞ μ ≠ ⊤) :
    ∀ᵐ x ∂μ, |F x| ≤ ENNReal.toReal (eLpNorm F ∞ μ) := by
  have hle : ∀ᵐ x ∂μ, ‖F x‖ₑ ≤ eLpNorm F ∞ μ := by
    rw [MeasureTheory.eLpNorm_exponent_top (aestronglyMeasurable_of_eLpNorm_ne_top hfin)]
    exact MeasureTheory.ae_le_eLpNormEssSup
  filter_upwards [hle] with x hx
  have := ENNReal.toReal_mono hfin hx
  simpa [Real.norm_eq_abs] using this

/-! ## Measurability of the frozen derivative norms -/

private theorem matrixNorm_add_le (A B : Mat d) :
    matrixNorm (A + B) ≤ matrixNorm A + matrixNorm B := by
  rw [matrixNorm_eq_matrixOperatorNorm, matrixNorm_eq_matrixOperatorNorm,
    matrixNorm_eq_matrixOperatorNorm]
  have h := matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub (A + B) A
  rwa [add_sub_cancel_left] at h

/-- The frozen first-derivative norm is Lipschitz for the operator norm. -/
theorem matrixDerivativeNorm_le_add_sq_mul_norm_sub (D E : Vec d →L[ℝ] Mat d) :
    matrixDerivativeNorm D ≤ matrixDerivativeNorm E + (d : ℝ) ^ 2 * ‖D - E‖ := by
  refine csSup_le (matrixDerivativeNorm_range_nonempty D) ?_
  rintro c ⟨v, rfl⟩
  calc matrixNorm (D v.1) = matrixNorm (E v.1 + (D - E) v.1) := by
        rw [show (D - E) v.1 = D v.1 - E v.1 from rfl]
        congr 1
        abel
    _ ≤ matrixNorm (E v.1) + matrixNorm ((D - E) v.1) := matrixNorm_add_le _ _
    _ ≤ matrixDerivativeNorm E + matrixDerivativeNorm (D - E) :=
        add_le_add (matrixNorm_apply_le_matrixDerivativeNorm E v.1 v.2)
          (matrixNorm_apply_le_matrixDerivativeNorm (D - E) v.1 v.2)
    _ ≤ matrixDerivativeNorm E + (d : ℝ) ^ 2 * ‖D - E‖ :=
        add_le_add le_rfl (matrixDerivativeNorm_le_sq_mul_norm (D - E))

theorem continuous_matrixDerivativeNorm :
    Continuous (matrixDerivativeNorm : (Vec d →L[ℝ] Mat d) → ℝ) := by
  refine (LipschitzWith.of_le_add_mul' ((d : ℝ) ^ 2) fun D E => ?_).continuous
  rw [dist_eq_norm]
  exact matrixDerivativeNorm_le_add_sq_mul_norm_sub D E

/-- The frozen second-derivative norm is Lipschitz for the operator norm. -/
theorem matrixSecondDerivativeNorm_le_add_sq_mul_norm_sub
    (H K : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :
    matrixSecondDerivativeNorm H ≤ matrixSecondDerivativeNorm K + (d : ℝ) ^ 2 * ‖H - K‖ := by
  refine csSup_le (matrixSecondDerivativeNorm_range_nonempty H) ?_
  rintro c ⟨v, rfl⟩
  have hv : ‖v.1‖ ≤ 1 := (norm_vec_le_vecNorm v.1).trans v.2
  have hHK : ‖H v.1 - K v.1‖ ≤ ‖H - K‖ := by
    rw [show H v.1 - K v.1 = (H - K) v.1 from rfl]
    exact ((H - K).le_opNorm v.1).trans (mul_le_of_le_one_right (norm_nonneg _) hv)
  calc matrixDerivativeNorm (H v.1)
      ≤ matrixDerivativeNorm (K v.1) + (d : ℝ) ^ 2 * ‖H v.1 - K v.1‖ :=
        matrixDerivativeNorm_le_add_sq_mul_norm_sub _ _
    _ ≤ matrixSecondDerivativeNorm K + (d : ℝ) ^ 2 * ‖H - K‖ :=
        add_le_add (matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm K v.1 v.2)
          (mul_le_mul_of_nonneg_left hHK (sq_nonneg _))

theorem continuous_matrixSecondDerivativeNorm :
    Continuous (matrixSecondDerivativeNorm : (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) → ℝ) := by
  refine (LipschitzWith.of_le_add_mul' ((d : ℝ) ^ 2) fun H K => ?_).continuous
  rw [dist_eq_norm]
  exact matrixSecondDerivativeNorm_le_add_sq_mul_norm_sub H K

/-- A field of continuous linear maps on `Vec d` is in `L^p` as soon as its values
on the coordinate directions are. -/
theorem memLp_clm_of_basisVec {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {p : ℝ≥0∞} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : α → Vec d →L[ℝ] F} (h : ∀ l : Fin d, MemLp (fun y => L y (basisVec l)) p μ) :
    MemLp L p μ := by
  classical
  let e := ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := F) (Fin d)
  have hA : MemLp (fun y => fun l : Fin d => L y (basisVec l)) p μ := memLp_pi_iff.2 h
  have hL : L = (e.symm : (Fin d → F) →L[ℝ] (Vec d →L[ℝ] F)) ∘
      fun y => fun l : Fin d => L y (basisVec l) := by
    funext y
    exact (e.symm_apply_apply (L y)).symm
  rw [hL]
  exact (e.symm : (Fin d → F) →L[ℝ] (Vec d →L[ℝ] F)).comp_memLp' hA

/-- Entrywise `L^p` membership of a derivative field gives `L^p` membership of
the field itself. -/
theorem memLp_matrixDerivative_of_entries {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} {p : ℝ≥0∞} {D : α → Vec d →L[ℝ] Mat d}
    (hmem : ∀ k i j : Fin d, MemLp (fun x => D x (basisVec k) i j) p μ) :
    MemLp D p μ :=
  memLp_clm_of_basisVec fun k =>
    memLp_pi_iff.2 fun i => memLp_pi_iff.2 fun j => hmem k i j

/-- A derivative field with entrywise `L^∞` entries has an a.e. strongly
measurable frozen derivative norm. -/
theorem aestronglyMeasurable_matrixDerivativeNorm_of_memLp
    {U : Set (Vec d)} {D : Vec d → Vec d →L[ℝ] Mat d}
    (hmem : ∀ k i j : Fin d, MemLp (fun x => D x (basisVec k) i j) ∞ (volumeMeasureOn U)) :
    AEStronglyMeasurable (fun y => matrixDerivativeNorm (D y)) (volumeMeasureOn U) :=
  continuous_matrixDerivativeNorm.comp_aestronglyMeasurable
    (memLp_matrixDerivative_of_entries hmem).aestronglyMeasurable

/-- Second-derivative analogue of
`aestronglyMeasurable_matrixDerivativeNorm_of_memLp`. -/
theorem aestronglyMeasurable_matrixSecondDerivativeNorm_of_memLp
    {U : Set (Vec d)} {H : Vec d → Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)}
    (hmem : ∀ l k i j : Fin d,
      MemLp (fun x => H x (basisVec l) (basisVec k) i j) ∞ (volumeMeasureOn U)) :
    AEStronglyMeasurable (fun y => matrixSecondDerivativeNorm (H y)) (volumeMeasureOn U) :=
  continuous_matrixSecondDerivativeNorm.comp_aestronglyMeasurable
    (memLp_clm_of_basisVec fun l =>
      memLp_matrixDerivative_of_entries fun k i j => hmem l k i j).aestronglyMeasurable

/-! ## Entrywise a.e. bounds through the frozen derivative norms -/

/-- Every coordinate entry of a derivative field is bounded a.e. by the
essential supremum of the frozen first-derivative norm, whose finiteness follows
from the entrywise `L^∞` memberships. -/
theorem ae_abs_apply_le_toReal_eLpNorm_matrixDerivativeNorm
    {U : Set (Vec d)} {D : Vec d → Vec d →L[ℝ] Mat d}
    (hmem : ∀ k i j : Fin d, MemLp (fun x => D x (basisVec k) i j) ∞ (volumeMeasureOn U))
    (k i j : Fin d) :
    ∀ᵐ x ∂ volumeMeasureOn U,
      |D x (basisVec k) i j| ≤
        ENNReal.toReal (eLpNorm (fun y => matrixDerivativeNorm (D y)) ∞ (volumeMeasureOn U)) := by
  classical
  have hall : ∀ᵐ x ∂ volumeMeasureOn U, ∀ k' i' j' : Fin d,
      |D x (basisVec k') i' j'| ≤
        ENNReal.toReal (eLpNorm (fun y => D y (basisVec k') i' j') ∞ (volumeMeasureOn U)) := by
    rw [MeasureTheory.ae_all_iff]
    intro k'
    rw [MeasureTheory.ae_all_iff]
    intro i'
    rw [MeasureTheory.ae_all_iff]
    intro j'
    exact ae_abs_le_toReal_eLpNorm_top (hmem k' i' j').eLpNorm_lt_top.ne
  have hbd : ∀ᵐ x ∂ volumeMeasureOn U, |matrixDerivativeNorm (D x)| ≤
      (d : ℝ) ^ 2 * ∑ k' : Fin d, ∑ i' : Fin d, ∑ j' : Fin d,
        ENNReal.toReal (eLpNorm (fun y => D y (basisVec k') i' j') ∞ (volumeMeasureOn U)) := by
    filter_upwards [hall] with x hx
    rw [abs_of_nonneg (matrixDerivativeNorm_nonneg _)]
    refine (matrixDerivativeNorm_le_sq_mul_sum (D x)).trans ?_
    gcongr with k' _ i' _ j' _
    exact hx k' i' j'
  filter_upwards [ae_abs_le_toReal_eLpNorm_top
    (eLpNorm_top_ne_top_of_ae_abs_le
      (aestronglyMeasurable_matrixDerivativeNorm_of_memLp hmem) hbd)] with x hx
  exact (abs_entry_apply_le_matrixDerivativeNorm (D x) k i j).trans ((le_abs_self _).trans hx)

/-- Second-derivative analogue of
`ae_abs_apply_le_toReal_eLpNorm_matrixDerivativeNorm`. -/
theorem ae_abs_apply_apply_le_toReal_eLpNorm_matrixSecondDerivativeNorm
    {U : Set (Vec d)} {H : Vec d → Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)}
    (hmem : ∀ l k i j : Fin d,
      MemLp (fun x => H x (basisVec l) (basisVec k) i j) ∞ (volumeMeasureOn U))
    (l k i j : Fin d) :
    ∀ᵐ x ∂ volumeMeasureOn U,
      |H x (basisVec l) (basisVec k) i j| ≤
        ENNReal.toReal
          (eLpNorm (fun y => matrixSecondDerivativeNorm (H y)) ∞ (volumeMeasureOn U)) := by
  classical
  have hall : ∀ᵐ x ∂ volumeMeasureOn U, ∀ l' k' i' j' : Fin d,
      |H x (basisVec l') (basisVec k') i' j'| ≤
        ENNReal.toReal
          (eLpNorm (fun y => H y (basisVec l') (basisVec k') i' j') ∞ (volumeMeasureOn U)) := by
    rw [MeasureTheory.ae_all_iff]
    intro l'
    rw [MeasureTheory.ae_all_iff]
    intro k'
    rw [MeasureTheory.ae_all_iff]
    intro i'
    rw [MeasureTheory.ae_all_iff]
    intro j'
    exact ae_abs_le_toReal_eLpNorm_top (hmem l' k' i' j').eLpNorm_lt_top.ne
  have hbd : ∀ᵐ x ∂ volumeMeasureOn U, |matrixSecondDerivativeNorm (H x)| ≤
      (d : ℝ) ^ 2 * ∑ l' : Fin d, ∑ k' : Fin d, ∑ i' : Fin d, ∑ j' : Fin d,
        ENNReal.toReal
          (eLpNorm (fun y => H y (basisVec l') (basisVec k') i' j') ∞ (volumeMeasureOn U)) := by
    filter_upwards [hall] with x hx
    rw [abs_of_nonneg (matrixSecondDerivativeNorm_nonneg _)]
    refine (matrixSecondDerivativeNorm_le_sq_mul_sum (H x)).trans ?_
    gcongr with l' _ k' _ i' _ j' _
    exact hx l' k' i' j'
  filter_upwards [ae_abs_le_toReal_eLpNorm_top
    (eLpNorm_top_ne_top_of_ae_abs_le
      (aestronglyMeasurable_matrixSecondDerivativeNorm_of_memLp hmem) hbd)] with x hx
  exact (abs_entry_apply_apply_le_matrixSecondDerivativeNorm (H x) l k i j).trans
    ((le_abs_self _).trans hx)

/-! ## The frozen unit-cube norms -/

theorem w1Infinity_nonneg (h : UnitCubeSkewW2Infinity d) : 0 ≤ h.w1Infinity := by
  simp only [UnitCubeSkewW2Infinity.w1Infinity]
  exact le_trans ENNReal.toReal_nonneg (le_max_left _ _)

theorem gradientW1Infinity_nonneg (h : UnitCubeSkewW2Infinity d) :
    0 ≤ h.gradientW1Infinity := by
  simp only [UnitCubeSkewW2Infinity.gradientW1Infinity]
  exact le_trans ENNReal.toReal_nonneg (le_max_left _ _)

theorem toReal_eLpNorm_matrixDerivativeNorm_le_w1Infinity (h : UnitCubeSkewW2Infinity d) :
    ENNReal.toReal (eLpNorm (fun x => matrixDerivativeNorm (h.firstDeriv x)) ∞
        (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))) ≤
      h.w1Infinity := by
  simp only [UnitCubeSkewW2Infinity.w1Infinity]
  exact le_max_left _ _

theorem toReal_eLpNorm_matrixSecondDerivativeNorm_le_gradientW1Infinity
    (h : UnitCubeSkewW2Infinity d) :
    ENNReal.toReal (eLpNorm (fun x => matrixSecondDerivativeNorm (h.secondDeriv x)) ∞
        (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))) ≤
      h.gradientW1Infinity := by
  simp only [UnitCubeSkewW2Infinity.gradientW1Infinity]
  exact le_max_left _ _

/-! ## Entrywise a.e. derivative bounds at the frozen carrier -/

theorem ae_abs_firstDeriv_le_w1Infinity (h : UnitCubeSkewW2Infinity d) (k i j : Fin d) :
    ∀ᵐ x ∂ volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      |h.firstDeriv x (basisVec k) i j| ≤ h.w1Infinity := by
  filter_upwards [ae_abs_apply_le_toReal_eLpNorm_matrixDerivativeNorm
    (D := h.firstDeriv) (fun k' i' j' => h.firstDeriv_memLp k' i' j') k i j] with x hx
  exact hx.trans (toReal_eLpNorm_matrixDerivativeNorm_le_w1Infinity h)

theorem ae_abs_secondDeriv_le_gradientW1Infinity (h : UnitCubeSkewW2Infinity d)
    (l k i j : Fin d) :
    ∀ᵐ x ∂ volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      |h.secondDeriv x (basisVec l) (basisVec k) i j| ≤ h.gradientW1Infinity := by
  filter_upwards [ae_abs_apply_apply_le_toReal_eLpNorm_matrixSecondDerivativeNorm
    (H := h.secondDeriv) (fun l' k' i' j' => h.secondDeriv_memLp l' k' i' j') l k i j] with x hx
  exact hx.trans (toReal_eLpNorm_matrixSecondDerivativeNorm_le_gradientW1Infinity h)

/-! ## The consumer corollaries -/

/-- **Lipschitz representative of a frozen unit-cube matrix-field entry.** -/
theorem exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value
    (h : UnitCubeSkewW2Infinity d) (i j : Fin d) :
    ∃ v : Vec d → ℝ,
      (∀ x y : Vec d, ‖v x - v y‖ ≤ (d : ℝ) * h.w1Infinity * ‖x - y‖) ∧
        v =ᵐ[volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))]
          fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j :=
  exists_lipschitz_ae_eq_of_hasWeakPartialDeriv_bound
    (U := ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (u := fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j)
    (g := fun k x => h.firstDeriv x (basisVec k) i j)
    (B := h.w1Infinity)
    (cubeDomain (originCube d 0)).isDomain
    (w1Infinity_nonneg h)
    (h.toLInfSkewMatrixFieldOn.1.2 i j)
    (fun k => h.firstDeriv_memLp k i j)
    (fun k => ae_abs_firstDeriv_le_w1Infinity h k i j)
    (fun k => h.hasWeakPartialDeriv_value k i j)

/-- **Lipschitz representative of a frozen unit-cube first-derivative entry.** -/
theorem exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_firstDeriv
    (h : UnitCubeSkewW2Infinity d) (k i j : Fin d) :
    ∃ v : Vec d → ℝ,
      (∀ x y : Vec d, ‖v x - v y‖ ≤ (d : ℝ) * h.gradientW1Infinity * ‖x - y‖) ∧
        v =ᵐ[volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))]
          fun x => h.firstDeriv x (basisVec k) i j :=
  exists_lipschitz_ae_eq_of_hasWeakPartialDeriv_bound
    (U := ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (u := fun x => h.firstDeriv x (basisVec k) i j)
    (g := fun l x => h.secondDeriv x (basisVec l) (basisVec k) i j)
    (B := h.gradientW1Infinity)
    (cubeDomain (originCube d 0)).isDomain
    (gradientW1Infinity_nonneg h)
    (h.firstDeriv_memLp k i j)
    (fun l => h.secondDeriv_memLp l k i j)
    (fun l => ae_abs_secondDeriv_le_gradientW1Infinity h l k i j)
    (fun l => h.hasWeakPartialDeriv_firstDeriv l k i j)

/-! ## Half-open cube form

The frozen carrier lives on the *open* unit cube, while the Besov and cube
average machinery integrates over the half-open realization `cubeSet`.  The two
restricted measures coincide, so the a.e. identifications transfer verbatim. -/

/-- Half-open-cell form of
`exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value`. -/
theorem exists_lipschitz_ae_eq_cubeSet_unitCubeSkewW2Infinity_value
    (h : UnitCubeSkewW2Infinity d) (i j : Fin d) :
    ∃ v : Vec d → ℝ,
      (∀ x y : Vec d, ‖v x - v y‖ ≤ (d : ℝ) * h.w1Infinity * ‖x - y‖) ∧
        v =ᵐ[volumeMeasureOn (cubeSet (originCube d 0))]
          fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j := by
  obtain ⟨v, hlip, heq⟩ := exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value h i j
  refine ⟨v, hlip, ?_⟩
  rwa [volumeMeasureOn, HCPolySupport.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- Half-open-cell form of
`exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_firstDeriv`. -/
theorem exists_lipschitz_ae_eq_cubeSet_unitCubeSkewW2Infinity_firstDeriv
    (h : UnitCubeSkewW2Infinity d) (k i j : Fin d) :
    ∃ v : Vec d → ℝ,
      (∀ x y : Vec d, ‖v x - v y‖ ≤ (d : ℝ) * h.gradientW1Infinity * ‖x - y‖) ∧
        v =ᵐ[volumeMeasureOn (cubeSet (originCube d 0))]
          fun x => h.firstDeriv x (basisVec k) i j := by
  obtain ⟨v, hlip, heq⟩ := exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_firstDeriv h k i j
  refine ⟨v, hlip, ?_⟩
  rwa [volumeMeasureOn, HCPolySupport.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
