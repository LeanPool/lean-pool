/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.Cube
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# The lattice `ℤ² ⊂ ℂ`, its cells and `ℤ²`-periodic functions on `ℂ`

* The lattice points `n₀ + i n₁` (`HarmonicAnalysis.latticePoint`): additivity, and
  `‖n‖_∞ ≤ |n₀ + i n₁|` (`HarmonicAnalysis.norm_le_norm_latticePoint`); the series
  `Σ_{n ∈ ℤ²} ‖n‖_∞^{−3}` converges (`HarmonicAnalysis.summable_inv_norm_pow_three`).
* The translates `j + (−½, ½]²`, `j ∈ ℤ²`, tile `ℂ`:
  `∫_ℂ h = Σ_j ∫_{(−½, ½]²} h (y + j) dy` for integrable `h`
  (`HarmonicAnalysis.hasSum_integral_centredCell_add`).
* Fourier coefficients on `𝕋²` as integrals over the centred cell
  (`HarmonicAnalysis.mFourierCoeff_eq_integral_centredCell`).
* A `ℤ²`-periodic function `g` on `ℂ` descends to `𝕋²` (`HarmonicAnalysis.torusLift`), with
  `torusLift g (ofComplex y) = g y`; it is continuous when `g` is, since `ofComplex` is an open
  quotient map (`HarmonicAnalysis.isOpenQuotientMap_ofComplex`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Complex
open scoped ComplexConjugate Real ENNReal

namespace HarmonicAnalysis

open UnitAddTorus

/-! ### Lattice points -/

@[simp]
theorem latticePoint_re (n : Fin 2 → ℤ) : (latticePoint n).re = n 0 := by
  simp [latticePoint]

@[simp]
theorem latticePoint_im (n : Fin 2 → ℤ) : (latticePoint n).im = n 1 := by
  simp [latticePoint]

theorem latticePoint_add (m n : Fin 2 → ℤ) :
    latticePoint (m + n) = latticePoint m + latticePoint n := by
  apply Complex.ext <;> simp

@[simp]
theorem latticePoint_zero : latticePoint 0 = 0 := by
  apply Complex.ext <;> simp

theorem latticePoint_neg (n : Fin 2 → ℤ) : latticePoint (-n) = -latticePoint n := by
  apply Complex.ext <;> simp

/-- `‖n‖_∞ ≤ |n₀ + i n₁|`. -/
theorem norm_le_norm_latticePoint (n : Fin 2 → ℤ) : ‖n‖ ≤ ‖latticePoint n‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  fin_cases i
  · simpa [Int.norm_eq_abs] using abs_re_le_norm (latticePoint n)
  · simpa [Int.norm_eq_abs] using abs_im_le_norm (latticePoint n)

/-- The projection `ℂ → 𝕋²` is `ℤ²`-periodic. -/
theorem ofComplex_add_latticePoint (y : ℂ) (k : Fin 2 → ℤ) :
    ofComplex (y + latticePoint k) = ofComplex y := by
  have h : ![(y + latticePoint k).re, (y + latticePoint k).im] =
      ![y.re, y.im] + fun i => (k i : ℝ) := by
    funext i
    fin_cases i <;> simp
  rw [ofComplex, h, ofPi_add_int, ofComplex]

/-- `Σ_{n ∈ ℤ²} ‖n‖_∞^{−3}` converges (the term `n = 0` is `0`). -/
theorem summable_inv_norm_pow_three : Summable fun n : Fin 2 → ℤ => (‖n‖ ^ 3)⁻¹ := by
  refine (EisensteinSeries.summable_one_div_norm_rpow (k := 3) (by norm_num)).congr fun n => ?_
  rw [Real.rpow_neg (norm_nonneg _), show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]

/-! ### The tiling of `ℂ` by the translates of the centred cell -/

/-- The centred cell lies in the closed unit disc. -/
theorem centredCell_subset_closedBall : centredCell ⊆ Metric.closedBall (0 : ℂ) 1 := by
  intro y hy
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
  rw [mem_closedBall_zero_iff]
  have h5 : |y.re| ≤ 2⁻¹ := abs_le.2 ⟨h1.le, h2⟩
  have h6 : |y.im| ≤ 2⁻¹ := abs_le.2 ⟨h3.le, h4⟩
  linarith [norm_le_abs_re_add_abs_im y]

/-- The centred cell has finite measure. -/
theorem volume_centredCell_lt_top : volume centredCell < ∞ :=
  (measure_mono centredCell_subset_closedBall).trans_lt measure_closedBall_lt_top

/-- An integer in `(−1, 1)` is `0`. -/
private theorem int_eq_zero_of_abs_lt_one {m : ℤ} (h1 : -1 < (m : ℝ)) (h2 : (m : ℝ) < 1) :
    m = 0 := by
  have h1' : -1 < m := by exact_mod_cast h1
  have h2' : m < 1 := by exact_mod_cast h2
  omega

/-- The translates `j + (−½, ½]²`, `j ∈ ℤ²`, of the centred cell tile `ℂ`: for integrable `h`,
`∫_ℂ h = Σ_{j ∈ ℤ²} ∫_{(−½, ½]²} h (y + j) dy`. -/
theorem hasSum_integral_centredCell_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℂ → E} (hh : Integrable h) :
    HasSum (fun k : Fin 2 → ℤ => ∫ y in centredCell, h (y + latticePoint k)) (∫ y, h y) := by
  set s : (Fin 2 → ℤ) → Set ℂ := fun k => (fun y => y - latticePoint k) ⁻¹' centredCell
  have hm : ∀ k, MeasurableSet (s k) := fun k =>
    measurableSet_centredCell.preimage (measurable_id.sub_const _)
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro j k hjk
    refine Set.disjoint_left.2 fun y hj hk => hjk ?_
    simp only [s, mem_preimage, centredCell, mem_ofPred_eq, mem_Ioc, sub_re, sub_im,
      latticePoint_re, latticePoint_im] at hj hk
    funext i
    fin_cases i
    · have := int_eq_zero_of_abs_lt_one (m := j 0 - k 0) (by push_cast; linarith)
        (by push_cast; linarith)
      simp only [Fin.zero_eta, Fin.isValue]
      omega
    · have := int_eq_zero_of_abs_lt_one (m := j 1 - k 1) (by push_cast; linarith)
        (by push_cast; linarith)
      simp only [Fin.mk_one, Fin.isValue]
      omega
  have hU : (⋃ k, s k) = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ⟨![⌈y.re - 2⁻¹⌉, ⌈y.im - 2⁻¹⌉], ?_⟩
    simp only [s, mem_preimage, centredCell, mem_ofPred_eq, mem_Ioc, sub_re, sub_im,
      latticePoint_re, latticePoint_im, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 := Int.le_ceil (y.re - 2⁻¹)
    have h2 := Int.ceil_lt_add_one (y.re - 2⁻¹)
    have h3 := Int.le_ceil (y.im - 2⁻¹)
    have h4 := Int.ceil_lt_add_one (y.im - 2⁻¹)
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hsum := hasSum_integral_iUnion hm hd (hh.integrableOn (s := ⋃ k, s k))
  rw [hU, Measure.restrict_univ] at hsum
  refine hsum.congr_fun fun k => ?_
  have hpre : (fun y => y + latticePoint k) ⁻¹' s k = centredCell := by
    ext y
    simp [s]
  rw [← hpre, (measurePreserving_add_right volume (latticePoint k)).setIntegral_preimage_emb
    (measurableEmbedding_addRight _) h (s k)]

/-! ### Functions on the torus -/

/-- `|e_n| = 1` on `𝕋²`. -/
theorem norm_mFourier_apply (n : Fin 2 → ℤ) (z : UnitAddTorus (Fin 2)) : ‖mFourier n z‖ = 1 :=
  norm_mFourier_apply_eq_one n z

/-- Fourier coefficients on `𝕋²` (with the Haar measure of total mass one) as integrals over the
centred cell: `F̂ (n) = ∫_{(−½, ½]²} e_{−n} (y) F (y) dy`. -/
theorem mFourierCoeff_eq_integral_centredCell {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (F : UnitAddTorus (Fin 2) → E) (n : Fin 2 → ℤ) :
    mFourierCoeff F n = ∫ y in centredCell, mFourier (-n) (ofComplex y) • F (ofComplex y) := by
  rw [mFourierCoeff_eq_integral F n (fun _ => -2⁻¹),
    ← Complex.volume_preserving_equiv_pi.setIntegral_preimage_emb
      Complex.measurableEquivPi.measurableEmbedding]
  congr 1
  ext y
  simp only [Fin.forall_fin_two, centredCell]
  norm_num

/-- The projection `ℂ → 𝕋²` is an open quotient map. -/
theorem isOpenQuotientMap_ofComplex : IsOpenQuotientMap ofComplex := by
  have h1 : IsOpenQuotientMap (ofPi : (Fin 2 → ℝ) → UnitAddTorus (Fin 2)) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  exact h1.comp basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.isOpenQuotientMap

/-- The function on `𝕋²` induced by a function `g` on `ℂ`: its value at `z` is the value of `g` at
the representative of `z` in `(0, 1]²`. For `ℤ²`-periodic `g`, `torusLift g (ofComplex y) = g y`
(`HarmonicAnalysis.torusLift_ofComplex`). -/
def torusLift (g : ℂ → ℂ) (z : UnitAddTorus (Fin 2)) : ℂ :=
  g ((toPi z 0 : ℂ) + (toPi z 1 : ℂ) * I)

theorem torusLift_ofComplex {g : ℂ → ℂ} (hg : ∀ y k, g (y + latticePoint k) = g y) (y : ℂ) :
    torusLift g (ofComplex y) = g y := by
  obtain ⟨k, hk⟩ := exists_toPi_ofPi ![y.re, y.im]
  have h : (toPi (ofComplex y) 0 : ℂ) + (toPi (ofComplex y) 1 : ℂ) * I = y + latticePoint k := by
    rw [ofComplex, hk]
    apply Complex.ext <;> simp
  rw [torusLift, h, hg]

/-- A continuous `ℤ²`-periodic function on `ℂ` descends to a continuous function on `𝕋²`. -/
theorem continuous_torusLift {g : ℂ → ℂ} (hg : ∀ y k, g (y + latticePoint k) = g y)
    (hc : Continuous g) : Continuous (torusLift g) := by
  rw [← isOpenQuotientMap_ofComplex.continuous_comp_iff]
  convert hc using 1
  funext y
  exact torusLift_ofComplex hg y

end HarmonicAnalysis
