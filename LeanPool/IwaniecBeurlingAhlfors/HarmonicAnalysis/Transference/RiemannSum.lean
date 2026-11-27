/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.Cube
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.Lattice
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor

/-!
# Lattice Riemann sums of functions continuous off the origin

`HarmonicAnalysis.tendsto_riemannSum_real`: if `φ : ℂ → ℂ` is continuous at every `ξ ≠ 0` and
`|φ (ξ)| ≤ C (1 + |ξ|)^{−3}`, then the Riemann sums over the lattice `R⁻¹ ℤ²`,
`Σ_{n ∈ ℤ²} R⁻² φ (n / R)`, tend to `∫_ℂ φ` as `R → ∞` through the reals. No continuity at `0` is
needed: the cells `R⁻¹ (n + [0, 1)²)` shrink, and the step functions `ξ ↦ φ (⌊R ξ⌋ / R)` converge to
`φ` off `0` under the integrable bound `C' (1 + |ξ|)^{−3}`. A continuous function with compact
support satisfies the hypotheses.

`HarmonicAnalysis.exists_tendsto_latticePoint_div`: every `ξ ∈ ℂ` is a limit of points of the
lattices `R⁻¹ ℤ²` as `R → ∞`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace HarmonicAnalysis

/-! ### The cells of the lattice `R⁻¹ ℤ²` -/

/-- The index `(⌊R Re ξ⌋, ⌊R Im ξ⌋) ∈ ℤ²` of the cell `R⁻¹ (n + [0, 1)²)` containing `ξ`. -/
private def cellIndex (R : ℝ) (ξ : ℂ) : Fin 2 → ℤ := ![⌊R * ξ.re⌋, ⌊R * ξ.im⌋]

private theorem measurable_cellIndex (R : ℝ) : Measurable (cellIndex R) :=
  measurable_pi_iff.mpr <| Fin.forall_fin_two.mpr
    ⟨(measurable_const.mul Complex.measurable_re).floor,
      (measurable_const.mul Complex.measurable_im).floor⟩

/-- `|⌊R x⌋ / R − x| ≤ R⁻¹`. -/
private theorem abs_floor_div_sub_le {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |⌊R * x⌋ / R - x| ≤ R⁻¹ := by
  have h : (⌊R * x⌋ : ℝ) / R - x = -(Int.fract (R * x) / R) := by
    rw [Int.fract]
    field_simp
    ring
  rw [h, abs_neg, abs_of_nonneg (div_nonneg (Int.fract_nonneg _) hR.le), div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.mpr hR.le) (Int.fract_lt_one _).le

/-- The lower left corner `⌊R ξ⌋ / R` of the cell containing `ξ` is within `2 / R` of `ξ`. -/
private theorem norm_latticePoint_cellIndex_div_sub_le {R : ℝ} (hR : 0 < R) (ξ : ℂ) :
    ‖latticePoint (cellIndex R ξ) / R - ξ‖ ≤ 2 / R := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h1 := abs_floor_div_sub_le hR ξ.re
  have h2 := abs_floor_div_sub_le hR ξ.im
  simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
    latticePoint_re, latticePoint_im, cellIndex]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (2 : ℝ) / R = R⁻¹ + R⁻¹ by ring]
  exact add_le_add h1 h2

/-- The cell `R⁻¹ (n + [0, 1)²)`, in the coordinates `ℂ ≃ ℝ × ℝ`. -/
private theorem cellIndex_preimage (R : ℝ) (n : Fin 2 → ℤ) :
    cellIndex R ⁻¹' {n} = Complex.measurableEquivRealProd ⁻¹'
      (((fun x : ℝ => R * x) ⁻¹' Set.Ico (n 0 : ℝ) (n 0 + 1)) ×ˢ
        ((fun x : ℝ => R * x) ⁻¹' Set.Ico (n 1 : ℝ) (n 1 + 1))) := by
  ext ξ
  simp [cellIndex, funext_iff, Fin.forall_fin_two, Int.floor_eq_iff]

/-- Each cell of `R⁻¹ ℤ²` has measure `R⁻²`. -/
private theorem volume_real_cellIndex_preimage {R : ℝ} (hR : 0 < R) (n : Fin 2 → ℤ) :
    volume.real (cellIndex R ⁻¹' {n}) = (R ^ 2)⁻¹ := by
  have hm : ∀ k : ℤ, MeasurableSet ((fun x : ℝ => R * x) ⁻¹' Set.Ico (k : ℝ) (k + 1)) :=
    fun _ => measurableSet_Ico.preimage (measurable_id.const_mul _)
  rw [Measure.real, cellIndex_preimage, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((hm _).prod (hm _)).nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_preimage_mul_left hR.ne', Real.volume_preimage_mul_left hR.ne', Real.volume_Ico,
    Real.volume_Ico]
  simp [abs_of_pos hR, ENNReal.toReal_mul, sq, hR.le]

private theorem rpow_neg_three {x : ℝ} (hx : 0 ≤ x) : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_ofNat]

/-! ### Riemann sums -/

/-- Lattice Riemann sums: for `φ` continuous off `0` with `|φ (ξ)| ≤ C (1 + |ξ|)^{−3}`,
`Σ_{n ∈ ℤ²} R⁻² φ (n / R) → ∫_ℂ φ` as `R → ∞` through the reals. -/
theorem tendsto_riemannSum_real {φ : ℂ → ℂ} (hφ : ∀ ξ ≠ 0, ContinuousAt φ ξ) {C : ℝ}
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-3 : ℝ)) :
    Tendsto (fun R : ℝ => ∑' n : Fin 2 → ℤ, ((R : ℂ) ^ 2)⁻¹ * φ (latticePoint n / R)) atTop
      (𝓝 (∫ ξ, φ ξ)) := by
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  -- The step functions `S R ξ = φ (⌊R ξ⌋ / R)`, constant on the cells of `R⁻¹ ℤ²`.
  set S : ℝ → ℂ → ℂ := fun R ξ => φ (latticePoint (cellIndex R ξ) / R) with hS
  -- The dominating function.
  set g : ℂ → ℝ := fun ξ => C * 27 * (1 + ‖ξ‖) ^ (-3 : ℝ) with hg
  have hg_int : Integrable g :=
    (integrable_one_add_norm (by simp [Complex.finrank_real_complex]; norm_num)).const_mul _
  have hS_meas : ∀ R, AEStronglyMeasurable (S R) volume := fun R =>
    ((measurable_of_countable fun n => φ (latticePoint n / R)).comp
      (measurable_cellIndex R)).aestronglyMeasurable
  have hS_bound : ∀ R : ℝ, 1 ≤ R → ∀ ξ, ‖S R ξ‖ ≤ g ξ := by
    intro R hR ξ
    set p := latticePoint (cellIndex R ξ) / R
    have hp : ‖ξ‖ ≤ ‖p‖ + 2 := by
      have h1 := norm_latticePoint_cellIndex_div_sub_le (zero_lt_one.trans_le hR) ξ
      have h2 : (2 : ℝ) / R ≤ 2 := div_le_self zero_le_two hR
      have h3 := norm_sub_norm_le ξ p
      rw [norm_sub_rev] at h3
      linarith
    have h1 : (1 + ‖ξ‖) ^ 3 ≤ 27 * (1 + ‖p‖) ^ 3 := by
      have : 1 + ‖ξ‖ ≤ 3 * (1 + ‖p‖) := by linarith [norm_nonneg p]
      calc (1 + ‖ξ‖) ^ 3 ≤ (3 * (1 + ‖p‖)) ^ 3 := by gcongr
        _ = 27 * (1 + ‖p‖) ^ 3 := by ring
    calc ‖S R ξ‖ ≤ C * (1 + ‖p‖) ^ (-3 : ℝ) := hC p
      _ ≤ g ξ := by
        simp only [hg, rpow_neg_three (by positivity : (0 : ℝ) ≤ 1 + ‖p‖),
          rpow_neg_three (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖), mul_assoc]
        gcongr
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
        linarith
  have hS_int : ∀ R : ℝ, 1 ≤ R → Integrable (S R) := fun R hR =>
    hg_int.mono' (hS_meas R) (ae_of_all _ (hS_bound R hR))
  -- The integral of `S R` is the Riemann sum.
  have hsum : ∀ R : ℝ, 1 ≤ R →
      HasSum (fun n => ((R : ℂ) ^ 2)⁻¹ * φ (latticePoint n / R)) (∫ ξ, S R ξ) := by
    intro R hR
    have hR0 : 0 < R := zero_lt_one.trans_le hR
    have hm : ∀ n, MeasurableSet (cellIndex R ⁻¹' {n}) := fun n =>
      measurable_cellIndex R (measurableSet_singleton n)
    have h := hasSum_integral_iUnion (μ := volume) hm
      (fun m n hmn => (Set.disjoint_singleton.mpr hmn).preimage _) (hS_int R hR).integrableOn
    rw [← Set.preimage_iUnion, Set.iUnion_of_singleton, Set.preimage_univ,
      Measure.restrict_univ] at h
    convert h using 1
    funext n
    rw [setIntegral_congr_fun (hm n) (g := fun _ => φ (latticePoint n / R))
      (fun ξ hξ => by simp only [hS, Set.mem_singleton_iff.mp hξ]),
      setIntegral_const, volume_real_cellIndex_preimage hR0, Complex.real_smul]
    push_cast
    rfl
  -- Dominated convergence.
  have hlim : Tendsto (fun R => ∫ ξ, S R ξ) atTop (𝓝 (∫ ξ, φ ξ)) := by
    refine tendsto_integral_filter_of_dominated_convergence g (Eventually.of_forall hS_meas)
      (eventually_atTop.mpr ⟨1, fun R hR => ae_of_all _ (hS_bound R hR)⟩) hg_int ?_
    filter_upwards [Measure.ae_ne volume 0] with ξ hξ
    refine (hφ ξ hξ).tendsto.comp ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_atTop.mpr ⟨1, fun R hR => norm_latticePoint_cellIndex_div_sub_le
        (zero_lt_one.trans_le hR) ξ⟩)
      (tendsto_const_nhds.div_atTop tendsto_id)
  exact hlim.congr' (eventually_atTop.mpr ⟨1, fun R hR => (hsum R hR).tsum_eq.symm⟩)

/-- The lattices `R⁻¹ ℤ²` become dense as `R → ∞`: for every `ξ` there are `n_R ∈ ℤ²` with
`n_R / R → ξ`. -/
theorem exists_tendsto_latticePoint_div (ξ : ℂ) :
    ∃ n : ℝ → Fin 2 → ℤ, Tendsto (fun R : ℝ => latticePoint (n R) / R) atTop (𝓝 ξ) := by
  refine ⟨fun R => cellIndex R ξ, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_atTop.mpr ⟨1, fun R hR => norm_latticePoint_cellIndex_div_sub_le
      (zero_lt_one.trans_le hR) ξ⟩) (tendsto_const_nhds.div_atTop tendsto_id)

end HarmonicAnalysis
