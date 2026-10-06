/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.ProjectionLimit

/-!
# High-contrast homogenization: Provider.Response.LinearOscillationDuality

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Oscillation duality for a linear cell functional

A bounded test function with small cell oscillation pairs against an integrable
field through the field's cell averages alone: writing the test function as the
telescoping sum of its cube projections and pairing each residual against the
next projection of the field, every term is a supremum bound for the residual
times a normalized cell-average sum.

The estimate is recorded at the endpoint exponents: the test function is
measured in `L^∞` on each cell and the field only through the first power of its
cell averages.  This is the reading a linear functional of a gradient needs,
because the cell averages of a gradient are exactly what coarse-grained data
controls.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory

open scoped ENNReal BigOperators

noncomputable section

/-! ## Endpoint pairing at one depth -/

private theorem ae_mem_cubeSet_normalizedCubeMeasure {d : ℕ} (Q : TriadicCube d) :
    ∀ᵐ x ∂(normalizedCubeMeasure Q), x ∈ cubeSet Q := by
  rw [normalizedCubeMeasure, cubeMeasure]
  exact MeasureTheory.Measure.ae_smul_measure
    (MeasureTheory.ae_restrict_mem (measurableSet_cubeSet Q)) _

/-- The normalized cell-average sum of a field is the cube average of the
absolute value of its projection. -/
theorem cubeAverage_abs_cubeProjection_eq_cubeBesovCircDepthAverage
    {d : ℕ} (Q : TriadicCube d) (G : Vec d → ℝ) (j : ℕ) :
    cubeAverage Q (fun x => |cubeProjection Q j G x|) =
      cubeBesovCircDepthAverage Q 1 G j := by
  have hmem : MemLp (cubeProjection Q j G) 1 (normalizedCubeMeasure Q) :=
    cubeProjection_memLp Q j 1 G
  have hleft :=
    cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q (1 : ℝ≥0∞)
      (cubeProjection Q j G) (by norm_num) (by norm_num) hmem
  have hright :=
    cubeLpNorm_rpow_cubeProjection_eq_cubeBesovCircDepthAverage Q (1 : ℝ≥0∞) G j
      (by norm_num) (by norm_num)
  rw [← hright, hleft]
  simp [Real.norm_eq_abs]

/-- **Endpoint pairing at one depth**: the projection of the field against the
projection residual of the test function is bounded by the residual's supremum
times the normalized cell-average sum at the next depth. -/
theorem abs_cubeAverage_cubeProjection_mul_cubeProjectionResidual_le
    {d : ℕ} (Q : TriadicCube d) (f G : Vec d → ℝ) (j : ℕ) {K : ℝ}
    (hf : MemLp f 1 (normalizedCubeMeasure Q))
    (hres : ∀ x ∈ cubeSet Q, |cubeProjectionResidual Q j f x| ≤ K) :
    |cubeAverage Q (fun x => cubeProjection Q (j + 1) G x *
        cubeProjectionResidual Q j f x)| ≤
      K * cubeBesovCircDepthAverage Q 1 G (j + 1) := by
  set μ : Measure (Vec d) := normalizedCubeMeasure Q with hμ
  set u : Vec d → ℝ := cubeProjection Q (j + 1) G with hu
  set w : Vec d → ℝ := cubeProjectionResidual Q j f with hw
  have hwdef : w = fun x => f x - cubeProjection Q j f x := by
    rw [hw]
    rfl
  have hae : ∀ᵐ x ∂μ, ‖w x‖ ≤ K := by
    filter_upwards [ae_mem_cubeSet_normalizedCubeMeasure Q] with x hx
    simpa [Real.norm_eq_abs] using hres x hx
  have hu1 : MemLp u 1 μ := cubeProjection_memLp Q (j + 1) 1 G
  have hw1 : MemLp w 1 μ := by
    rw [hwdef]
    exact hf.sub (cubeProjection_memLp Q j 1 f)
  have huInt : Integrable u μ := hu1.integrable le_rfl
  have hprod : Integrable (fun x => w x * u x) μ :=
    huInt.bdd_mul hw1.aestronglyMeasurable hae
  have habs : Integrable (fun x => |w x * u x|) μ := hprod.abs
  have hKabs : Integrable (fun x => K * |u x|) μ := huInt.abs.const_mul K
  have hpoint : (fun x => |w x * u x|) ≤ᵐ[μ] fun x => K * |u x| := by
    filter_upwards [hae] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hx)
      (abs_nonneg _)
  have hkey : |∫ x, w x * u x ∂μ| ≤ K * ∫ x, |u x| ∂μ := by
    calc |∫ x, w x * u x ∂μ| ≤ ∫ x, |w x * u x| ∂μ :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x, K * |u x| ∂μ := MeasureTheory.integral_mono_ae habs hKabs hpoint
      _ = K * ∫ x, |u x| ∂μ := MeasureTheory.integral_const_mul K _
  have hleft : cubeAverage Q (fun x => u x * w x) = ∫ x, w x * u x ∂μ := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, ← hμ]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => mul_comm (u x) (w x))
  have hrightAvg : ∫ x, |u x| ∂μ = cubeBesovCircDepthAverage Q 1 G (j + 1) := by
    rw [← cubeAverage_abs_cubeProjection_eq_cubeBesovCircDepthAverage Q G (j + 1),
      cubeAverage_eq_integral_normalizedCubeMeasure, ← hμ]
  rw [hleft, ← hrightAvg]
  exact hkey

/-! ## The finite-depth duality -/

/-- At the endpoint outer exponent the circ partial norm is the plain sum of its
depth seminorms. -/
theorem cubeBesovCircPartialNorm_one_one_eq_sum {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (G : Vec d → ℝ) (N : ℕ) :
    cubeBesovCircPartialNorm Q s 1 1 N G =
      ∑ j ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q s 1 G j := by
  rw [cubeBesovCircPartialNorm, cubeBesovCircPartialSeminorm]
  simp [Real.rpow_one]

/-- The depth seminorm at the endpoint inner exponent is the weight times the
normalized cell-average sum. -/
theorem cubeBesovCircDepthSeminorm_one_eq {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (G : Vec d → ℝ) (j : ℕ) :
    cubeBesovCircDepthSeminorm Q s 1 G j =
      cubeBesovCircDepthWeight Q s j * cubeBesovCircDepthAverage Q 1 G j := by
  rw [cubeBesovCircDepthSeminorm]
  simp [Real.rpow_one]

/-- **The finite-depth oscillation duality.**  A mean-zero test function whose
depth-`j` projection residual is at most `K` times the depth-`j+1` weight pairs
against the depth-`N` projection of the field with constant `K` and the field's
circ partial norm. -/
theorem abs_cubeBesovPairing_cubeProjection_le_mul_cubeBesovCircPartialNorm
    {d : ℕ} (Q : TriadicCube d) (f G : Vec d → ℝ) (N : ℕ) {s K : ℝ}
    (hK : 0 ≤ K)
    (hGInt : IntegrableOn G (cubeSet Q) volume)
    (hf : MemLp f 1 (normalizedCubeMeasure Q))
    (hfTop : ∀ j < N, ∀ R ∈ descendantsAtDepth Q j,
      MemLp (cubeFluctuation R f) ∞ (normalizedCubeMeasure R))
    (hmean : cubeAverage Q f = 0)
    (hres : ∀ j < N, ∀ x ∈ cubeSet Q,
      |cubeProjectionResidual Q j f x| ≤ K * cubeBesovCircDepthWeight Q s (j + 1)) :
    |cubeBesovPairing Q f (cubeProjection Q N G)| ≤
      K * cubeBesovCircPartialNorm Q s 1 1 N G := by
  classical
  have hconj : cubeBesovConjExponent (∞ : ℝ≥0∞) = 1 := by
    simp [cubeBesovConjExponent, ENNReal.conjExponent]
  have hgProj : ∀ j < N, ∀ R ∈ descendantsAtDepth Q j,
      MemLp (cubeProjection Q (j + 1) G) (cubeBesovConjExponent (∞ : ℝ≥0∞))
        (normalizedCubeMeasure R) := by
    intro j _hj R hR
    rw [hconj]
    exact cubeProjection_succ_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) 1 G hR
  have hid :=
    cubeBesovPairing_projection_eq_cubeAverage_mul_cubeAverage_add_sum
      (Q := Q) (p := (∞ : ℝ≥0∞)) (f := f) (g := G) (N := N) hGInt hfTop hgProj le_top
  rw [hid, hmean, zero_mul, zero_add]
  have hterm : ∀ j ∈ Finset.range N,
      |cubeAverage Q (fun x => cubeProjection Q (j + 1) G x *
        cubeProjectionResidual Q j f x)| ≤
      K * cubeBesovCircDepthSeminorm Q s 1 G (j + 1) := by
    intro j hj
    have hj' : j < N := Finset.mem_range.mp hj
    have hbase :=
      abs_cubeAverage_cubeProjection_mul_cubeProjectionResidual_le Q f G j
        (K := K * cubeBesovCircDepthWeight Q s (j + 1)) hf (hres j hj')
    rw [cubeBesovCircDepthSeminorm_one_eq]
    calc |cubeAverage Q (fun x => cubeProjection Q (j + 1) G x *
              cubeProjectionResidual Q j f x)|
        ≤ K * cubeBesovCircDepthWeight Q s (j + 1) *
            cubeBesovCircDepthAverage Q 1 G (j + 1) := hbase
      _ = K * (cubeBesovCircDepthWeight Q s (j + 1) *
            cubeBesovCircDepthAverage Q 1 G (j + 1)) := by ring
  calc |∑ j ∈ Finset.range N, cubeAverage Q (fun x =>
            cubeProjection Q (j + 1) G x * cubeProjectionResidual Q j f x)|
      ≤ ∑ j ∈ Finset.range N, |cubeAverage Q (fun x =>
            cubeProjection Q (j + 1) G x * cubeProjectionResidual Q j f x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, K * cubeBesovCircDepthSeminorm Q s 1 G (j + 1) :=
        Finset.sum_le_sum hterm
    _ = K * ∑ j ∈ Finset.range N, cubeBesovCircDepthSeminorm Q s 1 G (j + 1) := by
        rw [Finset.mul_sum]
    _ ≤ K * cubeBesovCircPartialNorm Q s 1 1 N G := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        rw [cubeBesovCircPartialNorm_one_one_eq_sum,
          Finset.sum_range_succ' (fun j => cubeBesovCircDepthSeminorm Q s 1 G j) N]
        have h0 : 0 ≤ cubeBesovCircDepthSeminorm Q s 1 G 0 :=
          cubeBesovCircDepthSeminorm_nonneg Q s 1 G 0
        linarith only [h0]

/-! ## The duality at full depth -/

/-- **The oscillation duality.**  For a bounded mean-zero test function whose
projection residuals obey the depth-weighted bound, the pairing against an
integrable field is controlled by any uniform bound for the field's circ partial
norms. -/
theorem abs_cubeBesovPairing_le_mul_of_uniform_cubeBesovCircPartialNorm_bound
    {d : ℕ} (Q : TriadicCube d) (f G : Vec d → ℝ) {s K C W : ℝ}
    (hK : 0 ≤ K)
    (hC : 0 ≤ C)
    (hGInt : IntegrableOn G (cubeSet Q) volume)
    (hfInt : IntegrableOn f (cubeSet Q) volume)
    (hf : MemLp f 1 (normalizedCubeMeasure Q))
    (hfBound : ∀ x ∈ cubeSet Q, |f x| ≤ C)
    (hfTop : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
      MemLp (cubeFluctuation R f) ∞ (normalizedCubeMeasure R))
    (hmean : cubeAverage Q f = 0)
    (hres : ∀ j : ℕ, ∀ x ∈ cubeSet Q,
      |cubeProjectionResidual Q j f x| ≤ K * cubeBesovCircDepthWeight Q s (j + 1))
    (hW : ∀ N : ℕ, cubeBesovCircPartialNorm Q s 1 1 N G ≤ W) :
    |cubeBesovPairing Q f G| ≤ K * W := by
  have hlim :
      Filter.Tendsto (fun n => cubeBesovPairing Q (cubeProjection Q (n + 1) G) f)
        Filter.atTop (nhds (cubeBesovPairing Q G f)) :=
    tendsto_cubeBesovPairing_projection_left_of_integrableOn_of_bounded
      Q G f C hGInt hfInt hC hfBound
  have hswap : ∀ n : ℕ,
      cubeBesovPairing Q (cubeProjection Q (n + 1) G) f =
        cubeBesovPairing Q f (cubeProjection Q (n + 1) G) := by
    intro n
    simp only [cubeBesovPairing]
    exact congrArg (cubeAverage Q) (funext fun x => mul_comm _ _)
  have hlim' :
      Filter.Tendsto (fun n => cubeBesovPairing Q f (cubeProjection Q (n + 1) G))
        Filter.atTop (nhds (cubeBesovPairing Q f G)) := by
    have hbase : cubeBesovPairing Q G f = cubeBesovPairing Q f G := by
      simp only [cubeBesovPairing]
      exact congrArg (cubeAverage Q) (funext fun x => mul_comm _ _)
    rw [← hbase]
    exact hlim.congr fun n => hswap n
  have habs :
      Filter.Tendsto
        (fun n => |cubeBesovPairing Q f (cubeProjection Q (n + 1) G)|)
        Filter.atTop (nhds |cubeBesovPairing Q f G|) := hlim'.abs
  refine le_of_tendsto habs (Filter.Eventually.of_forall fun n => ?_)
  calc |cubeBesovPairing Q f (cubeProjection Q (n + 1) G)|
      ≤ K * cubeBesovCircPartialNorm Q s 1 1 (n + 1) G :=
        abs_cubeBesovPairing_cubeProjection_le_mul_cubeBesovCircPartialNorm
          Q f G (n + 1) hK hGInt hf (fun j _ => hfTop j) hmean
          (fun j _ => hres j)
    _ ≤ K * W := mul_le_mul_of_nonneg_left (hW (n + 1)) hK

end

end HCPolySupport.HighContrast.Response
