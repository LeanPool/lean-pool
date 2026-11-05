/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.BesovCongr

/-!
# VectorPerturbation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `W^{1,∞}` positive Besov bound for a vector field

Vector-valued counterpart of
`Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov.Perturbation`.  The
scalar file proves

```
[u]_{B^{s}_{2,2}(Q), N} ≤ C(s) · ℓ(Q) · ‖∇u‖_{L^∞(Q)}
```

for a `B`-Lipschitz scalar field.  Term A of the `D_h` split needs exactly the
same estimate for the *vector* field `x ↦ hᵀ(x) p`, whose positive Besov
seminorm is measured by `cubeBesovPositiveVectorPartialSeminormTwo`.  The proof
is identical; the one-cube oscillation input is the vector oscillation lemma of
`Provider.DhBound.Besov.Product`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open HCPolySupport MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `L²` is dominated by `L^∞` on a normalized cube, for vector fields -/

theorem cubeLpNorm_two_le_cubeLpNorm_infty_of_memLp_infty_vec
    (Q : TriadicCube d) (u : Vec d → Vec d)
    (hu : MemLp u ∞ (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) u ≤ cubeLpNorm Q ∞ u := by
  let : MeasureTheory.IsProbabilityMeasure (normalizedCubeMeasure Q) := by
    refine ⟨?_⟩
    simp [normalizedCubeMeasure_apply_univ Q]
  have hle :
      MeasureTheory.eLpNorm u (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ≤
        MeasureTheory.eLpNorm u ∞ (normalizedCubeMeasure Q) :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have htoReal := ENNReal.toReal_mono (ne_of_lt hu.eLpNorm_lt_top) hle
  simpa [cubeLpNorm] using htoReal

/-! ## The one-cube `L²` oscillation of a Lipschitz vector field -/

/-- The `L²` oscillation of a `B`-Lipschitz vector field on a cube is at most the
side length times `B`. -/
theorem cubeLpNorm_two_cubeFluctuationVec_le_cubeScaleFactor_mul_of_lipschitzOn
    (Q : TriadicCube d) {ξ : Vec d → Vec d} {B : ℝ} (hB : 0 ≤ B)
    (hξLp : MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hLip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q, ‖ξ x - ξ y‖ ≤ B * ‖x - y‖) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q ξ) ≤ cubeScaleFactor Q * B := by
  have hfluctLp : MemLp (cubeFluctuationVec Q ξ) ∞ (normalizedCubeMeasure Q) :=
    hξLp.sub (MeasureTheory.memLp_const (cubeAverageVec Q ξ))
  refine (cubeLpNorm_two_le_cubeLpNorm_infty_of_memLp_infty_vec Q _ hfluctLp).trans ?_
  exact cubeLpNorm_infty_sub_cubeAverageVec_le_cubeScaleFactor_mul_of_lipschitzOn
    Q hB hξLp hLip

/-! ## The depth-`j` and finite-depth bounds -/

/-- Depth-`j` positive Besov contribution of a `B`-Lipschitz vector field. -/
theorem cubeBesovPositiveVectorDepthSeminorm_le_of_lipschitzOn
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) {ξ : Vec d → Vec d} {B : ℝ} (hB : 0 ≤ B)
    (hξLp : MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hLip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q, ‖ξ x - ξ y‖ ≤ B * ‖x - y‖) :
    cubeBesovPositiveVectorDepthSeminorm Q s ξ j ≤
      cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) (fun _ => B) j := by
  have hpointwise :
      ∀ R ∈ descendantsAtDepth Q j,
        (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R ξ)) ^ 2 ≤
          (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) (fun _ : Vec d => B)) ^ 2 := by
    intro R hR
    have hξR : MemLp ξ ∞ (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic (E := Vec d) hR hξLp
    have hLipR : ∀ x ∈ cubeSet R, ∀ y ∈ cubeSet R, ‖ξ x - ξ y‖ ≤ B * ‖x - y‖ := by
      intro x hx y hy
      exact hLip x (cubeSet_subset_of_mem_descendantsAtDepth hR hx) y
        (cubeSet_subset_of_mem_descendantsAtDepth hR hy)
    have hnormB : cubeLpNorm R (2 : ℝ≥0∞) (fun _ : Vec d => B) = B := by
      rw [cubeLpNorm_const R (2 : ℝ≥0∞) B (by norm_num)]
      exact Real.norm_of_nonneg hB
    have hosc : cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R ξ) ≤ cubeScaleFactor R * B :=
      cubeLpNorm_two_cubeFluctuationVec_le_cubeScaleFactor_mul_of_lipschitzOn R hB hξR hLipR
    have hnn : 0 ≤ cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R ξ) :=
      cubeLpNorm_nonneg R (2 : ℝ≥0∞) _
    rw [hnormB]
    nlinarith [hosc, hnn, mul_nonneg (cubeScaleFactor_nonneg R) hB]
  have havg :
      cubeBesovPositiveVectorDepthAverage Q ξ j ≤
        descendantsAverage Q j
          (fun R => (cubeScaleFactor R *
            cubeLpNorm R (2 : ℝ≥0∞) (fun _ : Vec d => B)) ^ 2) :=
    descendantsAverage_le_descendantsAverage Q j hpointwise
  have hbase :
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j
            (fun R => (cubeScaleFactor R *
              cubeLpNorm R (2 : ℝ≥0∞) (fun _ : Vec d => B)) ^ 2)) =
        cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) (fun _ => B) j := by
    simpa [Real.sqrt_eq_rpow] using
      cubeL2Scalar_scale_depth_term_eq Q s (fun _ : Vec d => B) j
  calc
    cubeBesovPositiveVectorDepthSeminorm Q s ξ j
        = Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (cubeBesovPositiveVectorDepthAverage Q ξ j) := rfl
    _ ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j
            (fun R => (cubeScaleFactor R *
              cubeLpNorm R (2 : ℝ≥0∞) (fun _ : Vec d => B)) ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt havg)
          (Real.rpow_nonneg (by norm_num) _)
    _ = cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) (fun _ => B) j := hbase

/-- **The vector perturbation Besov seminorm bound.** -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_le_of_lipschitzOn
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) {ξ : Vec d → Vec d} {B : ℝ} (hB : 0 ≤ B)
    (hs : s < 1)
    (hξLp : MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hLip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q, ‖ξ x - ξ y‖ ≤ B * ‖x - y‖) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N ξ ≤
      besovPerturbConst s * (cubeScaleFactor Q * B) := by
  have hconstLp : MemLp (fun _ : Vec d => B) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const B
  have hnormB : cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => B) = B := by
    rw [cubeLpNorm_const Q (2 : ℝ≥0∞) B (by norm_num)]
    exact Real.norm_of_nonneg hB
  have hsum :
      ∑ j ∈ Finset.range (N + 1), (cubeBesovPositiveVectorDepthSeminorm Q s ξ j) ^ 2 ≤
        ∑ j ∈ Finset.range (N + 1),
          (cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) (fun _ => B) j) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j _
    have hlow : 0 ≤ cubeBesovPositiveVectorDepthSeminorm Q s ξ j :=
      cubeBesovPositiveVectorDepthSeminorm_nonneg Q s ξ j
    have hhigh : 0 ≤ cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) (fun _ => B) j :=
      mul_nonneg (cubeScaleFactor_nonneg Q)
        (cubeL2ScalarDepthSeminorm_nonneg Q (s - 1) (fun _ => B) j)
    nlinarith [cubeBesovPositiveVectorDepthSeminorm_le_of_lipschitzOn Q s j hB hξLp hLip,
      hlow, hhigh]
  have hgeom :
      cubeL2ScalarPartialSeminormTwo Q (s - 1) N (fun _ => B) ≤
        besovPerturbConst s * cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => B) :=
    cubeL2ScalarPartialSeminormTwo_le_geometric_mul_cubeLpNorm_two_of_neg
      Q (s - 1) N (fun _ => B) hconstLp (by linarith)
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N ξ
        = Real.sqrt (∑ j ∈ Finset.range (N + 1),
            (cubeBesovPositiveVectorDepthSeminorm Q s ξ j) ^ 2) := rfl
    _ ≤ Real.sqrt (∑ j ∈ Finset.range (N + 1),
          (cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) (fun _ => B) j) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = cubeScaleFactor Q * cubeL2ScalarPartialSeminormTwo Q (s - 1) N (fun _ => B) := by
        rw [cubeL2ScalarPartialSeminormTwo]
        exact sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) (cubeScaleFactor Q)
          (fun j => cubeL2ScalarDepthSeminorm Q (s - 1) (fun _ => B) j)
          (cubeScaleFactor_nonneg Q)
    _ ≤ cubeScaleFactor Q * (besovPerturbConst s * B) := by
        rw [hnormB] at hgeom
        exact mul_le_mul_of_nonneg_left hgeom (cubeScaleFactor_nonneg Q)
    _ = besovPerturbConst s * (cubeScaleFactor Q * B) := by ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
