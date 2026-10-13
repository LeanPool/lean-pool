/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.CutoffProduct.VectorProduct

/-!
# Product

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Besov product estimate `e.besov.mult` at the consuming exponents

Source: ABK26 (`e.besov.mult`) as consumed at `e.split.besov.stuff` inside the
proof of `l.Dh.bound`.

The consuming instance is

```
‖ v ξ ‖_{B^{s}_{2,2}(□)}
  ≤ C ‖v‖_{L²(□)} ‖∇ξ‖_{L^∞(□)}  +  C ‖ξ‖_{L^∞(□)} [v]_{B^{s}_{2,2}(□)} ,
```

with a scalar multiplicand `v ∈ L²` and a vector multiplier `ξ ∈ W^{1,∞}`, at
`s = 3/8`.  This file proves exactly that split.

## What is new here

CoarseGraining already proves the per-cube Hölder step with **no** regularity
hypothesis (`cubeLpNorm_two_cubeFluctuationVec_scalar_smul_le_note_terms`), and
it proves the multiscale assembly for a `C^∞` multiplier
(the smooth-multiplier cutoff estimate for the positive Besov partial seminorm).
The sensitivity multiplier `∇ · h` is only `W^{1,∞}`, so the smoothness
hypothesis is unusable downstream.  This file redoes the assembly with the
multiplier regularity spelled as the *convex-domain* form of `W^{1,∞}`: a
Lipschitz bound on the cube.  On a convex set these are the same regularity
class, and no proof step is smuggled into a hypothesis.

## Structure

* `cubeLpNorm_infty_sub_cubeAverageVec_le_cubeScaleFactor_mul_of_lipschitzOn` —
  the oscillation of the multiplier on a cube;
* `cubeLpNorm_two_cubeFluctuationVec_scalar_smul_le_of_lipschitzOn` — one cube;
* `cubeBesovPositiveVectorDepthSeminorm_scalar_smul_le_of_lipschitzOn` — depth `j`;
* `cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_of_lipschitzOn` —
  finite-depth `ℓ²` assembly;
* `cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_besovMult` — the
  final `e.besov.mult` shape, with the `L²`-of-`v` factor.

Everything is stated at finite depth `N`, uniformly in `N`: the `sSup`
(infinite-depth) version cannot be stated without carrying a `BddAbove`
hypothesis, which the statement discipline forbids.  This matches how
CoarseGraining's own downstream consumers use the cutoff-product estimate.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov

open HCPolySupport MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Step 1: oscillation of a Lipschitz multiplier on a cube -/

/-- The `L^∞` oscillation about the mean of a multiplier that is `B`-Lipschitz on
the cube is at most the cube diameter times `B`.  This is the only place the
multiplier regularity is used; it replaces CoarseGraining's `ContDiff` route. -/
theorem cubeLpNorm_infty_sub_cubeAverageVec_le_cubeScaleFactor_mul_of_lipschitzOn
    (Q : TriadicCube d) {ξ : Vec d → Vec d} {B : ℝ} (hB : 0 ≤ B)
    (hξLp : MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hLip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q, ‖ξ x - ξ y‖ ≤ B * ‖x - y‖) :
    cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) ≤ cubeScaleFactor Q * B := by
  refine cubeLpNorm_infty_le_of_bound_on_cubeSet Q _
    (mul_nonneg (cubeScaleFactor_nonneg Q) hB) ?_
  intro x hx
  have havg : ‖ξ x - cubeAverageVec Q ξ‖ ≤ cubeLpNorm Q ∞ (fun y => ξ y - ξ x) :=
    norm_sub_cubeAverageVec_le_cubeLpNorm_infty_sub_const Q ξ x hξLp
  refine havg.trans ?_
  refine cubeLpNorm_infty_le_of_bound_on_cubeSet Q _
    (mul_nonneg (cubeScaleFactor_nonneg Q) hB) ?_
  intro y hy
  calc
    ‖ξ y - ξ x‖ ≤ B * ‖y - x‖ := hLip y hy x hx
    _ ≤ B * cubeScaleFactor Q :=
        mul_le_mul_of_nonneg_left (norm_sub_le_cubeScaleFactor_of_mem_cubeSet Q hy hx) hB
    _ = cubeScaleFactor Q * B := by ring

/-! ## Step 2: the one-cube product estimate -/

/-- One-cube form of `e.besov.mult` for a `B`-Lipschitz vector multiplier. -/
theorem cubeLpNorm_two_cubeFluctuationVec_scalar_smul_le_of_lipschitzOn
    (Q : TriadicCube d) (v : Vec d → ℝ) (ξ : Vec d → Vec d) {B : ℝ} (hB : 0 ≤ B)
    (hv : MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hLip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q, ‖ξ x - ξ y‖ ≤ B * ‖x - y‖) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q (fun x => v x • ξ x)) ≤
      2 * ((cubeScaleFactor Q * B) * cubeLpNorm Q (2 : ℝ≥0∞) v +
        cubeLpNorm Q ∞ ξ * cubeBesovOscillation Q (2 : ℝ≥0∞) v) := by
  have hosc :
      cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) ≤ cubeScaleFactor Q * B :=
    cubeLpNorm_infty_sub_cubeAverageVec_le_cubeScaleFactor_mul_of_lipschitzOn
      Q hB hξLp hLip
  have hv_nonneg : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) v := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) v
  refine (cubeLpNorm_two_cubeFluctuationVec_scalar_smul_le_note_terms
    Q v ξ hv hξLp).trans ?_
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right hosc hv_nonneg) le_rfl) (by norm_num)

/-! ## Step 3: the depth-`j` estimate -/

/-- Depth-`j` form of `e.besov.mult` for a `B`-Lipschitz vector multiplier. -/
theorem cubeBesovPositiveVectorDepthSeminorm_scalar_smul_le_of_lipschitzOn
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) (v : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B)
    (hv : MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hLip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q, ‖ξ x - ξ y‖ ≤ B * ‖x - y‖) :
    cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j ≤
      2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
        cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j) := by
  classical
  set A : TriadicCube d → ℝ :=
    fun R => (cubeScaleFactor R * B) * cubeLpNorm R (2 : ℝ≥0∞) v with hA_def
  set C : TriadicCube d → ℝ :=
    fun R => cubeLpNorm Q ∞ ξ * cubeBesovOscillation R (2 : ℝ≥0∞) v with hC_def
  have hA_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ A R := by
    intro R _
    exact mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg R) hB)
      (cubeLpNorm_nonneg R (2 : ℝ≥0∞) v)
  have hC_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ C R := by
    intro R _
    exact mul_nonneg (cubeLpNorm_nonneg Q ∞ ξ) (cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) v)
  have hlocal :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R (fun x => v x • ξ x)) ≤
          2 * (A R + C R) := by
    intro R hR
    have hvR : MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic (E := ℝ) hR hv
    have hξR : MemLp ξ ∞ (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic (E := Vec d) hR hξLp
    have hLipR : ∀ x ∈ cubeSet R, ∀ y ∈ cubeSet R, ‖ξ x - ξ y‖ ≤ B * ‖x - y‖ := by
      intro x hx y hy
      exact hLip x (cubeSet_subset_of_mem_descendantsAtDepth hR hx) y
        (cubeSet_subset_of_mem_descendantsAtDepth hR hy)
    have hcubeR :
        cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R (fun x => v x • ξ x)) ≤
          2 * ((cubeScaleFactor R * B) * cubeLpNorm R (2 : ℝ≥0∞) v +
            cubeLpNorm R ∞ ξ * cubeBesovOscillation R (2 : ℝ≥0∞) v) :=
      cubeLpNorm_two_cubeFluctuationVec_scalar_smul_le_of_lipschitzOn
        R v ξ hB hvR hξR hLipR
    refine hcubeR.trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by norm_num)
    exact mul_le_mul_of_nonneg_right (cubeLpNorm_infty_descendant_le hR ξ hξLp)
      (cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) v)
  have hsq_bound :
      descendantsAverage Q j
          (fun R => (cubeLpNorm R (2 : ℝ≥0∞)
            (cubeFluctuationVec R (fun x => v x • ξ x))) ^ 2) ≤
        descendantsAverage Q j (fun R => (2 * (A R + C R)) ^ 2) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    have hleft :
        0 ≤ cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R (fun x => v x • ξ x)) :=
      cubeLpNorm_nonneg R (2 : ℝ≥0∞) (cubeFluctuationVec R (fun x => v x • ξ x))
    have hright : 0 ≤ 2 * (A R + C R) :=
      mul_nonneg (by norm_num) (add_nonneg (hA_nonneg R hR) (hC_nonneg R hR))
    nlinarith [hlocal R hR, hleft, hright]
  have hroot_bound :
      Real.sqrt (descendantsAverage Q j
          (fun R => (cubeLpNorm R (2 : ℝ≥0∞)
            (cubeFluctuationVec R (fun x => v x • ξ x))) ^ 2)) ≤
        Real.sqrt (descendantsAverage Q j (fun R => (2 * (A R + C R)) ^ 2)) :=
    Real.sqrt_le_sqrt hsq_bound
  have hconst :
      Real.sqrt (descendantsAverage Q j (fun R => (2 * (A R + C R)) ^ 2)) =
        2 * Real.sqrt (descendantsAverage Q j (fun R => (A R + C R) ^ 2)) :=
    descendantsAverage_sqrt_const_mul_eq Q j 2 (fun R => A R + C R) (by norm_num)
  have hsplit :
      Real.sqrt (descendantsAverage Q j (fun R => (A R + C R) ^ 2)) ≤
        Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2)) +
          Real.sqrt (descendantsAverage Q j (fun R => (C R) ^ 2)) :=
    descendantsAverage_sqrt_add_le Q j A C hA_nonneg hC_nonneg
  have hAterm :
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2)) =
        cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j := by
    have hArew :
        descendantsAverage Q j (fun R => (A R) ^ 2) =
          descendantsAverage Q j
            (fun R => (B * (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v)) ^ 2) := by
      refine congrArg (descendantsAverage Q j) ?_
      funext R
      simp only [hA_def]
      ring
    have hbase :
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j
              (fun R => (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2)) =
          cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) v j := by
      simpa [Real.sqrt_eq_rpow] using cubeL2Scalar_scale_depth_term_eq Q s v j
    calc
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2))
          = Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j
                (fun R => (B * (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v)) ^ 2)) := by
            rw [hArew]
      _ = B * (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j
                (fun R => (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2))) := by
            rw [descendantsAverage_sqrt_const_mul_eq Q j B
              (fun R => cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) hB]
            ring
      _ = B * (cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) v j) := by
            rw [hbase]
      _ = cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j := by ring
  have hCterm :
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j (fun R => (C R) ^ 2)) =
        cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j := by
    calc
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j (fun R => (C R) ^ 2))
          = Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              (cubeLpNorm Q ∞ ξ *
                Real.sqrt (descendantsAverage Q j
                  (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) v) ^ 2))) := by
            rw [hC_def, descendantsAverage_sqrt_const_mul_eq Q j (cubeLpNorm Q ∞ ξ)
              (fun R => cubeBesovOscillation R (2 : ℝ≥0∞) v) (cubeLpNorm_nonneg Q ∞ ξ)]
      _ = cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j := by
            rw [cubeBesovPositiveScalarDepthSeminorm, cubeBesovPositiveScalarDepthAverage]
            ring
  calc
    cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j
        = Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j
              (fun R => (cubeLpNorm R (2 : ℝ≥0∞)
                (cubeFluctuationVec R (fun x => v x • ξ x))) ^ 2)) := by
          rw [cubeBesovPositiveVectorDepthSeminorm, cubeBesovPositiveVectorDepthAverage]
    _ ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j (fun R => (2 * (A R + C R)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hroot_bound (Real.rpow_nonneg (by norm_num) _)
    _ = 2 * (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j (fun R => (A R + C R) ^ 2))) := by
          rw [hconst]; ring
    _ ≤ 2 * (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2)) +
            Real.sqrt (descendantsAverage Q j (fun R => (C R) ^ 2)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hsplit (Real.rpow_nonneg (by norm_num) _)
    _ = 2 * ((Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2))) +
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j (fun R => (C R) ^ 2)))) := by ring
    _ = 2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
          cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j) := by
          rw [hAterm, hCterm]

/-! ## Step 4: the finite-depth `ℓ²` assembly -/

/-- Finite-depth form of `e.besov.mult` for a `B`-Lipschitz vector multiplier. -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_of_lipschitzOn
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (v : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B)
    (hv : MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hLip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q, ‖ξ x - ξ y‖ ≤ B * ‖x - y‖) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => v x • ξ x) ≤
      2 * (cubeScaleFactor Q * B * cubeL2ScalarPartialSeminormTwo Q (s - 1) N v +
        cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v) := by
  classical
  set A : ℕ → ℝ :=
    fun j => cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j with hA_def
  set C : ℕ → ℝ :=
    fun j => cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j with hC_def
  have hA_nonneg : ∀ j ∈ Finset.range (N + 1), 0 ≤ A j := by
    intro j _
    exact mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hB)
      (cubeL2ScalarDepthSeminorm_nonneg Q (s - 1) v j)
  have hC_nonneg : ∀ j ∈ Finset.range (N + 1), 0 ≤ C j := by
    intro j _
    exact mul_nonneg (cubeLpNorm_nonneg Q ∞ ξ)
      (cubeBesovPositiveScalarDepthSeminorm_nonneg Q s v j)
  have hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j ≤
          2 * (A j + C j) := by
    intro j _
    simpa [hA_def, hC_def] using
      cubeBesovPositiveVectorDepthSeminorm_scalar_smul_le_of_lipschitzOn
        Q s j v ξ hB hv hξLp hLip
  have hsq_bound :
      ∑ j ∈ Finset.range (N + 1),
          (cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j) ^ 2 ≤
        ∑ j ∈ Finset.range (N + 1), (2 * (A j + C j)) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hleft : 0 ≤ cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j :=
      cubeBesovPositiveVectorDepthSeminorm_nonneg Q s (fun x => v x • ξ x) j
    have hright : 0 ≤ 2 * (A j + C j) :=
      mul_nonneg (by norm_num) (add_nonneg (hA_nonneg j hj) (hC_nonneg j hj))
    nlinarith [hdepth j hj, hleft, hright]
  have hsplit :
      Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j + C j) ^ 2) ≤
        Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j) ^ 2) +
          Real.sqrt (∑ j ∈ Finset.range (N + 1), (C j) ^ 2) :=
    sqrt_sum_sq_add_le_sqrt (Finset.range (N + 1)) A C hA_nonneg hC_nonneg
  have hAsum :
      Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j) ^ 2) =
        cubeScaleFactor Q * B * cubeL2ScalarPartialSeminormTwo Q (s - 1) N v := by
    rw [hA_def, cubeL2ScalarPartialSeminormTwo]
    exact sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) (cubeScaleFactor Q * B)
      (fun j => cubeL2ScalarDepthSeminorm Q (s - 1) v j)
      (mul_nonneg (cubeScaleFactor_nonneg Q) hB)
  have hCsum :
      Real.sqrt (∑ j ∈ Finset.range (N + 1), (C j) ^ 2) =
        cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v := by
    rw [hC_def, cubeBesovPositiveScalarPartialSeminormTwo]
    exact sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) (cubeLpNorm Q ∞ ξ)
      (fun j => cubeBesovPositiveScalarDepthSeminorm Q s v j) (cubeLpNorm_nonneg Q ∞ ξ)
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => v x • ξ x)
        = Real.sqrt (∑ j ∈ Finset.range (N + 1),
            (cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j) ^ 2) := rfl
    _ ≤ Real.sqrt (∑ j ∈ Finset.range (N + 1), (2 * (A j + C j)) ^ 2) :=
        Real.sqrt_le_sqrt hsq_bound
    _ = 2 * Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j + C j) ^ 2) :=
        sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) 2 (fun j => A j + C j) (by norm_num)
    _ ≤ 2 * (Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j) ^ 2) +
          Real.sqrt (∑ j ∈ Finset.range (N + 1), (C j) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsplit (by norm_num)
    _ = 2 * (cubeScaleFactor Q * B * cubeL2ScalarPartialSeminormTwo Q (s - 1) N v +
          cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v) := by
        rw [hAsum, hCsum]

/-! ## Step 5: the `e.besov.mult` shape -/

/-- The constant produced by summing the geometric series `∑ 3^{2(s-1)j}`. -/
noncomputable def besovMultConst (s : ℝ) : ℝ :=
  2 * Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹)

theorem besovMultConst_pos {s : ℝ} (hs : s < 1) : 0 < besovMultConst s := by
  have hlt : Real.rpow (3 : ℝ) (2 * (s - 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpos : 0 < (1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹ := by
    exact inv_pos.mpr (by linarith)
  have := Real.sqrt_pos.mpr hpos
  unfold besovMultConst
  positivity

/-- **The Besov product estimate `e.besov.mult`** at the consuming exponents
`p = q = 2`, for a scalar multiplicand in `L²` and a `B`-Lipschitz (i.e.
`W^{1,∞}`) vector multiplier, at finite depth.

This is the exact split used at `e.split.besov.stuff`: an `L²` norm of the
multiplicand times the gradient bound of the multiplier, plus the `L^∞` norm of
the multiplier times the Besov seminorm of the multiplicand. -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_besovMult
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (v : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B) (hs : s < 1)
    (hv : MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hLip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q, ‖ξ x - ξ y‖ ≤ B * ‖x - y‖) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => v x • ξ x) ≤
      besovMultConst s *
        (cubeScaleFactor Q * B * cubeLpNorm Q (2 : ℝ≥0∞) v +
          cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v) := by
  have hgeom :
      cubeL2ScalarPartialSeminormTwo Q (s - 1) N v ≤
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) * cubeLpNorm Q (2 : ℝ≥0∞) v :=
    cubeL2ScalarPartialSeminormTwo_le_geometric_mul_cubeLpNorm_two_of_neg
      Q (s - 1) N v hv (by linarith)
  have hgeom_one : (1 : ℝ) ≤ Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) := by
    have hlt : Real.rpow (3 : ℝ) (2 * (s - 1)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hnn : 0 ≤ Real.rpow (3 : ℝ) (2 * (s - 1)) :=
      Real.rpow_nonneg (by norm_num) _
    have hle : (1 : ℝ) ≤ (1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by linarith)]
      linarith
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ _ := Real.sqrt_le_sqrt hle
  set K : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) with hK_def
  have hK_nonneg : 0 ≤ K := Real.sqrt_nonneg _
  have hcoeff_nonneg : 0 ≤ cubeScaleFactor Q * B :=
    mul_nonneg (cubeScaleFactor_nonneg Q) hB
  have hsecond_nonneg :
      0 ≤ cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v :=
    mul_nonneg (cubeLpNorm_nonneg Q ∞ ξ)
      (Real.sqrt_nonneg _)
  refine (cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_of_lipschitzOn
    Q s N v ξ hB hv hξLp hLip).trans ?_
  have hstep1 :
      cubeScaleFactor Q * B * cubeL2ScalarPartialSeminormTwo Q (s - 1) N v ≤
        K * (cubeScaleFactor Q * B * cubeLpNorm Q (2 : ℝ≥0∞) v) := by
    have := mul_le_mul_of_nonneg_left hgeom hcoeff_nonneg
    calc cubeScaleFactor Q * B * cubeL2ScalarPartialSeminormTwo Q (s - 1) N v
        ≤ cubeScaleFactor Q * B * (K * cubeLpNorm Q (2 : ℝ≥0∞) v) := this
      _ = K * (cubeScaleFactor Q * B * cubeLpNorm Q (2 : ℝ≥0∞) v) := by ring
  have hstep2 :
      cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v ≤
        K * (cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v) := by
    nlinarith [hsecond_nonneg, hgeom_one]
  have hsum :
      cubeScaleFactor Q * B * cubeL2ScalarPartialSeminormTwo Q (s - 1) N v +
          cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v ≤
        K * (cubeScaleFactor Q * B * cubeLpNorm Q (2 : ℝ≥0∞) v +
          cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v) := by
    have := add_le_add hstep1 hstep2
    calc _ ≤ K * (cubeScaleFactor Q * B * cubeLpNorm Q (2 : ℝ≥0∞) v) +
          K * (cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v) := this
      _ = _ := by ring
  calc
    2 * (cubeScaleFactor Q * B * cubeL2ScalarPartialSeminormTwo Q (s - 1) N v +
          cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v)
        ≤ 2 * (K * (cubeScaleFactor Q * B * cubeLpNorm Q (2 : ℝ≥0∞) v +
            cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = besovMultConst s *
          (cubeScaleFactor Q * B * cubeLpNorm Q (2 : ℝ≥0∞) v +
            cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v) := by
          unfold besovMultConst
          rw [hK_def]
          ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov
