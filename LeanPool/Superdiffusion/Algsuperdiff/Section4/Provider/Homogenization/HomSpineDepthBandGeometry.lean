/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineDepthStraddleMeasure

/-!
# HomSpineDepthBandGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Band geometry for the single-depth Gagliardo reduction

## What this file is for

`HomSpineDepthGagliardoBand` names the Gagliardo band input
`GridDepthGagliardoBandInput`; `HomSpineDepthStraddleMeasure` supplies the
separation and the straddling measure.  The reduction of the Gagliardo double
integral of the depth-`j` slice to the band sums needs four more elementary
facts, all proved here:

* `dist_le_euclideanDist` — the ambient sup metric is below the Euclidean one,
  so the Gagliardo kernel (which uses `euclideanDist` at a NEGATIVE exponent) is
  bounded above by the sup-metric kernel, and the sup-metric balls of
  `Real.volume_pi_closedBall` become available (`volume_closedBall_eq`, and its
  open-ball corollary `volume_setOf_dist_lt_le`);
* `exists_triadic_band` — every distance strictly inside `(0, side)` lies in
  exactly one triadic band `[3^{-(k+1)}·side, 3^{-k}·side)`, `k: ℕ`;
* `dist_lt_cubeScaleFactor` — the sup diameter of a triadic cube is its side,
  so band `k = 0` is the coarsest one that occurs;
* `mem_biUnion_cubeBoundaryLayer_of_gridDualDepthTest_ne` — the SEPARATION in
  the form the near bands consume: if the depth-`j` slice jumps between `x` and
  a point within `t·(cell side)` of it, then `x` is in the depth-`j` skeleton
  layer of thickness `t`, whose measure `HomSpineDepthStraddleMeasure` bounds.

The measurability facts the Tonelli step of the reduction needs
(`measurable_gridDualDepthTest`, `measurable_cubeEuclideanWspKernel`) are proved
here too, since they are pure ambient facts.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The two metrics, and sup-metric balls -/

/-- The ambient (sup) distance of `Vec d` is below the Euclidean distance.  The
Gagliardo kernel carries a NEGATIVE power of `euclideanDist`, so this is the
inequality that lets the estimate run on sup-metric balls. -/
theorem dist_le_euclideanDist (x y : Vec d) : dist x y ≤ euclideanDist x y := by
  refine (dist_pi_le_iff (euclideanDist_nonneg x y)).mpr fun i => ?_
  rw [Real.dist_eq]
  have hsq : (x i - y i) ^ 2 ≤ vecNormSq (x - y) := by
    have hmem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
    have hsingle := Finset.single_le_sum (f := fun k : Fin d => (x - y) k * (x - y) k)
      (fun k _ => mul_self_nonneg _) hmem
    simpa [vecNormSq, vecDot, pow_two] using hsingle
  calc |x i - y i| = Real.sqrt ((x i - y i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (vecNormSq (x - y)) := Real.sqrt_le_sqrt hsq
    _ = euclideanDist x y := rfl

/-- The Gagliardo kernel, bounded above by the sup-metric kernel.  (Both sides
vanish on the diagonal: `Real.rpow` sends `0` to `0` at a negative exponent.) -/
theorem euclideanDist_rpow_neg_le (x y : Vec d) {e : ℝ} (he : 0 < e) :
    euclideanDist x y ^ (-e) ≤ dist x y ^ (-e) := by
  rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist x y) with h0 | hpos
  · have hxy : x = y := by
      have := dist_eq_zero.mp h0.symm
      exact this
    subst hxy
    rw [dist_self, euclideanDist_self, Real.zero_rpow (by linarith only [he])]
  · exact Real.rpow_le_rpow_of_nonpos hpos (dist_le_euclideanDist x y)
      (by linarith only [he])

/-- The sup-metric closed ball has volume `(2ρ)^d`. -/
theorem volume_closedBall_eq (x : Vec d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (Metric.closedBall x ρ) = ENNReal.ofReal ((2 * ρ) ^ d) := by
  simpa using Real.volume_pi_closedBall x hρ

/-- The set of points within sup-distance `ρ` of `x` has volume at most `(2ρ)^d`. -/
theorem volume_setOf_dist_lt_le (x : Vec d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume {y : Vec d | dist x y < ρ} ≤ ENNReal.ofReal ((2 * ρ) ^ d) := by
  refine le_trans (measure_mono ?_) (le_of_eq (volume_closedBall_eq x hρ))
  intro y hy
  rw [Metric.mem_closedBall, dist_comm]
  exact le_of_lt hy

/-! ## 2. The triadic bands -/

/-- **THE TRIADIC BAND DECOMPOSITION.**  Every `u ∈ (0,1)` lies in exactly one
band `[3^{-(k+1)}, 3^{-k})` with `k: ℕ`. -/
theorem exists_triadic_band {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ∃ k : ℕ, (1 / 3 : ℝ) ^ (k + 1) ≤ u ∧ u < (1 / 3 : ℝ) ^ k := by
  classical
  have hex : ∃ n : ℕ, (1 / 3 : ℝ) ^ (n + 1) ≤ u := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hu0 (by norm_num : (1 / 3 : ℝ) < 1)
    refine ⟨n, le_of_lt (lt_of_le_of_lt ?_ hn)⟩
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]
    simpa using hu1
  · have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    have hmin := Nat.find_min hex hlt
    have hrw : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [hrw] at hmin
    exact lt_of_not_ge hmin

/-- The sup diameter of a triadic cube is its side: no band coarser than `k = 0`
occurs inside a cube. -/
theorem dist_lt_cubeScaleFactor {Q : TriadicCube d} {x y : Vec d}
    (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet Q) : dist x y < cubeScaleFactor Q := by
  have hpos : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  refine (dist_pi_lt_iff hpos).mpr fun i => ?_
  rw [Real.dist_eq, abs_lt]
  have hx1 := (hx i).1
  have hx2 := (hx i).2
  have hy1 := (hy i).1
  have hy2 := (hy i).2
  have hexp : ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q -
      ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q = cubeScaleFactor Q := by
    ring
  exact ⟨by linarith only [hy2, hx1, hexp], by linarith only [hx2, hy1, hexp]⟩

/-! ## 3. The separation, in skeleton-layer form -/

/-- **THE SEPARATION FOR THE NEAR BANDS.**  If the depth-`j` slice takes
different values at `x` and at a point within `t·(cell side)` of `x`, then `x`
lies in the depth-`j` skeleton layer of normalized thickness `t`, whose
normalized measure is at most `2·d·t`. -/
theorem mem_biUnion_cubeBoundaryLayer_of_gridDualDepthTest_ne (Q : TriadicCube d) (j : ℕ)
    (v : TriadicCube d → Vec d) {t : ℝ} (ht : 0 ≤ t) {x y : Vec d} (hx : x ∈ cubeSet Q)
    (hne : gridDualDepthTest Q j v y ≠ gridDualDepthTest Q j v x)
    (hlt : dist x y < t * (cubeScaleFactor Q / (3 : ℝ) ^ j)) :
    x ∈ ⋃ R ∈ descendantsAtDepth Q j, cubeBoundaryLayer R t := by
  obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet j hx
  have hscale : cubeScaleFactor R = cubeScaleFactor Q / (3 : ℝ) ^ j :=
    cubeScaleFactor_descendant_eq_div_pow hR
  refine Set.mem_biUnion hR ⟨hxR, ?_⟩
  intro hshrunk
  exact hne (gridDualDepthTest_eq_of_mem_cubeShrunkSet Q j v hR hshrunk ht (by rwa [hscale]))

/-! ## 4. Measurability -/

/-- A depth slice is measurable: a finite sum of indicators of cubes. -/
theorem measurable_gridDualDepthTest (Q : TriadicCube d) (j : ℕ)
    (v : TriadicCube d → Vec d) : Measurable (gridDualDepthTest Q j v) := by
  classical
  refine Finset.measurable_sum _ fun R _ => ?_
  exact measurable_const.indicator (measurableSet_cubeSet R)

/-- The Euclidean distance is measurable on the product. -/
theorem measurable_euclideanDist_pair :
    Measurable (fun z : Vec d × Vec d => euclideanDist z.1 z.2) := by
  have hsub : Measurable (fun z : Vec d × Vec d => z.1 - z.2) :=
    measurable_fst.sub measurable_snd
  have hh : Measurable (fun z : Vec d × Vec d => HilbertVec.ofVec (z.1 - z.2)) :=
    (HilbertVec.ofVecL d).continuous.measurable.comp hsub
  simpa only [euclideanDist, euclideanNorm_eq_norm_ofVec] using hh.norm

/-- The Gagliardo kernel of a measurable field is measurable. -/
theorem measurable_cubeEuclideanWspKernel (s : FractionalOrder) (q : FiniteLpExponent)
    {G : Vec d → Vec d} (hG : Measurable G) :
    Measurable (cubeEuclideanWspKernel s q G) := by
  have h₁ : Measurable (fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / q.exponent.toReal))) :=
    measurable_euclideanDist_pair.pow measurable_const
  have h₂ : Measurable (fun z : Vec d × Vec d => G z.1 - G z.2) :=
    (hG.comp measurable_fst).sub (hG.comp measurable_snd)
  have h₃ : Measurable (fun z : Vec d × Vec d =>
      HilbertVec.ofVec (G z.1 - G z.2)) :=
    (HilbertVec.ofVecL d).continuous.measurable.comp h₂
  exact h₁.smul h₃

end

end Algsuperdiff.Section4.Provider.Homogenization
