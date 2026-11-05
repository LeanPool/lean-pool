/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineDepthGagliardoBand

/-!
# HomSpineDepthStraddleMeasure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The straddling-pair ingredient: separation and the boundary-layer measure

## What this file is for

The Gagliardo half of the single-depth dual test (`HomSpineCzGridDepthTest` §4)
needs ONE geometric fact about the depth-`j` slice `g_j = gridDualDepthTest Q j
v`, a function constant on each depth-`j` cell:

```text
  g_j(y) ≠ g_j(x)   ⟹   x lies within |x-y| of the depth-j skeleton,
```

together with the size of that skeleton neighbourhood.  Both are proved here.

* `gridDualDepthTest_eq_of_mem_cubeShrunkSet` — THE SEPARATION.  If `x` sits in
  the `t`-shrunk core of its depth-`j` cell and `dist x y < t · (cell side)`,
  then `g_j(y) = g_j(x)`.  (Half-open triadic cells and the ambient sup metric:
  a sup-ball of radius `t·ℓ` around a point of the shrunk core stays inside the
  cell.)
* `volume_cubeBoundaryLayer_le` — THE STRADDLING MEASURE, `≤ 2·d·t·|R|` per
  cell, aggregating to `≤ 2·d·t` over the whole depth-`j` skeleton.  This is the `3^{j-k}`-smallness
  the near bands of the band reduction run on: at band `k ≥ j` the relevant
  thickness is `t = 3^{j-k}`.

MINING CORRECTION (recorded): the survey reported that `CoarseGraining`'s
`Geometry/BoundaryLayer` carries "no measure bound".  It does not, but
`Geometry/CubeMeasure` does — `volume_cubeBoundaryLayer_toReal_of_nonneg_le_half`
computes the layer volume EXACTLY as `|R| - ((1-2t)·ℓ)^d`.  Everything below is
that identity plus Bernoulli; no new measure theory is developed.

## What is still missing for the band reduction

The remaining ingredients are the tail-kernel integral
`∫_{y ∈ Q, |x-y| ≥ r} |x-y|^{-(s·p'+d)} dy ≤ C(d)·(1-3^{-s·p'})⁻¹·r^{-s·p'}`
and the layer-cake integration of `dist(x, skeleton)^{-s·p'}` against these
measures.  See this file report; they are NOT in this file.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Separation: the shrunk core does not see the skeleton -/

/-- A sup-ball of radius `t·ℓ` about a point of the `t`-shrunk core of a triadic
cube stays inside the (half-open) cube. -/
theorem mem_cubeSet_of_mem_cubeShrunkSet_of_dist_lt {R : TriadicCube d} {t : ℝ}
    {x y : Vec d} (hx : x ∈ cubeShrunkSet R t) (hy : dist x y < t * cubeScaleFactor R) :
    y ∈ cubeSet R := by
  intro i
  have hcoord : dist (x i) (y i) ≤ dist x y := dist_le_pi_dist x y i
  have habs : |x i - y i| < t * cubeScaleFactor R := by
    rw [Real.dist_eq] at hcoord
    linarith only [hcoord, hy]
  have hlo : ((R.index i : ℝ) - (1 / 2 : ℝ) + t) * cubeScaleFactor R ≤ x i := (hx i).1
  have hhi : x i < ((R.index i : ℝ) + (1 / 2 : ℝ) - t) * cubeScaleFactor R := (hx i).2
  have hlo' : ((R.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor R +
      t * cubeScaleFactor R ≤ x i := by
    have hexp : ((R.index i : ℝ) - (1 / 2 : ℝ) + t) * cubeScaleFactor R =
        ((R.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor R + t * cubeScaleFactor R := by
      ring
    linarith only [hlo, hexp.symm.le, hexp.le]
  have hhi' : x i < ((R.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor R -
      t * cubeScaleFactor R := by
    have hexp : ((R.index i : ℝ) + (1 / 2 : ℝ) - t) * cubeScaleFactor R =
        ((R.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor R - t * cubeScaleFactor R := by
      ring
    linarith only [hhi, hexp.symm.le, hexp.le]
  have habs1 : x i - y i < t * cubeScaleFactor R := (abs_lt.mp habs).2
  have habs2 : -(t * cubeScaleFactor R) < x i - y i := (abs_lt.mp habs).1
  exact ⟨by linarith only [hlo', habs1], by linarith only [hhi', habs2]⟩

/-- **THE SEPARATION.**  A depth-`j` slice is constant on the `t·ℓ`-ball around
any point of the `t`-shrunk core of a depth-`j` cell.  Contrapositive: the pairs
on which `g_j` actually jumps have `x` inside the boundary layer of thickness
`|x-y|/ℓ` — the straddling pairs. -/
theorem gridDualDepthTest_eq_of_mem_cubeShrunkSet (Q : TriadicCube d) (j : ℕ)
    (v : TriadicCube d → Vec d) {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j)
    {t : ℝ} {x y : Vec d} (hx : x ∈ cubeShrunkSet R t) (hxt : 0 ≤ t)
    (hy : dist x y < t * cubeScaleFactor R) :
    gridDualDepthTest Q j v y = gridDualDepthTest Q j v x := by
  have hxR : x ∈ cubeSet R := cubeShrunkSet_subset_cubeSet R hxt hx
  have hyR : y ∈ cubeSet R := mem_cubeSet_of_mem_cubeShrunkSet_of_dist_lt hx hy
  rw [gridDualDepthTest_apply_of_mem v hR hyR, gridDualDepthTest_apply_of_mem v hR hxR]

/-! ## 2. The straddling measure -/

/-- Bernoulli, in the form the layer volume needs: `1 - (1-u)^d ≤ d·u` on
`0 ≤ u ≤ 1`. -/
private theorem one_sub_one_sub_pow_le {u : ℝ} (hu1 : u ≤ 1) (n : ℕ) :
    1 - (1 - u) ^ n ≤ (n : ℝ) * u := by
  have hbern : 1 + (n : ℝ) * (-u) ≤ (1 + (-u)) ^ n :=
    one_add_mul_le_pow (by linarith only [hu1]) n
  have hrw : (1 : ℝ) + (-u) = 1 - u := by ring
  rw [hrw] at hbern
  linarith only [hbern]

/-- **THE STRADDLING MEASURE BOUND.**  The boundary layer of normalized
thickness `t` of a triadic cube has volume at most `2·d·t` times the cube's
volume — the `3^{j-k}`-smallness the near bands of the band reduction consume,
read at `t = 3^{j-k}`.

Proof: `CoarseGraining`'s exact layer volume `|R| - ((1-2t)·ℓ)^d`, plus Bernoulli. -/
theorem volume_cubeBoundaryLayer_le (R : TriadicCube d) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 2) :
    volume (cubeBoundaryLayer R t) ≤
      ENNReal.ofReal (2 * (d : ℝ) * t * cubeVolume R) := by
  have hne : volume (cubeBoundaryLayer R t) ≠ ⊤ :=
    measure_ne_top_of_subset (cubeBoundaryLayer_subset_cubeSet R t)
      (volume_cubeSet_lt_top R).ne
  have hval := volume_cubeBoundaryLayer_toReal_of_nonneg_le_half R ht0 ht
  have hLpos : (0 : ℝ) < cubeScaleFactor R := cubeScaleFactor_pos' R
  have hsplit : ((1 - 2 * t) * cubeScaleFactor R) ^ d =
      (1 - 2 * t) ^ d * cubeVolume R := by
    rw [mul_pow, cubeVolume_eq_scaleFactor_pow]
  have hbern : 1 - (1 - 2 * t) ^ d ≤ (d : ℝ) * (2 * t) :=
    one_sub_one_sub_pow_le (by linarith only [ht]) d
  have hVnn : (0 : ℝ) ≤ cubeVolume R := (cubeVolume_pos R).le
  have hbound : (volume (cubeBoundaryLayer R t)).toReal ≤
      2 * (d : ℝ) * t * cubeVolume R := by
    rw [hval, hsplit]
    have hstep : (1 - (1 - 2 * t) ^ d) * cubeVolume R ≤
        ((d : ℝ) * (2 * t)) * cubeVolume R :=
      mul_le_mul_of_nonneg_right hbern hVnn
    have hexp : (1 - (1 - 2 * t) ^ d) * cubeVolume R =
        cubeVolume R - (1 - 2 * t) ^ d * cubeVolume R := by ring
    have hexp2 : ((d : ℝ) * (2 * t)) * cubeVolume R = 2 * (d : ℝ) * t * cubeVolume R := by
      ring
    linarith only [hstep, hexp, hexp2]
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hbound

end

end Algsuperdiff.Section4.Provider.Homogenization
