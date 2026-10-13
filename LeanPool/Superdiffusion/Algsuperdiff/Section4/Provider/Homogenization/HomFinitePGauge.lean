/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomLiftScaleArith
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.Definitions

/-!
# HomFinitePGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the finite-`p` negative Besov carrier

## Why a finite `p`

A large finite `p` — here `p = 4d` — suffices, the `L^∞` statement being
recovered from it by Sobolev embedding.  The `p ↑ ∞` application of the general
coarse-graining proposition is replaced by the PRINTED finite-`p` proposition
(stated for `p ∈ [2,∞)` at `C(p,d)`), and the `L^∞` endpoint is reached by a
supercritical embedding.  This module supplies the finite-`p` carrier and the
one extraction step that converts it into the exponent shift `s ↦ s + d/p`.

## The carrier pin

The manuscript never defines `‖·‖_{W_hat^{-s,p}(□_m)}`: the manuscript defines only
the order `-1` duals.  The only negative-order fractional object defined
anywhere in the manuscript is the negative Besov seminorm,

```text
  [F]_{B^{-s}_{p,q}(□_m)}
    = ( Σ_{n ≤ m} 3^{sqn} ( avsum_{z ∈ 3^n ℤ^d ∩ □_m} |(F)_{z+□_n}|^p )^{q/p} )^{1/q}
```

(the printed weight `3^{sqm}` is the index typo). Under the Besov--Sobolev
dictionary `W^{-s,p} ≃ B^{-s}_{p,p}` the Step-3 object is the `(p,q) = (p,p)`
member, which is what this module defines.  Three facts about the printed grid
are load-bearing and are recorded here:

* the grid of the negative Besov seminorm definition is the **pure** lattice `3^n ℤ^d ∩ □_m`,
  i.e. exactly the triadic partition of `□_m` into the depth-`(m-n)`
  descendants — *not* the half-shifted family `3^{n-1} ℤ^d` of the positive
  seminorm the Besov seminorm definition.  So the carrier here is `CoarseGraining`'s
  `descendantsAtDepth`, verbatim;
* the depth weight `3^{-sj}` at depth `j = m - n` is exactly the display's
  own `3^{-ms}·3^{sn}`, i.e. the gauge below is the display's left-hand
  quantity `3^{-ms}‖·‖`.  This is the normalization
  (`negBesovInftyDepthSeminorm_eq_scaleNormalized`) at finite `p`;
* the inner norm is the Euclidean vector norm, as in the `p = ∞` pin.

## Main definitions and results

* `negBesovLpDepthMean` — the depth-`j` `ℓ^p` mean of the grid cell averages,
  `( avsum_{R ∈ D_j} |(F)_R|^p )^{1/p}`;
* `negBesovLpDepthSeminorm` — its `3^{-sj}` weighted form;
* `sqrt_vecNormSq_cubeAverageVec_le_of_depthBound` — **THE EXTRACTION**: one
  term of an `ℓ^p` mean over `3^{jd}` cells is at most `3^{jd/p}` times the
  mean, so the per-cell gauge holds at the shifted exponent `s + d/p` and at
  the SAME constant.

## References

* ABK26, the general coarse-graining proposition; the negative Besov seminorm definition; the Besov seminorm definition.
-/

open HCPolySupport HCPolySupport.Book.Ch03

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Elementary `rpow` arithmetic -/

/-- From `x ^ p ≤ C ^ p` with nonnegative `x, C` and positive `p`, conclude
`x ≤ C`.  Stated once so no proof below re-derives it. -/
theorem le_of_rpow_le_rpow {x C p : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (hp : 0 < p)
    (h : x ^ p ≤ C ^ p) : x ≤ C := by
  have h1 : (x ^ p) ^ (1 / p) ≤ (C ^ p) ^ (1 / p) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hx p) h (one_div_nonneg.mpr hp.le)
  rwa [← Real.rpow_mul hx, ← Real.rpow_mul hC, mul_one_div_cancel (ne_of_gt hp),
    Real.rpow_one, Real.rpow_one] at h1

/-- **The cardinality of the depth-`j` grid, as a real `rpow`.**  This is the
`3^{jd}` that the extraction pays. -/
theorem descendantsAtDepth_card_rpow (Q : TriadicCube d) (j : ℕ) :
    ((descendantsAtDepth Q j).card : ℝ) = (3 : ℝ) ^ ((d : ℝ) * (j : ℝ)) := by
  rw [descendantsAtDepth_card]
  push_cast
  rw [← Real.rpow_natCast (3 : ℝ) d, ← Real.rpow_natCast ((3 : ℝ) ^ (d : ℝ)) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

theorem descendantsAtDepth_card_pos (Q : TriadicCube d) (j : ℕ) :
    (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
  rw [descendantsAtDepth_card_rpow]
  exact three_rpow_pos _

/-! ## 2. The finite-`p` gauge on the printed grid -/

/-- **The depth-`j` `ℓ^p` mean of the grid cell averages**,
`( avsum_{R ∈ D_j} |(F)_R|^p )^{1/p}` — the inner index of
the negative Besov seminorm definition at a finite exponent `p`, on the pure triadic grid the
manuscript prints. -/
def negBesovLpDepthMean (Q : TriadicCube d) (p : ℝ) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  (descendantsAverage Q j fun R => Real.sqrt (vecNormSq (cubeAverageVec R F)) ^ p) ^ (1 / p)

/-- The weighted depth-`j` quantity of the finite-`p` gauge; the weight
`3^{-sj}` is the display's own `3^{-ms}·3^{sn}` at `n = m - j`. -/
def negBesovLpDepthSeminorm (Q : TriadicCube d) (s p : ℝ) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  (3 : ℝ) ^ (-s * (j : ℝ)) * negBesovLpDepthMean Q p F j

theorem negBesovLpDepthMean_def (Q : TriadicCube d) (p : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    negBesovLpDepthMean Q p F j =
      (descendantsAverage Q j fun R =>
        Real.sqrt (vecNormSq (cubeAverageVec R F)) ^ p) ^ (1 / p) := rfl

theorem negBesovLpDepthSeminorm_def (Q : TriadicCube d) (s p : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    negBesovLpDepthSeminorm Q s p F j =
      (3 : ℝ) ^ (-s * (j : ℝ)) * negBesovLpDepthMean Q p F j := rfl

/-! ## 3. Elementary API -/

theorem descendantsAverage_rpow_nonneg (Q : TriadicCube d) (p : ℝ)
    (F : Vec d → Vec d) (j : ℕ) :
    0 ≤ descendantsAverage Q j fun R => Real.sqrt (vecNormSq (cubeAverageVec R F)) ^ p :=
  descendantsAverage_nonneg Q j _ fun _ _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _

theorem negBesovLpDepthMean_nonneg (Q : TriadicCube d) (p : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    0 ≤ negBesovLpDepthMean Q p F j :=
  Real.rpow_nonneg (descendantsAverage_rpow_nonneg Q p F j) _

theorem negBesovLpDepthSeminorm_nonneg (Q : TriadicCube d) (s p : ℝ)
    (F : Vec d → Vec d) (j : ℕ) : 0 ≤ negBesovLpDepthSeminorm Q s p F j :=
  mul_nonneg (three_rpow_nonneg _) (negBesovLpDepthMean_nonneg Q p F j)

/-- The `p`-th power of the depth mean recovers the depth average. -/
theorem negBesovLpDepthMean_rpow (Q : TriadicCube d) {p : ℝ} (hp : 0 < p)
    (F : Vec d → Vec d) (j : ℕ) :
    negBesovLpDepthMean Q p F j ^ p =
      descendantsAverage Q j fun R => Real.sqrt (vecNormSq (cubeAverageVec R F)) ^ p := by
  rw [negBesovLpDepthMean_def,
    ← Real.rpow_mul (descendantsAverage_rpow_nonneg Q p F j),
    one_div_mul_cancel (ne_of_gt hp), Real.rpow_one]

/-! ## 5. THE EXTRACTION: one cell out of the `ℓ^p` mean -/

/-- **The extraction, per cell.**

If the depth-`j` weighted `ℓ^p` mean is at most `A`, then every single cell at
depth `j` obeys

```text
  |(F)_R| ≤ A · 3^{j(s + d/p)}.
```

The `3^{jd/p}` is exactly the cardinality `3^{jd}` of the depth-`j` grid raised
to `1/p`; there is no other loss, so the constant is `A` itself.  This is the
"Jensen one scale up" step, in its sharp form: an `ℓ^p` mean
controls one term at the price of the count, and that price is precisely the
exponent shift `s ↦ s + d/p`. -/
theorem sqrt_vecNormSq_cubeAverageVec_le_of_depthBound {Q : TriadicCube d} {s p A : ℝ}
    (hp : 0 < p) {F : Vec d → Vec d} {j : ℕ}
    (hbd : negBesovLpDepthSeminorm Q s p F j ≤ A)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j) :
    Real.sqrt (vecNormSq (cubeAverageVec R F)) ≤
      A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (j : ℝ)) := by
  classical
  have hcard : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := descendantsAtDepth_card_pos Q j
  have hA : 0 ≤ A := le_trans (negBesovLpDepthSeminorm_nonneg Q s p F j) hbd
  /- the depth mean is below `A · 3^{sj}` -/
  have hmean : negBesovLpDepthMean Q p F j ≤ A * (3 : ℝ) ^ (s * (j : ℝ)) := by
    have hw : (0 : ℝ) < (3 : ℝ) ^ (-s * (j : ℝ)) := three_rpow_pos _
    have hstep := mul_le_mul_of_nonneg_left hbd (le_of_lt (three_rpow_pos (s * (j : ℝ))))
    rw [negBesovLpDepthSeminorm_def, ← mul_assoc,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)] at hstep
    have hzero : s * (j : ℝ) + -s * (j : ℝ) = 0 := by ring
    rw [hzero, Real.rpow_zero, one_mul] at hstep
    calc negBesovLpDepthMean Q p F j ≤ (3 : ℝ) ^ (s * (j : ℝ)) * A := hstep
      _ = A * (3 : ℝ) ^ (s * (j : ℝ)) := by ring
  /- one term of the `ℓ^p` s -/
  have hterm : Real.sqrt (vecNormSq (cubeAverageVec R F)) ^ p ≤
      ((descendantsAtDepth Q j).card : ℝ) * negBesovLpDepthMean Q p F j ^ p := by
    have hsingle : Real.sqrt (vecNormSq (cubeAverageVec R F)) ^ p ≤
        ∑ S ∈ descendantsAtDepth Q j, Real.sqrt (vecNormSq (cubeAverageVec S F)) ^ p :=
      Finset.single_le_sum
        (f := fun S => Real.sqrt (vecNormSq (cubeAverageVec S F)) ^ p)
        (fun S _ => Real.rpow_nonneg (Real.sqrt_nonneg _) p) hR
    have hsum : ((descendantsAtDepth Q j).card : ℝ) * negBesovLpDepthMean Q p F j ^ p =
        ∑ S ∈ descendantsAtDepth Q j, Real.sqrt (vecNormSq (cubeAverageVec S F)) ^ p := by
      rw [negBesovLpDepthMean_rpow Q hp F j, descendantsAverage, ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hcard), one_mul]
    rw [hsum]
    exact hsingle
  /- invert the `p`-th pow -/
  have hgoal : Real.sqrt (vecNormSq (cubeAverageVec R F)) ^ p ≤
      (A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (j : ℝ))) ^ p := by
    refine hterm.trans ?_
    have hRHS : (A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (j : ℝ))) ^ p =
        ((descendantsAtDepth Q j).card : ℝ) * (A * (3 : ℝ) ^ (s * (j : ℝ))) ^ p := by
      have hpne : p ≠ 0 := ne_of_gt hp
      have hexp : (s + (d : ℝ) / p) * (j : ℝ) * p = (d : ℝ) * (j : ℝ) + s * (j : ℝ) * p := by
        field_simp
        ring
      rw [descendantsAtDepth_card_rpow,
        Real.mul_rpow hA (three_rpow_nonneg _),
        Real.mul_rpow hA (three_rpow_nonneg _),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hexp,
        Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring
    rw [hRHS]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (negBesovLpDepthMean_nonneg Q p F j) hmean (le_of_lt hp))
      (le_of_lt hcard)
  exact le_of_rpow_le_rpow (Real.sqrt_nonneg _)
    (mul_nonneg hA (three_rpow_nonneg _)) hp hgoal

end

end Algsuperdiff.Section4.Provider.Homogenization
