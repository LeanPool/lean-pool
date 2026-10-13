/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepWindows
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AffineSplitLift

/-!
# OneStepCompetitor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The affine (Taylor) competitor: the affine contraction, first inequality

`e.phi.approx.by.affine` opens with the definition-level step

```text
  E(v, U_k)  ≤  C 3^{(n-k)/2} [∇v]_{C^{0,1/2}(U_3)} ,
```

This module proves it, on an arbitrary truncated window and at the
development's declared Hölder carrier `Support.HolderSeminormBoundOn W (1/2) K
G`:

* `affineExcessRaw_le_taylor` — the *raw* excess is at most the sup-norm residual
  of the first-order Taylor competitor built at the window centre `x` with the
  **average** slope `(∇v)_W`, i.e. `2 d K (3^k/2)^{3/2}`;
* `affineExcess_le_taylor` — dividing by the `|W|^{-1/d}` normalizer (which the
  truncated-window sandwich of `OneStepWindows` bounds by `9·3^{-k}`) turns this
  into

  ```text
    E(v, (x+□_k) ∩ □_m)  ≤  taylorContractionConst d · K · (3^k)^{1/2} ,
  ```

  which at `k = n-k'` is the printed `C 3^{(n-k')/2} [∇v]_{C^{0,1/2}}` exactly.

The two proved atoms consumed are
`AffineSplitLift.abs_sub_affineLift_volumeAverage_le` (the mean-value/Hölder
residual) and `SandwichNondegeneracyAttainment.normalizedL2On_le_of_abs_le`
(the `L^∞ → L²` conversion); the composition into `affineExcess` had no
consumer before this module (`affineResidualLevel` has none in the tree).

## What is NOT here (the residue this module makes precise)

The *second* inequality of `e.phi.approx.by.affine` substitutes the
Schauder bound on `K = [∇v]_{C^{0,1/2}(U_3)}`; that bound is a
harmonic-regularity estimate (a gradient-Hölder Schauder estimate up to a face
of `∂□_m`) and is **not proved anywhere** in this repository, in
CoarseGraining, or in Mathlib.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The raw Taylor bound -/

/-- **The affine competitor on a truncated window.**

The first-order Taylor polynomial of `f` at the window centre, built with the
*average* gradient, is an admissible affine competitor; its `L^∞` residual is the
Hölder/mean-value bound `2 d K r^{3/2}` at `r = 3^k/2`. -/
theorem affineExcessRaw_le_taylor {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {f : Vec d → ℝ}
    {G : Vec d → Vec d} {K : ℝ} (hK : 0 ≤ K)
    (hmem : MemLp f 2 (volume.restrict (truncatedWindow x m k)))
    (hint : ∀ i, IntegrableOn (fun p => G p i) (truncatedWindow x m k) volume)
    (hf : HasGradientOn (truncatedWindow x m k) f G)
    (hG : HolderSeminormBoundOn (truncatedWindow x m k) (1 / 2 : ℝ) K G) :
    affineExcessRaw (truncatedWindow x m k) f
      ≤ 2 * (d : ℝ) * K * ((3 : ℝ) ^ k / 2) ^ (3 / 2 : ℝ) := by
  have hMnn : (0 : ℝ) ≤ 2 * (d : ℝ) * K * ((3 : ℝ) ^ k / 2) ^ (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (by positivity) hK) (Real.rpow_nonneg (by positivity) _)
  have hxW : x ∈ truncatedWindow x m k := mem_truncatedWindow_self k hx
  have hbound : ∀ y ∈ truncatedWindow x m k,
      |f y - affineEval (f x - vecDot (volumeAverageVec (truncatedWindow x m k) G) x)
          (volumeAverageVec (truncatedWindow x m k) G) y|
        ≤ 2 * (d : ℝ) * K * ((3 : ℝ) ^ k / 2) ^ (3 / 2 : ℝ) := by
    intro y hy
    have h := abs_sub_affineLift_volumeAverage_le (W := truncatedWindow x m k) (f := f)
      (G := G) (K := K) (r := (3 : ℝ) ^ k / 2) (x := x) (y := y)
      (convex_truncatedWindow x m k) hxW hy hK (by positivity)
      (volume_truncatedWindow_pos k hx) (volume_truncatedWindow_lt_top x m k) hint hf hG
      (fun p hp => norm_sub_le_of_mem_truncatedWindow hp)
    rwa [affineLift_eq_affineEval] at h
  refine le_trans (affineExcessRaw_le_affineDistOn (truncatedWindow x m k) f
    (f x - vecDot (volumeAverageVec (truncatedWindow x m k) G) x)
    (volumeAverageVec (truncatedWindow x m k) G)) ?_
  rw [affineDistOn]
  exact normalizedL2On_le_of_abs_le (measurableSet_truncatedWindow x m k)
    (volume_toReal_truncatedWindow_pos x hx hkm)
    (ne_of_lt (volume_truncatedWindow_lt_top x m k)) hMnn
    (integrableOn_sub_affineEval_sq_truncatedWindow x hmem _ _) hbound

/-! ## 2. The excess form -/

/-- The constant of the affine-competitor contraction: `18 d (1/2)^{3/2}`, the
product of the normalizer slack `9` of the truncated-window sandwich and the
mean-value factor `2 d (1/2)^{3/2}`. -/
def taylorContractionConst (d : ℕ) : ℝ := 18 * (d : ℝ) * ((1 : ℝ) / 2) ^ (3 / 2 : ℝ)

theorem taylorContractionConst_nonneg (d : ℕ) : 0 ≤ taylorContractionConst d := by
  rw [taylorContractionConst]
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)

/-- **The affine contraction, first inequality.**

`E(v, (x+□_k) ∩ □_m) ≤ C(d) · [∇v]_{C^{0,1/2}} · (3^k)^{1/2}`.  At `k = n - j`
this is the printed `C 3^{(n-j)/2} [∇v]_{C^{0,1/2}(U_3)}`. -/
theorem affineExcess_le_taylor (hd : d ≠ 0) {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {f : Vec d → ℝ}
    {G : Vec d → Vec d} {K : ℝ} (hK : 0 ≤ K)
    (hmem : MemLp f 2 (volume.restrict (truncatedWindow x m k)))
    (hint : ∀ i, IntegrableOn (fun p => G p i) (truncatedWindow x m k) volume)
    (hf : HasGradientOn (truncatedWindow x m k) f G)
    (hG : HolderSeminormBoundOn (truncatedWindow x m k) (1 / 2 : ℝ) K G) :
    affineExcess (truncatedWindow x m k) f
      ≤ taylorContractionConst d * K * ((3 : ℝ) ^ k) ^ (1 / 2 : ℝ) := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hsplit : ((3 : ℝ) ^ k / 2) ^ (3 / 2 : ℝ)
      = ((3 : ℝ) ^ k) ^ (3 / 2 : ℝ) * ((1 : ℝ) / 2) ^ (3 / 2 : ℝ) := by
    rw [show (3 : ℝ) ^ k / 2 = (3 : ℝ) ^ k * ((1 : ℝ) / 2) by ring,
      Real.mul_rpow hpos.le (by norm_num)]
  have hkey : (3 : ℝ) ^ (-k) * ((3 : ℝ) ^ k) ^ (3 / 2 : ℝ) = ((3 : ℝ) ^ k) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one,
      ← mul_assoc, zpow_neg, inv_mul_cancel₀ hpos.ne', one_mul]
  obtain ⟨_, hnorm⟩ := rpow_volume_truncatedWindow_bounds hd x hx hkm
  have hraw := affineExcessRaw_le_taylor hx hkm hK hmem hint hf hG
  calc affineExcess (truncatedWindow x m k) f
      = ((volume (truncatedWindow x m k)).toReal) ^ (-(d : ℝ)⁻¹) *
          affineExcessRaw (truncatedWindow x m k) f := rfl
    _ ≤ (9 * (3 : ℝ) ^ (-k)) * (2 * (d : ℝ) * K * ((3 : ℝ) ^ k / 2) ^ (3 / 2 : ℝ)) :=
        mul_le_mul hnorm hraw (affineExcessRaw_nonneg _ _) (by positivity)
    _ = taylorContractionConst d * K * ((3 : ℝ) ^ k) ^ (1 / 2 : ℝ) := by
        rw [taylorContractionConst, hsplit, ← hkey]
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
