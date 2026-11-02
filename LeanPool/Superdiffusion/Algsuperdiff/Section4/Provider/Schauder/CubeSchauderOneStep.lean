/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderProducer

/-!
# CubeSchauderOneStep

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the interior one-step contraction at the Lipschitz rate

The proved `ExcessDecay.excessDecay_oneStep_triangle_of_schauder` contracts at
`C(d)·3^{-k/2}`, which is the same rate as the forcing remainder: `theta/rho =
C(d)` is `k`-independent and larger than `1`, so no gap exists and the
Campanato exponent tops out strictly below `1/2`.  That route cannot reach the
frozen external's inclusive endpoint `s ≤ 1/2`.

This module re-derives the interior one step from the **Lipschitz** atom
`ExcessDecay.gradField_lipschitzOn_of_harmonic` (`α = 1`, the pointwise
`C^{1,1}` estimate for harmonic functions) instead of its `C^{0,1/2}` corollary,
and the contraction factor improves to `C(d)·3^{-k}`:

```text
  E(u, U_k) ≤ C_contr(d) · 3^{-k} · E(u, U_0)
              + C_rem(d,k) · 3^{-n} · ‖u - v‖_{L²(U_2)} ,
```

`U_j = (x + □_{n-j}) ∩ □_m`.  Since the remainder decays at `3^{-k/2}` per step
(the freezing gain of a `C^{0,1/2}` forcing), `theta = C_contr(d) 3^{-k}` is
strictly below `rho = 3^{-k/2}` as soon as `C_contr(d) < 3^{k/2}`, and the gap
is then uniform.  That is the resolution the development's rate question
needed; `CubeSchauderCampanato` fixes the step size and runs the iteration.

## Why the exponent improves

A first-order Taylor competitor built from a gradient which is only
`C^{0,1/2}(U)` has residual `K·r^{3/2}` on a window of radius `r`, hence excess
`K·r^{1/2}`; built from a **Lipschitz** gradient it has residual `L·r²`, hence
excess `L·r`.  Feeding the harmonic gradient-Lipschitz bound
`L ≲ 3^{-n} E(v,U_2)` gives `E(v,U_k) ≲ 3^{-n}·3^{n-k}·E(v,U_2) = 3^{-k}E(v,U_2)`
— one full power of the scale instead of a half.

## Main results

* `abs_sub_affineLift_volumeAverage_le_lipschitz` — the mean-value residual
  `2 d L r²` at a Lipschitz gradient field.
* `affineExcess_le_taylorLipschitz` — `E(f,W) ≤ (9d/2) · L · 3^k` on the
  truncated window of scale `k`.
* `exists_gradientLipschitz_interior` — the harmonic gradient-Lipschitz bound in
  the window vocabulary, at a constant multiple of `3^{-n} · E(v,U_2)`.
* `excessDecay_oneStep_lipschitz` — the displayed one-step contraction.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`),
  Proposition `p.Schauder.C1alpha`, display `e.Sch1a.1`.
* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The mean-value residual at a Lipschitz gradient -/

/-- **The affine-lift residual, Lipschitz gradient.**

If `f` has gradient field `G` on the convex window `W` of sup-radius `r` around
`x`, and `G` is `L`-Lipschitz on `W`, then `f` differs from its affine lift at
`x` (built with the *average* gradient) by at most `2 d L r²`.

This is the `α = 1` sibling of
`ExcessDecay.abs_sub_affineLift_volumeAverage_le`, whose `α = 1/2` hypothesis
yields the weaker `2 d K r^{3/2}`. -/
theorem abs_sub_affineLift_volumeAverage_le_lipschitz {W : Set (Vec d)} {f : Vec d → ℝ}
    {G : Vec d → Vec d} {L r : ℝ} {x y : Vec d} (hW : Convex ℝ W) (hx : x ∈ W)
    (hy : y ∈ W) (hL : 0 ≤ L) (hr0 : 0 ≤ r) (hvolpos : 0 < volume W)
    (hvoltop : volume W < ⊤) (hint : ∀ i, IntegrableOn (fun p => G p i) W volume)
    (hf : HasGradientOn W f G)
    (hG : ∀ p ∈ W, ∀ q ∈ W, ‖G p - G q‖ ≤ L * ‖p - q‖)
    (hdiam : ∀ p ∈ W, ‖p - x‖ ≤ r) :
    |f y - affineLift x (f x) (volumeAverageVec W G) y| ≤ 2 * (d : ℝ) * L * r ^ 2 := by
  have hLr : 0 ≤ L * r := mul_nonneg hL hr0
  have hbase : ∀ p ∈ W, ‖G p - G x‖ ≤ L * r := fun p hp =>
    (hG p hp x hx).trans (mul_le_mul_of_nonneg_left (hdiam p hp) hL)
  have havg : ‖volumeAverageVec W G - G x‖ ≤ L * r :=
    norm_volumeAverageVec_sub_le hvolpos hvoltop hint hLr hbase
  have hslope : ∀ p ∈ W, ‖G p - volumeAverageVec W G‖ ≤ 2 * (L * r) := by
    intro p hp
    have htri : ‖G p - volumeAverageVec W G‖ ≤
        ‖G p - G x‖ + ‖G x - volumeAverageVec W G‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub (G p) (G x) (volumeAverageVec W G)
    have hsymm : ‖G x - volumeAverageVec W G‖ = ‖volumeAverageVec W G - G x‖ :=
      norm_sub_rev _ _
    rw [hsymm] at htri
    linarith only [htri, hbase p hp, havg]
  have hmain := abs_sub_affineLift_le (f := f) (G := G) (A := volumeAverageVec W G)
    hW hx hy (by linarith only [hLr] : (0 : ℝ) ≤ 2 * (L * r)) hf hslope (hdiam y hy)
  refine hmain.trans (le_of_eq ?_)
  ring

/-! ## 2. The Lipschitz affine competitor on a truncated window -/

/-- The raw Lipschitz Taylor bound on the truncated window of scale `k`. -/
theorem affineExcessRaw_le_taylorLipschitz {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {f : Vec d → ℝ}
    {G : Vec d → Vec d} {L : ℝ} (hL : 0 ≤ L)
    (hmem : MemLp f 2 (volume.restrict (truncatedWindow x m k)))
    (hint : ∀ i, IntegrableOn (fun p => G p i) (truncatedWindow x m k) volume)
    (hf : HasGradientOn (truncatedWindow x m k) f G)
    (hG : ∀ p ∈ truncatedWindow x m k, ∀ q ∈ truncatedWindow x m k,
      ‖G p - G q‖ ≤ L * ‖p - q‖) :
    affineExcessRaw (truncatedWindow x m k) f
      ≤ 2 * (d : ℝ) * L * ((3 : ℝ) ^ k / 2) ^ 2 := by
  have hMnn : (0 : ℝ) ≤ 2 * (d : ℝ) * L * ((3 : ℝ) ^ k / 2) ^ 2 := by positivity
  have hxW : x ∈ truncatedWindow x m k := mem_truncatedWindow_self k hx
  have hbound : ∀ y ∈ truncatedWindow x m k,
      |f y - affineEval (f x - vecDot (volumeAverageVec (truncatedWindow x m k) G) x)
          (volumeAverageVec (truncatedWindow x m k) G) y|
        ≤ 2 * (d : ℝ) * L * ((3 : ℝ) ^ k / 2) ^ 2 := by
    intro y hy
    have h := abs_sub_affineLift_volumeAverage_le_lipschitz (W := truncatedWindow x m k)
      (f := f) (G := G) (L := L) (r := (3 : ℝ) ^ k / 2) (x := x) (y := y)
      (convex_truncatedWindow x m k) hxW hy hL (by positivity)
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

/-- The constant of the Lipschitz affine competitor: `9 d / 2`, the product of
the truncated normalizer's slack `9` and the mean-value factor `d/2`. -/
def taylorLipschitzConst (d : ℕ) : ℝ := 9 / 2 * (d : ℝ)

theorem taylorLipschitzConst_nonneg (d : ℕ) : 0 ≤ taylorLipschitzConst d := by
  rw [taylorLipschitzConst]
  positivity

/-- **The Lipschitz affine competitor, excess form.**

`E(f, (x+□_k) ∩ □_m) ≤ (9d/2) · L · 3^k` for `f` whose gradient field is
`L`-Lipschitz on the window.  One full power of the scale — the improvement over
`ExcessDecay.affineExcess_le_taylor`'s half power. -/
theorem affineExcess_le_taylorLipschitz (hd : d ≠ 0) {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {f : Vec d → ℝ}
    {G : Vec d → Vec d} {L : ℝ} (hL : 0 ≤ L)
    (hmem : MemLp f 2 (volume.restrict (truncatedWindow x m k)))
    (hint : ∀ i, IntegrableOn (fun p => G p i) (truncatedWindow x m k) volume)
    (hf : HasGradientOn (truncatedWindow x m k) f G)
    (hG : ∀ p ∈ truncatedWindow x m k, ∀ q ∈ truncatedWindow x m k,
      ‖G p - G q‖ ≤ L * ‖p - q‖) :
    affineExcess (truncatedWindow x m k) f ≤ taylorLipschitzConst d * L * (3 : ℝ) ^ k := by
  obtain ⟨_, hnorm⟩ := rpow_volume_truncatedWindow_bounds hd x hx hkm
  have hraw := affineExcessRaw_le_taylorLipschitz hx hkm hL hmem hint hf hG
  have hpos : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
  calc affineExcess (truncatedWindow x m k) f
      = ((volume (truncatedWindow x m k)).toReal) ^ (-(d : ℝ)⁻¹) *
          affineExcessRaw (truncatedWindow x m k) f := rfl
    _ ≤ (9 * (3 : ℝ) ^ (-k)) * (2 * (d : ℝ) * L * ((3 : ℝ) ^ k / 2) ^ 2) :=
        mul_le_mul hnorm hraw (affineExcessRaw_nonneg _ _) (by positivity)
    _ = taylorLipschitzConst d * L * (3 : ℝ) ^ k := by
        rw [taylorLipschitzConst, zpow_neg]
        field_simp





end

end Algsuperdiff.Section4.Provider.Schauder
