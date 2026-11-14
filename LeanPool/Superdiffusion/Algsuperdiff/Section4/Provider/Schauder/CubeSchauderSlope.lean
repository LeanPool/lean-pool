/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderCampanato

/-!
# CubeSchauderSlope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the vector slope comparison of two nested windows

`CubeSchauderCampanato.affineExcess_le_campanato` controls the excess of the
zero-datum solution on every truncated window.  Converting that Campanato bound
into a *pointwise* statement about the gradient needs the slopes of the affine
minimizers to form a Cauchy family, and for that the **vector** difference
`g − g'` must be controlled, not merely the difference of magnitudes
`|‖g‖ − ‖g'‖|` that `ExcessDecay.SlopeStability` exports.

The proved proof of `slopeStability_of_axisCubeSandwich` produces the vector
bound internally and then discards it in its very last step (the reverse
triangle inequality).  This module re-derives the strictly stronger statement,
in a two-window form that additionally allows the two windows to have
**different centres** — which is what the two-point Hölder estimate needs:

```text
  |∇ℓ(u,W) − ∇ℓ(u,W')| ≤ c₀(θ)⁻¹ · (E(u,W') + κ · E(u,W))   for W' ⊆ W .
```

The two ingredients are exactly the two proved halves of `e.grad.stability`:
`normalizedL2On_affineEval_sub_le` (Minkowski plus the volume ratio) and
`normalizedL2On_affineEval_ge_of_sandwich` (the exact cube second moment).
Nothing new is proved about either.

## Main results

* `slopeMagnitude_sub_le_of_sandwich` — the abstract two-window vector bound.
* `affineMinimizerPair` / `windowSlope` — the canonical minimizer choice,
  indexed by the **window set** so that equal windows get equal slopes.
* `slopeMagnitude_windowSlope_sub_le` — the bound on truncated windows, at the
  scale-free constant `slopeStabilityConst d (1/9) (volumeRatioConstTriadic d)`.

## References

* ABK26, (`e.grad.stability`); Armstrong--Kuusi, *Elliptic Regularity*,
  Proposition `p.Schauder.C1alpha`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The `rpow` bookkeeping -/

/-- `√(A/B)·A^e = (A/B)^{e+1/2}·B^e`: the identity that turns the volume-ratio
factor of the Minkowski step into the excess normalizer of the smaller window.
(A local copy of the private `SlopeStability.rpow_slope_identity`.) -/
private theorem rpow_ratio_identity {A B e : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.sqrt (A / B) * A ^ e = (A / B) ^ (e + 1 / 2) * B ^ e := by
  have hAB : (0 : ℝ) < A / B := div_pos hA hB
  have hBe : B ^ e ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hB e)
  rw [Real.sqrt_eq_rpow, Real.rpow_add hAB e (1 / 2), Real.div_rpow hA.le hB.le e]
  field_simp

/-! ## 2. The abstract two-window vector bound -/

/-- **The vector slope comparison of two nested windows.**

If `(c,g)` minimizes the affine deviation of `u` on `W`, `(c',g')` minimizes it
on `W' ⊆ W`, `W'` carries an aspect-`θ` cube sandwich and `W` sits inside a
cube, then

```text
  |g − g'| ≤ c₀(θ)⁻¹ · (E(u,W') + κ · E(u,W)) ,
```

with `κ` any bound for the volume-ratio power `(|W|/|W'|)^{1/d+1/2}`.

This is `slopeStability_of_axisCubeSandwich`'s chain stopped one step early: the
proved statement applies the reverse triangle inequality
`| ‖g‖ − ‖g'‖ | ≤ ‖g − g'‖` at the end and so exports only the weaker scalar
form.  Neither window has to be centred at the same point. -/
theorem slopeMagnitude_sub_le_of_sandwich (hd : 0 < d)
    {W W' : Set (Vec d)} {u : Vec d → ℝ} {c c' : ℝ} {g g' : Vec d}
    {zin' zout' zout : Vec d} {Lin' Lout' Lout θ κ : ℝ}
    (hLin' : 0 < Lin') (hLout' : 0 < Lout') (hLout : 0 < Lout)
    (hθ0 : 0 < θ) (hθ : θ * Lout' ≤ Lin')
    (hin' : axisCube zin' Lin' ⊆ W') (hout' : W' ⊆ axisCube zout' Lout')
    (hout : W ⊆ axisCube zout Lout)
    (hsub : W' ⊆ W) (hWpos : 0 < (volume W).toReal)
    (hmeasW : MeasurableSet W) (hmeas' : MeasurableSet W')
    (hu : MemLp u 2 (volume.restrict W))
    (hratio : ((volume W).toReal / (volume W').toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) ≤ κ)
    (hmin : IsAffineMinimizer W u c g) (hmin' : IsAffineMinimizer W' u c' g') :
    slopeMagnitude (g - g') ≤ (ndConst d θ)⁻¹ * (affineExcess W' u + κ * affineExcess W u) := by
  have hW'pos : 0 < (volume W').toReal := volume_toReal_pos_of_sandwich hLin' hin' hout'
  have hu' : MemLp u 2 (volume.restrict W') :=
    hu.mono_measure (Measure.restrict_mono hsub le_rfl)
  have haff' : ∀ (a : ℝ) (b : Vec d), MemLp (affineEval a b) 2 (volume.restrict W') :=
    fun a b => memLp_affineEval_of_sandwich hLout' hmeas' hout' a b
  have haffW : MemLp (affineEval c g) 2 (volume.restrict W) :=
    memLp_affineEval_of_sandwich hLout hmeasW hout c g
  have hmemW : MemLp (fun x => u x - affineEval c g x) 2 (volume.restrict W) := hu.sub haffW
  have hint : IntegrableOn (fun x => (u x - affineEval c g x) ^ 2) W :=
    (memLp_two_iff_integrable_sq hmemW.aestronglyMeasurable).1 hmemW
  -- the two proved halves
  have hcore := normalizedL2On_affineEval_sub_le hsub hWpos hW'pos hu' haff' hint hmin hmin'
  have hnd := normalizedL2On_affineEval_ge_of_sandwich hd hLin' hLout' hθ0 hθ hin' hout'
    (c - c') (g - g')
  -- undo the excess normalizers
  have hrawW := affineExcessRaw_eq_rpow_mul_affineExcess hWpos u
  have hrawW' := affineExcessRaw_eq_rpow_mul_affineExcess hW'pos u
  have hid := rpow_ratio_identity (e := (d : ℝ)⁻¹) hWpos hW'pos
  set B : ℝ := ((volume W').toReal) ^ ((d : ℝ)⁻¹) with hBdef
  have hBpos : 0 < B := Real.rpow_pos_of_pos hW'pos _
  have hEW : 0 ≤ affineExcess W u := affineExcess_nonneg _ _
  have hEW' : 0 ≤ affineExcess W' u := affineExcess_nonneg _ _
  have hchain : ndConst d θ * B * slopeMagnitude (g - g')
      ≤ B * affineExcess W' u
        + (((volume W).toReal / (volume W').toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) * B)
            * affineExcess W u := by
    have h := hnd.trans hcore
    rw [hrawW, hrawW'] at h
    calc ndConst d θ * B * slopeMagnitude (g - g')
        ≤ B * affineExcess W' u
          + Real.sqrt ((volume W).toReal / (volume W').toReal)
            * (((volume W).toReal) ^ ((d : ℝ)⁻¹) * affineExcess W u) := h
      _ = B * affineExcess W' u
          + (Real.sqrt ((volume W).toReal / (volume W').toReal)
              * ((volume W).toReal) ^ ((d : ℝ)⁻¹)) * affineExcess W u := by ring
      _ = B * affineExcess W' u
          + (((volume W).toReal / (volume W').toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) * B)
              * affineExcess W u := by rw [hid]
  have hkap : (((volume W).toReal / (volume W').toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) * B)
      * affineExcess W u ≤ (κ * B) * affineExcess W u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hBpos.le) hEW
  have hfinal : ndConst d θ * B * slopeMagnitude (g - g')
      ≤ B * (affineExcess W' u + κ * affineExcess W u) := by
    have hexp : B * (affineExcess W' u + κ * affineExcess W u)
        = B * affineExcess W' u + (κ * B) * affineExcess W u := by ring
    rw [hexp]
    linarith only [hchain, hkap]
  have hc₀ : 0 < ndConst d θ := ndConst_pos hθ0
  have hdiv : ndConst d θ * slopeMagnitude (g - g')
      ≤ affineExcess W' u + κ * affineExcess W u :=
    le_of_mul_le_mul_left (by linarith only [hfinal]) hBpos
  rw [inv_mul_eq_div, le_div_iff₀ hc₀]
  linarith only [hdiv]

/-! ## 3. The canonical minimizer of a window -/

/-- The canonical affine minimizer of `u` on `W`, indexed by the **set** `W`.

Indexing by the set (rather than by a centre/scale pair) is what makes
`affineMinimizerPair_congr` available: two truncated windows that happen to be
the same set get the same minimizer, which is exactly what the far-apart case
of the two-point Hölder estimate uses. -/
def affineMinimizerPair (W : Set (Vec d)) (u : Vec d → ℝ) : ℝ × Vec d :=
  Classical.epsilon fun p : ℝ × Vec d => IsAffineMinimizer W u p.1 p.2

theorem isAffineMinimizer_affineMinimizerPair {W : Set (Vec d)} {u : Vec d → ℝ}
    (h : ∃ p : ℝ × Vec d, IsAffineMinimizer W u p.1 p.2) :
    IsAffineMinimizer W u (affineMinimizerPair W u).1 (affineMinimizerPair W u).2 :=
  Classical.epsilon_spec h

/-- The slope of the canonical minimizer on the truncated window `(x+□_k) ∩ □_m`. -/
def windowSlope (m : ℤ) (u : Vec d → ℝ) (x : Vec d) (k : ℤ) : Vec d :=
  (affineMinimizerPair (truncatedWindow x m k) u).2

theorem isAffineMinimizer_windowSlope {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m k))) :
    IsAffineMinimizer (truncatedWindow x m k) u
      (affineMinimizerPair (truncatedWindow x m k) u).1 (windowSlope m u x k) := by
  obtain ⟨c, g, hcg⟩ := exists_isAffineMinimizer_truncatedWindow hx hkm hu
  exact isAffineMinimizer_affineMinimizerPair ⟨(c, g), hcg⟩

/-! ## 4. The bound on truncated windows -/

/-- The volume ratio of two truncated windows whose scales differ by at most one
is at most the triadic constant `3^{3d}`. -/
theorem volume_ratio_truncatedWindow_pair_le {m k l : ℤ} {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hy : y ∈ openCubeSet (originCube d m))
    (hkm : k - 1 ≤ m) (hlm : l - 1 ≤ m) (hlk : l ≤ k + 1) :
    (volume (truncatedWindow x m l)).toReal / (volume (truncatedWindow y m k)).toReal
      ≤ ((3 : ℝ) ^ (3 * d) : ℝ) := by
  have hup := (volume_toReal_truncatedWindow_bounds x hx hlm).2
  have hlo := (volume_toReal_truncatedWindow_bounds y hy hkm).1
  have hlopos : (0 : ℝ) < ((3 : ℝ) ^ (k - 2)) ^ d := by positivity
  have hden : 0 < (volume (truncatedWindow y m k)).toReal := lt_of_lt_of_le hlopos hlo
  rw [div_le_iff₀ hden]
  have hstep : ((3 : ℝ) ^ l) ^ d ≤ ((3 : ℝ) ^ (3 * d) : ℝ) * ((3 : ℝ) ^ (k - 2)) ^ d := by
    have hpow : ((3 : ℝ) ^ (3 * d) : ℝ) = ((3 : ℝ) ^ (3 : ℤ)) ^ d := by
      rw [pow_mul]
      norm_num
    rw [hpow, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have hz : ((3 : ℝ) ^ (3 : ℤ)) * (3 : ℝ) ^ (k - 2) = (3 : ℝ) ^ (k + 1) := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    rw [hz]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  refine hup.trans (hstep.trans ?_)
  exact mul_le_mul_of_nonneg_left hlo (by positivity)

/-- **The vector slope comparison on truncated windows.**

For base points `x, y ∈ □_m` and scales `l ≤ k + 1` with
`(y+□_k) ∩ □_m ⊆ (x+□_l) ∩ □_m`,

```text
  |∇ℓ(u,W_k(y)) − ∇ℓ(u,W_l(x))|
      ≤ C_stab(d) · (E(u,W_k(y)) + E(u,W_l(x))) ,
```

with `C_stab(d) = slopeStabilityConst d (1/9) (volumeRatioConstTriadic d)`, the
proved scale-free constant of `e.grad.stability`. -/
theorem slopeMagnitude_windowSlope_sub_le (hd : 0 < d) {m k l : ℤ} {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hy : y ∈ openCubeSet (originCube d m))
    (hkm : k - 1 ≤ m) (hlm : l - 1 ≤ m) (hlk : l ≤ k + 1)
    (hsub : truncatedWindow y m k ⊆ truncatedWindow x m l)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (truncatedWindow x m l))) :
    slopeMagnitude (windowSlope m u x l - windowSlope m u y k)
      ≤ slopeStabilityConst d (1 / 9 : ℝ) (volumeRatioConstTriadic d)
        * (affineExcess (truncatedWindow y m k) u
            + affineExcess (truncatedWindow x m l) u) := by
  obtain ⟨zin', zout', hin', hout'⟩ := exists_axisCube_sandwich_truncatedWindow y hy hkm
  obtain ⟨_, zout, _, hout⟩ := exists_axisCube_sandwich_truncatedWindow x hx hlm
  have hu' : MemLp u 2 (volume.restrict (truncatedWindow y m k)) :=
    hu.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hminW := isAffineMinimizer_windowSlope hx hlm hu
  have hminW' := isAffineMinimizer_windowSlope hy hkm hu'
  have hWpos : 0 < (volume (truncatedWindow x m l)).toReal :=
    volume_toReal_truncatedWindow_pos x hx hlm
  have hW'pos : 0 < (volume (truncatedWindow y m k)).toReal :=
    volume_toReal_truncatedWindow_pos y hy hkm
  have hexp : (0 : ℝ) ≤ (d : ℝ)⁻¹ + 1 / 2 := by positivity
  have hratio : ((volume (truncatedWindow x m l)).toReal
        / (volume (truncatedWindow y m k)).toReal) ^ ((d : ℝ)⁻¹ + 1 / 2)
      ≤ volumeRatioConstTriadic d := by
    rw [volumeRatioConstTriadic]
    exact Real.rpow_le_rpow (by positivity)
      (volume_ratio_truncatedWindow_pair_le hx hy hkm hlm hlk) hexp
  have hkey := slopeMagnitude_sub_le_of_sandwich (u := u) hd
    (zin' := zin') (zout' := zout') (zout := zout)
    (Lin' := (3 : ℝ) ^ (k - 2)) (Lout' := (3 : ℝ) ^ k) (Lout := (3 : ℝ) ^ l)
    (θ := (1 / 9 : ℝ)) (κ := volumeRatioConstTriadic d)
    (by positivity) (by positivity) (by positivity) (by norm_num)
    (le_of_eq (triadic_aspect k)) hin' hout' hout hsub hWpos
    (measurableSet_truncatedWindow x m l) (measurableSet_truncatedWindow y m k)
    hu hratio hminW hminW'
  refine hkey.trans ?_
  have hone : (1 : ℝ) ≤ volumeRatioConstTriadic d := one_le_volumeRatioConstTriadic d
  have hc₀ : 0 < ndConst d (1 / 9 : ℝ) := ndConst_pos (by norm_num)
  have hE' : 0 ≤ affineExcess (truncatedWindow y m k) u := affineExcess_nonneg _ _
  have hstep : affineExcess (truncatedWindow y m k) u
        + volumeRatioConstTriadic d * affineExcess (truncatedWindow x m l) u
      ≤ volumeRatioConstTriadic d
        * (affineExcess (truncatedWindow y m k) u
            + affineExcess (truncatedWindow x m l) u) := by
    have h := mul_le_mul_of_nonneg_right hone hE'
    rw [one_mul] at h
    linarith only [h]
  have hmul := mul_le_mul_of_nonneg_left hstep (inv_nonneg.2 hc₀.le)
  refine hmul.trans (le_of_eq ?_)
  rw [slopeStabilityConst]
  field_simp

end

end Algsuperdiff.Section4.Provider.Schauder
