/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderOneStep
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundarySchauder

/-!
# CubeSchauderBoundaryTwin

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the boundary twin of the Lipschitz gradient atom

`CubeSchauderOneStep.exists_gradientLipschitz_interior` reads the harmonic
gradient atom `gradField_lipschitzOn_of_harmonic` at its own exponent `α = 1`
on the **interior** window family.  The proved boundary producer
`ExcessDecay.Schauder.exists_gradientHolder_boundary_raw` reads the *lossy* `α
= 1/2` corollary `gradField_holderHalf_of_harmonic` on the **reflected** window
family.

The `hdiam` slot of the Hölder corollary disappears; nothing else changes.

The only arithmetic difference from the interior twin is the excess normalizer.
On the interior window `|W₂|^{-1/d} ≥ 3^{-(n-2)}`; on the reflected window the
partial reflections can double each side, so `|W₂| ≤ (2·3^{n-2})^d` and

```text
  affineExcessRaw (reflectedWindow x m (n-2)) V
    ≤ 2 · 3^{n-2} · affineExcess (reflectedWindow x m (n-2)) V ,
```

which is the same factor `2` the proved `exists_gradientHolder_boundary`
carries.  The constant is therefore the interior `1296` doubled, at the
boundary ratio: `boundaryLipschitzWindowConst d = 2592 · schauderConst d ·
boundarySchauderRatioConst d`.

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

/-! ## 1. The constant -/

/-- **The Lipschitz Schauder constant of the boundary branch.**  `C(d)`
explicit: `2592 · schauderConst d · boundarySchauderRatioConst d`, where
`2592 = 2 · 4 · 324` collects the atom's factor `4`, the half-radius
`R = 3^{n-3}/2` with the two triadic scale gaps `n-3`, `n-2` against `n`, and
the reflection's normalizer factor `2`. -/
def boundaryLipschitzWindowConst (d : ℕ) [NeZero d] : ℝ :=
  2592 * schauderConst d * boundarySchauderRatioConst d

theorem boundaryLipschitzWindowConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ boundaryLipschitzWindowConst d :=
  mul_nonneg (mul_nonneg (by norm_num) (schauderConst_nonneg d))
    (boundarySchauderRatioConst_nonneg d)

/-! ## 2. Two arithmetic identities -/

/-- The scale bookkeeping of the boundary Lipschitz producer:
`(3^{n-3}/2)⁻² · 3^{n-2} = 324 · 3^{-n}`. -/
private theorem boundary_lipschitz_scale_identity (n : ℤ) :
    ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (3 : ℝ) ^ (n - 2)
      = 324 * (3 : ℝ) ^ (-n) := by
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  have h27 : (3 : ℝ) ^ (-3 : ℤ) = 1 / 27 := by norm_num
  have h9 : (3 : ℝ) ^ (-2 : ℤ) = 1 / 9 := by norm_num
  have hA3 : (3 : ℝ) ^ (n - 3) = (3 : ℝ) ^ n / 27 := by
    rw [show n - 3 = n + (-3 : ℤ) by ring, zpow_add₀ h3ne, h27]
    ring
  have hA2 : (3 : ℝ) ^ (n - 2) = (3 : ℝ) ^ n / 9 := by
    rw [show n - 2 = n + (-2 : ℤ) by ring, zpow_add₀ h3ne, h9]
    ring
  have hnpos : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  rw [hA3, hA2, zpow_neg]
  field_simp
  ring

/-- For `a > 0` and `d ≠ 0`, the `d`-th power composed with the `(-1/d)` rpow is
inversion. -/
private theorem rpow_neg_inv_pow_twin {a : ℝ} (ha : 0 < a) (hd : d ≠ 0) :
    (a ^ d) ^ (-(d : ℝ)⁻¹) = a⁻¹ := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  rw [← Real.rpow_natCast a d, ← Real.rpow_mul ha.le]
  rw [show (d : ℝ) * -(d : ℝ)⁻¹ = -1 by field_simp]
  rw [Real.rpow_neg_one]

/-! ## 3. The reflected excess normalizer -/

/-- **The reflected window's normalizer, one side.**

`|reflectedWindow x m k| ≤ (2·3^k)^d`, so the unnormalized excess minimum is at
most `2·3^k` times the normalized one.  This is the exact source of the factor
`2` carried by the proved `exists_gradientHolder_boundary`. -/
theorem affineExcessRaw_reflectedWindow_le (hd : d ≠ 0) {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) (hkm' : k < m)
    (V : Vec d → ℝ) :
    affineExcessRaw (reflectedWindow x m k) V
      ≤ 2 * (3 : ℝ) ^ k * affineExcess (reflectedWindow x m k) V := by
  have hpos : (0 : ℝ) < (volume (reflectedWindow x m k)).toReal :=
    volume_toReal_reflectedWindow_pos x hx hkm
  have hle : (volume (reflectedWindow x m k)).toReal ≤ (2 * (3 : ℝ) ^ k) ^ d :=
    volume_toReal_reflectedWindow_le x hx hkm hkm'
  have hkpos : (0 : ℝ) < 2 * (3 : ℝ) ^ k := by
    have h := zpow_pos (by norm_num : (0 : ℝ) < 3) k
    linarith only [h]
  have hexp : -(d : ℝ)⁻¹ ≤ 0 := by
    have h : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
    linarith only [h]
  have hnorm : (2 * (3 : ℝ) ^ k)⁻¹
      ≤ ((volume (reflectedWindow x m k)).toReal) ^ (-(d : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow_of_nonpos hpos hle hexp
    rwa [rpow_neg_inv_pow_twin hkpos hd] at h
  have hEnn : 0 ≤ affineExcessRaw (reflectedWindow x m k) V :=
    affineExcessRaw_nonneg _ _
  have hstep : (2 * (3 : ℝ) ^ k)⁻¹ * affineExcessRaw (reflectedWindow x m k) V
      ≤ affineExcess (reflectedWindow x m k) V := by
    rw [affineExcess]
    exact mul_le_mul_of_nonneg_right hnorm hEnn
  have hmul := mul_le_mul_of_nonneg_left hstep hkpos.le
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hkpos), one_mul] at hmul

/-! ## 4. The boundary Lipschitz atom -/

/-- **The harmonic gradient-Lipschitz bound on the reflected one-step window.**

For `V` classically harmonic on the partially reflected window
`reflectedWindow x m (n-2)`, the gradient field `gradField V` is Lipschitz on
the inner truncated window `(x + □_{n-3}) ∩ □_m` with constant

```text
  boundaryLipschitzWindowConst d · 3^{-n} · E(V, reflectedWindow x m (n-2)) .
```

This is `ExcessDecay.Schauder.exists_gradientHolder_boundary_raw` with the atom
read at its own exponent `α = 1` instead of the lossy `α = 1/2` corollary: the
six geometry slots are literally the ones the proved boundary producer already
feeds, and the `hdiam` slot is dropped. -/
theorem exists_gradientLipschitz_boundary [NeZero d] (hd : d ≠ 0) {m n : ℤ}
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m)
    {V : Vec d → ℝ}
    (hharm : HarmonicOnNhd (V ∘ toEuc.symm)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)))
    (hintsq : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun y => (V y - affineEval c g y) ^ 2)
        (reflectedWindow x m (n - 2)) volume) :
    ∀ p ∈ truncatedWindow x m (n - 3), ∀ q ∈ truncatedWindow x m (n - 3),
      ‖gradField V p - gradField V q‖
        ≤ (boundaryLipschitzWindowConst d * (3 : ℝ) ^ (-n)
            * affineExcess (reflectedWindow x m (n - 2)) V) * ‖p - q‖ := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 := by linarith only [h3]
  have hR2 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 / 2 := by linarith only [h3]
  have hatom := gradField_lipschitzOn_of_harmonic
    (S := (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2))
    (W := truncatedWindow x m (n - 3)) (W₂ := reflectedWindow x m (n - 2))
    (R := (3 : ℝ) ^ (n - 3) / 2) (ratio := boundarySchauderRatioConst d)
    hharm (convex_truncatedWindow x m (n - 3)) hR
    (boundarySchauderRatioConst_nonneg d)
    (fun p hp => metricBall_toEuc_subset_image_reflectedWindow hmn hx hp)
    (fun p hp => euclideanBall_subset_reflectedWindow hmn hx hp hR2
      (by linarith only [h3]))
    (volume_toReal_reflectedWindow_pos x hx (by omega))
    (fun p _ => lt_of_lt_of_le (by positivity) (volume_toReal_euclideanBall_ge p hR2))
    (fun p _ => sqrt_volume_ratio_reflected_le hx hmn p)
    hintsq
  set E : ℝ := affineExcessRaw (reflectedWindow x m (n - 2)) V with hEdef
  set A : ℝ := affineExcess (reflectedWindow x m (n - 2)) V with hAdef
  have hEnn : 0 ≤ E := affineExcessRaw_nonneg _ _
  have hAnn : 0 ≤ A := affineExcess_nonneg _ _
  have hEA : E ≤ 2 * (3 : ℝ) ^ (n - 2) * A :=
    affineExcessRaw_reflectedWindow_le hd hx (by omega) (by omega) V
  -- the constant comparison
  set C : ℝ := schauderConst d with hCdef
  set ra : ℝ := boundarySchauderRatioConst d with hradef
  have hCnn : 0 ≤ C := schauderConst_nonneg d
  have hrann : 0 ≤ ra := boundarySchauderRatioConst_nonneg d
  have hRinv : (0 : ℝ) ≤ ((3 : ℝ) ^ (n - 3) / 2)⁻¹ := inv_nonneg.2 hR.le
  have hcoef : (0 : ℝ) ≤ 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ra :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCnn) hRinv) hRinv) hrann
  have hkey : 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E)
      ≤ boundaryLipschitzWindowConst d * (3 : ℝ) ^ (-n) * A := by
    have hstep : 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E)
        ≤ 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ra
            * (2 * (3 : ℝ) ^ (n - 2) * A) := by
      have h := mul_le_mul_of_nonneg_left hEA hcoef
      linarith only [h]
    refine hstep.trans (le_of_eq ?_)
    have hid := boundary_lipschitz_scale_identity n
    have hexp : 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ra
          * (2 * (3 : ℝ) ^ (n - 2) * A)
        = 8 * C * ra * A
            * (((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹
              * (3 : ℝ) ^ (n - 2)) := by
      ring
    rw [hexp, hid, boundaryLipschitzWindowConst, ← hCdef, ← hradef]
    ring
  intro p hp q hq
  refine (hatom p hp q hq).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact hkey

end

end Algsuperdiff.Section4.Provider.Schauder
