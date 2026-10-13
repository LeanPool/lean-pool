/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderProducer

/-!
# OneStepBoundarySchauder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Schauder gradient-Hölder estimate, boundary branch: the producer

`OneStepSchauderProducer.exists_gradientHolder_interior` instantiates the
Schauder atom at the *interior* ball family.  This module does the same at the
**boundary** family of `OneStepBoundaryGeometry`: the harmonicity domain is the
partially reflected window `reflectedWindow x m (n-2)`, on which the odd
extension of the competitor is classically harmonic
(`OneStepSchauderComposeBoundary.exists_classicalCompetitor_reflectedWindow`),
and the Hölder window is the branch's own `U_3 = (x + □_{n-3}) ∩ □_m`.

The output is **exactly** the four-slot package
`hint / hgrad / hhol / hschauder` that
`OneStepConditional.excessDecay_oneStep_of_harmonicApprox` consumes:

```text
  GV := gradField V ,
  ∀ i, IntegrableOn (fun p => GV p i) U_3 ,
  HasGradientOn U_3 V GV ,
  HolderSeminormBoundOn U_3 (1/2) K GV ,
  K ≤ Csch(d) · (3^{-n})^{1/2} · (3^{-(n-2)} · E_raw(V, reflectedWindow)) ,
```

with

```text
  Csch(d) = boundarySchauderConst d
          = 48 · 3^{3/2} · schauderConst d · √((24(d+1))^d) ,
```

the interior constant with `12(d+1)` replaced by `24(d+1)` — the sole cost of the
reflection is the `2^d` volume spread of `OddReflectionVolume`.

The **raw** form above is stated at the unnormalized excess minimum `E_raw`
together with the explicit scale factor `3^{-(n-2)}`, because that is the shape
in which the two downstream normalizers are read off:

* `exists_gradientHolder_boundary` divides by the *reflected* window's own
  normalizer `|reflectedWindow|^{-1/d} ≥ (2·3^{n-2})^{-1}`, giving the excess
  `E(V, reflectedWindow)` at the cost of a factor `2`;
* the split bound splits `E_raw` over `U_2 ⊔ (reflectedWindow \ U_2)`
  and divides by `U_2`'s normalizer, producing the manuscript's `C 3^{-n/2} E(v,
  U_2) + K_h` with `K_h` the far-side (datum) leg.

The raw display is *tight*: the inequality proved is the atom's own output with
the powers of `3` regrouped, no slack.

## References

* ABK26, `l.excess.decay.good.scales`, the Schauder gradient-Hölder estimate.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec basisVec euclideanBall openCubeSet originCube)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The constant -/

/-- **The Schauder constant of the boundary branch.**  `C(d)` explicit:
`48 · 3^{3/2} · schauderConst d · √((24(d+1))^d)`. -/
def boundarySchauderConst (d : ℕ) [NeZero d] : ℝ :=
  48 * (3 : ℝ) ^ (3 / 2 : ℝ) * schauderConst d * boundarySchauderRatioConst d

theorem boundarySchauderConst_nonneg (d : ℕ) [NeZero d] : 0 ≤ boundarySchauderConst d :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
    (schauderConst_nonneg d)) (boundarySchauderRatioConst_nonneg d)

/-! ## 2. The scale arithmetic -/

private theorem sqrt_zpow_div_self_boundary (n : ℤ) :
    Real.sqrt ((3 : ℝ) ^ (n - 3)) / (3 : ℝ) ^ (n - 3)
      = (3 : ℝ) ^ (3 / 2 : ℝ) * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hcast : ((3 : ℝ) ^ (n - 3)) = (3 : ℝ) ^ (((n : ℝ) - 3)) := by
    rw [show ((n : ℝ) - 3) = (((n - 3 : ℤ) : ℝ)) by push_cast; ring, Real.rpow_intCast]
  have hcastn : ((3 : ℝ) ^ (-n)) = (3 : ℝ) ^ ((-(n : ℝ))) := by
    rw [show (-(n : ℝ)) = (((-n : ℤ) : ℝ)) by push_cast; ring, Real.rpow_intCast]
  rw [Real.sqrt_eq_rpow, hcast, hcastn, ← Real.rpow_mul h3.le, ← Real.rpow_mul h3.le,
    ← Real.rpow_sub h3, ← Real.rpow_add h3]
  congr 1
  ring

/-! ## 3. The producer, raw form -/

/-- **The Schauder gradient-Hölder estimate, boundary branch — the producer, raw form.**

For `V` classically harmonic on the partially reflected window
`reflectedWindow x m (n-2)`, the gradient field `gradField V` realizes the four
slots `hint / hgrad / hhol / hschauder` of
`OneStepConditional.excessDecay_oneStep_of_harmonicApprox`, with

```text
  Csch = boundarySchauderConst d
```

and the right-hand side read at the *unnormalized* excess minimum on the
reflected window.  No interior hypothesis, and no restriction on the met set. -/
theorem exists_gradientHolder_boundary_raw [NeZero d] {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m)
    {V : Vec d → ℝ}
    (hharm : HarmonicOnNhd (V ∘ toEuc.symm)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)))
    (hintsq : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun y => (V y - affineEval c g y) ^ 2)
        (reflectedWindow x m (n - 2)) volume) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ i, IntegrableOn (fun p => gradField V p i) (truncatedWindow x m (n - 3)) volume) ∧
      HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
      HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K (gradField V) ∧
      K ≤ boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
            * ((3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (reflectedWindow x m (n - 2)) V) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 := by linarith only [h3]
  have hR2 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 / 2 := by linarith only [h3]
  have htne : ((3 : ℝ) ^ (n - 3)) ≠ 0 := ne_of_gt h3
  have hWS : ∀ p ∈ truncatedWindow x m (n - 3),
      toEuc p ∈ (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2) :=
    fun p hp => ⟨p, truncatedWindow_subset_reflectedWindow x m (n - 2)
      (truncatedWindow_mono x m (by omega : n - 3 ≤ n - 2) hp), rfl⟩
  -- the Hölder bound with the atom's constant, at the boundary ball family
  have hhol0 := gradField_holderHalf_of_harmonic
    (S := (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2))
    (W := truncatedWindow x m (n - 3)) (W₂ := reflectedWindow x m (n - 2))
    (R := (3 : ℝ) ^ (n - 3) / 2) (ratio := boundarySchauderRatioConst d)
    (D := (3 : ℝ) ^ (n - 3)) hharm (convex_truncatedWindow x m (n - 3)) hR
    (boundarySchauderRatioConst_nonneg d)
    (fun p hp => metricBall_toEuc_subset_image_reflectedWindow hmn hx hp)
    (fun p hp => euclideanBall_subset_reflectedWindow hmn hx hp hR2 (by linarith only [h3]))
    (volume_toReal_reflectedWindow_pos x hx (by omega))
    (fun p _ => lt_of_lt_of_le (by positivity) (volume_toReal_euclideanBall_ge p hR2))
    (fun p _ => sqrt_volume_ratio_reflected_le hx hmn p)
    hintsq
    (fun p hp q hq => norm_sub_le_of_mem_truncatedWindow_pair hp hq)
  set E : ℝ := affineExcessRaw (reflectedWindow x m (n - 2)) V with hEdef
  set C : ℝ := schauderConst d with hCdef
  set ra : ℝ := boundarySchauderRatioConst d with hradef
  have hEnn : 0 ≤ E := affineExcessRaw_nonneg _ _
  have hCnn : 0 ≤ C := schauderConst_nonneg d
  have hrann : 0 ≤ ra := boundarySchauderRatioConst_nonneg d
  have hKnn : (0 : ℝ) ≤ 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹
      * (ra * E) * Real.sqrt ((3 : ℝ) ^ (n - 3)) := by
    have hs : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (n - 3)) := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) hCnn) (inv_nonneg.2 hR.le)) (inv_nonneg.2 hR.le))
      (mul_nonneg hrann hEnn)) hs
  have hrewrite : 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E)
        * Real.sqrt ((3 : ℝ) ^ (n - 3))
      = 48 * C * ra * E * (Real.sqrt ((3 : ℝ) ^ (n - 3)) / (3 : ℝ) ^ (n - 3))
          * ((3 : ℝ) ^ (-(n - 2))) := by
    have hinv : (3 : ℝ) ^ (-(n - 2)) = ((3 : ℝ) ^ (n - 3))⁻¹ / 3 := by
      rw [zpow_neg, show n - 2 = (n - 3) + 1 by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
      field_simp
    rw [hinv]
    field_simp
    ring
  have hfinal : 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E)
        * Real.sqrt ((3 : ℝ) ^ (n - 3))
      ≤ boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * ((3 : ℝ) ^ (-(n - 2)) * E) := by
    rw [hrewrite, sqrt_zpow_div_self_boundary n, boundarySchauderConst, ← hCdef, ← hradef]
    refine le_of_eq ?_
    ring
  refine ⟨4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E)
      * Real.sqrt ((3 : ℝ) ^ (n - 3)), hKnn, ?_, ?_, hhol0, hfinal⟩
  · intro i
    exact integrableOn_gradField_coord (K := 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹
        * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E) * Real.sqrt ((3 : ℝ) ^ (n - 3)))
      (D := (3 : ℝ) ^ (n - 3))
      (measurableSet_truncatedWindow x m (n - 3))
      (ne_of_lt (volume_truncatedWindow_lt_top x m (n - 3))) hKnn
      (fun j => continuousOn_gradField_coord hharm hWS j) hhol0
      (fun p hp q hq => norm_sub_le_of_mem_truncatedWindow_pair hp hq)
      (mem_truncatedWindow_self (n - 3) hx) i
  · exact hasGradientOn_gradField hharm hWS

/-! ## 4. The producer at the reflected window's own normalizer -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
