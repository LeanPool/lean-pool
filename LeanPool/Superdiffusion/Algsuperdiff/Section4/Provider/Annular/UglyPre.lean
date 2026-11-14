/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.ResponseJSensitivityUnconditional
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Definition

/-!
# UglyPre

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 2 of `p.mathcalE.annular.decomp`: the sensitivity estimate at the
`(mu, sigma_0, h)`-witness

ABK26, Section 4.1, (`e.ugly.estimate.for.J.pre`).  The manuscript
localizes the response functional by applying the unconditional
sensitivity estimate `l.J.sensitivity.no.conditions` at the witness

```
  mu := sigmaBar_m * sigmaBar_{n-2}^{-1} ,
  sigma_0 := sigmaBar_{n-2} ,
  h := k_L - (k_L - k_m)_{cube_m} - k_{n-2}
```

on each cube `z + cube_n`.  This module proves that instantiation over the
proved running diffusivity, from the Section 2.4 anchor
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity_unconditional`.

The witness is exactly what makes the display's left side the manuscript's
`J(., sigmaBar_m^{-1/2} e, sigmaBar_m^{1/2} e)`: the anchor's load pair is at
the product gauge `mu * sigma_0`, and here `mu * sigma_0 = sigmaBar_m`.  That
identity is the arithmetic content of the parameter choice, and it is proved,
not assumed.

## Two forms

* `exists_responseJ_ugly_pre_terms` -- the anchor's terms at the witness.  This
  is the shape the downstream per-term collapse consumes (each of the anchor's
  last two terms is patched separately).
* `exists_responseJ_ugly_pre` -- the manuscript's printed three-term display, obtained
  from the four-term form by packaging the anchor's third and fourth terms into
  the single last term `C ((sigmaBar_m^{-1} + lambda^{-1}) ||grad h||)^2`.

## The `s <= 1/4` range

The cited lemma requires BOTH of its exponent slots in `(0, 1/4]`.  The
`t`-slot is the enclosing proposition's `s`, which ranges over
`[8 gamma, 1/2]`.  The interval `s in (1/4, 1/2]` is therefore NOT covered by
the citation.  Both theorems here carry the honest hypothesis `s <= 1/4` (and
the implied `gamma <= 1/8`); the uncovered range is an acknowledged gap, not
something narrowed silently.

## Two silent normalizations, not discharged here

The manuscript's display sits on the translated, rescaled cube `z + cube_n`
while the cited lemma is stated on the unit cube `cube_0`, and it replaces the
lemma's `||grad h||_{W^{1,infinity}(cube_0)}` by the scale-normalized
`3^{2n} ||grad(k_L - k_{n-2})||_{W-underline^{1,infinity}(z+cube_n)}`.  Neither
change of variables is performed in the source.  Here the coefficient `a`, the
skew perturbation `h` and hence the gauge `h.gradientW1Infinity` are the
caller's data on the unit cube, so both normalizations remain exactly where the
manuscript leaves them: at the instantiation site.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## Two carrier bridges -/

/-- The CoarseGraining ambient scalar matrix at a positive scalar is the Section 3
isotropic comparator.  Both are `sigma . (1 : Mat d)`. -/
private theorem scalarMatrix_eq_isotropicComparatorMatrix
    (sigma : Observable.PositiveScalar) :
    scalarMatrix (d := d) (sigma : ℝ) = Observable.isotropicComparatorMatrix sigma :=
  rfl

/-- The frozen `W^{1,infinity}` gauge of a skew perturbation is nonnegative: it is
a maximum of two `ENNReal.toReal` values. -/
theorem gradientW1Infinity_nonneg (h : UnitCubeSkewW2Infinity d) :
    0 ≤ h.gradientW1Infinity := by
  unfold UnitCubeSkewW2Infinity.gradientW1Infinity
  exact le_max_of_le_left ENNReal.toReal_nonneg

/-! ## Step 2 at the witness: the four anchor terms -/

/-- **`e.ugly.estimate.for.J.pre`, four-term form**.

The unconditional sensitivity estimate at `mu = sigmaBar_m
sigmaBar_{n-2}^{-1}`, `sigma_0 = sigmaBar_{n-2}`, with the lemma's `s`-slot at
`gamma` and its `t`-slot at the caller's `s`.  The load pair on the left is the
manuscript's, because `mu * sigma_0 = sigmaBar_m`.

The four summands are, in order, the anchor's `T_1`--`T_4`.  The manuscript
packages `T_3` and `T_4`; see `exists_responseJ_ugly_pre`. -/
theorem exists_responseJ_ugly_pre_terms (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m n : ℤ)
        (a : CoeffOn (cubeDomain (originCube d 0)))
        (h : UnitCubeSkewW2Infinity d) (s : ℝ) (e : Vec d),
        0 < s → s ≤ 1 / 4 → M.gamma ≤ 1 / 8 → vecNorm e = 1 →
        responseJ (cubeDomain (originCube d 0))
            (perturbCoeffOn (cubeDomain (originCube d 0)) a
              h.toLInfSkewMatrixFieldOn 1)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M m) e) ≤
          C * ((Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (n - 2) : ℝ)) *
              Real.rpow (1 + h.gradientW1Infinity *
                  (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹)
                (2 * s / (1 - 4 * M.gamma)) *
              unitCubeHomogenizationError s (.finite 2) (.finite 2) a
                (Observable.isotropicComparatorMatrix
                  (Annealed.sigmaBar M (n - 2))) ^ 2 +
            C * ((Annealed.sigmaBar M m : ℝ)⁻¹ *
                (Annealed.sigmaBar M (n - 2) : ℝ) ^ 2) *
              (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹ *
              Real.rpow (1 + h.gradientW1Infinity *
                  (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹)
                (4 * M.gamma / (1 - 4 * M.gamma)) *
              ((Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ ^ 2 * h.valueL2 ^ 2 +
                ((Annealed.sigmaBar M m : ℝ) *
                  (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ - 1) ^ 2) +
            C * (Annealed.sigmaBar M m : ℝ)⁻¹ ^ 2 * h.gradientW1Infinity ^ 2 +
            C * min 1 (h.gradientW1Infinity *
              (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹) ^ 2 := by
  obtain ⟨C, hC, hJ⟩ := responseJ_sensitivity_unconditional (d := d) dimension
  refine ⟨C, hC, ?_⟩
  intro M m n a h s e hs0 hs1 hgam1 he
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsm0 : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hsn0 : (0 : ℝ) < (Annealed.sigmaBar M (n - 2) : ℝ) :=
    (Annealed.sigmaBar M (n - 2)).2
  have hmu0 : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) *
      (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ := by positivity
  have hprod : ((Annealed.sigmaBar M m : ℝ) *
      (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹) * (Annealed.sigmaBar M (n - 2) : ℝ) =
      (Annealed.sigmaBar M m : ℝ) := by
    field_simp
  have key := hJ a h (2 * M.gamma) s
    ((Annealed.sigmaBar M m : ℝ) * (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹)
    (Annealed.sigmaBar M (n - 2) : ℝ) e (by linarith only [hg0])
    (by linarith only [hgam1]) hs0 hs1 hmu0 hsn0 he
  rw [hprod] at key
  have hden : (1 : ℝ) - 2 * (2 * M.gamma) = 1 - 4 * M.gamma := by ring
  have hnum : (2 : ℝ) * (2 * M.gamma) = 4 * M.gamma := by ring
  rw [hden, hnum] at key
  refine le_trans key (le_of_eq ?_)
  rw [scalarMatrix_eq_isotropicComparatorMatrix]
  field_simp

/-! ## The printed three-term display -/

/-- The anchor's last two terms are dominated by the manuscript's single packaged
term. -/
theorem two_terms_le_packaged {C P L G : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hG : 0 ≤ G) :
    C * P ^ 2 * G ^ 2 + C * min 1 (G * L) ^ 2 ≤ C * ((P + L) * G) ^ 2 := by
  have hmin0 : 0 ≤ min 1 (G * L) := le_min zero_le_one (mul_nonneg hG hL)
  have hmin : min 1 (G * L) ≤ G * L := min_le_right _ _
  have hsq : min 1 (G * L) ^ 2 ≤ (G * L) ^ 2 := pow_le_pow_left₀ hmin0 hmin 2
  have hcross : 0 ≤ C * (2 * (P * L * G ^ 2)) := by positivity
  calc
    C * P ^ 2 * G ^ 2 + C * min 1 (G * L) ^ 2
        ≤ C * P ^ 2 * G ^ 2 + C * (G * L) ^ 2 := by
          have hstep := mul_le_mul_of_nonneg_left hsq hC
          linarith only [hstep]
    _ ≤ C * ((P + L) * G) ^ 2 := by nlinarith only [hcross]

/-- **`e.ugly.estimate.for.J.pre`, as printed**.

The manuscript's three-term display: the two sensitivity terms with their
`(1 + ||grad h|| lambda^{-1})` growth factors, and the single packaged
gradient term `C ((sigmaBar_m^{-1} + lambda_{gamma,2}^{-1}) ||grad h||)^2`. -/
theorem exists_responseJ_ugly_pre (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m n : ℤ)
        (a : CoeffOn (cubeDomain (originCube d 0)))
        (h : UnitCubeSkewW2Infinity d) (s : ℝ) (e : Vec d),
        0 < s → s ≤ 1 / 4 → M.gamma ≤ 1 / 8 → vecNorm e = 1 →
        responseJ (cubeDomain (originCube d 0))
            (perturbCoeffOn (cubeDomain (originCube d 0)) a
              h.toLInfSkewMatrixFieldOn 1)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M m) e) ≤
          C * ((Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (n - 2) : ℝ)) *
              Real.rpow (1 + h.gradientW1Infinity *
                  (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹)
                (2 * s / (1 - 4 * M.gamma)) *
              unitCubeHomogenizationError s (.finite 2) (.finite 2) a
                (Observable.isotropicComparatorMatrix
                  (Annealed.sigmaBar M (n - 2))) ^ 2 +
            C * ((Annealed.sigmaBar M m : ℝ)⁻¹ *
                (Annealed.sigmaBar M (n - 2) : ℝ) ^ 2) *
              (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹ *
              Real.rpow (1 + h.gradientW1Infinity *
                  (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹)
                (4 * M.gamma / (1 - 4 * M.gamma)) *
              ((Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ ^ 2 * h.valueL2 ^ 2 +
                ((Annealed.sigmaBar M m : ℝ) *
                  (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ - 1) ^ 2) +
            C * (((Annealed.sigmaBar M m : ℝ)⁻¹ +
                  (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹) *
                h.gradientW1Infinity) ^ 2 := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hpre⟩ := exists_responseJ_ugly_pre_terms d dimension
  refine ⟨C, hC, ?_⟩
  intro M m n a h s e hs0 hs1 hgam1 he
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsm0 : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hPnn : (0 : ℝ) ≤ (Annealed.sigmaBar M m : ℝ)⁻¹ := (inv_pos.2 hsm0).le
  have hLnn : (0 : ℝ) ≤ (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹ :=
    Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.unitCubeLambda_inv_nonneg
      a (by linarith only [hg0])
      Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.isAdmissible_finite_two
  have hGnn : (0 : ℝ) ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  refine le_trans (hpre M m n a h s e hs0 hs1 hgam1 he) ?_
  have hpack := two_terms_le_packaged (C := C)
    (P := (Annealed.sigmaBar M m : ℝ)⁻¹)
    (L := (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹)
    (G := h.gradientW1Infinity) hC.le hPnn hLnn hGnn
  linarith only [hpack]

end

end Algsuperdiff.Section4.Provider.Annular
