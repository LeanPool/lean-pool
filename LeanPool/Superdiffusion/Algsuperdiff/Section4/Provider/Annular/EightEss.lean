/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.FluxCorrectedRepresentative

/-!
# EightEss

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `e.mathcal.E.eight.ess.bound` opening: unfolding the `(∞,2)` error

ABK26, Section 4.1: the first display of the proof of
`p.mathcalE.annular.decomp` opens

```
E_{s,∞,2}(□_m; ã_{L,m}, σ_m)^2
  ≤ C c_{2s} Σ_{n≤m} 3^{-2s(m-n)} max_{z ∈ 3^n Z^d ∩ □_m} max_{|e|=1}
        J(z+□_n, σ_m^{-1/2} e, σ_m^{1/2} e; ã_{L,m})
    + (the same with the transposed field) .
```

This module produces the **exact left-hand identity** at the proved observable
layer and reduces the display to its two genuine inputs.

## What is proved

`fluxCorrectedError_sq_eq_scaleSum` is an *identity*, not an estimate:

```
fluxCorrectedError M L m s ω ^ 2
  = c_{2s} Σ_{l ≥ 0} 3^{-2 s l}
      · maxDescendantNormalizedBlockResponse (□_m at depth l) (ã_{L,m}) (σ_m Id) ,
```

with the manuscript's own normalizing factor `c_{2s} = 1 - 3^{-2s}` explicit
and the scale index `l = m - n`, so the geometric weight is literally
`3^{-2s(m-n)}`.  This is the proved
`Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum` transported along
`Support.fluxCorrectedError_characterization`.

## What is slotted, and why

Two conversions separate the identity above from the printed display, and N is
available in the repository today:

1. **`e.bfJ.general`** -- the inner quantity is `normalizedBlockResponseMax`, a
   maximum of the *doubled* response over the full-block unit sphere of `2d`
   dimensions.  The printed display replaces it by the half-sum of the scalar
   `J` at the pair `(σ_m^{-1/2}e, σ_m^{1/2}e)` for the field and for its
   transpose.  The proved
   `responseJ_scalarLoading_le_normalizedBlockResponseMax` runs in the O
   direction (`J ≤ block max`), so this conversion is a genuine missing input.
2. **The descendant-vs-lattice identification** -- the inner maximum runs over
   `descendantsAtScale □_m (m-l)`, the triadic descendants of `□_m`; the
   manuscript's maximum runs over the lattice points `3^n Z^d ∩ □_m`.  The two
   enumerate the same cubes, but no lemma identifies them
   (`Support.latticeCubeSet` carries no proved lemma at all).

`eightEss_of_blockResponse_le` therefore takes both, jointly, as the single
named hypothesis `hbfJ` -- exactly the graph's `e.bfJ.general` edge -- and
delivers the printed two-term display.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## The geometric weight in the manuscript's spelling -/

/-- The `q = 2` geometric weight of the `(∞,2)` error is the manuscript's `c_{2s}
3^{-2 s l}` (the factor written `𝔠_{2s}`). -/
theorem geometricWeight_two_eq (s : ℝ) (l : ℕ) :
    Ch02.geometricWeight s 2 l
      = (1 - (3 : ℝ) ^ (-(2 * s))) * (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) := by
  rw [Ch02.geometricWeight, Ch02.geometricDiscount]
  congr 2
  · congr 1
    ring
  · congr 1
    ring

/-! ## The exact scale-sum identity -/

/-- **The `(∞,2)` opening as an identity**.

The squared flux-corrected error is exactly the `c_{2s}`-normalized geometric
scale sum of the descendant maxima of the normalized block response.  The
summation index `l` is the manuscript's `m - n`. -/
theorem fluxCorrectedError_sq_eq_scaleSum (M : ABKModel d) (L m : ℤ)
    {s : ℝ} (hs : 0 < s) (omega : Cutoff.CutoffSample d) :
    Support.fluxCorrectedError M L m s omega ^ 2
      = ∑' l : ℕ, Ch02.geometricWeight s 2 l
          * maxDescendantNormalizedBlockResponseAtScale (originCube d m) (m - (l : ℤ))
              (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
              (isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
  rw [Support.fluxCorrectedError_characterization,
    homogenizationErrorOnCube_infinity_two_sq_eq_tsum (originCube d m) hs]
  rfl

/-- The same identity with the manuscript's `c_{2s}` pulled out of the sum. -/
theorem fluxCorrectedError_sq_eq_normalized (M : ABKModel d) (L m : ℤ)
    {s : ℝ} (hs : 0 < s) (omega : Cutoff.CutoffSample d) :
    Support.fluxCorrectedError M L m s omega ^ 2
      = (1 - (3 : ℝ) ^ (-(2 * s)))
        * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ))
            * maxDescendantNormalizedBlockResponseAtScale (originCube d m) (m - (l : ℤ))
                (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
                (isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
  rw [fluxCorrectedError_sq_eq_scaleSum M L m hs omega, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  rw [geometricWeight_two_eq]
  ring

/-! ## The two-term display -/

/-- **`e.mathcal.E.eight.ess.bound`, modulo `e.bfJ.general`**.

Given the conversion of the descendant block-response maximum into the
manuscript's two lattice `J`-maxima -- the field term `Jfld` and the transpose
term `Jtrn`, at the constant `C` -- the printed two-term display follows, with
`c_{2s}` explicit.

`hbfJ` is the graph's `e.bfJ.general` edge together with the descendant-vs-
lattice identification; both are recorded frontier inputs, not proved here. -/
theorem eightEss_of_blockResponse_le (M : ABKModel d) (L m : ℤ)
    {s C : ℝ} (hs : 0 < s) (omega : Cutoff.CutoffSample d)
    {Jfld Jtrn : ℕ → ℝ}
    (hbfJ : ∀ l : ℕ,
      maxDescendantNormalizedBlockResponseAtScale (originCube d m) (m - (l : ℤ))
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m))
        ≤ C * (Jfld l + Jtrn l))
    (hsumF : Summable (fun l : ℕ => (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jfld l))
    (hsumT : Summable (fun l : ℕ => (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jtrn l)) :
    Support.fluxCorrectedError M L m s omega ^ 2
      ≤ C * (1 - (3 : ℝ) ^ (-(2 * s)))
          * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jfld l
        + C * (1 - (3 : ℝ) ^ (-(2 * s)))
          * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jtrn l := by
  classical
  set B : ℕ → ℝ := fun l =>
    maxDescendantNormalizedBlockResponseAtScale (originCube d m) (m - (l : ℤ))
      (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M m)) with hBdef
  have hB0 : ∀ l : ℕ, 0 ≤ B l := by
    intro l
    have hscale : (originCube d m).scale = m := rfl
    rw [hBdef]
    exact maxDescendantNormalizedBlockResponseAtScale_nonneg (originCube d m)
      (by rw [hscale]; omega) _ _
  have hw0 : ∀ l : ℕ, (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) :=
    fun l => Real.rpow_nonneg (by norm_num) _
  have hmaj : ∀ l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * B l
      ≤ C * ((3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jfld l)
        + C * ((3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jtrn l) := by
    intro l
    have hstep := mul_le_mul_of_nonneg_left (hbfJ l) (hw0 l)
    refine hstep.trans (le_of_eq ?_)
    ring
  have hmajSum : Summable (fun l : ℕ =>
      C * ((3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jfld l)
        + C * ((3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jtrn l)) :=
    (hsumF.mul_left C).add (hsumT.mul_left C)
  have hB0' : ∀ l : ℕ, 0 ≤ (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * B l :=
    fun l => mul_nonneg (hw0 l) (hB0 l)
  have hBsum : Summable (fun l : ℕ => (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * B l) :=
    Summable.of_nonneg_of_le hB0' hmaj hmajSum
  have hsumLe : ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * B l
      ≤ C * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jfld l
        + C * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jtrn l := by
    calc ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * B l
        ≤ ∑' l : ℕ, (C * ((3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jfld l)
            + C * ((3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jtrn l)) :=
          Summable.tsum_le_tsum hmaj hBsum hmajSum
      _ = (∑' l : ℕ, C * ((3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jfld l))
            + ∑' l : ℕ, C * ((3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jtrn l) :=
          Summable.tsum_add (hsumF.mul_left C) (hsumT.mul_left C)
      _ = C * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jfld l
            + C * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jtrn l := by
          rw [tsum_mul_left, tsum_mul_left]
  have hdisc : (0 : ℝ) ≤ 1 - (3 : ℝ) ^ (-(2 * s)) := by
    have hlt : (3 : ℝ) ^ (-(2 * s)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
    linarith only [hlt]
  rw [fluxCorrectedError_sq_eq_normalized M L m hs omega]
  calc (1 - (3 : ℝ) ^ (-(2 * s)))
        * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * B l
      ≤ (1 - (3 : ℝ) ^ (-(2 * s)))
          * (C * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jfld l
            + C * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jtrn l) :=
        mul_le_mul_of_nonneg_left hsumLe hdisc
    _ = C * (1 - (3 : ℝ) ^ (-(2 * s)))
          * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jfld l
        + C * (1 - (3 : ℝ) ^ (-(2 * s)))
          * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jtrn l := by ring

end

end Algsuperdiff.Section4.Provider.Annular
