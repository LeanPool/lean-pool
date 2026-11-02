/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Ugly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.UglyPre

/-!
# UglyChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `e.ugly.estimate.for.J.pre` to `e.ugly.estimate.for.J` composition

ABK26, Section 4.1.  This module closes the chain: `UglyPre` produces the
four sensitivity terms from the Section 2.4 anchor, and `Ugly` collapses
them against the good-event budgets.  The composition below runs both, so
the only remaining inputs are the manuscript's own displayed facts.

Here it is discharged.

## The two silent normalizations, made explicit

* `hgrad` --- the caller supplies `Gn` with
  `h.gradientW1Infinity = 3^{2n} Gn`.  This is exactly the manuscript's
  unremarked replacement of the unit-cube gauge `||grad h||_{W^{1,infinity}(cube_0)}`
  by the scale-normalized `3^{2n} ||grad(k_L - k_{n-2})||_{W-underline^{1,infinity}(z+cube_n)}`.
* The cube itself.  Every carrier here is the unit cube of the anchor; the
  manuscript's translation and rescaling to `z + cube_n` is not performed.

## The `s <= 1/4` residual

`hs14` is the honest range: the cited sensitivity lemma requires its exponent
slots in `(0, 1/4]`, and the manuscript instantiates the `t`-slot at the
enclosing proposition's `s in [8 gamma, 1/2]`.  The interval `(1/4, 1/2]` is
not covered.  `Ugly.uglyJEstimate_of_sensitivity` itself is stated on the full
`[8 gamma, 1/2]` window, so a future producer of the four-term bound valid
there composes with no change.

## The gapped gauge

The right-hand side `Cl * 3^{gamma(m-n)}` is unchanged.  See `UglyPre`.

## The `sigmaBar_{n-2}` lower constant

The `sigmaBar_{n-2}` lower bound is
carried at `1/4`, not at the printed `1/2`:
the Section 3 induction state supports only the relaxed constant at the
exponent `3^{gamma n}`.  See `Ugly.lean` for the arithmetic and for the
resulting constant bookkeeping in the `hC` slot.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-- **The composed per-cube estimate**: the unconditional sensitivity anchor, at
the `(mu, sigma_0)`-witness, collapsed by the two good-event budgets, the two
`sigmaBar` lower bounds, the `sigmaBar` ratio and the Poincare split into the
printed five-term display. -/
theorem exists_responseJ_ugly_estimate (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (M : ABKModel d) (m n : ℤ)
        (a : CoeffOn (cubeDomain (originCube d 0)))
        (h : UnitCubeSkewW2Infinity d) (e : Vec d)
        (s kap Cl Cr Cp Ash C Gn Gm Lnrm : ℝ),
        0 < s → s ≤ 1 / 4 → 8 * M.gamma ≤ s → vecNorm e = 1 →
        ((n : ℝ) ≤ (m : ℝ)) → 0 ≤ Ash → 0 ≤ Gn →
        0 < kap → M.gamma * kap ^ 2 = Disorder.cstar M →
        1 / 2 * (kap * (3 : ℝ) ^ (M.gamma * (m : ℝ))) ≤ (Annealed.sigmaBar M m : ℝ) →
        1 / 4 * (kap * (3 : ℝ) ^ (M.gamma * (n : ℝ))) ≤
          (Annealed.sigmaBar M (n - 2) : ℝ) →
        (Annealed.sigmaBar M (n - 2) : ℝ) *
            (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹ ≤
          Cl * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) →
        (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
            ((3 : ℝ) ^ (2 * (n : ℝ)) * Gn) ≤
          Ash * (3 : ℝ) ^ (s / 4 * ((m : ℝ) - (n : ℝ))) →
        (Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (n - 2) : ℝ) ≤ Cr →
        h.gradientW1Infinity = (3 : ℝ) ^ (2 * (n : ℝ)) * Gn →
        h.valueL2 ^ 2 ≤
          2 * Lnrm ^ 2 + 2 * (Cp * ((3 : ℝ) ^ (2 * (m : ℝ)) * Gm)) ^ 2 →
        Cs * (1 + Ash * Cl) ^ 2 * Cr * (1 + Cl)
            + 16 * Cs * (1 + Ash * Cl) ^ 2 * Cl * (1 + Cp ^ 2)
            + 4 * Cs * (1 + 4 * Cl ^ 2) ≤ C →
        IsUglyJEstimate
          (responseJ (cubeDomain (originCube d 0))
            (perturbCoeffOn (cubeDomain (originCube d 0)) a
              h.toLInfSkewMatrixFieldOn 1)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M m) e))
          (unitCubeHomogenizationError s (.finite 2) (.finite 2) a
            (Observable.isotropicComparatorMatrix
              (Annealed.sigmaBar M (n - 2))) ^ 2)
          (((Annealed.sigmaBar M m : ℝ) *
            (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ - 1) ^ 2)
          (((3 : ℝ) ^ (-(M.gamma * (n : ℝ))) * Lnrm) ^ 2)
          (((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) * Gn) ^ 2)
          (((3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ)) * Gm) ^ 2)
          (Disorder.cstar M) M.gamma
          ((3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ))))
          ((3 : ℝ) ^ ((s + M.gamma) * ((m : ℝ) - (n : ℝ)))) C := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, hCs, hpre⟩ := exists_responseJ_ugly_pre_terms d dimension
  refine ⟨Cs, hCs, ?_⟩
  intro M m n a h e s kap Cl Cr Cp Ash C Gn Gm Lnrm hs0 hs14 hsgam he hnm hAsh
    hGn hkap0 hkap hsigmlow hsignlow hlam hshell hratio hgrad hH hC
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hgam18 : M.gamma ≤ 1 / 8 := by linarith only [hsgam, hs14]
  have hlamInv : (0 : ℝ) ≤ (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹ :=
    Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.unitCubeLambda_inv_nonneg
      a (by linarith only [hg0])
      Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.isAdmissible_finite_two
  have key := hpre M m n a h s e hs0 hs14 hgam18 he
  rw [hgrad] at key
  exact uglyJEstimate_of_sensitivity (kap := kap) (Cs := Cs) (Cl := Cl) (Cr := Cr)
    (Cp := Cp) (Ash := Ash) (C := C) (mm := (m : ℝ)) (nn := (n : ℝ))
    (q := (m : ℝ) - (n : ℝ)) (Gn := Gn) (Gm := Gm) (Lnrm := Lnrm)
    (lamInv := (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹)
    (sigm := (Annealed.sigmaBar M m : ℝ))
    (sign := (Annealed.sigmaBar M (n - 2) : ℝ))
    (Hsq := h.valueL2 ^ 2)
    hs0 (by linarith only [hs14]) hsgam hnm rfl hCs.le hAsh (sq_nonneg _) hGn
    (sq_nonneg _) hlamInv (Disorder.cstar_characterization M).1 hkap0 hkap
    (Annealed.sigmaBar M m).2 (Annealed.sigmaBar M (n - 2)).2 hsigmlow hsignlow
    hlam hshell hratio hH key hC

end

end Algsuperdiff.Section4.Provider.Annular
