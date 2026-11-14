/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.JResponseApplication

/-!
# DisplayBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# The two printed recurrence displays, transported to the integration interface

ABK26's `l.approximate.recurrence.formula` (statement, proof) concludes with
the pair of displays `e.what.do.we.have`.  Written at the pair of scales `n`
and `m = n + h`, and with the manuscript's `(log 3) c_star sum_{k=n+1}^{n+h}
3^{2 gamma k}` spelled in the already-proved carrier `recurrenceIncrement`,
they read

```
sigmabar_m sigmabar_n^{-1}
    <= 1 + recurrenceIncrement c_star gamma n m * (sigmabar_n^{-1})^2
         + E_rec gamma ,
sigmabar_n sigmabar_m^{-1}
    <= 1 - recurrenceIncrement c_star gamma n m * (sigmabar_n^{-1})^2
         + F_rec (m - n)^2 (sigmabar_n^{-1})^4 3^{4 gamma m}
         + E_rec gamma ,
```

with `E_rec =^2 |log gamma|^2` and `F_rec = C` the manuscript's own constants.

The immediately following lemma `l.integrate.approx.recurrence` is already
available here as
`Provider.Diffusivity.RecurrenceIntegration.integrate_approx_recurrence_cstarPlus`.
It does not consume the displays in the printed ratio form: its `hupper`
(`e.assump.upper`) and `hlower` (`e.assump.lower.modified`) binders are the
displays after multiplication by `sigmabar_n` respectively `sigmabar_m`, and
its lower binder carries the additive error against `sigmabar_n`, whereas the
printed lower display carries it against `sigmabar_m`.

This module performs that transport.  The quotient bound is taken from the
induction hypothesis `S(m_0, E)` alone -- specifically from its first clause
`e.shom.h.bounds`, through the proved
`Provider.Multiscale.sigmaBar_le_four_mul_rpow_mul_sigmaBar` -- so the forward
display is *not* needed to produce it.

## What is realized, and at which carrier

Everything is stated at the genuine running diffusivity
`Algsuperdiff.Section3.Annealed.sigmaBar M`, at the genuine disorder constant
`Algsuperdiff.Section3.Disorder.cstar M`, at `M.gamma`, and against the exact
binder shapes of `integrate_approx_recurrence_cstarPlus`.  No abstract sequence
stands in for `sigmabar`, and the increment is the proved
`recurrenceIncrement`, i.e. the manuscript's
`(log 3) c_star sum_{k=n+1}^{m} 3^{2 gamma k}`.

## What is NOT claimed

`l.approximate.recurrence.formula` is **not** proved here, and nothing in this
file asserts it.  Its whole analytic content -- the fresh-shell Dirichlet and
Neumann correctors, their Calderon-Zygmund `L^8` bounds, the mesoscopic
oscillation estimate, the localized variational split, the good-event
coefficient switch and the two one-sided Jensen legs, -- is untouched.

Supplying them is exactly the missing work.  Two further deviations are
declared rather than hidden:

* **The `m_star_star` floor is dropped.**  ABK26 supplies the displays only for
  `m_star_star <= n`, while `integrate_approx_recurrence_cstarPlus` demands
  them at every pair `n <= m <= m_0`.  The binders here follow the consumer and
  impose no lower floor, so they are *stronger* than what delivers.
  **This deviation is now paid, and the note above is retained only for
  provenance.**  `ApproximateRecurrence.SubLandmarkDisplays` proves the two
  binders outright below the landmark, so a caller need supply them only for
  `m_star_star <= n`.  On it the plateau forces every tracked quantity to be
  `O(gamma^2)` against a binder slack of `E gamma`.  See
  `integrate_approx_recurrence_of_landmark_floored` there, whose proof is a
  single call to the unchanged engine.
* **The shell budget is narrower than the source's.**  ABK26 allows `h <= 6
  c_star gamma^{-1}`; the consumer's range is `(m : real) <= (n : real) + c_star
  gamma^{-1}`.  The narrower range is a *weaker* hypothesis here, so this
  direction costs nothing; it is recorded because the constant `36` below is
  computed on it.

## References

* ABK26, `l.approximate.recurrence.formula`, statement, `e.what.do.we.have`,
  proof.
* ABK26, `l.integrate.approx.recurrence`; `e.assump.upper` and
  `e.assump.lower.modified`.
* ABK26, `d.mathcalS.def` and `e.shom.h.bounds`.
* ABK26, `c_star <= 1` and (the running-diffusivity comparison at constant `4`).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

noncomputable section

variable {d : ℕ}

/-! ## The two printed displays, transported -/

/-- **Line 1 of `e.what.do.we.have`, multiplied by `sigmabar_n`.**

The conclusion is verbatim the `hupper` binder of
`integrate_approx_recurrence_cstarPlus`
(`e.assump.upper`) at `E := Erec`, `s := fun k => (sigmaBar M k : real)`,
`cstar := cstar M` and `gamma := M.gamma`. -/
theorem sigmaBar_le_of_forward_display (M : ABKModel d) {Erec : ℝ} {n m : ℤ}
    (hdisp :
      (Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤
        1 +
            recurrenceIncrement (Disorder.cstar M) M.gamma n m *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 +
          Erec * M.gamma) :
    (Annealed.sigmaBar M m : ℝ) ≤
      (1 + Erec * M.gamma) * (Annealed.sigmaBar M n : ℝ) +
        recurrenceIncrement (Disorder.cstar M) M.gamma n m *
          ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
  have hposn : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hne : (Annealed.sigmaBar M n : ℝ) ≠ 0 := ne_of_gt hposn
  have hmul := mul_le_mul_of_nonneg_right hdisp hposn.le
  have hleft :
      (Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
          (Annealed.sigmaBar M n : ℝ) = (Annealed.sigmaBar M m : ℝ) := by
    field_simp
  have hright :
      (1 +
              recurrenceIncrement (Disorder.cstar M) M.gamma n m *
                (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 +
            Erec * M.gamma) *
          (Annealed.sigmaBar M n : ℝ) =
        (1 + Erec * M.gamma) * (Annealed.sigmaBar M n : ℝ) +
          recurrenceIncrement (Disorder.cstar M) M.gamma n m *
            ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
    field_simp
    ring
  rw [hleft, hright] at hmul
  exact hmul

/-- **Line 2 of `e.what.do.we.have`, multiplied by `sigmabar_m` and renormalized
against `sigmabar_n`.**

The conclusion is verbatim the `hlower` binder of
`integrate_approx_recurrence_cstarPlus`
(`e.assump.lower.modified`) at `E := K * Erec` and `F := Frec`.

Nothing else changes; in particular the signed increment and the quadratic
`h^2` term are untouched. -/
theorem sigmaBar_ge_of_reverse_display (M : ABKModel d) {Erec Frec K : ℝ}
    {n m : ℤ} (hErec : 0 ≤ Erec)
    (hK : (Annealed.sigmaBar M m : ℝ) ≤ K * (Annealed.sigmaBar M n : ℝ))
    (hdisp :
      (Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤
        1 -
              recurrenceIncrement (Disorder.cstar M) M.gamma n m *
                (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 +
            Frec * ((m : ℝ) - (n : ℝ)) ^ 2 *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
              (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) +
          Erec * M.gamma) :
    (1 - K * Erec * M.gamma) * (Annealed.sigmaBar M n : ℝ) +
          recurrenceIncrement (Disorder.cstar M) M.gamma n m *
            (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 * (Annealed.sigmaBar M m : ℝ) -
        Frec * ((m : ℝ) - (n : ℝ)) ^ 2 *
          (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 * (Annealed.sigmaBar M m : ℝ) *
          (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) ≤
      (Annealed.sigmaBar M m : ℝ) := by
  have hgamma : (0 : ℝ) ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hposm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hne : (Annealed.sigmaBar M m : ℝ) ≠ 0 := ne_of_gt hposm
  have hmul := mul_le_mul_of_nonneg_right hdisp hposm.le
  have hleft :
      (Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ *
          (Annealed.sigmaBar M m : ℝ) = (Annealed.sigmaBar M n : ℝ) := by
    field_simp
  rw [hleft] at hmul
  have hexpand :
      (1 -
                recurrenceIncrement (Disorder.cstar M) M.gamma n m *
                  (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 +
              Frec * ((m : ℝ) - (n : ℝ)) ^ 2 *
                (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
                (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) +
            Erec * M.gamma) *
          (Annealed.sigmaBar M m : ℝ) =
        (Annealed.sigmaBar M m : ℝ) -
              recurrenceIncrement (Disorder.cstar M) M.gamma n m *
                (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 *
                (Annealed.sigmaBar M m : ℝ) +
            Frec * ((m : ℝ) - (n : ℝ)) ^ 2 *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
              (Annealed.sigmaBar M m : ℝ) *
              (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) +
          Erec * M.gamma * (Annealed.sigmaBar M m : ℝ) := by
    ring
  rw [hexpand] at hmul
  have habs :
      Erec * M.gamma * (Annealed.sigmaBar M m : ℝ) ≤
        K * Erec * M.gamma * (Annealed.sigmaBar M n : ℝ) := by
    calc
      Erec * M.gamma * (Annealed.sigmaBar M m : ℝ)
          ≤ Erec * M.gamma * (K * (Annealed.sigmaBar M n : ℝ)) :=
            mul_le_mul_of_nonneg_left hK (mul_nonneg hErec hgamma)
      _ = K * Erec * M.gamma * (Annealed.sigmaBar M n : ℝ) := by ring
  linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
