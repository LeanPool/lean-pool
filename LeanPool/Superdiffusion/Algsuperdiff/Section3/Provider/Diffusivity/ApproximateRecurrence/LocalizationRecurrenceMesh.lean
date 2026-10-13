/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Definition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationCutoffMesh

/-!
# LocalizationRecurrenceMesh

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The localized variational test at the recurrence carriers

ABK26, `l.approximate.recurrence.formula` (statement), Step 1, the display
`e.lower.bound.basic.split`.

`LocalizationCutoffMesh.lean` proves the insertion inequality and its quadratic
expansion at the actual cutoff coefficient family, on the mesh
`mesoCubeGrid d K (cutoffMesoScale a gamma lowScale highScale)`, at *abstract*
`sigma`, `lowScale`, `highScale`, `gapMultiplier` and `gamma`.  This module
reads that statement at the recurrence's own data --

* `sigma := Annealed.sigmaBar M (m - h)`, the manuscript's `shom_{m-h}`;
* `lowScale := m - h` and `highScale := m`, the two endpoints of the fresh
  shell `bfh = k_m - k_{m-h}`;
* `gapMultiplier := recurrenceGapMultiplier = 32`, the proof-internal
  multiplier; the printed `16` of `e.recurrence.params` is
  nowhere used;
* `gamma := M.gamma`;
* the big cube `originCube d Kc` at the gate `10^10 gamma^{-1} <= Kc - m`

-- and converts the grid average into the `descendantsAverage` form at the
depth `j` fixed by `(originCube d Kc).scale - j = recurrenceMesoScale 32 gamma m h`.

That is exactly the carrier convention of
`exists_const_descendantsAverage_integral_principalEnergy_le_annealedLimit`,
whose conclusion bounds the `descendantsAverage` of the *first* summand
produced here.  The two statements are therefore composable at one and the same
corrector pair: the terminal produces a corrector family and this module's
principal statement consumes a corrector pair, so a caller may specialize the
family at a sample and feed it here.

## What is proved

* `localizationRecurrenceMesoScale_eq` -- the scale identity
  `cutoffMesoScale a gamma (m - h) m = recurrenceMesoScale a gamma m h`.
* `mesoCubeGrid_recurrenceMesoScale_eq_descendantsAtDepth` -- the mesh at the
  recurrence buffer is the depth-`j` descendant family of `cu_{Kc}`.
* `exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded` --
  the third line of `e.lower.bound.basic.split` at the recurrence carriers, in
  `descendantsAverage` form: the localized variational test, with its principal
  term and its two fluctuation terms displayed separately.  The two correctors
  of `e.def.w` are assumed, not produced.

## References

* ABK26, `l.approximate.recurrence.formula`; `e.recurrence.params`, `e.def.w`,
  `e.recurrence.P.def`, `e.Pz.def`, `e.Fz.def`, `e.lower.bound.basic.split`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## The recurrence geometry: buffer scale, mesh, descendant depth -/

/-- **The buffer scale of `e.recurrence.params` read at the recurrence's own scale
pair.**  With `lowScale = m - h` and `highScale = m`, `cutoffMesoScale` is
literally `recurrenceMesoScale ... m h`, i.e. `n = m - h - a ceil|log_3
gamma|`.  Unconditional. -/
theorem localizationRecurrenceMesoScale_eq (a : ℕ) (gamma : ℝ) (m : ℤ) (h : ℕ) :
    cutoffMesoScale a gamma (m - (h : ℤ)) m = recurrenceMesoScale a gamma m (h : ℤ) := by
  simp only [cutoffMesoScale]
  congr 1
  ring

/-- **The mesoscopic tiling is the descendant family of the manuscript's depth.**
The site set `3^n Z^d cap cu_{Kc}` at the buffer scale `n = recurrenceMesoScale
a gamma m h` is `descendantsAtDepth (originCube d Kc) j` exactly when `j` is
the depth named by `(originCube d Kc).scale - j = recurrenceMesoScale a gamma m
h`.

: on `hscale`, which only *names* `j`, and on `hn`, the containment of the
buffer scale below `Kc`. -/
theorem mesoCubeGrid_recurrenceMesoScale_eq_descendantsAtDepth {a : ℕ} {gamma : ℝ}
    {m Kc : ℤ} {h j : ℕ}
    (hn : recurrenceMesoScale a gamma m (h : ℤ) ≤ Kc)
    (hscale : ((originCube d Kc).scale : ℤ) - (j : ℤ) =
      recurrenceMesoScale a gamma m (h : ℤ)) :
    mesoCubeGrid d Kc (recurrenceMesoScale a gamma m (h : ℤ)) =
      descendantsAtDepth (originCube d Kc) j := by
  have hsc : ((originCube d Kc).scale : ℤ) = Kc := rfl
  rw [hsc] at hscale
  rw [mesoCubeGrid_eq_descendantsAtDepth hn]
  congr 1
  omega

/-! ## The localized variational test -/

/-- **The third line of `e.lower.bound.basic.split` at the recurrence carriers, in
`descendantsAverage` form: the localized variational test.**

```
P . bfA_m(cu_{Kc}) P
  <= avsum_{z in 3^n Zd cap cu_{Kc}}
       ( P_z . bfA_m(z+cu_n) P_z
         + 2 P_z . fint_{z+cu_n} bfA_m tilde S_z
         + fint_{z+cu_n} tilde S_z . bfA_m tilde S_z ) .
```

The first summand is the principal term of Step 3; the latter two are the
fluctuation contribution of Step 2.  **No estimate on either is asserted
here.**

The `descendantsAverage` carrier, the `sigmaBar` gauge, the shell pair
`(m - h, m)` and the depth identity are the same as those of
`exists_const_descendantsAverage_integral_principalEnergy_le_annealedLimit`,
so a caller holding both may add them cube by cube.

: identical to the previous statement. -/
theorem exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded
    (M : ABKModel d) (omega : CutoffSample d) (m Kc : ℤ) (h : ℕ)
    (hK : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (Kc : ℝ) - (m : ℝ))
    (e e' : Vec d) (j : ℕ)
    (hscale : ((originCube d Kc).scale : ℤ) - (j : ℤ) =
      recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ))
    (wD : H10Function (openCubeSet (originCube d Kc)))
    (wN : H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (_hwD : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d Kc)) wD
      (fun x => -Corrector.streamForcing
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ omega.val (m - (h : ℤ)) m e x))
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d Kc)) wN
      (fun x => -Corrector.streamForcing
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ omega.val (m - (h : ℤ)) m e' x)) :
    ∃ S T : TriadicCube d → DoubledField d,
      (∀ R ∈ descendantsAtDepth (originCube d Kc) j,
          IsDoubledMuMinimizer (cubeDomain R)
            ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R)
            (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) omega.val
              (m - (h : ℤ)) m e e' R wD wN) (S R)) ∧
        (∀ R ∈ descendantsAtDepth (originCube d Kc) j,
            IsDoubledMuMinimizerField (cubeDomain R)
              ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R)
              (localizationFz (Annealed.sigmaBar M (m - (h : ℤ))) omega.val
                (m - (h : ℤ)) m e' R wD wN) (T R)) ∧
          (∀ R ∈ descendantsAtDepth (originCube d Kc) j,
              IsDoubledResponseField (cubeDomain R)
                ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R) (T R)) ∧
            blockVecDot (recurrenceP (Annealed.sigmaBar M (m - (h : ℤ))) e e')
                (blockMatVecMul
                  (Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d Kc))
                    ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn
                      (originCube d Kc)))
                  (recurrenceP (Annealed.sigmaBar M (m - (h : ℤ))) e e')) ≤
              descendantsAverage (originCube d Kc) j
                (fun R =>
                  blockVecDot
                      (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) omega.val
                        (m - (h : ℤ)) m e e' R wD wN)
                      (blockMatVecMul (Book.Ch02.coarseBlockMatrix (cubeDomain R)
                        ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R))
                        (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) omega.val
                          (m - (h : ℤ)) m e e' R wD wN))
                    + 2 * volumeAverage (openCubeSet R) (fun x =>
                        blockVecDot
                          (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) omega.val
                            (m - (h : ℤ)) m e e' R wD wN)
                          (blockMatVecMul
                            (blockMatrixField
                              ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R)
                              x)
                            ((T R).eval x)))
                    + 2 * doubledMuValue (cubeDomain R)
                        ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R)
                        (T R)) := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hlow : m - (h : ℤ) ≤ m := by omega
  have hKc : (m : ℝ) + 10 ^ 10 * M.gamma⁻¹ ≤ (Kc : ℝ) := by linarith
  obtain ⟨S, T, hS, hT, hresp, hle⟩ :=
    exists_localizationCutoffMeshSplit_le_mesoGridAverage_expanded M
      (Annealed.sigmaBar M (m - (h : ℤ))) omega recurrenceGapMultiplier hgamma0 hlow
      hKc e e' wD hwN
  rw [localizationRecurrenceMesoScale_eq] at hS hT hresp hle
  have hnle : recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) ≤ Kc := by
    have h1 : cutoffMesoScale recurrenceGapMultiplier M.gamma (m - (h : ℤ)) m ≤ Kc :=
      cutoffMesoScale_le_bigScale recurrenceGapMultiplier hgamma0 hlow hKc
    rwa [localizationRecurrenceMesoScale_eq] at h1
  rw [mesoCubeGrid_recurrenceMesoScale_eq_descendantsAtDepth hnle hscale] at hS hT hresp hle
  exact ⟨S, T, hS, hT, hresp, hle⟩

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
