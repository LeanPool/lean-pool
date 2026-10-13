/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseDisplayTwoGrid
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseDisplayTwoMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseMomentsFourth

/-!
# PrincipalResponseDisplayTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Provider: display 2 of leg (iv) of the principal response

Source display in ABK26, inside Step 3 of the proof of
`l.approximate.recurrence.formula` (label):

```
  ( avsum_{z in 3^n Zd cap cu_K} E[ | bfAhom_{m-1}^{1/2} P_z |^4 ] )^{1/4}  <=  C .
```

## What is assembled here

The chain has six links, five of which are supplied by the modules imported
above and by the two proved engines:

1. the **collapse** of the normalization (`annealedSqrtNormSq_principalPz_eq`,
   from `ellipticityBudget_eq`) and the **gauge transport** to `shom_{m-1}`
   (`sq_annealedSqrtNormSq_le_gaugeRatio_sq_mul`), which together reduce the
   integrand to the raw averaged slope pair times the squared gauge ratio;
2. the **vector Jensen inequality at the fourth power** and the
   **`L^4 <= L^8` bridge** on each localization cube (portable module
   `CubeJensenVec`);
3. the **grid re-assembly** to a single global `L^8` norm on `cu_K`
   (`descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le`);
4. **`e.nablaw.in.L.eight`** for the two corrector gradients, and `e.km.kn.Lp`
   at `p = 8` for the extra forcing `shom^{-1} h e'` carried by the Neumann
   slot of `e.Pz.def`, merged into a single `Gamma_1` lane by
   `isBigOWith_gammaSigma_one_add`;
5. the **transport** of that lane from the canonical shell law to the
   cutoff-sample law (`isBigOWith_cutoffSampleLaw_of_isBigOWith`); and
6. the **expectation** (`integral_le_of_le_shift_add_kappa_sq`, which runs the
   proved `integral_rpow_two_le_of_shift_add_one_orlicz`) and the fourth root.

## The gauge factor is displayed, not absorbed

The manuscript writes the display at the gauge `shom_{m-1}`, while `P_z` is
built at `shom_{m-h}`.  The bound below therefore carries the explicit factor
`(gaugeRatio shom_{m-h} shom_{m-1})^{1/2}`.  It is *not* absorbed into `C`: the
three scale gates that this theorem binds do not control `shom_{m-1}` (they
constrain scales at most `m0 >= m - h` only), so the manuscript's remark that
`e.shom.h.bounds` makes the ratio dimensional is an input this theorem does not
have and does not silently assume.  This is the same convention as the proved
`PrincipalResponseMomentsFourth`, which names the ratio and does not bound it.

## The two analytic binders

`hmeasX` is the measurability of the display's own integrand: the manuscript
writes `E[...]`, which presupposes that the bracket is a random variable.  It is
a well-definedness condition, not a step of the estimate; no bound and no
conclusion of any predecessor is assumed.  The two solution binders `hwD`,
`hwN` are the manuscript's own definitions `e.def.w` of the two correctors, one
per sample.

## References

* ABK26, display, inside `l.approximate.recurrence.formula`; `e.Pz.def`;
  `e.def.w` (label; the proved `FreshShellL8` cites, which is a citation
  drift, not a statement drift); `e.recurrence.params`;
  `e.nablaw.in.L.eight`; `e.km.kn.Lp`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The pathwise grid bound -/

private abbrev principalResponseDisplayTwo_momentBounds1_statement : Prop :=
    ∀ (d : ℕ) (_ : (2 : ℕ) ≤ d) (Chead g0a Clp : ℝ) (_ : (0 : ℝ) < Clp) (g0b : ℝ)
      (_ :
        ∀ (gamma : ℝ),
          (0 : ℝ) < gamma →
            gamma ≤ g0b → (2 : ℝ) * Clp * ((24 : ℝ) * (3 : ℝ) ^ (18 : ℝ)) ≤ (3 : ℝ) ^ ((10 : ℝ) ^ (9 : ℕ) * gamma⁻¹))
      (M : ABKModel d) (_ : M.gamma ≤ min g0a g0b) (m K : ℤ) (h : ℕ)
      (_ : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑K : ℝ) - (↑m : ℝ)) (e e' : Vec d) (_ : Ch02.vecNorm e' ≤ (1 : ℝ)) (j : ℕ)
      (sigmaTop : PositiveScalar) (wD : Cutoff.CutoffSample d → H10Function (openCubeSet (originCube d K)))
      (wN : Cutoff.CutoffSample d → H1MeanZeroFunction (openCubeSet (originCube d K)))
      (_ :
        ∀ (z : Cutoff.CutoffSample d),
          IsZeroTraceDirichletRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
            (openCubeSet (originCube d K)) (wD z) fun (x : Vec d) =>
            -streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ (↑z : Cutoff.ShellSeq d) (m - (↑h : ℤ)) m e x)
      (_ :
        ∀ (z : Cutoff.CutoffSample d),
          IsMeanZeroNeumannRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
            (openCubeSet (originCube d K)) (wN z) fun (x : Vec d) =>
            -streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ (↑z : Cutoff.ShellSeq d) (m - (↑h : ℤ)) m e' x)
      (_ : (0 : ℝ) < M.gamma) (_ : M.gamma ≤ (1 / 4 : ℝ))
      (_ : (0 : ℝ) < (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ))
      (_ : (0 : ℝ) ≤ (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹) (Tf : Cutoff.ShellSeq d → ℝ)
      (_ :
        IndependentSums.IsBigOWith (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d))
          (IndependentSums.gammaSigma (1 : ℝ)) Tf (M.gamma ^ (100 : ℕ)))
      (_ :
        ∀ (omega : Cutoff.ShellSeq d) (wD : H10Function (openCubeSet (originCube d K))),
          (IsZeroTraceDirichletRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
              (openCubeSet (originCube d K)) wD fun (x : Vec d) =>
              -streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ omega (m - (↑h : ℤ)) m e x) →
            ∀ (wN : H1MeanZeroFunction (openCubeSet (originCube d K))),
              (IsMeanZeroNeumannRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                  (openCubeSet (originCube d K)) wN fun (x : Vec d) =>
                  -streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ omega (m - (↑h : ℤ)) m e' x) →
                cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) wD.grad ^ (2 : ℕ) +
                    cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) wN.toH1Function.grad ^ (2 : ℕ) ≤
                  Chead + Tf omega)
      (T : Cutoff.ShellSeq d → ℝ),
      let A0 : ℝ := min M.gamma⁻¹ ((↑m : ℝ) - (↑(m - (↑h : ℤ)) : ℝ)) * (3 : ℝ) ^ ((2 : ℝ) * M.gamma * (↑m : ℝ));
      ∀
        (_ :
          ∀ (omega : Cutoff.ShellSeq d),
            Stream.streamIncrementLpNorm (8 : ℝ) K (m - (↑h : ℤ)) m omega ^ (2 : ℕ) ≤ Clp * A0 + T omega)
        (_ :
          IndependentSums.IsBigOWith (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d))
            (IndependentSums.gammaSigma (1 : ℝ)) T (Clp * A0 * (3 : ℝ) ^ (-((↑d : ℝ) / (8 : ℝ)) * ((↑K : ℝ) - (↑m : ℝ)))))
        (_ : (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ ^ (2 : ℕ) * A0 ≤ (24 : ℝ) * (3 : ℝ) ^ (18 : ℝ)),
        let Xz : Cutoff.CutoffSample d → ℝ := fun (z : Cutoff.CutoffSample d) =>
          descendantsAverage (originCube d K) j fun (R : TriadicCube d) =>
            annealedSqrtNormSq sigmaTop
                (principalPz (Annealed.sigmaBar M (m - (↑h : ℤ))) (↑z : Cutoff.ShellSeq d) (m - (↑h : ℤ)) m e e' R (wD z)
                  (wN z)) ^
              (2 : ℕ);
        ∀
          (_ :
            Xz = fun (z : Cutoff.CutoffSample d) =>
              descendantsAverage (originCube d K) j fun (R : TriadicCube d) =>
                annealedSqrtNormSq sigmaTop
                    (principalPz (Annealed.sigmaBar M (m - (↑h : ℤ))) (↑z : Cutoff.ShellSeq d) (m - (↑h : ℤ)) m e e' R
                      (wD z) (wN z)) ^
                  (2 : ℕ)),
          let Wz : Cutoff.CutoffSample d → ℝ := fun (z : Cutoff.CutoffSample d) =>
            cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) (wD z).grad ^ (2 : ℕ) +
                (2 : ℝ) * cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) (wN z).toH1Function.grad ^ (2 : ℕ) +
              (2 : ℝ) *
                cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞)
                    (streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ (↑z : Cutoff.ShellSeq d) (m - (↑h : ℤ)) m
                      e') ^
                  (2 : ℕ);
          ∀
            (_ :
              Wz = fun (z : Cutoff.CutoffSample d) =>
                cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) (wD z).grad ^ (2 : ℕ) +
                    (2 : ℝ) * cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) (wN z).toH1Function.grad ^ (2 : ℕ) +
                  (2 : ℝ) *
                    cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞)
                        (streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ (↑z : Cutoff.ShellSeq d) (m - (↑h : ℤ))
                          m e') ^
                      (2 : ℕ)),
            let Ysh : Cutoff.ShellSeq d → ℝ := fun (omega : Cutoff.ShellSeq d) =>
              (2 : ℝ) * Tf omega + (2 : ℝ) * (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ ^ (2 : ℕ) * T omega;
            ∀
              (_ :
                Ysh = fun (omega : Cutoff.ShellSeq d) =>
                  (2 : ℝ) * Tf omega + (2 : ℝ) * (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ ^ (2 : ℕ) * T omega),
              (∀ (z : Cutoff.CutoffSample d), (0 : ℝ) ≤ Xz z) ∧
                (∀ (z : Cutoff.CutoffSample d), (0 : ℝ) ≤ Wz z) ∧
                  (∀ (z : Cutoff.CutoffSample d),
                      Wz z ≤
                        (2 : ℝ) * Chead + (2 : ℝ) * Clp * ((24 : ℝ) * (3 : ℝ) ^ (18 : ℝ)) + Ysh (↑z : Cutoff.ShellSeq d)) ∧
                    IndependentSums.IsBigOWith (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d))
                        (IndependentSums.gammaSigma (1 : ℝ))
                        (fun (omega : ℤ → Frozen.Assumptions.ShellField d) =>
                          (2 : ℝ) * Tf omega + (2 : ℝ) * (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ ^ (2 : ℕ) * T omega)
                        ((2 : ℝ) * ((2 : ℝ) * M.gamma ^ (100 : ℕ) + M.gamma ^ (100 : ℕ))) ∧
                      (2 : ℝ) * ((2 : ℝ) * M.gamma ^ (100 : ℕ) + M.gamma ^ (100 : ℕ)) = (6 : ℝ) * M.gamma ^ (100 : ℕ)

private abbrev principalResponseDisplayTwo_momentBounds2_statement : Prop :=
    ∀ (d : ℕ) (Chead : ℝ) (_ : (0 : ℝ) < Chead) (Clp : ℝ) (_ : (0 : ℝ) < Clp)
      (_ : (0 : ℝ) < orliczSecondMomentScale (1 : ℝ)) (M : ABKModel d) (m K : ℤ) (h : ℕ) (e e' : Vec d)
      (_ : Ch02.vecNorm e ≤ (1 : ℝ)) (_ : Ch02.vecNorm e' ≤ (1 : ℝ)) (j : ℕ) (sigmaTop : PositiveScalar)
      (wD : Cutoff.CutoffSample d → H10Function (openCubeSet (originCube d K)))
      (wN : Cutoff.CutoffSample d → H1MeanZeroFunction (openCubeSet (originCube d K))) (_ : (0 : ℝ) < M.gamma)
      (_ : M.gamma ≤ (1 / 4 : ℝ)) (Tf T : Cutoff.ShellSeq d → ℝ),
      let Xz : Cutoff.CutoffSample d → ℝ := fun (z : Cutoff.CutoffSample d) =>
        descendantsAverage (originCube d K) j fun (R : TriadicCube d) =>
          annealedSqrtNormSq sigmaTop
              (principalPz (Annealed.sigmaBar M (m - (↑h : ℤ))) (↑z : Cutoff.ShellSeq d) (m - (↑h : ℤ)) m e e' R (wD z)
                (wN z)) ^
            (2 : ℕ);
      ∀ (_ : Measurable Xz),
        let Wz : Cutoff.CutoffSample d → ℝ := fun (z : Cutoff.CutoffSample d) =>
          cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) (wD z).grad ^ (2 : ℕ) +
              (2 : ℝ) * cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) (wN z).toH1Function.grad ^ (2 : ℕ) +
            (2 : ℝ) *
              cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞)
                  (streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ (↑z : Cutoff.ShellSeq d) (m - (↑h : ℤ)) m
                    e') ^
                (2 : ℕ);
        let Ysh : Cutoff.ShellSeq d → ℝ := fun (omega : Cutoff.ShellSeq d) =>
          (2 : ℝ) * Tf omega + (2 : ℝ) * (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ ^ (2 : ℕ) * T omega;
        ∀
          (_ :
            Ysh = fun (omega : Cutoff.ShellSeq d) =>
              (2 : ℝ) * Tf omega + (2 : ℝ) * (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ ^ (2 : ℕ) * T omega)
          (_ : (0 : ℝ) < gaugeRatio (Annealed.sigmaBar M (m - (↑h : ℤ))) sigmaTop)
          (_ :
            ∀ (z : Cutoff.CutoffSample d),
              Xz z ≤
                (16 : ℝ) * gaugeRatio (Annealed.sigmaBar M (m - (↑h : ℤ))) sigmaTop ^ (2 : ℕ) *
                    (vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ)) +
                  (16 : ℝ) * gaugeRatio (Annealed.sigmaBar M (m - (↑h : ℤ))) sigmaTop ^ (2 : ℕ) * Wz z ^ (2 : ℕ))
          (_ :
            ∀ (z : Cutoff.CutoffSample d),
              (0 : ℝ) ≤
                (fun (z : Cutoff.CutoffSample d) =>
                    descendantsAverage (originCube d K) j fun (R : TriadicCube d) =>
                      annealedSqrtNormSq sigmaTop
                          (principalPz (Annealed.sigmaBar M (m - (↑h : ℤ))) (↑z : Cutoff.ShellSeq d) (m - (↑h : ℤ)) m e e' R
                            (wD z) (wN z)) ^
                        (2 : ℕ))
                  z)
          (_ :
            ∀ (z : Cutoff.CutoffSample d),
              (0 : ℝ) ≤
                (fun (z : Cutoff.CutoffSample d) =>
                    cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) (wD z).grad ^ (2 : ℕ) +
                        (2 : ℝ) * cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) (wN z).toH1Function.grad ^ (2 : ℕ) +
                      (2 : ℝ) *
                        cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞)
                            (streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ (↑z : Cutoff.ShellSeq d)
                              (m - (↑h : ℤ)) m e') ^
                          (2 : ℕ))
                  z)
          (_ :
            ∀ (z : Cutoff.CutoffSample d),
              (fun (z : Cutoff.CutoffSample d) =>
                    cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) (wD z).grad ^ (2 : ℕ) +
                        (2 : ℝ) * cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) (wN z).toH1Function.grad ^ (2 : ℕ) +
                      (2 : ℝ) *
                        cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞)
                            (streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ (↑z : Cutoff.ShellSeq d)
                              (m - (↑h : ℤ)) m e') ^
                          (2 : ℕ))
                  z ≤
                (2 : ℝ) * Chead + (2 : ℝ) * Clp * ((24 : ℝ) * (3 : ℝ) ^ (18 : ℝ)) +
                  (fun (omega : Cutoff.ShellSeq d) =>
                      (2 : ℝ) * Tf omega + (2 : ℝ) * (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ ^ (2 : ℕ) * T omega)
                    (↑z : Cutoff.ShellSeq d))
          (_ :
            IndependentSums.IsBigOWith (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d))
              (IndependentSums.gammaSigma (1 : ℝ))
              (fun (omega : ℤ → Frozen.Assumptions.ShellField d) =>
                (2 : ℝ) * Tf omega + (2 : ℝ) * (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ ^ (2 : ℕ) * T omega)
              ((6 : ℝ) * M.gamma ^ (100 : ℕ))),
          ∫ (z : Cutoff.CutoffSample d), Xz z ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
              gaugeRatio (Annealed.sigmaBar M (m - (↑h : ℤ))) sigmaTop ^ (2 : ℕ) *
                ((32 : ℝ) +
                  (16 : ℝ) *
                    ((2 : ℝ) *
                        ((2 : ℝ) * Chead + (2 : ℝ) * Clp * ((24 : ℝ) * (3 : ℝ) ^ (18 : ℝ)) +
                          (6 : ℝ) * orliczSecondMomentScale (1 : ℝ))) ^
                      (2 : ℕ)) ∧
            (0 : ℝ) ≤ ∫ (z : Cutoff.CutoffSample d), Xz z ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ∧
              (gaugeRatio (Annealed.sigmaBar M (m - (↑h : ℤ))) sigmaTop ^ (2 : ℕ) *
                    ((32 : ℝ) +
                      (16 : ℝ) *
                        ((2 : ℝ) *
                            ((2 : ℝ) * Chead + (2 : ℝ) * Clp * ((24 : ℝ) * (3 : ℝ) ^ (18 : ℝ)) +
                              (6 : ℝ) * orliczSecondMomentScale (1 : ℝ))) ^
                          (2 : ℕ))) ^
                  (1 / 4 : ℝ) =
                gaugeRatio (Annealed.sigmaBar M (m - (↑h : ℤ))) sigmaTop ^ (1 / 2 : ℝ) *
                  ((32 : ℝ) +
                      (16 : ℝ) *
                        ((2 : ℝ) *
                            ((2 : ℝ) * Chead + (2 : ℝ) * Clp * ((24 : ℝ) * (3 : ℝ) ^ (18 : ℝ)) +
                              (6 : ℝ) * orliczSecondMomentScale (1 : ℝ))) ^
                          (2 : ℕ)) ^
                    (1 / 4 : ℝ)

private theorem principalResponseDisplayTwo_estimate1 :
    ∀ {d : ℕ} (sigmaLow : PositiveScalar) (omega : Cutoff.ShellSeq d)
      (lowScale highScale : ℤ) (e' : Vec d) (Q : TriadicCube d) (wD : H10Function (openCubeSet Q))
      (wN : H1MeanZeroFunction (openCubeSet Q)),
      let F : Vec d → Vec d := streamForcing (↑sigmaLow : ℝ)⁻¹ omega lowScale highScale e';
      ∀ (hnnN : (0 : ℝ) ≤ cubeEuclideanLpNorm Q (8 : ℝ≥0∞) wN.toH1Function.grad)
        (hnnF : (0 : ℝ) ≤ cubeEuclideanLpNorm Q (8 : ℝ≥0∞) F)
        (hnnGN : (0 : ℝ) ≤ cubeEuclideanLpNorm Q (8 : ℝ≥0∞) (neumannFluxField sigmaLow omega lowScale highScale e' wN))
        (hnnD : (0 : ℝ) ≤ cubeEuclideanLpNorm Q (8 : ℝ≥0∞) wD.grad)
        (hGNsq :
          cubeEuclideanLpNorm Q (8 : ℝ≥0∞) (neumannFluxField sigmaLow omega lowScale highScale e' wN) ^ (2 : ℕ) ≤
            (2 : ℝ) * cubeEuclideanLpNorm Q (8 : ℝ≥0∞) wN.toH1Function.grad ^ (2 : ℕ) +
              (2 : ℝ) * cubeEuclideanLpNorm Q (8 : ℝ≥0∞) F ^ (2 : ℕ)),
        let S : ℝ :=
          cubeEuclideanLpNorm Q (8 : ℝ≥0∞) wD.grad ^ (2 : ℕ) +
              (2 : ℝ) * cubeEuclideanLpNorm Q (8 : ℝ≥0∞) wN.toH1Function.grad ^ (2 : ℕ) +
            (2 : ℝ) * cubeEuclideanLpNorm Q (8 : ℝ≥0∞) F ^ (2 : ℕ);
        ∀
          (hSdef :
            S =
              cubeEuclideanLpNorm Q (8 : ℝ≥0∞) wD.grad ^ (2 : ℕ) +
                  (2 : ℝ) * cubeEuclideanLpNorm Q (8 : ℝ≥0∞) wN.toH1Function.grad ^ (2 : ℕ) +
                (2 : ℝ) * cubeEuclideanLpNorm Q (8 : ℝ≥0∞) F ^ (2 : ℕ)),
          cubeEuclideanLpNorm Q (8 : ℝ≥0∞) wD.grad ^ (4 : ℕ) +
              cubeEuclideanLpNorm Q (8 : ℝ≥0∞) (neumannFluxField sigmaLow omega lowScale highScale e' wN) ^ (4 : ℕ) ≤
            S ^ (2 : ℕ) := by
  intro d sigmaLow omega lowScale highScale e' Q wD wN F hnnN hnnF hnnGN hnnD hGNsq S hSdef
  have h1 : cubeEuclideanLpNorm Q 8 wD.toH1Function.grad ^ (4 : ℕ) =
      (cubeEuclideanLpNorm Q 8 wD.toH1Function.grad ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
  have h2 : cubeEuclideanLpNorm Q 8
        (neumannFluxField sigmaLow omega lowScale highScale e' wN) ^ (4 : ℕ) =
      (cubeEuclideanLpNorm Q 8
        (neumannFluxField sigmaLow omega lowScale highScale e' wN) ^ (2 : ℕ)) ^
        (2 : ℕ) := by ring
  rw [h1, h2, hSdef]
  have hbsq : (cubeEuclideanLpNorm Q 8
        (neumannFluxField sigmaLow omega lowScale highScale e' wN) ^ (2 : ℕ)) ^
          (2 : ℕ) ≤
      (2 * cubeEuclideanLpNorm Q 8 wN.toH1Function.grad ^ (2 : ℕ) +
        2 * cubeEuclideanLpNorm Q 8 F ^ (2 : ℕ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (pow_nonneg hnnGN 2) hGNsq 2
  have hcross : (0 : ℝ) ≤ 2 * (cubeEuclideanLpNorm Q 8 wD.toH1Function.grad ^ (2 : ℕ) *
      (2 * cubeEuclideanLpNorm Q 8 wN.toH1Function.grad ^ (2 : ℕ) +
        2 * cubeEuclideanLpNorm Q 8 F ^ (2 : ℕ))) :=
    mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg hnnD 2)
      (add_nonneg (mul_nonneg (by norm_num) (pow_nonneg hnnN 2))
        (mul_nonneg (by norm_num) (pow_nonneg hnnF 2))))
  linarith only [hbsq, hcross]

/-- **The pathwise grid form of display 2.**  Combining the collapse of the
normalization, the gauge transport, the vector Jensen inequality at the fourth
power, the grid re-assembly and the `L^4 <= L^8` bridge:

```
  avsum_R | bfAhom_{sigmaTop}^{1/2} P_R |^4
    <=  16 rho^2 ( |e'|^4 + |e|^4 )
        + 16 rho^2 ( ‖grad w_D‖^2 + 2‖grad w_N‖^2 + 2‖shom^{-1} h e'‖^2 )^2 ,
```

with `rho = gaugeRatio sigmaLow sigmaTop` and every norm the volume-normalized
Euclidean `L^8` norm on `Q`. -/
theorem pathwise_descendantsAverage_sq_annealedSqrtNormSq_le
    (sigmaLow sigmaTop : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e e' : Vec d) (Q : TriadicCube d) (j : ℕ)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q))
    (hD : MemLp wD.toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hN : MemLp wN.toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q j
        (fun R => annealedSqrtNormSq sigmaTop
          (principalPz sigmaLow omega lowScale highScale e e' R wD wN) ^ (2 : ℕ)) ≤
      16 * gaugeRatio sigmaLow sigmaTop ^ (2 : ℕ) *
          (vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ)) +
        16 * gaugeRatio sigmaLow sigmaTop ^ (2 : ℕ) *
          (cubeEuclideanLpNorm Q 8 wD.toH1Function.grad ^ (2 : ℕ) +
            2 * cubeEuclideanLpNorm Q 8 wN.toH1Function.grad ^ (2 : ℕ) +
            2 * cubeEuclideanLpNorm Q 8
                (streamForcing ((sigmaLow : ℝ))⁻¹ omega lowScale highScale e')
                ^ (2 : ℕ)) ^ (2 : ℕ) := by
  classical
  set F : Vec d → Vec d :=
    streamForcing ((sigmaLow : ℝ))⁻¹ omega lowScale highScale e' with hFdef
  have hFcont : Continuous F := continuous_streamForcing _ _ _ _ _
  have hFmem : MemLp F (8 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_continuous Q _ hFcont
  have hGN : neumannFluxField sigmaLow omega lowScale highScale e' wN =
      fun x => wN.toH1Function.grad x + F x := rfl
  have hGNmem : MemLp (neumannFluxField sigmaLow omega lowScale highScale e' wN)
      (8 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    rw [hGN]
    exact hN.add hFmem
  -- the two grid bounds
  have hD1 := descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le Q j e'
    (fun x => wD.toH1Function.grad x) hD
  have hD2 := descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le Q j e
    (neumannFluxField sigmaLow omega lowScale highScale e' wN) hGNmem
  -- the gauge transport and the collapse
  have hgauge := descendantsAverage_sq_annealedSqrtNormSq_principalPz_le
    sigmaLow sigmaTop omega lowScale highScale e e' Q j wD wN
  -- the Minkowski step on the Neumann slot
  have hmink : cubeEuclideanLpNorm Q 8
        (neumannFluxField sigmaLow omega lowScale highScale e' wN) ≤
      cubeEuclideanLpNorm Q 8 wN.toH1Function.grad + cubeEuclideanLpNorm Q 8 F := by
    rw [hGN]
    exact cubeEuclideanLpNorm_add_le Q (by norm_num) _ _
      (memLp_vecNorm_of_memLp Q hN) (memLp_vecNorm_of_memLp Q hFmem)
  have hnnN : (0 : ℝ) ≤ cubeEuclideanLpNorm Q 8 wN.toH1Function.grad :=
    cubeEuclideanLpNorm_nonneg _ _ _
  have hnnF : (0 : ℝ) ≤ cubeEuclideanLpNorm Q 8 F := cubeEuclideanLpNorm_nonneg _ _ _
  have hnnGN : (0 : ℝ) ≤ cubeEuclideanLpNorm Q 8
      (neumannFluxField sigmaLow omega lowScale highScale e' wN) :=
    cubeEuclideanLpNorm_nonneg _ _ _
  have hnnD : (0 : ℝ) ≤ cubeEuclideanLpNorm Q 8 wD.toH1Function.grad :=
    cubeEuclideanLpNorm_nonneg _ _ _
  have hGNsq : cubeEuclideanLpNorm Q 8
        (neumannFluxField sigmaLow omega lowScale highScale e' wN) ^ (2 : ℕ) ≤
      2 * cubeEuclideanLpNorm Q 8 wN.toH1Function.grad ^ (2 : ℕ) +
        2 * cubeEuclideanLpNorm Q 8 F ^ (2 : ℕ) := by
    calc cubeEuclideanLpNorm Q 8
          (neumannFluxField sigmaLow omega lowScale highScale e' wN) ^ (2 : ℕ)
        ≤ (cubeEuclideanLpNorm Q 8 wN.toH1Function.grad +
            cubeEuclideanLpNorm Q 8 F) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hnnGN hmink 2
      _ ≤ 2 * cubeEuclideanLpNorm Q 8 wN.toH1Function.grad ^ (2 : ℕ) +
            2 * cubeEuclideanLpNorm Q 8 F ^ (2 : ℕ) := by
          linarith only [sq_nonneg (cubeEuclideanLpNorm Q 8 wN.toH1Function.grad -
            cubeEuclideanLpNorm Q 8 F)]
  -- the fourth powers
  set S : ℝ := cubeEuclideanLpNorm Q 8 wD.toH1Function.grad ^ (2 : ℕ) +
    2 * cubeEuclideanLpNorm Q 8 wN.toH1Function.grad ^ (2 : ℕ) +
    2 * cubeEuclideanLpNorm Q 8 F ^ (2 : ℕ) with hSdef
  have hSnn : (0 : ℝ) ≤ S := by
    rw [hSdef]
    exact add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg zero_le_two (sq_nonneg _)))
      (mul_nonneg zero_le_two (sq_nonneg _))
  have hsum : cubeEuclideanLpNorm Q 8 wD.toH1Function.grad ^ (4 : ℕ) +
      cubeEuclideanLpNorm Q 8
        (neumannFluxField sigmaLow omega lowScale highScale e' wN) ^ (4 : ℕ) ≤
      S ^ (2 : ℕ)  := @principalResponseDisplayTwo_estimate1 (d) (sigmaLow) (omega) (lowScale) (highScale) (e') (Q) (wD) (wN) (hnnN) (hnnF) (hnnGN) (hnnD) (hGNsq) (hSdef)
  have hrho : (0 : ℝ) < gaugeRatio sigmaLow sigmaTop := gaugeRatio_pos _ _
  have hrhosq : (0 : ℝ) ≤ 2 * gaugeRatio sigmaLow sigmaTop ^ (2 : ℕ) := by positivity
  have hstep : 2 * gaugeRatio sigmaLow sigmaTop ^ (2 : ℕ) *
      (descendantsAverage Q j
          (fun R => vecNormSq (e' + cubeAverageVec R
            (fun x => wD.toH1Function.grad x)) ^ (2 : ℕ)) +
        descendantsAverage Q j
          (fun R => vecNormSq (e + cubeAverageVec R
            (neumannFluxField sigmaLow omega lowScale highScale e' wN)) ^
            (2 : ℕ))) ≤
      16 * gaugeRatio sigmaLow sigmaTop ^ (2 : ℕ) *
          (vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ)) +
        16 * gaugeRatio sigmaLow sigmaTop ^ (2 : ℕ) * S ^ (2 : ℕ) := by
    have hinner :
        descendantsAverage Q j
            (fun R => vecNormSq (e' + cubeAverageVec R
              (fun x => wD.toH1Function.grad x)) ^ (2 : ℕ)) +
          descendantsAverage Q j
            (fun R => vecNormSq (e + cubeAverageVec R
              (neumannFluxField sigmaLow omega lowScale highScale e' wN)) ^
              (2 : ℕ)) ≤
        8 * (vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ)) + 8 * S ^ (2 : ℕ) := by
      linarith only [hD1, hD2, hsum]
    have hscaled := mul_le_mul_of_nonneg_left hinner hrhosq
    linarith only [hscaled]
  exact hgauge.trans hstep


/-! ## Display 2 of leg (iv) -/

private theorem principalResponseDisplayTwo_momentBounds1 : principalResponseDisplayTwo_momentBounds1_statement := by
  intro d hd Chead _ Clp hClppos _ hg0b M hMgamma m K h hK _ e' he' j _ wD wN hwD hwN hgamma hquarter _ hsigInvnn Tf hTftail hTfbound T A0 hTle hTtail hnormalized Xz hXzdef Wz hWzdef Ysh hYshdef
  have hX0 : ∀ z, 0 ≤ Xz z := by
    intro z
    simp only [hXzdef]
    exact descendantsAverage_nonneg _ j _ fun R _ => sq_nonneg _
  have hWnn : ∀ z, 0 ≤ Wz z := by
    intro z
    simp only [hWzdef]
    exact add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg zero_le_two (sq_nonneg _)))
      (mul_nonneg zero_le_two (sq_nonneg _))
  have hWY : ∀ z, Wz z ≤
      (2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) + Ysh z.val := by
    intro z
    have hfresh := hTfbound z.val (wD z) (hwD z) (wN z) (hwN z)
    have hFnorm := cubeEuclideanLpNorm_streamForcing_le (d := d) hsigInvnn K
      (m - (h : ℤ)) m z.val he'
    have hFnn : (0 : ℝ) ≤ cubeEuclideanLpNorm (originCube d K) 8
        (streamForcing ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val
          (m - (h : ℤ)) m e') := cubeEuclideanLpNorm_nonneg _ _ _
    have hFsq : cubeEuclideanLpNorm (originCube d K) 8
          (streamForcing ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val
            (m - (h : ℤ)) m e') ^ (2 : ℕ) ≤
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
          Stream.streamIncrementLpNorm 8 K (m - (h : ℤ)) m z.val ^ (2 : ℕ) := by
      calc cubeEuclideanLpNorm (originCube d K) 8
            (streamForcing ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val
              (m - (h : ℤ)) m e') ^ (2 : ℕ)
          ≤ (((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
              Stream.streamIncrementLpNorm 8 K (m - (h : ℤ)) m z.val) ^ (2 : ℕ) :=
            pow_le_pow_left₀ hFnn hFnorm 2
        _ = ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
              Stream.streamIncrementLpNorm 8 K (m - (h : ℤ)) m z.val ^ (2 : ℕ) := by
            rw [mul_pow]
    have hmass := hTle z.val
    have hdistrib : ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
        (Clp * A0 + T z.val) =
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) * (Clp * A0) +
          ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) * T z.val := by
      ring
    have hstep1 : ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
        Stream.streamIncrementLpNorm 8 K (m - (h : ℤ)) m z.val ^ (2 : ℕ) ≤
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
          (Clp * A0 + T z.val) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    have hstep2 : ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
        (Clp * A0) ≤ Clp * (24 * (3 : ℝ) ^ (18 : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hnormalized hClppos.le
      calc ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) * (Clp * A0)
          = Clp * (((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) * A0) := by
            ring
        _ ≤ Clp * (24 * (3 : ℝ) ^ (18 : ℝ)) := hmul
    have hnnD : (0 : ℝ) ≤ cubeEuclideanLpNorm (originCube d K) 8
        (wD z).toH1Function.grad ^ (2 : ℕ) := sq_nonneg _
    simp only [hWzdef, hYshdef]
    linarith only [hfresh, hFsq, hstep1, hstep2, hdistrib.le, hdistrib.ge, hnnD]
  -- merging and transporting the two lanes
  have hlane1 : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 1) (fun omega => 2 * Tf omega)
      (2 * M.gamma ^ (100 : ℕ)) := hTftail.const_mul (by norm_num)
  have hlane2raw : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 1)
      (fun omega => 2 * ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
        T omega)
      (2 * ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
        (Clp * A0 * (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))))) :=
    hTtail.const_mul (by positivity)
  have hamp : 2 * ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
      (Clp * A0 * (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ)))) ≤
      M.gamma ^ (100 : ℕ) := by
    have hCsmall : 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ)) ≤
        (3 : ℝ) ^ ((10 : ℝ) ^ (9 : ℕ) * M.gamma⁻¹) :=
      hg0b M.gamma hgamma (le_trans hMgamma (min_le_right _ _))
    have hgap := const_mul_rpow_gap_le_gammaPow
      (C := 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) (gamma := M.gamma)
      (G := (K : ℝ) - (m : ℝ)) (by positivity) hgamma hquarter hd hK hCsmall
    have hdecay : (0 : ℝ) ≤ (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have hmul : 2 * Clp *
        (((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) * A0) ≤
        2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ)) :=
      mul_le_mul_of_nonneg_left hnormalized (by positivity)
    calc 2 * ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
          (Clp * A0 * (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))))
        = (2 * Clp * (((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) * A0)) *
            (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))) := by ring
      _ ≤ (2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) *
            (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))) :=
          mul_le_mul_of_nonneg_right hmul hdecay
      _ ≤ M.gamma ^ (100 : ℕ) := hgap
  have hlane2 : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 1)
      (fun omega => 2 * ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
        T omega) (M.gamma ^ (100 : ℕ)) := hlane2raw.mono_scale hamp
  have hmerge := isBigOWith_gammaSigma_one_add hlane1 hlane2
  have hsix : 2 * (2 * M.gamma ^ (100 : ℕ) + M.gamma ^ (100 : ℕ)) =
      6 * M.gamma ^ (100 : ℕ) := by ring
  exact ⟨hX0, hWnn, hWY, hmerge, hsix⟩

private theorem principalResponseDisplayTwo_momentBounds2 : principalResponseDisplayTwo_momentBounds2_statement := by
  intro d Chead hCheadpos Clp _ _ M m _ h e e' he he' j sigmaTop _ _ hgamma hquarter _ _ Xz hmeasX Wz Ysh hYshdef hrho hXle hX0 hWnn hWY hmerge
  have hmergeY : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 1) Ysh (6 * M.gamma ^ (100 : ℕ)) := by
    rw [hYshdef]
    exact hmerge
  have htransport := isBigOWith_cutoffSampleLaw_of_isBigOWith M hmergeY
  -- the expectation
  have hApos : (0 : ℝ) < 6 * M.gamma ^ (100 : ℕ) := by positivity
  have hbnn : (0 : ℝ) ≤ 2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ)) := by
    have h1 : (0 : ℝ) ≤ 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ)) := by positivity
    linarith only [h1, hCheadpos]
  have hkappapos : (0 : ℝ) <
      16 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) := by
    positivity
  have hmain := integral_le_of_le_shift_add_kappa_sq
    (mu := (Cutoff.cutoffSampleLaw M).toMeasure) (X := Xz) (W := Wz)
    (Y := fun z : Cutoff.CutoffSample d => Ysh z.val)
    (B := 16 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) *
      (vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ)))
    (kappa := 16 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ))
    (b := 2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ)))
    (A := 6 * M.gamma ^ (100 : ℕ)) (sigma := 1)
    (by norm_num) hApos hbnn hkappapos hmeasX hX0 hWnn hXle hWY htransport
  -- the numerical envelope
  have hgammaone : M.gamma ^ (100 : ℕ) ≤ 1 :=
    pow_le_one₀ hgamma.le (by linarith only [hquarter])
  have hEsq : vecNormSq e ^ (2 : ℕ) ≤ 1 := by
    have hE : vecNormSq e ≤ 1 := by
      rw [← Book.Ch02.vecNorm_sq_eq_vecNormSq e]
      exact pow_le_one₀ (Book.Ch02.vecNorm_nonneg e) he
    exact pow_le_one₀ (vecNormSq_nonneg e) hE
  have hEsq' : vecNormSq e' ^ (2 : ℕ) ≤ 1 := by
    have hE : vecNormSq e' ≤ 1 := by
      rw [← Book.Ch02.vecNorm_sq_eq_vecNormSq e']
      exact pow_le_one₀ (Book.Ch02.vecNorm_nonneg e') he'
    exact pow_le_one₀ (vecNormSq_nonneg e') hE
  have hBle : 16 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) *
      (vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ)) ≤
      32 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) := by
    have hsum : vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ) ≤ 2 := by
      linarith only [hEsq, hEsq']
    calc 16 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) *
          (vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ))
        ≤ 16 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) * 2 :=
          mul_le_mul_of_nonneg_left hsum hkappapos.le
      _ = 32 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) := by
          ring
  have hmomle : (2 * ((2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) +
        orliczSecondMomentScale 1 * (6 * M.gamma ^ (100 : ℕ)))) ^ (2 : ℕ) ≤
      (2 * ((2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) +
        6 * orliczSecondMomentScale 1)) ^ (2 : ℕ) := by
    have hstep : orliczSecondMomentScale 1 * (6 * M.gamma ^ (100 : ℕ)) ≤
        6 * orliczSecondMomentScale 1 := by
      have h6 : (0 : ℝ) ≤ 6 * orliczSecondMomentScale 1 := by positivity
      calc orliczSecondMomentScale 1 * (6 * M.gamma ^ (100 : ℕ))
          = (6 * orliczSecondMomentScale 1) * M.gamma ^ (100 : ℕ) := by ring
        _ ≤ (6 * orliczSecondMomentScale 1) * 1 :=
            mul_le_mul_of_nonneg_left hgammaone h6
        _ = 6 * orliczSecondMomentScale 1 := by ring
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hstep]) 2
  have hscale := mul_le_mul_of_nonneg_left hmomle hkappapos.le
  have hcollect : 32 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) +
      16 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) *
        (2 * ((2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) +
          6 * orliczSecondMomentScale 1)) ^ (2 : ℕ) =
      gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) *
        (32 + 16 * (2 * ((2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) +
          6 * orliczSecondMomentScale 1)) ^ (2 : ℕ)) := by ring
  have hfinal : ∫ z : Cutoff.CutoffSample d, Xz z
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) *
        (32 + 16 * (2 * ((2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) +
          6 * orliczSecondMomentScale 1)) ^ (2 : ℕ)) := by
    rw [← hcollect]
    linarith only [hmain, hBle, hscale]
  -- the fourth root
  have hIntnn : (0 : ℝ) ≤ ∫ z : Cutoff.CutoffSample d, Xz z
      ∂(Cutoff.cutoffSampleLaw M).toMeasure := integral_nonneg fun z => hX0 z
  have hbasepos : (0 : ℝ) < 32 + 16 * (2 * ((2 * Chead +
      2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) +
        6 * orliczSecondMomentScale 1)) ^ (2 : ℕ) := by positivity
  have hroot : (gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) *
        (32 + 16 * (2 * ((2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) +
          6 * orliczSecondMomentScale 1)) ^ (2 : ℕ))) ^ ((1 : ℝ) / 4) =
      gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ ((1 : ℝ) / 2) *
        (32 + 16 * (2 * ((2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) +
          6 * orliczSecondMomentScale 1)) ^ (2 : ℕ)) ^ ((1 : ℝ) / 4) := by
    rw [Real.mul_rpow (by positivity) hbasepos.le]
    congr 1
    rw [← Real.rpow_natCast
      (gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop) 2,
      ← Real.rpow_mul hrho.le]
    norm_num
  exact ⟨hfinal, hIntnn, hroot⟩

/-- **Display 2 of leg (iv) of `l.approximate.recurrence.formula`.**

```
  E[ avsum_R | bfAhom_{sigmaTop}^{1/2} P_R |^4 ]^{1/4}
      <=  ( gaugeRatio shom_{m-h} sigmaTop )^{1/2} * C ,
```

with `R` running over the triadic descendants of `cu_K` at depth `j` and `P_R`
the localized load of `e.Pz.def`.  At the manuscript's reading gauge
`sigmaTop = shom_{m-1}` the displayed factor is the ratio the manuscript absorbs
into `C` by `e.shom.h.bounds`; it is left visible here because the gates bound
above do not constrain the scale `m - 1`.

The expectation stands outermost, which is the pathwise-then-integrate reading;
the manuscript's own order `avsum_[...]` follows from it by the finite
linearity of the grid average whenever the individual expectations exist. -/
theorem exists_const_fourthMoment_annealedSqrtNormSq_principalPz_le
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
        ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
          ∀ (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
            Algsuperdiff.Frozen.Section3.inductionState M m0 E →
            ∀ (m K : ℤ) (h : ℕ), 0 < h → m - (h : ℤ) ≤ m0 →
              (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
              (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
              ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
                Book.Ch02.vecNorm e' ≤ 1 →
                ∀ (j : ℕ) (sigmaTop : PositiveScalar)
                  (wD : Cutoff.CutoffSample d →
                    H10Function (openCubeSet (originCube d K)))
                  (wN : Cutoff.CutoffSample d →
                    H1MeanZeroFunction (openCubeSet (originCube d K))),
                  (∀ z : Cutoff.CutoffSample d,
                    IsZeroTraceDirichletRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wD z)
                      (fun x => -streamForcing
                        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val
                        (m - (h : ℤ)) m e x)) →
                  (∀ z : Cutoff.CutoffSample d,
                    IsMeanZeroNeumannRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wN z)
                      (fun x => -streamForcing
                        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val
                        (m - (h : ℤ)) m e' x)) →
                  Measurable (fun z : Cutoff.CutoffSample d =>
                    descendantsAverage (originCube d K) j
                      (fun R => annealedSqrtNormSq sigmaTop
                        (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) z.val
                          (m - (h : ℤ)) m e e' R (wD z) (wN z)) ^ (2 : ℕ))) →
                  (∫ z : Cutoff.CutoffSample d,
                      descendantsAverage (originCube d K) j
                        (fun R => annealedSqrtNormSq sigmaTop
                          (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) z.val
                            (m - (h : ℤ)) m e e' R (wD z) (wN z)) ^ (2 : ℕ))
                      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ^ ((1 : ℝ) / 4) ≤
                    gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^
                        ((1 : ℝ) / 2) * C := by
  classical
  obtain ⟨Chead, hCheadpos, g0a, hg0apos, hg0aquarter, hFresh⟩ :=
    exists_cubeEuclideanL8_gradient_sq_sum_le_const_add_gammaPow d hd
  obtain ⟨Clp, hClppos, hLP⟩ := exists_streamIncrementLpNormSq_head_tail d
  obtain ⟨C0, hC0pos, hCZ⟩ :=
    Algsuperdiff.Frozen.External.calderon_zygmund (d := d) hd (8 : ℝ≥0∞)
      (by norm_num) (by norm_num)
  have hgapconst : (0 : ℝ) < 24 * (3 : ℝ) ^ (18 : ℝ) := by
    have hthree : (0 : ℝ) < (3 : ℝ) ^ (18 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    linarith only [hthree]
  obtain ⟨g0b, hg0bpos, hg0bquarter, hg0b⟩ :=
    exists_gamma_threshold_for_gap_constant (2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ)))
  have hc2pos : (0 : ℝ) < orliczSecondMomentScale 1 :=
    orliczSecondMomentScale_pos (by norm_num)
  refine ⟨(32 + 16 * (2 * ((2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) +
      6 * orliczSecondMomentScale 1)) ^ (2 : ℕ)) ^ ((1 : ℝ) / 4),
    Real.rpow_pos_of_pos (by positivity) _, min g0a g0b,
    lt_min hg0apos hg0bpos, (min_le_left _ _).trans hg0aquarter, ?_⟩
  intro M hMgamma m0 E hS m K h hhpos hm hh hK e e' he he' j sigmaTop wD wN
    hwD hwN hmeasX
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hquarter : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hsigpos : (0 : ℝ) < (Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) :=
    (Annealed.sigmaBar M (m - (h : ℤ))).2
  have hsigInvnn : (0 : ℝ) ≤ ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ :=
    (inv_pos.2 hsigpos).le
  have hmK : m ≤ K := by
    have hpos : (0 : ℝ) < (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ :=
      mul_pos (by norm_num) (inv_pos.2 hgamma)
    have hle : (m : ℝ) ≤ (K : ℝ) := by linarith only [hpos, hK]
    exact_mod_cast hle
  have hnm : m - (h : ℤ) < m := by omega
  -- `L^8` membership of the two corrector gradients, from the Calderon-Zygmund anchor
  have hgradD : ∀ z : Cutoff.CutoffSample d,
      MemLp (wD z).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d K)) := by
    intro z
    have hmem : MemLp (streamForcing
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val (m - (h : ℤ)) m e)
        (8 : ℝ≥0∞) (normalizedCubeMeasure (originCube d K)) :=
      memLp_normalizedCubeMeasure_of_continuous _ _
        (continuous_streamForcing _ _ _ _ _)
    exact ((hCZ (originCube d K) (streamForcing
      ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val (m - (h : ℤ)) m e)
      hmem).1 (wD z) (hwD z)).1
  have hgradN : ∀ z : Cutoff.CutoffSample d,
      MemLp (wN z).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d K)) := by
    intro z
    have hmem : MemLp (streamForcing
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val (m - (h : ℤ)) m e')
        (8 : ℝ≥0∞) (normalizedCubeMeasure (originCube d K)) :=
      memLp_normalizedCubeMeasure_of_continuous _ _
        (continuous_streamForcing _ _ _ _ _)
    exact ((hCZ (originCube d K) (streamForcing
      ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val (m - (h : ℤ)) m e')
      hmem).2 (wN z) (hwN z)).1
  -- the two lanes of `e.nablaw.in.L.eight` and of `e.km.kn.Lp`
  obtain ⟨Tf, hTfnn, hTftail, hTfbound⟩ :=
    hFresh M (le_trans hMgamma (min_le_left _ _)) m0 E hS m K h hhpos hm hh hK
      e e' he he'
  obtain ⟨T, hTnn, hTle, hTtail⟩ := hLP M K (m - (h : ℤ)) m hnm hmK
  have hcast : (m : ℝ) - ((m - (h : ℤ) : ℤ) : ℝ) = (h : ℝ) := by push_cast; ring
  set A0 : ℝ := min M.gamma⁻¹ ((m : ℝ) - ((m - (h : ℤ) : ℤ) : ℝ)) *
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) with hA0def
  have hA0nn : (0 : ℝ) ≤ A0 := by
    rw [hA0def]
    have hmin : (0 : ℝ) ≤ min M.gamma⁻¹ ((m : ℝ) - ((m - (h : ℤ) : ℤ) : ℝ)) := by
      refine le_min (inv_pos.2 hgamma).le ?_
      rw [hcast]
      positivity
    have hthree : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    exact mul_nonneg hmin hthree.le
  -- the deterministic head of the forcing lane
  have hhead := inv_sigmaBarSq_mul_shellWidth_le M hS hm hh
  have hnormalized :
      ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) * A0 ≤
        24 * (3 : ℝ) ^ (18 : ℝ) := by
    have hle : A0 ≤ (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
      rw [hA0def]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos (by norm_num) _).le
      rw [hcast]
      exact min_le_right _ _
    calc ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) * A0
        ≤ ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) *
            ((h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ (2 : ℕ))⁻¹ * (h : ℝ) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
          rw [inv_pow]; ring
      _ ≤ 24 * (3 : ℝ) ^ (18 : ℝ) := hhead
  -- the observable, the energy and the merged lane
  set Xz : Cutoff.CutoffSample d → ℝ := fun z =>
    descendantsAverage (originCube d K) j
      (fun R => annealedSqrtNormSq sigmaTop
        (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) z.val (m - (h : ℤ)) m
          e e' R (wD z) (wN z)) ^ (2 : ℕ)) with hXzdef
  set Wz : Cutoff.CutoffSample d → ℝ := fun z =>
    cubeEuclideanLpNorm (originCube d K) 8 (wD z).toH1Function.grad ^ (2 : ℕ) +
      2 * cubeEuclideanLpNorm (originCube d K) 8
        (wN z).toH1Function.grad ^ (2 : ℕ) +
      2 * cubeEuclideanLpNorm (originCube d K) 8
        (streamForcing ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val
          (m - (h : ℤ)) m e') ^ (2 : ℕ) with hWzdef
  set Ysh : Cutoff.ShellSeq d → ℝ := fun omega =>
    2 * Tf omega +
      2 * ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ ^ (2 : ℕ) * T omega
    with hYshdef
  have hrho : (0 : ℝ) <
      gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop := gaugeRatio_pos _ _
  have hXle : ∀ z, Xz z ≤
      16 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) *
          (vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ)) +
        16 * gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) *
          Wz z ^ (2 : ℕ) := by
    intro z
    simp only [hXzdef, hWzdef]
    exact pathwise_descendantsAverage_sq_annealedSqrtNormSq_le
      (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop z.val (m - (h : ℤ)) m e e'
      (originCube d K) j (wD z) (wN z) (hgradD z) (hgradN z)
  obtain ⟨hX0, hWnn, hWY, hmerge, hsix⟩ :=
    @principalResponseDisplayTwo_momentBounds1 (d) (hd) (Chead) (g0a) (Clp) (hClppos) (g0b) (hg0b)
      (M) (hMgamma) (m) (K) (h) (hK) (e) (e') (he') (j) (sigmaTop) (wD) (wN) (hwD) (hwN) (hgamma)
        (hquarter) (hsigpos) (hsigInvnn) (Tf) (hTftail) (hTfbound) (T) (hTle) (hTtail)
          (hnormalized) (hXzdef) (hWzdef) (hYshdef)
  rw [hsix] at hmerge
  obtain ⟨hfinal, hIntnn, hroot⟩ :=
    @principalResponseDisplayTwo_momentBounds2 (d) (Chead) (hCheadpos) (Clp) (hClppos) (hc2pos)
      (M) (m) (K) (h) (e) (e') (he) (he') (j) (sigmaTop) (wD) (wN) (hgamma) (hquarter) (Tf) (T)
        (hmeasX) (hYshdef) (hrho) (hXle) (hX0) (hWnn) (hWY) (hmerge)
  calc (∫ z : Cutoff.CutoffSample d, Xz z
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ^ ((1 : ℝ) / 4)
      ≤ (gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ (2 : ℕ) *
          (32 + 16 * (2 * ((2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) +
            6 * orliczSecondMomentScale 1)) ^ (2 : ℕ))) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hIntnn hfinal (by norm_num)
    _ = gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) sigmaTop ^ ((1 : ℝ) / 2) *
          (32 + 16 * (2 * ((2 * Chead + 2 * Clp * (24 * (3 : ℝ) ^ (18 : ℝ))) +
            6 * orliczSecondMomentScale 1)) ^ (2 : ℕ)) ^ ((1 : ℝ) / 4) := hroot

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
