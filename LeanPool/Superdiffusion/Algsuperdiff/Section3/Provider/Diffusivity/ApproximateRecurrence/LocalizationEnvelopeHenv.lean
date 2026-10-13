/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeSpatial
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellExistence

/-!
# LocalizationEnvelopeHenv

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
descriptions below are an informal inventory only.

# Provider: the annealed `L^4` envelope, derived from the `L^8` leg

Source displays in ABK26:

* `e.nablaw.in.L.eight` (label; display);
* `e.lower.bound.oscillations` (label; display), whose deduction is "by
  `e.nablaw.in.L.eight` and `e.W.1.inf.bound`".

## What `henv` is, exactly

The covering step of `LocalizationEnvelopeMesh` consumes

```
  henv :  int_Omega fint_{cu_K} |grad w|^4  <=  E .
```

This is **not** the manuscript's `L^8` leg.  It is the remaining *annealed*
`L^4` consequence that still has to be derived **from** that leg.  The leg
itself, `e.nablaw.in.L.eight`, is a *pathwise* statement about the *eighth*
normalized norm:

```
  ‖grad w_D‖^2_{L8bar(cu_K)} + ‖grad w_N‖^2_{L8bar(cu_K)}  <=  Chead + Tfluct(omega) ,
```

with `Tfluct` an `O_{Gamma_1}(cgamma^100)` random variable.  Three steps
separate the two; this module performs the first and names the constant the
third produces:

1. **The leg split.**  Both summands are nonnegative, so each of the two
   correctors separately obeys `‖grad w‖^2_{L8bar(cu_K)} <= Chead + Tfluct`.
   Discarding one summand needs the *other* problem to be solvable, which is
   exactly what `Corrector.FreshShellExistence` supplies; no measurable
   selection is involved, because the discarded solution is used only to
   instantiate a universally quantified inequality at one fixed sample point.
2. **The spatial step**, `LocalizationEnvelopeSpatial`:
   `fint_{cu_K} |grad w|^4 <= ‖grad w‖^4_{L8bar(cu_K)} <= (Chead + Tfluct)^2`.
3. **The probabilistic step**, `LocalizationEnvelopeMoment`:
   `E[(Chead + Tfluct)^2] <= 2 Chead^2 + 2 E[Tfluct^2] <= 2 Chead^2 + 32 e^2 A^2`
   at `A = cgamma^100`.

## The envelope constant

```
  freshShellFourthEnergyConst Chead A  =  2 Chead^2 + 32 e^2 A^2 ,
```

and each factor is traceable:

* `2 Chead^2 + 2 E[Tfluct^2]` is `(a+b)^2 <= 2a^2 + 2b^2`, the sharp elementary
  constant;
* `E[Tfluct^2] <= (4 e A)^2 = 16 e^2 A^2` is CoarseGraining's
  `integral_rpow_le_of_isBigOWith_gammaSigma` at `sigma = 1`, `p = 2`, whose
  constant is `gammaMomentConst 1 * 2 = 2 e * 2 = 4 e` (module
  `LocalizationEnvelopeMoment`);
* `2 * 16 e^2 A^2 = 32 e^2 A^2`.

`Chead` is the head constant of `e.nablaw.in.L.eight` and `A = cgamma^100` is
its printed fluctuation amplitude; neither is re-derived here.

## What is proved

* `freshShellFourthEnergyConst` -- the explicit envelope constant.
* `exists_freshShell_cubeEuclideanL8_leg_bound` -- the leg split of
  `e.nablaw.in.L.eight`: each corrector separately, with the same `Chead`,
  the same threshold and the same `Tfluct`.

The derivation of `henv` itself from that leg, and its instantiation at the
actual correctors of `e.def.w` with no envelope binder left, are
`LocalizationEnvelopeWire.gridFourthMoment_mesoWindowEnergy_le_of_measurable_fourthEnergy`
and
`LocalizationEnvelopeWire.exists_freshShell_gridFourthMoment_mesoWindowEnergy_le_wired`,
which need the covering discharge as well and so are the natural place for it.

## What is not proved here

* **Measurability of `Tfluct` in the sample is open.**
  `Corrector.FreshShellL8` produces `Tfluct` existentially and asserts nothing
  about its measurability; `IndependentSums.IsBigOWith` is a statement about
  `mu.real` of upper-tail sets and does not imply it.  Any annealed derivation
  from the leg therefore has to carry that measurability explicitly, as an
  antecedent *inside* the existential that produces `Tfluct`, which is the
  narrowest honest placement.
* **Measurability of the correctors in the sample is open.**  The leg split
  below assumes nothing of the kind: it is quantified over one sample point and
  one pair of solutions at a time, with no sample-space hypothesis at all.
* **`L^8` membership of the gradient is a binder.**  A finite
  `cubeEuclideanLpNorm` does not give it (see `LocalizationEnvelopeSpatial`).
* **The second inequality, `<= cgamma^{15}`, is untouched.**

## References

* ABK26, `e.nablaw.in.L.eight`; `e.def.w`, display (label);
  `e.recurrence.params`, display (label), with the `h` gate;
  `e.lower.bound.oscillations` (its deduction).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## The envelope constant -/

/-- The annealed fourth-energy envelope of the covering step:
`2 Chead^2 + 32 e^2 A^2`, where `Chead` is the head constant of
`e.nablaw.in.L.eight` and `A` its fluctuation amplitude. -/
def freshShellFourthEnergyConst (Chead A : ℝ) : ℝ :=
  2 * Chead ^ (2 : ℕ) + 32 * Real.exp 1 ^ (2 : ℕ) * A ^ (2 : ℕ)

/-- Unconditional: the envelope constant is nonnegative.  No sign hypothesis on
`Chead` is needed, both powers being even. -/
theorem freshShellFourthEnergyConst_nonneg (Chead A : ℝ) :
    0 ≤ freshShellFourthEnergyConst Chead A := by
  have h : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  unfold freshShellFourthEnergyConst
  positivity

/-! ## The leg split of `e.nablaw.in.L.eight` -/

/-- **The leg split of `e.nablaw.in.L.eight`.**

`Corrector.exists_cubeEuclideanL8_gradient_sq_sum_le_const_add_gammaPow` bounds
the *sum* of the two squared normalized `L^8` gradient norms.  Since both
summands are nonnegative, each corrector separately obeys the same bound; the
only thing needed to discard the other summand is that the other problem is
solvable at the same sample point, which
`Corrector.exists_isMeanZeroNeumannRhsWeakSolution_streamForcing` and
`Corrector.exists_isZeroTraceDirichletRhsWeakSolution_streamForcing` supply
unconditionally.  `Chead`, the threshold `gamma0`, `Tfluct` and its tail are
unchanged. -/
theorem exists_freshShell_cubeEuclideanL8_leg_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ Chead : ℝ, 0 < Chead ∧
      ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
        ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
          ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
            Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
            ∀ (m K : ℤ) (hh : ℕ), 0 < hh → m - (hh : ℤ) ≤ m0 →
              (hh : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
              (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
              ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
                Book.Ch02.vecNorm e' ≤ 1 →
                ∃ Tfluct : Cutoff.ShellSeq d → ℝ,
                  (∀ omega, 0 ≤ Tfluct omega) ∧
                  IndependentSums.IsBigOWith M.P.toMeasure
                      (IndependentSums.gammaSigma 1) Tfluct
                      (M.gamma ^ (100 : ℕ)) ∧
                  (∀ (omega : Cutoff.ShellSeq d)
                      (wD : H10Function (openCubeSet (originCube d K))),
                      IsZeroTraceDirichletRhsWeakSolution
                          (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                          (openCubeSet (originCube d K)) wD
                          (fun x => -Corrector.streamForcing
                            ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹ omega
                            (m - (hh : ℤ)) m e x) →
                      Corrector.cubeEuclideanLpNorm (originCube d K) 8
                          wD.toH1Function.grad ^ (2 : ℕ) ≤ Chead + Tfluct omega) ∧
                  (∀ (omega : Cutoff.ShellSeq d)
                      (wN : H1MeanZeroFunction (openCubeSet (originCube d K))),
                      IsMeanZeroNeumannRhsWeakSolution
                          (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                          (openCubeSet (originCube d K)) wN
                          (fun x => -Corrector.streamForcing
                            ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹ omega
                            (m - (hh : ℤ)) m e' x) →
                      Corrector.cubeEuclideanLpNorm (originCube d K) 8
                          wN.toH1Function.grad ^ (2 : ℕ) ≤ Chead + Tfluct omega) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Chead, hCheadpos, gamma0, hg0pos, hg0quarter, hmain⟩ :=
    Corrector.exists_cubeEuclideanL8_gradient_sq_sum_le_const_add_gammaPow d hd
  refine ⟨Chead, hCheadpos, gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he'
  obtain ⟨Tfluct, hTnn, hTtail, hbound⟩ :=
    hmain M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he'
  refine ⟨Tfluct, hTnn, hTtail, ?_, ?_⟩
  · intro omega wD hwD
    obtain ⟨wN, hwN⟩ :=
      Corrector.exists_isMeanZeroNeumannRhsWeakSolution_streamForcing
        (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹ omega
        (m - (hh : ℤ)) m e'
    have h := hbound omega wD hwD wN hwN
    have hnn : (0 : ℝ) ≤ Corrector.cubeEuclideanLpNorm (originCube d K) 8
        wN.toH1Function.grad ^ (2 : ℕ) := sq_nonneg _
    linarith
  · intro omega wN hwN
    obtain ⟨wD, hwD⟩ :=
      Corrector.exists_isZeroTraceDirichletRhsWeakSolution_streamForcing
        (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹ omega
        (m - (hh : ℤ)) m e
    have h := hbound omega wD hwD wN hwN
    have hnn : (0 : ℝ) ≤ Corrector.cubeEuclideanLpNorm (originCube d K) 8
        wD.toH1Function.grad ^ (2 : ℕ) := sq_nonneg _
    linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
