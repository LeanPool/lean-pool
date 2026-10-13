/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Junctions
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseTerminal
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellUniqueness

/-!
# JunctionDischargePrincipalSwitch

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Junction 4 discharged: the principal comparison at the closure's own correctors

ABK26, `l.approximate.recurrence.formula`, Steps 1--3 and
`e.lower.bound.principal.one`.

`Closure.Junctions.PrincipalSwitchEndpoint` is the proved principal-response
terminal
`PrincipalResponseTerminal.exists_const_descendantsAverage_integral_principalEnergy_le_annealedLimit`,
re-indexed from the terminal's `(m - hgap, m)` to the recurrence pair `(n, n +
h)`.  Two things separate the two statements, and this module supplies both.

1. **The integer re-indexing.**  Instantiating the terminal at `m := n + h` and
   `hgap := h` leaves the single rewrite `n + h - h = n`; that is the whole of
   the carrier difference, exactly as `Closure.Junctions`' header records.

2. **The choice of correctors.**  The terminal *produces* its pair `w_D, w_N`
   existentially, indexed by the shell sequence.  The closure assembly cannot
   use that pair: Steps 4 and 5 and the fresh-shell energy display all read the
   correctors along the **increment path** (`Closure.alongIncrementPath`), and
   one and the same pair has to serve all four junctions at every localization
   cube.  So the terminal's conclusion has to be transported from *its* witness
   pair to *the caller's* pair.

   That transport is legitimate, and unconditional: the two problems of
   `e.def.w` determine their solutions' gradients
   (`Corrector.FreshShellUniqueness`), and both
   `Closure.principalEnergyAverage` and `Closure.gaugeEnergyAverage` see the
   correctors only through `cubeAverageVec R (grad w)` on the descendant cubes
   of `cu_K`.  The congruence lemmas below make that visible, one carrier at a
   time, and `principalSwitchEndpoint_of_terminal` states the terminal at an
   **arbitrary** pair of solutions of `e.def.w`.

## What is supplied

* `cubeAverageVec_congr_ae` --- the cube average only sees the a.e. class.
* `grad_ae_eq_of_isZeroTraceDirichletRhsWeakSolution`,
  `grad_ae_eq_of_isMeanZeroNeumannRhsWeakSolution` --- gradient uniqueness of
  `e.def.w` in the pointwise a.e. spelling the congruences consume.
* `principalPz_congr_ae`, `gaugedPrincipalLoadShell_congr_ae`,
  `principalEnergyAverage_congr_ae`, `gaugeEnergyAverage_congr_ae`,
  `principalSwitchEndpoint_congr_ae` --- the transport, carrier by carrier.
* `principalSwitchEndpoint_of_terminal` --- `Closure.PrincipalSwitchEndpoint`,
  proved, at any pair of `e.def.w` solutions, from the proved terminal.

## The terminal's source premises, threaded

`principalSwitchEndpoint_of_terminal` carries exactly the terminal's own
binders, re-indexed:

| binder | terminal's form | here |
|---|---|---|
| induction state | `inductionState M (m - 1) E` | `inductionState M (n + h - 1) Ec` |
| shell nondegeneracy | `0 < hgap` | `0 < h` |
| regime | `Cterm cstar^{-1} <= E` | unchanged |
| fifth-root gate | `cgamma <= E^{-5}` | unchanged |
| shell budget | `hgap <= 6 cstar cgamma^{-1}` | unchanged |
| localization gap | `10^10 cgamma^{-1} <= Kc - m` | `... <= Kc - (n + h)` |
| directions | `|e|, |e'| <= 1` | unchanged |
| depth naming | `Kc - j = recurrenceMesoScale a cgamma m hgap` | at `m = n + h` |

No binder is added, none is weakened, and no smallness beyond the terminal's own
is assumed.  The two corrector binders `hwD`, `hwN` are `e.def.w` itself --- the
*definition* of the pair the caller is using, not an assumption about it.

## References

* ABK26, `l.approximate.recurrence.formula`, Steps 1--3.
* ABK26, `e.def.w`; `e.Pz.def`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector

noncomputable section

variable {d : ℕ}

/-! ## The cube average sees only the a.e. class -/

/-- Unconditional: two fields that agree a.e. on a triadic cube have the same
cube average. -/
theorem cubeAverageVec_congr_ae (R : TriadicCube d) {g1 g2 : Vec d → Vec d}
    (hg : g1 =ᵐ[volume.restrict (cubeSet R)] g2) :
    cubeAverageVec R g1 = cubeAverageVec R g2 := by
  funext i
  have hcomp : (fun x => g1 x i) =ᵐ[volume.restrict (cubeSet R)] fun x => g2 x i := by
    filter_upwards [hg] with x hx
    exact congrFun hx i
  show cubeAverage R (fun x => g1 x i) = cubeAverage R (fun x => g2 x i)
  rw [cubeAverage, cubeAverage, integral_congr_ae hcomp]

/-! ## Gradient uniqueness of `e.def.w`, in the pointwise a.e. spelling -/

/-- Unconditional: two zero-trace Dirichlet weak solutions of `e.def.w` for one
and the same forcing have a.e. equal gradients.  This is
`Corrector.gradToVectorL2_eq_of_isZeroTraceDirichletRhsWeakSolution_openCubeSet`
read through `H1Function.coeFn_gradToVectorL2`. -/
theorem grad_ae_eq_of_isZeroTraceDirichletRhsWeakSolution (Q : TriadicCube d)
    {g : Vec d → Vec d} {u v : H10Function (openCubeSet Q)}
    (hu : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) u g)
    (hv : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) v g) :
    (fun x => u.toH1Function.grad x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => v.toH1Function.grad x := by
  have heq := gradToVectorL2_eq_of_isZeroTraceDirichletRhsWeakSolution_openCubeSet Q hu hv
  have h1 := H1Function.coeFn_gradToVectorL2 u.toH1Function
  have h2 := H1Function.coeFn_gradToVectorL2 v.toH1Function
  rw [heq] at h1
  exact h1.symm.trans h2

/-- Unconditional: the mean-zero Neumann mirror. -/
theorem grad_ae_eq_of_isMeanZeroNeumannRhsWeakSolution (Q : TriadicCube d)
    {g : Vec d → Vec d} {u v : H1MeanZeroFunction (openCubeSet Q)}
    (hu : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) u g)
    (hv : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) v g) :
    (fun x => u.toH1Function.grad x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => v.toH1Function.grad x := by
  have heq : u.toH1Function.gradToVectorL2 = v.toH1Function.gradToVectorL2 :=
    gradToVectorL2_eq_of_isMeanZeroNeumannRhsWeakSolution_openCubeSet Q hu hv
  have h1 := H1Function.coeFn_gradToVectorL2 u.toH1Function
  have h2 := H1Function.coeFn_gradToVectorL2 v.toH1Function
  rw [heq] at h1
  exact h1.symm.trans h2

/-! ## The transport, carrier by carrier -/

private theorem descendantsAverage_congr_mem' (Q : TriadicCube d) (j : ℕ)
    {f g : TriadicCube d → ℝ} (hfg : ∀ R ∈ descendantsAtDepth Q j, f R = g R) :
    descendantsAverage Q j f = descendantsAverage Q j g := by
  show ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, f R =
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, g R
  rw [Finset.sum_congr rfl hfg]

/-- Unconditional: `e.Pz.def` reads the two correctors only through their cube
averages, so a.e. equal gradients give the same load. -/
theorem principalPz_congr_ae (sigma : PositiveScalar) (omega : ShellSeq d)
    (lowScale highScale : ℤ) (e e' : Vec d) {Q : TriadicCube d} {j : ℕ}
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j)
    {wD1 wD2 : H10Function (openCubeSet Q)}
    {wN1 wN2 : H1MeanZeroFunction (openCubeSet Q)}
    (hD : (fun x => wD1.toH1Function.grad x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => wD2.toH1Function.grad x)
    (hN : (fun x => wN1.toH1Function.grad x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => wN2.toH1Function.grad x) :
    principalPz sigma omega lowScale highScale e e' R wD1 wN1 =
      principalPz sigma omega lowScale highScale e e' R wD2 wN2 := by
  have hDR := ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR hD
  have hNR := ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR hN
  have h1 : cubeAverageVec R (fun x => wD1.toH1Function.grad x) =
      cubeAverageVec R (fun x => wD2.toH1Function.grad x) :=
    cubeAverageVec_congr_ae R hDR
  have h2 : cubeAverageVec R (neumannFluxField sigma omega lowScale highScale e' wN1) =
      cubeAverageVec R (neumannFluxField sigma omega lowScale highScale e' wN2) := by
    refine cubeAverageVec_congr_ae R ?_
    filter_upwards [hNR] with x hx
    show wN1.toH1Function.grad x + _ = wN2.toH1Function.grad x + _
    rw [hx]
  rw [principalPz, principalPz, h1, h2]

/-- Unconditional: the gauged load of the terminal inherits the congruence. -/
theorem gaugedPrincipalLoadShell_congr_ae (sigma : PositiveScalar) (omega : ShellSeq d)
    (lowScale highScale : ℤ) (e e' : Vec d) {Q : TriadicCube d} {j : ℕ}
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j)
    {wD1 wD2 : ShellSeq d → H10Function (openCubeSet Q)}
    {wN1 wN2 : ShellSeq d → H1MeanZeroFunction (openCubeSet Q)}
    (hD : (fun x => (wD1 omega).toH1Function.grad x)
      =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => (wD2 omega).toH1Function.grad x)
    (hN : (fun x => (wN1 omega).toH1Function.grad x)
      =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => (wN2 omega).toH1Function.grad x) :
    gaugedPrincipalLoadShell sigma R lowScale highScale e e' wD1 wN1 omega =
      gaugedPrincipalLoadShell sigma R lowScale highScale e e' wD2 wN2 omega := by
  rw [gaugedPrincipalLoadShell, gaugedPrincipalLoadShell,
    principalPz_congr_ae sigma omega lowScale highScale e e' hR hD hN]

/-- Unconditional: the left-hand carrier of the terminal depends on the
correctors only through their a.e. classes. -/
theorem principalEnergyAverage_congr_ae (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (j : ℕ) (e e' : Vec d)
    {wD1 wD2 : ShellSeq d → H10Function (openCubeSet (originCube d Kc))}
    {wN1 wN2 : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc))}
    (hD : ∀ omega : ShellSeq d, (fun x => (wD1 omega).toH1Function.grad x)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d Kc))]
      fun x => (wD2 omega).toH1Function.grad x)
    (hN : ∀ omega : ShellSeq d, (fun x => (wN1 omega).toH1Function.grad x)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d Kc))]
      fun x => (wN2 omega).toH1Function.grad x) :
    principalEnergyAverage M n h Kc j e e' wD1 wN1 =
      principalEnergyAverage M n h Kc j e e' wD2 wN2 := by
  refine descendantsAverage_congr_mem' _ _ fun R hR => ?_
  have hfun : (fun omega : CutoffSample d =>
      switchCubeEnergy M (n + (h : ℤ)) R
        (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
          (wD1 omega.val) (wN1 omega.val)) omega) =
      fun omega : CutoffSample d =>
      switchCubeEnergy M (n + (h : ℤ)) R
        (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
          (wD2 omega.val) (wN2 omega.val)) omega := by
    funext omega
    rw [principalPz_congr_ae (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' hR
      (hD omega.val) (hN omega.val)]
  exact congrArg (fun F => ∫ omega : CutoffSample d, F omega
    ∂(cutoffSampleLaw M).toMeasure) hfun

/-- Unconditional: the right-hand carrier of the terminal, likewise. -/
theorem gaugeEnergyAverage_congr_ae (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (j : ℕ) (e e' : Vec d)
    {wD1 wD2 : ShellSeq d → H10Function (openCubeSet (originCube d Kc))}
    {wN1 wN2 : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc))}
    (hD : ∀ omega : ShellSeq d, (fun x => (wD1 omega).toH1Function.grad x)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d Kc))]
      fun x => (wD2 omega).toH1Function.grad x)
    (hN : ∀ omega : ShellSeq d, (fun x => (wN1 omega).toH1Function.grad x)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d Kc))]
      fun x => (wN2 omega).toH1Function.grad x) :
    gaugeEnergyAverage M n h Kc j e e' wD1 wN1 =
      gaugeEnergyAverage M n h Kc j e e' wD2 wN2 := by
  refine descendantsAverage_congr_mem' _ _ fun R hR => ?_
  have hfun : (fun omega : CutoffSample d =>
      blockVecDot
        (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e e'
          wD1 wN1 omega.val)
        (blockMatVecMul
          (Ch02.blockDiag ((Annealed.sigmaBar M n : ℝ) • (1 : Mat d))
            (((Annealed.sigmaBar M n : ℝ))⁻¹ • (1 : Mat d)))
          (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e e'
            wD1 wN1 omega.val))) =
      fun omega : CutoffSample d =>
      blockVecDot
        (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e e'
          wD2 wN2 omega.val)
        (blockMatVecMul
          (Ch02.blockDiag ((Annealed.sigmaBar M n : ℝ) • (1 : Mat d))
            (((Annealed.sigmaBar M n : ℝ))⁻¹ • (1 : Mat d)))
          (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e e'
            wD2 wN2 omega.val)) := by
    funext omega
    rw [gaugedPrincipalLoadShell_congr_ae (Annealed.sigmaBar M n) omega.val n
      (n + (h : ℤ)) e e' hR (hD omega.val) (hN omega.val)]
  exact congrArg (fun F => ∫ omega : CutoffSample d, F omega
    ∂(cutoffSampleLaw M).toMeasure) hfun

/-- Unconditional: `Closure.PrincipalSwitchEndpoint` transports along a.e.-equal
corrector gradients. -/
theorem principalSwitchEndpoint_congr_ae (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (j : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e e' : Vec d)
    {wD1 wD2 : ShellSeq d → H10Function (openCubeSet (originCube d Kc))}
    {wN1 wN2 : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc))}
    (hD : ∀ omega : ShellSeq d, (fun x => (wD1 omega).toH1Function.grad x)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d Kc))]
      fun x => (wD2 omega).toH1Function.grad x)
    (hN : ∀ omega : ShellSeq d, (fun x => (wN1 omega).toH1Function.grad x)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d Kc))]
      fun x => (wN2 omega).toH1Function.grad x)
    (hswitch : PrincipalSwitchEndpoint M n h Kc j Ec e e' wD1 wN1) :
    PrincipalSwitchEndpoint M n h Kc j Ec e e' wD2 wN2 := by
  unfold PrincipalSwitchEndpoint at hswitch ⊢
  rwa [principalEnergyAverage_congr_ae M n h Kc j e e' hD hN,
    gaugeEnergyAverage_congr_ae M n h Kc j e e' hD hN] at hswitch

/-! ## Junction 4, discharged -/

/-- **`Closure.PrincipalSwitchEndpoint`, proved, at any pair of `e.def.w`
solutions.**

The constant `Cterm` is the proved terminal's own; the premises are the
terminal's own, re-indexed from `(m - hgap, m)` to `(n, n + h)`.  `hwD` and
`hwN` are the *definition* of the corrector pair the caller is using, i.e.
`e.def.w` at the directions `e`, `e'`; the terminal's own witness pair is
discarded in favour of the caller's by gradient uniqueness.

No incomplete-proof axiom is inherited.  See the module header. -/
theorem principalSwitchEndpoint_of_terminal (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cterm : ℝ, 0 < Cterm ∧
      ∀ (M : ABKModel d) (n Kc : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (n + (h : ℤ) - 1) Ec →
        0 < h →
        Cterm * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) →
        M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ) →
        (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
        (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (Kc : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) →
        ∀ e e' : Vec d, Ch02.vecNorm e ≤ 1 → Ch02.vecNorm e' ≤ 1 →
          ∀ j : ℕ,
            ((originCube d Kc).scale : ℤ) - (j : ℤ) =
              recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ) →
            ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
              (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc))),
              (∀ omega : ShellSeq d,
                IsZeroTraceDirichletRhsWeakSolution
                  (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                  (openCubeSet (originCube d Kc)) (wD omega)
                  (fun x => -streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n
                    (n + (h : ℤ)) e x)) →
              (∀ omega : ShellSeq d,
                IsMeanZeroNeumannRhsWeakSolution
                  (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                  (openCubeSet (originCube d Kc)) (wN omega)
                  (fun x => -streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n
                    (n + (h : ℤ)) e' x)) →
              PrincipalSwitchEndpoint M n h Kc j Ec e e' wD wN := by
  obtain ⟨Cterm, hCterm, hmain⟩ :=
    exists_const_descendantsAverage_integral_principalEnergy_le_annealedLimit d hd
  refine ⟨Cterm, hCterm, ?_⟩
  intro M n Kc h Ec hstate hh hCE hgammaE hhcap hK e e' he he' j hscale wD wN hwD hwN
  obtain ⟨wD0, wN0, hwD0, hwN0, hle⟩ :=
    hmain M (n + (h : ℤ)) Kc h Ec hstate hh hCE hgammaE hhcap hK e e' he he' j hscale
  have hnh : n + (h : ℤ) - (h : ℤ) = n := by ring
  rw [hnh] at hwD0 hwN0 hle
  have hDae : ∀ omega : ShellSeq d, (fun x => (wD0 omega).toH1Function.grad x)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d Kc))]
      fun x => (wD omega).toH1Function.grad x := fun omega =>
    grad_ae_eq_of_isZeroTraceDirichletRhsWeakSolution _ (hwD0 omega) (hwD omega)
  have hNae : ∀ omega : ShellSeq d, (fun x => (wN0 omega).toH1Function.grad x)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d Kc))]
      fun x => (wN omega).toH1Function.grad x := fun omega =>
    grad_ae_eq_of_isMeanZeroNeumannRhsWeakSolution _ (hwN0 omega) (hwN omega)
  exact principalSwitchEndpoint_congr_ae M n h Kc j Ec e e' hDae hNae hle

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
