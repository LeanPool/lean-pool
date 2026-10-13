/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenFluxMeasurability
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5InputOscillation

/-!
# GammaTenInteriorCellInputs

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The cellwise typing inputs of the interior envelope, at the closure's families

ABK26, `e.nablaw.oscillations`, `e.Fz.def`, `e.def.w`, `e.nablaw.in.L.eight`.

## What this module supplies

The interior Besov envelope of `Closure.GammaTenInteriorGaugedEnvelope` carries,
for each of its two raw legs, the three cellwise typing binders

```
  Measurable (osc cell) ,   Integrable ((osc cell)^4) ,   MemLp (field) 2 ,
```

read at **every** depth-refined interior grid.  Each is a statement about one
cell, and the only spatial data a cell of the interior grid carries is its scale
and its containment in the localization cube.  This module produces the six at
the closure's own Dirichlet and Neumann families, from the single `L^8`
membership of the two corrector gradients:

* the Dirichlet leg's measurability is the proved
  `Closure.Step5InputOscillation.measurable_meshOscillationCell_freshShellDirichletGrad`,
  composed with the sample inclusion;
* the flux leg's is
  `Closure.GammaTenFluxMeasurability.measurable_meshOscillationCell_neumannFluxField_cutoffSample`;
* the flux leg's fourth-power integrability is the Dirichlet-style one for the
  Neumann *gradient* plus
`integrable_meshOscillationCell_pow_four_neumannFluxField_cutoffSample`;
* the two `L^2` memberships are the proved
  `Closure.GammaTenAssemblySide.memLp_two_gradH10_normalizedCubeMeasure_of_subset`
  and `..._neumannFluxField_normalizedCubeMeasure`.

## What is proved

* `memLp_eight_neumannFluxField_closure` --- the flux leg is `L^8` on the
  localization cube, the gradient by `e.nablaw.in.L.eight` and the forcing because
  it is continuous.
* `measurable_meshOscillationCell_closureDirichlet_cutoffSample` and
  `measurable_meshOscillationCell_closureFlux_cutoffSample` --- the two
  measurabilities at one cell.
* `integrable_meshOscillationCell_pow_four_closureFlux_cutoffSample` --- the flux
  leg's fourth-power integrability at one cell, from the Neumann gradient's.

## Binders

The standing `2 <= d`, the cell data `hsc : R.scale = nn` and
`hsub : openCubeSet R ⊆ openCubeSet (cu_K)`, the scale gate `nn <= n` and
`n < n + h` for the integrability, and --- for the integrability only --- the
Neumann gradient cell's own fourth-power integrability.  No smallness gate on
`cgamma` and no model estimate occurs.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `e.nablaw.oscillations`, `e.Fz.def`, `e.def.w`, `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 HCPolySupport.Book.Ch03
open MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The flux leg is `L^8` on the localization cube -/

/-- **The flux leg of `e.Fz.def` is `L^8` on `cu_K`.**  The gradient by
`e.nablaw.in.L.eight`, the stream forcing because it is continuous.

Proved from `memLp_eight_grad_closureNeumannAlong`. -/
theorem memLp_eight_neumannFluxField_closure [NeZero d] (hd : 2 ≤ d) (M : ABKModel d)
    (n : ℤ) (h : ℕ) (K : ℕ) (e' : Vec d) (omega : ShellSeq d) :
    MemLp (neumannFluxField (Annealed.sigmaBar M n) omega n (n + (h : ℤ)) e'
        (closureNeumannAlong M n h K e' omega)) (8 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (K : ℤ))) :=
  (memLp_eight_grad_closureNeumannAlong hd M n h K e' omega).add
    (memLp_normalizedCubeMeasure_of_continuous (originCube d (K : ℤ)) 8
      (continuous_streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e'))

/-! ## Measurability of the two oscillation cells -/

/-- **The Dirichlet leg's oscillation cell is measurable on the cutoff-sample
carrier.**

Conditional on `hd` and the cell data `hsc`, `hsub`.

Proved from `memLp_eight_grad_closureDirichletAlong`. -/
theorem measurable_meshOscillationCell_closureDirichlet_cutoffSample [NeZero d]
    (hd : 2 ≤ d) (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e : Vec d)
    {nn : ℤ} (R : TriadicCube d) (hsc : R.scale = nn)
    (hsub : openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ))) :
    Measurable fun omega : CutoffSample d =>
      meshOscillationCell nn
        (closureDirichletAlong M n h K e omega.val).toH1Function.grad R := by
  have hL8 : ∀ omega : ShellSeq d,
      MemLp (closureDirichletAlong M n h K e omega).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d (K : ℤ))) := fun omega =>
    memLp_eight_grad_closureDirichletAlong hd M n h K e omega
  have hbase := measurable_meshOscillationCell_freshShellDirichletGrad
    (originCube d (K : ℤ)) ((Annealed.sigmaBar M n : ℝ))⁻¹ n (n + (h : ℤ)) e R hsc hsub
    (closureDirichletAlong M n h K e)
    (isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e)
    (fun omega k => (integrableOn_openCubeSet_coord_of_memLp_eight
      (originCube d (K : ℤ)) (hL8 omega) k).mono_set hsub)
    (fun omega k => (integrableOn_openCubeSet_coord_sq_of_memLp_eight
      (originCube d (K : ℤ)) (hL8 omega) k).mono_set hsub)
  exact hbase.comp measurable_subtype_coe

/-- **The flux leg's oscillation cell is measurable on the cutoff-sample
carrier.**

Conditional on `hd` and the cell data `hsc`, `hsub`.

Proved from `memLp_eight_grad_closureNeumannAlong`. -/
theorem measurable_meshOscillationCell_closureFlux_cutoffSample [NeZero d]
    (hd : 2 ≤ d) (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e' : Vec d)
    {nn : ℤ} (R : TriadicCube d) (hsc : R.scale = nn)
    (hsub : openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ))) :
    Measurable fun omega : CutoffSample d =>
      meshOscillationCell nn
        (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
          (closureNeumannAlong M n h K e' omega.val)) R := by
  have hL8 : ∀ omega : ShellSeq d,
      MemLp (neumannFluxField (Annealed.sigmaBar M n) omega n (n + (h : ℤ)) e'
          (closureNeumannAlong M n h K e' omega)) (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d (K : ℤ))) := fun omega =>
    memLp_eight_neumannFluxField_closure hd M n h K e' omega
  exact measurable_meshOscillationCell_neumannFluxField_cutoffSample
    (originCube d (K : ℤ)) (Annealed.sigmaBar M n) ((Annealed.sigmaBar M n : ℝ))⁻¹ n
    (n + (h : ℤ)) e' e' R hsc hsub (closureNeumannAlong M n h K e')
    (isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e')
    (fun omega k => (integrableOn_openCubeSet_coord_of_memLp_eight
      (originCube d (K : ℤ)) (hL8 omega) k).mono_set hsub)
    (fun omega k => (integrableOn_openCubeSet_coord_sq_of_memLp_eight
      (originCube d (K : ℤ)) (hL8 omega) k).mono_set hsub)

/-! ## The flux leg's fourth-power integrability -/

/-- **The flux leg's `hintcell` at one cell, from the Neumann gradient's.**

Conditional on `hd`, the scale gates `hnn`, `hh`, the cell data `hsc`, `hsub`, and the
Neumann gradient cell's own fourth-power integrability `hoscInt`.

Proved from `memLp_eight_grad_closureNeumannAlong` through the measurability. -/
theorem integrable_meshOscillationCell_pow_four_closureFlux_cutoffSample [NeZero d]
    (hd : 2 ≤ d) (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e' : Vec d)
    (hh : 0 < h) {nn : ℤ} (hnn : nn ≤ n) (R : TriadicCube d) (hsc : R.scale = nn)
    (hsub : openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ)))
    (hoscInt : Integrable (fun omega : CutoffSample d =>
        meshOscillationCell nn
          (closureNeumannAlong M n h K e' omega.val).toH1Function.grad R ^ (4 : ℕ))
      (cutoffSampleLaw M).toMeasure) :
    Integrable (fun omega : CutoffSample d =>
        meshOscillationCell nn
          (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
            (closureNeumannAlong M n h K e' omega.val)) R ^ (4 : ℕ))
      (cutoffSampleLaw M).toMeasure := by
  have hlt : n < n + (h : ℤ) := by
    have h1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
    omega
  exact integrable_meshOscillationCell_pow_four_neumannFluxField_cutoffSample M
    (Annealed.sigmaBar M n) hlt e' (closureNeumannAlong M n h K e') hnn R hsc hsub
    (measurable_meshOscillationCell_closureFlux_cutoffSample hd M n h K e' R hsc hsub)
    hoscInt

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
