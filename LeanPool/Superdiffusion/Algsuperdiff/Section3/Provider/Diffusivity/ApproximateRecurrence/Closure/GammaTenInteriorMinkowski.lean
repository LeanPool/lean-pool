/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenDepthStreamForcing
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicReplaceMinkowski
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationNestedFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponsePz

/-!
# GammaTenInteriorMinkowski

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The oscillation cell is subadditive, and the flux leg splits

ABK26, `e.nablaw.oscillations`, `e.Fz.def`, `e.def.w`.

## Why this is needed

The Neumann leg of `bfF_z` is not the Neumann corrector's gradient: by
`PrincipalResponsePz.neumannFluxField` it is

```
  neumannFluxField sigma omega lo hi e' wN
    = wN.grad + streamForcing sigma^{-1} omega lo hi e' ,
```

so the oscillation input of Step 2 at the flux leg has to be read at a **sum**.
`Closure.GammaTenDepthStreamForcing.meshOscillationCell_streamForcing_le` bounds
the second summand; what is missing is the triangle inequality that lets the two
be added, at the *oscillation* (mean-subtracted) cell rather than at the
deviation from a fixed constant.

## What is proved

* `volumeAverageVec_add` --- linearity of the vector volume average.
* `sqrt_meanSquareOscillationVecOn_add_le_of_memVectorL2` --- **the triangle
  inequality for the mean-square oscillation**, from the proved deviation form
  `Corrector.HarmonicReplaceMinkowski.sqrt_meanSquareDeviationVecOn_add_le_of_memVectorL2`
  read at the two fields' own averages.  Only the two `L^2` memberships are
  assumed: no continuity is required of either summand.
* `meshOscillationCell_add_le` --- the same at the mesh cell of
  `e.nablaw.oscillations`.
* `meshOscillationCell_neumannFluxField_le` --- **the flux-leg split**: the
  oscillation cell of the Neumann flux field is the oscillation cell of
  `grad w_N` plus the deterministic shell-derivative term of the forcing.

## Binders

The two `L^2` memberships on the oscillation cube, `0 <= sigmaInv` and the scale
gate `n <= lowScale` of the forcing bound.  No smallness gate, no model, no
probability and no corrector estimate occurs.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `e.nablaw.oscillations`, `e.Fz.def`, `e.def.w`, `e.W.1.inf.bound`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 HCPolySupport.Book.Ch03
open MeasureTheory
open Algsuperdiff.Section3.Cutoff Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector

noncomputable section

variable {d : ℕ}

/-! ## Linearity of the vector volume average -/

/-- Coordinates of an `L^2` vector field on a finite-measure set are integrable. -/
theorem integrableOn_coord_of_memVectorL2 {V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)] {f : Vec d → Vec d} (hf : MemVectorL2 V f)
    (k : Fin d) : IntegrableOn (fun x => f x k) V volume :=
  (memScalarL2_coord_of_memVectorL2 hf k).integrable (by norm_num)

/-- **Linearity of the vector volume average.**  Conditional only on
coordinatewise integrability. -/
theorem volumeAverageVec_add {V : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : ∀ k : Fin d, IntegrableOn (fun x => f x k) V volume)
    (hg : ∀ k : Fin d, IntegrableOn (fun x => g x k) V volume) :
    volumeAverageVec V (fun x => f x + g x) =
      volumeAverageVec V f + volumeAverageVec V g := by
  funext k
  have hstep := volumeAverage_add (hf k) (hg k)
  show volumeAverage V (fun x => f x k + g x k) =
    volumeAverage V (fun x => f x k) + volumeAverage V (fun x => g x k)
  exact hstep

/-! ## The triangle inequality at the mean-square oscillation -/

/-- **The triangle inequality for the mean-square oscillation of `L^2` fields.**

`|| (f + g) - avg (f + g) ||_{L2bar(V)} <= || f - avg f ||_{L2bar(V)} +
|| g - avg g ||_{L2bar(V)}` on any finite-measure set, with no continuity
hypothesis.

only on the two `L^2` memberships. -/
theorem sqrt_meanSquareOscillationVecOn_add_le_of_memVectorL2 {V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)] {f g : Vec d → Vec d}
    (hf : MemVectorL2 V f) (hg : MemVectorL2 V g) :
    Real.sqrt (Book.Ch01.meanSquareOscillationVecOn V (fun x => f x + g x)) ≤
      Real.sqrt (Book.Ch01.meanSquareOscillationVecOn V f) +
        Real.sqrt (Book.Ch01.meanSquareOscillationVecOn V g) := by
  have havg : volumeAverageVec V (fun x => f x + g x) =
      volumeAverageVec V f + volumeAverageVec V g :=
    volumeAverageVec_add (fun k => integrableOn_coord_of_memVectorL2 hf k)
      (fun k => integrableOn_coord_of_memVectorL2 hg k)
  show Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V (fun x => f x + g x)
      (volumeAverageVec V (fun x => f x + g x))) ≤ _
  rw [havg]
  exact sqrt_meanSquareDeviationVecOn_add_le_of_memVectorL2 hf hg
    (volumeAverageVec V f) (volumeAverageVec V g)

/-- **The oscillation cell of `e.nablaw.oscillations` is subadditive.**

only on the two `L^2` memberships on the oscillation cube. -/
theorem meshOscillationCell_add_le (n : ℤ) {f g : Vec d → Vec d} (R : TriadicCube d)
    (hf : MemVectorL2 (openCubeAtScale (triadicCubeShift R) n) f)
    (hg : MemVectorL2 (openCubeAtScale (triadicCubeShift R) n) g) :
    meshOscillationCell n (fun x => f x + g x) R ≤
      meshOscillationCell n f R + meshOscillationCell n g R :=
  sqrt_meanSquareOscillationVecOn_add_le_of_memVectorL2 hf hg

/-! ## The flux leg -/

/-- **The oscillation cell of the Neumann flux field splits.**

```
  osc_n (neumannFluxField sigma omega lo hi e' wN) (R)
    <=  osc_n (grad w_N) (R)
        + 3^n . sigma^{-1} . d . |e'|_2 . shellDerivNormSum lo hi z_R omega .
```

The second summand is the proved deterministic bound
`Closure.GammaTenDepthStreamForcing.meshOscillationCell_streamForcing_le`; the
dimensional factor there is `d`, not `sqrt d`, and it is not absorbed here.

on the two `L^2` memberships on the oscillation cube, on `0 <= sigma^{-1}` and
on the scale gate `n <= lowScale`. -/
theorem meshOscillationCell_neumannFluxField_le {sigma : PositiveScalar}
    (omega : ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d) {Qc : TriadicCube d}
    (wN : H1MeanZeroFunction (openCubeSet Qc)) (n : ℤ) (hn : n ≤ lowScale)
    (R : TriadicCube d)
    (hgrad : MemVectorL2 (openCubeAtScale (triadicCubeShift R) n)
      wN.toH1Function.grad)
    (hforce : MemVectorL2 (openCubeAtScale (triadicCubeShift R) n)
      (streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e')) :
    meshOscillationCell n (neumannFluxField sigma omega lowScale highScale e' wN) R ≤
      meshOscillationCell n wN.toH1Function.grad R +
        (3 : ℝ) ^ n * (((sigma : ℝ))⁻¹ * (d : ℝ) * vecNorm e' *
          shellDerivNormSum lowScale highScale (triadicCubeShift R) omega) := by
  have hsig : (0 : ℝ) ≤ ((sigma : ℝ))⁻¹ := (inv_pos.2 sigma.2).le
  have hsplit : neumannFluxField sigma omega lowScale highScale e' wN =
      fun x => wN.toH1Function.grad x +
        streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x := rfl
  rw [hsplit]
  refine le_trans (meshOscillationCell_add_le n R hgrad hforce) ?_
  exact add_le_add le_rfl
    (meshOscillationCell_streamForcing_le hsig omega lowScale highScale e' n hn R)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
