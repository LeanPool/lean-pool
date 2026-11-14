/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.CutoffAnalyticData
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeCutoffLimit
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeJointCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DirichletSolvability
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.InteriorContinuity

/-!
# ExitTimeCutoffLimitTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Continuous representatives of the exit-time solutions, and the truncated family

The exit-time datum problem `-∇·a∇u = 1` on `y + □_n` with zero boundary values is posed here
for three coefficient fields: the truncated fields `a_L = ν I + k_L` at every truncation scale,
the full stream field `a = ν I + k`, and the constant comparator `σ_n I`.  All three have the
same structure — a positive scalar symmetric part and a continuous skew part of arbitrary size —
and that structure alone gives every solution a representative continuous on the open cube, by
freezing the skew part at each interior point and applying the small-contrast interior estimate
on a small ball.  No smallness, no event and no bound on the solution is used.

The last section collects the truncated solutions with their representatives into one family
indexed by the truncation scales, in the form the passage `L → ∞` consumes.

## Main results

* `exists_isCubeRepresentative_of_isDirichletSolutionAt` — a continuous representative for a
  coefficient field with scalar symmetric part and continuous skew part.
* `exists_isCubeRepresentative_cutoff`, `exists_isCubeRepresentative_streamCoefficient`,
  `exists_isCubeRepresentative_comparator` — the three instances.
* `exists_cutoffSolutionFamily_linearAxisDatum` — the truncated solutions with their
  representatives at every truncation scale.

## References

* ABK26, the localized exit-time problem of Section 5.2, and the passage `L → ∞` from the
  truncated fields `a_L` to `a`.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
open DivergenceFormProcess.Form
open HCPolySupport MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Continuous representatives from the structure of the coefficient -/

/-- **The exit-time solution has a continuous representative.**  For a coefficient field whose
symmetric part is the scalar field `ν I` with `ν > 0` and whose skew part is continuous on the
cube — of arbitrary size — the solution of the exit-time datum problem has a representative
continuous on the open cube.  The datum of the equation is the constant one, which is bounded,
and that is the only bound the interior estimate consumes: nothing is assumed about the size of
the solution. -/
theorem exists_isCubeRepresentative_of_isDirichletSolutionAt [NeZero d] (hd : 2 ≤ d)
    {nu : ℝ} (hnu : 0 < nu) {a : CoeffField d} {y : Vec d} {n : ℤ}
    (hsymm : ∀ z, symmPart (a z) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun z => a z - nu • (1 : Mat d)) (cubeSetAt y n))
    {i : Fin d} {u : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt a y n u (linearAxisDatum i)) :
    ∃ uRep : Vec d → ℝ, IsCubeRepresentative y n u uRep := by
  obtain ⟨w, hval, hw⟩ := exists_isScalarForcedWeakSolution_of_isDirichletSolutionAt hu
  obtain ⟨uRep, hcontRep, hae, -⟩ :=
    continuousOn_of_weakSolution_continuousCoeff hd (isOpen_cubeSetAt y n) hnu hsymm hcont
      (g := fun _ => (1 : ℝ)) (memLp_top_const (1 : ℝ)) hw
  refine ⟨uRep, ?_, hcontRep⟩
  filter_upwards [hae] with z hz
  rw [hz]
  exact (hval z).symm

/-- **The truncated field's exit-time solution has a continuous representative**, at every
truncation scale.  The symmetric part of `a_L` is `ν I` and the skew part `k_L` is continuous. -/
theorem exists_isCubeRepresentative_cutoff (M : ABKModel d) (L n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {i : Fin d} {u : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField) y n u
      (linearAxisDatum i)) :
    ∃ uRep : Vec d → ℝ, IsCubeRepresentative y n u uRep := by
  have : NeZero d := Algsuperdiff.Section3.Provider.Orlicz.neZero_of_model M
  exact exists_isCubeRepresentative_of_isDirichletSolutionAt M.shellPrefix.dimension M.nu_pos
    (fun z => Cutoff.symmPart_coefficientCutoff M.nu L omega z)
    (((continuous_coefficientCutoff M L omega).sub continuous_const).continuousOn) hu

/-- **The full stream field's exit-time solution has a continuous representative.**  The
symmetric part of `a = ν I + k` is `ν I` and the stream field `k` is continuous. -/
theorem exists_isCubeRepresentative_streamCoefficient (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Field.FullSample d M.gamma) {i : Fin d} {u : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt (Field.streamCoefficient M.nu omega) y n u
      (linearAxisDatum i)) :
    ∃ uRep : Vec d → ℝ, IsCubeRepresentative y n u uRep := by
  have : NeZero d := Algsuperdiff.Section3.Provider.Orlicz.neZero_of_model M
  exact exists_isCubeRepresentative_of_isDirichletSolutionAt M.shellPrefix.dimension M.nu_pos
    (fun z => Field.symmPart_streamCoefficient M.nu omega z)
    (((Field.continuous_streamCoefficient M.nu omega).sub continuous_const).continuousOn) hu

/-- **The comparator's exit-time solution has a continuous representative.**  The constant field
`σ_n I` is its own symmetric part and its skew part vanishes. -/
theorem exists_isCubeRepresentative_comparator (M : ABKModel d) (n : ℤ) (y : Vec d)
    {i : Fin d} {u : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n u
      (linearAxisDatum i)) :
    ∃ uRep : Vec d → ℝ, IsCubeRepresentative y n u uRep := by
  have : NeZero d := Algsuperdiff.Section3.Provider.Orlicz.neZero_of_model M
  have hskew : matTranspose (0 : Mat d) = -(0 : Mat d) := by
    ext p q
    simp [matTranspose]
  exact exists_isCubeRepresentative_of_isDirichletSolutionAt M.shellPrefix.dimension
    (Algsuperdiff.Section3.Provider.Orlicz.sigmaBar_pos M n)
    (fun _ => DivergenceFormProcess.Decay.symmPart_scalar_add_skew (add_zero _).symm hskew)
    continuousOn_const hu

/-! ## 2. The truncated family at every scale -/

/-- **The truncated exit-time solutions and their representatives, at every truncation
scale.**  Solvability is unconditional for the rough field, and the representative comes from
the structure of `a_L`; neither depends on the sample, on an event, or on the relative position
of the truncation scale and the cube scale. -/
theorem exists_cutoffSolutionFamily_linearAxisDatum (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) (i : Fin d) :
    ∃ (u : ℤ → H1Function (cubeSetAt y n)) (uRep : ℤ → Vec d → ℝ),
      (∀ L : ℤ, IsDirichletSolutionAt
        ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField) y n (u L)
          (linearAxisDatum i)) ∧
        ∀ L : ℤ, IsCubeRepresentative y n (u L) (uRep L) := by
  choose u hu using fun L : ℤ =>
    exists_isDirichletSolutionAt_cutoff M L n y omega
      (holderSeminormBoundOn_linearAxisDatum i y n)
  choose uRep huRep using fun L : ℤ =>
    exists_isCubeRepresentative_cutoff M L n y omega (hu L)
  exact ⟨u, uRep, hu, huRep⟩

end

end Algsuperdiff.Section5.Provider
