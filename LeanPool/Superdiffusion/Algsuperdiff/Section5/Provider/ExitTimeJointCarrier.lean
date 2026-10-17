/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OneStepLaplaceComposer
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDEIdentificationCube

/-!
# ExitTimeJointCarrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Two inputs of the per-cell exit-time reading

The one-step Laplace estimate consumes, at each cell, two Dirichlet solutions,
their continuous representatives, and the identification of the expected exit
time from the cell with the representative of the rough-field solution.  Two
ingredients of that reading are recorded here: the rough-field solution of the
exit-time datum solves the constant forcing in the zero-trace class, with the
`H¹₀` witness of the Dirichlet condition; and on the good cube event its
continuous representative is bounded uniformly on the cube.

## Main results

* `exists_isScalarForcedWeakSolution_of_isDirichletSolutionAt` — the scalar
  forced weak solution of the exit-time datum.
* `abs_isCubeRepresentative_le_of_mem_qEvent` — the uniform bound on the cube
  supplied by the good cube event.

## References

* ABK26, the localized exit-time problem of Section 5.2 and the one-step
  Laplace estimate of Section 5.3.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form
open DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup MeasureTheory Set
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ## 2. The compactified reading, discharged from the chain -/

variable [NeZero d]

omit [NeZero d] in
/-- The rough-field solution of the exit-time datum solves the constant forcing
in the zero-trace class, with the `H¹₀` witness of the Dirichlet condition. -/
theorem exists_isScalarForcedWeakSolution_of_isDirichletSolutionAt
    {a : CoeffField d} {y : Vec d} {n : ℤ} {u : H1Function (cubeSetAt y n)} {i : Fin d}
    (hu : IsDirichletSolutionAt a y n u (linearAxisDatum i)) :
    ∃ w : H10Function (cubeSetAt y n),
      (∀ x, u.toFun x = w.toH1Function.toFun x) ∧
        IsScalarForcedWeakSolution a (cubeSetAt y n) (fun _ => (1 : ℝ))
          w.toH1Function := by
  obtain ⟨⟨w, hval, hgrad⟩, hweak⟩ := (isDirichletSolutionAt_linearAxisDatum_iff i).1 hu
  have : IsFiniteMeasure (volumeMeasureOn (cubeSetAt y n)) :=
    (isOpenBoundedConvexDomain_cubeSetAt y n).isFiniteMeasure_restrict_volume
  refine ⟨w, hval, memLp_const (1 : ℝ), fun phi => ?_⟩
  have hphi := hweak phi
  simp only [← hgrad] at hphi ⊢
  rw [hphi]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (one_mul _).symm)

/-! ## 4. The uniform bound on the cube, and the family of good sites -/

omit [NeZero d] in
/-- **A uniform bound for the representative of the rough-field solution on a
good cube.**  On the good cube event the exit-time homogenization estimate
supplies one continuous representative bounded by `C T(3^n)` at every point of
the cube; by uniqueness of continuous representatives the same bound holds for
any representative of the same solution.  This is the bound the identification
of the exit-time function consumes. -/
theorem abs_isCubeRepresentative_le_of_mem_qEvent (d : ℕ) (hdim : 2 ≤ d) (cstar : ℝ)
    (hcstar : 0 < cstar) (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 Cev C : ℝ, 0 < gamma0 ∧ 0 < Cev ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      ∀ n : ℤ,
      ∀ (y : Vec d) (i : Fin d),
      ∀ omega ∈ qEvent M Creg Cev n y ep,
      ∀ m : ℤ, n ≤ m →
      ∀ (u v : H1Function (cubeSetAt y n)) (uRep vRep : Vec d → ℝ),
        IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) y n u
            (linearAxisDatum i) →
        IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v
            (linearAxisDatum i) →
        IsCubeRepresentative y n u uRep →
        IsCubeRepresentative y n v vRep →
        ∀ z ∈ cubeSetAt y n, |uRep z| ≤ C * exitTimeScale M n := by
  obtain ⟨gamma0, Cev, C, c, hgamma0, hCev, hC, -, hmain⟩ :=
    exit_time_homogenization_on_good_cube d hdim cstar hcstar Creg hCreg
  refine ⟨gamma0, Cev, C, hgamma0, hCev, hC, ?_⟩
  intro M hcs hgam ep hep n y i omega homega m hm u v uRep vRep hu hv huRep hvRep z hz
  obtain ⟨-, uRep', huRep', -, hsup, -⟩ :=
    hmain M hcs hgam ep hep n y i omega homega m hm u v vRep hu hv hvRep
  rw [isCubeRepresentative_unique huRep huRep' hz]
  exact hsup z hz

end

end Algsuperdiff.Section5.Provider
