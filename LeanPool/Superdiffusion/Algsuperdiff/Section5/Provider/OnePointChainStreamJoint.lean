/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.EarlyExit
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeJointStream
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OnePointChainLaplace

/-!
# OnePointChainStreamJoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The one-step Laplace estimate for the full stream field

The one-step contraction of `OnePointChainLaplace` is re-derived here from the per-cell joint of
the full stream field.  Nothing about the argument changes: the contraction follows from an upper
bound on the expected exit time valid from every starting point, a lower bound on the inner cube,
the Paley--Zygmund survival probability, and the continuity of the representative.  What changes
is the analytic input, which is now the exit-time datum problem of the full field `ν I + k`
rather than of a truncation of it, and the good-cube bounds it obeys.

Because the truncation scale no longer enters the coefficient of the cell problem, the statements
below carry no truncation scale at all: one sample of the full field and one cube scale determine
the cell.

## Main results

* `one_step_laplace_on_good_cube_stream_image` — the one-step contraction at the reading of every
  point of the closed inner cube.
* `one_step_laplace_step_of_good_sites_stream_image` — the same over a finite family of good
  cells, with one discount rate and one contraction factor.
* `one_step_laplace_hone_of_good_sites_stream_image` — its padded-family form.

## References

* ABK26, the one-step Laplace estimate of Section 5.3.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support Algsuperdiff.Section5.Trace
open DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-! ## 1. The lower bound on the closed inner cube -/

section Lower

variable {d : ℕ} {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

private theorem expectedExitTime_lower_on_closedInnerCube_of_ident
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {U : Set alpha} {emb : Vec d → alpha} {y : Vec d} {n : ℤ} {wRep : Vec d → ℝ}
    (hcont : ContinuousOn wRep (cubeSetAt y n))
    (hident : ∀ x ∈ cubeSetAt y n, expectedExitTime P hP U (emb x) = ENNReal.ofReal (wRep x))
    {b : ℝ} (hb : 0 < b)
    (hlower : ∀ x ∈ cubeSetAt y (n - 1),
      ENNReal.ofReal b ≤ expectedExitTime P hP U (emb x)) :
    ∀ x ∈ closure (cubeSetAt y (n - 1)),
      ENNReal.ofReal b ≤ expectedExitTime P hP U (emb x) := by
  have hclosure : closure (cubeSetAt y (n - 1)) ⊆ cubeSetAt y n := by
    simpa only [sub_add_cancel] using closure_cubeSetAt_subset_cubeSetAt_succ y (n - 1)
  have hopen : ∀ x ∈ cubeSetAt y (n - 1), b ≤ wRep x := by
    intro x hx
    have hxOuter : x ∈ cubeSetAt y n := hclosure (subset_closure hx)
    have h := hlower x hx
    rw [hident x hxOuter] at h
    rcases (ENNReal.ofReal_le_ofReal_iff').mp h with hbu | hb0
    · exact hbu
    · exact False.elim ((not_le_of_gt hb) hb0)
  have hclosed : IsClosed
      {x | x ∈ closure (cubeSetAt y (n - 1)) ∧ b ≤ wRep x} :=
    isClosed_closure.isClosed_le continuousOn_const (hcont.mono hclosure)
  have hsub : cubeSetAt y (n - 1) ⊆
      {x | x ∈ closure (cubeSetAt y (n - 1)) ∧ b ≤ wRep x} :=
    fun x hx => ⟨subset_closure hx, hopen x hx⟩
  intro x hx
  rw [hident x (hclosure hx)]
  exact ENNReal.ofReal_le_ofReal (closure_minimal hsub hclosed hx).2

end Lower

/-! ## 2. The one-step contraction on a carrier -/

/-- **The one-step Laplace estimate on a good cube of the full stream field, read inside a
carrier.**  The cube is read in the state space of the process through a map `emb`, and `U` is
the set it is read as.  The constants of the joint exit-time estimate for the full field give a
scale-independent strict contraction at the reading of every point of the closed inner cube, at
discount rate `(C * T(3^n))⁻¹`. -/
theorem one_step_laplace_on_good_cube_stream_image (d : ℕ) (hdim : 2 ≤ d)
    (cstar : ℝ) (hcstar : 0 < cstar) (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 Cev C c : ℝ, 0 < gamma0 ∧ 0 < Cev ∧ 0 < C ∧ 0 < c ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) → ep ≤ c →
      ∀ n : ℤ,
      ∀ (y : Vec d) (i : Fin d),
      ∀ omega : Field.FullSample d M.gamma, omega.1 ∈ qEvent M Creg Cev n y ep →
      ∀ (alpha : Type) [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
        [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
        [LocallyCompactSpace alpha]
        (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative),
        P.IsFellerKernelSemigroup → P.KolmogorovRegular hP →
      ∀ (U : Set alpha) (emb : Vec d → alpha),
        IsCubeExitTimeSolutionDataStream M n omega alpha P hP U emb i y →
        oneStepLaplaceContraction (Real.toNNReal C) (Real.toNNReal C⁻¹) < 1 ∧
          ∀ x ∈ closure (cubeSetAt y (n - 1)),
            ∫⁻ eta, Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight
                (C * exitTimeScale M n)⁻¹ (ContinuousPath.exitTime U) eta
              ∂(hP.continuousProcess P (emb x)) ≤
              oneStepLaplaceContraction (Real.toNNReal C) (Real.toNNReal C⁻¹) := by
  obtain ⟨gamma0, Cev, C, c, hgamma0, hCev, hC, hc, hmain⟩ :=
    exit_time_exponential_moment_on_good_cube_stream d hdim cstar hcstar Creg hCreg
  refine ⟨gamma0, Cev, C, c, hgamma0, hCev, hC, hc, ?_⟩
  intro M hcs hgam ep hep hepc n y i omega homega alpha _ _ _ _ _ _ _ P hP hFeller hKreg
    U emb hjoint
  obtain ⟨hupper, hlower, -⟩ :=
    hmain M hcs hgam ep hep n y i omega homega alpha P hP hFeller hKreg U emb hjoint
  obtain ⟨w, wRep, hdata, hU, -, hident⟩ := hjoint
  have hCinv : 0 < C⁻¹ := inv_pos.mpr hC
  have hCup : 0 < Real.toNNReal C := Real.toNNReal_pos.mpr hC
  have hclow : 0 < Real.toNNReal C⁻¹ := Real.toNNReal_pos.mpr hCinv
  have hTreal : 0 < exitTimeScale M n := exitTimeScale_pos M n
  have hT : 0 < Real.toNNReal (exitTimeScale M n) := Real.toNNReal_pos.mpr hTreal
  have hCupCoe : ((Real.toNNReal C : ℝ≥0) : ℝ) = C := Real.coe_toNNReal C hC.le
  have hclowCoe : ((Real.toNNReal C⁻¹ : ℝ≥0) : ℝ) = C⁻¹ := Real.coe_toNNReal C⁻¹ hCinv.le
  have hTCoe : ((Real.toNNReal (exitTimeScale M n) : ℝ≥0) : ℝ) = exitTimeScale M n :=
    Real.coe_toNNReal _ hTreal.le
  have hupperAll : ∀ z : alpha, expectedExitTime P hP U z ≤
      ((Real.toNNReal C * Real.toNNReal (exitTimeScale M n) : ℝ≥0) : ℝ≥0∞) := by
    intro z
    have hz := expectedExitTime_le_of_le_on P hP hKreg hupper z
    simpa only [ENNReal.coe_mul, hCupCoe, hTCoe, ENNReal.coe_toNNReal,
      ENNReal.ofNNReal_toNNReal, ENNReal.ofReal_mul hC.le] using hz
  have hlowerClosed : ∀ z ∈ closure (cubeSetAt y (n - 1)),
      ((Real.toNNReal C⁻¹ * Real.toNNReal (exitTimeScale M n) : ℝ≥0) : ℝ≥0∞) ≤
        expectedExitTime P hP U (emb z) := by
    have hbase := expectedExitTime_lower_on_closedInnerCube_of_ident P hP hdata.2.1.2 hident
      (mul_pos hCinv hTreal) (hlower hepc)
    intro z hz
    simpa only [ENNReal.coe_mul, hclowCoe, hTCoe, ENNReal.coe_toNNReal,
      ENNReal.ofNNReal_toNNReal, ENNReal.ofReal_mul hCinv.le] using hbase z hz
  refine ⟨oneStepLaplaceContraction_lt_one hCup hclow, ?_⟩
  intro z hz
  have hsurv := survivalProbabilityConstant_le_measure_le_exitTime_on P hP hFeller hKreg
    U hU (Real.toNNReal (exitTimeScale M n)) (Real.toNNReal C) (Real.toNNReal C⁻¹) hT
    hupperAll (emb z) (hlowerClosed z hz)
  have hcontract := lintegral_discountedExitTime_le_oneStepLaplaceContraction
    P hP hU (Real.toNNReal (exitTimeScale M n)) (Real.toNNReal C) (Real.toNNReal C⁻¹)
    hT hCup (emb z) hsurv
  simpa only [hCupCoe, hTCoe] using hcontract

/-! ## 3. The collected contraction -/

/-- **The one-step estimate for the full stream field, collected over a family of good cells.**
For a finite injective family of scale-`n` lattice sites whose cells are all good at one sample
of the full field, one common discount rate `(C T(3^n))⁻¹` and one common contraction factor
serve every read cell at once. -/
theorem one_step_laplace_step_of_good_sites_stream_image (d : ℕ) (hdim : 2 ≤ d)
    (cstar : ℝ) (hcstar : 0 < cstar) (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 Cev C c : ℝ, 0 < gamma0 ∧ 0 < Cev ∧ 0 < C ∧ 0 < c ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) → ep ≤ c →
      ∀ n : ℤ,
      ∀ (omega : Field.FullSample d M.gamma) (i : Fin d) (r : ℕ)
        (sites : Fin r ↪ Section5.Percolation.Site d),
        (∀ j : Fin r,
          omega.1 ∈ qEvent M Creg Cev n (rescaledLatticePoint n (sites j)) ep) →
      ∀ (alpha : Type) [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
        [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
        [LocallyCompactSpace alpha]
        (emb : Vec d → alpha) (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative),
        P.IsFellerKernelSemigroup → P.KolmogorovRegular hP →
        (∀ j : Fin r, IsCubeExitTimeSolutionDataStream M n omega alpha P hP
          (emb '' cubeSetAt (rescaledLatticePoint n (sites j)) n) emb i
          (rescaledLatticePoint n (sites j))) →
        0 < (C * exitTimeScale M n)⁻¹ ∧
        oneStepLaplaceContraction (Real.toNNReal C) (Real.toNNReal C⁻¹) < 1 ∧
        ∀ j : Fin r, ∀ z ∈ closure (cubeSetAt (rescaleSite (n - 1) (sites j)) (n - 1)),
          ∫⁻ eta, Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight (C * exitTimeScale M n)⁻¹
              (ContinuousPath.exitTime
                (emb '' cubeSetAt (rescaleSite (n - 1) (sites j)) n)) eta
            ∂(hP.continuousProcess P (emb z)) ≤
            oneStepLaplaceContraction (Real.toNNReal C) (Real.toNNReal C⁻¹) := by
  obtain ⟨gamma0, Cev, C, c, hgamma0, hCev, hC, hc, hmain⟩ :=
    one_step_laplace_on_good_cube_stream_image d hdim cstar hcstar Creg hCreg
  refine ⟨gamma0, Cev, C, c, hgamma0, hCev, hC, hc, ?_⟩
  intro M hcs hgam ep hep hepc n omega i r sites hsites alpha _ _ _ _ _ _ _ emb P hP
    hFeller hKreg hjoint
  have hCinv : 0 < C⁻¹ := inv_pos.mpr hC
  refine ⟨inv_pos.mpr (mul_pos hC (exitTimeScale_pos M n)),
    oneStepLaplaceContraction_lt_one (Real.toNNReal_pos.mpr hC)
      (Real.toNNReal_pos.mpr hCinv), ?_⟩
  intro j
  rw [← rescaledLatticePoint_eq_rescaleSite n (sites j)]
  obtain ⟨-, hcontract⟩ :=
    hmain M hcs hgam ep hep hepc n (rescaledLatticePoint n (sites j)) i omega
      (hsites j) alpha P hP hFeller hKreg _ emb (hjoint j)
  exact hcontract

/-- **The collected estimate for the full stream field, in the padded-family form.**  The read
cells and their read enlargements are the padded families indexed by `ℕ`, which is the hypothesis
the hit-then-exit estimate consumes. -/
theorem one_step_laplace_hone_of_good_sites_stream_image (d : ℕ) (hdim : 2 ≤ d)
    (cstar : ℝ) (hcstar : 0 < cstar) (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 Cev C c : ℝ, 0 < gamma0 ∧ 0 < Cev ∧ 0 < C ∧ 0 < c ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) → ep ≤ c →
      ∀ n : ℤ,
      ∀ (omega : Field.FullSample d M.gamma) (i : Fin d) (r : ℕ)
        (sites : Fin r ↪ Section5.Percolation.Site d),
        (∀ j : Fin r,
          omega.1 ∈ qEvent M Creg Cev n (rescaledLatticePoint n (sites j)) ep) →
      ∀ (alpha : Type) [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
        [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
        [LocallyCompactSpace alpha]
        (emb : C(Vec d, alpha)) (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative),
        P.IsFellerKernelSemigroup → P.KolmogorovRegular hP →
        (∀ j : Fin r, IsCubeExitTimeSolutionDataStream M n omega alpha P hP
          (emb '' cubeSetAt (rescaledLatticePoint n (sites j)) n) emb i
          (rescaledLatticePoint n (sites j))) →
        0 < (C * exitTimeScale M n)⁻¹ ∧
        oneStepLaplaceContraction (Real.toNNReal C) (Real.toNNReal C⁻¹) < 1 ∧
        ∀ l : ℕ, ∀ z ∈ emb '' enumeratedClosedCubeFamily (n - 1) sites l,
          ∫⁻ eta, Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight (C * exitTimeScale M n)⁻¹
              (ContinuousPath.exitTime
                (emb '' enumeratedOpenEnlargementFamily (n - 1) sites l)) eta
            ∂(hP.continuousProcess P z) ≤
            oneStepLaplaceContraction (Real.toNNReal C) (Real.toNNReal C⁻¹) := by
  obtain ⟨gamma0, Cev, C, c, hgamma0, hCev, hC, hc, hmain⟩ :=
    one_step_laplace_step_of_good_sites_stream_image d hdim cstar hcstar Creg hCreg
  refine ⟨gamma0, Cev, C, c, hgamma0, hCev, hC, hc, ?_⟩
  intro M hcs hgam ep hep hepc n omega i r sites hsites alpha _ _ _ _ _ _ _ emb P hP
    hFeller hKreg hjoint
  obtain ⟨hlam, hrho, hstep⟩ :=
    hmain M hcs hgam ep hep hepc n omega i r sites hsites alpha emb P hP hFeller hKreg
      hjoint
  refine ⟨hlam, hrho, one_step_laplace_hone_of_partition_cubes_image emb P hP (n - 1) sites
    _ _ ?_⟩
  intro j z hz
  simpa only [sub_add_cancel] using hstep j z hz

end

end Algsuperdiff.Section5.Provider
