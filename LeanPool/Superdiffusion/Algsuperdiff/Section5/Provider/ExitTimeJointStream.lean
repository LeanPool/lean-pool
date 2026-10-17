/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeCutoffLimit
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeJointCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamCube

/-!
# ExitTimeJointStream

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-cell exit-time joint of the full stream field

The one-step Laplace estimate consumes, at each cell, the expected exit time of the process from
that cell, identified with the continuous representative of the solution of the exit-time datum
problem `-∇·a∇w = 1` on the cell.  The coefficient field `a` of that problem must be the field the
process itself carries.  For the process of one realization of the stream field that is the full
field `ν I + k`, not a truncation of it: the truncated fields and the full field have different
Dirichlet solutions, and only their limit as the truncation scale grows is the full field's
solution.

This file states the per-cell joint for the full field and discharges it on the one-point
compactification.  The analytic side of the cell is the exit-time datum problem for the full
field, together with the truncated solutions and the comparator solution that the good-cube
estimates compare it with; the process side is the exit-time identity of the stream crux chain,
composed with the identification of the exit-time function with the continuous representative.

## Main definitions

* `IsCubeStreamExitTimeData` — the analytic data of one cell for the full field.
* `HasCubeStreamExitTimeData` — its existential form.
* `IsCubeExitTimeSolutionDataStream` — the per-cell joint on a general carrier.

## Main results

* `abs_isCubeRepresentative_stream_le_of_mem_qEvent` — the two-sided bound for the full field's
  exit-time function on a good cube.
* `exit_time_exponential_moment_on_good_cube_stream` — the exit-time bounds and the normalized
  exponential moment, from the joint.
* `isCubeExitTimeSolutionDataStream_onePoint_of_mem_qEvent` — the joint on the one-point
  compactification, from the analytic data and the inputs of the stream crux chain.

## References

* ABK26, the localized exit-time problem of Section 5.2 and the one-step Laplace estimate of
  Section 5.3.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form
open DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup MeasureTheory Set
open scoped ENNReal NNReal Topology ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ## 1. The analytic data of one cell -/

/-- **The exit-time analytic data of one cell for the full stream field.**  The solution `w` of
the exit-time datum problem for the full field `ν I + k` on `y + □_n`, its continuous
representative `wRep`, and the two families the good-cube estimates compare it with: the
solutions of the same problem for the truncated fields at every scale, with their representatives,
and the solution of the constant-coefficient comparator problem with its representative. -/
def IsCubeStreamExitTimeData (M : ABKModel d) (n : ℤ) (omega : Field.FullSample d M.gamma)
    (i : Fin d) (y : Vec d) (w : H1Function (cubeSetAt y n)) (wRep : Vec d → ℝ) : Prop :=
  IsDirichletSolutionAt (Field.streamCoefficient M.nu omega) y n w (linearAxisDatum i) ∧
    IsCubeRepresentative y n w wRep ∧
    ∃ (u : ℤ → H1Function (cubeSetAt y n)) (uRep : ℤ → Vec d → ℝ)
      (v : H1Function (cubeSetAt y n)) (vRep : Vec d → ℝ),
      (∀ L : ℤ, IsDirichletSolutionAt
        ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField) y n (u L)
          (linearAxisDatum i)) ∧
        (∀ L : ℤ, IsCubeRepresentative y n (u L) (uRep L)) ∧
        IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v
          (linearAxisDatum i) ∧
        IsCubeRepresentative y n v vRep

/-- **The cell carries exit-time analytic data for the full stream field.** -/
def HasCubeStreamExitTimeData (M : ABKModel d) (n : ℤ) (omega : Field.FullSample d M.gamma)
    (i : Fin d) (y : Vec d) : Prop :=
  ∃ (w : H1Function (cubeSetAt y n)) (wRep : Vec d → ℝ),
    IsCubeStreamExitTimeData M n omega i y w wRep

/-! ## 2. The per-cell joint -/

/-- **The solution data of one cell for the full stream field, read on a general carrier.**  At
the centre `y` and cube scale `n`: a solution of the exit-time datum problem for the full field
with its continuous representative and the comparison data, together with the identification of
the expected exit time from `U` at the reading of a point of the cube with the representative.
The set `U` is required to be open and to carry no starting point other than the readings of
points of the cube. -/
def IsCubeExitTimeSolutionDataStream (M : ABKModel d) (n : ℤ)
    (omega : Field.FullSample d M.gamma) (alpha : Type)
    [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (U : Set alpha) (emb : Vec d → alpha) (i : Fin d) (y : Vec d) : Prop :=
  ∃ (w : H1Function (cubeSetAt y n)) (wRep : Vec d → ℝ),
    IsCubeStreamExitTimeData M n omega i y w wRep ∧
      IsOpen U ∧
      (∀ z ∈ U, ∃ x ∈ cubeSetAt y n, emb x = z) ∧
      ∀ x ∈ cubeSetAt y n, expectedExitTime P hP U (emb x) = ENNReal.ofReal (wRep x)

/-! ## 3. The two-sided bound on a good cube -/

/-- **The full field's exit-time function is bounded on a good cube.**  The truncated solutions
obey the two-sided bound `|u_L| ≤ C T(3^n)` on the cube at every truncation scale above the cube
scale, and both halves survive the `L²` limit, so the same bound holds for the continuous
representative of the full field's solution. -/
theorem abs_isCubeRepresentative_stream_le_of_mem_qEvent (d : ℕ) (hdim : 2 ≤ d) (cstar : ℝ)
    (hcstar : 0 < cstar) (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 Cev C : ℝ, 0 < gamma0 ∧ 0 < Cev ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      ∀ n : ℤ,
      ∀ (y : Vec d) (i : Fin d),
      ∀ omega : Field.FullSample d M.gamma, omega.1 ∈ qEvent M Creg Cev n y ep →
      ∀ (w : H1Function (cubeSetAt y n)) (wRep : Vec d → ℝ),
        IsCubeStreamExitTimeData M n omega i y w wRep →
        ∀ z ∈ cubeSetAt y n, |wRep z| ≤ C * exitTimeScale M n := by
  obtain ⟨gamma0, Cev, C, hgamma0, hCev, hC, hmain⟩ :=
    abs_isCubeRepresentative_le_of_mem_qEvent d hdim cstar hcstar Creg hCreg
  refine ⟨gamma0, Cev, C, hgamma0, hCev, hC, ?_⟩
  intro M hcs hgam ep hep n y i omega homega w wRep hdata z hz
  obtain ⟨hw, hwRep, u, uRep, v, vRep, hu, huRep, hv, hvRep⟩ := hdata
  have hlim := tendsto_l2_exitTime_cutoff M omega y n i hu hw
  have hcut : ∀ L : ℤ, n ≤ L → ∀ x ∈ cubeSetAt y n,
      |uRep L x| ≤ C * exitTimeScale M n := fun L hL x hx =>
    hmain M hcs hgam ep hep n y i omega.1 homega L hL (u L) v (uRep L) vRep (hu L) hv
      (huRep L) hvRep x hx
  have hupperEv : ∀ᶠ L : ℤ in Filter.atTop,
      ∀ x ∈ cubeSetAt y n, uRep L x ≤ C * exitTimeScale M n :=
    Filter.eventually_atTop.2 ⟨n, fun L hL x hx => (abs_le.1 (hcut L hL x hx)).2⟩
  have hlowerEv : ∀ᶠ L : ℤ in Filter.atTop,
      ∀ x ∈ cubeSetAt y n, -(C * exitTimeScale M n) ≤ uRep L x :=
    Filter.eventually_atTop.2 ⟨n, fun L hL x hx => (abs_le.1 (hcut L hL x hx)).1⟩
  exact abs_le.2
    ⟨ge_on_open_subset_of_tendsto_l2 (isOpen_cubeSetAt y n) subset_rfl huRep hwRep hlowerEv
        hlim hz,
      le_on_open_subset_of_tendsto_l2 (isOpen_cubeSetAt y n) subset_rfl huRep hwRep hupperEv
        hlim hz⟩

/-! ## 4. The exit-time bounds and the exponential moment, from the joint -/

/-- **The exponential moment of the exit time from a good cube, for the full stream field.**  The
process enters only through the joint: the expected exit time from `U` at the reading of a point
of the cube is the continuous representative of the full field's exit-time function there.  On
the good cube event the expected exit time is then at most `C T(3^n)` from every starting point,
at least `C⁻¹ T(3^n)` from every point of the inner cube once the accuracy is below the returned
threshold, and the exponential moment of `τ(U)/(C T(3^n))` is at most `2`. -/
theorem exit_time_exponential_moment_on_good_cube_stream (d : ℕ) (hdim : 2 ≤ d) (cstar : ℝ)
    (hcstar : 0 < cstar) (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 Cev C c : ℝ, 0 < gamma0 ∧ 0 < Cev ∧ 0 < C ∧ 0 < c ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) →
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
        (∀ z ∈ U, expectedExitTime P hP U z ≤ ENNReal.ofReal (C * exitTimeScale M n)) ∧
          (ep ≤ c → ∀ x ∈ cubeSetAt y (n - 1),
            ENNReal.ofReal (C⁻¹ * exitTimeScale M n) ≤ expectedExitTime P hP U (emb x)) ∧
          ∀ z : alpha,
            ∫⁻ eta, ContinuousPath.exponentialStoppingWeight
                (C * exitTimeScale M n)⁻¹ (ContinuousPath.exitTime U) eta
              ∂(IsConservative.continuousProcess P hP z) ≤ 2 := by
  obtain ⟨gamma0, Cev, C0, c0, hgamma0, hCev, hC0, hc0, hmain⟩ :=
    exit_time_bounds_on_good_cube_stream d hdim cstar hcstar Creg hCreg
  have hlogpos : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  refine ⟨gamma0, Cev, max C0 (38 * C0 / Real.log (19 / 10)), c0, hgamma0, hCev,
    lt_of_lt_of_le hC0 (le_max_left _ _), hc0, ?_⟩
  intro M hcs hgam ep hep n y i omega homega alpha _ _ _ _ _ _ _ P hP hFeller hKreg U emb
    hjoint
  obtain ⟨w, wRep, hdata, hU, hUemb, hident⟩ := hjoint
  obtain ⟨hw, hwRep, u, uRep, v, vRep, hu, huRep, hv, hvRep⟩ := hdata
  set C : ℝ := max C0 (38 * C0 / Real.log (19 / 10)) with hC_def
  have hCpos : 0 < C := lt_of_lt_of_le hC0 (le_max_left _ _)
  have hTpos : 0 < exitTimeScale M n := exitTimeScale_pos M n
  obtain ⟨hupper, hlower⟩ :=
    hmain M hcs hgam ep hep n y i omega homega u uRep v vRep w wRep hu huRep hv hvRep hw
      hwRep
  have hC0C : C0 ≤ C := le_max_left _ _
  have hCle : 38 * C0 / Real.log (19 / 10) ≤ C := le_max_right _ _
  have hkey : 38 * C0 ≤ C * Real.log (19 / 10) := by
    rw [div_le_iff₀ hlogpos] at hCle
    linarith only [hCle]
  have hU0 : ∀ z ∈ U, expectedExitTime P hP U z ≤
      ENNReal.ofReal (C0 * exitTimeScale M n) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hUemb z hz
    rw [hident x hx]
    exact ENNReal.ofReal_le_ofReal (hupper x hx)
  have hsubcube : cubeSetAt y (n - 1) ⊆ cubeSetAt y n := by
    simpa using cubeSetAt_subset_cubeSetAt_succ y (n - 1)
  refine ⟨fun z hz => le_trans (hU0 z hz) (ENNReal.ofReal_le_ofReal ?_), ?_, fun z => ?_⟩
  · exact mul_le_mul_of_nonneg_right hC0C hTpos.le
  · intro hepc x hx
    rw [hident x (hsubcube hx)]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hlower hepc x hx))
    have hinv : C⁻¹ ≤ C0⁻¹ := by
      rw [inv_le_inv₀ hCpos hC0]
      exact hC0C
    exact mul_le_mul_of_nonneg_right hinv hTpos.le
  · refine lintegral_exponentialStoppingWeight_exitTime_le_two_of_le_on P hP hFeller hKreg
      hU (le_of_lt (mul_pos hC0 hTpos)) hU0 (by positivity) ?_ z
    rw [inv_mul_eq_div, div_le_iff₀ (mul_pos hCpos hTpos)]
    nlinarith only [hkey, hTpos, hCpos, hlogpos]

/-! ## 5. The joint on the one-point compactification -/

section OnePoint

variable [NeZero d]

/-- **The compactified reading of the per-cell joint, from the stream crux chain.**  The chain's
exit-time identity for the process of the stream field's split-skew resolvent equals the
exit-time function of the cube, and the exit-time function of the cube is the continuous
representative of the full field's exit-time solution wherever that representative is bounded.
No small-contrast datum and no compatibility of the field with a truncation are used. -/
theorem isCubeExitTimeSolutionDataStream_onePoint_of_chain (M : ABKModel d) (n : ℤ)
    (omega : Field.FullSample d M.gamma) (i : Fin d) (y : Vec d)
    (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : (Field.streamWholeSpaceAnalyticData M omega).KernelResolventIdentifiesAnalyticMinimal R)
    (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        ((Field.streamWholeSpaceC0BarrierData M omega).resolvent).toContractiveResolvent.operator
          mu g)
    (w : H1Function (cubeSetAt y n)) (wRep : Vec d → ℝ)
    (hdata : IsCubeStreamExitTimeData M n omega i y w wRep)
    {Mb : ℝ} (hMb : 0 ≤ Mb) (hb : ∀ z ∈ cubeSetAt y n, |wRep z| ≤ Mb) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsCubeExitTimeSolutionDataStream M n omega (OnePoint (Vec d))
      R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
      ((↑) : Vec d → OnePoint (Vec d)) i y := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  refine ⟨w, wRep, hdata, OnePoint.isOpen_image_coe.mpr (isOpen_cubeSetAt y n), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · intro x hx
    obtain ⟨w0, hval, hw0⟩ :=
      exists_isScalarForcedWeakSolution_of_isDirichletSolutionAt hdata.1
    have hae : wRep =ᵐ[volumeMeasureOn (cubeSetAt y n)] w0.toH1Function.toFun := by
      filter_upwards [hdata.2.1.1] with z hz
      rw [hz, hval z]
    have hchain :=
      WholeSpaceAnalyticData.lintegral_exitTime_eq_cubeSetAtExitFunction_stream
        (M := M) (omega := omega) R hreg hcons hid hT y n hx
    have hpde := (Field.streamWholeSpaceAnalyticData M
      omega).cubeSetAtExitFunction_coe_eq_of_isScalarForcedWeakSolution y n w0 hw0 hae
        hdata.2.1.2 hMb hb hx
    change ∫⁻ eta, MarkovProcess.ContinuousPath.exitTime
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) eta
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (x : OnePoint (Vec d))) = _
    rw [hchain, hpde]

/-- **The compactified per-cell joint on a good cube.**  The uniform bound the identification of
the exit-time function needs is the two-sided good-cube bound, so on the good cube event the
analytic data of the cell alone produce the joint. -/
theorem isCubeExitTimeSolutionDataStream_onePoint_of_mem_qEvent (d : ℕ) [NeZero d]
    (hdim : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 Cev : ℝ, 0 < gamma0 ∧ 0 < Cev ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      ∀ n : ℤ,
      ∀ (y : Vec d) (i : Fin d),
      ∀ omega : Field.FullSample d M.gamma, omega.1 ∈ qEvent M Creg Cev n y ep →
        HasCubeStreamExitTimeData M n omega i y →
      ∀ (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular),
        R.kernelSemigroup.IsConservative →
        (Field.streamWholeSpaceAnalyticData M omega).KernelResolventIdentifiesAnalyticMinimal R →
        (∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
          R.toContractiveResolvent.operator mu g =
            ((Field.streamWholeSpaceC0BarrierData M
              omega).resolvent).toContractiveResolvent.operator mu g) →
        letI := hreg.metricSpace
        letI := hreg.completeSpace
        IsCubeExitTimeSolutionDataStream M n omega (OnePoint (Vec d))
          R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
          ((↑) : Vec d → OnePoint (Vec d)) i y := by
  obtain ⟨gamma0, Cev, C, hgamma0, hCev, hC, hbound⟩ :=
    abs_isCubeRepresentative_stream_le_of_mem_qEvent d hdim cstar hcstar Creg hCreg
  refine ⟨gamma0, Cev, hgamma0, hCev, ?_⟩
  intro M hcs hgam ep hep n y i omega homega hdata R hreg hcons hid hT
  obtain ⟨w, wRep, hw⟩ := hdata
  exact isCubeExitTimeSolutionDataStream_onePoint_of_chain M n omega i y R hreg hcons hid hT
    w wRep hw (mul_nonneg hC.le (exitTimeScale_pos M n).le)
    (hbound M hcs hgam ep hep n y i omega homega w wRep hw)

end OnePoint

end

end Algsuperdiff.Section5.Provider
