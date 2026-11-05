/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExitLaw
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExpectedExitTime
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.StoppingLtTop
public import LeanPool.MarkovProcess.MarkovProcess.Path.ExitTimeShift

/-!
# StoppedDirichlet

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The remaining exit time of a continuous process

Let `Q` be the continuous-path process of a conservative Feller kernel semigroup, let `U` be an
open set, let `tau` be the first exit time from `U`, and let
  `w y = E_y[tau]`

be the expected exit time from the starting point `y`.  This file proves the identity that
governs the stopped process at a deterministic horizon `t`:
  `E_x[w(X_{t and tau})] + E_x[t and tau] = w x`   (`lintegral_expectedExitTime_add`),

for every starting point `x` of `U`.  In words: the expected time still to be spent in `U` after
the stopped time is the total expected time minus the expected time already spent.

The proof uses no generator and no domain membership.  It rests on three facts.  Pathwise, the
exit time splits as the truncated exit time plus, on the survival event `{t < tau}`, the exit time
of the path shifted by `t` (`exitTime_eq_exitTimeTrunc_add`).  The simple Markov property at the
deterministic time `t`, restricted to the survival event -- which belongs to the canonical
filtration at time `t` -- converts the shifted term into `w(X_t)`
(`lintegral_indicator_survivalEvent_shift`).  Finally, on the complementary event the stopped
path sits on the frontier of `U`, where `w` vanishes because a path starting outside `U` leaves
immediately (`ae_expectedExitTime_eval_exitTimeTrunc`).

The same restricted Markov property in Bochner form (`setIntegral_shift`) is recorded here; it is
what the harmonic identities of the companion file consume.

Two shapes of the main identity are given: the additive one in `ℝ≥0∞`, which needs no finiteness,
and the subtractive and real-valued ones under a finite expected exit time from the starting
point.
-/

namespace DivergenceFormProcess.StoppedDirichlet

open MeasureTheory ProbabilityTheory
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal

noncomputable section

section PathLevel

variable {alpha : Type*} [MetricSpace alpha]

/-- The survival event: the paths that are still in `U` at time `t`. -/
def survivalEvent (U : Set alpha) (t : NNReal) : Set (ContinuousPath alpha) :=
  {omega : ContinuousPath alpha | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega}

/-- The position of a path at its exit time from `U`, read at the time `(exitTime U).toNNReal`. -/
def exitPosition (U : Set alpha) (omega : ContinuousPath alpha) : alpha :=
  omega ((ContinuousPath.exitTime U omega).toNNReal)

/-- On the survival event the exit time truncated at `t` is `t`. -/
theorem exitTimeTrunc_of_mem_survivalEvent {U : Set alpha} {t : NNReal}
    {omega : ContinuousPath alpha} (h : omega ∈ survivalEvent U t) :
    ContinuousPath.exitTimeTrunc U t omega = t := by
  have hcoe : ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ≥0∞) = (t : ℝ≥0∞) := by
    rw [ContinuousPath.coe_exitTimeTrunc_ennreal, min_eq_right (le_of_lt h)]
  exact_mod_cast hcoe

/-- Off the survival event the exit time truncated at `t` is the exit time itself. -/
theorem exitTimeTrunc_of_notMem_survivalEvent {U : Set alpha} {t : NNReal}
    {omega : ContinuousPath alpha} (h : omega ∉ survivalEvent U t) :
    ContinuousPath.exitTimeTrunc U t omega = (ContinuousPath.exitTime U omega).toNNReal := by
  have hle : ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞) := not_lt.mp h
  have hcoe : ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ≥0∞) =
      ContinuousPath.exitTime U omega := by
    rw [ContinuousPath.coe_exitTimeTrunc_ennreal, min_eq_left hle]
  rw [← ENNReal.toNNReal_coe (ContinuousPath.exitTimeTrunc U t omega), hcoe]

/-- Off the survival event the stopped position is the exit position. -/
theorem eval_exitTimeTrunc_of_notMem_survivalEvent {U : Set alpha} {t : NNReal}
    {omega : ContinuousPath alpha} (h : omega ∉ survivalEvent U t) :
    omega (ContinuousPath.exitTimeTrunc U t omega) = exitPosition U omega := by
  rw [exitTimeTrunc_of_notMem_survivalEvent h]
  rfl

/-- On the survival event, and at a finite exit time, shifting by `t` does not move the exit
position. -/
theorem exitPosition_shift {U : Set alpha} {t : NNReal} {omega : ContinuousPath alpha}
    (hmem : omega ∈ survivalEvent U t) (hfin : ContinuousPath.exitTime U omega ≠ ⊤) :
    exitPosition U (ContinuousPath.shift t omega) = exitPosition U omega := by
  have hadd := ContinuousPath.exitTime_shift_add U omega t hmem
  have hafin : ContinuousPath.exitTime U (ContinuousPath.shift t omega) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hadd
    exact hfin hadd.symm
  have htoNNReal : (ContinuousPath.exitTime U omega).toNNReal =
      (ContinuousPath.exitTime U (ContinuousPath.shift t omega)).toNNReal + t := by
    rw [← hadd, ENNReal.toNNReal_add hafin ENNReal.coe_ne_top, ENNReal.toNNReal_coe]
  rw [exitPosition, exitPosition, htoNNReal, ContinuousPath.shift_apply, add_comm]

/-- **The pathwise splitting of the exit time at a deterministic horizon.**  The exit time is the
truncated exit time plus, on the survival event, the exit time of the shifted path. -/
theorem exitTime_eq_exitTimeTrunc_add (U : Set alpha) (t : NNReal)
    (omega : ContinuousPath alpha) :
    ContinuousPath.exitTime U omega =
      ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ≥0∞) +
        Set.indicator (survivalEvent U t)
          (fun omega ↦ ContinuousPath.exitTime U (ContinuousPath.shift t omega)) omega := by
  by_cases ht : (t : ℝ≥0∞) < ContinuousPath.exitTime U omega
  · have hmem : omega ∈ survivalEvent U t := ht
    rw [Set.indicator_of_mem hmem, ContinuousPath.coe_exitTimeTrunc_ennreal,
      min_eq_right ht.le, add_comm]
    exact (ContinuousPath.exitTime_shift_add U omega t ht).symm
  · have hmem : omega ∉ survivalEvent U t := ht
    rw [Set.indicator_of_notMem hmem, add_zero, ContinuousPath.coe_exitTimeTrunc_ennreal,
      min_eq_left (not_lt.mp ht)]

variable [MeasurableSpace alpha] [BorelSpace alpha]

/-- The exit position is a Borel function on path space. -/
theorem measurable_exitPosition {U : Set alpha} (hU : IsOpen U) :
    Measurable (exitPosition (alpha := alpha) U) :=
  ContinuousPath.measurable_eval_untopD_exitTimeTop U hU

/-- The survival event belongs to the canonical filtration at its own time. -/
theorem measurableSet_survivalEvent_canonicalFiltration {U : Set alpha} (hU : IsOpen U)
    (t : NNReal) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha) t] (survivalEvent U t) :=
  ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration U hU t

/-- The survival event is a Borel set of path space. -/
theorem measurableSet_survivalEvent {U : Set alpha} (hU : IsOpen U) (t : NNReal) :
    MeasurableSet (survivalEvent (alpha := alpha) U t) :=
  ContinuousPath.measurableSet_lt_exitTime U hU t

end PathLevel

section Process

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- The expected exit time from `U` of the continuous process started at `y`. -/
def expectedExitTime (U : Set alpha) (y : alpha) : ℝ≥0∞ :=
  ∫⁻ omega, ContinuousPath.exitTime U omega ∂(IsConservative.continuousProcess P hP y)

/-- The expected exit time is a Borel function of the starting point. -/
theorem measurable_expectedExitTime {U : Set alpha} (hU : IsOpen U) :
    Measurable (expectedExitTime P hP U) :=
  (ContinuousPath.measurable_exitTime U hU).lintegral_kernel

/-- A process started outside `U` leaves `U` at once, so the expected exit time vanishes off
`U`. -/
theorem expectedExitTime_eq_zero_of_notMem (hK : P.KolmogorovRegular hP)
    {U : Set alpha} {y : alpha} (hy : y ∉ U) : expectedExitTime P hP U y = 0 := by
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [IsConservative.ae_eval_zero_eq hP hK y] with omega h0
  refine le_antisymm ?_ zero_le
  simpa using ContinuousPath.exitTime_le_of_notMem U omega 0 (h0 ▸ hy)

/-- Almost surely from a starting point of `U`, the expected exit time read at the stopped
position is the expected exit time read at time `t` on the survival event, and zero elsewhere:
off the survival event the stopped path sits on the frontier of `U`. -/
theorem ae_expectedExitTime_eval_exitTimeTrunc (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) (t : NNReal) {x : alpha} (hx : x ∈ U) :
    ∀ᵐ omega ∂(IsConservative.continuousProcess P hP x),
      expectedExitTime P hP U (omega (ContinuousPath.exitTimeTrunc U t omega)) =
        Set.indicator (survivalEvent U t)
          (fun omega ↦ expectedExitTime P hP U (omega t)) omega := by
  filter_upwards [IsConservative.ae_eval_zero_eq hP hK x] with omega h0
  by_cases ht : (t : ℝ≥0∞) < ContinuousPath.exitTime U omega
  · have hmem : omega ∈ survivalEvent U t := ht
    rw [Set.indicator_of_mem hmem, exitTimeTrunc_of_mem_survivalEvent hmem]
  · have hmem : omega ∉ survivalEvent U t := ht
    have hle : ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞) := not_lt.mp ht
    have hfin : ContinuousPath.exitTime U omega ≠ ⊤ := (hle.trans_lt ENNReal.coe_lt_top).ne
    rw [Set.indicator_of_notMem hmem, exitTimeTrunc_of_notMem_survivalEvent hmem]
    refine expectedExitTime_eq_zero_of_notMem P hP hK ?_
    have hfront := ContinuousPath.coordinate_exitTime_mem_frontier U hU omega (h0 ▸ hx) hfin
    rw [hU.frontier_eq] at hfront
    exact hfront.2

/-- The expected stopped time never exceeds the horizon, hence is finite. -/
theorem lintegral_exitTimeTrunc_ne_top (U : Set alpha) (t : NNReal) (x : alpha) :
    (∫⁻ omega, ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ≥0∞)
      ∂(IsConservative.continuousProcess P hP x)) ≠ ⊤ := by
  have hle : (∫⁻ omega, ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ≥0∞)
      ∂(IsConservative.continuousProcess P hP x)) ≤ (t : ℝ≥0∞) := by
    calc (∫⁻ omega, ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ≥0∞)
        ∂(IsConservative.continuousProcess P hP x)) ≤
        ∫⁻ _omega : ContinuousPath alpha, (t : ℝ≥0∞)
          ∂(IsConservative.continuousProcess P hP x) := by
          refine lintegral_mono fun omega ↦ ?_
          exact ENNReal.coe_le_coe.mpr (ContinuousPath.exitTimeTrunc_le U t omega)
      _ ≤ (t : ℝ≥0∞) := by
          rw [lintegral_const, measure_univ, mul_one]
  exact (hle.trans_lt ENNReal.coe_lt_top).ne

variable [LocallyCompactSpace alpha]

/-- **The restricted Markov property at a deterministic time, in extended nonnegative form.**  On
the survival event, which belongs to the canonical filtration at time `t`, the expectation of a
nonnegative observable of the shifted path is its expectation under the process restarted from
the position at time `t`. -/
theorem lintegral_indicator_survivalEvent_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) (t : NNReal)
    {F : ContinuousPath alpha → ℝ≥0∞} (hF : Measurable F) (x : alpha) :
    ∫⁻ omega, Set.indicator (survivalEvent U t)
        (fun omega ↦ F (ContinuousPath.shift t omega)) omega
        ∂(IsConservative.continuousProcess P hP x) =
      ∫⁻ omega, Set.indicator (survivalEvent U t)
        (fun omega ↦ ∫⁻ eta, F eta ∂(IsConservative.continuousProcess P hP (omega t))) omega
        ∂(IsConservative.continuousProcess P hP x) := by
  have hS := measurableSet_survivalEvent_canonicalFiltration hU t
  have hkey := StoppingTime.lintegral_mul_indicator_of_restrict_map
    (m := ContinuousPath.canonicalFiltration (alpha := alpha) t)
    (IsConservative.continuousProcess P hP x)
    (Kernel.comap (IsConservative.continuousProcess P hP)
      (ContinuousPath.coordinateProcess (alpha := alpha) t)
      (ContinuousPath.measurable_coordinateProcess t))
    (ContinuousPath.shift t) (ContinuousPath.measurable_shift_fixed t)
    ((ContinuousPath.canonicalFiltration (alpha := alpha)).le t)
    (survivalEvent U t) hS
    (fun A hA ↦ hFeller.continuousProcess_restrict_map_shift P hP hK x t _ (hA.inter hS))
    F hF (fun _ ↦ 1) measurable_const
  simpa only [one_mul, Kernel.comap_apply, ContinuousPath.coordinateProcess_apply] using hkey

/-- **The restricted Markov property at a deterministic time, in Bochner form.**  Over an event of
the canonical filtration at time `t`, the integral of a bounded observable of the shifted path is
the integral of its expectation under the process restarted from the position at time `t`. -/
theorem setIntegral_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (t : NNReal) (x : alpha) (F : ContinuousPath alpha → ℝ)
    (hF : StronglyMeasurable F) (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C)
    (A : Set (ContinuousPath alpha))
    (hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha) t] A) :
    ∫ omega in A, F (ContinuousPath.shift t omega)
        ∂(IsConservative.continuousProcess P hP x) =
      ∫ omega in A, (∫ eta, F eta ∂(IsConservative.continuousProcess P hP (omega t)))
        ∂(IsConservative.continuousProcess P hP x) := by
  have hm := (ContinuousPath.canonicalFiltration (alpha := alpha)).le t
  have hint : Integrable (fun omega ↦ F (ContinuousPath.shift t omega))
      (IsConservative.continuousProcess P hP x) :=
    Integrable.of_bound
      ((hF.comp_measurable (ContinuousPath.measurable_shift_fixed t)).aestronglyMeasurable) C
      (Filter.Eventually.of_forall fun omega ↦ hFC _)
  have hcond := hFeller.continuousProcess_condExp_shift P hP hK x t F hF C hFC
  calc ∫ omega in A, F (ContinuousPath.shift t omega)
        ∂(IsConservative.continuousProcess P hP x)
      = ∫ omega in A, ((IsConservative.continuousProcess P hP x)[
          fun omega ↦ F (ContinuousPath.shift t omega)|
            ContinuousPath.canonicalFiltration (alpha := alpha) t]) omega
        ∂(IsConservative.continuousProcess P hP x) :=
        (MeasureTheory.setIntegral_condExp hm hint hA).symm
    _ = ∫ omega in A, (∫ eta, F eta ∂(IsConservative.continuousProcess P hP (omega t)))
        ∂(IsConservative.continuousProcess P hP x) :=
        integral_congr_ae (ae_restrict_of_ae hcond)

/-- **The remaining exit time at a deterministic horizon.**  From a starting point of the open set
`U`, the expected exit time read at the stopped position, plus the expected stopped time, is the
expected exit time from the starting point. -/
theorem lintegral_expectedExitTime_add
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) (t : NNReal) {x : alpha} (hx : x ∈ U) :
    (∫⁻ omega, expectedExitTime P hP U (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x)) +
      (∫⁻ omega, ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ≥0∞)
        ∂(IsConservative.continuousProcess P hP x)) =
      expectedExitTime P hP U x := by
  have hsplit : expectedExitTime P hP U x =
      ∫⁻ omega, (((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ≥0∞) +
        Set.indicator (survivalEvent U t)
          (fun omega ↦ ContinuousPath.exitTime U (ContinuousPath.shift t omega)) omega)
        ∂(IsConservative.continuousProcess P hP x) :=
    lintegral_congr fun omega ↦ exitTime_eq_exitTimeTrunc_add U t omega
  rw [hsplit, lintegral_add_left (measurable_coe_exitTimeTrunc U hU t), add_comm]
  congr 1
  rw [lintegral_indicator_survivalEvent_shift P hP hFeller hK hU t
    (ContinuousPath.measurable_exitTime U hU) x]
  exact lintegral_congr_ae (ae_expectedExitTime_eval_exitTimeTrunc P hP hK hU t hx)

/-- Under a finite expected exit time, the expected exit time read at the stopped position is
finite. -/
theorem lintegral_expectedExitTime_ne_top
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) (t : NNReal) {x : alpha} (hx : x ∈ U)
    (hwfin : expectedExitTime P hP U x ≠ ⊤) :
    (∫⁻ omega, expectedExitTime P hP U (omega (ContinuousPath.exitTimeTrunc U t omega))
      ∂(IsConservative.continuousProcess P hP x)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top hwfin ?_
  rw [← lintegral_expectedExitTime_add P hP hFeller hK hU t hx]
  exact le_self_add

/-- **The remaining exit time, in real form.**  Under a finite expected exit time from the starting
point, the real expected exit time read at the stopped position, plus the real expected stopped
time, is the real expected exit time. -/
theorem integral_expectedExitTime_add
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) (t : NNReal) {x : alpha} (hx : x ∈ U)
    (hwfin : expectedExitTime P hP U x ≠ ⊤) :
    (∫ omega, (expectedExitTime P hP U
          (omega (ContinuousPath.exitTimeTrunc U t omega))).toReal
        ∂(IsConservative.continuousProcess P hP x)) +
      (∫ omega, ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ)
        ∂(IsConservative.continuousProcess P hP x)) =
      (expectedExitTime P hP U x).toReal := by
  have hmeas : Measurable fun omega : ContinuousPath alpha ↦
      expectedExitTime P hP U (omega (ContinuousPath.exitTimeTrunc U t omega)) :=
    (measurable_expectedExitTime P hP hU).comp
      (ContinuousPath.measurable_eval_stoppingTime_borel _
        (ContinuousPath.isStoppingTime_exitTimeTrunc U hU t))
  have ha := lintegral_expectedExitTime_ne_top P hP hFeller hK hU t hx hwfin
  have hb := lintegral_exitTimeTrunc_ne_top P hP U t x
  have hfirst : (∫ omega, (expectedExitTime P hP U
        (omega (ContinuousPath.exitTimeTrunc U t omega))).toReal
      ∂(IsConservative.continuousProcess P hP x)) =
      (∫⁻ omega, expectedExitTime P hP U (omega (ContinuousPath.exitTimeTrunc U t omega))
        ∂(IsConservative.continuousProcess P hP x)).toReal :=
    integral_toReal hmeas.aemeasurable (ae_lt_top hmeas ha)
  have hsecond : (∫ omega, ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ)
      ∂(IsConservative.continuousProcess P hP x)) =
      (∫⁻ omega, ((ContinuousPath.exitTimeTrunc U t omega : NNReal) : ℝ≥0∞)
        ∂(IsConservative.continuousProcess P hP x)).toReal := by
    rw [lintegral_exitTimeTrunc_eq hP U hU t x, ENNReal.toReal_ofReal]
    exact integral_nonneg fun omega ↦ NNReal.zero_le_coe
  rw [hfirst, hsecond, ← ENNReal.toReal_add ha hb,
    lintegral_expectedExitTime_add P hP hFeller hK hU t hx]

/-- The real expected exit time read at the stopped position is integrable. -/
theorem integrable_expectedExitTime_eval_exitTimeTrunc
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) (t : NNReal) {x : alpha} (hx : x ∈ U)
    (hwfin : expectedExitTime P hP U x ≠ ⊤) :
    Integrable (fun omega ↦ (expectedExitTime P hP U
        (omega (ContinuousPath.exitTimeTrunc U t omega))).toReal)
      (IsConservative.continuousProcess P hP x) := by
  have hmeas : Measurable fun omega : ContinuousPath alpha ↦
      expectedExitTime P hP U (omega (ContinuousPath.exitTimeTrunc U t omega)) :=
    (measurable_expectedExitTime P hP hU).comp
      (ContinuousPath.measurable_eval_stoppingTime_borel _
        (ContinuousPath.isStoppingTime_exitTimeTrunc U hU t))
  exact integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable
    (lintegral_expectedExitTime_ne_top P hP hFeller hK hU t hx hwfin)

end Process

end

end DivergenceFormProcess.StoppedDirichlet
