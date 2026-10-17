/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ResolventExitDecomposition

/-!
# ExitTimeChaining

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Chaining bounds for exit times

A measurable choice from a countable family of open neighbourhoods gives a stopping time `sigma`
on canonical path space: after every restart, `sigma` is the exit time of the newly selected
neighbourhood.  This file defines the accumulated time and discounted weight of `N` such exits.
The strong Markov property turns a uniform one-step Laplace bound on a restart region `W` into its
`N`-th power, which bounds exit from a possibly different set `U` when the chain covers that exit.

Public declarations:

* `ContinuousPath.iteratedStoppingTime`;
* `ContinuousPath.iteratedStoppingTime_succ'`;
* `ContinuousPath.discountedStoppingWeight`;
* `ContinuousPath.iteratedStoppingWeight`;
* `ContinuousPath.iteratedStoppingWeight_eq_discountedStoppingWeight`;
* `ContinuousPath.measurable_discountedStoppingWeight_stopped`;
* `ContinuousPath.measurable_discountedStoppingWeight`;
* `ContinuousPath.measurable_iteratedStoppingWeight`;
* `IsFellerKernelSemigroup.lintegral_iteratedStoppingWeight_le`;
* `IsConservative.lintegral_exp_neg_exitTime_le_rho_pow`.

The construction does not prove a geometric covering property for any particular family of sets.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

open MarkovProcess

namespace Algsuperdiff.Process

namespace ContinuousPath

open MarkovProcess.ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The accumulated time of `n` successive applications of a path-space stopping rule, restarting
the rule after each finite stopping time. -/
noncomputable def iteratedStoppingTime (sigma : ContinuousPath alpha → ℝ≥0∞) :
    ℕ → ContinuousPath alpha → ℝ≥0∞
  | 0, _ => 0
  | n + 1, omega =>
      sigma omega + iteratedStoppingTime sigma n (shift ((sigma omega).untopD 0) omega)

/-- Tail-recursive form of the accumulated stopping time: append the next rule after the first
`n` cycles. -/
theorem iteratedStoppingTime_succ' (sigma : ContinuousPath alpha → ℝ≥0∞)
    (n : ℕ) (omega : ContinuousPath alpha) :
    iteratedStoppingTime sigma (n + 1) omega =
      iteratedStoppingTime sigma n omega +
        sigma (shift ((iteratedStoppingTime sigma n omega).untopD 0) omega) := by
  induction n generalizing omega with
  | zero =>
      change sigma omega + 0 = 0 + sigma (shift 0 omega)
      rw [add_zero, zero_add, shift_zero]
  | succ n ih =>
      by_cases htop : iteratedStoppingTime sigma (n + 1) omega = ⊤
      · rw [htop, top_add]
        let eta : ContinuousPath alpha := shift ((sigma omega).untopD 0) omega
        have htop' : sigma omega + iteratedStoppingTime sigma n eta = ⊤ := by
          simpa only [iteratedStoppingTime, eta] using htop
        calc
          iteratedStoppingTime sigma (n + 1 + 1) omega =
              sigma omega + iteratedStoppingTime sigma (n + 1) eta := rfl
          _ = sigma omega + (iteratedStoppingTime sigma n eta +
                sigma (shift ((iteratedStoppingTime sigma n eta).untopD 0) eta)) := by
              rw [ih]
          _ = (sigma omega + iteratedStoppingTime sigma n eta) +
                sigma (shift ((iteratedStoppingTime sigma n eta).untopD 0) eta) := by
              rw [add_assoc]
          _ = ⊤ := by rw [htop', top_add]
      · let eta : ContinuousPath alpha := shift ((sigma omega).untopD 0) omega
        have hdecomp : iteratedStoppingTime sigma (n + 1) omega =
            sigma omega + iteratedStoppingTime sigma n eta := rfl
        have hparts : sigma omega ≠ ⊤ ∧ iteratedStoppingTime sigma n eta ≠ ⊤ :=
          ENNReal.add_ne_top.mp (hdecomp ▸ htop)
        lift sigma omega to NNReal using hparts.1 with a ha
        lift iteratedStoppingTime sigma n eta to NNReal using hparts.2 with b hb
        have heta : eta = shift a omega := by
          dsimp only [eta]
          rw [← ha]
          rfl
        rw [heta] at hb
        have hUntopA : (a : ℝ≥0∞).untopD 0 = a := rfl
        have hUntopB : (b : ℝ≥0∞).untopD 0 = b := rfl
        have hUntopAB : ((a + b : NNReal) : ℝ≥0∞).untopD 0 = a + b := rfl
        rw [iteratedStoppingTime, ih, hdecomp, ← ha, hUntopA,
          ← hb, hUntopB, ← ENNReal.coe_add, hUntopAB]
        rw [shift_add, ENNReal.coe_add, add_assoc]

/-- The discounted finite-time weight of an extended-real time functional. -/
noncomputable def discountedStoppingWeight (lam : ℝ) (sigma : ContinuousPath alpha → ℝ≥0∞)
    (omega : ContinuousPath alpha) : ℝ≥0∞ :=
  ({omega | sigma omega < ⊤} : Set _).indicator
    (fun omega ↦ ENNReal.ofReal (Real.exp (-lam * (sigma omega).toReal))) omega

/-- The product of the discounted finite-time weights along `n` successive restarts. -/
noncomputable def iteratedStoppingWeight (lam : ℝ) (sigma : ContinuousPath alpha → ℝ≥0∞) :
    ℕ → ContinuousPath alpha → ℝ≥0∞
  | 0, _ => 1
  | n + 1, omega =>
      discountedStoppingWeight lam sigma omega *
        iteratedStoppingWeight lam sigma n (shift ((sigma omega).untopD 0) omega)

/-- The recursively defined weight is the discount at the accumulated stopping time, with value
zero when one of the successive stopping times is infinite. -/
theorem iteratedStoppingWeight_eq_discountedStoppingWeight (lam : ℝ)
    (sigma : ContinuousPath alpha → ℝ≥0∞) (n : ℕ) (omega : ContinuousPath alpha) :
    iteratedStoppingWeight lam sigma n omega =
      discountedStoppingWeight lam (iteratedStoppingTime sigma n) omega := by
  induction n generalizing omega with
  | zero => simp [iteratedStoppingWeight, iteratedStoppingTime, discountedStoppingWeight]
  | succ n ih =>
      rw [iteratedStoppingWeight, ih]
      have htime : iteratedStoppingTime sigma (n + 1) = fun eta ↦
          sigma eta + iteratedStoppingTime sigma n
            (shift ((sigma eta).untopD 0) eta) := by
        funext eta
        rw [iteratedStoppingTime]
      rw [htime]
      simp only [discountedStoppingWeight]
      by_cases hsigma : sigma omega = ⊤
      · simp [hsigma]
      · by_cases htail : iteratedStoppingTime sigma n
            (shift ((sigma omega).untopD 0) omega) = ⊤
        · simp [htail]
        · have hsMem : omega ∈ {eta | sigma eta < ⊤} :=
            WithTop.lt_top_iff_ne_top.mpr hsigma
          have htMem : shift ((sigma omega).untopD 0) omega ∈
              {eta | iteratedStoppingTime sigma n eta < ⊤} :=
            WithTop.lt_top_iff_ne_top.mpr htail
          have haddMem : omega ∈ {eta | sigma eta + iteratedStoppingTime sigma n
              (shift ((sigma eta).untopD 0) eta) < ⊤} :=
            ENNReal.add_lt_top.mpr ⟨WithTop.lt_top_iff_ne_top.mpr hsigma,
              WithTop.lt_top_iff_ne_top.mpr htail⟩
          rw [Set.indicator_of_mem hsMem, Set.indicator_of_mem htMem,
            Set.indicator_of_mem haddMem]
          rw [ENNReal.toReal_add hsigma htail]
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          ring

section Measurable

variable [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- The discounted finite-time weight of a canonical-filtration stopping time is measurable for
its stopped sigma-algebra. -/
theorem measurable_discountedStoppingWeight_stopped
    (sigma : ContinuousPath alpha → ℝ≥0∞)
    (hsigma : IsStoppingTime (canonicalFiltration (alpha := alpha)) sigma) (lam : ℝ) :
    Measurable[hsigma.measurableSpace] (discountedStoppingWeight lam sigma) := by
  exact (ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.measurable.comp
      (measurable_const.mul (ENNReal.measurable_toReal.comp hsigma.measurable)))).indicator
        (StoppingTime.measurableSet_stoppingTime_lt_top hsigma)

omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- The discounted finite-time weight of a canonical-filtration stopping time is Borel
measurable on path space. -/
theorem measurable_discountedStoppingWeight
    (sigma : ContinuousPath alpha → ℝ≥0∞)
    (hsigma : IsStoppingTime (canonicalFiltration (alpha := alpha)) sigma) (lam : ℝ) :
    Measurable (discountedStoppingWeight lam sigma) :=
  (measurable_discountedStoppingWeight_stopped sigma hsigma lam).mono
    hsigma.measurableSpace_le le_rfl

omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- The iterated discounted weight of a canonical-filtration stopping time is Borel measurable
on path space. -/
theorem measurable_iteratedStoppingWeight
    (sigma : ContinuousPath alpha → ℝ≥0∞)
    (hsigma : IsStoppingTime (canonicalFiltration (alpha := alpha)) sigma) (lam : ℝ) (n : ℕ) :
    Measurable (iteratedStoppingWeight lam sigma n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact (measurable_discountedStoppingWeight sigma hsigma lam).mul
        (ih.comp (measurable_shift_untopD_stoppingTime sigma hsigma))

end Measurable

end ContinuousPath

namespace SubMarkovKernelSemigroup

open MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- A uniform one-step discounted stopping bound compounds geometrically under strong-Markov
restarts, provided every finite restart from `U` remains in `U`. -/
theorem IsFellerKernelSemigroup.lintegral_iteratedStoppingWeight_le
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (sigma : ContinuousPath alpha → ℝ≥0∞)
    (hsigma : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha)) sigma)
    (lam : ℝ) (rho : ℝ≥0∞) (hrho : rho ≠ ⊤)
    (hsmall : ∀ y ∈ U, ∫⁻ omega, ContinuousPath.discountedStoppingWeight lam sigma omega
      ∂(IsConservative.continuousProcess P hP y) ≤ rho)
    (hstay : ∀ omega, omega 0 ∈ U → sigma omega < ⊤ →
      omega ((sigma omega).untopD 0) ∈ U)
    (n : ℕ) (x : alpha) (hx : x ∈ U) :
    ∫⁻ omega, ContinuousPath.iteratedStoppingWeight lam sigma n omega
        ∂(IsConservative.continuousProcess P hP x) ≤ rho ^ n := by
  induction n generalizing x with
  | zero => simp [ContinuousPath.iteratedStoppingWeight]
  | succ n ih =>
      let Q : Kernel alpha (ContinuousPath alpha) := IsConservative.continuousProcess P hP
      let S : Set (ContinuousPath alpha) := {omega | sigma omega < ⊤}
      let W : ContinuousPath alpha → ℝ≥0∞ :=
        ContinuousPath.discountedStoppingWeight lam sigma
      let F : ContinuousPath alpha → ℝ≥0∞ :=
        ContinuousPath.iteratedStoppingWeight lam sigma n
      have hS : MeasurableSet[hsigma.measurableSpace] S :=
        StoppingTime.measurableSet_stoppingTime_lt_top hsigma
      have hW : Measurable[hsigma.measurableSpace] W :=
        ContinuousPath.measurable_discountedStoppingWeight_stopped sigma hsigma lam
      have hF : Measurable F :=
        ContinuousPath.measurable_iteratedStoppingWeight sigma hsigma lam n
      have hRestart :
          ∫⁻ omega, W omega * S.indicator
              (fun omega ↦ F (ContinuousPath.shift ((sigma omega).untopD 0) omega)) omega ∂Q x =
            ∫⁻ omega, W omega * S.indicator
              (fun omega ↦ ∫⁻ eta, F eta ∂Q (omega ((sigma omega).untopD 0))) omega ∂Q x := by
        apply StoppingTime.lintegral_mul_indicator_of_restrict_map
          (mu := Q x)
          (kappa := Kernel.comap Q (fun omega ↦ omega ((sigma omega).untopD 0))
            (ContinuousPath.measurable_eval_untopD_stoppingTime sigma hsigma))
          (Y := fun omega ↦ ContinuousPath.shift ((sigma omega).untopD 0) omega)
          (m := hsigma.measurableSpace) (S := S) (F := F) (W := W)
        · exact ContinuousPath.measurable_shift_untopD_stoppingTime sigma hsigma
        · exact hsigma.measurableSpace_le
        · exact hS
        · intro A hA
          exact hFeller.continuousProcess_restrict_map_shift_stoppingTime_lt_top
            P hP hK x sigma hsigma A hA
        · exact hF
        · exact hW
      have hzero : ∀ᵐ omega ∂Q x, omega 0 = x :=
        IsConservative.ae_eval_zero_eq hP hK x
      have hpoint : ∀ᵐ omega ∂Q x,
          W omega * S.indicator
              (fun omega ↦ ∫⁻ eta, F eta ∂Q (omega ((sigma omega).untopD 0))) omega ≤
            W omega * rho ^ n := by
        filter_upwards [hzero] with omega homega
        by_cases hs : omega ∈ S
        · rw [Set.indicator_of_mem hs]
          exact mul_le_mul_right (ih (omega ((sigma omega).untopD 0))
            (hstay omega (homega.symm ▸ hx) hs)) _
        · rw [Set.indicator_of_notMem hs]
          simpa only [mul_zero] using (zero_le : (0 : ℝ≥0∞) ≤ W omega * rho ^ n)
      have hleft :
          (∫⁻ omega, ContinuousPath.iteratedStoppingWeight lam sigma (n + 1) omega ∂Q x) =
            ∫⁻ omega, W omega * S.indicator
              (fun omega ↦ F (ContinuousPath.shift ((sigma omega).untopD 0) omega)) omega ∂Q x := by
        refine lintegral_congr fun omega ↦ ?_
        change W omega * F (ContinuousPath.shift ((sigma omega).untopD 0) omega) = _
        by_cases hs : omega ∈ S
        · rw [Set.indicator_of_mem hs]
        · rw [Set.indicator_of_notMem hs]
          change ¬sigma omega < ⊤ at hs
          simp [W, ContinuousPath.discountedStoppingWeight, hs]
      rw [hleft, hRestart]
      calc
        (∫⁻ omega, W omega * S.indicator
            (fun omega ↦ ∫⁻ eta, F eta ∂Q (omega ((sigma omega).untopD 0))) omega ∂Q x) ≤
            ∫⁻ omega, W omega * rho ^ n ∂Q x := lintegral_mono_ae hpoint
        _ = rho ^ n * ∫⁻ omega, W omega ∂Q x := by
          rw [show (fun omega ↦ W omega * rho ^ n) = fun omega ↦ rho ^ n * W omega by
            funext omega; exact mul_comm _ _]
          exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top hrho)
        _ ≤ rho ^ n * rho := mul_le_mul_right (hsmall x hx) _
        _ = rho ^ (n + 1) := by rw [pow_succ]

/-- **Exit-time chaining bound.**  Suppose `sigma` encodes a measurable selection of a small
neighbourhood at the current state. If its discounted mass is at most `rho` throughout a restart
region `W`, finite selected exits restart in `W`, and almost every path from `x` completes `N`
selected exits no later than its exit from a possibly different set `U`, then the discounted
finite-exit mass from `U` is at most `rho ^ N`. -/
theorem IsConservative.lintegral_exp_neg_exitTime_le_rho_pow
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (W U : Set alpha) (lam : ℝ) (hlam : 0 < lam)
    (sigma : ContinuousPath alpha → ℝ≥0∞)
    (hsigma : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha)) sigma)
    (rho : ℝ≥0∞) (hrho : rho ≠ ⊤)
    (hsmall : ∀ y ∈ W, ∫⁻ omega, ContinuousPath.discountedStoppingWeight lam sigma omega
      ∂(IsConservative.continuousProcess P hP y) ≤ rho)
    (hstay : ∀ omega, omega 0 ∈ W → sigma omega < ⊤ →
      omega ((sigma omega).untopD 0) ∈ W)
    (N : ℕ) (x : alpha) (hx : x ∈ W)
    (hcover : ∀ᵐ omega ∂(IsConservative.continuousProcess P hP x),
      ContinuousPath.exitTime U omega < ⊤ →
        ContinuousPath.iteratedStoppingTime sigma N omega ≤ ContinuousPath.exitTime U omega) :
    ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal
          (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega
        ∂(IsConservative.continuousProcess P hP x) ≤ rho ^ N := by
  calc
    (∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal
          (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega
        ∂(IsConservative.continuousProcess P hP x)) ≤
        ∫⁻ omega, ContinuousPath.iteratedStoppingWeight lam sigma N omega
          ∂(IsConservative.continuousProcess P hP x) := by
      refine lintegral_mono_ae ?_
      filter_upwards [hcover] with omega hcov
      by_cases hexit : ContinuousPath.exitTime U omega < ⊤
      · have hmem : omega ∈ {omega | ContinuousPath.exitTime U omega < ⊤} := hexit
        rw [Set.indicator_of_mem hmem,
          ContinuousPath.iteratedStoppingWeight_eq_discountedStoppingWeight]
        have hchain : ContinuousPath.iteratedStoppingTime sigma N omega < ⊤ :=
          lt_of_le_of_lt (hcov hexit) hexit
        have hchainMem :
            omega ∈ {omega | ContinuousPath.iteratedStoppingTime sigma N omega < ⊤} := hchain
        rw [ContinuousPath.discountedStoppingWeight, Set.indicator_of_mem hchainMem]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hreal :
            (ContinuousPath.iteratedStoppingTime sigma N omega).toReal ≤
              (ContinuousPath.exitTime U omega).toReal :=
          ENNReal.toReal_mono (ne_of_lt hexit) (hcov hexit)
        exact mul_le_mul_of_nonpos_left hreal (neg_nonpos.mpr hlam.le)
      · have hmem : omega ∉ {omega | ContinuousPath.exitTime U omega < ⊤} := hexit
        rw [Set.indicator_of_notMem hmem]
        exact zero_le
    _ ≤ rho ^ N := IsFellerKernelSemigroup.lintegral_iteratedStoppingWeight_le P hP hFeller hK W
      sigma
      hsigma lam rho hrho hsmall hstay N x hx

end

end SubMarkovKernelSemigroup

end Algsuperdiff.Process
