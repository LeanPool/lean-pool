/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExitTimeLaplace
public import LeanPool.Superdiffusion.Algsuperdiff.Process.Trajectory.HitExitChaining

/-!
# HitExitTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The early-exit tail from composite hit-then-exit chaining

Composing the Chernoff bound of `Trajectory/ExitTimeLaplace.lean` with the geometric estimate of
`Trajectory/HitExitChaining.lean` turns the discounted chaining bound into a bound on the
probability of leaving the open set `U` before a deterministic time,

  `Q_x {τ_U ≤ t} ≤ e^{λ t} ρ ^ N`

(`IsConservative.measure_exitTime_le_le_rho_pow_hitExit`).  The hypotheses are those of the
chaining estimate, together with openness of `U`, which the Chernoff bound needs; the deterministic
horizon `t` is arbitrary, so the consumer chooses it after fixing the discount rate.

Nothing new is proved about the geometry of the hit family: the counting premise is exactly the one
of the chaining estimate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

open MarkovProcess

namespace Algsuperdiff.Process.SubMarkovKernelSemigroup

open MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- **The early-exit tail of composite hit-then-exit chaining.**  Under the hypotheses of the
chaining estimate, the probability of leaving the open set `U` by the deterministic time `t` is at
most `e^{lam t} rho ^ N`. -/
theorem IsConservative.measure_exitTime_le_le_rho_pow_hitExit
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (V V' : ℕ → Set alpha) (hVmeasurable : ∀ i, MeasurableSet (V i))
    (hDclosed : IsClosed (⋃ i, V i)) (hV'open : ∀ i, IsOpen (V' i))
    (U : Set alpha) (hU : IsOpen U)
    (lam : ℝ) (hlam : 0 < lam) (rho : ℝ≥0∞) (hrho : rho ≠ ⊤)
    (hone : ∀ i, ∀ z ∈ V i,
      ∫⁻ eta, ContinuousPath.discountedStoppingWeight lam
          (ContinuousPath.exitTime (V' i)) eta
        ∂(IsConservative.continuousProcess P hP z) ≤ rho)
    (K D N : ℕ) (x : alpha)
    (hoverlap : ∀ i, ∃ s : Finset ℕ,
      s.card ≤ K ∧ ∀ j, (V j ∩ V' i).Nonempty → j ∈ s)
    (hvisits : ∀ᵐ omega ∂(IsConservative.continuousProcess P hP x),
      ContinuousPath.exitTime U omega < ⊤ →
        ∃ s : Finset ℕ, D ≤ s.card ∧ ∀ i ∈ s,
          ∃ t : NNReal, (t : ℝ≥0∞) < ContinuousPath.exitTime U omega ∧ omega t ∈ V i)
    (hcount : N * K < D) (t : NNReal) :
    IsConservative.continuousProcess P hP x
        {omega | ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (lam * (t : ℝ))) * rho ^ N := by
  refine (hP.measure_exitTime_le_le P U hU lam hlam.le t x).trans ?_
  refine mul_le_mul_right ?_ _
  exact IsConservative.lintegral_exp_neg_exitTime_le_rho_pow_hitExit P hP hFeller hK V V' hVmeasurable
    hDclosed hV'open U lam hlam rho hrho hone K D N x hoverlap hvisits hcount

end

end Algsuperdiff.Process.SubMarkovKernelSemigroup
