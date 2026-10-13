/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedTruncation

/-!
# MomentBoostedChernoff

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Internal finite-family Chernoff reduction for moment-boosted tails

This module is a deterministic probability component of the `p > 2` branch
for `e.kl.bounds.large`; it is not a source-facing stream theorem.  It turns
the strengthened one-sided tail and an independently verified second moment
into the exact finite-sum truncation estimate used by the later coloring
transport.  The key tilted-tail bound is supplied by
`MomentBoostedTruncation.lean`, whose fixed base is independent of `sigma`.

The argument is a direct use of the local truncated-MGF and independent-sum A.
No generic `gammaTriangleConst` is invoked.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open HCPolySupport HCPolySupport.IndependentSums
open scoped BigOperators

noncomputable section

/-- Internal finite-family Chernoff estimate for centered unit-scale
moment-boosted variables.  The result deliberately remains at the explicit
truncation stage; cutoff optimization and coloring are separate lemmas. -/
theorem measureReal_upperTailEvent_finset_sum_le_momentBoosted
    {Omega iota : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {X : iota → Omega → ℝ} {s : Finset iota}
    {a sigma l L C2 : ℝ}
    (h_indep : iIndepFun X mu)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) mu)
    (h_sq : ∀ i ∈ s, Integrable (fun omega => |X i omega| ^ (2 : ℕ)) mu)
    (h_mean : ∀ i ∈ s, ∫ omega, X i omega ∂mu = 0)
    (h_second : ∀ i ∈ s,
      ∫ omega, |X i omega| ^ (2 : ℕ) ∂mu ≤ C2)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hX : ∀ i ∈ s, IsBigOWith mu (momentBoostedGammaSigma sigma) (X i) 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L)
    (hlL : l ≤ momentBoostedKernelCoeff sigma * L ^ (sigma - 1)) :
    mu.real (upperTailEvent (fun omega => ∑ i ∈ s, X i omega) a) ≤
      Real.exp (-l * a + (s.card : ℝ) *
        (l ^ (2 : ℕ) * (C2 / 2 + Real.exp 1 / 2 +
          (48 : ℝ) ^ (2 / sigma) / 2))) +
        (s.card : ℝ) * (momentBoostedGammaSigma sigma L)⁻¹ := by
  let v : ℝ := l ^ (2 : ℕ) *
    (C2 / 2 + Real.exp 1 / 2 + (48 : ℝ) ^ (2 / sigma) / 2)
  have hsplit :=
    measureReal_upperTailEvent_finset_sum_le_upperTruncation_add_card_mul_of_isBigOWith
      (μ := mu) (X := X) (s := s) (L := L) (a := a) hX hL
  have htrunc :
      mu.real
          (upperTailEvent
            (fun omega => ∑ i ∈ s, upperTruncation (X i) L omega) a) ≤
        Real.exp (-l * a + (s.card : ℝ) * v) := by
    refine
      upperTruncation_tail_le_exp_of_independent_momentGeneratingFunction
        (μ := mu) (X := X) (s := s) (a := a)
        (l := l) (L := L) (v := v)
        h_indep h_meas hl ?_
    intro i hi
    exact mgf_upperTruncation_le_exp_of_secondMoment_and_tail
      (mu := mu) (X := X i) (l := l) (L := L) (C2 := C2)
      (K := (48 : ℝ) ^ (2 / sigma))
      (h_meas i) (h_int i hi) (h_sq i hi) (h_mean i hi)
      (h_second i hi) hl hl1 hL
      (integral_Ioc_one_L_tail_le_momentBoosted_fixedBase
        hsigma hsigma_one (hX i hi) hl hL hlL)
  calc
    mu.real (upperTailEvent (fun omega => ∑ i ∈ s, X i omega) a) ≤
        mu.real
            (upperTailEvent
              (fun omega => ∑ i ∈ s, upperTruncation (X i) L omega) a) +
          (s.card : ℝ) * (momentBoostedGammaSigma sigma L)⁻¹ := hsplit
    _ ≤ Real.exp (-l * a + (s.card : ℝ) * v) +
          (s.card : ℝ) * (momentBoostedGammaSigma sigma L)⁻¹ :=
      add_le_add htrunc le_rfl
    _ = Real.exp (-l * a + (s.card : ℝ) *
        (l ^ (2 : ℕ) * (C2 / 2 + Real.exp 1 / 2 +
          (48 : ℝ) ^ (2 / sigma) / 2))) +
        (s.card : ℝ) * (momentBoostedGammaSigma sigma L)⁻¹ := by
      rfl

end

end Algsuperdiff.Section3.Provider.Stream
