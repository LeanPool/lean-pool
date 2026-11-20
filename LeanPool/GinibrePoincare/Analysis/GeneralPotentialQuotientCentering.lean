/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialQuotientCentering.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialQuotientProjection
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialQuotientCompactGap
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialCenteringDecomposition
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialVandermondeGauge
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPartitionVandermonde

/-!
# General potential quotient centering

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialHolomorphicQuotientProjection_centered_orthogonal_constant`,
`potentialHolomorphicQuotientProjection_centered_compact_gap`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- The actual normalized gauge of a constant is the actual weighted Vandermonde. -/
theorem potentialPiVandermondeL2Equiv_constant (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) (c : ℂ)
        :
    potentialPiVandermondeL2Equiv n hn hV hfin (potentialConstantL2 n hn hV hfin c) =
      ((Real.sqrt (potentialPartition n V).toReal : ℂ)⁻¹ * c) •
        partitionWeightedVandermondeL2 n hn hV hrot hfin := by
  apply Lp.ext
  have hc := (configurationVolume_absolutelyContinuous_potentialMeasure n hn hV hfin).ae_eq
    (potentialConstantL2_coeFn n hn hV hfin c)
  filter_upwards [potentialVandermondeL2_coeFn_public n hn hV hfin
      (potentialConstantL2 n hn hV hfin c), hc,
    partitionWeightedVandermondeL2_coeFn n hn hV hrot hfin,
    Lp.coeFn_smul ((Real.sqrt (potentialPartition n V).toReal : ℂ)⁻¹ * c)
      (partitionWeightedVandermondeL2 n hn hV hrot hfin)] with z hg hc hw hs
  change (potentialVandermondeL2 n hn hV hfin (potentialConstantL2 n hn hV hfin c)) z = _
  rw [hg, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hc, hw]
  unfold potentialVandermondeMultiplier piPotentialHalfWeight
  rw [potentialPiHalfWeight_eq]
  ring

/-- The genuine nonquadratic quotient projection fixes actual constants. -/
theorem potentialHolomorphicQuotientProjection_constant {d : ℕ} (hn : 0 < d + 1)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition (d + 1) V < ⊤) (c : ℂ) :
    potentialHolomorphicQuotientProjection hn hV hfin
      (potentialConstantL2 (d+1) hn hV.continuous hfin c) =
      potentialConstantL2 (d+1) hn hV.continuous hfin c := by
  apply (potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin).injective
  rw [potentialHolomorphicQuotientProjection_gauge,
    potentialPiVandermondeL2Equiv_constant (d+1) hn hV.continuous hrot hfin c,
    map_smul, partitionWeightedVandermondeL2_fixed]

theorem potentialHolomorphicQuotientProjection_centered_orthogonal_constant {d : ℕ}
    (hn : 0 < d + 1) {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition (d + 1) V < ⊤) (f : Configuration (d + 1) → ℝ)
    (hf : MemLp f 2 (potentialMeasure (d + 1) V)) (c : ℂ) :
    inner ℂ (potentialConstantL2 (d+1) hn hV.continuous hfin c)
      (potentialHolomorphicQuotientProjection hn hV hfin
        (potentialCenteredL2 (d+1) hn hV.continuous hfin f hf)) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left,
    potentialHolomorphicQuotientProjection_adjoint,
    potentialHolomorphicQuotientProjection_constant hn hV hrot hfin]
  exact potentialCenteredL2_orthogonal_constant (d+1) hn hV.continuous hfin f hf c

theorem potentialHolomorphicQuotientProjection_centered_residual {d : ℕ}
    (hn : 0 < d + 1) {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition (d + 1) V < ⊤) (f : Configuration (d + 1) → ℝ)
    (hf : MemLp f 2 (potentialMeasure (d + 1) V)) :
    potentialCenteredL2 (d+1) hn hV.continuous hfin f hf -
      potentialHolomorphicQuotientProjection hn hV hfin
        (potentialCenteredL2 (d+1) hn hV.continuous hfin f hf) =
    hf.ofReal.toLp (fun z => (f z : ℂ)) -
      potentialHolomorphicQuotientProjection hn hV hfin (hf.ofReal.toLp (fun z => (f z : ℂ))) := by
  rw [potentialCenteredL2_eq_sub_constant, map_sub,
    potentialHolomorphicQuotientProjection_constant hn hV hrot hfin]
  abel

theorem potentialHolomorphicQuotientProjection_centered_compact_gap {d : ℕ}
    (hn : 0 < d + 1) (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hsub : IsRhoSubharmonicPotential ρ V)
    (hfin : potentialPartition (d + 1) V < ⊤) (f : Configuration (d + 1) → ℝ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let hmem := potentialSmoothCompact_memLp (d+1) hn hV.continuous hfin f hf.continuous hc
    let u := potentialCenteredL2 (d+1) hn hV.continuous hfin f hmem
    ‖u - potentialHolomorphicQuotientProjection hn hV hfin u‖ ^ 2 ≤
      (1 / (2 * ((d+1 : ℕ) : ℝ) * ρ)) * potentialGradientEnergy (d+1) V f := by
  dsimp only
  rw [potentialHolomorphicQuotientProjection_centered_residual hn hV hrot hfin]
  exact potentialHolomorphicQuotientProjection_compact_gap hn ρ hρ hV hsub hfin f hf hc

end
end GinibrePoincare
