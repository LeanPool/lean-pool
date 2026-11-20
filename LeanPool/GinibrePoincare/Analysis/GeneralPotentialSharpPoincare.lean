/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialSharpPoincare.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialQuotientNonnegativeClosure
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialQuotientVariance

/-!
# Poincaré inequality for general potentials

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `rhoSubharmonic_potential_smooth_poincare`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Nonquadratic Poincaré inequality for every symmetric compactly supported C¹
observable, derived from the actual weighted projection and phase geometry. -/
theorem rhoSubharmonic_potential_compact_poincare {d : ℕ} (hn : 0 < d + 1)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition (d + 1) V < ⊤) (ρ : ℝ) (hρ : 0 < ρ)
    (hsub : IsRhoSubharmonicPotential ρ V) (f : Configuration (d + 1) → ℝ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hs : IsSymmetric f) :
    potentialVariance (d+1) V f ≤
      (1 / (ρ * ((d+1 : ℕ) : ℝ))) * potentialGradientEnergy (d+1) V f := by
  let hmem := potentialSmoothCompact_memLp (d+1) hn hV.continuous hfin f hf.continuous hc
  have hp := potentialHolomorphicQuotient_centered_mem_positive hn hV hrot hfin f hmem hs
  have hv := potentialVariance_le_two_quotient_residual_of_positive hn hV hrot hfin f hmem hp
  have he := potentialHolomorphicQuotientProjection_centered_compact_gap hn ρ hρ hV hrot hsub hfin f
      hf hc
  dsimp only at he
  calc
    potentialVariance (d+1) V f ≤ _ := hv
    _ ≤ 2 * ((1 / (2 * ((d+1 : ℕ) : ℝ) * ρ)) * potentialGradientEnergy (d+1) V f) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

theorem rhoSubharmonic_potential_smooth_poincare {n : ℕ} (hn : 0 < n)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (ρ : ℝ) (hρ : 0 < ρ)
    (hsub : IsRhoSubharmonicPotential ρ V) (f : Configuration n → ℝ)
    (hf : IsSmoothCompactSymmetric f) :
    potentialVariance n V f ≤ (1 / (ρ * (n : ℝ))) * potentialGradientEnergy n V f := by
  cases n with
  | zero => omega
  | succ d =>
    exact rhoSubharmonic_potential_compact_poincare hn hV hrot hfin ρ hρ hsub f
      (hf.1.of_le (by norm_num)) hf.2.1 hf.2.2

end
end GinibrePoincare
