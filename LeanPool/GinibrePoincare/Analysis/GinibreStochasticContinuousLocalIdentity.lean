/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticContinuousLocalIdentity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRestrictedIto

/-! Genuine continuous local identities follow simultaneously from fixed-time identities. -/

@[expose] public section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreContinuous_identity_until_of_rational (f g : ℝ≥0 → ℝ)
    (hf : Continuous f) (hg : Continuous g) (θ : ℝ≥0)
    (hRat : ∀ q : ℚ, (q : ℝ).toNNReal ≤ θ → f (q : ℝ).toNNReal=g (q : ℝ).toNNReal) :
    ∀ t ≤ θ, f t=g t := by
  classical
  intro t ht
  by_cases hzero : t=0
  · subst t
    simpa using hRat 0 (by simp)
  have htpos : (0 : ℝ)<t := by exact_mod_cast (pos_iff_ne_zero.mpr hzero)
  have hq : ∀ k : ℕ, ∃ q : ℚ,
      max 0 ((t : ℝ)-1/((k : ℝ)+1))<(q : ℝ) ∧ (q : ℝ)<t := by
    intro k
    apply exists_rat_btwn
    apply max_lt htpos
    have he : (0 : ℝ)<1/((k : ℝ)+1) := by positivity
    linarith
  choose q hq using hq
  have hqpos (k : ℕ) : (0 : ℝ)≤q k :=
    ((le_max_left 0 ((t : ℝ)-1/((k : ℝ)+1))).trans_lt (hq k).1).le
  have hseq : Tendsto (fun k => (q k : ℝ).toNNReal) atTop (𝓝 t) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun k => dist_nonneg) _ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    intro k
    rw [NNReal.dist_eq, Real.coe_toNNReal _ (hqpos k), abs_of_nonpos (sub_nonpos.mpr (hq k).2.le)]
    have hh := le_max_right 0 ((t : ℝ)-1/((k : ℝ)+1))
    linarith [(hq k).1]
  apply (isClosed_eq hf hg).mem_of_tendsto hseq
  apply Filter.Eventually.of_forall
  intro k
  apply hRat
  have hh : (q k : ℝ).toNNReal ≤ t := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hqpos k)]
    exact (hq k).2.le
  exact hh.trans ht

theorem ginibre_ae_continuous_identity_until {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g : ℝ≥0 → Ω → ℝ) (θ : Ω → ℝ≥0)
    (hf : ∀ᵐ ω ∂P, Continuous (fun t => f t ω))
    (hg : ∀ᵐ ω ∂P, Continuous (fun t => g t ω))
    (hFixed : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, t ≤ θ ω → f t ω=g t ω) :
    ∀ᵐ ω ∂P, ∀ t ≤ θ ω, f t ω=g t ω := by
  have hRat : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ).toNNReal≤θ ω →
      f (q : ℝ).toNNReal ω=g (q : ℝ).toNNReal ω :=
    ae_all_iff.mpr (fun q => hFixed (q : ℝ).toNNReal)
  filter_upwards [hf, hg, hRat] with ω hf hg hRat
  exact ginibreContinuous_identity_until_of_rational (fun t => f t ω) (fun t => g t ω) hf hg (θ ω)
      hRat
end
end GinibrePoincare
