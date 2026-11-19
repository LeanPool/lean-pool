/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterHittingExhaustion.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterBeforeHitting
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterGlobalNonvanishing
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalizationExhaustion

/-! Small-center stopping cannot obstruct compact time intervals once its
threshold is below the genuine positive path minimum. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreCenterSmallHitting_ge_of_lower_bound {Ω : Type*} {n : ℕ}
    (X : ℝ≥0 → Ω → Configuration n) (C δ : ℝ) (T b : ℝ≥0) (ω : Ω)
    (hbT : b ≤ T) (hb : ∀ t ω, ginibreCenterSquared n (X t ω) ≤ C)
    (hlower : ∀ t ≤ b, δ < ginibreCenterSquared n (X t ω)) :
    b ≤ hittingBtwn (fun s ω => C-ginibreCenterSquared n (X s ω))
      {x : ℝ | C-δ ≤ ‖x‖} 0 T ω := by
  classical
  unfold hittingBtwn
  split_ifs with hh
  · apply le_csInf
    · obtain ⟨t, ht, hh⟩ := hh
      exact ⟨t, ht, hh⟩
    · intro t ht
      by_contra h
      have htb : t ≤ b := (not_le.mp h).le
      have hm : C-δ ≤ ‖C-ginibreCenterSquared n (X t ω)‖ := ht.2
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hb t ω))] at hm
      linarith [hlower t htb]
  · exact hbT

theorem ginibreBrownian_center_small_stops_exhaust_ae
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ b : ℝ≥0, ∀ᶠ k : ℕ in atTop,
      let X := ginibreBrownianHamiltonianStoppedProcess n α z B (ginibreHamiltonian n z+k) k
      ∀ C : ℝ, (∀ t ω, ginibreCenterSquared n (X t ω) ≤ C) →
        b ≤ min (ginibreBrownianHamiltonianBoundedStop n α z B (ginibreHamiltonian n z+k) k ω)
          (hittingBtwn (fun t ω => C-ginibreCenterSquared n (X t ω))
            {x : ℝ | C-2/((k : ℝ)+1) ≤ ‖x‖} 0 k ω) := by
  filter_upwards [ginibreBrownian_center_compact_positive_lower_bound hn α z hz hcenter B P hB hind,
    ginibreBrownianHamiltonianBoundedStop_exhausts_ae (by omega) α z hz B P hB hind]
    with ω hpositive hExhaust
  intro b
  obtain ⟨c, hc, hbound⟩ := hpositive b
  have hlim : Tendsto (fun k : ℕ => 2/((k : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (b : ℝ)
  filter_upwards [hExhaust b, hlim.eventually (gt_mem_nhds hc), eventually_ge_atTop k₀]
    with k hσ hδ hk
  dsimp only
  intro C hC
  refine le_min hσ ?_
  apply ginibreCenterSmallHitting_ge_of_lower_bound _ C _ k b ω
  · exact_mod_cast hk₀.trans (show (k₀ : ℝ) ≤ k by exact_mod_cast hk)
  · exact hC
  · intro t ht
    have he : ginibreBrownianHamiltonianStoppedProcess n α z B
        (ginibreHamiltonian n z+k) k t ω = ginibreBrownianMaximalProcess n α z B t ω := by
      change ginibreBrownianMaximalProcess n α z B (min t _) ω = _
      rw [min_eq_left (ht.trans hσ)]
    rw [he]
    exact hδ.trans_le (hbound t ⟨bot_le, ht⟩)

end
end GinibrePoincare
