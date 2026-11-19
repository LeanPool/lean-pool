/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroLampertiIncrementGlobal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroLampertiIncrementLocal
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalizationExhaustion

/-! Genuine center Lamperti increments on every fixed strictly positive-start
interval, including paths starting with zero center. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_center_Lamperti_positive_start_fixed
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβShift : ∀ a r, TendstoInMeasure P (fun k => brownianUnitShiftedUniformSum B
      (fun u ω => ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B u ω))
      a r (k + 1)) atTop (fun ω => β (a + r) ω - β a ω))
    (a r : ℝ≥0) (ha : 0 < a) :
    ∀ᵐ ω ∂P,
      ginibreSquareRootCenter n (ginibreBrownianMaximalProcess n α z B (a+r) ω)-
        ginibreSquareRootCenter n (ginibreBrownianMaximalProcess n α z B a ω) =
        Real.sqrt (2*(α : ℝ)/(n : ℝ))*(β (a+r) ω-β a ω)+
          ∫ s in (a : ℝ)..(a+r : ℝ≥0), ginibreLampertiCenterDrift n α
            (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)) := by
  let X := fun k : ℕ => ginibreBrownianHamiltonianStoppedProcess n α z B (ginibreHamiltonian n z+k)
      k
  have hR (k : ℕ) : ginibreHamiltonian n z ≤ ginibreHamiltonian n z+k :=
    le_add_of_nonneg_right (Nat.cast_nonneg k)
  have hLocal (k : ℕ) : ∀ᵐ ω ∂P, a+r ≤ (k : ℝ≥0) →
      (a+r ≤ ginibreBrownianHamiltonianBoundedStop n α z B (ginibreHamiltonian n z+k) k ω ∧
        ∀ u ∈ Icc a (a+r), 1/((k : ℝ)+1) < ginibreCenterSquared n (X k u ω)) →
      ginibreSquareRootCenter n (X k (a+r) ω)-ginibreSquareRootCenter n (X k a ω) =
        Real.sqrt (2*(α : ℝ)/(n : ℝ))*(β (a+r) ω-β a ω)+
          ∫ s in (a : ℝ)..(a+r : ℝ≥0), ginibreLampertiCenterDrift n α
            (ginibreCenterSquared n (X k s.toNNReal ω)) := by
    by_cases hk : a+r ≤ (k : ℝ≥0)
    · exact (ginibreBrownian_center_Lamperti_positive_start_local hn α z hz B P hB hind e β hβShift
        (ginibreHamiltonian n z+k) (hR k) k a r hk (1/((k : ℝ)+1)) (by positivity)).mono
        (fun ω hω _ => hω)
    · exact ae_of_all P (fun ω hω => False.elim (hk hω))
  filter_upwards [ae_all_iff.mpr hLocal,
    ginibreBrownian_center_positive_interval_lower_bound hn α hα z hz B P hB hind,
    ginibreBrownianHamiltonianBoundedStop_exhausts_ae (by omega) α z hz B P hB hind] with ω hLocal
        hlow hex
  obtain ⟨c, hc, hclow⟩ := hlow a (a+r) ha (le_add_of_nonneg_right bot_le)
  have hsmall : ∀ᶠ k : ℕ in atTop, 1/((k : ℝ)+1) < c :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hc)
  obtain ⟨k, hk, hstop⟩ := (hsmall.and (hex (a+r))).exists
  have hXeq (u : ℝ≥0) (hu : u ≤ a+r) : X k u ω=ginibreBrownianMaximalProcess n α z B u ω := by
    change ginibreBrownianMaximalProcess n α z B (min u _) ω = _
    rw [min_eq_left (hu.trans hstop)]
  have hcap : a+r ≤ (k : ℝ≥0) := hstop.trans (ginibreDrivenHamiltonianBoundedStop_le n α _ z _ k)
  have hh := hLocal k hcap ⟨hstop, fun u hu => by rw [hXeq u hu.2]; exact hk.trans_le (hclow u hu)⟩
  rw [hXeq (a+r) le_rfl, hXeq a (le_add_of_nonneg_right bot_le)] at hh
  have hInt : (∫ s in (a : ℝ)..(a+r : ℝ≥0), ginibreLampertiCenterDrift n α
      (ginibreCenterSquared n (X k s.toNNReal ω))) =
      ∫ s in (a : ℝ)..(a+r : ℝ≥0), ginibreLampertiCenterDrift n α
        (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (show (a : ℝ) ≤ (a+r : ℝ≥0) from by exact_mod_cast (le_add_of_nonneg_right
                                                         (bot_le : 0 ≤ r)))] at hs
    dsimp only
    rw [hXeq _ ((Real.toNNReal_le_iff_le_coe).mpr hs.2)]
  rw [hInt] at hh
  exact hh

end
end GinibrePoincare
