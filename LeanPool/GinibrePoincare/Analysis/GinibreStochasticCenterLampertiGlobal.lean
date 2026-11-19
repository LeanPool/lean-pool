/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterLampertiGlobal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLampertiIto
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterHittingExhaustion

/-! The actual radial Brownian motion is identified globally by Lamperti's
formula, using the constructed exhausting Hamiltonian localizations. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_global_center_Lamperti_identity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβC : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (hβLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k + 1) ω) atTop (β t)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (ginibreSquareRootCenter n) (ginibreBrownianMaximalProcess n α z B t
          ω)-(ginibreSquareRootCenter n) z =
        Real.sqrt (2*(α : ℝ)/(n : ℝ))*β t ω+
          ∫ s in (0 : ℝ)..t, ginibreLampertiCenterDrift n α
            (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)) := by
  have hR (k : ℕ) : ginibreHamiltonian n z ≤ ginibreHamiltonian n z+k :=
    le_add_of_nonneg_right (Nat.cast_nonneg k)
  let X := fun k : ℕ => ginibreBrownianHamiltonianStoppedProcess n α z B (ginibreHamiltonian n z+k)
      k
  let C := fun k : ℕ => Classical.choose (ginibreHamiltonianSublevel_centerSquared_bound
    (show 0 < n by omega) (ginibreHamiltonian n z+k))
  have hC (k : ℕ) (t : ℝ≥0) (ω : Ω) : ginibreCenterSquared n (X k t ω) ≤ C k :=
    (Classical.choose_spec (ginibreHamiltonianSublevel_centerSquared_bound
      (show 0 < n by omega) (ginibreHamiltonian n z+k))).2 _
        (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B _ (hR k) k t ω)
  let θ := fun (k : ℕ) ω => min (ginibreBrownianHamiltonianBoundedStop n α z B (ginibreHamiltonian n
      z+k) k ω)
    (hittingBtwn (fun s ω => C k-ginibreCenterSquared n (X k s ω))
      {x : ℝ | C k-2/((k : ℝ)+1) ≤ ‖x‖} 0 k ω)
  have hLocal (k : ℕ) : ∀ᵐ ω ∂P, 2/((k : ℝ)+1) ≤ ginibreCenterSquared n z →
      ∀ t ≤ θ k ω, (ginibreSquareRootCenter n) (X k t ω)-(ginibreSquareRootCenter n) z =
        Real.sqrt (2*(α : ℝ)/(n : ℝ))*β t ω+
          ∫ s in (0 : ℝ)..t, ginibreLampertiCenterDrift n α (ginibreCenterSquared n (X k s.toNNReal
              ω)) := by
    by_cases hk : 2/((k : ℝ)+1) ≤ ginibreCenterSquared n z
    · have hh := ginibreBrownianMaximalProcess_local_center_Lamperti_identity hn α z hz B P hB hind
        e β hβC hβLim (ginibreHamiltonian n z+k) (hR k) k (C k) (1/((k : ℝ)+1))
        (by positivity) (by simpa [div_eq_mul_inv] using hk) (hC k)
      simpa only [X, θ, div_eq_mul_inv, one_mul] using hh.mono (fun ω hω _ => hω)
    · exact ae_of_all P (fun ω h => (hk h).elim)
  have hinit : ∀ᶠ k : ℕ in atTop, 2/((k : ℝ)+1) ≤ ginibreCenterSquared n z := by
    have hl : Tendsto (fun k : ℕ => 2/((k : ℝ)+1)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    exact (hl.eventually (gt_mem_nhds hcenter)).mono (fun k hk => hk.le)
  filter_upwards [ae_all_iff.mpr hLocal,
    ginibreBrownian_center_small_stops_exhaust_ae hn α z hz hcenter B P hB hind]
    with ω hω hExhaust
  intro t
  obtain ⟨k, hk, hkt⟩ := (hinit.and ((hExhaust t).mono (fun k hk => hk (C k) (hC k)))).exists
  have hh := hω k hk t hkt
  have hσ : t ≤ ginibreBrownianHamiltonianBoundedStop n α z B (ginibreHamiltonian n z+k) k ω :=
    hkt.trans (min_le_left _ _)
  have hXt : ginibreBrownianHamiltonianStoppedProcess n α z B (ginibreHamiltonian n z+k) k t ω =
      ginibreBrownianMaximalProcess n α z B t ω := by
    change ginibreBrownianMaximalProcess n α z B (min t _) ω = _
    rw [min_eq_left hσ]
  have hInt : (∫ s in (0 : ℝ)..t, ginibreLampertiCenterDrift n α
        (ginibreCenterSquared n (X k s.toNNReal ω))) =
      ∫ s in (0 : ℝ)..t, ginibreLampertiCenterDrift n α
        (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hst : s.toNNReal ≤ t := (Real.toNNReal_le_iff_le_coe).mpr hs.2
    change ginibreLampertiCenterDrift n α (ginibreCenterSquared n
      (ginibreBrownianMaximalProcess n α z B (min s.toNNReal _) ω)) = _
    rw [min_eq_left (hst.trans hσ)]
  change (ginibreSquareRootCenter n) (ginibreBrownianHamiltonianStoppedProcess n α z B
    (ginibreHamiltonian n z+k) k t ω)-(ginibreSquareRootCenter n) z = _ at hh
  rw [hXt, hInt] at hh
  exact hh
end
end GinibrePoincare
