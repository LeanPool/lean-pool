/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticLampertiGlobal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLampertiIto
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLampertiGenerator

/-! The actual radial Brownian motion is identified globally by Lamperti's
formula, using the constructed exhausting Hamiltonian localizations. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_global_Lamperti_identity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβC : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (hβLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k + 1) ω) atTop (β t)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ginibreSquareRootRadius (ginibreBrownianMaximalProcess n α z B t ω)-ginibreSquareRootRadius z
          =
        Real.sqrt (2*(α : ℝ)/(n : ℝ))*β t ω+
          ∫ s in (0 : ℝ)..t, ginibreLampertiRadialDrift n α
            (pairwiseRadius (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)) := by
  have hR (k : ℕ) : ginibreHamiltonian n z ≤ ginibreHamiltonian n z+k :=
    le_add_of_nonneg_right (Nat.cast_nonneg k)
  have hLocal (k : ℕ) := ginibreBrownianMaximalProcess_local_Lamperti_identity hn α z hz B P hB hind
    e β hβC hβLim (ginibreHamiltonian n z+k) (hR k) k
  filter_upwards [ae_all_iff.mpr hLocal,
    ginibreBrownianHamiltonianBoundedStop_exhausts_ae (by omega) α z hz B P hB hind]
    with ω hω hExhaust
  intro t
  obtain ⟨k, hkt⟩ := (hExhaust t).exists
  have hh := hω k t hkt
  have hXt : ginibreBrownianHamiltonianStoppedProcess n α z B (ginibreHamiltonian n z+k) k t ω =
      ginibreBrownianMaximalProcess n α z B t ω := by
    change ginibreBrownianMaximalProcess n α z B (min t _) ω = _
    rw [min_eq_left hkt]
  have hInt : (∫ s in (0 : ℝ)..t, ginibreRealPaperSpeedGenerator n α ginibreSquareRootRadius
        (ginibreBrownianHamiltonianStoppedProcess n α z B (ginibreHamiltonian n z+k) k s.toNNReal
            ω)) =
      ∫ s in (0 : ℝ)..t, ginibreLampertiRadialDrift n α
        (pairwiseRadius (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hst : s.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
      exact hs.2
    have hCF := (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B
      (ginibreHamiltonian n z+k) (hR k) k s.toNNReal ω).1
    dsimp only
    rw [ginibreRealPaperSpeedGenerator_squareRootRadius hn α _ hCF]
    change ginibreLampertiRadialDrift n α (pairwiseRadius
      (ginibreBrownianMaximalProcess n α z B (min s.toNNReal _) ω)) = _
    rw [min_eq_left (hst.trans hkt)]
  rw [hXt, hInt] at hh
  exact hh
end
end GinibrePoincare
