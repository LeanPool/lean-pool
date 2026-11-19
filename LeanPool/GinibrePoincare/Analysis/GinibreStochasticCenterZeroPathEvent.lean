/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroPathEvent.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterGlobalNonvanishing
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalGlobalPathElement

/-! The genuine center-nonhitting event is Borel in the continuous-path space.
This permits independent random positive initial centers in canonical restarts. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The configuration paths whose coordinate sum is nonzero at every nonnegative time. -/
def ginibrePositiveCenterPaths (n : ℕ) : Set C(ℝ, Configuration n) :=
  {p | ∀ t : ℝ, 0 ≤ t → 0 < ginibreCenterSquared n (p t)}

theorem ginibrePositiveCenterPaths_measurable (n : ℕ) :
    @MeasurableSet C(ℝ, Configuration n) (borel _) (ginibrePositiveCenterPaths n) := by
  let : MeasurableSpace C(ℝ, Configuration n) := borel _
  let : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
  have he : ginibrePositiveCenterPaths n =
      ⋂ k : ℕ, {p : C(ℝ, Configuration n) | MapsTo p (Icc (0 : ℝ) k)
        {z | 0 < ginibreCenterSquared n z}} := by
    ext p
    simp only [ginibrePositiveCenterPaths, Set.mem_ofPred_eq, mem_iInter, MapsTo, mem_Icc]
    constructor
    · intro hp k t ht
      exact hp t ht.1
    · intro hp t ht
      obtain ⟨k, hk⟩ := exists_nat_ge t
      exact hp k ⟨ht, hk⟩
  rw [he]
  apply MeasurableSet.iInter
  intro k
  exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc
    (isOpen_lt continuous_const (contDiff_ginibreCenterSquared n).continuous)).measurableSet

theorem ginibreDrivenGlobalPathElement_center_nonhitting_noise_ae
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : {z : Configuration n // CollisionFree z}) (hc : 0 < ginibreCenterSquared n z.val)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ N ∂P.map (ginibreBrownianFullContinuousNoise n B α),
      ginibreDrivenGlobalPathElement α (z, N) ∈ ginibrePositiveCenterPaths n := by
  have hm := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  have hPath : @Measurable _ C(ℝ, Configuration n) _ (borel _)
      (fun N : GinibreContinuousNoise n => ginibreDrivenGlobalPathElement α (z, N)) :=
    (ginibreDrivenGlobalPathElement_measurable (by omega) α).comp measurable_prodMk_left
  rw [ae_map_iff hm.aemeasurable
    (hPath (ginibrePositiveCenterPaths_measurable n))]
  filter_upwards [ginibreBrownian_center_global_nonvanishing hn α z.val z.property hc B P hB hind,
    ginibreBrownianMaximalLifetime_top_ae (by omega) α z.val z.property B P hB hind]
    with ω hnonzero htop
  intro t ht
  unfold ginibreBrownianMaximalLifetime at htop
  simp only [ginibreDrivenGlobalPathElement, dite_eq_left htop,
    ContinuousMap.coe_mk]
  exact lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (hnonzero t.toNNReal))

end
end GinibrePoincare
