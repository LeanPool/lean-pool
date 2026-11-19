/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterSquaredIntegral.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalTestItoIntegral
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterSquaredNoiseSums

/-! Actual CIR radial martingale compensation with its genuinely constructed
original Brownian-integral representation, on canonical Hamiltonian stops. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_local_center_CIR_integral_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) :
    let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t ≤ T, TendstoInMeasure P (fun k ω => ∑ i,
        brownianUniformLeftSum (B i)
          (fun s ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*(ginibreCenterSquared n) (X s ω))*
            ginibreCenterRadialDirection n e (X s ω) i) t (k+1) ω) atTop (J t)) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
        (ginibreCenterSquared n) (X t ω)-(ginibreCenterSquared n) z = J t ω+
          ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
            ((1 : ℝ)-(ginibreCenterSquared n) (X s.toNNReal ω))) := by
  classical
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  have hf : ContDiffOn ℝ 2 ((ginibreCenterSquared n) : Configuration n → ℝ) {x | CollisionFree x} :=
    ((contDiff_ginibreCenterSquared n).of_le
      (by exact WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffOn
  obtain ⟨J, hJM, hJC, hJL, hJ0, hLimit, hIto, hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_integral_exists (by omega) α z hz B P hB hind R hR
        T (ginibreCenterSquared n) hf
  have hCF (s : ℝ≥0) (ω : Ω) : CollisionFree (X s ω) :=
    (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T s ω).1
  have hSum (t : ℝ≥0) : ginibreConfigurationBrownianGradientSum n B α X (ginibreCenterSquared n) t =
      (fun k ω => ∑ i, brownianUniformLeftSum (B i)
        (fun s ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*(ginibreCenterSquared n) (X s ω))*
          ginibreCenterRadialDirection n e (X s ω) i) t (k+1) ω) := by
    funext k ω
    exact ginibreConfigurationBrownianGradientSum_centerSquared hn B α α.coe_nonneg X hCF e t k ω
  refine ⟨J, hJM, hJC, hJL, hJ0,?_,?_⟩
  · intro t ht
    rw [← hSum t]
    exact hLimit t ht
  · filter_upwards [hIto] with ω hω
    intro t ht
    have hh := hω t ht
    have hg : (fun s : ℝ => ginibreRealPaperSpeedGenerator n α (ginibreCenterSquared n) (X
        s.toNNReal ω)) =
        (fun s => (4*(α : ℝ)/(n : ℝ))*((1 : ℝ)-(ginibreCenterSquared n) (X s.toNNReal ω))) := by
      funext s
      exact ginibreRealPaperSpeedGenerator_centerSquared hn α _ (hCF _ ω)
    rw [hg] at hh
    exact hh

end
end GinibrePoincare
