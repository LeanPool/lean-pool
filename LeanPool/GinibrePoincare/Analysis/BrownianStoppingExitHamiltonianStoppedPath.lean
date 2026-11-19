/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitHamiltonianStoppedPath.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianLevelStopping
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitMaximalEquation
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianLevelLocalization

/-! Genuine compact Hamiltonian localization of the canonical Brownian maximal process. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The first time the Hamiltonian reaches the level `R`, truncated at the horizon `T`, for the
Ginibre path driven by the Brownian noise of the sample `ω`. -/
def ginibreBrownianHamiltonianBoundedStop {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0)
    (ω : Ω) : ℝ≥0 :=
  ginibreDrivenHamiltonianBoundedStop n α (ginibreBrownianFullContinuousNoise n B α ω).val z R T

/-- The Brownian-driven maximal Ginibre process stopped at the bounded level-`R` stopping time
`ginibreBrownianHamiltonianBoundedStop n α z B R T ω`. -/
def ginibreBrownianHamiltonianStoppedProcess {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T t : ℝ≥0)
    (ω : Ω) : Configuration n :=
  ginibreBrownianMaximalProcess n α z B (min t (ginibreBrownianHamiltonianBoundedStop n α z B R T
      ω)) ω

theorem ginibreBrownianHamiltonianBoundedStop_isStoppingTime {Ω : Type*}
    [mAmbient : MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) :
    IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (fun ω => ((ginibreBrownianHamiltonianBoundedStop n α z B R T ω : ℝ≥0) : ℝ≥0∞)) := by
  have hs := (ginibreBrownianHamiltonianFirstLevel_isStoppingTime hn α z hz B P hB R hR).min_const T
  have he : (fun ω => ((ginibreBrownianHamiltonianBoundedStop n α z B R T ω : ℝ≥0) : ℝ≥0∞)) =
      fun ω => min (ginibreBrownianHamiltonianFirstLevel n α z B R ω) (T : ℝ≥0∞) := by
    funext ω
    exact (ginibreDrivenHamiltonianBoundedStop_coe n α _ z R T).trans (min_comm _ _)
  rw [he]
  exact hs

theorem ginibreBrownianHamiltonianStoppedProcess_range {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T t : ℝ≥0) (ω : Ω) :
    ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω ∈ ginibreHamiltonianSublevel n R :=
  ginibreDrivenHamiltonianBoundedStop_range hn α _
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz R hR T t

theorem ginibreBrownianHamiltonianStoppedProcess_continuous {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) (ω : Ω) :
    Continuous (fun t => ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω) := by
  let N := ginibreBrownianFullContinuousNoise n B α ω
  let s := ginibreDrivenHamiltonianBoundedStop n α N.val z R T
  have hs := ginibreDrivenHamiltonianBoundedStop_lt_lifetime hn α N.val N.val.continuous N.property
      z hz R hR T
  have hc := (ginibreDrivenMaximalPath_segment s hs).1
  have hg : Continuous (fun t : ℝ≥0 => ((min t s : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  have hh := hc.comp_continuous hg (fun t => ⟨(min t s).coe_nonneg, by
    exact_mod_cast min_le_right t s⟩)
  simpa only [ginibreBrownianHamiltonianStoppedProcess, ginibreBrownianHamiltonianBoundedStop,
    ginibreBrownianMaximalProcess, ginibreDrivenMaximalPath, Real.toNNReal_coe, Function.comp_def,
        s, N] using hh

end
end GinibrePoincare
