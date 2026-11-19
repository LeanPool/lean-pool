/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianLocalizationLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianChapmanKolmogorov

/-!
# Ginibre Hamiltonian localization limit

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreDrivenHamiltonianBoundedStop_eventually_eq_cap`.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenHamiltonianBoundedStop_eventually_eq_cap {n : ℕ} (hn : 0 < n)
    (α : ℝ) (N : GinibreContinuousNoise n) (z : Configuration n) (hz : CollisionFree z)
    (hLife : ginibreDrivenMaximalLifetime n α N.val z = ⊤) (T : ℝ≥0) :
    ∃ C : ℝ, ∀ R > C, ginibreHamiltonian n z ≤ R ∧
      ginibreDrivenHamiltonianBoundedStop n α N.val z R T=T := by
  have hT : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N.val z := by simp [hLife]
  let H : ℝ≥0 → ℝ := fun t => ginibreHamiltonian n
    (ginibreDrivenMaximalValue n α N.val z (min t T))
  have hH : Continuous H := ginibreDrivenHamiltonianPrefix_continuous T hT
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hH.continuousOn
  refine ⟨|ginibreHamiltonian n z|+|C|+1,?_⟩
  intro R hR
  have hzR : ginibreHamiltonian n z ≤ R := by linarith [le_abs_self (ginibreHamiltonian n z),
                                                abs_nonneg C]
  refine ⟨hzR,?_⟩
  have hnot : ¬ginibreDrivenHamiltonianFirstLevel n α N.val z R ≤ (T : ℝ≥0∞) := by
    intro hh
    rcases (ginibreDrivenHamiltonianFirstLevel_le_iff_lifetime hn α N.val N.val.continuous
        N.property z hz R hzR T).mp hh with hbad | ⟨_, t, ht, hvalue⟩
    · simp [hLife] at hbad
    · have hb := hC t ht
      change ‖H t‖ ≤ C at hb
      simp only [H, min_eq_left ht.2, Real.norm_eq_abs] at hb
      have hup := (le_abs_self _).trans hb
      linarith [le_abs_self C, abs_nonneg (ginibreHamiltonian n z)]
  unfold ginibreDrivenHamiltonianBoundedStop
  rw [min_eq_left (le_of_lt (lt_of_not_ge hnot)), ENNReal.toNNReal_coe]

end
end GinibrePoincare
