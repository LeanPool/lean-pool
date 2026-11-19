/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitHamiltonianNonexplosion.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianActualBound
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalGlobal

/-! Genuine stopped martingale decompositions imply infinite actual canonical lifetime.
The decomposition input is the precise Itô identity, rather than an exit estimate. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalLifetime_top_ae_of_stopped_martingales
    {Ω : Type*} [mAmbient : MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hIto : ∀ T : ℝ≥0, ∀ R : ℝ, ginibreHamiltonian n z < R → ∃ N : ℝ≥0 → Ω → ℝ,
      Martingale N (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ᵐ ω ∂P, Continuous (fun t => N t ω)) ∧ (N 0 =ᵐ[P] 0) ∧
      (fun ω => ginibreHamiltonian n (ginibreBrownianHamiltonianStoppedProcess n α z B R T T ω))
          =ᵐ[P]
        (fun ω => ginibreHamiltonian n z + N (ginibreBrownianHamiltonianBoundedStop n α z B R T ω) ω
            +
          ∫ s in (0 : ℝ)..(ginibreBrownianHamiltonianBoundedStop n α z B R T ω : ℝ),
            ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n)
              (ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal s) ω))) :
    ∀ᵐ ω ∂P, ginibreBrownianMaximalLifetime n α z B ω = ⊤ := by
  have hHlower := ginibreHamiltonian_bounded_below hn z hz
  have hNull (T : ℝ≥0) : P {ω | ginibreBrownianMaximalLifetime n α z B ω ≤ (T : ℝ≥0∞)} = 0 := by
    let C := ginibreHamiltonian n z + ginibreHamiltonianLowerBoundConstant n + 4*α*(T : ℝ)
    have hC : 0 ≤ C := by
      dsimp [C]
      have ht : 0 ≤ 4*α*(T : ℝ) := by positivity
      linarith
    have hBound (m : ℕ) :
        P.real {ω | ginibreBrownianMaximalLifetime n α z B ω ≤ (T : ℝ≥0∞)} ≤ C/((m : ℝ)+1) := by
      let R := ginibreHamiltonian n z + (m : ℝ) + 1
      have hR : ginibreHamiltonian n z < R := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) m]
      have hRL : -ginibreHamiltonianLowerBoundConstant n < R := lt_of_le_of_lt hHlower hR
      obtain ⟨N, hN, hNc, hN0, hID⟩ := hIto T R hR
      have hb := ginibreBrownianMaximalLifetime_probability_bound_of_martingale hn α hα z hz B P hB
        R hR.le hRL T N hN hNc hN0 hID
      apply hb.trans
      change C/(R+ginibreHamiltonianLowerBoundConstant n) ≤ C/((m : ℝ)+1)
      have hm : 0 < (m : ℝ)+1 := by positivity
      have hDen : (m : ℝ)+1 ≤ R+ginibreHamiltonianLowerBoundConstant n := by dsimp [R]; linarith
      exact div_le_div_of_nonneg_left hC hm hDen
    have hlim : Tendsto (fun m : ℕ => C/((m : ℝ)+1)) atTop (𝓝 0) := by
      simpa only [mul_one_div, mul_zero] using
        (tendsto_const_nhds (x := C)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact (measureReal_eq_zero_iff).mp (le_antisymm
      (ge_of_tendsto hlim (Eventually.of_forall hBound)) measureReal_nonneg)
  have hUnion : P (⋃ m : ℕ, {ω | ginibreBrownianMaximalLifetime n α z B ω ≤ ((m : ℝ≥0) : ℝ≥0∞)}) = 0
      :=
    measure_iUnion_null (fun m => hNull (m : ℝ≥0))
  apply ae_iff.mpr
  apply measure_mono_null _ hUnion
  intro ω hω
  have hfin : ginibreBrownianMaximalLifetime n α z B ω ≠ ⊤ := hω
  obtain ⟨m, hm⟩ := exists_nat_gt (ginibreBrownianMaximalLifetime n α z B ω).toReal
  apply Set.mem_iUnion.mpr
  refine ⟨m, ?_⟩
  change ginibreBrownianMaximalLifetime n α z B ω ≤ ((m : ℝ≥0) : ℝ≥0∞)
  rw [← ENNReal.coe_toNNReal hfin]
  apply ENNReal.coe_le_coe.mpr
  exact_mod_cast hm.le

end
end GinibrePoincare
