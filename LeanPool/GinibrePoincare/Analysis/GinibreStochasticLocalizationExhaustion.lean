/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticLocalizationExhaustion.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticNoncollision

/-! # Hamiltonian stopping times exhaust time

The localizations use energy levels `ginibreHamiltonian n z + k` and time caps
`k`. First-hit times are monotone in the energy level; taking their minimum
with the cap preserves monotonicity in both parameters.

For a path of infinite lifetime and a fixed horizon `b`, its continuous
Hamiltonian path is bounded on `[0, b]`. Choose `k` larger than both `b` and
this bound minus the initial Hamiltonian. The energy level cannot be reached
before `b`, and the cap cannot stop the path there either. This deterministic
argument is applied on the full-measure event of infinite Brownian lifetime.
The conclusion is eventual domination of every finite horizon, which is the
exhaustion property used by the global local-martingale and CIR endpoints. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenHamiltonianFirstLevel_mono_level (n : ℕ) (α : ℝ)
    (N : ℝ → Configuration n) (z : Configuration n) :
    Monotone (ginibreDrivenHamiltonianFirstLevel n α N z) := by
  intro R S hRS
  by_cases hS : (ginibreDrivenLevelHit n α N z S).Nonempty
  · obtain ⟨t, he, ht⟩ := ginibreDrivenHamiltonianFirstLevel_attained hS
    rw [he]
    apply (ginibreDrivenHamiltonianFirstLevel_le_iff t).mpr
    exact ⟨t, ⟨ht.1, hRS.trans ht.2⟩, le_rfl⟩
  · simp only [ginibreDrivenHamiltonianFirstLevel, dite_eq_right hS]
    exact le_top

theorem ginibreDrivenHamiltonianBoundedStop_mono_level_cap (n : ℕ) (α : ℝ)
    (N : ℝ → Configuration n) (z : Configuration n)
    {R S : ℝ} (hRS : R ≤ S) {T U : ℝ≥0} (hTU : T ≤ U) :
    ginibreDrivenHamiltonianBoundedStop n α N z R T ≤
      ginibreDrivenHamiltonianBoundedStop n α N z S U := by
  apply ENNReal.coe_le_coe.mp
  rw [ginibreDrivenHamiltonianBoundedStop_coe, ginibreDrivenHamiltonianBoundedStop_coe]
  exact min_le_min (ENNReal.coe_le_coe.mpr hTU)
    (ginibreDrivenHamiltonianFirstLevel_mono_level n α N z hRS)

theorem ginibreBrownianHamiltonianBoundedStop_natural_monotone {Ω : Type*}
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Monotone (fun k : ℕ => ginibreBrownianHamiltonianBoundedStop n α z B
      (ginibreHamiltonian n z+k) k ω) := by
  intro k l hkl
  apply ginibreDrivenHamiltonianBoundedStop_mono_level_cap n α
    (ginibreBrownianFullContinuousNoise n B α ω).val z
  · exact add_le_add (le_refl (ginibreHamiltonian n z)) (by exact_mod_cast hkl)
  · exact_mod_cast hkl

theorem ginibreDrivenHamiltonianBoundedStop_exhausts_of_lifetime_top
    {n : ℕ} (α : ℝ) (N : ℝ → Configuration n) (z : Configuration n)
    (hlife : ginibreDrivenMaximalLifetime n α N z = ⊤) (b : ℝ≥0) :
    ∀ᶠ k : ℕ in atTop,
      b ≤ ginibreDrivenHamiltonianBoundedStop n α N z (ginibreHamiltonian n z+k) k := by
  have hb : (b : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z := by simp [hlife]
  have hc := ginibreDrivenHamiltonianPrefix_continuous b hb
  obtain ⟨C, hC, hBound⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) b)).image
      hc).isBounded.exists_pos_norm_le
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (max (b : ℝ) (C-ginibreHamiltonian n z))
  filter_upwards [eventually_ge_atTop k₀] with k hk
  have hkReal : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have hbK : b ≤ (k : ℝ≥0) := by
    apply NNReal.coe_le_coe.mp
    have := (le_max_left (b : ℝ) (C-ginibreHamiltonian n z)).trans_lt hk₀
    exact this.le.trans hkReal
  have hCR : C < ginibreHamiltonian n z+k := by
    have := (le_max_right (b : ℝ) (C-ginibreHamiltonian n z)).trans_lt hk₀
    linarith
  have hFirst : (b : ℝ≥0∞) ≤ ginibreDrivenHamiltonianFirstLevel n α N z (ginibreHamiltonian n z+k)
      := by
    apply le_of_not_gt
    intro hlt
    obtain ⟨s, hs, hsb⟩ := (ginibreDrivenHamiltonianFirstLevel_le_iff b).mp hlt.le
    have hAbs : ‖ginibreHamiltonian n (ginibreDrivenMaximalValue n α N z s)‖ ≤ C := by
      apply hBound _
      refine ⟨s, ⟨bot_le, hsb⟩,?_⟩
      simp only [min_eq_left hsb]
    have hVal : ginibreHamiltonian n (ginibreDrivenMaximalValue n α N z s) ≤ C :=
      (le_abs_self _).trans hAbs
    exact (not_le_of_gt hCR) (hs.2.trans hVal)
  apply ENNReal.coe_le_coe.mp
  rw [ginibreDrivenHamiltonianBoundedStop_coe]
  exact le_min (ENNReal.coe_le_coe.mpr hbK) hFirst

theorem ginibreBrownianHamiltonianBoundedStop_exhausts_ae
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ b : ℝ≥0, ∀ᶠ k : ℕ in atTop,
      b ≤ ginibreBrownianHamiltonianBoundedStop n α z B (ginibreHamiltonian n z+k) k ω := by
  filter_upwards [ginibreBrownianMaximalLifetime_top_ae hn α z hz B P hB hind] with ω hω
  intro b
  exact ginibreDrivenHamiltonianBoundedStop_exhausts_of_lifetime_top α _ z hω b
end
end GinibrePoincare
