/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitHamiltonianLevelStopping.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianPrefix
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianFirstLevel

/-! Actual first Hamiltonian levels are stopping times of the canonical Brownian solution. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The first time the Hamiltonian of the maximal Ginibre path driven by the Brownian noise of
the sample `ω` reaches the level `R` (`⊤` if it never does before the lifetime). -/
def ginibreBrownianHamiltonianFirstLevel {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ginibreDrivenHamiltonianFirstLevel n α (ginibreBrownianFullContinuousNoise n B α ω).val z R

theorem ginibreBrownianHamiltonianPrefix_norm_level {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (R : ℝ) (T : ℝ≥0) (ω : Ω)
    (hT : (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω) :
    (∃ t ∈ Icc 0 T, R ≤ ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω)) ↔
      R + ginibreHamiltonianLowerBoundConstant n ≤
        ‖ginibreBrownianHamiltonianPrefix n α z B T ω +
          ContinuousMap.const _ (ginibreHamiltonianLowerBoundConstant n)‖ := by
  let : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, by simp⟩⟩
  let f := ginibreBrownianHamiltonianPrefix n α z B T ω +
    ContinuousMap.const _ (ginibreHamiltonianLowerBoundConstant n)
  have hf (t : Icc (0 : ℝ≥0) T) : ‖f t‖ =
      ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω) +
        ginibreHamiltonianLowerBoundConstant n := by
    have ha : (t.val : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω :=
      (ENNReal.coe_le_coe.mpr t.property.2).trans_lt hT
    have he := ginibreDrivenMaximalPath_equation (n := n) (α := α)
      (N := (ginibreBrownianFullContinuousNoise n B α ω).val) (z := z)
      (t := (t.val : ℝ)) ⟨t.val.coe_nonneg, by
        simpa only [ENNReal.ofReal_coe_nnreal, ginibreBrownianMaximalLifetime] using ha⟩
    have hb := ginibreHamiltonian_bounded_below hn _ he.1
    change ‖ginibreBrownianHamiltonianPrefix n α z B T ω t + _‖ = _
    rw [ginibreBrownianHamiltonianPrefix_apply, ite_eq_left hT, Real.norm_eq_abs,
      abs_of_nonneg]
    · rfl
    · have hb' : -ginibreHamiltonianLowerBoundConstant n ≤
          ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω) := by
        simpa only [ginibreDrivenMaximalPath, ginibreBrownianMaximalProcess,
          Real.toNNReal_coe] using hb
      change 0 ≤ ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω) +
        ginibreHamiltonianLowerBoundConstant n
      linarith
  constructor
  · rintro ⟨t, ht, hval⟩
    have hnorm := f.norm_coe_le_norm ⟨t, ht⟩
    rw [hf] at hnorm
    change R + _ ≤ ‖f‖
    linarith
  · intro h
    obtain ⟨t, ht⟩ := ginibreContinuousMap_exists_norm_max f
    rw [ht, hf] at h
    refine ⟨t, t.property, ?_⟩
    linarith

theorem ginibreBrownianHamiltonianFirstLevel_isStoppingTime {Ω : Type*}
    [mAmbient : MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) :
    IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (ginibreBrownianHamiltonianFirstLevel n α z B R) := by
  intro T
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  have hLife := ginibreBrownianMaximalLifetime_isStoppingTime hn α z B P hB
  have hDead := hLife.measurableSet_le T
  have hAlive := hLife.measurableSet_gt T
  let : MeasurableSpace C(Icc (0 : ℝ≥0) T, ℝ) := borel _
  let : BorelSpace C(Icc (0 : ℝ≥0) T, ℝ) := ⟨rfl⟩
  have hm := ginibreBrownianHamiltonianPrefix_measurable hn α z B P hB T
  have hc : @Measurable C(Icc (0 : ℝ≥0) T, ℝ) ℝ (borel _) _
      (fun f => ‖f + ContinuousMap.const _ (ginibreHamiltonianLowerBoundConstant n)‖) :=
    (continuous_id.add continuous_const).norm.measurable
  have hMax := measurableSet_le (f := fun _ : Ω => R + ginibreHamiltonianLowerBoundConstant n)
    measurable_const (hc.comp hm)
  have hSet : @MeasurableSet Ω (F T)
      ({ω | ginibreBrownianMaximalLifetime n α z B ω ≤ (T : ℝ≥0∞)} ∪
        ({ω | (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω} ∩
          {ω | R + ginibreHamiltonianLowerBoundConstant n ≤
            ‖ginibreBrownianHamiltonianPrefix n α z B T ω +
              ContinuousMap.const _ (ginibreHamiltonianLowerBoundConstant n)‖})) :=
    hDead.union (hAlive.inter hMax)
  change @MeasurableSet Ω (F T)
    {ω | ginibreBrownianHamiltonianFirstLevel n α z B R ω ≤ (T : ℝ≥0∞)}
  convert hSet using 1
  ext ω
  have he := ginibreDrivenHamiltonianFirstLevel_le_iff_lifetime hn α
    (ginibreBrownianFullContinuousNoise n B α ω).val
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz R hR T
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  rw [show ginibreBrownianHamiltonianFirstLevel n α z B R ω =
    ginibreDrivenHamiltonianFirstLevel n α
      (ginibreBrownianFullContinuousNoise n B α ω).val z R from rfl]
  rw [he]
  change (ginibreBrownianMaximalLifetime n α z B ω ≤ (T : ℝ≥0∞)) ∨
    ((T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω ∧ ∃ t ∈ Icc 0 T,
    R ≤ ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω)) ↔ _
  constructor
  · rintro (hd | ⟨ha, hh⟩)
    · exact Or.inl hd
    · exact Or.inr ⟨ha, (ginibreBrownianHamiltonianPrefix_norm_level hn α z B R T ω ha).mp hh⟩
  · rintro (hd | ⟨ha, hh⟩)
    · exact Or.inl hd
    · exact Or.inr ⟨ha, (ginibreBrownianHamiltonianPrefix_norm_level hn α z B R T ω ha).mpr hh⟩

end
end GinibrePoincare
