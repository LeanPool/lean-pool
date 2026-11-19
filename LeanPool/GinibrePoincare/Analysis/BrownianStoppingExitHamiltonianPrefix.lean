/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitHamiltonianPrefix.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitLifetimeStopping
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalLevel
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousStoppingTime

/-! Measurable Hamiltonian paths on each alive compact time prefix. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The Hamiltonian along the Brownian-driven maximal Ginibre path on `[0, T]`, packaged as a
continuous map via `ContinuousMap.mkD`; it is `0` when `T` is not below the maximal lifetime. -/
def ginibreBrownianHamiltonianPrefix {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (ω : Ω) : C(Icc (0 : ℝ≥0) T, ℝ) :=
  ContinuousMap.mkD (fun t => if (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω
    then ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω) else 0) 0

theorem ginibreBrownianHamiltonianPrefix_continuous {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (ω : Ω) : Continuous (fun t : Icc (0 : ℝ≥0) T =>
      if (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω then
        ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω) else 0) := by
  classical
  by_cases hT : (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω
  · simp only [ite_eq_left hT]
    let N := ginibreBrownianFullContinuousNoise n B α ω
    have hc := ginibreDrivenMaximalPath_hamiltonian_continuousOn n α N.val z
    have hg : Continuous (fun t : Icc (0 : ℝ≥0) T => ((t : ℝ≥0) : ℝ)) :=
      NNReal.continuous_coe.comp continuous_subtype_val
    have hm : MapsTo (fun t : Icc (0 : ℝ≥0) T => ((t : ℝ≥0) : ℝ)) univ
        (ginibreDrivenMaximalDomain n α N.val z) := by
      intro t _
      refine ⟨t.val.coe_nonneg, ?_⟩
      rw [ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.coe_le_coe.mpr t.property.2).trans_lt hT
    have hh := hc.comp_continuous hg (fun t => hm (Set.mem_univ t))
    simpa only [ginibreDrivenMaximalPath, ginibreBrownianMaximalProcess,
      Real.toNNReal_coe, Function.comp_def, N] using hh
  · simp only [ite_eq_right hT]
    exact continuous_const

theorem ginibreBrownianHamiltonianPrefix_apply {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (ω : Ω) (t : Icc (0 : ℝ≥0) T) :
    ginibreBrownianHamiltonianPrefix n α z B T ω t =
      if (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω then
        ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω) else 0 := by
  exact ContinuousMap.mkD_apply_of_continuous
    (ginibreBrownianHamiltonianPrefix_continuous n α z B T ω)

theorem ginibreHamiltonian_measurable (n : ℕ) : Measurable (ginibreHamiltonian n) := by
  exact (measurable_const.mul (contDiff_configurationNormSq (n := n)).continuous.measurable).sub
    (Real.measurable_log.comp (contDiff_vandermondeWeight n).continuous.measurable)

theorem ginibreBrownianHamiltonianPrefix_measurable {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    @Measurable Ω C(Icc (0 : ℝ≥0) T, ℝ)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) T)
      (borel _) (ginibreBrownianHamiltonianPrefix n α z B T) := by
  classical
  let : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, by simp⟩⟩
  let : MeasurableSpace C(Icc (0 : ℝ≥0) T, ℝ) := borel _
  let : BorelSpace C(Icc (0 : ℝ≥0) T, ℝ) := ⟨rfl⟩
  have hAlive := (ginibreBrownianMaximalLifetime_isStoppingTime hn α z B P hB).measurableSet_gt T
  change @MeasurableSet Ω
    (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) T)
    {ω | (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω} at hAlive
  apply ginibre_measurable_continuousMap_of_evaluations
    (mΩ := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) T)
  intro t
  have hm := ((ginibreBrownianMaximalProcess_stronglyAdapted hn α z B P hB t).mono
    ((ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)).mono
      t.property.2)).measurable
  have hi : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) T) _
      (fun ω => if (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω then
        ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω) else 0) :=
    ((ginibreHamiltonian_measurable n).comp hm).ite hAlive measurable_const
  simpa only [ginibreBrownianHamiltonianPrefix_apply] using hi

end
end GinibrePoincare
