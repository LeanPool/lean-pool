/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticContinuousStoppingTime.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathClosedHittingTime

/-! Actual continuous norm exits are stopping times, without right-continuity assumptions. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreContinuousMap_exists_norm_max {T E : Type*} [TopologicalSpace T] [CompactSpace T]
    [Nonempty T] [NormedAddCommGroup E] (f : C(T, E)) : ∃ t, ‖f‖ = ‖f t‖ := by
  obtain ⟨t, ht, hMax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
      f.continuous.norm.continuousOn
  refine ⟨t, le_antisymm ((ContinuousMap.norm_le_of_nonempty f).mpr (fun s => hMax (by trivial)))
      (f.norm_coe_le_norm t)⟩

theorem ginibreContinuous_norm_exit_isStoppingTime {Ω E : Type*} [mAmbient : MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (F : Filtration ℝ≥0 mAmbient) (u : ℝ≥0 → Ω → E)
    (huAdapt : StronglyAdapted F u) (huCont : ∀ ω, Continuous (fun t => u t ω))
    (r : ℝ) (T : ℝ≥0) : IsStoppingTime F (fun ω => ((hittingBtwn u {x | r ≤ ‖x‖} 0 T ω : ℝ≥0) :
        WithTop ℝ≥0)) := by
  intro t
  let : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, by simp⟩⟩
  let : MeasurableSpace C(Icc (0 : ℝ≥0) t, E) := borel _
  let : BorelSpace C(Icc (0 : ℝ≥0) t, E) := ⟨rfl⟩
  let R : Ω → C(Icc (0 : ℝ≥0) t, E) := fun ω =>
    ⟨fun s => u s ω, (huCont ω).comp continuous_subtype_val⟩
  have hR : @Measurable Ω _ (F t) _ R := by
    apply ginibre_measurable_continuousMap_of_evaluations (mΩ := F t)
    intro s
    exact ((huAdapt s).mono (F.mono s.property.2)).measurable
  have hNorm : @Measurable Ω ℝ (F t) _ (fun ω => ‖R ω‖) := continuous_norm.measurable.comp hR
  have hSet : @MeasurableSet Ω (F t) {ω | r ≤ ‖R ω‖} := measurableSet_le measurable_const hNorm
  have hExists (ω : Ω) : (∃ j ∈ Icc 0 t, r ≤ ‖u j ω‖) ↔ r ≤ ‖R ω‖ := by
    constructor
    · rintro ⟨j, hj, hNormj⟩
      exact hNormj.trans ((R ω).norm_coe_le_norm ⟨j, hj⟩)
    · intro h
      obtain ⟨j, hj⟩ := ginibreContinuousMap_exists_norm_max (R ω)
      exact ⟨j, j.property, by simpa only [hj, R, ContinuousMap.coe_mk] using h⟩
  have hClosed : IsClosed {x : E | r ≤ ‖x‖} := isClosed_le continuous_const continuous_norm
  have hEq : {ω | ((hittingBtwn u {x | r ≤ ‖x‖} 0 T ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
      if T ≤ t then Set.univ else {ω | r ≤ ‖R ω‖} := by
    classical
    ext ω
    simp only [WithTop.coe_le_coe, Set.mem_ofPred_eq]
    rw [drivenContinuous_closed_hitting_le_iff u _ hClosed T t ω (huCont ω)]
    simp only [Set.mem_ofPred_eq]
    rw [hExists]
    by_cases hT : T ≤ t <;> simp [hT]
  rw [hEq]
  split_ifs <;> first | exact MeasurableSet.univ | exact hSet

end
end GinibrePoincare
