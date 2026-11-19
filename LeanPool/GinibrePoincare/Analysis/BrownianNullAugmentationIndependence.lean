/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianNullAugmentationIndependence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticPastAugmentation

/-!
# Brownian null augmentation independence

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `indepFun_of_nullAugmented_measurable`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

@[instance_reducible]
private def aeBaseMeasurableSpace {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := ∃ t, @MeasurableSet Ω m t ∧ ∀ᵐ ω ∂P, ω ∈ s ↔ ω ∈ t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, Filter.Eventually.of_forall (fun _ => Iff.rfl)⟩
  measurableSet_compl s hs := by
    obtain ⟨t, ht, he⟩ := hs
    exact ⟨tᶜ, ht.compl, he.mono (fun ω h => not_congr h)⟩
  measurableSet_iUnion f hf := by
    choose t ht he using hf
    refine ⟨⋃ j, t j, MeasurableSet.iUnion ht, ?_⟩
    filter_upwards [ae_all_iff.mpr he] with ω hω
    simp only [Set.mem_iUnion]
    exact exists_congr (fun j => hω j)

theorem ginibreNullAugmentation_measurableSet_ae_base {Ω : Type*}
    [mAmbient : MeasurableSpace Ω] (P : Measure Ω) (m : MeasurableSpace Ω)
    (s : Set Ω) (hs : @MeasurableSet Ω (ginibreNullAugmentation (mAmbient := mAmbient) P m) s) :
    ∃ t, @MeasurableSet Ω m t ∧ ∀ᵐ ω ∂P, ω ∈ s ↔ ω ∈ t := by
  have hm : m ≤ @aeBaseMeasurableSpace Ω mAmbient P m := by
    intro t ht
    exact ⟨t, ht, Filter.Eventually.of_forall (fun _ => Iff.rfl)⟩
  have hn : MeasurableSpace.generateFrom {s : Set Ω | P s = 0} ≤ @aeBaseMeasurableSpace Ω mAmbient P
      m := by
    apply MeasurableSpace.generateFrom_le
    intro t ht
    refine ⟨∅, MeasurableSet.empty, ?_⟩
    have hnot : ∀ᵐ ω ∂P, ω ∉ t := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using (show P t = 0 from ht)
    exact hnot.mono (fun ω hω => by simp [hω])
  exact (sup_le hm hn) s hs

theorem indep_nullAugmentation {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (m₁ m₂ : MeasurableSpace Ω) (hm₁ : m₁ ≤ mAmbient) (hm₂ : m₂ ≤ mAmbient)
    (hi : Indep m₁ m₂ P) :
    Indep (ginibreNullAugmentation (mAmbient := mAmbient) P m₁)
      (ginibreNullAugmentation (mAmbient := mAmbient) P m₂) P := by
  rw [indep_iff_forall_indepSet]
  intro s t hs ht
  obtain ⟨s₀, hs₀, hes⟩ := ginibreNullAugmentation_measurableSet_ae_base (mAmbient := mAmbient) P m₁
      s hs
  obtain ⟨t₀, ht₀, het⟩ := ginibreNullAugmentation_measurableSet_ae_base (mAmbient := mAmbient) P m₂
      t ht
  apply (indepSet_iff_measure_inter_eq_mul
    (ginibreNullAugmentation_le (mAmbient := mAmbient) P m₁ hm₁ _ hs)
    (ginibreNullAugmentation_le (mAmbient := mAmbient) P m₂ hm₂ _ ht) P).mpr
  have hsEq : P s = P s₀ := measure_congr (hes.mono (fun _ h => propext h))
  have htEq : P t = P t₀ := measure_congr (het.mono (fun _ h => propext h))
  have hiEq : P (s ∩ t) = P (s₀ ∩ t₀) := measure_congr (by
    filter_upwards [hes, het] with ω hs ht
    exact propext (and_congr hs ht))
  rw [hsEq, htEq, hiEq]
  exact (hi.indepSet_of_measurableSet hs₀ ht₀).measure_inter_eq_mul

theorem indep_nullAugmentation_right {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (m₁ m₂ : MeasurableSpace Ω) (hm₁ : m₁ ≤ mAmbient) (hm₂ : m₂ ≤ mAmbient)
    (hi : Indep m₁ m₂ P) :
    Indep m₁ (ginibreNullAugmentation (mAmbient := mAmbient) P m₂) P := by
  have hh := indep_nullAugmentation (mAmbient := mAmbient) P m₁ m₂ hm₁ hm₂ hi
  rw [indep_iff_forall_indepSet] at hh ⊢
  intro s t hs ht
  exact hh s t (ginibreNullAugmentation_base_le (mAmbient := mAmbient) P m₁ _ hs) ht

theorem indepFun_of_nullAugmented_measurable {Ω A E : Type*}
    [mAmbient : MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (m : MeasurableSpace Ω) (hm : m ≤ mAmbient) (X : Ω → E) (hx : @Measurable Ω E mAmbient _ X)
    (Y : Ω → A) (hy : @Measurable Ω A (ginibreNullAugmentation (mAmbient := mAmbient) P m) _ Y)
    (hi : Indep (MeasurableSpace.comap X inferInstance) m P) : IndepFun X Y P := by
  have hh := indep_nullAugmentation_right (mAmbient := mAmbient) P
    (MeasurableSpace.comap X inferInstance) m hx.comap_le hm hi
  change Indep (MeasurableSpace.comap X inferInstance) (MeasurableSpace.comap Y inferInstance) P
  rw [indep_iff_forall_indepSet] at hh ⊢
  intro s t hs ht
  exact hh s t hs (hy.comap_le _ ht)

end
end GinibrePoincare
