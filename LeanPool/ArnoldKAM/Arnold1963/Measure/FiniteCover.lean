/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Basic.ENNReal.Real

/-!
Finite-cover loss estimates using subadditivity, allowing overlapping local patches.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KamProject.Arnold1963

theorem measure_complement_finite_union_lt {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (μ : Measure E) (F : Set E) (P K : ι → Set E) {ε η κ : ℝ}
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hfin : μ F ≠ ⊤)
    (hcover : μ (F \ ⋃ i, P i) < ENNReal.ofReal ε * μ F)
    (hloss : ∀ i, μ (P i \ K i) ≤ ENNReal.ofReal η * μ F)
    (hbudget : ε + (Fintype.card ι : ℝ) * η ≤ κ) :
    μ (F \ ⋃ i, K i) < ENNReal.ofReal κ * μ F := by
  classical
  have hsub : F \ ⋃ i, K i ⊆ (F \ ⋃ i, P i) ∪ ⋃ i, P i \ K i := by
    intro x hx
    by_cases hp : x ∈ ⋃ i, P i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact Or.inr (mem_iUnion.mpr ⟨i, hi, fun hk => hx.2 (mem_iUnion.mpr ⟨i, hk⟩)⟩)
    · exact Or.inl ⟨hx.1, hp⟩
  have hsum : μ (⋃ i, P i \ K i) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * η) * μ F := by
    calc
      _ ≤ ∑ i, μ (P i \ K i) := measure_iUnion_fintype_le μ _
      _ ≤ ∑ _i : ι, ENNReal.ofReal η * μ F := Finset.sum_le_sum fun i _ => hloss i
      _ = _ := by simp [ENNReal.ofReal_mul, nsmul_eq_mul, mul_assoc]
  have hbfin : ENNReal.ofReal ((Fintype.card ι : ℝ) * η) * μ F ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  calc
    μ (F \ ⋃ i, K i) ≤ μ (F \ ⋃ i, P i) + μ (⋃ i, P i \ K i) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ μ (F \ ⋃ i, P i) + ENNReal.ofReal ((Fintype.card ι : ℝ) * η) * μ F :=
      add_le_add le_rfl hsum
    _ < ENNReal.ofReal ε * μ F + ENNReal.ofReal ((Fintype.card ι : ℝ) * η) * μ F :=
      ENNReal.add_lt_add_right hbfin hcover
    _ = ENNReal.ofReal (ε + (Fintype.card ι : ℝ) * η) * μ F := by
      rw [← add_mul, ← ENNReal.ofReal_add hε (mul_nonneg (Nat.cast_nonneg _) hη)]
    _ ≤ ENNReal.ofReal κ * μ F := mul_le_mul' (ENNReal.ofReal_le_ofReal hbudget) le_rfl

end KamProject.Arnold1963
