/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Increasing limits of actual measures

An increasing sequence of measures defines a measure by taking suprema on
measurable sets. Countability also gives the same formula on arbitrary sets,
using a common measurable hull. No local finiteness is assumed or concluded.
This supplies the measure-theoretic limit needed by PSH truncations without
importing any Bedford--Taylor existence or locality obligation.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.FirstPass.IncreasingMeasures

variable {X : Type*} [MeasurableSpace X]

private theorem iSup_tsum_of_monotone {ι : Type*} (f : ℕ → ι → ℝ≥0∞)
    (hf : ∀ i, Monotone (fun k => f k i)) :
    (⨆ k, ∑' i, f k i) = ∑' i, ⨆ k, f k i := by
  simp_rw [tsum_eq_iSup_sum]
  rw [iSup_comm]
  congr 1
  funext s
  exact (ENNReal.finsetSum_iSup_of_monotone hf).symm

/-- The measure obtained from an increasing sequence, with no mass bound. -/
def increasingLimit (μ : ℕ → Measure X) (hμ : Monotone μ) : Measure X :=
  Measure.ofMeasurable (fun s _ => ⨆ k, μ k s) (by simp) (by
    intro f hf hd
    simp_rw [measure_iUnion hd hf]
    exact iSup_tsum_of_monotone (fun k i => μ k (f i))
      (fun i k l hkl => Measure.le_iff'.mp (hμ hkl) (f i)))

theorem increasingLimit_apply_measurable (μ : ℕ → Measure X) (hμ : Monotone μ)
    {s : Set X} (hs : MeasurableSet s) :
    increasingLimit μ hμ s = ⨆ k, μ k s :=
  Measure.ofMeasurable_apply s hs

theorem le_increasingLimit (μ : ℕ → Measure X) (hμ : Monotone μ) (k : ℕ) :
    μ k ≤ increasingLimit μ hμ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [increasingLimit_apply_measurable μ hμ hs]
  exact le_iSup (fun j => μ j s) k

/-- Countably many measurable hulls give the supremum formula even on
nonmeasurable sets. No completion or finiteness hypothesis is needed. -/
theorem increasingLimit_apply (μ : ℕ → Measure X) (hμ : Monotone μ) (s : Set X) :
    increasingLimit μ hμ s = ⨆ k, μ k s := by
  apply le_antisymm
  · let t := ⋂ k, toMeasurable (μ k) s
    have hst : s ⊆ t := fun x hx => mem_iInter.mpr
      (fun k => subset_toMeasurable (μ k) s hx)
    calc
      increasingLimit μ hμ s ≤ increasingLimit μ hμ t := measure_mono hst
      _ = ⨆ k, μ k t := increasingLimit_apply_measurable μ hμ
        (MeasurableSet.iInter (fun k => measurableSet_toMeasurable (μ k) s))
      _ ≤ ⨆ k, μ k s := iSup_mono (fun k => by
        calc
          μ k t ≤ μ k (toMeasurable (μ k) s) := measure_mono (iInter_subset _ k)
          _ = μ k s := measure_toMeasurable s)
  · exact iSup_le (fun k => Measure.le_iff'.mp (le_increasingLimit μ hμ k) s)

theorem increasingLimit_le_iff (μ : ℕ → Measure X) (hμ : Monotone μ)
    (ν : Measure X) : increasingLimit μ hμ ≤ ν ↔ ∀ k, μ k ≤ ν := by
  constructor
  · intro h k
    exact (le_increasingLimit μ hμ k).trans h
  · intro h
    apply Measure.le_iff'.mpr
    intro s
    rw [increasingLimit_apply]
    exact iSup_le (fun k => Measure.le_iff'.mp (h k) s)

theorem increasingLimit_zero_iff (μ : ℕ → Measure X) (hμ : Monotone μ) (s : Set X) :
    increasingLimit μ hμ s = 0 ↔ ∀ k, μ k s = 0 := by
  rw [increasingLimit_apply]
  simp

/-- Finiteness requires a uniform bound, not merely finiteness of each term. -/
theorem increasingLimit_lt_top_iff (μ : ℕ → Measure X) (hμ : Monotone μ) (s : Set X) :
    increasingLimit μ hμ s < ⊤ ↔ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k, μ k s ≤ C := by
  constructor
  · intro h
    exact ⟨increasingLimit μ hμ s, h,
      fun k => Measure.le_iff'.mp (le_increasingLimit μ hμ k) s⟩
  · rintro ⟨C, hC, h⟩
    rw [increasingLimit_apply]
    exact (iSup_le h).trans_lt hC

theorem tendsto_increasingLimit (μ : ℕ → Measure X) (hμ : Monotone μ) (s : Set X) :
    Tendsto (fun k => μ k s) atTop (𝓝 (increasingLimit μ hμ s)) := by
  rw [increasingLimit_apply]
  exact tendsto_atTop_iSup (fun k l hkl => Measure.le_iff'.mp (hμ hkl) s)

theorem increasingLimit_restrict (μ : ℕ → Measure X) (hμ : Monotone μ)
    (s : Set X) :
    (increasingLimit μ hμ).restrict s =
      increasingLimit (fun k => (μ k).restrict s)
        (fun _ _ hkl => Measure.restrict_mono (Subset.refl s) (hμ hkl)) := by
  apply Measure.ext
  intro t ht
  calc
    (increasingLimit μ hμ).restrict s t = increasingLimit μ hμ (t ∩ s) :=
      Measure.restrict_apply ht
    _ = ⨆ k, μ k (t ∩ s) := increasingLimit_apply μ hμ (t ∩ s)
    _ = ⨆ k, (μ k).restrict s t := by simp_rw [Measure.restrict_apply ht]
    _ = _ := (increasingLimit_apply _ _ t).symm

/-- A restriction which stabilizes at stage k is exactly the limit restriction. -/
theorem increasingLimit_restrict_of_stabilizes (μ : ℕ → Measure X)
    (hμ : Monotone μ) (s : Set X) (k : ℕ)
    (hstable : ∀ l, k ≤ l → (μ l).restrict s = μ k) :
    (increasingLimit μ hμ).restrict s = μ k := by
  rw [increasingLimit_restrict μ hμ s]
  apply le_antisymm
  · apply (increasingLimit_le_iff _ _ _).mpr
    intro l
    rcases le_total l k with hl | hl
    · exact (Measure.restrict_mono (Subset.refl s) (hμ hl)).trans
        (le_of_eq (hstable k le_rfl))
    · exact le_of_eq (hstable l hl)
  · rw [← hstable k le_rfl]
    exact le_increasingLimit (fun l => (μ l).restrict s) _ k

end SGPT.Foundations.Analysis.FirstPass.IncreasingMeasures
