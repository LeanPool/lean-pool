/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.PhysicalKeyRelabel
public import LeanPool.ShellsortMean.VerifiedOptimum
public import Mathlib.Data.Finset.Sort

/-! The input distribution is uniform on bijections from physical slots to
the actual key set. The same gap table works for every key set of size n. -/
@[expose] public noncomputable section
namespace Shellsort.PhysicalKeyOptimum
open HarvestOperationalAudit HarvestBlockIteration PredeterminedOptimum

/-- The slot-indexed array associated to a bijection onto the key set. -/
def physicalArray {α : Type} {n : ℕ} {s : Finset α}
    (b : Fin n ≃ ↥s) : Vector α n := Vector.ofFn fun i => (b i : α)

/-- The mean comparison cost over all bijective assignments of the key set to slots. -/
def physicalMean {α : Type} [LinearOrder α] (n : ℕ) (s : Finset α) (w : PositiveWord) : ℝ :=
  (∑ b : Fin n ≃ ↥s, ((runWord (physicalArray b) w).2 : ℝ)) /
    (Fintype.card (Fin n ≃ ↥s) : ℝ)

private def assignments {α : Type} [LinearOrder α] {n : ℕ} (s : Finset α) (hs : s.card = n) :
    RankPlacement n ≃ (Fin n ≃ ↥s) :=
  (Equiv.inv (Equiv.Perm (Fin n))).trans
    ((Equiv.refl (Fin n)).equivCongr (s.orderIsoOfFin hs).toEquiv)

private theorem assignment_slots {α : Type} [LinearOrder α] {n : ℕ} (s : Finset α)
    (hs : s.card = n) (p : RankPlacement n) :
    physicalArray (assignments s hs p) = (slots p).map (s.orderEmbOfFin hs) := by
  apply Vector.ext
  intro i hi
  simp only [physicalArray, slots, Vector.getElem_ofFn, Vector.getElem_map]
  rfl

theorem physicalMean_eq {α : Type} [LinearOrder α] {n : ℕ} (s : Finset α)
    (hs : s.card = n) (w : PositiveWord) :
    physicalMean n s w = arrayMean n w := by
  let reward (b : Fin n ≃ ↥s) : ℝ := (runWord (physicalArray b) w).2
  have sumEq := Equiv.sum_comp (assignments s hs) reward
  have count : Fintype.card (Fin n ≃ ↥s) = n.factorial := by
    simpa only [RankPlacement, Fintype.card_perm, Fintype.card_fin] using
      (Fintype.card_congr (assignments s hs)).symm
  unfold physicalMean arrayMean uniformAverage
  rw [count]
  apply congrArg (fun z : ℝ => z / (n.factorial : ℝ))
  change (∑ b, reward b) = _
  rw [← sumEq]
  apply Finset.sum_congr rfl
  intro p _
  simp only [reward, assignment_slots, relabel_word]

theorem exists_uniform_family_for_physical_keys :
    ∃ W : ℕ → PositiveWord, ∀ n, 2 ≤ n → Legal n (W n) ∧
      ∀ (α : Type) [LinearOrder α] (s : Finset α) (hs : s.card = n),
      (∀ b : Fin n ≃ ↥s, (runWord (physicalArray b) (W n)).1 =
        Vector.ofFn (s.orderEmbOfFin hs)) ∧
      (∀ v, Legal n v → physicalMean n s (W n) ≤ physicalMean n s v) ∧
      (n : ℝ) * Real.logb 2 n / 2 ≤ Real.logb 2 (n.factorial : ℝ) ∧
      Real.logb 2 (n.factorial : ℝ) ≤ physicalMean n s (W n) ∧
      physicalMean n s (W n) ≤ (1 + (2 : ℝ) ^ 165) * (n : ℝ) * Real.logb 2 n := by
  obtain ⟨W, spec⟩ := exists_optimal_executed_family
  refine ⟨W, fun n hn => ?_⟩
  obtain ⟨legal, sorted, best, half, lower, upper⟩ := spec n hn
  refine ⟨legal, ?_⟩
  intro α _ s hs
  refine ⟨?_, ?_, half, ?_, ?_⟩
  · intro b
    obtain ⟨p, rfl⟩ := (assignments s hs).surjective b
    rw [assignment_slots, relabel_word]
    change (runWord (slots p) (W n)).1.map _ = _
    rw [sorted]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, Vector.getElem_map, id_eq]
  · intro v hv
    simpa only [physicalMean_eq s hs] using best v hv
  · simpa only [physicalMean_eq s hs] using lower
  · simpa only [physicalMean_eq s hs] using upper


end Shellsort.PhysicalKeyOptimum
