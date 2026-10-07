/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Model.G0HNN
public import LeanPool.SmallUndecidableGroups.GroupTheory.MultipleHNN

/-!
# Concrete normal-form consequences for Borisov's `G₀`

This file specializes the iterated-HNN model in
`GroupUndecidability.Borisov.Model.G0HNN` to the presentation maps and
positive words used in Borisov's Assertions IV--V.
-/

@[expose] public section

namespace Undecidability
namespace BorisovG0NormalForm

open Function
open BorisovG0HNN
open BorisovIntersections

noncomputable section

/-! ## Swapped HNN model -/

/-- Interpret the four presentation generators in the HNN model after
interchanging `s₁` and `s₂`.  The defining relations are symmetric in the
two stable letters, so this also descends to `G₀`. -/
def swappedGenerator : Fin 4 → G0HNN := ![hnnD, hnnE, hnnS2, hnnS1]

theorem swapped_relators :
    ∀ r ∈ presentation.relSet, FreeGroup.lift swappedGenerator r = 1 := by
  rintro r ⟨i, rfl⟩
  fin_cases i
  · apply (Word.eval_relation_eq_one_iff swappedGenerator _ _).2
    have h : hnnS2⁻¹ * hnnD ^ 4 * hnnS2 = hnnD := by
      calc
        _ = hnnS2⁻¹ * (hnnD ^ 4 * hnnS2) := by simp [mul_assoc]
        _ = hnnS2⁻¹ * (hnnS2 * hnnD) := by rw [hnn_d_four_mul_s2]
        _ = hnnD := by simp
    simpa [presentation, sDRelator, dWord, s1Word, swappedGenerator,
      mul_assoc] using h
  · apply (Word.eval_relation_eq_one_iff swappedGenerator _ _).2
    have h : hnnS2⁻¹ * hnnE * hnnS2 = hnnE ^ 4 := by
      calc
        _ = hnnS2⁻¹ * (hnnE * hnnS2) := by simp [mul_assoc]
        _ = hnnS2⁻¹ * (hnnS2 * hnnE ^ 4) := by rw [hnn_e_mul_s2]
        _ = hnnE ^ 4 := by simp
    simpa [presentation, sERelator, eWord, s1Word, swappedGenerator,
      mul_assoc] using h
  · apply (Word.eval_relation_eq_one_iff swappedGenerator _ _).2
    have h : hnnS1⁻¹ * hnnD ^ 4 * hnnS1 = hnnD := by
      calc
        _ = hnnS1⁻¹ * (hnnD ^ 4 * hnnS1) := by simp [mul_assoc]
        _ = hnnS1⁻¹ * (hnnS1 * hnnD) := by rw [hnn_d_four_mul_s1]
        _ = hnnD := by simp
    simpa [presentation, sDRelator, dWord, s2Word, swappedGenerator,
      mul_assoc] using h
  · apply (Word.eval_relation_eq_one_iff swappedGenerator _ _).2
    have h : hnnS1⁻¹ * hnnE * hnnS1 = hnnE ^ 4 := by
      calc
        _ = hnnS1⁻¹ * (hnnE * hnnS1) := by simp [mul_assoc]
        _ = hnnS1⁻¹ * (hnnS1 * hnnE ^ 4) := by rw [hnn_e_mul_s1]
        _ = hnnE ^ 4 := by simp
    simpa [presentation, sERelator, eWord, s2Word, swappedGenerator,
      mul_assoc] using h

/-- The model interpretation with the two stable generators exchanged. -/
def swappedToHNN : G0 →* G0HNN :=
  PresentedGroup.toGroup swapped_relators

@[simp] theorem swappedToHNN_of (i : Fin 4) :
    swappedToHNN (PresentedGroup.of i) = swappedGenerator i := by
  simp [swappedToHNN]

@[simp] theorem swappedToHNN_stable_one :
    swappedToHNN (stable 1) = hnnS1 := by
  simp [stable, BorisovIntersections.evalWord, stableWord, s2Word,
    FP.evalWord, swappedGenerator]

/-! ## Positive stable words -/

/-- Evaluate a positive binary word at the two model stable generators. -/
def modelPositive (w : List (Fin 2)) : G0HNN :=
  Thue.evalPositive hnnS1 hnnS2 w

@[simp] theorem toHNN_positiveWord (w : List (Fin 2)) :
    toHNN (evalWord (positiveWord w)) = modelPositive w := by
  simp only [BorisovIntersections.evalWord, FP.evalWord, positiveWord,
    Word.eval_substitutePositive, modelPositive, Thue.evalPositive]
  rw [map_list_prod]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  fin_cases i <;> simp [hnnGenerator, s1Word, s2Word]

theorem count_zero_pos_of_containsBoth {w : List (Fin 2)}
    (hw : Thue.ContainsBoth w) : 0 < w.count (0 : Fin 2) :=
  List.count_pos_iff.mpr hw.1

/-! ## Images of the displayed `A_i` and `B_i` -/

@[simp] theorem toHNN_d : toHNN BorisovIntersections.d = hnnD := by
  simpa [presentedD] using toHNN_presentedD

@[simp] theorem toHNN_e : toHNN BorisovIntersections.e = hnnE := by
  simpa [presentedE] using toHNN_presentedE

@[simp] theorem toHNN_stable_zero : toHNN (stable 0) = hnnS1 := by
  simpa [presentedS1, stable, stableWord] using toHNN_presentedS1

@[simp] theorem toHNN_stable_one : toHNN (stable 1) = hnnS2 := by
  simpa [presentedS2, stable, stableWord] using toHNN_presentedS2

private theorem a_eq_product (datum : Thue.StandingDatum) (i : Fin 3) :
    a datum i = BorisovIntersections.d ^ (i.val + 1) *
      evalWord (positiveWord (datum.F i)) *
        BorisovIntersections.e ^ (i.val + 1) := by
  simp [a, aWord, evalWord, FP.evalWord, Word.eval_product,
    BorisovIntersections.d, BorisovIntersections.e, dWord, eWord, mul_assoc]

private theorem b_eq_product (datum : Thue.StandingDatum) (i : Fin 3) :
    b datum i = BorisovIntersections.d ^ (i.val + 1) *
      evalWord (positiveWord (datum.E i)) *
        BorisovIntersections.e ^ (i.val + 1) := by
  simp [b, bWord, evalWord, FP.evalWord, Word.eval_product,
    BorisovIntersections.d, BorisovIntersections.e, dWord, eWord, mul_assoc]

@[simp] theorem toHNN_a (datum : Thue.StandingDatum) (i : Fin 3) :
    toHNN (a datum i) =
      hnnD ^ (i.val + 1) * modelPositive (datum.F i) *
        hnnE ^ (i.val + 1) := by
  rw [a_eq_product, map_mul, map_mul, map_pow, map_pow,
    toHNN_d, toHNN_e, toHNN_positiveWord]

@[simp] theorem toHNN_b (datum : Thue.StandingDatum) (i : Fin 3) :
    toHNN (b datum i) =
      hnnD ^ (i.val + 1) * modelPositive (datum.E i) *
        hnnE ^ (i.val + 1) := by
  rw [b_eq_product, map_mul, map_mul, map_pow, map_pow,
    toHNN_d, toHNN_e, toHNN_positiveWord]

/-! ## Concrete support exclusions -/

private theorem hnnD_mem_stageOne :
    hnnD ∈ MonoidHom.range g1ToG0HNN := by
  refine ⟨baseToG1 baseD, ?_⟩
  rfl

private theorem hnnE_mem_stageOne :
    hnnE ∈ MonoidHom.range g1ToG0HNN := by
  refine ⟨baseToG1 baseE, ?_⟩
  rfl

private theorem hnnS1_mem_stageOne :
    hnnS1 ∈ MonoidHom.range g1ToG0HNN := by
  refine ⟨BorisovHNNModel.s1, ?_⟩
  rfl

theorem toHNN_mem_stageOne_of_mem_J_zero {x : G0}
    (hx : x ∈ J 0) :
    toHNN x ∈ MonoidHom.range g1ToG0HNN := by
  let H := (MonoidHom.range g1ToG0HNN).comap toHNN
  have hle : J 0 ≤ H := by
    unfold J
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hnnD_mem_stageOne
    · exact hnnE_mem_stageOne
    · change toHNN (stable 0) ∈ MonoidHom.range g1ToG0HNN
      simpa using hnnS1_mem_stageOne
  exact hle hx

theorem swappedToHNN_mem_stageOne_of_mem_J_one {x : G0}
    (hx : x ∈ J 1) :
    swappedToHNN x ∈ MonoidHom.range g1ToG0HNN := by
  let H := (MonoidHom.range g1ToG0HNN).comap swappedToHNN
  have hle : J 1 ≤ H := by
    unfold J
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hnnD_mem_stageOne
    · exact hnnE_mem_stageOne
    · change swappedToHNN (stable 1) ∈ MonoidHom.range g1ToG0HNN
      simpa using hnnS1_mem_stageOne
  exact hle hx

end

end BorisovG0NormalForm
end Undecidability
