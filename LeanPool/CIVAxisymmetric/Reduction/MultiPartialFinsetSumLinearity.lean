/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialLinearity
public import LeanPool.CIVAxisymmetric.Reduction.AnalyticBoundOnConstant

/-!
### Linearity of multi-partial derivatives over finite sums

The `Finset`-indexed generalization of `multiPartial_add` / `multiPartial_const_smul`, the
shape needed whenever `thm:analytic:interior` (Kahane 1969, Theorem 1.2) differentiates a finite
linear combination of several coupled unknowns — for instance velocity, vorticity, and an
adjoined force term — rather than just two fields.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem multiPartial_finset_sum {ι : Type*} {h : ι → ParabolicPoint → ℝ} {u : Finset ι}
    {s : Set Vec3} (hs : IsOpen s) (t : ℝ)
    (hG : ∀ j ∈ u, ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h j (x, t)) s)
    (α : Fin 3 → ℕ) {x : Vec3} (hx : x ∈ s) :
    multiPartial (fun z => ∑ j ∈ u, h j z) α (x, t) = ∑ j ∈ u, multiPartial (h j) α (x, t) := by
  classical
  refine Finset.induction_on u (fun _ => ?_) (fun a s' has ih hG => ?_) hG
  · have hsum_empty : (fun z : ParabolicPoint => ∑ j ∈ (∅ : Finset ι), h j z) =
      fun _ : ParabolicPoint => (0 : ℝ) := by
      ext z; simp [Finset.sum_empty]
    rw [hsum_empty]
    simp only [Finset.sum_empty]
    by_cases hsum : α 0 + α 1 + α 2 = 0
    · have hα_eq : α = fun _ => 0 := by
        have hsum' : α 0 + α 1 + α 2 = 0 := hsum
        have ⟨hα01, hα2⟩ := Nat.add_eq_zero_iff.mp hsum'
        have ⟨hα0, hα1⟩ := Nat.add_eq_zero_iff.mp hα01
        ext i
        fin_cases i <;> assumption
      rw [hα_eq]
      exact multiPartial_const_zero_order (c := (0 : ℝ)) (x, t)
    · have hpos : 1 ≤ α 0 + α 1 + α 2 :=
        Nat.one_le_of_lt (Nat.pos_of_ne_zero hsum)
      rw [multiPartial_const_eq_zero_of_le hpos (x, t)]
  · have ha_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h a (x, t)) s :=
      hG a (Finset.mem_insert_self a s')
    have hs'_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => ∑ j ∈ s', h j (x, t)) s :=
      ContDiffOn.sum fun j hj => hG j (Finset.mem_insert_of_mem hj)
    have hsum_insert : (fun z : ParabolicPoint => ∑ j ∈ insert a s', h j z) =
        (fun z => h a z + ∑ j ∈ s', h j z) := by
      ext z; simp [Finset.sum_insert has]
    rw [hsum_insert]
    rw [multiPartial_add hs t ha_smooth hs'_smooth α hx]
    rw [ih (fun j hj => hG j (Finset.mem_insert_of_mem hj))]
    simp [Finset.sum_insert has]

theorem multiPartial_fin3_sum {h : Fin 3 → ParabolicPoint → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (t : ℝ) (hG : ∀ j : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h j (x, t)) s)
    (α : Fin 3 → ℕ) {x : Vec3} (hx : x ∈ s) :
    multiPartial (fun z => ∑ j : Fin 3, h j z) α (x, t) = ∑ j : Fin 3, multiPartial (h j) α (x,
      t) := by
  simpa using multiPartial_finset_sum (u := Finset.univ) hs t (fun j _ => hG j) α hx

theorem multiPartial_finset_sum_const_smul {ι : Type*} {h : ι → ParabolicPoint → ℝ} {c : ι → ℝ}
    {u : Finset ι} {s : Set Vec3} (hs : IsOpen s) (t : ℝ)
    (hG : ∀ j ∈ u, ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h j (x, t)) s)
    (α : Fin 3 → ℕ) {x : Vec3} (hx : x ∈ s) :
    multiPartial (fun z => ∑ j ∈ u, c j * h j z) α (x, t) =
      ∑ j ∈ u, c j * multiPartial (h j) α (x, t) := by
  have hG_mul : ∀ j ∈ u, ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => c j * h j (x, t)) s := by
    intro j hj
    have h_smul := (hG j hj).const_smul (c j)
    simpa [smul_eq_mul] using h_smul
  rw [multiPartial_finset_sum hs t hG_mul α hx]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [multiPartial_const_smul hs t (hG j hj) α (c j) hx]

theorem abs_multiPartial_finset_sum_le {ι : Type*} {h : ι → ParabolicPoint → ℝ} {u : Finset ι}
    {s : Set Vec3} (hs : IsOpen s) (t : ℝ)
    (hG : ∀ j ∈ u, ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h j (x, t)) s)
    (α : Fin 3 → ℕ) {x : Vec3} (hx : x ∈ s) :
    |multiPartial (fun z => ∑ j ∈ u, h j z) α (x, t)| ≤ ∑ j ∈ u, |multiPartial (h j) α (x, t)| := by
  rw [multiPartial_finset_sum hs t hG α hx]
  simpa [Real.norm_eq_abs] using norm_sum_le u (fun j => multiPartial (h j) α (x, t))

end CIV
