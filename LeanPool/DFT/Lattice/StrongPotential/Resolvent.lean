/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.StrongPotential.PowerSums
import Mathlib.Algebra.BigOperators.Field
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.Ring

/-!
# Explicit divided-difference coefficients

`alpha_rec`, `alpha_sum`, the resolvent route sum `Fres`, its recursion `Fres_rec`, and the explicit
diagonal coefficient `alpha_diag : α_y(y) = [y = c] + Σ_{p pred y} A_{yp} Fres_p(w_y)`.
-/

@[expose] public section

namespace DFT

section

open Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

section
variable {A : Matrix C C ℝ} {w : C → ℝ} (hw : Function.Injective w) {d : C → ℕ} (hL : Lip A d)
  {c : C} (hc : d c = 0)

/-- Source term of the recursion. -/
noncomputable def Ssrc (y z : C) : ℝ :=
  ∑ p ∈ Finset.univ.erase y, (if d p + 1 = d y then A y p * alphaRep A w hw d hL c hc p z else 0)

lemma alpha_rec (y z : C) :
    alphaRep A w hw d hL c hc y z * (w z - w y) = Ssrc hw hL hc y z := by
  have h : ∀ k : ℕ, ∑ z', (alphaRep A w hw d hL c hc y z' * w z') * w z' ^ k =
      ∑ z', (w y * alphaRep A w hw d hL c hc y z' + Ssrc hw hL hc y z') * w z' ^ k := by
    intro k
    have e1 : ∑ z', (alphaRep A w hw d hL c hc y z' * w z') * w z' ^ k = T A w d c (k + 1) y := by
      rw [alphaRep_rep hw hL hc]; apply Finset.sum_congr rfl; intro z' _; ring
    rw [e1, T_succ w hL hc, alphaRep_rep hw hL hc, Finset.mul_sum]
    simp only [Ssrc, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl; intro z' _; ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro p _
      split_ifs
      · rw [alphaRep_rep hw hL hc, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro z' _; ring
      · simp
  have key := ps_unique _ _ _ _ h (w z)
  have hfilt : Finset.univ.filter (fun z' => w z' = w z) = {z} := by
    ext z'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hw h, fun h => h ▸ rfl⟩
  rw [hfilt, Finset.sum_singleton, Finset.sum_singleton] at key
  linarith

lemma alpha_sum (y : C) : ∑ z, alphaRep A w hw d hL c hc y z = if y = c then 1 else 0 := by
  have := alphaRep_rep hw hL hc y 0
  simp only [pow_zero, mul_one] at this
  rw [← this, T_zero w hc]

/-- Resolvent route sum. -/
noncomputable def Fres (y : C) (x : ℝ) : ℝ := ∑ z, alphaRep A w hw d hL c hc y z / (x - w z)

lemma Ssrc_self (y : C) : Ssrc hw hL hc y y = 0 := by
  apply Finset.sum_eq_zero; intro p hp
  split_ifs with hdp
  · have : alphaRep A w hw d hL c hc p y = 0 := by
      by_contra hne
      rcases alphaRep_supp hw hL hc p y hne with h | h
      · exact (Finset.mem_erase.mp hp).1 h.symm
      · omega
    rw [this, mul_zero]
  · rfl

/-- Interchange the source and configuration sums in the resolvent. -/
theorem source_sum (y : C) (x : ℝ) :
    ∑ z, Ssrc hw hL hc y z / (x - w z) =
      ∑ p ∈ Finset.univ.erase y, (if d p + 1 = d y then A y p * Fres hw hL hc p x else 0) := by
  simp only [Ssrc, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  split_ifs
  · simp only [Fres, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro z _; ring
  · simp

/-- **Explicit diagonal coefficient.** -/
theorem alpha_diag (y : C) :
    alphaRep A w hw d hL c hc y y = (if y = c then 1 else 0) +
      ∑ p ∈ Finset.univ.erase y, (if d p + 1 = d y then A y p * Fres hw hL hc p (w y) else 0) := by
  have hs := alpha_sum hw hL hc y
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y)] at hs
  have hoff : ∀ z ∈ Finset.univ.erase y, alphaRep A w hw d hL c hc y z =
      Ssrc hw hL hc y z / (w z - w y) := by
    intro z hz
    have hne : w z - w y ≠ 0 := sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hz).1 (hw h))
    rw [← alpha_rec hw hL hc y z]; field_simp
  rw [Finset.sum_congr rfl hoff] at hs
  have hS : ∑ z ∈ Finset.univ.erase y, Ssrc hw hL hc y z / (w z - w y) =
      -∑ z, Ssrc hw hL hc y z / (w y - w z) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y), Ssrc_self, zero_div, zero_add,
        ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro z _
    rw [← neg_sub, div_neg]
  rw [hS] at hs
  rw [source_sum hw hL hc y (w y)] at hs
  linarith

/-- **Resolvent recursion** (away from the poles of the relevant layers). -/
theorem Fres_rec (y : C) (x : ℝ) (hx : ∀ z, d z ≤ d y → x ≠ w z) :
    Fres hw hL hc y x * (x - w y) = (if y = c then 1 else 0) +
      ∑ p ∈ Finset.univ.erase y, (if d p + 1 = d y then A y p * Fres hw hL hc p x else 0) := by
  have hsupp : ∀ z, alphaRep A w hw d hL c hc y z ≠ 0 → x - w z ≠ 0 := by
    intro z hz
    rcases alphaRep_supp hw hL hc y z hz with h | h
    · subst h; exact sub_ne_zero.mpr (hx z le_rfl)
    · exact sub_ne_zero.mpr (hx z h.le)
  have e1 : Fres hw hL hc y x * (x - w y) =
      ∑ z, alphaRep A w hw d hL c hc y z + ∑ z, Ssrc hw hL hc y z / (x - w z) := by
    simp only [Fres, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro z _
    by_cases hz : alphaRep A w hw d hL c hc y z = 0
    · have : Ssrc hw hL hc y z = 0 := by
        rw [← alpha_rec hw hL hc y z, hz, zero_mul]
      rw [hz, this]; simp
    · have hne := hsupp z hz
      rw [← alpha_rec hw hL hc y z]; field_simp; ring
  rw [e1, alpha_sum]
  rw [source_sum hw hL hc y x]

end

end

end DFT
