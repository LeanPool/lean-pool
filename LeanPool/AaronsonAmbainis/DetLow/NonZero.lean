/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import LeanPool.AaronsonAmbainis.DetLow.Basic

/-!
# DetLow: the determinant of the agreement matrix is nonzero

This is Lemma 3.4 of the paper.
Evaluate every variable at the real number `c = 2 ^ n` (`n = Fintype.card ι`). The evaluated
matrix has diagonal entries `c ^ n` and off-diagonal entries `c ^ k` with `k + 1 ≤ n`, and a row
has fewer than `2 ^ n = c` off-diagonal entries, so the matrix is strictly diagonally dominant
and its determinant is nonzero (Gershgorin: `det_ne_zero_of_sum_row_lt_diag`).
-/

@[expose] public section

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Evaluation of all variables at the real number `c`. -/
noncomputable def evalAt (c : ℝ) : MvPolynomial ι ℤ →+* ℝ :=
  eval₂Hom (Int.castRingHom ℝ) (fun _ => c)

/-- The number of coordinates in which `x` and `z` agree. -/
def agCount (x z : Cube ι) : ℕ := (univ.filter fun i => x i = z i).card

omit [DecidableEq ι] in
theorem evalAt_agMon (c : ℝ) (x z : Cube ι) :
    evalAt c (agMon x z) = c ^ agCount x z := by
  have h : ∀ i, evalAt c (if x i = z i then (X i : MvPolynomial ι ℤ) else 1)
      = if x i = z i then c else 1 := by
    intro i
    by_cases hi : x i = z i
    · rw [ite_eq_left hi, ite_eq_left hi]
      simp [evalAt]
    · rw [ite_eq_right hi, ite_eq_right hi, map_one]
  unfold agMon agCount
  rw [map_prod]
  simp_rw [h]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

omit [DecidableEq ι] in
theorem agCount_self (x : Cube ι) : agCount x x = Fintype.card ι := by
  simp [agCount]

omit [DecidableEq ι] in
theorem agCount_lt (x z : Cube ι) (h : x ≠ z) : agCount x z < Fintype.card ι := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  unfold agCount
  rw [← Finset.card_univ]
  apply Finset.card_lt_card
  rw [Finset.filter_ssubset]
  exact ⟨i, mem_univ i, hi⟩

theorem evalMat_apply (c : ℝ) (g : Cube ι → Bool) (x z : Ones g) :
    (evalAt c).mapMatrix (agMatrix g) x z = c ^ agCount x.1 z.1 :=
  evalAt_agMon c x.1 z.1

/-- A row of the ones of `g` has fewer than `2 ^ n` off-diagonal entries. -/
theorem card_erase_succ_le (g : Cube ι → Bool) (x : Ones g) :
    (univ.erase x).card + 1 ≤ 2 ^ Fintype.card ι := by
  have h2 : (univ.erase x).card < (univ : Finset (Ones g)).card :=
    Finset.card_erase_lt_of_mem (mem_univ x)
  have h3 : (univ : Finset (Ones g)).card ≤ 2 ^ Fintype.card ι := by
    rw [Finset.card_univ]
    calc Fintype.card (Ones g) ≤ Fintype.card (Cube ι) := Fintype.card_subtype_le _
      _ = 2 ^ Fintype.card ι := by simp
  omega

/-- The evaluated matrix is strictly diagonally dominant when `c = 2 ^ n`. -/
theorem evalMat_dominant (g : Cube ι → Bool) (c : ℝ) (hc : c = 2 ^ Fintype.card ι)
    (x : Ones g) :
    ∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖
      < ‖(evalAt c).mapMatrix (agMatrix g) x x‖ := by
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hc]
    exact one_le_pow₀ (by norm_num)
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcard : ((univ.erase x).card : ℝ) + 1 ≤ c := by
    rw [hc]
    exact_mod_cast card_erase_succ_le g x
  have hpow : 0 < c ^ Fintype.card ι := pow_pos hcpos _
  have hdiag : ‖(evalAt c).mapMatrix (agMatrix g) x x‖ = c ^ Fintype.card ι := by
    rw [evalMat_apply, agCount_self, Real.norm_of_nonneg (pow_nonneg hcpos.le _)]
  have hsum : (∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖) * c
      ≤ ((univ.erase x).card : ℝ) * c ^ Fintype.card ι := by
    rw [Finset.sum_mul]
    calc ∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖ * c
        ≤ ∑ _z ∈ univ.erase x, c ^ Fintype.card ι := by
          apply Finset.sum_le_sum
          intro z hz
          have hzx : x.1 ≠ z.1 := fun h => (Finset.ne_of_mem_erase hz) (Subtype.ext h.symm)
          rw [evalMat_apply, Real.norm_of_nonneg (pow_nonneg hcpos.le _), ← pow_succ]
          exact pow_le_pow_right₀ hc1 (agCount_lt x.1 z.1 hzx)
      _ = ((univ.erase x).card : ℝ) * c ^ Fintype.card ι := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [hdiag]
  have hlt : (∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖) * c
      < c ^ Fintype.card ι * c := by
    calc (∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖) * c
        ≤ ((univ.erase x).card : ℝ) * c ^ Fintype.card ι := hsum
      _ < c * c ^ Fintype.card ι := by
          apply mul_lt_mul_of_pos_right _ hpow
          linarith
      _ = c ^ Fintype.card ι * c := mul_comm _ _
  exact lt_of_mul_lt_mul_right hlt hcpos.le

/-- Lemma 3.4 of the paper: the determinant of the agreement matrix is nonzero. -/
theorem agMatrix_det_ne_zero (g : Cube ι → Bool) : (agMatrix g).det ≠ 0 := by
  intro h0
  have hne : ((evalAt ((2 : ℝ) ^ Fintype.card ι)).mapMatrix (agMatrix g)).det ≠ 0 :=
    det_ne_zero_of_sum_row_lt_diag (fun x => evalMat_dominant g _ rfl x)
  apply hne
  rw [← RingHom.map_det, h0, map_zero]

end DetLow
end AaronsonAmbainis
