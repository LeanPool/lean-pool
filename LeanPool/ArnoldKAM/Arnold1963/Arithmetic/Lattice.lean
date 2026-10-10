/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Spaces
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
Counting integer lattice shells in the sum-of-absolute-coordinates norm. Natural lengths are
proved equal to the public real-valued indexLength. All mode cutoffs are strict.
-/

@[expose] public section

noncomputable section

namespace KamProject.Arnold1963

/-- The integer-valued sum of absolute Fourier coordinates, used to enumerate shells. -/
def latticeLength {n : ℕ} (k : FourierIndex n) : ℕ := ∑ j, (k j).natAbs

theorem indexLength_eq_latticeLength {n : ℕ} (k : FourierIndex n) :
    indexLength k = (latticeLength k : ℝ) := by
  simp [indexLength, latticeLength, Nat.cast_sum]

theorem natAbs_le_latticeLength {n : ℕ} (k : FourierIndex n) (j : Fin n) :
    (k j).natAbs ≤ latticeLength k := by
  exact Finset.single_le_sum (f := fun i => (k i).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

@[simp] theorem latticeLength_zero {n : ℕ} : latticeLength (0 : FourierIndex n) = 0 := by
  simp [latticeLength]

@[simp] theorem latticeLength_eq_zero {n : ℕ} (k : FourierIndex n) :
    latticeLength k = 0 ↔ k = 0 := by
  constructor
  · intro h
    funext j
    have := natAbs_le_latticeLength k j
    simp_all
  · rintro rfl
    simp

theorem latticeLength_cons {n : ℕ} (a : ℤ) (k : FourierIndex n) :
    latticeLength (Fin.cons a k) = a.natAbs + latticeLength k := by
  simp [latticeLength, Fin.sum_univ_succ]

/-- The finite integer coordinate box containing every shell of the given radius. -/
def latticeBox (n m : ℕ) : Finset (FourierIndex n) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(m : ℤ)) (m : ℤ))

/-- The finite shell of integer indices with the specified sum of absolute coordinates. -/
def latticeShell (n m : ℕ) : Finset (FourierIndex n) :=
  (latticeBox n m).filter (fun k => latticeLength k = m)

@[simp] theorem mem_latticeShell {n m : ℕ} {k : FourierIndex n} :
    k ∈ latticeShell n m ↔ latticeLength k = m := by
  simp only [latticeShell, Finset.mem_filter, and_iff_right_iff_imp]
  intro h
  apply Fintype.mem_piFinset.2
  intro j
  have := natAbs_le_latticeLength k j
  simp only [Finset.mem_Icc]
  omega

@[simp] theorem latticeShell_zero (n : ℕ) : latticeShell n 0 = {0} := by
  ext k
  simp

theorem card_shell_fiber_le (n m : ℕ) (a : ℤ) :
    ((latticeShell (n + 1) m).filter (fun k => k 0 = a)).card ≤
      (latticeShell n (m - a.natAbs)).card := by
  apply Finset.card_le_card_of_injOn Fin.tail
  · intro k hk
    obtain ⟨hk, ha⟩ := Finset.mem_filter.mp hk
    have hlen := mem_latticeShell.mp hk
    have heq : latticeLength k = (k 0).natAbs + latticeLength (Fin.tail k) := by
      conv_lhs => rw [← Fin.cons_self_tail k]
      exact latticeLength_cons _ _
    apply mem_latticeShell.mpr
    omega
  · intro k hk l hl hkl
    have hk0 := (Finset.mem_filter.mp hk).2
    have hl0 := (Finset.mem_filter.mp hl).2
    rw [← Fin.cons_self_tail k, ← Fin.cons_self_tail l, hk0, hl0, hkl]

theorem card_latticeShell_one_le (m : ℕ) : (latticeShell 1 m).card ≤ 2 := by
  have h : (latticeShell 1 m).card ≤ ({(m : ℤ), -(m : ℤ)} : Finset ℤ).card := by
    apply Finset.card_le_card_of_injOn (fun k => k 0)
    · intro k hk
      have hlen : (k 0).natAbs = m := by simpa [latticeLength] using mem_latticeShell.mp hk
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      omega
    · intro k hk l hl heq
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      simpa [hj] using heq
  exact h.trans ((Finset.card_insert_le _ _).trans_eq (by simp))

theorem card_latticeShell_le (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (latticeShell n m).card ≤ 2 ^ n * m ^ (n - 1) := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa using card_latticeShell_one_le m
    have hn : 0 < n := Nat.pos_of_ne_zero hn0
    let C := 2 ^ n * m ^ (n - 1)
    let fiber := fun a : ℤ => ((latticeShell (n + 1) m).filter (fun k => k 0 = a)).card
    have hC : 2 ≤ C := by
      calc
        2 = (2 : ℕ) ^ 1 * 1 := by norm_num
        _ ≤ 2 ^ n * m ^ (n - 1) :=
          Nat.mul_le_mul (pow_le_pow_right' (by omega) hn) (one_le_pow₀ (by omega))
    have hend (a : ℤ) (ha : a.natAbs = m) : fiber a ≤ 1 := by
      have := card_shell_fiber_le n m a
      simpa [fiber, ha] using this
    have hint (a : ℤ) (ha : a ∈ Finset.Ioo (-(m : ℤ)) (m : ℤ)) : fiber a ≤ C := by
      have ha' : a.natAbs < m := by simp only [Finset.mem_Ioo] at ha; omega
      exact (card_shell_fiber_le n m a).trans
        ((ih (m - a.natAbs) hn (by omega)).trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le m _) (n - 1))))
    have hsum : (latticeShell (n + 1) m).card =
        ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), fiber a := by
      apply Finset.card_eq_sum_card_fiberwise
      intro k hk
      have hlen := mem_latticeShell.mp hk
      have := natAbs_le_latticeLength k 0
      simp only [Finset.mem_coe, Finset.mem_Icc]
      omega
    have hsplit : Finset.Icc (-(m : ℤ)) (m : ℤ) =
        insert (-(m : ℤ)) (insert (m : ℤ) (Finset.Ioo (-(m : ℤ)) (m : ℤ))) := by
      rw [Finset.Ioo_insert_right (by omega), Finset.Ioc_insert_left (by omega)]
    have hcount : (Finset.Ioo (-(m : ℤ)) (m : ℤ)).card = 2 * m - 1 := by
      rw [Int.card_Ioo]
      omega
    have hbound : (latticeShell (n + 1) m).card ≤ 2 + (2 * m - 1) * C := by
      rw [hsum, hsplit, Finset.sum_insert (by simp; omega),
        Finset.sum_insert (by simp)]
      have hneg := hend (-(m : ℤ)) (by simp)
      have hpos := hend (m : ℤ) (by simp)
      have hmid : (∑ a ∈ Finset.Ioo (-(m : ℤ)) (m : ℤ), fiber a) ≤ (2 * m - 1) * C := by
        calc
          _ ≤ ∑ _a ∈ Finset.Ioo (-(m : ℤ)) (m : ℤ), C := Finset.sum_le_sum hint
          _ = _ := by simp [hcount]
      omega
    calc
      _ ≤ 2 + (2 * m - 1) * C := hbound
      _ ≤ (2 * m) * C := by nlinarith [Nat.sub_add_cancel (show 1 ≤ 2 * m by omega)]
      _ = 2 ^ (n + 1) * m ^ ((n + 1) - 1) := by
        dsimp [C]
        simp only [pow_succ]
        have hp : m ^ (n - 1) * m = m ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
        calc
          _ = (2 ^ n * 2) * (m ^ (n - 1) * m) := by ring
          _ = _ := by rw [hp]

/-- The finite union of nonzero lattice shells through the specified radius. -/
def nonzeroLatticeBall (n M : ℕ) : Finset (FourierIndex n) :=
  (Finset.Icc 1 M).biUnion (latticeShell n)

@[simp] theorem mem_nonzeroLatticeBall {n M : ℕ} {k : FourierIndex n} :
    k ∈ nonzeroLatticeBall n M ↔ 0 < latticeLength k ∧ latticeLength k ≤ M := by
  simp only [nonzeroLatticeBall, Finset.mem_biUnion, Finset.mem_Icc, mem_latticeShell]
  constructor
  · rintro ⟨i, hi, hlen⟩
    omega
  · intro h
    exact ⟨latticeLength k, by omega, rfl⟩

theorem card_nonzeroLatticeBall_le (n M : ℕ) (hn : 0 < n) :
    (nonzeroLatticeBall n M).card ≤ 2 ^ n * M ^ n := by
  by_cases hM : M = 0
  · subst M
    simp [nonzeroLatticeBall]
  have hM : 0 < M := Nat.pos_of_ne_zero hM
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 M, (latticeShell n r).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ Finset.Icc 1 M, 2 ^ n * M ^ (n - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr := Finset.mem_Icc.mp hr
      exact (card_latticeShell_le n r hn hr.1).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr.2 (n - 1)))
    _ = 2 ^ n * M ^ n := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_id]
      have hp : M ^ (n - 1) * M = M ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]
      calc
        _ = 2 ^ n * (M ^ (n - 1) * M) := by ring
        _ = _ := by rw [hp]

/-- Nonzero Fourier indices with length strictly below the real cutoff. -/
def lowModes (n : ℕ) (N : ℝ) : Finset (FourierIndex n) :=
  nonzeroLatticeBall n (⌈N⌉₊ - 1)

@[simp] theorem mem_lowModes {n : ℕ} {N : ℝ} {k : FourierIndex n} :
    k ∈ lowModes n N ↔ 0 < indexLength k ∧ indexLength k < N := by
  rw [lowModes, mem_nonzeroLatticeBall, indexLength_eq_latticeLength]
  rw [Nat.cast_pos, ← Nat.lt_ceil]
  omega

/-- Fourier modes below the cutoff, including zero when the cutoff is positive. -/
def fourierModes (n : ℕ) (N : ℝ) : Finset (FourierIndex n) :=
  if 0 < N then insert 0 (lowModes n N) else ∅

@[simp] theorem mem_fourierModes {n : ℕ} {N : ℝ} {k : FourierIndex n} :
    k ∈ fourierModes n N ↔ indexLength k < N := by
  classical
  have hnonneg := indexLength_nonneg k
  have hzero : indexLength k = 0 ↔ k = 0 := by
    rw [indexLength_eq_latticeLength, Nat.cast_eq_zero, latticeLength_eq_zero]
  by_cases hN : 0 < N
  · simp only [fourierModes, ite_eq_left hN, Finset.mem_insert, mem_lowModes]
    constructor
    · rintro (rfl | h)
      · simpa [indexLength] using hN
      · exact h.2
    · intro h
      by_cases hk : k = 0
      · exact Or.inl hk
      · exact Or.inr ⟨lt_of_le_of_ne hnonneg (Ne.symm (mt hzero.mp hk)), h⟩
  · simp only [fourierModes, ite_eq_right hN, Finset.notMem_empty, false_iff, not_lt]
    exact (le_of_not_gt hN).trans hnonneg

theorem not_mem_fourierModes {n : ℕ} {N : ℝ} {k : FourierIndex n} :
    k ∉ fourierModes n N ↔ N ≤ indexLength k := by
  simp

theorem fourierModes_eq_insert_lowModes (n : ℕ) {N : ℝ} (hN : 0 < N) :
    fourierModes n N = insert 0 (lowModes n N) := by
  simp [fourierModes, hN]

theorem card_lowModes_le {n : ℕ} {N : ℝ} (hn : 0 < n) (hN : 1 < N) :
    ((lowModes n N).card : ℝ) ≤ (2 : ℝ) ^ n * N ^ n := by
  have hceil : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hbound : ((⌈N⌉₊ - 1 : ℕ) : ℝ) ≤ N := by
    rw [Nat.cast_sub hceil, Nat.cast_one]
    have := Nat.ceil_lt_add_one (show 0 ≤ N by linarith)
    linarith
  calc
    _ ≤ ((2 ^ n * (⌈N⌉₊ - 1) ^ n : ℕ) : ℝ) := by
      exact_mod_cast card_nonzeroLatticeBall_le n (⌈N⌉₊ - 1) hn
    _ = (2 : ℝ) ^ n * ((⌈N⌉₊ - 1 : ℕ) : ℝ) ^ n := by norm_cast
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hbound n) (by positivity)

end KamProject.Arnold1963
