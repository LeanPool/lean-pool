/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ChainCoordinates
public import LeanPool.ShellsortMean.SubsetBits

/-! Coordinates and counts of threshold bits inside a gap chain. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- The tag bit is a dummy coordinate and does not belong to the smaller-key subset. -/
def fullBitsSubset {n : ℕ} (i : Fin n) (z : Fin n → Bool) : Finset (Fin n) :=
  subsetOfBits i (fun a => z a.val)

theorem mem_fullBitsSubset {n : ℕ} (i a : Fin n) (z : Fin n → Bool) :
    a ∈ fullBitsSubset i z ↔ a ≠ i ∧ z a = true := by
  by_cases hai : a = i
  · subst a
    simp [fullBitsSubset, self_not_mem_subsetOfBits]
  · simpa [fullBitsSubset, hai] using
      (mem_subsetOfBits i (fun j => z j.val) ⟨a, hai⟩)

theorem fullBitsSubset_filter {n : ℕ} (i : Fin n) (z : Fin n → Bool) :
    fullBitsSubset i z = Finset.univ.filter (fun a => a ≠ i ∧ z a = true) := by
  ext a
  simp only [mem_fullBitsSubset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The restriction of a slot-indexed bit vector to one gap chain in slot order. -/
def chainBits {n h : ℕ} (hh : 0 < h) (z : Fin n → Bool) (s : Fin h) :
    Fin (sourceTrialLength (n / h) (n % h) s.val) → Bool :=
  fun v => z ((positionChainEquiv n h hh).symm ⟨s, v⟩)

theorem fullBits_chain_count {n h : ℕ} (hh : 0 < h)
    (i : Fin n) (z : Fin n → Bool) (s : Fin h) :
    chainLowerCount (fullBitsSubset i z) h s.val =
      ∑ v : Fin (sourceTrialLength (n / h) (n % h) s.val),
        if (positionChainEquiv n h hh).symm ⟨s, v⟩ ≠ i ∧ chainBits hh z s v = true
        then 1 else 0 := by
  rw [chainLowerCount, fullBitsSubset_filter, Finset.filter_filter]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← (positionChainEquiv n h hh).symm.sum_comp]
  rw [Fintype.sum_sigma]
  simp only [positionChainEquiv_symm_residue]
  have hf : ∀ q : Fin h,
      (∑ v : Fin (sourceTrialLength (n / h) (n % h) q.val),
        if (((positionChainEquiv n h hh).symm ⟨q, v⟩ ≠ i ∧
          z ((positionChainEquiv n h hh).symm ⟨q, v⟩) = true) ∧ q.val = s.val)
        then 1 else 0) =
      if q = s then (∑ v : Fin (sourceTrialLength (n / h) (n % h) q.val),
        if (positionChainEquiv n h hh).symm ⟨q, v⟩ ≠ i ∧ chainBits hh z q v = true
        then 1 else 0) else 0 := by
    intro q
    by_cases hqs : q = s
    · subst q
      simp only [ite_true, and_true, chainBits]
      rfl
    · have hval : q.val ≠ s.val := fun he => hqs (Fin.ext he)
      simp only [hval, and_false, ite_false, hqs, Finset.sum_const_zero]
  simp_rw [hf]
  simp

/-- A non-owner chain contains every original position of that chain, so its
smaller-key count is exactly the Bernoulli vector count. -/
theorem nonowner_fullBits_chain_count {n h : ℕ} (hh : 0 < h)
    (i : Fin n) (z : Fin n → Bool) (s : Fin h) (hs : s.val ≠ i.val % h) :
    chainLowerCount (fullBitsSubset i z) h s.val = bitCount (chainBits hh z s) := by
  rw [fullBits_chain_count hh i z s]
  unfold bitCount
  apply Finset.sum_congr rfl
  intro v _
  have hne : (positionChainEquiv n h hh).symm ⟨s, v⟩ ≠ i := by
    intro he
    have hm := congrArg (fun a : Fin n => a.val % h) he
    rw [positionChainEquiv_symm_residue] at hm
    exact hs hm
  simp [hne]

/-- The owner bit is omitted from its own chain count. -/
def ownerBitCount {L : ℕ} (o : Fin L) (z : Fin L → Bool) : ℕ :=
  ∑ v : Fin L, if v ≠ o ∧ z v = true then 1 else 0

theorem owner_coordinate_eq_iff {n h : ℕ} (hh : 0 < h) (i : Fin n)
    (v : Fin (sourceTrialLength (n / h) (n % h)
      ((positionChainEquiv n h hh) i).1.val)) :
    (positionChainEquiv n h hh).symm ⟨((positionChainEquiv n h hh) i).1, v⟩ = i ↔
      v = ((positionChainEquiv n h hh) i).2 := by
  constructor
  · intro he
    have hc := congrArg (positionChainEquiv n h hh) he
    simp only [Equiv.apply_symm_apply] at hc
    exact eq_of_heq (Sigma.mk.inj_iff.mp hc).2
  · intro he
    subst v
    exact (positionChainEquiv n h hh).symm_apply_apply i

theorem owner_fullBits_chain_count {n h : ℕ} (hh : 0 < h)
    (i : Fin n) (z : Fin n → Bool) :
    chainLowerCount (fullBitsSubset i z) h (((positionChainEquiv n h hh) i).1.val) =
      ownerBitCount (((positionChainEquiv n h hh) i).2)
        (chainBits hh z (((positionChainEquiv n h hh) i).1)) := by
  rw [fullBits_chain_count hh i z (((positionChainEquiv n h hh) i).1)]
  unfold ownerBitCount
  apply Finset.sum_congr rfl
  intro v _
  simp only [ne_eq, owner_coordinate_eq_iff hh i v]

/-- Full original-position bits and all actual chain bit-vectors are equivalent. -/
def positionBitsEquiv (n h : ℕ) (hh : 0 < h) :
    (Fin n → Bool) ≃
      (∀ s : Fin h, Fin (sourceTrialLength (n / h) (n % h) s.val) → Bool) where
  toFun z := chainBits hh z
  invFun x a := x (((positionChainEquiv n h hh) a).1)
    (((positionChainEquiv n h hh) a).2)
  left_inv z := by
    funext a
    exact congrArg z ((positionChainEquiv n h hh).symm_apply_apply a)
  right_inv x := by
    funext s v
    change x (((positionChainEquiv n h hh)
      ((positionChainEquiv n h hh).symm ⟨s, v⟩)).1)
      (((positionChainEquiv n h hh)
      ((positionChainEquiv n h hh).symm ⟨s, v⟩)).2) = x s v
    exact congrArg (fun c : ChainCoordinate n h => x c.1 c.2)
      ((positionChainEquiv n h hh).apply_symm_apply ⟨s, v⟩)

theorem positionBitsEquiv_apply {n h : ℕ} (hh : 0 < h) (z : Fin n → Bool) :
    positionBitsEquiv n h hh z = chainBits hh z := rfl

theorem chainBits_reassemble {n h : ℕ} (hh : 0 < h)
    (x : ∀ s : Fin h, Fin (sourceTrialLength (n / h) (n % h) s.val) → Bool) :
    chainBits hh ((positionBitsEquiv n h hh).symm x) = x :=
  (positionBitsEquiv n h hh).apply_symm_apply x

end Shellsort
end
