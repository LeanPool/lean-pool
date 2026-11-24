/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, diagnostics, and proof consolidation. -/

module

public import LeanPool.ShellsortMean.ConditionalSource
public import LeanPool.ShellsortMean.SourceDecomposition

/-! An equivalence between physical slots and residue-chain coordinates. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Actual finite chain coordinates, including the n mod h long-chain boundary. -/
abbrev ChainCoordinate (n h : ℕ) :=
  Σ s : Fin h, Fin (sourceTrialLength (n / h) (n % h) s.val)

theorem actual_chain_length (n h : ℕ) (hh : 0 < h) (s : Fin h) :
    (chainPositions n h s.val).card = sourceTrialLength (n / h) (n % h) s.val := by
  rw [chainPositions_card, residuePrefixCount_formula h s.val n hh s.isLt]
  unfold sourceTrialLength
  split_ifs <;> simp

theorem actual_chain_prefix_lt (n h : ℕ) (hh : 0 < h) (s : Fin h)
    (v : Fin (sourceTrialLength (n / h) (n % h) s.val)) :
    s.val + h * v.val < n := by
  apply source_prefix_position_lt (Finset.univ : Finset (Fin n)) h s.val v.val hh s.isLt
  change v.val < (chainPositions n h s.val).card
  rw [actual_chain_length n h hh s]
  exact v.isLt

theorem actual_chain_quotient_lt {n h : ℕ} (i : Fin n) :
    i.val / h < sourceTrialLength (n / h) (n % h) (i.val % h) := by
  have hi := i.isLt
  have hiE := Nat.mod_add_div i.val h
  have hnE := Nat.mod_add_div n h
  have hq : i.val / h ≤ n / h := Nat.div_le_div_right (Nat.le_of_lt hi)
  unfold sourceTrialLength
  split_ifs with hr
  · omega
  · by_contra hnot
    have he : i.val / h = n / h := by omega
    rw [he] at hiE
    omega

/-- Explicit residue/quotient coordinates for every original position. -/
def positionChainEquiv (n h : ℕ) (hh : 0 < h) : Fin n ≃ ChainCoordinate n h where
  toFun i := ⟨⟨i.val % h, Nat.mod_lt _ hh⟩, ⟨i.val / h, actual_chain_quotient_lt i⟩⟩
  invFun c := ⟨c.1.val + h * c.2.val, actual_chain_prefix_lt n h hh c.1 c.2⟩
  left_inv i := Fin.ext (Nat.mod_add_div i.val h)
  right_inv c := by
    rcases c with ⟨⟨s, hs⟩, ⟨v, hv⟩⟩
    have hm : (s + h * v) % h = s := by simp [Nat.add_mod, Nat.mod_eq_of_lt hs]
    have hd : (s + h * v) / h = v := by
      rw [Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hs, Nat.zero_add]
    apply Sigma.ext (Fin.ext hm)
    apply (Fin.heq_ext_iff (by dsimp only; rw [hm])).mpr
    exact hd

theorem positionChainEquiv_residue (n h : ℕ) (hh : 0 < h) (i : Fin n) :
    ((positionChainEquiv n h hh) i).1.val = i.val % h := rfl

theorem positionChainEquiv_ordinal (n h : ℕ) (hh : 0 < h) (i : Fin n) :
    ((positionChainEquiv n h hh) i).2.val = i.val / h := rfl

theorem positionChainEquiv_symm_val (n h : ℕ) (hh : 0 < h) (c : ChainCoordinate n h) :
    ((positionChainEquiv n h hh).symm c).val = c.1.val + h * c.2.val := rfl

theorem positionChainEquiv_symm_residue (n h : ℕ) (hh : 0 < h)
    (c : ChainCoordinate n h) :
    ((positionChainEquiv n h hh).symm c).val % h = c.1.val := by
  rw [positionChainEquiv_symm_val]
  simp [Nat.add_mod, Nat.mod_eq_of_lt c.1.isLt]

end Shellsort
end
