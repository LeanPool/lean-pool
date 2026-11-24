/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.GapInsertionBridge
public import Mathlib.Data.List.FinRange

/-! Equivalence of the insertion output of a chain and the rank-based gap sort. -/

@[expose] public noncomputable section
namespace Shellsort

theorem chainKeys_injective {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (s : Fin k) : Function.Injective (chainKeys p k hk s) := by
  intro v w h
  have hp := p.symm.injective h
  have hc := (positionChainEquiv n k hk).symm.injective hp
  exact eq_of_heq (Sigma.mk.inj_iff.mp hc).2

theorem chainKeys_mem_iff {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (s : Fin k) (x : Fin n) :
    x ∈ List.ofFn (chainKeys p k hk s) ↔ (p x).val % k = s.val := by
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := List.mem_ofFn.mp hx
    have hp := congrArg p hv
    simp only [chainKeys, Equiv.apply_symm_apply] at hp
    rw [← hp, positionChainEquiv_symm_residue]
  · intro hx
    let v : Fin (sourceTrialLength (n / k) (n % k) s.val) :=
      ⟨(p x).val / k, by rw [← hx]; exact actual_chain_quotient_lt hk (p x)⟩
    apply List.mem_ofFn.mpr
    refine ⟨v, ?_⟩
    have hp : (positionChainEquiv n k hk).symm ⟨s, v⟩ = p x := by
      apply Fin.ext
      change s.val + k * ((p x).val / k) = (p x).val
      simpa only [hx] using Nat.mod_add_div (p x).val k
    change p.symm ((positionChainEquiv n k hk).symm ⟨s, v⟩) = x
    rw [hp, Equiv.symm_apply_apply]

theorem gapSort_chainKeys_sorted {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (s : Fin k) :
    (List.ofFn (chainKeys (gapSort p k) k hk s)).Pairwise (fun x y => x ≤ y) := by
  apply List.pairwise_ofFn.mpr
  intro v w hvw
  apply le_of_lt
  have hs := gapSort_sorted p k (chainKeys (gapSort p k) k hk s v)
    (chainKeys (gapSort p k) k hk s w)
    (by simp only [chainKeys, Equiv.apply_symm_apply, positionChainEquiv_symm_residue])
  apply hs.mp
  simp only [chainKeys, Equiv.apply_symm_apply]
  exact (chainPosition_lt_iff n k hk s v w).mpr hvw

theorem gapSort_chainKeys_perm {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (s : Fin k) :
    (List.ofFn (chainKeys (gapSort p k) k hk s)).Perm
      (List.ofFn (chainKeys p k hk s)) := by
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_ofFn_ofInjective (chainKeys_injective (gapSort p k) k hk s))
    (List.nodup_ofFn_ofInjective (chainKeys_injective p k hk s))).mpr
  intro x
  rw [chainKeys_mem_iff, chainKeys_mem_iff, gapSort_preserves_residue]

/-- The actual insertion program returns exactly the pre-existing gapSort
checkpoint on every chain, not merely a list with the same inversion counter. -/
theorem insertionExecution_chain_eq_gapSort {n : ℕ} (p : RankPlacement n)
    (k : ℕ) (hk : 0 < k) (s : Fin k) :
    (insertionExecution (List.ofFn (chainKeys p k hk s))).1 =
      List.ofFn (chainKeys (gapSort p k) k hk s) := by
  exact List.Perm.eq_of_pairwise'
    (insertionExecution_sorted _) (gapSort_chainKeys_sorted p k hk s)
    ((insertionExecution_perm _).trans (gapSort_chainKeys_perm p k hk s).symm)

/-- The key returned at physical slot i after executing insertion on its chain. -/
def gapInsertionOutputAt {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (i : Fin n) : Fin n :=
  let c := (positionChainEquiv n k hk) i
  let output := (insertionExecution (List.ofFn (chainKeys p k hk c.1))).1
  output[c.2.val]'(by
    have hl := (insertionExecution_perm (List.ofFn (chainKeys p k hk c.1))).length_eq
    rw [List.length_ofFn] at hl
    change c.2.val < (insertionExecution (List.ofFn (chainKeys p k hk c.1))).1.length
    rw [hl]
    exact c.2.isLt)

/-- Every physical slot of the executed output equals the actual gapSort array. -/
theorem gapInsertionOutputAt_eq {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (i : Fin n) :
    gapInsertionOutputAt p k hk i = (gapSort p k).symm i := by
  unfold gapInsertionOutputAt
  simp only [insertionExecution_chain_eq_gapSort, List.getElem_ofFn]
  change (gapSort p k).symm ((positionChainEquiv n k hk).symm
    ((positionChainEquiv n k hk) i)) = (gapSort p k).symm i
  rw [Equiv.symm_apply_apply]

end Shellsort
end
