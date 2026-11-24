/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.PermutationGeometry
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Order.Hom.Set

/-! A genuine gap-sorting operator on finite rank placements. Each chain is
sorted by an order isomorphism, and the chains are assembled into a permutation.
Sorting correctness is proved from the construction, not assumed. -/
@[expose] public noncomputable section
namespace Shellsort

abbrev KeyFiber {n : ℕ} (p : RankPlacement n) (k r : ℕ) :=
  { x : Fin n // (p x).val % k = r }

abbrev PositionFiber (n k r : ℕ) := { i : Fin n // i.val % k = r }

def originalFiberEquiv {n : ℕ} (p : RankPlacement n) (k r : ℕ) :
    KeyFiber p k r ≃ PositionFiber n k r where
  toFun x := ⟨p x.val, x.property⟩
  invFun i := ⟨p.symm i.val, by simpa using i.property⟩
  left_inv x := by ext; simp
  right_inv i := by ext; simp

def sortedFiberIso {n : ℕ} (p : RankPlacement n) (k r : ℕ) :
    KeyFiber p k r ≃o PositionFiber n k r :=
  (Fintype.orderIsoFinOfCardEq (KeyFiber p k r) rfl).symm.trans
    (Fintype.orderIsoFinOfCardEq (PositionFiber n k r)
      (Fintype.card_congr (originalFiberEquiv p k r).symm))

/-- Sort each residue class in increasing key order. k=0 is harmless: each
position is its own residue class and the operator leaves the array unchanged. -/
def gapSort {n : ℕ} (p : RankPlacement n) (k : ℕ) : RankPlacement n :=
  Equiv.ofFiberEquiv (fun r => (sortedFiberIso p k r).toEquiv)

theorem gapSort_preserves_residue {n : ℕ} (p : RankPlacement n) (k : ℕ) (x : Fin n) :
    (gapSort p k x).val % k = (p x).val % k :=
  Equiv.ofFiberEquiv_map (fun r => (sortedFiberIso p k r).toEquiv) x

theorem gapSort_apply_fiber {n : ℕ} (p : RankPlacement n) (k r : ℕ)
    (x : KeyFiber p k r) :
    gapSort p k x.val = (sortedFiberIso p k r x).val := by
  rcases x with ⟨x, hx⟩
  cases hx
  rfl

theorem gapSort_strict_order_on_fiber {n : ℕ} (p : RankPlacement n) (k r : ℕ)
    (x y : KeyFiber p k r) :
    gapSort p k x.val < gapSort p k y.val ↔ x.val < y.val := by
  rw [gapSort_apply_fiber, gapSort_apply_fiber]
  exact (sortedFiberIso p k r).lt_iff_lt

/-- For any two keys ending in the same chain, their order is exactly their rank order. -/
theorem gapSort_sorted {n : ℕ} (p : RankPlacement n) (k : ℕ) (x y : Fin n)
    (hchain : (gapSort p k x).val % k = (gapSort p k y).val % k) :
    gapSort p k x < gapSort p k y ↔ x < y := by
  have hres : (p x).val % k = (p y).val % k := by
    simpa only [gapSort_preserves_residue] using hchain
  exact gapSort_strict_order_on_fiber p k ((p y).val % k) ⟨x, hres⟩ ⟨y, rfl⟩

def candidateFiberIso {n : ℕ} (p q : RankPlacement n) (k r : ℕ)
    (hres : ∀ x, (q x).val % k = (p x).val % k)
    (hsort : ∀ x y, (p x).val % k = (p y).val % k → (q x < q y ↔ x < y)) :
    KeyFiber p k r ≃o PositionFiber n k r where
  toFun x := ⟨q x.val, (hres x.val).trans x.property⟩
  invFun i := ⟨q.symm i.val, by
    have h := hres (q.symm i.val)
    simpa using h.symm.trans (by simpa using i.property)⟩
  left_inv x := by ext; simp
  right_inv i := by ext; simp
  map_rel_iff' := by
    intro x y
    change q x.val ≤ q y.val ↔ x.val ≤ y.val
    rw [← not_lt, ← not_lt]
    exact not_congr (hsort y.val x.val (y.property.trans x.property.symm))

/-- The construction is the unique class-preserving, chain-sorted placement. -/
theorem gapSort_unique {n : ℕ} (p q : RankPlacement n) (k : ℕ)
    (hres : ∀ x, (q x).val % k = (p x).val % k)
    (hsort : ∀ x y, (p x).val % k = (p y).val % k → (q x < q y ↔ x < y)) :
    gapSort p k = q := by
  ext x
  let r := (p x).val % k
  have heq : sortedFiberIso p k r = candidateFiberIso p q k r hres hsort :=
    Subsingleton.elim _ _
  have hx := congrArg (fun e : KeyFiber p k r ≃o PositionFiber n k r =>
    (e ⟨x, rfl⟩).val) heq
  change (sortedFiberIso p k r ⟨x, rfl⟩).val = q x at hx
  exact congrArg Fin.val ((gapSort_apply_fiber p k r ⟨x, rfl⟩).trans hx)

theorem gapSort_idempotent {n : ℕ} (p : RankPlacement n) (k : ℕ) :
    gapSort (gapSort p k) k = gapSort p k := by
  apply gapSort_unique
  · intro x; rfl
  · intro x y h
    exact gapSort_sorted p k x y h

theorem gapSort_one {n : ℕ} (p : RankPlacement n) :
    gapSort p 1 = Equiv.refl _ := by
  apply gapSort_unique
  · intro x; simp [Nat.mod_one]
  · intro x y _; rfl

theorem gapSort_zero {n : ℕ} (p : RankPlacement n) : gapSort p 0 = p := by
  ext x
  have h := gapSort_preserves_residue p 0 x
  simpa using h

end Shellsort
end
