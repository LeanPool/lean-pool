/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.NestedDissection.Elimination
public import LeanPool.PlanarSeparator.WordRAM.Algebraic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Linarith

/-!
# Operation count of dense elimination

`opInv` is defined in `NestedDissection/Spec.lean`.

Gaussian elimination without pivoting (`NestedDissection.Elimination`) written in the counting
monad `WordRAM.Algebraic.Counted` of the arithmetic cost model.  The cost model charges ring
operations only; elimination also needs one inversion per pivot, which this library charges as
one multiplicative operation (`NestedDissection.opInv`).

Eliminating the first row and column of an `(m + 1) × (m + 1)` matrix costs one inversion,
`m` multiplications for the multipliers and `m ^ 2` multiplications and `m ^ 2` subtractions
for the Schur complement.

## Main definitions

* `NestedDissection.opInv`: charged inversion.
* `NestedDissection.schurCounted`: one elimination step.
* `NestedDissection.luCounted`: the full elimination, returning the factors `(L, U)`.
* `NestedDissection.prodCounted`, `NestedDissection.detCounted`: the determinant as the product
  of the pivots.

## Main results

* `NestedDissection.luCounted_val`: `(luCounted A).val = (lowerFactor A, upperFactor A)`.
* `NestedDissection.luCounted_cost`: the exact count
  `⟨∑ m < n, m ^ 2, ∑ m < n, (1 + m + m ^ 2)⟩`.
* `NestedDissection.luCounted_total_le`: at most `n ^ 3` operations.
* `NestedDissection.detCounted_val`, `NestedDissection.detCounted_total_le`: the determinant in at
  most `n ^ 3 + n` operations.
-/

namespace NestedDissection

open WordRAM.Algebraic

@[expose] public section

universe u

variable {K : Type u}

@[simp] theorem val_opInv [Inv K] (a : K) : (opInv a).val = a⁻¹ := rfl
@[simp] theorem cost_opInv [Inv K] (a : K) : (opInv a).cost = ⟨0, 1⟩ := rfl

/-- Product of the entries of a vector, accumulated from the right: `n` multiplications. -/
def prodCounted [Mul K] [One K] : {n : ℕ} → (Fin n → K) → Counted K
  | 0, _ => pure 1
  | _ + 1, v => do
    let r ← prodCounted (Fin.tail v)
    Op.mul (v 0) r

theorem prodCounted_val [CommMonoid K] {n : ℕ} (v : Fin n → K) :
    (prodCounted v).val = ∏ i, v i := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prodCounted, ih, Fin.prod_univ_succ, Fin.tail]

theorem prodCounted_cost [Mul K] [One K] {n : ℕ} (v : Fin n → K) :
    (prodCounted v).cost = ⟨0, n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => ext <;> simp [prodCounted, ih]

section Field

variable [Field K]

/-- One elimination step: the multipliers `A (i+1) 0 * A 0 0⁻¹` and the Schur complement. -/
def schurCounted {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Counted ((Fin n → K) × Matrix (Fin n) (Fin n) K) := do
  let p ← opInv (A 0 0)
  let l ← Counted.pi fun i : Fin n => Op.mul (A i.succ 0) p
  let S ← Counted.pi fun i : Fin n => Counted.pi fun j : Fin n => do
    let t ← Op.mul (l i) (A 0 j.succ)
    Op.sub (A i.succ j.succ) t
  pure (l, Matrix.of S)

theorem schurCounted_val {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (schurCounted A).val = (fun i => A i.succ 0 * (A 0 0)⁻¹, schur A) := rfl

theorem schurCounted_cost {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (schurCounted A).cost = ⟨n * n, 1 + n + n * n⟩ := by
  ext <;> simp [schurCounted, Finset.card_univ]
  ring

/-- Gaussian elimination without pivoting in the counting monad, returning `(L, U)`. -/
def luCounted : {n : ℕ} → Matrix (Fin n) (Fin n) K →
    Counted (Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K)
  | 0, A => pure (A, A)
  | _ + 1, A => do
    let lS ← schurCounted A
    let LU ← luCounted lS.2
    pure (bordered 1 0 lS.1 LU.1, bordered (A 0 0) (fun j => A 0 j.succ) 0 LU.2)

theorem luCounted_val {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (luCounted A).val = (lowerFactor A, upperFactor A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [luCounted, Counted.val_bind, Counted.val_pure, schurCounted_val, ih]
    rfl

/-- Number of additive operations of dense elimination of size `n`. -/
def denseAdds (n : ℕ) : ℕ := ∑ m ∈ Finset.range n, m * m

/-- Number of multiplicative operations (including inversions) of dense elimination. -/
def denseMuls (n : ℕ) : ℕ := ∑ m ∈ Finset.range n, (1 + m + m * m)

theorem luCounted_cost {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (luCounted A).cost = ⟨denseAdds n, denseMuls n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [luCounted, Counted.cost_bind, Counted.cost_pure, ih, schurCounted_cost]
    ext <;> simp [denseAdds, denseMuls, Finset.sum_range_succ] <;> ring

theorem denseAdds_add_denseMuls_le (n : ℕ) : denseAdds n + denseMuls n ≤ n ^ 3 := by
  induction n with
  | zero => simp [denseAdds, denseMuls]
  | succ n ih =>
    simp only [denseAdds, denseMuls, Finset.sum_range_succ] at ih ⊢
    nlinarith

/-- **Dense elimination costs at most `n ^ 3` arithmetic operations.** -/
theorem luCounted_total_le {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (luCounted A).cost.total ≤ n ^ 3 := by
  rw [luCounted_cost, OpCount.total_mk]
  exact denseAdds_add_denseMuls_le n

/-- The determinant computed by elimination: the product of the pivots. -/
def detCounted {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Counted K := do
  let LU ← luCounted A
  prodCounted fun i => LU.2 i i

theorem detCounted_val_eq_prod {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (detCounted A).val = ∏ k, pivots A k := by
  simp [detCounted, luCounted_val, prodCounted_val, upperFactor_apply_self]

/-- Elimination computes the determinant when all pivots but the last are nonzero (for
instance when all proper leading principal minors are nonzero, `pivots_ne_zero`). -/
theorem detCounted_val {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ k : Fin n, (k : ℕ) + 1 < n → pivots A k ≠ 0) :
    (detCounted A).val = A.det := by
  rw [detCounted_val_eq_prod, det_eq_prod_pivots A h]

theorem detCounted_total_le {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (detCounted A).cost.total ≤ n ^ 3 + n := by
  have := luCounted_total_le A
  simp only [detCounted, Counted.cost_bind, OpCount.total_add, prodCounted_cost,
    OpCount.total_mk]
  omega

end Field

end

end NestedDissection
