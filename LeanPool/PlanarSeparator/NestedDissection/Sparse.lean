/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.NestedDissection.DenseCost
public import LeanPool.PlanarSeparator.NestedDissection.Fill

/-!
# Sparse elimination and fill

Elimination without pivoting written *in place*: `stage A k` is the matrix after the first `k`
elimination steps, where step `k` updates the entries `(i, j)` with `i, j > k` by
`M i j ← M i j - M i k * (M k k)⁻¹ * M k j` and leaves all other entries alone.  The trailing
block of `stage A k` is the `k`-fold Schur complement, so the pivots and both triangular
factors of `NestedDissection.Elimination` can be read off the stages (`pivots_eq_stage`,
`upperFactor_eq_stage`, `lowerFactor_eq_stage`), and all of them off the final matrix
`stage A n` (`pivots_eq_stage_final`, `upperFactor_eq_stage_final`,
`lowerFactor_eq_stage_final`, `det_eq_prod_stage_final`).

If the off-diagonal nonzero entries of `A` lie on the edges of a graph `G`, then every
off-diagonal nonzero entry of every stage lies on an edge of the filled graph `fill G Fin.val`
(`stage_eq_zero_of_not_fill`).  Hence an elimination that only updates the positions `(i, j)`
where `i` and `j` are both later neighbours of `k` in a graph `H ⊇ fill G` computes exactly the
same stages (`sparseStage_eq_stage`).  Its operation count is
`∑ v, (1 + d v + 2 * d v ^ 2) ≤ 2 * ∑ v, (d v + 1) ^ 2`, where `d v` is the number of later
neighbours of `v` in `H` (`sparseCounted_total_le`).  See Rose, Tarjan and Lueker
[*Algorithmic aspects of vertex elimination on graphs*, SIAM J. Comput. 5 (1976)] and George
[*Nested dissection of a regular finite element mesh*, SIAM J. Numer. Anal. 10 (1973)].

## Main definitions

`elimStep`, `stage` and `sparseCounted` (with `sparseStepCounted`) are defined in
`NestedDissection/Spec.lean`, `sparseStep` and `sparseStage` here.

* `NestedDissection.elimStep`, `NestedDissection.stage`: dense in-place elimination.
* `NestedDissection.sparseStep`, `NestedDissection.sparseStage`: elimination restricted to a
  pattern `H`.
* `NestedDissection.sparseCounted`: the restricted elimination in the counting monad.

## Main results

* `NestedDissection.stage_lowWalk`, `NestedDissection.stage_eq_zero_of_not_fill`: the fill
  structure theorem.
* `NestedDissection.sparseStage_eq_stage`: restricted elimination is exact.
* `NestedDissection.sparseCounted_val`, `NestedDissection.sparseCounted_total_le`.
* `NestedDissection.sparseCounted_fill_total_le`: the count for `H = fill G Fin.val`.
-/

namespace NestedDissection

open WordRAM.Algebraic Matrix

@[expose] public section

universe u

variable {K : Type u} [Field K]

/-! ### Dense in-place elimination -/

section Stage

variable {n : ℕ}

@[simp] theorem stage_zero (A : Matrix (Fin n) (Fin n) K) : stage A 0 = A := rfl

theorem stage_succ_of_lt (A : Matrix (Fin n) (Fin n) K) {k : ℕ} (h : k < n) :
    stage A (k + 1) = elimStep ⟨k, h⟩ (stage A k) := dite_eq_left h

theorem stage_succ_of_le (A : Matrix (Fin n) (Fin n) K) {k : ℕ} (h : n ≤ k) :
    stage A (k + 1) = stage A k := dite_eq_right (by omega)

/-- After the first step, the trailing block of the stages is the elimination of the Schur
complement. -/
theorem stage_succ_submatrix (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k : ℕ) :
    (stage A (k + 1)).submatrix Fin.succ Fin.succ = stage (schur A) k := by
  induction k with
  | zero =>
    ext i j
    simp [stage_succ_of_lt A (Nat.succ_pos n), elimStep, Fin.succ_pos]
  | succ k ih =>
    by_cases hk : k < n
    · have e : (⟨k + 1, by omega⟩ : Fin (n + 1)) = Fin.succ ⟨k, hk⟩ := rfl
      have ih' : ∀ a b, stage A (k + 1) a.succ b.succ = stage (schur A) k a b :=
        fun a b => congrFun (congrFun ih a) b
      ext i j
      simp only [submatrix_apply, stage_succ_of_lt A (show k + 1 < n + 1 by omega),
        stage_succ_of_lt (schur A) hk, elimStep, of_apply, e, Fin.succ_lt_succ_iff, ih']
    · rw [stage_succ_of_le A (show n + 1 ≤ k + 1 by omega),
        stage_succ_of_le (schur A) (show n ≤ k by omega), ih]

theorem stage_succ_succ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k : ℕ) (i j : Fin n) :
    stage A (k + 1) i.succ j.succ = stage (schur A) k i j :=
  congrFun (congrFun (stage_succ_submatrix A k) i) j

/-- The `k`-th pivot is the `(k, k)` entry of the `k`-th stage. -/
theorem pivots_eq_stage (A : Matrix (Fin n) (Fin n) K) (k : Fin n) :
    pivots A k = stage A k k k := by
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
    induction k using Fin.cases with
    | zero => rfl
    | succ k => rw [pivots_succ, ih, Fin.val_succ, stage_succ_succ]

/-- The upper factor is the upper triangle of the stages: row `i` of `U` is row `i` of the
`i`-th stage. -/
theorem upperFactor_eq_stage (A : Matrix (Fin n) (Fin n) K) {i j : Fin n} (h : i ≤ j) :
    upperFactor A i j = stage A i i j := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => rfl
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (by simp)
      | succ j =>
        rw [upperFactor_succ, bordered_succ_succ, ih _ (Fin.succ_le_succ_iff.mp h), Fin.val_succ,
          stage_succ_succ]

/-- The multipliers: `L i j = stage A j i j / stage A j j j` for `j < i`. -/
theorem lowerFactor_eq_stage (A : Matrix (Fin n) (Fin n) K) {i j : Fin n} (h : j < i) :
    lowerFactor A i j = stage A j i j * (stage A j j j)⁻¹ := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact absurd h (Fin.not_lt_zero _)
    | succ i =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j =>
        rw [lowerFactor_succ, bordered_succ_succ, ih _ (Fin.succ_lt_succ_iff.mp h), Fin.val_succ,
          stage_succ_succ, stage_succ_succ]

/-- Entry `(i, j)` is no longer changed once the earlier of `i`, `j` has been eliminated. -/
theorem stage_apply_of_le (A : Matrix (Fin n) (Fin n) K) {i j : Fin n} {k : ℕ}
    (hk : min (i : ℕ) j ≤ k) : stage A k i j = stage A (min (i : ℕ) j) i j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← Nat.add_assoc]
    by_cases h : min (i : ℕ) j + m < n
    · rw [stage_succ_of_lt A h, elimStep, of_apply, ite_eq_right (fun hc => by
        have := hc.1; have := hc.2; simp only [Fin.lt_def] at *; omega), ih (by omega)]
    · rw [stage_succ_of_le A (by omega), ih (by omega)]

/-- The final in-place matrix `stage A n` holds the pivots on its diagonal. -/
theorem pivots_eq_stage_final (A : Matrix (Fin n) (Fin n) K) (k : Fin n) :
    pivots A k = stage A n k k := by
  rw [pivots_eq_stage, stage_apply_of_le A (k := n) (by have := k.2; omega), min_self]

/-- The final in-place matrix holds `U` in its upper triangle. -/
theorem upperFactor_eq_stage_final (A : Matrix (Fin n) (Fin n) K) {i j : Fin n} (h : i ≤ j) :
    upperFactor A i j = stage A n i j := by
  have h' : (i : ℕ) ≤ j := h
  rw [upperFactor_eq_stage A h, stage_apply_of_le A (k := n) (by have := i.2; omega),
    min_eq_left h']

/-- The final in-place matrix holds `L` (times the pivots) in its strict lower triangle. -/
theorem lowerFactor_eq_stage_final (A : Matrix (Fin n) (Fin n) K) {i j : Fin n} (h : j < i) :
    lowerFactor A i j = stage A n i j * (stage A n j j)⁻¹ := by
  have h' : (j : ℕ) ≤ i := le_of_lt h
  rw [lowerFactor_eq_stage A h, stage_apply_of_le A (i := i) (j := j) (k := n)
    (by have := j.2; omega), stage_apply_of_le A (i := j) (j := j) (k := n)
    (by have := j.2; omega), min_eq_right h', min_self]

/-- The determinant is the product of the diagonal of the final in-place matrix (all pivots but
the last nonzero). -/
theorem det_eq_prod_stage_final (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ k : Fin n, (k : ℕ) + 1 < n → pivots A k ≠ 0) :
    A.det = ∏ k, stage A n k k := by
  rw [det_eq_prod_pivots A h]
  exact Finset.prod_congr rfl fun k _ => pivots_eq_stage_final A k

/-! ### The fill structure theorem -/

variable (G : SimpleGraph (Fin n))

/-- **Structure of fill.**  If every off-diagonal nonzero entry of `A` is an edge of `G`, then
every off-diagonal nonzero entry `(i, j)` of the `k`-th stage is joined in `G` by a walk whose
interior vertices are among the first `min k (min i j)` vertices. -/
theorem stage_lowWalk (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, i ≠ j → A i j ≠ 0 → G.Adj i j)
    (k : ℕ) {i j : Fin n} (hij : i ≠ j) (h : stage A k i j ≠ 0) :
    LowWalk G Fin.val (min k (min i j)) i j := by
  induction k generalizing i j with
  | zero => exact .adj (hA i j hij h)
  | succ k ih =>
    have hmono : min k (min (i : ℕ) j) ≤ min (k + 1) (min i j) := by omega
    by_cases hk : k < n
    · rw [stage_succ_of_lt A hk] at h
      simp only [elimStep, of_apply] at h
      split_ifs at h with hc
      · by_cases hM : stage A k i j = 0
        · rw [hM, zero_sub, neg_ne_zero, mul_ne_zero_iff, mul_ne_zero_iff] at h
          obtain ⟨⟨h₁, -⟩, h₂⟩ := h
          have hik : i ≠ ⟨k, hk⟩ := (ne_of_lt hc.1).symm
          have hkj : (⟨k, hk⟩ : Fin n) ≠ j := ne_of_lt hc.2
          have w₁ := ih hik h₁
          have w₂ := ih hkj h₂
          have hc' : k < (i : ℕ) ∧ k < (j : ℕ) := ⟨hc.1, hc.2⟩
          have e₁ : min k (min (i : ℕ) k) = k := by omega
          have e₂ : min k (min k (j : ℕ)) = k := by omega
          simp only [e₁, e₂] at w₁ w₂
          rw [show min (k + 1) (min (i : ℕ) j) = k + 1 by omega]
          exact (w₁.mono (Nat.le_succ k)).trans (Nat.lt_succ_self k) (w₂.mono (Nat.le_succ k))
        · exact (ih hij hM).mono hmono
      · exact (ih hij h).mono hmono
    · rw [stage_succ_of_le A (by omega)] at h
      exact (ih hij h).mono hmono

/-- **Fill structure theorem.**  Entries outside the filled pattern stay zero throughout
elimination. -/
theorem stage_eq_zero_of_not_fill (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ i j, i ≠ j → A i j ≠ 0 → G.Adj i j) (k : ℕ) {i j : Fin n} (hij : i ≠ j)
    (h : ¬ (fill G Fin.val).Adj i j) : stage A k i j = 0 := by
  by_contra h'
  exact h (fill_adj_of_lowWalk hij (stage_lowWalk G A hA k hij h') (min_le_right _ _))

/-! ### Elimination restricted to a pattern -/

variable (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]

/-- The elimination step with pivot `k` restricted to the positions `(i, j)` with `i` and `j`
later neighbours of `k` in `H`. -/
def sparseStep (k : Fin n) (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j =>
    if i ∈ laterNbrs Fin.val H k ∧ j ∈ laterNbrs Fin.val H k then
      M i j - M i k * (M k k)⁻¹ * M k j
    else M i j

/-- The stages of the restricted elimination. -/
def sparseStage (A : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => A
  | k + 1 => if h : k < n then sparseStep H ⟨k, h⟩ (sparseStage A k) else sparseStage A k

variable {G H}

/-- **Restricted elimination is exact**: if `fill G ≤ H`, it computes the same stages. -/
theorem sparseStage_eq_stage (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ i j, i ≠ j → A i j ≠ 0 → G.Adj i j) (hH : fill G Fin.val ≤ H) (k : ℕ) :
    sparseStage H A k = stage A k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < n
    · rw [stage_succ_of_lt A hk, sparseStage, dite_eq_left hk, ih]
      set kk : Fin n := ⟨k, hk⟩
      have hz : ∀ i : Fin n, kk < i → i ∉ laterNbrs Fin.val H kk →
          stage A k i kk = 0 ∧ stage A k kk i = 0 := by
        intro i hi hn
        have hadj : ¬ (fill G Fin.val).Adj kk i := fun hf =>
          hn (mem_laterNbrs.mpr ⟨hH hf, hi⟩)
        exact ⟨stage_eq_zero_of_not_fill G A hA k (ne_of_lt hi).symm fun hf => hadj hf.symm,
          stage_eq_zero_of_not_fill G A hA k (ne_of_lt hi) hadj⟩
      ext i j
      simp only [sparseStep, elimStep, of_apply]
      by_cases hc : kk < i ∧ kk < j
      · rw [ite_eq_left hc]
        split_ifs with hm
        · rfl
        · rw [not_and_or] at hm
          rcases hm with hm | hm
          · rw [(hz i hc.1 hm).1]; ring
          · rw [(hz j hc.2 hm).2]; ring
      · rw [ite_eq_right hc, ite_eq_right]
        rintro ⟨hi, hj⟩
        exact hc ⟨(mem_laterNbrs.mp hi).2, (mem_laterNbrs.mp hj).2⟩
    · rw [stage_succ_of_le A (by omega), sparseStage, dite_eq_right hk, ih]

/-! ### Operation count of the restricted elimination -/

variable (H)

theorem sparseStepCounted_val (k : Fin n) (M : Matrix (Fin n) (Fin n) K) :
    (sparseStepCounted H k M).val = sparseStep H k M := by
  ext i j
  simp only [sparseStepCounted, sparseStep, Counted.val_bind, Counted.val_pure, Counted.val_pi,
    of_apply, val_opInv]
  by_cases h : i ∈ laterNbrs Fin.val H k ∧ j ∈ laterNbrs Fin.val H k
  · simp [h]
  · simp [h]

/-- The cost of one restricted step with `d` later neighbours: one inversion, `d`
multiplications for the multipliers and `d ^ 2` multiplications and subtractions. -/
def stepCost (m : ℕ) : OpCount :=
  if h : m < n then
    ⟨(laterNbrs Fin.val H ⟨m, h⟩).card * (laterNbrs Fin.val H ⟨m, h⟩).card,
      1 + (laterNbrs Fin.val H ⟨m, h⟩).card +
        (laterNbrs Fin.val H ⟨m, h⟩).card * (laterNbrs Fin.val H ⟨m, h⟩).card⟩
  else 0

theorem sparseStepCounted_cost (k : Fin n) (M : Matrix (Fin n) (Fin n) K) :
    (sparseStepCounted H k M).cost = stepCost H k := by
  rw [stepCost, dite_eq_left k.2]
  simp only [sparseStepCounted, Counted.cost_bind, Counted.cost_pure, Counted.cost_pi,
    cost_opInv, apply_ite Counted.cost, Op.cost_mul, Op.cost_sub, ite_and]
  ext
  · simp [Finset.sum_ite_mem]
  · simp [Finset.sum_ite_mem]
    ring

theorem sparseCounted_val' (A : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    (sparseCounted H A k).val = sparseStage H A k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < n
    · simp [sparseCounted, sparseStage, hk, ih, sparseStepCounted_val]
    · simp [sparseCounted, sparseStage, hk, ih]

theorem sparseCounted_cost (A : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    (sparseCounted H A k).cost = ∑ m ∈ Finset.range k, stepCost H m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    by_cases hk : k < n
    · simp [sparseCounted, hk, sparseStepCounted_cost]
    · simp [sparseCounted, hk, stepCost]

variable {H}

/-- **Restricted elimination computes the stages of elimination** when `fill G ≤ H`. -/
theorem sparseCounted_val (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ i j, i ≠ j → A i j ≠ 0 → G.Adj i j) (hH : fill G Fin.val ≤ H) (k : ℕ) :
    (sparseCounted H A k).val = stage A k := by
  rw [sparseCounted_val', sparseStage_eq_stage A hA hH]

variable (H)

/-- **Operation count of restricted elimination**: at most `2 * ∑ v, (d v + 1) ^ 2`, where
`d v` is the number of later neighbours of `v` in `H`. -/
theorem sparseCounted_total_le (A : Matrix (Fin n) (Fin n) K) :
    (sparseCounted H A n).cost.total ≤
      2 * ∑ v : Fin n, ((laterNbrs Fin.val H v).card + 1) ^ 2 := by
  rw [sparseCounted_cost, ← Fin.sum_univ_eq_sum_range, OpCount.total, OpCount.adds_sum,
    OpCount.muls_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  simp only [stepCost, dite_eq_left v.2, Fin.eta]
  nlinarith

end Stage

/-- **Sparse elimination with the filled pattern.**  For a matrix whose off-diagonal nonzero
entries are edges of `G`, elimination restricted to the filled graph computes the stages of
elimination (in particular all pivots, `pivots_eq_stage`) using at most
`2 * ∑ v, (deg⁺ v + 1) ^ 2` operations, `deg⁺ v` being the number of later neighbours of `v`
in `fill G Fin.val`. -/
theorem sparseCounted_fill {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel (fill G Fin.val).Adj]
    (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, i ≠ j → A i j ≠ 0 → G.Adj i j) :
    (sparseCounted (fill G Fin.val) A n).val = stage A n ∧
      (sparseCounted (fill G Fin.val) A n).cost.total ≤
        2 * ∑ v : Fin n, ((laterNbrs Fin.val (fill G Fin.val) v).card + 1) ^ 2 :=
  ⟨sparseCounted_val A hA le_rfl n, sparseCounted_total_le _ A⟩

end

end NestedDissection
