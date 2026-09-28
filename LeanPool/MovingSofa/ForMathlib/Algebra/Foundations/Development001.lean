/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Algebra.BigOperators.Triangle`.
* `ForMathlib.Algebra.Order.Fin`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Triangular rearrangement of a double sum over a `Finset`

A double sum over `s ×ˢ s` splits into the closed lower triangle `{(u, t) | u ≤ t}` and its
transpose. The two pieces overlap exactly on the diagonal, so for a kernel vanishing there the
lower-triangular sum plus its transpose recovers the whole double sum.

`Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag` is the `Fintype` and `LocallyFiniteOrder` analogue,
and `Fin.sum_sum_eq_sum_triangle_add` the `Fin` analogue; neither applies to a general `Finset`
of a plain `LinearOrder`.
-/

@[expose] public section

namespace Finset

variable {ι M : Type*} [LinearOrder ι] [AddCommMonoid M]

/-- For a kernel vanishing on the diagonal, the closed lower-triangular double sum plus the same
sum with the two arguments swapped is the full double sum. -/
theorem sum_filter_le_add_sum_filter_le_swap (s : Finset ι) (f : ι → ι → M)
    (hdiag : ∀ x, f x x = 0) :
    ((∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f u t) +
        ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u) =
      ∑ x ∈ s, ∑ y ∈ s, f x y := by
  classical
  calc ((∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f u t) +
          ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u)
      = (∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ t < u), f t u) +
          ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u := by
        rw [Finset.sum_comm' (t' := s) (s' := fun u ↦ s.filter (fun t ↦ u ≤ t))
          (by simp; tauto)]
        refine congrArg₂ _ (Finset.sum_congr rfl fun t _ ↦ (Finset.sum_subset
          (monotone_filter_right _ fun _ _ ↦ le_of_lt) fun u hu hu' ↦ ?_).symm) rfl
        simp only [mem_filter, not_and, not_lt] at hu hu'
        rw [le_antisymm (hu' hu.1) hu.2, hdiag]
    _ = ∑ x ∈ s, ∑ y ∈ s, f x y := by
        rw [add_comm, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ ↦ by
          simpa using Finset.sum_filter_add_sum_filter_not s (· ≤ x) (f x)

end Finset

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Algebra / Order / Fin
-/

@[expose] public section

noncomputable section

namespace Fin

/-- A finite sequence is bounded by its final value plus its positive backward increments. -/
theorem apply_le_last_add_sum_max_sub {n : ℕ} (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    f i ≤ f (Fin.last n) + ∑ j : Fin n, max (f j.castSucc - f j.succ) 0 := by
  induction n with
  | zero => fin_cases i; simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have htail (k : Fin (n + 1)) := ih (fun j ↦ f j.succ) k
    have hnonneg : 0 ≤ max (f 0 - f (Fin.succ 0)) 0 := le_max_right _ _
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · have h := htail 0
      have hmax := le_max_left (f 0 - f (Fin.succ 0)) 0
      simpa only [Fin.succ_last, Fin.succ_castSucc, Fin.castSucc_zero] using
        (show f 0 ≤ f (Fin.last (n + 1)) +
          (max (f 0 - f (Fin.succ 0)) 0 +
            ∑ j : Fin n, max (f j.castSucc.succ - f j.succ.succ) 0) by
          simp only [Fin.succ_last] at h
          linarith)
    · have h := htail k
      simpa only [Fin.succ_last, Fin.succ_castSucc, Fin.castSucc_zero] using
        (show f k.succ ≤ f (Fin.last (n + 1)) +
          (max (f 0 - f (Fin.succ 0)) 0 +
            ∑ j : Fin n, max (f j.castSucc.succ - f j.succ.succ) 0) by
          simp only [Fin.succ_last] at h
          linarith)

end Fin

end

end

end
