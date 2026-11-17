/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Ring.Rat

/-!
# The Schwartz–Zippel lemma over an arbitrary finite type of variables

Mathlib's `MvPolynomial.schwartz_zippel_totalDegree` is stated for variables indexed by `Fin n`,
as an inequality between nonnegative rationals. This file transports it to an arbitrary finite
type of variables and clears the denominators, giving an inequality between natural numbers.

## Main results

* `MvPolynomial.schwartz_zippel_totalDegree_card`: a nonzero polynomial `p` in the variables
  `σ` has at most `p.totalDegree * #S ^ (card σ - 1)` zeros in `S ^ σ`, stated multiplicatively.
-/

@[expose] public section

open Finset Fintype

namespace MvPolynomial

variable {R σ : Type*} [CommRing R] [IsDomain R] [DecidableEq R] [Fintype σ] [DecidableEq σ]

/-- The **Schwartz–Zippel lemma** for an arbitrary finite type of variables, with natural-number
cardinalities: a nonzero polynomial `p` vanishes at no more than a proportion
`p.totalDegree / #S` of the points of `S ^ σ`. -/
theorem schwartz_zippel_totalDegree_card {p : MvPolynomial σ R} (hp : p ≠ 0) (S : Finset R) :
    #{x ∈ piFinset fun _ : σ ↦ S | eval x p = 0} * #S ≤ p.totalDegree * #S ^ card σ := by
  let e := equivFin σ
  have hq : rename e p ≠ 0 := (map_ne_zero_iff _ (rename_injective e e.injective)).mpr hp
  have hfin : #{x ∈ piFinset fun _ : Fin (card σ) ↦ S | eval x (rename e p) = 0} * #S ≤
      (rename e p).totalDegree * #S ^ card σ := by
    obtain rfl | hS := S.eq_empty_or_nonempty
    · simp
    have hS' : (0 : ℚ) < #S := by exact_mod_cast hS.card_pos
    have h := NNRat.coe_le_coe.mpr (schwartz_zippel_totalDegree hq S)
    push_cast at h
    rw [div_le_div_iff₀ (pow_pos hS' _) hS'] at h
    exact_mod_cast h
  have hcard : #{x ∈ piFinset fun _ : σ ↦ S | eval x p = 0} ≤
      #{x ∈ piFinset fun _ : Fin (card σ) ↦ S | eval x (rename e p) = 0} := by
    refine card_le_card_of_injOn (fun x ↦ x ∘ e.symm) (fun x hx ↦ ?_) ?_
    · simp only [coe_filter, Set.mem_ofPred_eq, mem_piFinset] at hx ⊢
      simpa [eval_rename, Function.comp_def] using ⟨fun i ↦ hx.1 _, hx.2⟩
    · intro x _ y _ h
      funext i
      simpa using congrFun h (e i)
  calc _ ≤ #{x ∈ piFinset fun _ : Fin (card σ) ↦ S | eval x (rename e p) = 0} * #S := by gcongr
    _ ≤ (rename e p).totalDegree * #S ^ card σ := hfin
    _ ≤ p.totalDegree * #S ^ card σ := by gcongr; exact totalDegree_rename_le e p

end MvPolynomial
