/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import LeanPool.PLAcceleratedNesterovLean.Core.Defs

/-!
# Bootstrap Step 2: Choosing α

Two auxiliary facts for the bootstrap argument:

* `exists_alpha_psi_small`: if `R > 0` and `Ψ` is continuous at `m` with `Ψ m = 0`, then `Ψ < R²`
  on a ball around `m`. The bootstrap uses this to choose the initial radius `α`.
* `series_bound_from_geometric`: a finite sum dominated termwise by `C * r ^ k` is at most
  `C * ∑ r ^ k`.

The induction keeping the iterates in `Ω` is proved in `Convergence/Bootstrap/Main.lean`, and its
result is `bootstrap_total_displacement`.
-/

@[expose] public section

noncomputable section

namespace PLAcceleratedNesterovLean

/-- If Ψ is continuous, Ψ(m) = 0, and R > 0, there exists α > 0 with Ψ(x) < R²
    for all x in B(m, α). -/
theorem exists_alpha_psi_small {d : ℕ} (m : E d) (Ψ : E d → ℝ)
    (hcont : ContinuousAt Ψ m) (hzero : Ψ m = 0) (R : ℝ) (hR : 0 < R) :
    ∃ α : ℝ, 0 < α ∧ ∀ x, dist x m < α → Ψ x < R ^ 2 := by
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont (R ^ 2) hR2
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have h := hball hx
  have hle : Ψ x ≤ dist (Ψ x) (Ψ m) := by
    rw [Real.dist_eq, hzero, sub_zero]; exact le_abs_self _
  linarith

/-- Sum bound: if f(k) ≤ C · r^k for all k, then Σ f(k) ≤ C · Σ r^k. -/
theorem series_bound_from_geometric (f : ℕ → ℝ) (C r : ℝ) (n : ℕ)
    (_hC : 0 ≤ C) (_hr : 0 ≤ r) (hf : ∀ k, k < n → f k ≤ C * r ^ k) :
    (Finset.range n).sum f ≤ C * (Finset.range n).sum (fun k => r ^ k) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k hk => hf k (Finset.mem_range.mp hk)

end PLAcceleratedNesterovLean
