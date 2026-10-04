/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.IteratedFamily
public import LeanPool.EllipticPDE.Embedding.HolderOfGradClosed


/-!
# Second case of the Sobolev embedding of order k

Guo, *Partial Differential Equations*, Theorem IV.2.3: for `u ∈ W^{m,p}(Ω)` with `m > n/p`, the
conclusion is `u ∈ C^{m-1-⌊n/p⌋, γ}(Ω)`. This file states and proves the case `p = 2`, locally,
from the supply of weak derivatives the interior regularity theory produces.

## Order and exponent

An order-`m` supply of weak derivatives in `L²` gives classical derivatives up to
`k = m - 1 - ⌊d/2⌋`, and the top ones are Hölder-`1/2`. The order is the cited one on the nose,
and so is the exponent when `d` is odd, where `⌊d/2⌋ + 1 - d/2 = 1/2`; when `d` is even the
cited `γ` is free in `(0, 1)` and `1/2` is the choice
`EllipticPdes.Embedding.contDiffOn_holder_of_gradClosed` fixes.

The hypothesis `m > d/2` the cited statement asks for is `k + 1 + ⌊d/2⌋ ≤ m` here, at `k = 0`.

## Multi-index form

The conclusion is stated over lists of directions, as the cited statement is over multi-indices. The
entry `v α` is the partial derivative of `v []` along `α`, which the last component of the
conclusion says exactly: on the ball the classical derivative of `v α` is the tuple of the
`v (j :: α)`. So `C^{k, 1/2}` reads as it should, that every partial derivative of order at most
`k` exists classically and is Hölder-`1/2`.

## Main declarations

* `EllipticPdes.Regularity.exists_contDiffOn_holder_ball_of_hasIteratedWeakDerivOn`: the
  multi-index form.
* `EllipticPdes.Regularity.exists_contDiffOn_holder_ball`: the same read at the root.

## References

Guo, *Partial Differential Equations*, Theorem IV.2.3.
Evans, *Partial Differential Equations* (2nd ed.), §5.6.3.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev EllipticPdes.Embedding

variable {d : ℕ}

/-- **Second case in multi-index form.** An `L²` class with weak derivatives up to order
`m` on `V`, and `k + 1 + ⌊d/2⌋ ≤ m`, has on any ball compactly inside `V` a family of
representatives indexed by lists of directions: the empty list represents the class, every list
of length at most `k` is Hölder-`1/2` and of class `C^{k - |α|}`, and each is the classical
derivative of its parent.

The supply is spent in three places. Morrey takes the weak gradient, the ladder takes `⌊d/2⌋`
more raising it to `L^{2d}`, and reading the order-`k` derivative asks the same of everything `k`
levels up, which together are the `k + 1 + ⌊d/2⌋` of the hypothesis. -/
theorem exists_contDiffOn_holder_ball_of_hasIteratedWeakDerivOn (hd : 0 < d)
    {V : Set (EuclideanSpace ℝ (Fin d))} (u : L2D V) {m k : ℕ}
    (H : HasIteratedWeakDerivOn V m u) (hmk : k + 1 + d / 2 ≤ m)
    {c : EuclideanSpace ℝ (Fin d)} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hBV : Metric.ball c R ⊆ V) :
    ∃ v : List (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ,
      v [] =ᵐ[volume.restrict (Metric.ball c r)] (u : EuclideanSpace ℝ (Fin d) → ℝ) ∧
      (∀ α : List (Fin d), α.length ≤ k →
        ∃ M : ℝ≥0, HolderOnWith M (1 / 2 : ℝ≥0) (v α) (Metric.ball c r)) ∧
      (∀ α : List (Fin d), α.length ≤ k →
        ContDiffOn ℝ ((k - α.length : ℕ) : ℕ) (v α) (Metric.ball c r)) ∧
      (∀ α : List (Fin d), α.length < k → ∀ y ∈ Metric.ball c r,
        HasFDerivAt (v α) (gradCLM (fun j => v (j :: α)) y) y) := by
  obtain ⟨F, hFgrad, hFmem, hF0⟩ := exists_gradClosed_of_hasIteratedWeakDerivOn_le u H hBV
  obtain ⟨v, hvae, hvhol, hcn, hfd⟩ :=
    EllipticPdes.Embedding.contDiffOn_holder_of_gradClosed hd c hr hrR
      (F := F) (nxt := fun (α : List (Fin d)) j => j :: α) (dep := List.length) (m := m)
      (fun α j => by simp) hFgrad (fun α _ => hFmem α)
  refine ⟨v, ?_, fun α hα => hvhol α (by omega), fun α hα => hcn _ α (by omega),
    fun α hα y hy => hfd α (by omega) y hy⟩
  have hroot : ([] : List (Fin d)).length + 1 + d / 2 ≤ m := by
    simp only [List.length_nil]; omega
  have h0 : v [] =ᵐ[volume.restrict (Metric.ball c r)] F [] := hvae [] hroot
  rw [← hF0]
  exact h0

/-- **Second case at the root.** An `L²` class `u` on `V` with weak derivatives to order
`m`, and `k + 1 + ⌊d/2⌋ ≤ m`, has on any ball whose enlargement sits inside `V` a representative
of class `C^k`, Hölder-`1/2` there.

This is Theorem IV.2.3 case (ii) of Guo, *Partial Differential Equations*, at `p = 2`, read
locally. The order `k = m - 1 - ⌊d/2⌋` is the cited one, and the cited hypothesis `m > d/2` is
the displayed inequality at `k = 0`. The exponent `1/2` is the cited `⌊d/2⌋ + 1 - d/2` when `d`
is odd; when `d` is even that value is `0`, the cited statement leaves the exponent free in
`(0, 1)`, and `1/2` is what the landing exponent `2d` gives.

The cited statement takes a bounded `Ω` with `C¹` boundary and concludes on its closure, with a
norm estimate.
The statement here asks nothing of a boundary, concludes on an open ball, and is qualitative;
the estimate belongs to `EllipticPdes.Regularity.higher_interior_regularity`, which supplies the
weak derivatives this consumes. It is read off the multi-index form
`EllipticPdes.Regularity.exists_contDiffOn_holder_ball_of_hasIteratedWeakDerivOn` at the empty
list. -/
theorem exists_contDiffOn_holder_ball (hd : 0 < d)
    {V : Set (EuclideanSpace ℝ (Fin d))} (u : L2D V) {m k : ℕ}
    (H : HasIteratedWeakDerivOn V m u) (hmk : k + 1 + d / 2 ≤ m)
    {c : EuclideanSpace ℝ (Fin d)} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hBV : Metric.ball c R ⊆ V) :
    ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
      w =ᵐ[volume.restrict (Metric.ball c r)] (u : EuclideanSpace ℝ (Fin d) → ℝ) ∧
      ContDiffOn ℝ (k : ℕ) w (Metric.ball c r) ∧
      ∃ M : ℝ≥0, HolderOnWith M (1 / 2 : ℝ≥0) w (Metric.ball c r) := by
  obtain ⟨v, hv0, hvhol, hcn, _⟩ :=
    exists_contDiffOn_holder_ball_of_hasIteratedWeakDerivOn hd u H hmk hr hrR hBV
  refine ⟨v [], hv0, ?_, hvhol [] (by simp)⟩
  have := hcn [] (by simp)
  simpa using this

end EllipticPdes.Regularity
