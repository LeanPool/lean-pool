/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# WindowRearrange

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Window rearrangement of geometric layer tails

ABK26, `l.minimal.scale.sep` Steps 1 and 2.  The minimal-scale separation bound
sums, over a window of scales `k ∈ [n, m]`, a geometric layer tail.  Upward
(Step 2) the tail is `∑_{l ≥ k} 3^{−α(l−k)} Y_l`; downward (Step 1) it is `∑_{l
≤ k} 3^{−α(k−l)} X_l`.  Both rearrange into

  `(1 − 3^{−α})⁻¹ · ∑_{l ∈ [n,m]} Y_l  +  min(m − n + 1, (1 − 3^{−α})⁻¹) · (tail)`,

i.e. a **window part** carrying the geometric constant `Cgeo = (1 − 3^{−α})⁻¹`
and an **off-window part** carrying the *sharper* coefficient
`min(window length, Cgeo)`. The `min` is load-bearing: in the short-window regime
`m − n < α⁻¹` the crude `Cgeo` on the off-window term loses a power of the
parameter and the printed envelope fails.

## Main results

* `Algsuperdiff.Probability.window_geom_tail_rearrange` — the upward headline,
  with the `min` coefficient on the off-window tail.
* `Algsuperdiff.Probability.window_geom_tail_rearrange_le` — the crude
  `Cgeo`-on-both-terms corollary.
* `Algsuperdiff.Probability.window_geom_head_rearrange` — the downward
  (below-window) reflection.

## Design

Everything here is **pure deterministic real analysis**: no probability, no
measure theory, no summability hypothesis, and the import closure is Mathlib
only. The statements are unconditional in the layer field (only nonnegativity is
assumed), which forces an honest treatment of the `tsum` junk value: if the
off-window family fails to be summable then *every* layer tail on the left also
fails (the families differ by a finite prefix and a positive geometric
rescaling), so both sides degenerate and the inequality is trivial.

In the summable case the proof is a **finite induction on the window length**,
using the exact one-step recursion `T k = Y k + 3^{−α} · T (k+1)` for the layer
tail `T k = ∑_j 3^{−αj} Y (k+j)`. The inductive invariant keeps the tail
coefficient as the *partial* geometric sum `3^{−α} · ∑_{s ≤ M} 3^{−αs}`, which is
simultaneously `≤ M + 1` and `≤ Cgeo` — that is exactly where the `min` comes
from.

## References

* ABK26, `l.minimal.scale.sep`, Step 1 and Step 2.
-/

namespace Algsuperdiff.Probability

open scoped BigOperators

/-! ## Elementary geometric facts -/

theorem threePow_neg_natMul (t : ℝ) (j : ℕ) :
    (3 : ℝ) ^ (-(t * (j : ℝ))) = ((3 : ℝ) ^ (-t)) ^ j := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-t)) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- Every partial geometric sum is bounded by the full geometric constant. -/
private theorem geom_partial_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ s ∈ Finset.range N, r ^ s ≤ (1 - r)⁻¹ := by
  have h1r : 0 < 1 - r := by linarith only [hr1]
  have hmul : (∑ s ∈ Finset.range N, r ^ s) * (r - 1) = r ^ N - 1 := geom_sum_mul r N
  have hpow : (0 : ℝ) ≤ r ^ N := pow_nonneg hr0 N
  have hkey : (∑ s ∈ Finset.range N, r ^ s) * (1 - r) ≤ 1 := by
    linarith only [hmul, hpow]
  have hstep := mul_le_mul_of_nonneg_right hkey (inv_nonneg.2 h1r.le)
  rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt h1r), mul_one, one_mul] at hstep

/-- A partial geometric sum of `N` terms with ratio in `[0, 1)` is bounded by
`N`. -/
private theorem geom_partial_le_card {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ s ∈ Finset.range N, r ^ s ≤ (N : ℝ) := by
  have h : ∑ s ∈ Finset.range N, r ^ s ≤ ∑ _s ∈ Finset.range N, (1 : ℝ) :=
    Finset.sum_le_sum fun i _ => pow_le_one₀ hr0 hr1.le
  simpa using h

/-! ## Summability transfer between base points -/

/-- **Base-point shift, both directions.** For a positive ratio `r`, the
geometric layer family based at `a` is summable iff the one based at `a + δ` is:
the two differ by a finite prefix and the positive rescaling `r^δ`. -/
private theorem summable_layer_shift {r : ℝ} (hr0 : 0 < r) (Y : ℤ → ℝ) (a : ℤ) (δ : ℕ) :
    Summable (fun j : ℕ => r ^ j * Y (a + (j : ℤ)))
      ↔ Summable (fun j : ℕ => r ^ j * Y (a + (δ : ℤ) + (j : ℤ))) := by
  have hkey : ∀ j : ℕ, r ^ (j + δ) * Y (a + ((j + δ : ℕ) : ℤ))
      = r ^ δ * (r ^ j * Y (a + (δ : ℤ) + (j : ℤ))) := by
    intro j
    have harg : a + ((j + δ : ℕ) : ℤ) = a + (δ : ℤ) + (j : ℤ) := by push_cast; ring
    rw [harg, pow_add]
    ring
  have hδ : (0 : ℝ) < r ^ δ := pow_pos hr0 δ
  constructor
  · intro h
    have h2 : Summable (fun j : ℕ => r ^ (j + δ) * Y (a + ((j + δ : ℕ) : ℤ))) :=
      (summable_nat_add_iff (f := fun j : ℕ => r ^ j * Y (a + (j : ℤ))) δ).2 h
    have h3 : Summable (fun j : ℕ => r ^ δ * (r ^ j * Y (a + (δ : ℤ) + (j : ℤ)))) :=
      h2.congr hkey
    refine (h3.mul_left (r ^ δ)⁻¹).congr fun j => ?_
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hδ), one_mul]
  · intro h
    refine (summable_nat_add_iff (f := fun j : ℕ => r ^ j * Y (a + (j : ℤ))) δ).1 ?_
    exact (h.mul_left (r ^ δ)).congr fun j => (hkey j).symm

/-- **Base-point transfer.** Summability of the geometric layer family does not
depend on the base point at all. -/
private theorem summable_layer_any {r : ℝ} (hr0 : 0 < r) (Y : ℤ → ℝ) (a b : ℤ)
    (h : Summable (fun j : ℕ => r ^ j * Y (a + (j : ℤ)))) :
    Summable (fun j : ℕ => r ^ j * Y (b + (j : ℤ))) := by
  rcases le_total a b with hab | hab
  · have h2 := (summable_layer_shift hr0 Y a (b - a).toNat).1 h
    have harg : a + (((b - a).toNat : ℕ) : ℤ) = b := by omega
    rwa [harg] at h2
  · refine (summable_layer_shift hr0 Y b (a - b).toNat).2 ?_
    have harg : b + (((a - b).toNat : ℕ) : ℤ) = a := by omega
    rwa [harg]

/-! ## The one-step layer recursion -/

/-- **The one-step tail recursion** `T k = Y k + r · T (k+1)` for the geometric
layer tail `T k = ∑'_j r^j · Y (k + j)`. -/
private theorem tsum_layer_succ {r : ℝ} (hr0 : 0 < r) {Y : ℤ → ℝ} (k : ℤ)
    (h : Summable (fun j : ℕ => r ^ j * Y (k + 1 + (j : ℤ)))) :
    ∑' j : ℕ, r ^ j * Y (k + (j : ℤ))
      = Y k + r * ∑' j : ℕ, r ^ j * Y (k + 1 + (j : ℤ)) := by
  have hk : Summable (fun j : ℕ => r ^ j * Y (k + (j : ℤ))) :=
    summable_layer_any hr0 Y (k + 1) k h
  have key : ∑' j : ℕ, r ^ j * Y (k + (j : ℤ))
      = r ^ (0 : ℕ) * Y (k + ((0 : ℕ) : ℤ))
        + ∑' b : ℕ, r ^ (b + 1) * Y (k + ((b + 1 : ℕ) : ℤ)) := hk.tsum_eq_zero_add
  have h0 : r ^ (0 : ℕ) * Y (k + ((0 : ℕ) : ℤ)) = Y k := by norm_num
  have key2 : ∑' b : ℕ, r ^ (b + 1) * Y (k + ((b + 1 : ℕ) : ℤ))
      = r * ∑' j : ℕ, r ^ j * Y (k + 1 + (j : ℤ)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    have harg : k + ((j + 1 : ℕ) : ℤ) = k + 1 + (j : ℤ) := by push_cast; ring
    rw [harg, pow_succ]
    ring
  rw [key, h0, key2]

/-! ## The finite window induction (abstract in the layer tail `T`) -/

/-- **The window induction.** If a nonnegative `T` obeys the one-step recursion
`T k = Y k + r · T (k+1)` for all `k ≥ n`, then over the window `[n, n+M]`

  `∑_{k=n}^{n+M} T k ≤ (1−r)⁻¹ · ∑_{l=n}^{n+M} Y l + r·(∑_{s ≤ M} r^s)·T (n+M+1)`.

The tail coefficient is kept as the **partial** geometric sum — this is what later
yields the `min(M+1, (1−r)⁻¹)` sharpening. -/
private theorem window_ind {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {T Y : ℤ → ℝ} (hY : ∀ l, 0 ≤ Y l) {n : ℤ}
    (hrec : ∀ k, n ≤ k → T k = Y k + r * T (k + 1)) :
    ∀ M : ℕ, ∑ k ∈ Finset.Icc n (n + (M : ℤ)), T k
      ≤ (1 - r)⁻¹ * (∑ l ∈ Finset.Icc n (n + (M : ℤ)), Y l)
        + r * (∑ s ∈ Finset.range (M + 1), r ^ s) * T (n + (M : ℤ) + 1) := by
  intro M
  induction M with
  | zero =>
    have h := hrec n le_rfl
    have hC : (1 : ℝ) ≤ (1 - r)⁻¹ := by
      have h1 := geom_partial_le_inv hr0 hr1 1
      simpa using h1
    have hYn : Y n ≤ (1 - r)⁻¹ * Y n := le_mul_of_one_le_left (hY n) hC
    simp only [Nat.cast_zero, add_zero, Finset.Icc_self, Finset.sum_singleton, zero_add,
      Finset.sum_range_one, pow_zero, mul_one]
    linarith only [h, hYn]
  | succ M ih =>
    have hcast : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by push_cast; ring
    rw [hcast, ← add_assoc]
    have hins : Finset.Icc n (n + (M : ℤ) + 1)
        = insert (n + (M : ℤ) + 1) (Finset.Icc n (n + (M : ℤ))) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (n + (M : ℤ) + 1) ∉ Finset.Icc n (n + (M : ℤ)) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hins, Finset.sum_insert hnot, Finset.sum_insert hnot]
    have hGrec : (∑ s ∈ Finset.range (M + 1 + 1), r ^ s)
        = r * (∑ s ∈ Finset.range (M + 1), r ^ s) + 1 := geom_sum_succ
    have hrecT : T (n + (M : ℤ) + 1)
        = Y (n + (M : ℤ) + 1) + r * T (n + (M : ℤ) + 1 + 1) := hrec _ (by omega)
    have hYle : (∑ s ∈ Finset.range (M + 1 + 1), r ^ s) * Y (n + (M : ℤ) + 1)
        ≤ (1 - r)⁻¹ * Y (n + (M : ℤ) + 1) :=
      mul_le_mul_of_nonneg_right (geom_partial_le_inv hr0 hr1 (M + 1 + 1)) (hY _)
    calc T (n + (M : ℤ) + 1) + ∑ k ∈ Finset.Icc n (n + (M : ℤ)), T k
        ≤ T (n + (M : ℤ) + 1)
            + ((1 - r)⁻¹ * (∑ l ∈ Finset.Icc n (n + (M : ℤ)), Y l)
              + r * (∑ s ∈ Finset.range (M + 1), r ^ s) * T (n + (M : ℤ) + 1)) := by
          linarith only [ih]
      _ = (1 - r)⁻¹ * (∑ l ∈ Finset.Icc n (n + (M : ℤ)), Y l)
            + (∑ s ∈ Finset.range (M + 1 + 1), r ^ s) * T (n + (M : ℤ) + 1) := by
          rw [hGrec]; ring
      _ = (1 - r)⁻¹ * (∑ l ∈ Finset.Icc n (n + (M : ℤ)), Y l)
            + (∑ s ∈ Finset.range (M + 1 + 1), r ^ s)
              * (Y (n + (M : ℤ) + 1) + r * T (n + (M : ℤ) + 1 + 1)) := by
          rw [← hrecT]
      _ ≤ (1 - r)⁻¹ * (Y (n + (M : ℤ) + 1) + ∑ l ∈ Finset.Icc n (n + (M : ℤ)), Y l)
            + r * (∑ s ∈ Finset.range (M + 1 + 1), r ^ s) * T (n + (M : ℤ) + 1 + 1) := by
          linarith only [hYle]

/-! ## The rearrangement at an abstract ratio `r ∈ (0,1)` -/

/-- **The window rearrangement, `npow` form.** Unconditional: no summability
hypothesis, and the `tsum` junk value is handled by an explicit case split. -/
private theorem rearrange_pow {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {Y : ℤ → ℝ} (hY : ∀ l, 0 ≤ Y l) {n m : ℤ} (hnm : n ≤ m) :
    ∑ k ∈ Finset.Icc n m, (∑' j : ℕ, r ^ j * Y (k + (j : ℤ)))
      ≤ (1 - r)⁻¹ * (∑ l ∈ Finset.Icc n m, Y l)
        + min (((m - n + 1 : ℤ) : ℝ)) ((1 - r)⁻¹)
            * ∑' j : ℕ, r ^ j * Y (m + 1 + (j : ℤ)) := by
  have h1r : 0 < 1 - r := by linarith only [hr1]
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = n + (M : ℤ) := ⟨(m - n).toNat, by omega⟩
  by_cases hs : Summable (fun j : ℕ => r ^ j * Y (n + (M : ℤ) + 1 + (j : ℤ)))
  · -- Summable case: the layer tails are genuine sums and obey the one-step recursion.
    have hsum : ∀ k : ℤ, Summable (fun j : ℕ => r ^ j * Y (k + (j : ℤ))) := fun k =>
      summable_layer_any hr0 Y _ k hs
    have hT : ∀ k : ℤ, 0 ≤ (∑' j : ℕ, r ^ j * Y (k + (j : ℤ))) := fun k =>
      tsum_nonneg fun j => mul_nonneg (pow_nonneg hr0.le j) (hY _)
    have hrec : ∀ k : ℤ, n ≤ k →
        (∑' j : ℕ, r ^ j * Y (k + (j : ℤ)))
          = Y k + r * ∑' j : ℕ, r ^ j * Y (k + 1 + (j : ℤ)) := fun k _ =>
      tsum_layer_succ hr0 k (hsum (k + 1))
    have hind : ∑ k ∈ Finset.Icc n (n + (M : ℤ)), (∑' j : ℕ, r ^ j * Y (k + (j : ℤ)))
        ≤ (1 - r)⁻¹ * (∑ l ∈ Finset.Icc n (n + (M : ℤ)), Y l)
          + r * (∑ s ∈ Finset.range (M + 1), r ^ s)
              * (∑' j : ℕ, r ^ j * Y (n + (M : ℤ) + 1 + (j : ℤ))) :=
      window_ind hr0.le hr1 hY hrec M
    have hGnonneg : 0 ≤ ∑ s ∈ Finset.range (M + 1), r ^ s :=
      Finset.sum_nonneg fun i _ => pow_nonneg hr0.le i
    have hshrink : r * (∑ s ∈ Finset.range (M + 1), r ^ s)
        ≤ ∑ s ∈ Finset.range (M + 1), r ^ s := by
      have hstep := mul_le_mul_of_nonneg_right hr1.le hGnonneg
      linarith only [hstep]
    have hcoef : r * (∑ s ∈ Finset.range (M + 1), r ^ s)
        ≤ min (((n + (M : ℤ) - n + 1 : ℤ) : ℝ)) ((1 - r)⁻¹) := by
      refine le_min ?_ ?_
      · have hc : (((n + (M : ℤ) - n + 1 : ℤ) : ℝ)) = ((M + 1 : ℕ) : ℝ) := by
          push_cast; ring
        rw [hc]
        exact le_trans hshrink (geom_partial_le_card hr0.le hr1 (M + 1))
      · exact le_trans hshrink (geom_partial_le_inv hr0.le hr1 (M + 1))
    have hstep := mul_le_mul_of_nonneg_right hcoef (hT (n + (M : ℤ) + 1))
    linarith only [hind, hstep]
  · -- Non-summable case: every layer tail on the left is the junk value `0`.
    have hzero : ∀ k : ℤ, (∑' j : ℕ, r ^ j * Y (k + (j : ℤ))) = 0 := fun k =>
      tsum_eq_zero_of_not_summable fun hcon => hs (summable_layer_any hr0 Y k _ hcon)
    have hW : 0 ≤ ∑ l ∈ Finset.Icc n (n + (M : ℤ)), Y l :=
      Finset.sum_nonneg fun i _ => hY i
    have hlhs :
        ∑ k ∈ Finset.Icc n (n + (M : ℤ)), (∑' j : ℕ, r ^ j * Y (k + (j : ℤ))) = 0 := by
      rw [Finset.sum_congr rfl fun k _ => hzero k, Finset.sum_const_zero]
    rw [hlhs, hzero (n + (M : ℤ) + 1), mul_zero, add_zero]
    exact mul_nonneg (inv_nonneg.2 h1r.le) hW

/-! ## The upward (Step-2) rearrangement -/

/-- **The Step-2 window rearrangement** (ABK26, `l.minimal.scale.sep` Step
2).  For a nonnegative layer field `Y : ℤ → ℝ` and a geometric decay rate `α
> 0`,

  `∑_{k=n}^{m} ∑_{l ≥ k} 3^{−α(l−k)} Y_l`

rearranges into a window sum with constant `Cgeo = (1 − 3^{−α})⁻¹` plus a
geometric tail beyond `m` with the sharper coefficient `min(m − n + 1, Cgeo)`.
No summability hypothesis: in the non-summable regime both sides degenerate to
the `tsum` junk value. -/
theorem window_geom_tail_rearrange
    {α : ℝ} (hα : 0 < α) {Y : ℤ → ℝ} (hY : ∀ l, 0 ≤ Y l) {n m : ℤ} (hnm : n ≤ m) :
    ∑ k ∈ Finset.Icc n m, (∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * Y (k + (j : ℤ)))
      ≤ (1 - (3 : ℝ) ^ (-α))⁻¹ * (∑ l ∈ Finset.Icc n m, Y l)
        + min (((m - n + 1 : ℤ) : ℝ)) ((1 - (3 : ℝ) ^ (-α))⁻¹)
            * (∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * Y (m + 1 + (j : ℤ))) := by
  have hrw : ∀ a : ℤ, (∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * Y (a + (j : ℤ)))
      = ∑' j : ℕ, ((3 : ℝ) ^ (-α)) ^ j * Y (a + (j : ℤ)) := fun a =>
    tsum_congr fun j => by rw [threePow_neg_natMul]
  simp only [hrw]
  exact rearrange_pow (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hα])) hY hnm

/-- **Crude corollary**: the same rearrangement with the single constant
`Cgeo = (1 − 3^{−α})⁻¹` in front of both the window sum and the off-window tail.
Weaker than `window_geom_tail_rearrange` (which sharpens the tail coefficient to
`min(m − n + 1, Cgeo)`), but often the convenient shape. -/
theorem window_geom_tail_rearrange_le
    {α : ℝ} (hα : 0 < α) {Y : ℤ → ℝ} (hY : ∀ l, 0 ≤ Y l) {n m : ℤ} (hnm : n ≤ m) :
    ∑ k ∈ Finset.Icc n m, (∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * Y (k + (j : ℤ)))
      ≤ (1 - (3 : ℝ) ^ (-α))⁻¹ *
          (∑ l ∈ Finset.Icc n m, Y l
            + ∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * Y (m + 1 + (j : ℤ))) := by
  have h := window_geom_tail_rearrange hα hY hnm
  have htail : 0 ≤ ∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * Y (m + 1 + (j : ℤ)) :=
    tsum_nonneg fun j => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hY _)
  have hmin := mul_le_mul_of_nonneg_right
    (min_le_right (((m - n + 1 : ℤ) : ℝ)) ((1 - (3 : ℝ) ^ (-α))⁻¹)) htail
  linarith only [h, hmin]

/-! ## The downward (Step-1) reflection -/

/-- **The Step-1 window rearrangement**.  The reflection `l ↦ −l` of
`window_geom_tail_rearrange`: a window sum of *downward* geometric layer tails
splits into the window sum plus a head below `n`, with the sharp `min`
coefficient on the head. -/
theorem window_geom_head_rearrange
    {α : ℝ} (hα : 0 < α) {X : ℤ → ℝ} (hX : ∀ l, 0 ≤ X l) {n m : ℤ} (hnm : n ≤ m) :
    ∑ k ∈ Finset.Icc n m, (∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * X (k - (j : ℤ)))
      ≤ (1 - (3 : ℝ) ^ (-α))⁻¹ * (∑ l ∈ Finset.Icc n m, X l)
        + min (((m - n + 1 : ℤ) : ℝ)) ((1 - (3 : ℝ) ^ (-α))⁻¹)
            * (∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * X (n - 1 - (j : ℤ))) := by
  have hmn : -m ≤ -n := by omega
  have hbase := window_geom_tail_rearrange (α := α) hα
    (Y := fun l => X (-l)) (fun l => hX (-l)) hmn
  -- Reindex both finite sums by `k ↦ -k`.
  have hL : ∑ k ∈ Finset.Icc (-m) (-n),
        (∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * X (-(k + (j : ℤ))))
      = ∑ k ∈ Finset.Icc n m,
        (∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * X (k - (j : ℤ))) := by
    refine Finset.sum_nbij' (fun a => -a) (fun a => -a) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a _; exact neg_neg a
    · intro a _; exact neg_neg a
    · intro a _
      refine tsum_congr (fun j => ?_)
      have hj : -(a + (j : ℤ)) = -a - (j : ℤ) := by ring
      rw [hj]
  have hW : ∑ l ∈ Finset.Icc (-m) (-n), X (-l) = ∑ l ∈ Finset.Icc n m, X l := by
    refine Finset.sum_nbij' (fun a => -a) (fun a => -a) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a _; exact neg_neg a
    · intro a _; exact neg_neg a
    · intro a _; rfl
  have hT : ∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * X (-(-n + 1 + (j : ℤ)))
      = ∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * X (n - 1 - (j : ℤ)) := by
    refine tsum_congr (fun j => ?_)
    have hj : -(-n + 1 + (j : ℤ)) = n - 1 - (j : ℤ) := by ring
    rw [hj]
  have hcard : ((-n - -m + 1 : ℤ) : ℝ) = ((m - n + 1 : ℤ) : ℝ) := by
    norm_cast; omega
  rw [hL, hW, hT, hcard] at hbase
  exact hbase

end Algsuperdiff.Probability
