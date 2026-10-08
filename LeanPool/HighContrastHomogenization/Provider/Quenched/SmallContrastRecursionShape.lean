/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Scalar.DecayDelay
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastRecursionShape

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Shaping the small-contrast weak value onto the iteration lemma

The one-step estimate produces, at generation `n`, a *depth-indexed* weighted
sum of hatted drops

  `∑_{j ≤ H_w} r^j (F(n-j) - F(n))`,

whereas the cited iteration lemma
(`Prop42Scalar.HistoryIterationDecay.akbook_iteration_decay`) consumes a
*generation-indexed* weighted sum of consecutive increments

  `∑_{k ∈ [1,n]} r^{n-k} (F(k-1) - F(k))`.

This file proves the exact conversion between the two (`lagged_drop_sum_le`),
with the geometric constant `(1-r)^{-1}` and no dependence on the depth `H_w`
— which is what makes the shaping legitimate when the window reaches back to
the entry scale.  The proof is a one-line induction on a strengthened
invariant carrying the tail `r^N(1-r)^{-1}G_N`; no double-sum exchange is
needed.

Two further scalar facts are recorded, both used when the *square* of the
weak value is regrouped:

* `sum_weighted_sqrt_sq_le` — the Cauchy–Schwarz regroup that turns the
  rooted drop sum `∑ w_j √(c·D_j)` into the linear drop sum `∑ w_j D_j`
  (this is what makes the drops enter the recursion linearly, as HC (4.17)
  requires);
* `sq_add_three_le` — the three-term square split of the weak value into its
  variance, source and centering groups.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-! ## The depth-to-generation conversion -/

/-- The scalar induction step of the invariant. -/
private theorem geom_step {r u sg gn sa aN rN : ℝ} (hu : u * (1 - r) = 1)
    (ih : sg + rN * u * gn ≤ u * sa) :
    sg + rN * gn + rN * r * u * (gn + aN) ≤ u * (sa + rN * r * aN) := by
  have hlin : u - r * u = 1 := by linear_combination hu
  have hkey : rN * gn * (u - r * u) = rN * gn := by
    rw [hlin]
    ring
  nlinarith only [ih, hkey]

/-- The strengthened invariant: the weighted partial sums of the increments,
with the geometric tail carried explicitly. -/
private theorem geom_partial_sum_invariant {r : ℝ} (hr1 : r < 1)
    (a : ℕ → ℝ) :
    ∀ N : ℕ,
      (∑ j ∈ Finset.range N, r ^ j * ∑ i ∈ Finset.range j, a i) +
          r ^ N * (1 - r)⁻¹ * ∑ i ∈ Finset.range N, a i ≤
        (1 - r)⁻¹ * ∑ i ∈ Finset.range N, r ^ (i + 1) * a i := by
  have hden : 0 < 1 - r := by linarith only [hr1]
  have hu : (1 - r)⁻¹ * (1 - r) = 1 := inv_mul_cancel₀ (ne_of_gt hden)
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have hstep := geom_step (r := r) (u := (1 - r)⁻¹)
        (sg := ∑ j ∈ Finset.range N, r ^ j * ∑ i ∈ Finset.range j, a i)
        (gn := ∑ i ∈ Finset.range N, a i)
        (sa := ∑ i ∈ Finset.range N, r ^ (i + 1) * a i)
        (aN := a N) (rN := r ^ N) hu ih
      rw [Finset.sum_range_succ (f := fun j => r ^ j * ∑ i ∈ Finset.range j, a i),
        Finset.sum_range_succ (f := fun i => a i),
        Finset.sum_range_succ (f := fun i => r ^ (i + 1) * a i)]
      have hpow : r ^ (N + 1) = r ^ N * r := by ring
      rw [hpow]
      have hcomm : r ^ N * r * (1 - r)⁻¹ = r ^ N * r * (1 - r)⁻¹ := rfl
      linarith only [hstep, hcomm]

/-- **The depth-indexed drop sum is dominated by the generation-indexed
increment sum.**  For a nonincreasing sequence `F` and a geometric weight
`r ∈ [0,1)`,

  `∑_{j < N} r^j (F(n-j) - F n) ≤ (1-r)^{-1} ∑_{k ∈ [1,n]} r^{n-k}(F(k-1) - F k)`

whenever `N ≤ n`.  The right side is exactly the drop-history sum the
iteration decay consumes. -/
theorem lagged_drop_sum_le {F : ℕ → ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {n N : ℕ} (hN : N ≤ n) :
    ∑ j ∈ Finset.range N, r ^ j * (F (n - j) - F n) ≤
      (1 - r)⁻¹ * ∑ k ∈ Finset.Icc 1 n, r ^ (n - k) * (F (k - 1) - F k) := by
  classical
  have hden : 0 < 1 - r := by linarith only [hr1]
  set a : ℕ → ℝ := fun i => F (n - i - 1) - F (n - i) with ha
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i
    have h : F (n - i) ≤ F (n - i - 1) := hFmono _ _ (Nat.sub_le _ _)
    simpa only [ha] using sub_nonneg.mpr h
  -- the partial sums of the increments telescope to the drops
  have hG : ∀ j : ℕ, ∑ i ∈ Finset.range j, a i = F (n - j) - F n := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Finset.sum_range_succ, ih, ha]
        have hstep : n - (j + 1) = n - j - 1 := by omega
        rw [hstep]
        ring
  -- the invariant, dropping the nonnegative tail
  have hinv := geom_partial_sum_invariant hr1 a N
  have htail : (0 : ℝ) ≤ r ^ N * (1 - r)⁻¹ * ∑ i ∈ Finset.range N, a i := by
    have h1 : (0 : ℝ) ≤ r ^ N := pow_nonneg hr0 N
    have h2 : (0 : ℝ) ≤ (1 - r)⁻¹ := le_of_lt (inv_pos.mpr hden)
    have h3 : (0 : ℝ) ≤ ∑ i ∈ Finset.range N, a i :=
      Finset.sum_nonneg fun i _ => ha0 i
    positivity
  have hstep1 : ∑ j ∈ Finset.range N, r ^ j * (F (n - j) - F n) ≤
      (1 - r)⁻¹ * ∑ i ∈ Finset.range N, r ^ (i + 1) * a i := by
    have hrw : ∑ j ∈ Finset.range N, r ^ j * (F (n - j) - F n) =
        ∑ j ∈ Finset.range N, r ^ j * ∑ i ∈ Finset.range j, a i := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hG j]
    rw [hrw]
    linarith only [hinv, htail]
  -- the weight `r^{i+1}` is below `r^i`, and `range N ⊆ range n`
  have hstep2 : ∑ i ∈ Finset.range N, r ^ (i + 1) * a i ≤
      ∑ i ∈ Finset.range n, r ^ i * a i := by
    have hsub : Finset.range N ⊆ Finset.range n := by
      intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => ?_))
    · have hle : r ^ (i + 1) ≤ r ^ i := by
        have : r ^ (i + 1) = r ^ i * r := by ring
        rw [this]
        nlinarith only [pow_nonneg hr0 i, hr1, hr0]
      exact mul_le_mul_of_nonneg_right hle (ha0 i)
    · exact mul_nonneg (pow_nonneg hr0 i) (ha0 i)
  -- reindex `i ↦ n - i`
  have hreindex : ∑ i ∈ Finset.range n, r ^ i * a i =
      ∑ k ∈ Finset.Icc 1 n, r ^ (n - k) * (F (k - 1) - F k) := by
    refine Finset.sum_nbij' (fun i => n - i) (fun k => n - k) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_Icc]
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      show n - (n - i) = i
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      show n - (n - k) = k
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      have h1 : n - (n - i) = i := by omega
      rw [h1, ha]
  have hinv0 : (0 : ℝ) ≤ (1 - r)⁻¹ := le_of_lt (inv_pos.mpr hden)
  calc ∑ j ∈ Finset.range N, r ^ j * (F (n - j) - F n)
      ≤ (1 - r)⁻¹ * ∑ i ∈ Finset.range N, r ^ (i + 1) * a i := hstep1
    _ ≤ (1 - r)⁻¹ * ∑ i ∈ Finset.range n, r ^ i * a i :=
        mul_le_mul_of_nonneg_left hstep2 hinv0
    _ = (1 - r)⁻¹ * ∑ k ∈ Finset.Icc 1 n, r ^ (n - k) * (F (k - 1) - F k) := by
        rw [hreindex]

/-- The real-power weight of the weak value is the natural power of the
one-step ratio. -/
theorem rpow_weight_eq_pow {mu : ℝ} (j : ℕ) :
    (3 : ℝ) ^ (-mu * (j : ℝ)) = ((3 : ℝ) ^ (-mu)) ^ j := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-mu)) j, ← Real.rpow_mul (by norm_num)]

/-! ## The Cauchy–Schwarz regroup of the rooted drop sum -/

/-- **The Cauchy–Schwarz regroup.**  A weighted sum of square roots of drops
squares to a weighted *linear* sum of the drops, with the total weight as the
constant.  This is the step that keeps the drops linear in the recursion. -/
theorem sum_weighted_sqrt_sq_le {ι : Type*} (s : Finset ι) (w D : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hD : ∀ i ∈ s, 0 ≤ D i) {c : ℝ} (hc : 0 ≤ c) :
    (∑ i ∈ s, w i * Real.sqrt (c * D i)) ^ 2 ≤
      (∑ i ∈ s, w i) * (c * ∑ i ∈ s, w i * D i) := by
  classical
  have hkey : ∀ i ∈ s,
      w i * Real.sqrt (c * D i) =
        Real.sqrt (w i) * Real.sqrt (w i * (c * D i)) := by
    intro i hi
    rw [Real.sqrt_mul (hw i hi), ← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have hrw : ∑ i ∈ s, w i * Real.sqrt (c * D i) =
      ∑ i ∈ s, Real.sqrt (w i) * Real.sqrt (w i * (c * D i)) :=
    Finset.sum_congr rfl hkey
  rw [hrw]
  refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i * (c * D i)))) ?_
  have h1 : ∑ i ∈ s, Real.sqrt (w i) ^ 2 = ∑ i ∈ s, w i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hw i hi)
  have h2 : ∑ i ∈ s, Real.sqrt (w i * (c * D i)) ^ 2 =
      c * ∑ i ∈ s, w i * D i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Real.sq_sqrt (mul_nonneg (hw i hi) (mul_nonneg hc (hD i hi)))]
    ring
  rw [h1, h2]

/-! ## The three-term square split -/

/-- **The three-term square split** of the weak value into its variance,
source and centering groups. -/
theorem sq_add_three_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- The square of a weighted linear drop sum is linear in the drop sum once
the drops are uniformly small. -/
theorem sq_sum_le_of_le {ι : Type*} (s : Finset ι) (w D : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hD : ∀ i ∈ s, 0 ≤ D i)
    {delta : ℝ} (hdelta : ∀ i ∈ s, D i ≤ delta) :
    (∑ i ∈ s, w i * D i) ^ 2 ≤
      (delta * ∑ i ∈ s, w i) * ∑ i ∈ s, w i * D i := by
  have h0 : 0 ≤ ∑ i ∈ s, w i * D i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hD i hi)
  have hle : ∑ i ∈ s, w i * D i ≤ delta * ∑ i ∈ s, w i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [mul_comm delta (w i)]
    exact mul_le_mul_of_nonneg_left (hdelta i hi) (hw i hi)
  calc (∑ i ∈ s, w i * D i) ^ 2 = (∑ i ∈ s, w i * D i) * ∑ i ∈ s, w i * D i := sq _
    _ ≤ (delta * ∑ i ∈ s, w i) * ∑ i ∈ s, w i * D i :=
        mul_le_mul_of_nonneg_right hle h0

end

end HCPolySupport.HighContrast.Quenched
