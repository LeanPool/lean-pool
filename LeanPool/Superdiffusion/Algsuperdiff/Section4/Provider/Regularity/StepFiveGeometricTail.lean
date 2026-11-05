/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# StepFiveGeometricTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 5: the geometric tail of the `δ_j` series

## The target

ABK26 `t.regularity` Step 5: "Summing the series for the `δ_j` terms".  Both
non-`ε` legs of `δ_j` are geometrically dominated from the TOP scale `m`
downwards,

```text
   3^{j/2} σ_j^{-1}  ≤  C 3^{-(1/2 - γ)(m-j)} · 3^{m/2} σ_m^{-1} ,
   3^{j/2}            =      3^{-(1/2)(m-j)} · 3^{m/2} ,
```

so each contributes a convergent geometric series `∑_{j=n}^{m-1} r^{m-j}` with
`r ∈ (0,1)`, bounded by `r/(1-r)` uniformly in `n` and `m`.  This module is the
pure-real algebra of that summation, over an abstract ratio `r` and an abstract
dominated family, with no `rpow` and no `exp` anywhere: the caller supplies `r
:= 3^{-(1/2-γ)}` (resp.  `3^{-1/2}`) as an already-formed real in `(0,1)`, and
the integer exponent `m - j` is a `zpow`.

The partial sum is computed sharply (`sum_Icc_le_of_zpow_dominated_sharp`), because
the crude bound `r/(1-r)` is not preserved by the downward induction — adding a
term at the bottom of the window needs the exact residual `(r -
r^{m-n+1})/(1-r)`.

## References

* ABK26, `t.regularity` Step 5, (`e.sum.delta.j.bound`).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

/-! ## 1. Interval bookkeeping -/

/-- Extending a `ℤ`-interval by one step at the BOTTOM. -/
theorem Icc_sub_one_left_eq_insert {n M : ℤ} (h : n - 1 ≤ M) :
    Finset.Icc (n - 1) M = insert (n - 1) (Finset.Icc n M) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-! ## 2. The scalar step of the downward induction -/

/-- The one-step algebra of the sharp geometric partial sum: if the new bottom term
`F` is at most `K A` and the sum above it has residual `K(r - A)`, then the
extended sum has residual `K(r - A r)`.  Every atom is an abstract real; no
`zpow`, no `rpow`. -/
theorem geomTail_step {r K A F S : ℝ} (h1r : 0 < 1 - r) (hF : F ≤ K * A)
    (hS : (1 - r) * S ≤ K * (r - A)) :
    (1 - r) * F + (1 - r) * S ≤ K * (r - A * r) := by
  have h1 : (1 - r) * F ≤ (1 - r) * (K * A) :=
    mul_le_mul_of_nonneg_left hF h1r.le
  linarith only [h1, hS]

/-! ## 3. The sharp partial sum -/

/-- **The sharp geometric partial-sum bound.**  For a nonnegative family `f`
dominated from the top scale, `f j ≤ K r^{m-j}` with `0 < r < 1`,

```text
   (1 - r) · ∑_{j=n}^{m-1} f j  ≤  K (r - r^{m-n+1}) .
```

Proved by downward induction on `n` from `m`, which is why the sharp form is
needed: the crude bound is not an inductive invariant. -/
theorem mul_sum_Icc_le_of_zpow_dominated {r K : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {f : ℤ → ℝ} {m : ℤ} (hdom : ∀ j : ℤ, j ≤ m → f j ≤ K * r ^ (m - j)) :
    ∀ n : ℤ, n ≤ m →
      (1 - r) * ∑ j ∈ Finset.Icc n (m - 1), f j ≤ K * (r - r ^ (m - n + 1)) := by
  have h1r : (0 : ℝ) < 1 - r := by linarith only [hr1]
  have hrne : r ≠ 0 := ne_of_gt hr0
  intro n hn
  induction n, hn using Int.leInductionDown with
  | base =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      have hz : m - m + 1 = (1 : ℤ) := by omega
      rw [hz, zpow_one]
      simp
  | pred n hn ih =>
      have hsplit : Finset.Icc (n - 1) (m - 1) = insert (n - 1) (Finset.Icc n (m - 1)) :=
        Icc_sub_one_left_eq_insert (by omega)
      have hnotmem : (n - 1) ∉ Finset.Icc n (m - 1) := by
        simp only [Finset.mem_Icc]
        omega
      have hsum : ∑ j ∈ Finset.Icc (n - 1) (m - 1), f j
          = f (n - 1) + ∑ j ∈ Finset.Icc n (m - 1), f j := by
        rw [hsplit, Finset.sum_insert hnotmem]
      have hexp1 : m - (n - 1) = m - n + 1 := by omega
      have hexp2 : m - (n - 1) + 1 = (m - n + 1) + 1 := by omega
      have hF : f (n - 1) ≤ K * r ^ (m - n + 1) := by
        have hd := hdom (n - 1) (by omega)
        rwa [hexp1] at hd
      have hpow : r ^ (m - (n - 1) + 1) = r ^ (m - n + 1) * r := by
        rw [hexp2, zpow_add_one₀ hrne]
      rw [hsum, hpow, mul_add]
      exact geomTail_step h1r hF ih

/-- **The geometric tail, in the form Step 5 uses**: for a nonnegative family
dominated by `K r^{m-j}` from the top scale `m`,

```text
   ∑_{j=n}^{m-1} f j  ≤  K r / (1 - r)          uniformly in n ≤ m .
```

The uniformity in `n` is the whole point: `e.sum.delta.j.bound` has no `(m-n)`
factor on its two geometric legs. -/
theorem sum_Icc_le_of_zpow_dominated {r K : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {f : ℤ → ℝ} {n m : ℤ} (hn : n ≤ m) (hf0 : 0 ≤ f m)
    (hdom : ∀ j : ℤ, j ≤ m → f j ≤ K * r ^ (m - j)) :
    ∑ j ∈ Finset.Icc n (m - 1), f j ≤ K * r / (1 - r) := by
  have h1r : (0 : ℝ) < 1 - r := by linarith only [hr1]
  have hK : 0 ≤ K := by
    have hd := hdom m le_rfl
    have h0 : m - m = (0 : ℤ) := by omega
    rw [h0, zpow_zero, mul_one] at hd
    linarith only [hf0, hd]
  have hpow : 0 < r ^ (m - n + 1) := zpow_pos hr0 _
  have hmain := mul_sum_Icc_le_of_zpow_dominated hr0 hr1 hdom n hn
  have hslack : K * (r - r ^ (m - n + 1)) ≤ K * r :=
    mul_le_mul_of_nonneg_left (by linarith only [hpow]) hK
  rw [le_div_iff₀ h1r]
  linarith only [hmain, hslack]

end Algsuperdiff.Section4.Provider.Regularity
