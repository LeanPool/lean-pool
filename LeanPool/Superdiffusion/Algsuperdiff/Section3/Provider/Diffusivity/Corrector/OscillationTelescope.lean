/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# OscillationTelescope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The nested-recentring accumulation behind `e.nablaw.oscillations`

ABK26 states `e.nablaw.oscillations` on the triadic cubes `z + cu_n subset z +
cu_{m-h}`, and proves it by writing down a one-step estimate on the concentric
Euclidean *balls* `B_r(z) subset B_{3r}(z)` followed by the words "and
iterating this yields".

So the adjacent-cube recurrence that a naive cube reading of the manuscript
would iterate simply does not hold.

Concretely, on the nested triadic cubes `U_j := z + cu_{n+j}`, `0 <= j <= N`,
one writes the fine-scale field as a finite sum of harmonic increments born at
each scale,

```
  g = u_N + sum_{j < N} (u_j - u_{j+1}) + (g - u_0)   on U_0 ,
```

and estimates the oscillation on `U_0` of each summand *directly from its own
birth scale*, never through a chain of adjacent-scale contractions.  Each
increment born at scale `j` is therefore hit once by the arbitrary-gap factor
`3^{-j}` and once by the birth-scale forcing size `3^{n+j}`; the two cancel, so
the forcing accumulates **linearly** in `N` while the coarse term keeps the full
geometric factor `3^{-N}`.  That is exactly the shape of the printed display,
obtained without the false adjacent-cube contraction.

## Contents

* `zpow_neg_natCast_mul_zpow_add` -- the single cancellation `3^{-j} * 3^{n+j} =
  3^n` on which the whole mechanism rests.
* `sum_zpow_neg_mul_le_nsmul_of_triadic_bound` -- the accumulation
  `sum_{j < N} A * 3^{-j} * (E j + rho * E (j+1)) <= N * A (1 + 3 rho) * 3^n * c`
  under the birth-scale bound `E j <= c * 3^{n+j}`.
* `le_zpow_mul_add_nsmul_of_nested_decomposition` -- the display-shaped
  assembly `Phi 0 <= A * 3^{-N} * Phi N + (A (1 + 3 rho) N + A + 2) * 3^n * c`.

## References

* ABK26, `e.nablaw.oscillations`, statement and the ball one-step estimate and
  the word "iterating".
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

/-- `3^{-j} * 3^{n+j} = 3^n`: the arbitrary-gap harmonic factor for an increment
born at scale `j` exactly cancels the birth-scale size of the forcing.  This one
cancellation is the reason the forcing in `e.nablaw.oscillations` accumulates
linearly rather than geometrically. -/
theorem zpow_neg_natCast_mul_zpow_add (n : ℤ) (j : ℕ) :
    (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (n + (j : ℤ)) = (3 : ℝ) ^ n := by
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  ring

/-- **The birth-scale accumulation.**

If the per-scale error `E j` obeys the birth-scale bound `E j <= c * 3^{n+j}`
for every `j <= N`, then weighting the scale-`j` term by the arbitrary-gap
factor `3^{-j}` makes every summand equal in size, so the sum grows only
linearly:

```
  sum_{j < N} A * 3^{-j} * (E j + rho * E (j+1))
    <= N * (A * (1 + 3 rho) * (3^n * c)) .
```

The `rho * E (j+1)` term carries the volume ratio incurred when the harmonic
approximation born at scale `j+1` is restricted to the cube of scale `j`. -/
theorem sum_zpow_neg_mul_le_nsmul_of_triadic_bound {E : ℕ → ℝ} {n : ℤ} {N : ℕ}
    {A rho c : ℝ} (hA : 0 ≤ A) (hrho : 0 ≤ rho)
    (hE : ∀ j ≤ N, E j ≤ c * (3 : ℝ) ^ (n + (j : ℤ))) :
    ∑ j ∈ Finset.range N, A * (3 : ℝ) ^ (-(j : ℤ)) * (E j + rho * E (j + 1)) ≤
      (N : ℝ) * (A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c)) := by
  have hterm : ∀ j ∈ Finset.range N,
      A * (3 : ℝ) ^ (-(j : ℤ)) * (E j + rho * E (j + 1)) ≤
        A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c) := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hEj : E j ≤ c * (3 : ℝ) ^ (n + (j : ℤ)) := hE j hjN.le
    have hEj1 : E (j + 1) ≤ c * ((3 : ℝ) ^ (n + (j : ℤ)) * 3) := by
      have h := hE (j + 1) hjN
      have hcast : (3 : ℝ) ^ (n + ((j + 1 : ℕ) : ℤ)) = (3 : ℝ) ^ (n + (j : ℤ)) * 3 := by
        have hidx : n + ((j + 1 : ℕ) : ℤ) = (n + (j : ℤ)) + 1 := by push_cast; ring
        rw [hidx, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
      rwa [hcast] at h
    have hwpos : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_pos (by norm_num) _
    have hscaled : rho * E (j + 1) ≤ rho * (c * ((3 : ℝ) ^ (n + (j : ℤ)) * 3)) :=
      mul_le_mul_of_nonneg_left hEj1 hrho
    have hinner : E j + rho * E (j + 1) ≤
        (1 + 3 * rho) * ((3 : ℝ) ^ (n + (j : ℤ)) * c) := by linarith
    have hfac : (0 : ℝ) ≤ A * (3 : ℝ) ^ (-(j : ℤ)) := mul_nonneg hA hwpos.le
    calc A * (3 : ℝ) ^ (-(j : ℤ)) * (E j + rho * E (j + 1))
        ≤ A * (3 : ℝ) ^ (-(j : ℤ)) *
            ((1 + 3 * rho) * ((3 : ℝ) ^ (n + (j : ℤ)) * c)) :=
          mul_le_mul_of_nonneg_left hinner hfac
      _ = A * (1 + 3 * rho) *
            (((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (n + (j : ℤ))) * c) := by ring
      _ = A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c) := by
          rw [zpow_neg_natCast_mul_zpow_add]
  calc ∑ j ∈ Finset.range N, A * (3 : ℝ) ^ (-(j : ℤ)) * (E j + rho * E (j + 1))
      ≤ ∑ _j ∈ Finset.range N, A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c) :=
        Finset.sum_le_sum hterm
    _ = (N : ℝ) * (A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The display-shaped assembly of the nested-recentring route.**

Suppose the fine-scale oscillation `Phi 0` has a decomposition into a coarse
harmonic term `T`, finitely many harmonic increments `S j` born at the
intermediate scales `j < N`, and a fine-scale approximation defect (`hsplit`);
suppose the coarse term obeys the arbitrary-gap estimate from scale `N` directly
to scale `0` (`hT`); suppose each increment obeys the arbitrary-gap estimate
from its own birth scale `j` directly to scale `0` (`hS`); and suppose the
approximation errors obey the birth-scale bound `E j <= c * 3^{n+j}` (`hE`).
Then

```
  Phi 0 <= A * 3^{-N} * Phi N + (A (1 + 3 rho) N + A + 2) * (3^n * c) ,
```

which is the shape of `e.nablaw.oscillations` with `N = m - h - n`: the full
geometric gain `3^{-(m-h-n)}` on the coarse oscillation and a forcing term
linear in `m - h - n` carrying the single factor `3^n`.

Every hypothesis is an *input to be discharged elsewhere*; see the module
disclosure.  Nothing here asserts that any of them holds, and this statement
claims no source node. -/
theorem le_zpow_mul_add_nsmul_of_nested_decomposition {Phi E S : ℕ → ℝ} {T : ℝ}
    {n : ℤ} {N : ℕ} {A rho c : ℝ} (hA : 0 ≤ A) (hrho : 0 ≤ rho)
    (hE : ∀ j ≤ N, E j ≤ c * (3 : ℝ) ^ (n + (j : ℤ)))
    (hsplit : Phi 0 ≤ T + (∑ j ∈ Finset.range N, S j) + 2 * E 0)
    (hT : T ≤ A * (3 : ℝ) ^ (-(N : ℤ)) * (Phi N + E N))
    (hS : ∀ j < N, S j ≤ A * (3 : ℝ) ^ (-(j : ℤ)) * (E j + rho * E (j + 1))) :
    Phi 0 ≤ A * (3 : ℝ) ^ (-(N : ℤ)) * Phi N +
      (A * (1 + 3 * rho) * (N : ℝ) + A + 2) * ((3 : ℝ) ^ n * c) := by
  -- The coarse term keeps the full geometric factor, and its own error is
  -- flattened by the same cancellation `3^{-N} * 3^{n+N} = 3^n`.
  have hTbound : T ≤ A * (3 : ℝ) ^ (-(N : ℤ)) * Phi N + A * ((3 : ℝ) ^ n * c) := by
    have hEN : E N ≤ c * (3 : ℝ) ^ (n + (N : ℤ)) := hE N le_rfl
    have hwpos : (0 : ℝ) < (3 : ℝ) ^ (-(N : ℤ)) := zpow_pos (by norm_num) _
    have hfac : (0 : ℝ) ≤ A * (3 : ℝ) ^ (-(N : ℤ)) := mul_nonneg hA hwpos.le
    have hstep : A * (3 : ℝ) ^ (-(N : ℤ)) * (Phi N + E N) ≤
        A * (3 : ℝ) ^ (-(N : ℤ)) * (Phi N + c * (3 : ℝ) ^ (n + (N : ℤ))) :=
      mul_le_mul_of_nonneg_left (by linarith) hfac
    have hflat : A * (3 : ℝ) ^ (-(N : ℤ)) * (Phi N + c * (3 : ℝ) ^ (n + (N : ℤ))) =
        A * (3 : ℝ) ^ (-(N : ℤ)) * Phi N +
          A * (((3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ (n + (N : ℤ))) * c) := by ring
    rw [hflat, zpow_neg_natCast_mul_zpow_add] at hstep
    exact hT.trans hstep
  -- The increments accumulate linearly.
  have hsum : ∑ j ∈ Finset.range N, S j ≤
      (N : ℝ) * (A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c)) :=
    le_trans (Finset.sum_le_sum fun j hj => hS j (Finset.mem_range.mp hj))
      (sum_zpow_neg_mul_le_nsmul_of_triadic_bound hA hrho hE)
  -- The fine-scale defect is one further copy of the birth-scale size at `j = 0`.
  have hdefect : 2 * E 0 ≤ 2 * ((3 : ℝ) ^ n * c) := by
    have h0 := hE 0 (Nat.zero_le N)
    have hz : (3 : ℝ) ^ (n + ((0 : ℕ) : ℤ)) = (3 : ℝ) ^ n := by norm_num
    rw [hz] at h0
    linarith
  have hcollect :
      (N : ℝ) * (A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c)) + A * ((3 : ℝ) ^ n * c) +
          2 * ((3 : ℝ) ^ n * c) =
        (A * (1 + 3 * rho) * (N : ℝ) + A + 2) * ((3 : ℝ) ^ n * c) := by ring
  linarith [hsplit, hTbound, hsum, hdefect, hcollect.ge, hcollect.le]

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
