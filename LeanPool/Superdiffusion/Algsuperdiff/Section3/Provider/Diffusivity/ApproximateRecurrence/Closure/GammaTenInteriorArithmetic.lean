/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorGeometry

/-!
# GammaTenInteriorArithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The depth fold closes: the linear factor of the depth endpoints is summable

ABK26, Step 2 of `l.approximate.recurrence.formula`,
`e.lower.bound.oscillations`.

## The one inequality that has to be honest

The depth-indexed endpoints of `Closure.GammaTenDepthOscillation` carry the decay
factor `(1 + i) 3^{-i}`, **not** the bare `3^{-i}`: the linear factor of the
buffer `N_i = Ngap + i` is genuinely there.  At the fourth power the per-depth
input of the Besov fold is therefore

```
  D i  =  cgamma^{64} (1+i)^4 3^{-4i}  =  cgamma^{64} (1+i)^4 81^{-i} ,
```

while the fold's own weights are `2^{i+1} 3^{4 s i} = 2^{i+1} 9^i` at the
closure's exponent `s = gammaTenBesovExponent = 1/2`.  The ratio gate of
`Closure.GammaTenEnvelopeInputGrid.sum_two_pow_mul_rpow_pow_four_geometric_le`
is `2 . 9 . r <= 1/2`, i.e. `r <= 1/36`, so what must be true is

```
  (1 + i)^4 81^{-i}  <=  25 . 36^{-i}   for every i ,
```

equivalently the integer inequality `(1+i)^4 4^i <= 25 . 9^i`.  That is
`succ_pow_four_mul_four_pow_le`, and it is **tight**: at `i = 4` the two sides
are `625 . 256 = 160000` and `25 . 6561 = 164025`.  It is proved here by
induction from `i = 4` --- the four smaller cases are checked directly, because
the induction step `4 (i+2)^4 <= 9 (i+1)^4` is false for `i <= 3`.

Everything downstream is bookkeeping: with the refinement cost `2` of
`Closure.GammaTenInteriorGeometry` the fold input is `A r^i` at
`A = 50 cgamma^{64}` and `r = 1/36`, the fold sum is below `4 A = 200 cgamma^{64}`,
and `200 cgamma^{64} <= cgamma^{60}` because `200 (1/4)^4 = 200/256 < 1`.  The
resulting envelope's grid fourth-moment **root** is therefore below
`(cgamma^{60})^{1/4} = cgamma^{15}`, which is exactly the threshold
`Closure.GammaTenCloserAssembly.ClosureBesovEnvelopeInput` demands.

## What is proved

* `succ_pow_four_mul_four_pow_le` --- the integer inequality.
* `depth_decay_pow_four_le` --- its real form, at the depth endpoints' own decay
  factor.
* `gridFourthMoment_le_pow_four_of_root_le` --- the fourth moment from its root.

The composite --- the fold sum of the depth endpoints' fourth powers, with the
refinement cost included --- is assembled on top of these in
`Closure.GammaTenStripEnvelopeConst.sum_depth_fold_const_le`, which stops at
`200 A^4 cgamma^{64}` and leaves the closing numerical step in `cgamma` to its
caller.

## Binders

Elementary arithmetic and `0 < cgamma <= 1/4`.  No smallness gate beyond that
quarter bound, nothing about the mesh, the corrector or the sample space.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport MeasureTheory

noncomputable section

/-! ## The tight integer inequality -/

/-- **`(1+i)^4 4^i <= 25 . 9^i`.**  The induction step `4 (i+2)^4 <= 9 (i+1)^4`
holds only from `i = 4` on, so the four smaller cases are checked directly.
Unconditional. -/
theorem succ_pow_four_mul_four_pow_le (i : ℕ) :
    (1 + i) ^ 4 * 4 ^ i ≤ 25 * 9 ^ i := by
  rcases lt_or_ge i 4 with hlt | hge
  · interval_cases i <;> norm_num
  · induction i, hge using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
        have hstep : 4 * (k + 2) ^ 4 ≤ 9 * (k + 1) ^ 4 := by
          obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = 4 + m := ⟨k - 4, by omega⟩
          nlinarith [Nat.zero_le m, Nat.zero_le (m * m), Nat.zero_le (m * m * m),
            Nat.zero_le (m * m * m * m)]
        calc (1 + (k + 1)) ^ 4 * 4 ^ (k + 1)
            = (4 * (k + 2) ^ 4) * 4 ^ k := by ring
          _ ≤ (9 * (k + 1) ^ 4) * 4 ^ k := Nat.mul_le_mul_right _ hstep
          _ = 9 * ((1 + k) ^ 4 * 4 ^ k) := by ring
          _ ≤ 9 * (25 * 9 ^ k) := Nat.mul_le_mul_left _ ih
          _ = 25 * 9 ^ (k + 1) := by ring

/-- **The depth endpoints' decay factor at the fourth power.**  The linear factor
`(1 + i)` costs the absolute constant `25` and nothing else: the ratio stays at
the fold's own gate `1/36`.  Unconditional. -/
theorem depth_decay_pow_four_le (i : ℕ) :
    ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) ^ (4 : ℕ) ≤
      25 * ((1 : ℝ) / 36) ^ i := by
  have hnat : ((1 + i) ^ 4 * 4 ^ i : ℕ) ≤ ((25 * 9 ^ i : ℕ)) :=
    succ_pow_four_mul_four_pow_le i
  have hreal : ((1 : ℝ) + (i : ℝ)) ^ (4 : ℕ) * (4 : ℝ) ^ i ≤ 25 * (9 : ℝ) ^ i := by
    have hcast := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at hcast
    linarith
  have hrpow : (3 : ℝ) ^ (-(i : ℝ)) = (((3 : ℝ) ^ i)⁻¹) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  have h81 : ((3 : ℝ) ^ i) ^ (4 : ℕ) = (81 : ℝ) ^ i := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have h36 : (0 : ℝ) < (36 : ℝ) ^ i := by positivity
  have h81pos : (0 : ℝ) < (81 : ℝ) ^ i := by positivity
  have hfactor : (4 : ℝ) ^ i * (9 : ℝ) ^ i = (36 : ℝ) ^ i := by
    rw [← mul_pow]; norm_num
  have hsquare : (9 : ℝ) ^ i * (9 : ℝ) ^ i = (81 : ℝ) ^ i := by
    rw [← mul_pow]; norm_num
  have hcross : ((1 : ℝ) + (i : ℝ)) ^ (4 : ℕ) * (36 : ℝ) ^ i ≤ 25 * (81 : ℝ) ^ i := by
    have h9 : (0 : ℝ) ≤ (9 : ℝ) ^ i := by positivity
    have hmul := mul_le_mul_of_nonneg_right hreal h9
    calc ((1 : ℝ) + (i : ℝ)) ^ (4 : ℕ) * (36 : ℝ) ^ i
        = ((1 : ℝ) + (i : ℝ)) ^ (4 : ℕ) * (4 : ℝ) ^ i * (9 : ℝ) ^ i := by
          rw [← hfactor]; ring
      _ ≤ 25 * (9 : ℝ) ^ i * (9 : ℝ) ^ i := hmul
      _ = 25 * (81 : ℝ) ^ i := by rw [← hsquare]; ring
  rw [hrpow, mul_pow, inv_pow, h81]
  have hlhs : ((1 : ℝ) + (i : ℝ)) ^ (4 : ℕ) * ((81 : ℝ) ^ i)⁻¹ =
      ((1 : ℝ) + (i : ℝ)) ^ (4 : ℕ) / (81 : ℝ) ^ i := by
    rw [div_eq_mul_inv]
  have hrhs : (25 : ℝ) * ((1 : ℝ) / 36) ^ i = 25 / (36 : ℝ) ^ i := by
    rw [div_pow, one_pow]
    ring
  rw [hlhs, hrhs]
  exact (div_le_div_iff₀ h81pos h36).mpr hcross

/-! ## The fourth moment from its root -/

/-- The grid fourth moment from its fourth root.  Unconditional. -/
theorem gridFourthMoment_le_pow_four_of_root_le {d : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) (I : Finset (TriadicCube d))
    (F : TriadicCube d → Omega → ℝ) {c : ℝ}
    (h : gridFourthMomentRoot mu I F ≤ c) :
    gridFourthMoment mu I F ≤ c ^ (4 : ℕ) := by
  have h0 : (0 : ℝ) ≤ gridFourthMoment mu I F := gridFourthMoment_nonneg mu I F
  have hroot : gridFourthMoment mu I F ^ ((4 : ℝ)⁻¹) ≤ c := h
  have hpow : (gridFourthMoment mu I F ^ ((4 : ℝ)⁻¹)) ^ ((4 : ℝ)) ≤ c ^ ((4 : ℝ)) :=
    Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hroot (by norm_num)
  rw [← Real.rpow_mul h0, show ((4 : ℝ)⁻¹ * (4 : ℝ)) = 1 by norm_num,
    Real.rpow_one] at hpow
  rw [rpow_four_eq_pow_four] at hpow
  exact hpow

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
