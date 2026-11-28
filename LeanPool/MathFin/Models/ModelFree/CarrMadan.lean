/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Carr–Madan static replication (spanning formula)

Any twice-differentiable European payoff `f` decomposes, around a reference level
`κ`, as cash + a forward + a static portfolio of out-of-the-money options:

  `f S = f κ + f' κ · (S − κ) + ∫_L^κ f''(K)·(K − S)⁺ dK + ∫_κ^U f''(K)·(S − K)⁺ dK`,

the **Carr–Madan spanning formula** (`carrMadan_spanning`). The puts (strikes `K < κ`)
and calls (strikes `K > κ`) are weighted by the payoff convexity `f''`. We prove the
honest **compact strike-range** version on `[L, U]` (no improper integrals); the textbook
unbounded form is the `L = 0`, `U → ∞` limit, which needs separate integrability-at-`∞`
hypotheses.

The proof is one integration by parts — the second-order Taylor remainder
`∫_κ^S (S − t) f''(t) dt = f S − f κ − f' κ (S − κ)`
(`secondOrder_remainder_eq_integral`) — followed by a case split on `S` vs `κ`: in each
case one option leg vanishes (its positive part is `0` over its strike range) and the other
reproduces the remainder.

## Main results

* `carrMadan_spanning`: for `f` twice differentiable on `[L, U]` with `f''` continuous there, and
  `L ≤ κ ≤ U`, `S ∈ [L, U]`,
  `f S = f κ + f' κ · (S − κ) + ∫_L^κ f''(K)·(K − S)⁺ dK + ∫_κ^U f''(K)·(S − K)⁺ dK`.
  This is the compact strike-range form; no improper integral appears.
* `carrMadan_log_spanning`: the case `f = log` with `0 < L`, where the option weights are
  `−1/K²`.

## References

* [Carr and Madan (2001)][CarrMadan2001]
* [Demeterfi et al., *More than you ever wanted to know about volatility
  swaps*][DemeterfiDermanKamalZou1999]

## Tags

static replication, spanning formula, Carr–Madan formula, variance swap replication,
Taylor remainder, strip of options, JEL G13, MSC 91G20
-/

@[expose] public section

namespace MathFin

/-- **Second-order Taylor remainder as an integral against `f''`.** For `f` twice
differentiable on `[[κ, S]]` with continuous `f''`,
`∫_κ^S (S − t) · f''(t) dt = f S − f κ − f' κ · (S − κ)`. One integration by parts
(`u = S − ·`, `v = f'`) plus the fundamental theorem of calculus.

This is the `n = 1` case of Mathlib's `taylor_integral_remainder` (stated there via
`ContDiffOn` + `iteratedDerivWithin`); we keep this explicit-`HasDerivAt` form because the
spanning proof consumes `f'`, `f''` as named functions and the `iteratedDerivWithin` bridge
would be longer than the IBP proof itself. -/
theorem secondOrder_remainder_eq_integral {f f' f'' : ℝ → ℝ} {κ S : ℝ}
    (hf : ∀ t ∈ Set.uIcc κ S, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.uIcc κ S, HasDerivAt f' (f'' t) t)
    (hf'' : ContinuousOn f'' (Set.uIcc κ S)) :
    ∫ t in κ..S, (S - t) * f'' t = f S - f κ - f' κ * (S - κ) := by
  have hu : ∀ t ∈ Set.uIcc κ S, HasDerivAt (fun s ↦ S - s) (-1 : ℝ) t :=
    fun t _ ↦ by simpa using (hasDerivAt_id t).const_sub S
  have hf'_cont : ContinuousOn f' (Set.uIcc κ S) :=
    fun t ht ↦ (hf' t ht).continuousAt.continuousWithinAt
  have hf'_int : IntervalIntegrable f' MeasureTheory.volume κ S := hf'_cont.intervalIntegrable
  have hf''_int : IntervalIntegrable f'' MeasureTheory.volume κ S := hf''.intervalIntegrable
  have hconst_int : IntervalIntegrable (fun _ ↦ (-1 : ℝ)) MeasureTheory.volume κ S :=
    intervalIntegrable_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hf' hconst_int hf''_int
  have hftc : ∫ t in κ..S, f' t = f S - f κ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hf hf'_int
  calc ∫ t in κ..S, (S - t) * f'' t
      = (S - S) * f' S - (S - κ) * f' κ - ∫ t in κ..S, (-1 : ℝ) * f' t := hibp
    _ = (S - S) * f' S - (S - κ) * f' κ + ∫ t in κ..S, f' t := by
          rw [intervalIntegral.integral_const_mul]; ring
    _ = f S - f κ - f' κ * (S - κ) := by rw [hftc]; ring

/-- **Carr–Madan static replication / spanning formula (compact strike range).** For a
twice-differentiable payoff `f` on `[L, U]` (pointwise derivatives `f'`, `f''`, with `f''`
continuous) and reference level `κ ∈ [L, U]`, every spot `S ∈ [L, U]` satisfies

  `f S = f κ + f' κ · (S − κ) + ∫_L^κ f''(K)·(K − S)⁺ dK + ∫_κ^U f''(K)·(S − K)⁺ dK`,

i.e. the payoff is cash `f κ`, a forward position `f' κ` in `(S − κ)`, plus a static book of
puts (strikes `K ∈ [L, κ]`) and calls (strikes `K ∈ [κ, U]`) held in density `f''(K) dK`.
This is the honest compact-strike-range Carr–Madan formula; the textbook unbounded form is
the `L = 0`, `U → ∞` limit, needing separate integrability-at-`∞` hypotheses. -/
theorem carrMadan_spanning {f f' f'' : ℝ → ℝ} {L U κ S : ℝ}
    (hLκ : L ≤ κ) (hκU : κ ≤ U) (hS : S ∈ Set.Icc L U)
    (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc L U, HasDerivAt f' (f'' t) t)
    (hf'' : ContinuousOn f'' (Set.Icc L U)) :
    f S = f κ + f' κ * (S - κ)
      + (∫ K in L..κ, f'' K * max (K - S) 0)
      + (∫ K in κ..U, f'' K * max (S - K) 0) := by
  have hκ : κ ∈ Set.Icc L U := ⟨hLκ, hκU⟩
  have hL : L ∈ Set.Icc L U := ⟨le_rfl, hLκ.trans hκU⟩
  have hU : U ∈ Set.Icc L U := ⟨hLκ.trans hκU, le_rfl⟩
  have hsub : Set.uIcc κ S ⊆ Set.Icc L U := Set.uIcc_subset_Icc hκ hS
  have hcore : ∫ t in κ..S, (S - t) * f'' t = f S - f κ - f' κ * (S - κ) :=
    secondOrder_remainder_eq_integral (fun t ht ↦ hf t (hsub ht))
      (fun t ht ↦ hf' t (hsub ht)) (hf''.mono hsub)
  have hcont_put : ContinuousOn (fun K ↦ f'' K * max (K - S) 0) (Set.Icc L U) :=
    hf''.mul (((continuous_id.sub continuous_const).max continuous_const).continuousOn)
  have hcont_call : ContinuousOn (fun K ↦ f'' K * max (S - K) 0) (Set.Icc L U) :=
    hf''.mul (((continuous_const.sub continuous_id).max continuous_const).continuousOn)
  rcases le_total κ S with h | h
  · -- `κ ≤ S`: the put leg vanishes; the call leg is the remainder.
    have hput0 : (∫ K in L..κ, f'' K * max (K - S) 0) = 0 := by
      have h0 : Set.EqOn (fun K ↦ f'' K * max (K - S) 0) (fun _ ↦ (0 : ℝ)) (Set.uIcc L κ) := by
        intro K hK
        rw [Set.uIcc_of_le hLκ] at hK
        simp only [max_eq_right (show K - S ≤ 0 by linarith [hK.2]), mul_zero]
      rw [intervalIntegral.integral_congr h0]; simp
    have hcall : (∫ K in κ..U, f'' K * max (S - K) 0) = f S - f κ - f' κ * (S - κ) := by
      have hsplit : (∫ K in κ..U, f'' K * max (S - K) 0)
          = (∫ K in κ..S, f'' K * max (S - K) 0) + (∫ K in S..U, f'' K * max (S - K) 0) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont_call.mono (Set.uIcc_subset_Icc hκ hS)).intervalIntegrable
          (hcont_call.mono (Set.uIcc_subset_Icc hS hU)).intervalIntegrable).symm
      have hupper : (∫ K in S..U, f'' K * max (S - K) 0) = 0 := by
        have h0 : Set.EqOn (fun K ↦ f'' K * max (S - K) 0) (fun _ ↦ (0 : ℝ)) (Set.uIcc S U) := by
          intro K hK
          rw [Set.uIcc_of_le hS.2] at hK
          simp only [max_eq_right (show S - K ≤ 0 by linarith [hK.1]), mul_zero]
        rw [intervalIntegral.integral_congr h0]; simp
      have hlower : (∫ K in κ..S, f'' K * max (S - K) 0) = ∫ K in κ..S, (S - K) * f'' K := by
        refine intervalIntegral.integral_congr fun K hK ↦ ?_
        rw [Set.uIcc_of_le h] at hK
        rw [max_eq_left (show (0 : ℝ) ≤ S - K by linarith [hK.2])]; ring
      rw [hsplit, hupper, hlower, add_zero, hcore]
    rw [hput0, hcall]; ring
  · -- `S ≤ κ`: the call leg vanishes; the put leg is the remainder.
    have hcall0 : (∫ K in κ..U, f'' K * max (S - K) 0) = 0 := by
      have h0 : Set.EqOn (fun K ↦ f'' K * max (S - K) 0) (fun _ ↦ (0 : ℝ)) (Set.uIcc κ U) := by
        intro K hK
        rw [Set.uIcc_of_le hκU] at hK
        simp only [max_eq_right (show S - K ≤ 0 by linarith [hK.1]), mul_zero]
      rw [intervalIntegral.integral_congr h0]; simp
    have hput : (∫ K in L..κ, f'' K * max (K - S) 0) = f S - f κ - f' κ * (S - κ) := by
      have hsplit : (∫ K in L..κ, f'' K * max (K - S) 0)
          = (∫ K in L..S, f'' K * max (K - S) 0) + (∫ K in S..κ, f'' K * max (K - S) 0) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont_put.mono (Set.uIcc_subset_Icc hL hS)).intervalIntegrable
          (hcont_put.mono (Set.uIcc_subset_Icc hS hκ)).intervalIntegrable).symm
      have hlowZero : (∫ K in L..S, f'' K * max (K - S) 0) = 0 := by
        have h0 : Set.EqOn (fun K ↦ f'' K * max (K - S) 0) (fun _ ↦ (0 : ℝ)) (Set.uIcc L S) := by
          intro K hK
          rw [Set.uIcc_of_le hS.1] at hK
          simp only [max_eq_right (show K - S ≤ 0 by linarith [hK.2]), mul_zero]
        rw [intervalIntegral.integral_congr h0]; simp
      have hhigh : (∫ K in S..κ, f'' K * max (K - S) 0) = ∫ K in S..κ, (K - S) * f'' K := by
        refine intervalIntegral.integral_congr fun K hK ↦ ?_
        rw [Set.uIcc_of_le h] at hK
        rw [max_eq_left (show (0 : ℝ) ≤ K - S by linarith [hK.1])]; ring
      rw [hsplit, hlowZero, hhigh, zero_add, ← hcore,
          intervalIntegral.integral_symm S κ, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun K _ ↦ ?_
      ring
    rw [hcall0, hput]; ring

/-- **Carr–Madan log-contract replication** — the variance-swap building block. On a positive
strike range `0 < L ≤ κ ≤ U`, the log payoff replicates as a forward position `κ⁻¹·(S − κ)` in
the underlying plus a static strip of out-of-the-money options weighted by `1/K²`:

  `log S = log κ + κ⁻¹·(S − κ) + ∫_L^κ −(K²)⁻¹·(K − S)⁺ dK + ∫_κ^U −(K²)⁻¹·(S − K)⁺ dK`.

The `−1/K²` weight (the log payoff's convexity `f''`) is exactly the density of OTM puts and
calls a variance swap holds. Specialises `carrMadan_spanning` to `f = Real.log`. -/
theorem carrMadan_log_spanning {L U κ S : ℝ} (hL : 0 < L)
    (hLκ : L ≤ κ) (hκU : κ ≤ U) (hS : S ∈ Set.Icc L U) :
    Real.log S = Real.log κ + κ⁻¹ * (S - κ)
      + (∫ K in L..κ, -(K ^ 2)⁻¹ * max (K - S) 0)
      + (∫ K in κ..U, -(K ^ 2)⁻¹ * max (S - K) 0) := by
  have hpos : ∀ t ∈ Set.Icc L U, t ≠ 0 := fun t ht ↦ (lt_of_lt_of_le hL ht.1).ne'
  exact carrMadan_spanning (f := Real.log) (f' := fun t ↦ t⁻¹) (f'' := fun K ↦ -(K ^ 2)⁻¹)
    hLκ hκU hS (fun t ht ↦ Real.hasDerivAt_log (hpos t ht))
    (fun t ht ↦ by simpa using hasDerivAt_inv (hpos t ht))
    (((continuousOn_id.pow 2).inv₀ (fun K hK ↦ pow_ne_zero 2 (hpos K hK))).neg)

end MathFin
