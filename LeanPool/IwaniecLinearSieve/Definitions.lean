/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Chebyshev

/-!
# The definitions in the advertised statements

Shared definitions of sifted sets, sieve functions and delay-equation majorants.
Their analytic and combinatorial properties are proved in the modules below.
-/

@[expose] public section

open Real Finset

namespace IwaniecLinearSieve

/-! ## Sifted sets ([I71, §1]) -/

/-- The primes `p < z`. -/
noncomputable def primesLT (z : ℝ) : Finset ℕ := Nat.primesBelow ⌈z⌉₊

/-- The primes `p < z` with `p ∤ k`. -/
noncomputable def primesLTk (k : ℕ) (z : ℝ) : Finset ℕ := (primesLT z).filter fun p ↦ ¬ p ∣ k

/-- Iwaniec's `R_k(z) = ∏_{p < z, p ∤ k} (1 - 1/p)`. -/
noncomputable def Rk (k : ℕ) (z : ℝ) : ℝ := ∏ p ∈ primesLTk k z, (1 - (p : ℝ)⁻¹)

/-- Iwaniec's `A_k(M; z)`: the number of terms of `M` not divisible by any prime `p < z`
with `p ∤ k`. -/
noncomputable def siftedCount (k : ℕ) (M : Multiset ℤ) (z : ℝ) : ℕ :=
  M.countP fun a ↦ ∀ p ∈ primesLTk k z, ¬ (p : ℤ) ∣ a

/-- Iwaniec's `|M_d|`: the number of terms of `M` divisible by `d`. -/
def multiplesCount (M : Multiset ℤ) (d : ℕ) : ℕ := M.countP fun a ↦ (d : ℤ) ∣ a

/-! ## The sieve functions `f` and `F` ([I71, §3, (3.1)–(3.7)]) -/

/-- The formula `3 log (3 / (s - 1)) + s - 4` for `g₂` on `[2, 4]`. -/
noncomputable def gTwoFormula (s : ℝ) : ℝ := 3 * log (3 / (s - 1)) + s - 4

/-- Left end of the domain of `g i` in [I71]: `2` for even `i`, `3` for odd `i`. -/
noncomputable def gLower (i : ℕ) : ℝ := if Even i then 2 else 3

/-- The kernel `t ↦ h (t - 1) / (t - 1)`, with the denominator replaced by `max (t - 1) 1` so that
it is continuous on `ℝ` whenever `h` is. It agrees with `h (t - 1) / (t - 1)` for `t ≥ 2`. -/
noncomputable def shiftKernel (h : ℝ → ℝ) (t : ℝ) : ℝ := h (t - 1) / max (t - 1) 1

/-- Iwaniec's functions `g_n` of [I71, (3.1)–(3.3)], extended to all of `ℝ`:
`g₂(s) = 3 log (3 / (s - 1)) + s - 4` on `[2, 4]` and `0` for `s ≥ 4`, and
`g_{n+1}(s) = ∫_s^∞ g_n(t - 1) / (t - 1) dt` for `s` at least `gLower (n + 1)`.
Outside the domains of [I71] the argument is clamped: the even functions are constant on
`s ≤ 2`, the odd ones on `s ≤ 3`, and `g 0 = g 1 = 0`. The upper limit `n + 5 = (n + 3) + 2`
of the integral can replace `∞` because `g (n + 2) s = 0` for `s ≥ n + 4`. -/
noncomputable def g : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | 2, s => gTwoFormula (max 2 (min s 4))
  | n + 3, s => ∫ t in max s (gLower (n + 3))..((n : ℝ) + 5), shiftKernel (g (n + 2)) t

/-- Iwaniec's `f(s) = Σ_{i ≥ 1} g_{2i}(s)` [I71, (3.6)]; constant (`= f(2) = 2`) for `s ≤ 2`. -/
noncomputable def fSieve (s : ℝ) : ℝ := ∑' n : ℕ, g (2 * n + 2) s

/-- Iwaniec's `F(s) = Σ_{i ≥ 1} g_{2i+1}(s)` [I71, (3.7)]; constant (`= F(3)`) for `s ≤ 3`. -/
noncomputable def FSieve (s : ℝ) : ℝ := ∑' n : ℕ, g (2 * n + 3) s

/-! ## The function `𝔐` ([I71, §3, Definition]) -/

namespace Delay

/-- One Picard-type step: `y₀` up to `3`, then integrate `k x * y (x - 1)` from `3`. -/
noncomputable def step (k y₀ y : ℝ → ℝ) (s : ℝ) : ℝ :=
  y₀ (min s 3) + ∫ x in (3 : ℝ)..max s 3, k x * y (x - 1)

/-- The iterates of `step`; the `n`-th one is correct on `(-∞, n + 3]`. -/
noncomputable def iter (k y₀ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => y₀
  | n + 1 => step k y₀ (iter k y₀ n)

/-- The solution `y` of the delay equation `y s = y₀ s` for `s ≤ 3` and
`y s = y₀ 3 + ∫ x in 3..s, k x * y (x - 1)` for `s ≥ 3`. -/
noncomputable def sol (k y₀ : ℝ → ℝ) (s : ℝ) : ℝ := iter k y₀ ⌈s⌉₊ s

end Delay

/-- The kernel `x / (x - 1)²` of the delay equations, frozen to the left of `3`. -/
noncomputable def delayKer (x : ℝ) : ℝ := max x 3 / (max x 3 - 1) ^ 2

/-- Initial values of `𝔚` on `[2, 3]` (constant to the left of `2`). -/
noncomputable def initW (s : ℝ) : ℝ := 1 / (max s 2 - 1) - log (max s 2 - 1)

/-- Iwaniec's `𝔐` [I71, §3, Definition]: `𝔐(s) = 2 + 1/(s - 1) - log (s - 1)` on `[2, 3]`
(constant `3` to the left of `2`) and `𝔐'(s) = -s/(s - 1)² 𝔐(s - 1)` for `s > 3`. -/
noncomputable def bigM : ℝ → ℝ := Delay.sol (fun x => -delayKer x) (fun s => 2 + initW s)

end IwaniecLinearSieve
