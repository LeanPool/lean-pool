/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Construction
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

/-! # The normalisation `m_{K,M}` of Section 5

We define the local exponents `L_p(K, M)` of (5.1) exactly as in the paper (with the counts
`ℓ_A(a)`, the allocation `T, E, ε_a, L_a`, the weights (4.6)–(4.7), the inner exponent
`γ_p^in` (4.8), the outer exponent `γ_p^out` (4.14)) of Section 5.
We do not export the paper's separate normalising factor: the
proved integrality and growth estimates concern `Zeta5Irrational.mN`.

These are the paper's definitions, kept for reference and for `vS` (used by
`Zeta5Irrational.Legendre`).
The normalisation actually used in the proof is `Zeta5Irrational.mN`
(`Zeta5Irrational/Norm.lean`), whose local
exponents are the bounds proved in `Zeta5Irrational/Arith`.
-/

@[expose] public section

open Finset Polynomial

namespace Zeta5Irrational

/-- `ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ ±a (mod p)}`. -/
def ellA (p A a : ℕ) : ℕ :=
  ((Icc 1 A).filter fun j => j % p = a % p ∨ (j + a) % p = 0).card

/-- The parameters of Section 4.1 for `K = 40 n`, `N = 3 n`, `h = 37 n`, cutoff `M`, prime `p`. -/
structure InnerData where
  /-- Scale parameter determining `K = 40n`, `N = 3n`, and `h = 37n`. -/
  n : ℕ
  /-- Cutoff separating the small-prime and intermediate-prime ranges. -/
  M : ℕ
  /-- Prime parameter; primality is imposed by results using these data. -/
  p : ℕ

namespace InnerData

variable (D : InnerData)

/-- Pole cutoff `K = 40n`. -/
def K : ℕ :=
  40 * D.n

/-- Auxiliary zero cutoff `N = 3n`. -/
def N : ℕ :=
  3 * D.n

/-- Size `h = 37n` of the Hankel determinant. -/
def h : ℕ :=
  37 * D.n

/-- Reserved row count `4M + 10` for the zero residue class. -/
def L0 : ℕ :=
  4 * D.M + 10

/-- `m = (p - 1)/2`. -/
def m : ℕ :=
  (D.p - 1) / 2

/-- Integer quotient of the zero cutoff `N` by `p`. -/
def mN : ℕ :=
  D.N / D.p

/-- Integer quotient of the pole cutoff `K` by `p`. -/
def mK : ℕ :=
  D.K / D.p

/-- Number of pole indices up to `K` congruent to `a` or `-a` modulo `p`. -/
def ellK (a : ℕ) : ℕ :=
  ellA D.p D.K a

/-- Number of zero indices up to `N` congruent to `a` or `-a` modulo `p`. -/
def ellN (a : ℕ) : ℕ :=
  ellA D.p D.N a

/-- `b_a = 3 ℓ_N(a)`. -/
def b (a : ℕ) : ℕ :=
  3 * D.ellN a

/-- The total number of ordinary rows `h - L₀ + 3(N - m_N)` (as an integer). -/
def total : ℤ :=
  (D.h : ℤ) - D.L0 + 3 * ((D.N : ℤ) - D.mN)

/-- `T` of (4.4). -/
def T : ℤ :=
  D.total / D.m

/-- `E` of (4.4). -/
def E : ℤ :=
  D.total % D.m

/-- The rank of the class `a` in decreasing order of `ℓ_K` (ties broken by the index). -/
def rank (a : ℕ) : ℕ :=
  ((Icc 1 D.m).filter fun c => D.ellK c > D.ellK a ∨ (D.ellK c = D.ellK a ∧ c < a)).card

/-- `ε_a = 1` for the first `E` classes in decreasing order of `ℓ_K(a)`. -/
def eps (a : ℕ) : ℤ :=
  if (D.rank a : ℤ) < D.E then 1 else 0

/-- `L_a = T - b_a + ε_a`. -/
def L (a : ℕ) : ℤ :=
  D.T - D.b a + D.eps a

/-- `Z_a = T + ε_a`. -/
def Z (a : ℕ) : ℤ :=
  D.T + D.eps a

/-- The row weights (4.6) for `a > 0` (as rationals, they are half-integers). -/
def w (a : ℕ) (i : ℤ) : ℚ :=
  i + D.b a - ((D.ellK a : ℚ) + 4) / 2

/-- The minimum over the ordinary classes in (4.7). -/
def w0min : ℚ :=
  if hm : 1 ≤ D.m then
    ((Icc 1 D.m).image fun c => (D.Z c : ℚ) - ((D.ellK c : ℚ) + 4) / 2).min' (by simpa using hm)
  else 0

/-- The zero-block weights (4.7). -/
def w0 (i : ℤ) : ℚ :=
  min (2 * i + 6 * (D.mN : ℚ) - D.mK + 1 / 2) D.w0min

/-- The inner exponent `γ_p^in` of (4.8) (an integer; we take the floor of the rational sum). -/
def gammaIn : ℤ :=
  ⌊2 * ((∑ i ∈ range D.L0, D.w0 i) + ∑ a ∈ Icc 1 D.m, ∑ i ∈ range (D.L a).toNat, D.w a i)⌋

/-! ### The outer range (4.14) -/

/-- `v = K - p ⌊K/p⌋`. -/
def v : ℕ :=
  D.K % D.p

/-- Nonnegative overlap term `max 0 (N + v - p + 1)` in the outer-range bound. -/
def u : ℤ :=
  max 0 ((D.N : ℤ) + D.v - D.p + 1)

/-- Auxiliary outer-range count `min N v + u`. -/
def tp : ℤ :=
  min (D.N : ℤ) D.v + D.u

/-- Outer-range rank-loss bound `max 0 (K + 4N - 2p + 2)`. -/
def rp : ℤ :=
  max 0 ((D.K : ℤ) + 4 * D.N - 2 * D.p + 2)

/-- The outer exponent `γ_p^out` of (4.14) (`0` for `p > K`). -/
def gammaOut : ℤ :=
  if D.K < D.p then 0
  else
    if D.K < 2 * D.p then
      -7 * ((D.K : ℤ) - D.p) + 6 * D.tp - 1 - min D.rp ((D.p : ℤ) - 1 - D.N + D.u)
    else -7 * ((D.K : ℤ) - D.p) + 3 + 12 * D.N + 5 * D.tp - min D.rp ((D.p : ℤ) + D.u)

/-- `v_p(S_K)`. -/
noncomputable def vS : ℤ :=
  padicValRat D.p (S D.n)

/-- The local exponent `L_p(K, M)` of (5.1). -/
noncomputable def Lp : ℤ :=
  if D.p * D.M ≤ D.K then -6 * (D.h : ℤ) * Nat.log D.p (5 * D.K) - D.h * padicValNat D.p 24
  else if 3 * D.p ≤ D.K then D.vS + D.gammaIn else D.vS + D.gammaOut

end InnerData

end Zeta5Irrational
