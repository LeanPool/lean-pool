/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import Mathlib.Data.Nat.Notation

/-!
# Newman's theorem: the local valuation lemma

At a prime p write ν = v_p(N), j = v_p(gcd(N, 24)), k = v_p(h), e₂ = v_p(2), and let a, b, c, d be
the
valuations of the entries of a primitive integer matrix B (a large value standing for a zero entry)
with δ₀ = v_p(det B).  The conditions C1–C18 say that B normalizes D L D⁻¹ (they come from
conjugating E₁₂, NE₂₁, εE₂₂ by B and by B⁻¹).  Then B has the local shape of (8′):
either det B is a p-unit and p^{ν−2k} divides the lower-left entry, or v_p(det B) = ν − 2k and
p^{ν−2k} divides the two diagonal entries and the lower-left entry.

This replaces the lattice/tree argument of [Nw §§4–7]; it is proved by `omega`.  (An independent
brute-force check of the same implication, used only to choose this route: `scripts/valcheck.py`.)
-/

@[expose] public section

namespace CongruenceNormalizers

theorem local_form (p ν j k e₂ δ₀ a b c d : ℕ)
    (_hp : (p = 2 ∧ j = min ν 3 ∧ e₂ = 1) ∨ (p = 3 ∧ j = min ν 1 ∧ e₂ = 0) ∨ (j = 0 ∧ e₂ = 0))
    (hk : k = min j (ν / 2))
    (prim : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0)
    (u1 : min (a + d) (b + c) ≤ δ₀) (u2 : a + d ≠ b + c → δ₀ = min (a + d) (b + c))
    (_C1 : δ₀ ≤ k + a + c) (C2 : δ₀ ≤ 2 * a) (C3 : δ₀ + ν ≤ 2 * k + 2 * c)
    (_C4 : j + δ₀ ≤ e₂ + k + a + c) (_C5 : δ₀ + k ≤ ν + b + d) (C6 : δ₀ + 2 * k ≤ ν + 2 * b)
    (C7 : δ₀ ≤ 2 * d) (_C8 : j + δ₀ + k ≤ e₂ + ν + b + d) (_C9 : δ₀ ≤ j + b + c)
    (C10 : δ₀ + k ≤ j + a + b) (C11 : δ₀ + ν ≤ j + k + c + d) (_C12 : δ₀ ≤ e₂ + b + c)
    (_C13 : δ₀ ≤ k + c + d) (_C14 : j + δ₀ ≤ e₂ + k + c + d) (_C15 : δ₀ + k ≤ ν + a + b)
    (_C16 : j + δ₀ + k ≤ e₂ + ν + a + b) (C17 : δ₀ + k ≤ j + b + d)
    (C18 : δ₀ + ν ≤ j + k + a + c) :
    (δ₀ = 0 ∧ ν - 2 * k ≤ c) ∨
      (δ₀ = ν - 2 * k ∧ ν - 2 * k ≤ a ∧ ν - 2 * k ≤ c ∧ ν - 2 * k ≤ d) := by
  omega

end CongruenceNormalizers
