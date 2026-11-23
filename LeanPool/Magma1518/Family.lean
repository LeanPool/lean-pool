/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.Magma1518.Laws

/-!
# Finite 1518-magmas violating laws 47, 614, 817 and 3862

Theorem F of the accompanying note describes extensions of the Z/3 shift: on `Z/3 × M` put
`(x, s) ◇ (y, t) = (y + 1, a[x][y] · s + b[x][y] · t)` for two `3 × 3` coefficient matrices `a`, `b`
over a ring with `1/2` and a square root `i` of `-1`. This file checks two members by kernel
evaluation, with `M = 𝔽₅` (`i = 2`, 15 elements) and `M = 𝔽₁₃` (`i = 5`, 39 elements): law 1518
holds, the four targets 47, 614, 817 and 3862 fail, and squaring `S` satisfies `S³ ≠ id` and
`S¹² = id`. The general statement over a ring is not formalized here.

The pair `(x, s)` with `x < 3`, `s < p` is encoded as the number `p * x + s`.
-/

@[expose] public section

namespace Magma1518

/-- The operation of Theorem F on `Z/3 × 𝔽_p`, on codes `p * x + s`, for coefficient matrices
`a`, `b` given as functions of the row and column. -/
def extensionCode (p : Nat) (a b : Nat → Nat → Nat) (u v : Nat) : Nat :=
  p * ((v / p + 1) % 3) + (a (u / p) (v / p) * (u % p) + b (u / p) (v / p) * (v % p)) % p

/-- Entry `(x, y)` of a `3 × 3` matrix given by its rows. -/
def entry (rows : List (List Nat)) (x y : Nat) : Nat :=
  (rows.getD x []).getD y 0

namespace F5

/-- The matrix `a` of the member over `𝔽₅`. -/
def a : Nat → Nat → Nat := entry [[1, 2, 2], [2, 1, 3], [3, 2, 4]]

/-- The matrix `b` of the member over `𝔽₅`. -/
def b : Nat → Nat → Nat := entry [[1, 4, 2], [3, 1, 1], [4, 3, 4]]

/-- The 15-element magma: Theorem F over `𝔽₅`. The final reduction modulo 15 only gives the value
its type; `extensionCode` is already below 15. -/
def op (u v : Fin 15) : Fin 15 :=
  ⟨extensionCode 5 a b u.val v.val % 15, Nat.mod_lt _ (by decide)⟩

/-- Squaring, `S x = x ◇ x`. -/
def sq (x : Fin 15) : Fin 15 := op x x

theorem law1518 : Law1518 op := by
  unfold Law1518
  decide +kernel

theorem not47 : ¬ Law47 op := by
  unfold Law47
  decide +kernel

theorem not614 : ¬ Law614 op := by
  unfold Law614
  decide +kernel

theorem not817 : ¬ Law817 op := by
  unfold Law817
  decide +kernel

theorem not3862 : ¬ Law3862 op := by
  unfold Law3862
  decide +kernel

theorem sq_cubed_ne_id : ¬ ∀ x, sq (sq (sq x)) = x := by
  decide +kernel

theorem sq_pow_twelve : ∀ x, sq (sq (sq (sq (sq (sq (sq (sq (sq (sq (sq (sq x))))))))))) = x := by
  decide +kernel

end F5

namespace F13

/-- The matrix `a` of the member over `𝔽₁₃`. -/
def a : Nat → Nat → Nat := entry [[10, 6, 11], [11, 10, 6], [6, 11, 10]]

/-- The matrix `b` of the member over `𝔽₁₃`. -/
def b : Nat → Nat → Nat := entry [[1, 3, 7], [7, 1, 3], [3, 7, 1]]

/-- The 39-element magma: Theorem F over `𝔽₁₃`. The final reduction modulo 39 only gives the value
its type; `extensionCode` is already below 39. -/
def op (u v : Fin 39) : Fin 39 :=
  ⟨extensionCode 13 a b u.val v.val % 39, Nat.mod_lt _ (by decide)⟩

/-- Squaring, `S x = x ◇ x`. -/
def sq (x : Fin 39) : Fin 39 := op x x

theorem law1518 : Law1518 op := by
  unfold Law1518
  decide +kernel

theorem not47 : ¬ Law47 op := by
  unfold Law47
  decide +kernel

theorem not614 : ¬ Law614 op := by
  unfold Law614
  decide +kernel

theorem not817 : ¬ Law817 op := by
  unfold Law817
  decide +kernel

theorem not3862 : ¬ Law3862 op := by
  unfold Law3862
  decide +kernel

theorem sq_cubed_ne_id : ¬ ∀ x, sq (sq (sq x)) = x := by
  decide +kernel

theorem sq_pow_twelve : ∀ x, sq (sq (sq (sq (sq (sq (sq (sq (sq (sq (sq (sq x))))))))))) = x := by
  decide +kernel

end F13

/-- Theorem F, checked members: over `𝔽₅` and over `𝔽₁₃` the extension satisfies law 1518 and
violates each of laws 47, 614, 817 and 3862. -/
theorem family_members :
    (Law1518 F5.op ∧ ¬ Law47 F5.op ∧ ¬ Law614 F5.op ∧ ¬ Law817 F5.op ∧ ¬ Law3862 F5.op) ∧
    (Law1518 F13.op ∧ ¬ Law47 F13.op ∧ ¬ Law614 F13.op ∧ ¬ Law817 F13.op ∧
      ¬ Law3862 F13.op) :=
  ⟨⟨F5.law1518, F5.not47, F5.not614, F5.not817, F5.not3862⟩,
    ⟨F13.law1518, F13.not47, F13.not614, F13.not817, F13.not3862⟩⟩

end Magma1518
