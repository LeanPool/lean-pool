/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Data.Int.GCD

import Mathlib.Algebra.Order.Group.Int
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.GetD
import Mathlib.Data.Set.Finite.Lattice

/-!
# The specification

A point satisfies the integral binary-form equation `y ^ 2 = F(x, z)`.
The numerator `x` and denominator `z` are coprime and normalized, with `z > 0` or
`(x, z) = (1, 0)`. The height is `max |x| z`. This specification is independent
of the executable search.

* `Ratpoints.binaryForm` evaluates the binary form at the two coordinates.
* `Ratpoints.IsPoint` specifies the normalized points of bounded height.
* `Ratpoints.points` is the finite set of these points.
-/

@[expose] public section

namespace Ratpoints

/-- The degree of the polynomial `∑ cᵢ Xⁱ`: the largest index of a nonzero entry of `c`, or `0`
if there is none. -/
def degree (c : List ℤ) : ℕ := (c.reverse.dropWhile (· == 0)).length - 1

/-- The binary form `F(x, z) = ∑ cᵢ xⁱ z^(D - i)` of even degree `D = d + d % 2` of the
polynomial of degree `d` with coefficient list `c`. -/
def binaryForm (c : List ℤ) (x z : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (degree c + 1), c.getD i 0 * x ^ i * z ^ (degree c + degree c % 2 - i)

theorem degree_def (c : List ℤ) : degree c = (c.reverse.dropWhile (· == 0)).length - 1 := rfl

@[simp]
theorem degree_nil : degree [] = 0 := rfl

theorem degree_le_length_sub_one (c : List ℤ) : degree c ≤ c.length - 1 :=
  Nat.sub_le_sub_right (by simpa using (c.reverse.dropWhile_sublist (· == 0)).length_le) 1

theorem getD_eq_zero_of_degree_lt {c : List ℤ} {i : ℕ} (hi : degree c < i) : c.getD i 0 = 0 := by
  have hc := List.rdropWhile_append_rtakeWhile (p := (· == (0 : ℤ))) (l := c)
  have hlen : (c.rdropWhile (· == 0)).length ≤ i := by
    rw [degree_def] at hi
    simp only [List.rdropWhile, List.length_reverse]
    lia
  rw [← hc, List.getD_append_right _ _ _ _ hlen]
  rcases lt_or_ge (i - (c.rdropWhile (· == 0)).length) (c.rtakeWhile (· == 0)).length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    simpa using List.mem_rtakeWhile_imp (List.getElem_mem h)
  · exact List.getD_eq_default _ _ h

/-- The pair `(x, z)` is normalized and of height at most `H`, as the program prints the points:
`gcd(x, z) = 1`, `0 < z` or `(x, z) = (1, 0)`, `|x| ≤ H` and `z ≤ H`. So is the pair `(x, z)` of
every triple `(x, 0, z)` that the program prints under `RATPOINTS_NO_CHECK`, whether the triple is
a point or not. -/
def IsNormalizedPair (H : ℕ) (x z : ℤ) : Prop :=
  Int.gcd x z = 1 ∧ (0 < z ∨ z = 0 ∧ x = 1) ∧ |x| ≤ H ∧ z ≤ H

instance instDecidableIsNormalizedPair (H : ℕ) (x z : ℤ) : Decidable (IsNormalizedPair H x z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `(x, y, z)` is a point of height at most `H` on `y ^ 2 = F(x, z)`, `F = Ratpoints.binaryForm c`,
normalized as the program prints it: the equation holds, and `(x, z)` is normalized and of height
at most `H` (`Ratpoints.IsNormalizedPair`). -/
def IsPoint (c : List ℤ) (H : ℕ) (p : ℤ × ℤ × ℤ) : Prop :=
  p.2.1 ^ 2 = binaryForm c p.1 p.2.2 ∧ IsNormalizedPair H p.1 p.2.2

instance instDecidablePredIsPoint (c : List ℤ) (H : ℕ) : DecidablePred (IsPoint c H) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem finite_setOf_isPoint (c : List ℤ) (H : ℕ) : {p | IsPoint c H p}.Finite := by
  refine .of_finite_fibers (fun p ↦ (p.1, p.2.2)) ?_ fun b _ ↦ ?_
  · refine ((Set.finite_Icc (-H : ℤ) H).prod (Set.finite_Icc (0 : ℤ) H)).subset ?_
    rintro _ ⟨p, ⟨-, -, hz, hx, hzH⟩, rfl⟩
    exact ⟨abs_le.mp hx, by grind, hzH⟩
  · refine ((Set.finite_Icc (-binaryForm c b.1 b.2) (binaryForm c b.1 b.2)).image
      fun y ↦ (b.1, y, b.2)).subset ?_
    intro ⟨x, y, z⟩ ⟨⟨hy, _⟩, hb⟩
    obtain rfl : (x, z) = b := hb
    exact ⟨y, ⟨by lia [Int.le_self_sq (-y), neg_sq y], hy ▸ Int.le_self_sq y⟩, rfl⟩

/-- The finite set of the normalized points of height at most `H` on `y ^ 2 = F(x, z)`. -/
noncomputable def points (c : List ℤ) (H : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (finite_setOf_isPoint c H).toFinset

@[simp]
theorem mem_points {c : List ℤ} {H : ℕ} {p : ℤ × ℤ × ℤ} : p ∈ points c H ↔ IsPoint c H p :=
  Set.Finite.mem_toFinset _

/-! ### Points from the program's output, checked by `decide` -/

-- `ratpoints '-2 0 0 1' 130 -q` prints `(129 : 3830 : 100)`.
example : IsPoint [-2, 0, 0, 1] 130 (129, 3830, 100) := by decide

-- Degree 3 with a vanishing leading coefficient: the point at infinity `(1 : 0 : 0)`.
example : IsPoint [1, 1, 1, 1, 0] 1 (1, 0, 0) := by decide

-- The leading coefficient 2 is not a square: no point at infinity.
example : ¬ IsPoint [1, 0, 0, 0, 2] 5 (1, 1, 0) := by decide

end Ratpoints

end
