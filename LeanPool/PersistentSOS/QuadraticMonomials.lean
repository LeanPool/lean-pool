/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
Original MIT notice (retained under the permission to sublicense):

MIT License

Copyright (c) 2026 JD Jones

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Tactic.IntervalCases

/-!
# Quadratic Monomials

Part of the explicit persistent quartic SOS counterexample.
-/

public section
namespace PersistentSOS

/-- Every monomial of total degree at most two is constant, a variable,
or a product of two variables (allowing a repeated variable). -/
theorem exponent_degree_le_two {σ : Type*} (d : σ →₀ ℕ)
    (h : d.sum (fun _ n => n) ≤ 2) :
    d = 0 ∨ (∃ i, d = Finsupp.single i 1) ∨
      (∃ i j, d = Finsupp.single i 1 + Finsupp.single j 1) := by
  classical
  have hc : d.toMultiset.card ≤ 2 := by simpa only [Finsupp.card_toMultiset, Function.id_def]
    using h
  interval_cases hcard : d.toMultiset.card
  · left
    have hm : d.toMultiset = 0 := Multiset.card_eq_zero.mp hcard
    have := congrArg Multiset.toFinsupp hm
    simpa using this
  · right; left
    obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp hcard
    refine ⟨i, ?_⟩
    have := congrArg Multiset.toFinsupp hi
    simpa using this
  · right; right
    obtain ⟨i, j, hij⟩ := Multiset.card_eq_two.mp hcard
    refine ⟨i, j, ?_⟩
    have := congrArg Multiset.toFinsupp hij
    simpa [← Multiset.singleton_add, map_add] using this

end PersistentSOS
