/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Integer polynomials and verified Bernstein sign checkers

Vendored from `SevenTriangles/Certificates/IntPoly.lean` (commit `b17ca52a`), with an early
failure test (`endNeg`) inside the bisection and, at the end of the file, consecutive interval
chains (`chainCheck`) and nonnegativity with explicit rational split points (`nonnegOnSplit`).

`IPoly := List Int` is a dense coefficient list, lowest degree first.  Every operation below is
computable, uses only structural recursion (or explicit fuel), and is meant to be unfolded by the
kernel inside `decide +kernel` proofs.  The semantic layer (`evalR`) is noncomputable and the two
soundness theorems `nonnegOn_sound` / `posOn_sound` are the only trusted statements.

Length conventions (they matter: Bernstein coefficients depend on the *formal* degree, i.e. on the
list length, so trailing zeros are never trimmed):

* `add p q` has length `max p.length q.length`; `smul c p`, `sub p q` follow;
* `mul` is the literal recursion `mul [] q = []`, `mul (a :: p) q = add (smul a q) (0 :: mul p q)`:
  length `p.length + q.length - 1` for nonempty factors, and `mul p [] = [0, …, 0]` (`p.length`
  zeros).  Consequently `comp p a e d` of a nonempty `p` has length `p.length + 1` (one trailing
  zero: the Bernstein test is degree-elevated by one).  The Python exporter reproduces exactly
  this ("literal mode"); do not "optimise" the representation without changing both sides;
* `pascal n` has length `n + 1`; `bern p` has the same length as `p`;
* `strip p = (j, q)` with `p = x ^ j * q` and `q` either empty or with nonzero constant term.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

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

@[expose] public section

namespace ConwaySoifer.Certificates

/-- Dense integer coefficients in increasing degree order; trailing zeros are retained. -/
abbrev IPoly := List Int

namespace IPoly

/-! ## Computable operations -/

/-- Coefficientwise addition of dense integer polynomials. -/
def add : IPoly → IPoly → IPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

/-- Multiply every polynomial coefficient by an integer scalar. -/
def smul (c : Int) : IPoly → IPoly
  | [] => []
  | a :: p => c * a :: smul c p

/-- Subtract dense integer coefficient lists. -/
def sub (p q : IPoly) : IPoly := add p (smul (-1) q)

/-- Multiplication by `x`. -/
def shift (p : IPoly) : IPoly := 0 :: p

/-- Product (literal recursion; see the length conventions above). -/
def mul : IPoly → IPoly → IPoly
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

/-- Remove the leading (lowest-degree) zero coefficients: `strip p = (j, q)` with `p = x ^ j q`. -/
def strip : IPoly → Nat × IPoly
  | [] => (0, [])
  | a :: p =>
      if a = 0 then
        match strip p with
        | (j, q) => (j + 1, q)
      else (0, a :: p)

/-- Row `n` of Pascal's triangle, i.e. the coefficients of `(1 + x) ^ n`. -/
def pascal : Nat → IPoly
  | 0 => [1]
  | n + 1 =>
      let r := pascal n
      add (0 :: r) (r ++ [0])

/-- Coefficients of `p` in the (unnormalised) Bernstein basis `t ^ k (1-t) ^ (n-k)`, `n = p.length -
1`. -/
def bern : IPoly → IPoly
  | [] => []
  | c :: cs => add (smul c (pascal cs.length)) (0 :: bern cs)

/-- Structural integer exponentiation. -/
def ipow (b : Int) : Nat → Int
  | 0 => 1
  | n + 1 => b * ipow b n

/-- `comp p a e d = Σ_j c_j d ^ (n-j) (a + e t) ^ j` where `n = p.length - 1`; the affine
substitution `x = (a + e t) / d` cleared of denominators. -/
def comp : IPoly → Int → Int → Int → IPoly
  | [], _, _, _ => []
  | c :: rest, a, e, d => add [c * ipow d rest.length] (mul [a, e] (comp rest a e d))

/-- Test that every integer coefficient is nonnegative. -/
def allNonneg : IPoly → Bool
  | [] => true
  | c :: p => decide (0 ≤ c) && allNonneg p

/-- Test that every integer coefficient is strictly positive. -/
def allPos : IPoly → Bool
  | [] => true
  | c :: p => decide (0 < c) && allPos p

end IPoly

open IPoly

/-- `Σ_j c_j num ^ j den ^ (N-j)` (with truncated subtraction); equals `den ^ N * p (num/den)`
whenever
`N ≥ p.length - 1`.  Used only for exact sign comparisons inside the untrusted search. -/
def evalScaledN : IPoly → Int → Int → Nat → Int
  | [], _, _, _ => 0
  | c :: p, num, den, N => c * ipow den N + num * evalScaledN p num den (N - 1)

/-- The first or last Bernstein coefficient (the values at the ends of the interval) is
negative: bisection cannot succeed.  Only an optimisation of the search; soundness never uses it. -/
def endNeg (c : IPoly) : Bool :=
  match c.head?, c.getLast? with
  | some x, some y => decide (x < 0) || decide (y < 0)
  | _, _ => false

/-- Detect a nonpositive endpoint Bernstein coefficient before attempting bisection. -/
def endNonpos (c : IPoly) : Bool :=
  match c.head?, c.getLast? with
  | some x, some y => decide (x ≤ 0) || decide (y ≤ 0)
  | _, _ => false

/-- `p ≥ 0` on `[a/d, b/d]`, by Bernstein coefficients with adaptive bisection. -/
def nonnegOn (p : IPoly) : Int → Int → Int → Nat → Bool
  | a, b, d, 0 => allNonneg (bern (comp p a (b - a) d))
  | a, b, d, fuel + 1 =>
      let c := bern (comp p a (b - a) d)
      allNonneg c ||
        (!endNeg c && nonnegOn p (2 * a) (a + b) (2 * d) fuel &&
          nonnegOn p (a + b) (2 * b) (2 * d) fuel)

/-- `q > 0` on `[a/d, b/d]`, by strictly positive Bernstein coefficients (needs `q ≠ []`). -/
def posOn' (q : IPoly) : Int → Int → Int → Nat → Bool
  | a, b, d, 0 => allPos (bern (comp q a (b - a) d))
  | a, b, d, fuel + 1 =>
      let c := bern (comp q a (b - a) d)
      allPos c ||
        (!endNonpos c && posOn' q (2 * a) (a + b) (2 * d) fuel &&
          posOn' q (a + b) (2 * b) (2 * d) fuel)

/-- `p > 0` on `[a/d, b/d] ∩ (0, ∞)`: strip the factor `x ^ j`, then `posOn'` on the quotient. -/
def posOn (p : IPoly) (a b d : Int) (fuel : Nat) : Bool :=
  match strip p with
  | (_, []) => false
  | (_, c :: q) => posOn' (c :: q) a b d fuel

/-! ## Semantics -/

section RealEvaluation

/-- Horner evaluation over the reals. -/
noncomputable def evalR : IPoly → ℝ → ℝ
  | [], _ => 0
  | c :: p, x => (c : ℝ) + x * evalR p x

namespace IPoly

@[simp] theorem evalR_nil (x : ℝ) : evalR [] x = 0 := rfl
@[simp] theorem evalR_cons (c : Int) (p : IPoly) (x : ℝ) :
    evalR (c :: p) x = (c : ℝ) + x * evalR p x := rfl

theorem evalR_add (p q : IPoly) (x : ℝ) : evalR (add p q) x = evalR p x + evalR q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]; ring

theorem evalR_smul (c : Int) (p : IPoly) (x : ℝ) : evalR (smul c p) x = (c : ℝ) * evalR p x := by
  induction p with
  | nil => simp [smul]
  | cons a p ih => simp [smul, ih]; ring

theorem evalR_sub (p q : IPoly) (x : ℝ) : evalR (sub p q) x = evalR p x - evalR q x := by
  simp [sub, evalR_add, evalR_smul]; ring

theorem evalR_shift (p : IPoly) (x : ℝ) : evalR (shift p) x = x * evalR p x := by
  simp [shift]

theorem evalR_mul (p q : IPoly) (x : ℝ) : evalR (mul p q) x = evalR p x * evalR q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp [mul, evalR_add, evalR_smul, ih]; ring

theorem cast_ipow (b : Int) (n : Nat) : ((ipow b n : Int) : ℝ) = (b : ℝ) ^ n := by
  induction n with
  | zero => simp [ipow]
  | succ n ih => simp [ipow, ih, pow_succ]; ring

theorem evalR_strip (p : IPoly) (x : ℝ) :
    evalR p x = x ^ (strip p).1 * evalR (strip p).2 x := by
  induction p with
  | nil => simp [strip]
  | cons a p ih =>
    by_cases ha : a = 0
    · subst ha
      rcases hs : strip p with ⟨j, q⟩
      rw [hs] at ih
      simp [strip, hs, ih, pow_succ]
      ring
    · simp [strip, ha]

/-! ### Lengths -/

theorem length_add (p q : IPoly) : (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]

theorem length_smul (c : Int) (p : IPoly) : (smul c p).length = p.length := by
  induction p with
  | nil => simp [smul]
  | cons a p ih => simp [smul, ih]

theorem length_pascal (n : Nat) : (pascal n).length = n + 1 := by
  induction n with
  | zero => simp [pascal]
  | succ n ih => simp [pascal, length_add, ih]

theorem length_bern (p : IPoly) : (bern p).length = p.length := by
  induction p with
  | nil => simp [bern]
  | cons c cs ih => simp [bern, length_add, length_smul, length_pascal, ih]

theorem comp_ne_nil (p : IPoly) (a e d : Int) (hp : p ≠ []) : comp p a e d ≠ [] := by
  cases p with
  | nil => exact absurd rfl hp
  | cons c rest =>
    simp only [comp]
    cases h : mul [a, e] (comp rest a e d) with
    | nil => simp [add]
    | cons y ys => simp [add]

theorem bern_ne_nil (p : IPoly) (hp : p ≠ []) : bern p ≠ [] := by
  cases p with
  | nil => exact absurd rfl hp
  | cons c cs =>
    simp only [bern]
    cases h : smul c (pascal cs.length) with
    | nil => simp [add]
    | cons y ys => simp [add]

/-! ### Homogeneous (Bernstein) evaluation -/

/-- `evalH b s t = Σ_k b_k t ^ k s ^ (n-k)` with `n = b.length - 1`. -/
noncomputable def evalH : IPoly → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | c :: cs, s, t => (c : ℝ) * s ^ cs.length + t * evalH cs s t

theorem evalH_add (p q : IPoly) (hlen : p.length = q.length) (s t : ℝ) :
    evalH (add p q) s t = evalH p s t + evalH q s t := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => simp [add, evalH]
    | cons b q => simp at hlen
  | cons a p ih =>
    cases q with
    | nil => simp at hlen
    | cons b q =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [add, evalH, length_add, hlen, max_self, ih q hlen]
      push_cast
      ring

theorem evalH_smul (c : Int) (p : IPoly) (s t : ℝ) :
    evalH (smul c p) s t = (c : ℝ) * evalH p s t := by
  induction p with
  | nil => simp [smul, evalH]
  | cons a p ih => simp only [smul, evalH, length_smul, ih]; push_cast; ring

theorem evalH_append_zero (p : IPoly) (s t : ℝ) :
    evalH (p ++ [0]) s t = s * evalH p s t := by
  induction p with
  | nil => simp [evalH]
  | cons a p ih =>
    simp only [List.cons_append, evalH, List.length_append, List.length_singleton, ih]; ring

theorem evalH_pascal (n : Nat) (s t : ℝ) : evalH (pascal n) s t = (s + t) ^ n := by
  induction n with
  | zero => simp [pascal, evalH]
  | succ n ih =>
    simp only [pascal]
    rw [evalH_add _ _ (by simp [length_pascal]), evalH_append_zero]
    simp only [evalH, length_pascal, ih]
    push_cast
    ring

theorem evalH_bern (p : IPoly) (t : ℝ) : evalH (bern p) (1 - t) t = evalR p t := by
  induction p with
  | nil => simp [bern, evalH]
  | cons c cs ih =>
    simp only [bern]
    rw [evalH_add _ _ (by simp [length_smul, length_pascal, length_bern]), evalH_smul, evalH_pascal]
    simp only [evalH, ih, evalR_cons]
    push_cast
    ring

theorem allNonneg_iff (b : IPoly) : allNonneg b = true ↔ ∀ c ∈ b, 0 ≤ c := by
  induction b with
  | nil => simp [allNonneg]
  | cons c cs ih => simp [allNonneg, ih]

theorem allPos_iff (b : IPoly) : allPos b = true ↔ ∀ c ∈ b, 0 < c := by
  induction b with
  | nil => simp [allPos]
  | cons c cs ih => simp [allPos, ih]

theorem evalH_nonneg (b : IPoly) (h : allNonneg b = true) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ evalH b s t := by
  induction b with
  | nil => simp [evalH]
  | cons c cs ih =>
    simp only [allNonneg, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [evalH]
    have hc : (0 : ℝ) ≤ c := by
      exact_mod_cast h.1
    have := ih h.2
    positivity

theorem evalH_pos (b : IPoly) (h : allPos b = true) (hb : b ≠ []) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hst : 0 < s + t) : 0 < evalH b s t := by
  induction b with
  | nil => exact absurd rfl hb
  | cons c cs ih =>
    simp only [allPos, Bool.and_eq_true, decide_eq_true_eq] at h
    have hc : (0 : ℝ) < c := by
      exact_mod_cast h.1
    simp only [evalH]
    cases cs with
    | nil => simp [evalH, hc]
    | cons c' cs' =>
      have hpos := ih h.2 (by simp)
      rcases eq_or_lt_of_le ht with ht0 | ht0
      · subst ht0
        have hs' : 0 < s := by
          linarith
        have : 0 < (c : ℝ) * s ^ (c' :: cs').length := by
          positivity
        linarith
      · have h1 : 0 ≤ (c : ℝ) * s ^ (c' :: cs').length := by
          positivity
        have h2 : 0 < t * evalH (c' :: cs') s t := mul_pos ht0 hpos
        linarith

/-! ### Affine substitution -/

theorem evalR_comp (p : IPoly) (a e d : Int) (hd : (d : ℝ) ≠ 0) (t : ℝ) :
    (d : ℝ) * evalR (comp p a e d) t =
      (d : ℝ) ^ p.length * evalR p (((a : ℝ) + e * t) / d) := by
  induction p with
  | nil => simp [comp]
  | cons c rest ih =>
    simp only [comp, evalR_add, evalR_mul, evalR_cons, evalR_nil, List.length_cons]
    push_cast
    rw [cast_ipow]
    have hy : (d : ℝ) ^ (rest.length + 1) * (((a : ℝ) + e * t) / d) =
        (d : ℝ) ^ rest.length * ((a : ℝ) + e * t) := by
      field_simp
      ring
    have hmul : ((a : ℝ) + t * ((e : ℝ) + t * 0)) * ((d : ℝ) * evalR (comp rest a e d) t) =
        ((a : ℝ) + e * t) * ((d : ℝ) ^ rest.length * evalR rest (((a : ℝ) + e * t) / d)) := by
      rw [ih]; ring
    linear_combination hmul - (evalR rest (((a : ℝ) + e * t) / d)) * hy

end IPoly

open IPoly

theorem exists_param (a b d : Int) (hd : 0 < d) (x : ℝ) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (a : ℝ) + ((b - a : Int) : ℝ) * t = d * x := by
  have hd' : (0 : ℝ) < d := by
    exact_mod_cast hd
  have ha : (a : ℝ) ≤ d * x := by
    rw [div_le_iff₀ hd'] at hlo; linarith
  have hb : (d : ℝ) * x ≤ b := by
    rw [le_div_iff₀ hd'] at hhi; linarith
  by_cases hab : (a : ℝ) < b
  · have hba : (0 : ℝ) < (b : ℝ) - a := sub_pos.mpr hab
    refine ⟨((d : ℝ) * x - a) / ((b : ℝ) - a), div_nonneg (by linarith) hba.le, ?_, ?_⟩
    · rw [div_le_one hba]; linarith
    · push_cast
      field_simp
      ring
  · have hab' : (a : ℝ) = b := le_antisymm (by linarith) (not_lt.mp hab)
    refine ⟨0, le_rfl, zero_le_one, ?_⟩
    push_cast
    linarith

theorem bern_comp_nonneg_sound (p : IPoly) (a b d : Int)
    (h : allNonneg (bern (comp p a (b - a) d)) = true) (hd : 0 < d) (x : ℝ)
    (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) : 0 ≤ evalR p x := by
  obtain ⟨t, ht0, ht1, hxt⟩ := exists_param a b d hd x hlo hhi
  have hd' : (0 : ℝ) < d := by
    exact_mod_cast hd
  have hq : 0 ≤ evalR (comp p a (b - a) d) t := by
    rw [← evalH_bern]
    exact evalH_nonneg _ h (by linarith) ht0
  have hc := evalR_comp p a (b - a) d hd'.ne' t
  have hx : ((a : ℝ) + ((b - a : Int) : ℝ) * t) / d = x := by
    rw [hxt]; field_simp
  rw [hx] at hc
  have : 0 ≤ (d : ℝ) ^ p.length * evalR p x := by
    rw [← hc]; exact mul_nonneg hd'.le hq
  exact (mul_nonneg_iff_of_pos_left (pow_pos hd' _)).mp this

theorem bern_comp_pos_sound (q : IPoly) (hq : q ≠ []) (a b d : Int)
    (h : allPos (bern (comp q a (b - a) d)) = true) (hd : 0 < d) (x : ℝ)
    (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) : 0 < evalR q x := by
  obtain ⟨t, ht0, ht1, hxt⟩ := exists_param a b d hd x hlo hhi
  have hd' : (0 : ℝ) < d := by
    exact_mod_cast hd
  have hne : bern (comp q a (b - a) d) ≠ [] := bern_ne_nil _ (comp_ne_nil _ _ _ _ hq)
  have hq' : 0 < evalR (comp q a (b - a) d) t := by
    rw [← evalH_bern]
    exact evalH_pos _ h hne (by linarith) ht0 (by linarith)
  have hc := evalR_comp q a (b - a) d hd'.ne' t
  have hx : ((a : ℝ) + ((b - a : Int) : ℝ) * t) / d = x := by
    rw [hxt]; field_simp
  rw [hx] at hc
  have : 0 < (d : ℝ) ^ q.length * evalR q x := by
    rw [← hc]; exact mul_pos hd' hq'
  exact (mul_pos_iff_of_pos_left (pow_pos hd' _)).mp this

theorem half_lo (a d : Int) (x : ℝ) (hlo : (a : ℝ) / d ≤ x) :
    ((2 * a : Int) : ℝ) / ((2 * d : Int) : ℝ) ≤ x := by
  push_cast
  rw [mul_div_mul_left _ _ (two_ne_zero)]
  exact hlo

theorem half_hi (b d : Int) (x : ℝ) (hhi : x ≤ (b : ℝ) / d) :
    x ≤ ((2 * b : Int) : ℝ) / ((2 * d : Int) : ℝ) := by
  push_cast
  rw [mul_div_mul_left _ _ (two_ne_zero)]
  exact hhi

theorem nonnegOn_sound (p : IPoly) (a b d : Int) (fuel : Nat)
    (h : nonnegOn p a b d fuel = true) (hd : 0 < d) (x : ℝ) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) : 0 ≤ evalR p x := by
  induction fuel generalizing a b d with
  | zero => exact bern_comp_nonneg_sound p a b d h hd x hlo hhi
  | succ fuel ih =>
    simp only [nonnegOn, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨-, h1⟩, h2⟩
    · exact bern_comp_nonneg_sound p a b d h hd x hlo hhi
    · have hd2 : 0 < 2 * d := by
        omega
      rcases le_total x (((a + b : Int) : ℝ) / ((2 * d : Int) : ℝ)) with hm | hm
      · exact ih (2 * a) (a + b) (2 * d) h1 hd2 (half_lo a d x hlo) hm
      · exact ih (a + b) (2 * b) (2 * d) h2 hd2 hm (half_hi b d x hhi)

theorem posOn'_sound (q : IPoly) (hq : q ≠ []) (a b d : Int) (fuel : Nat)
    (h : posOn' q a b d fuel = true) (hd : 0 < d) (x : ℝ) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) : 0 < evalR q x := by
  induction fuel generalizing a b d with
  | zero => exact bern_comp_pos_sound q hq a b d h hd x hlo hhi
  | succ fuel ih =>
    simp only [posOn', Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨-, h1⟩, h2⟩
    · exact bern_comp_pos_sound q hq a b d h hd x hlo hhi
    · have hd2 : 0 < 2 * d := by
        omega
      rcases le_total x (((a + b : Int) : ℝ) / ((2 * d : Int) : ℝ)) with hm | hm
      · exact ih (2 * a) (a + b) (2 * d) h1 hd2 (half_lo a d x hlo) hm
      · exact ih (a + b) (2 * b) (2 * d) h2 hd2 hm (half_hi b d x hhi)

theorem posOn_sound (p : IPoly) (a b d : Int) (fuel : Nat)
    (h : posOn p a b d fuel = true) (hd : 0 < d) (x : ℝ) (hx : 0 < x)
    (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) : 0 < evalR p x := by
  unfold posOn at h
  split at h
  · exact absurd h (by simp)
  · rename_i j c q hs
    have hq := posOn'_sound (c :: q) (by simp) a b d fuel h hd x hlo hhi
    rw [evalR_strip p x, hs]
    exact mul_pos (pow_pos hx _) hq

end RealEvaluation

/-! ## Consecutive interval chains and rational split points -/

/-- Rational number `n/m` with `m > 0`, as a pair. -/
abbrev IRat := Int × Int

/-- `chainCheck f hi cur pieces`: `pieces = [(a₁, b₁, d₁), …]` are consecutive rational intervals
`[aᵢ/dᵢ, bᵢ/dᵢ]` (all `dᵢ > 0`) starting at `cur`, ending at `hi`, and `f aᵢ bᵢ dᵢ` holds on
each.  Endpoint equality is tested by cross-multiplication. -/
def chainCheck (f : Int → Int → Int → Bool) (hi : IRat) : IRat → List (Int × Int × Int) → Bool
  | _, [] => false
  | (cn, cd), [(a', b', d')] =>
      decide (0 < d') && decide (cn * d' = a' * cd) && f a' b' d' &&
        decide (b' * hi.2 = hi.1 * d')
  | (cn, cd), (a', b', d') :: s :: rest =>
      decide (0 < d') && decide (cn * d' = a' * cd) && f a' b' d' &&
        chainCheck f hi (b', d') (s :: rest)

/-- The consecutive pieces of `[cur, b/d]` cut at the split points `pts` (each `n/m`, `m > 0`),
produced by the untrusted search. -/
def piecesFrom (b d : Int) : IRat → List IRat → List (Int × Int × Int)
  | (n, m), [] => [(n * d, b * m, m * d)]
  | (n, m), (n', m') :: rest => (n * m', n' * m, m * m') :: piecesFrom b d (n', m') rest

/-- Build exact adjacent rational intervals between supplied split points. -/
def piecesOf (a b d : Int) (pts : List IRat) : List (Int × Int × Int) := piecesFrom b d (a, d) pts

/-- Nonnegativity on `[a/d, b/d]` with explicit split points: trusted only through
`chainCheck` and `nonnegOn` on each piece. -/
def nonnegOnSplit (p : IPoly) (a b d : Int) (fuel : Nat) (pts : List IRat) : Bool :=
  chainCheck (fun a' b' d' => nonnegOn p a' b' d' fuel) (b, d) (a, d) (piecesOf a b d pts)

section IntervalSoundness

theorem rat_eq_of_cross {a b c d : Int} (hb : 0 < b) (hd : 0 < d) (h : a * d = c * b) :
    (a : ℝ) / b = (c : ℝ) / d := by
  have hbR : (0 : ℝ) < b := by
    exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by
    exact_mod_cast hd
  rw [div_eq_div_iff hbR.ne' hdR.ne']
  exact_mod_cast h

theorem chainCheck_sound (f : Int → Int → Int → Bool) (hi : IRat) (hhi : 0 < hi.2) (x : ℝ)
    (hx : x ≤ (hi.1 : ℝ) / hi.2) (pieces : List (Int × Int × Int)) :
    ∀ cur : IRat, 0 < cur.2 → chainCheck f hi cur pieces = true → (cur.1 : ℝ) / cur.2 ≤ x →
      ∃ a' b' d', 0 < d' ∧ f a' b' d' = true ∧ (a' : ℝ) / d' ≤ x ∧ x ≤ (b' : ℝ) / d' := by
  induction pieces with
  | nil => intro cur _ h; simp [chainCheck] at h
  | cons s rest ih =>
    rintro ⟨cn, cd⟩ hcd h hlo
    obtain ⟨a', b', d'⟩ := s
    cases rest with
    | nil =>
      rw [chainCheck] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hd', hcur⟩, hf⟩, hb⟩ := h
      refine ⟨a', b', d', hd', hf, ?_, ?_⟩
      · rw [rat_eq_of_cross hd' hcd hcur.symm]; exact hlo
      · rw [rat_eq_of_cross hd' hhi hb]; exact hx
    | cons s' rest' =>
      rw [chainCheck] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hd', hcur⟩, hf⟩, hrest⟩ := h
      rcases le_total x ((b' : ℝ) / d') with hm | hm
      · refine ⟨a', b', d', hd', hf, ?_, hm⟩
        rw [rat_eq_of_cross hd' hcd hcur.symm]; exact hlo
      · exact ih (b', d') hd' hrest hm

theorem nonnegOnSplit_sound (p : IPoly) (a b d : Int) (fuel : Nat) (pts : List IRat)
    (h : nonnegOnSplit p a b d fuel pts = true) (hd : 0 < d) (x : ℝ)
    (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) : 0 ≤ evalR p x := by
  obtain ⟨a', b', d', hd', hf, hlo', hhi'⟩ :=
    chainCheck_sound _ (b, d) hd x hhi _ (a, d) hd h hlo
  exact nonnegOn_sound p a' b' d' fuel hf hd' x hlo' hhi'

end IntervalSoundness

end ConwaySoifer.Certificates
