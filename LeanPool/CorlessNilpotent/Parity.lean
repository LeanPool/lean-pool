/-
Copyright (c) 2026 Marcel Blattner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Blattner
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import LeanPool.CorlessNilpotent.Path

/-!
# The folding identity, reduction modulo 2, and Corless's dimension theorem
-/

@[expose] public section

open Polynomial Finset

namespace Corless

/-- A sequence of `2n + 2` weights has opposite middle weights and mirrored halves. -/
def IsFolded (s : ℕ → ℤ) (n : ℕ) : Prop :=
  s (n + 1) = -s n ∧ ∀ i < n, s (2 * n + 1 - i) = s i

/-- Lemma 1 (folding identity). For a path with `2n + 3` vertices whose two middle edges carry
opposite signs and whose two halves are mirror images, `D = (D of a half)²`. -/
lemma Dv_fold (s : ℕ → ℤ) (n : ℕ) (h : IsFolded s n) :
    Dv s (2 * n + 3) = Dv s (n + 1) ^ 2 := by
  obtain ⟨hmid, hmir⟩ := h
  have suffix (m a : ℕ) (hm : m ≤ n + 1) (ha : a + m = 2 * n + 3) :
      Dv (fun i => s (i + a)) m = Dv s m := by
    rw [← Dv_reverse s m]
    apply Dv_congr
    intro i hi
    have agree := hmir (m - 2 - i) (by omega)
    rwa [show 2 * n + 1 - (m - 2 - i) = i + a by omega] at agree
  have hsplit := Dv_split s n (n + 1)
  rw [show n + (n + 1) + 2 = 2 * n + 3 by omega] at hsplit
  simp only [Nat.add_assoc] at hsplit
  have hleft := Dv_succ_succ_left (fun i => s (i + n + 1)) n
  simp_rw [Nat.zero_add, show ∀ i : ℕ, i + 2 + n + 1 = i + (n + 3) by intro i; omega,
    show ∀ i : ℕ, i + 1 + n + 1 = i + (n + 2) by intro i; omega] at hleft
  simp only [Nat.add_assoc] at hleft
  rw [hsplit, hleft, suffix (n + 1) (n + 2) le_rfl (by omega),
    suffix n (n + 3) (by omega) (by omega), hmid, C_neg]
  ring

/-- The matching polynomial of the unweighted path with `j` vertices (a Fibonacci polynomial). -/
noncomputable def f (j : ℕ) : ℤ[X] := Dv (fun _ => 1) j

lemma f_succ_succ (j : ℕ) : f (j + 2) = f (j + 1) + X * f j := by
  simp [f, Dv_succ_succ]

/-- A sign sequence: every weight is `1` or `-1`. -/
def IsSign (s : ℕ → ℤ) : Prop := ∀ i, s i = 1 ∨ s i = -1

/-- Reduction modulo 2: for a sign sequence, `D ≡ f (mod 2)`. -/
lemma Dv_parity {s : ℕ → ℤ} (hs : IsSign s) : ∀ j, ∃ R : ℤ[X], Dv s j = f j + 2 * R
  | 0 => ⟨0, by simp [f]⟩
  | 1 => ⟨0, by simp [f]⟩
  | j + 2 => by
      obtain ⟨R1, h1⟩ := Dv_parity hs (j + 1)
      obtain ⟨R0, h0⟩ := Dv_parity hs j
      rcases hs j with h | h
      · exact ⟨R1 + X * R0, by rw [Dv_succ_succ, f_succ_succ, h1, h0, h]; simp; ring⟩
      · exact ⟨R1 - X * f j - X * R0, by rw [Dv_succ_succ, f_succ_succ, h1, h0, h]; simp; ring⟩

lemma two_le_pow (k : ℕ) : 2 ≤ 2 ^ (k + 1) := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The half and full path sizes expressed using the length of the half's edge sequence. -/
lemma folded_sizes (k : ℕ) :
    2 ^ (k + 1) - 1 = 2 ^ (k + 1) - 2 + 1 ∧
      2 ^ (k + 2) - 1 = 2 * (2 ^ (k + 1) - 2) + 3 := by
  have h := two_le_pow k
  constructor
  · omega
  · rw [pow_succ]
    omega

/-- Folding duplicates the half-path edges and adds two middle edges. -/
lemma folded_edges (k : ℕ) : 2 ^ (k + 2) - 2 = 2 * (2 ^ (k + 1) - 2) + 2 := by
  have full := (folded_sizes k).2
  omega

/-- The reference sequence: all `1` except `-1` at position `n + 1`. -/
def star (n : ℕ) : ℕ → ℤ := fun i => if i = n + 1 then -1 else 1

lemma isSign_star (n : ℕ) : IsSign (star n) := fun i => by
  by_cases h : i = n + 1 <;> simp [star, h]

lemma Dv_star (n : ℕ) : Dv (star n) (2 * n + 3) = f (n + 1) ^ 2 := by
  rw [Dv_fold]
  · congr 1
    apply Dv_congr
    intro i hi
    have : i ≠ n + 1 := by omega
    simp [star, this]
  · constructor
    · simp [star]
    · intro i hi
      have h1 : 2 * n + 1 - i ≠ n + 1 := by omega
      have h2 : i ≠ n + 1 := by omega
      simp [star, h1, h2]

/-- `f (2^(k+1) - 1) ≡ 1 (mod 2)`, proved through the folding identity. -/
lemma f_pow_two (k : ℕ) : ∃ A : ℤ[X], f (2 ^ (k + 1) - 1) = 1 + 2 * A := by
  induction k with
  | zero => exact ⟨0, by simp [f]⟩
  | succ k ih =>
      obtain ⟨A, hA⟩ := ih
      let n := 2 ^ (k + 1) - 2
      obtain ⟨hN, hM⟩ : 2 ^ (k + 1) - 1 = n + 1 ∧ 2 ^ (k + 2) - 1 = 2 * n + 3 :=
        folded_sizes k
      obtain ⟨R, hR⟩ := Dv_parity (isSign_star n) (2 * n + 3)
      rw [hN] at hA
      refine ⟨2 * A + 2 * A ^ 2 - R, ?_⟩
      rw [hM]
      have : f (2 * n + 3) = (1 + 2 * A) ^ 2 - 2 * R := by
        rw [← hA, ← Dv_star, hR]; ring
      rw [this]
      ring

/-- Reduction of `f` modulo 2. -/
noncomputable def fbar (j : ℕ) : (ZMod 2)[X] := (f j).map (Int.castRingHom (ZMod 2))

lemma fbar_succ_succ (j : ℕ) : fbar (j + 2) = fbar (j + 1) + X * fbar j := by
  simp [fbar, f_succ_succ, Polynomial.map_add, Polynomial.map_mul]

lemma two_eq_zero_Z2X : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero

/-- Lemma 2 (closed form over 𝔽₂): substituting `x = y + y²` gives `(1 + y)^(j+1) + y^(j+1)`. -/
lemma fbar_comp : ∀ j, (fbar j).comp (X + X ^ 2) = (1 + X) ^ (j + 1) + X ^ (j + 1)
  | 0 => by
      simp [fbar, f]
      linear_combination (-(X : (ZMod 2)[X])) * two_eq_zero_Z2X
  | 1 => by
      simp [fbar, f]
      linear_combination (-(X : (ZMod 2)[X])) * two_eq_zero_Z2X - X ^ 2 * two_eq_zero_Z2X
  | j + 2 => by
      rw [fbar_succ_succ, add_comp, mul_comp, X_comp, fbar_comp (j + 1), fbar_comp j]
      linear_combination (X : (ZMod 2)[X]) ^ (j + 2) * two_eq_zero_Z2X

/-- Over 𝔽₂, `(1 + X)^n = 1 + X^n` with `n ≥ 1` forces `n` to be a power of two. -/
lemma pow_two_of_frob : ∀ n : ℕ, 1 ≤ n → ((1 + X : (ZMod 2)[X]) ^ n = 1 + X ^ n) → ∃ a, n = 2 ^ a
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, _ => ⟨0, by norm_num⟩
  | n + 2, _, h => by
      -- the coefficient of X forces n + 2 to be even
      have hc := congrArg (fun p : (ZMod 2)[X] => p.coeff 1) h
      simp only [coeff_one_add_X_pow, coeff_add, coeff_one, coeff_X_pow] at hc
      have hn1 : (1 : ℕ) ≠ n + 2 := by omega
      simp only [Nat.choose_one_right, one_ne_zero, ite_false, hn1, zero_add] at hc
      have heven : Even (n + 2) := by
        have : ((n + 2 : ℕ) : ZMod 2) = 0 := by exact_mod_cast hc
        rw [ZMod.natCast_eq_zero_iff_even] at this
        exact this
      obtain ⟨r, hr⟩ := heven
      have hr1 : 1 ≤ r := by omega
      -- squares agree, and squaring is injective in characteristic 2
      have hsq : ((1 + X : (ZMod 2)[X]) ^ r) ^ 2 = (1 + X ^ r) ^ 2 := by
        have hfrob : (1 + X ^ r : (ZMod 2)[X]) ^ 2 = 1 + X ^ (r * 2) := by
          have := add_pow_char (R := (ZMod 2)[X]) (p := 2) (1 : (ZMod 2)[X]) (X ^ r)
          rw [one_pow, ← pow_mul] at this
          exact this
        rw [hfrob, ← pow_mul, show r * 2 = n + 2 by omega]
        exact h
      have hr' : (1 + X : (ZMod 2)[X]) ^ r = 1 + X ^ r :=
        frobenius_inj (ZMod 2)[X] 2 hsq
      obtain ⟨a, ha⟩ := pow_two_of_frob r hr1 hr'
      exact ⟨a + 1, by rw [pow_succ, ← ha]; omega⟩

/-- Corless's dimension theorem: if `D = 1` for a sign sequence on a path with `m ≥ 1` vertices,
then `m = 2^(k+1) - 1` for some `k`. -/
theorem dimension {s : ℕ → ℤ} (hs : IsSign s) {m : ℕ} (hm : 1 ≤ m) (h : Dv s m = 1) :
    ∃ k, m = 2 ^ (k + 1) - 1 := by
  obtain ⟨R, hR⟩ := Dv_parity hs m
  have hf : fbar m = 1 := by
    have : f m = 1 - 2 * R := by rw [← h, hR]; ring
    have h2 : Polynomial.map (Int.castRingHom (ZMod 2)) (2 : ℤ[X]) = 2 := by simp
    simp only [fbar, this, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, h2,
      two_eq_zero_Z2X, zero_mul, sub_zero]
  have hc := fbar_comp m
  rw [hf, one_comp] at hc
  have h2 : (1 + X : (ZMod 2)[X]) ^ (m + 1) = 1 + X ^ (m + 1) := by
    linear_combination (-1 : (ZMod 2)[X]) * hc - X ^ (m + 1) * two_eq_zero_Z2X
  obtain ⟨a, ha⟩ := pow_two_of_frob (m + 1) (by omega) h2
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0] at ha; omega
    · exact h0
  exact ⟨a - 1, by rw [show a - 1 + 1 = a by omega]; omega⟩

end Corless
