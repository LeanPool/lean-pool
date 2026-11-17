/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteBinomialIdentity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

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

public import LeanPool.GinibrePoincare.Analysis.HermiteOrthogonalityCombinatorics

/-! # Alternating Vandermonde identities for complex Hermites -/


@[expose] public section


open scoped BigOperators ComplexConjugate

namespace GinibrePoincare
namespace ComplexHermite

/-- An alternating form of Vandermonde's identity.  The proof extracts a
coefficient from
`(1+X)^N ((1+X)-1)^r = (1+X)^N X^r`. -/
theorem alternating_vandermonde (N K r : ℕ) :
    (∑ l ∈ Finset.range (r + 1),
      ((-1 : ℤ) ^ l) * (Nat.choose r l : ℤ) *
        (Nat.choose (N + r - l) K : ℤ)) =
      if r ≤ K then (Nat.choose N (K - r) : ℤ) else 0 := by
  let A : Polynomial ℤ := Polynomial.X + 1
  have hpoly :
      ∑ l ∈ Finset.range (r + 1),
          Polynomial.C (((-1 : ℤ) ^ l) * (Nat.choose r l : ℤ)) *
            A ^ (N + r - l) =
        Polynomial.X ^ r * A ^ N := by
    calc
      _ = A ^ N *
          ∑ l ∈ Finset.range (r + 1),
            Polynomial.C (((-1 : ℤ) ^ l) * (Nat.choose r l : ℤ)) *
              A ^ (r - l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        have hlr : l ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
        rw [show N + r - l = N + (r - l) by omega, pow_add]
        ring
      _ = A ^ N * ((Polynomial.C (-1) + A) ^ r) := by
        congr 1
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro l hl
        rw [show (Nat.choose r l : Polynomial ℤ) =
            Polynomial.C (Nat.choose r l : ℤ) by rfl,
          ← Polynomial.C_pow, Polynomial.C_mul]
        ring
      _ = Polynomial.X ^ r * A ^ N := by
        simp [A]
        ring
  have hcoeff := congrArg (fun P : Polynomial ℤ => P.coeff K) hpoly
  unfold A at hcoeff
  rw [Polynomial.coeff_X_pow_mul'] at hcoeff
  let coeffHom : Polynomial ℤ →+ ℤ :=
    { toFun := fun P => P.coeff K
      map_zero' := Polynomial.coeff_zero K
      map_add' := fun P Q => Polynomial.coeff_add P Q K }
  change coeffHom
      (∑ l ∈ Finset.range (r + 1),
        Polynomial.C (((-1 : ℤ) ^ l) * (Nat.choose r l : ℤ)) *
          (Polynomial.X + 1) ^ (N + r - l)) = _ at hcoeff
  simp only [map_sum] at hcoeff
  change (∑ l ∈ Finset.range (r + 1),
      (Polynomial.C (((-1 : ℤ) ^ l) * (Nat.choose r l : ℤ)) *
        (Polynomial.X + 1) ^ (N + r - l)).coeff K) = _ at hcoeff
  simpa only [Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_one_pow] using hcoeff

private theorem factorial_choose_balance (s l P M : ℕ)
    (hls : l ≤ s) (hM : M = P + (s - l)) :
    l.factorial * Nat.choose s l * M.factorial =
      s.factorial * P.factorial * Nat.choose M P := by
  have hPM : P ≤ M := by omega
  apply Nat.mul_right_cancel (m := (s - l).factorial)
  · positivity
  calc
    (l.factorial * Nat.choose s l * M.factorial) * (s - l).factorial =
        (Nat.choose s l * l.factorial * (s - l).factorial) * M.factorial := by ring
    _ = s.factorial * M.factorial := by
      rw [Nat.choose_mul_factorial_mul_factorial hls]
    _ = s.factorial *
        (Nat.choose M P * P.factorial * (M - P).factorial) := by
      rw [Nat.choose_mul_factorial_mul_factorial hPM]
    _ = (s.factorial * P.factorial * Nat.choose M P) *
        (s - l).factorial := by
      rw [hM]
      simp only [Nat.add_sub_cancel_left]
      ring

private theorem inner_hermite_alternating (p q r s k : ℕ)
    (hbal : p + s = q + r) (hkp : k ≤ p) (hkq : k ≤ q) :
    (∑ l ∈ Finset.range (min r s + 1),
      ((-1 : ℤ) ^ l) * (Nat.choose r l : ℤ) * (Nat.choose s l : ℤ) *
        (l.factorial : ℤ) * (((q - k) + (r - l)).factorial : ℤ)) =
      (s.factorial : ℤ) * ((p - k).factorial : ℤ) *
        (if r ≤ p - k then (Nat.choose (q - k) (p - k - r) : ℤ) else 0) := by
  let F : ℕ → ℤ := fun l =>
    ((-1 : ℤ) ^ l) * (Nat.choose r l : ℤ) * (Nat.choose s l : ℤ) *
      (l.factorial : ℤ) * (((q - k) + (r - l)).factorial : ℤ)
  let G : ℕ → ℤ := fun l =>
    ((-1 : ℤ) ^ l) * (Nat.choose r l : ℤ) *
      ((s.factorial * (p - k).factorial : ℕ) : ℤ) *
        (Nat.choose ((q - k) + r - l) (p - k) : ℤ)
  have hsub : Finset.range (min r s + 1) ⊆ Finset.range (r + 1) :=
    Finset.range_mono (Nat.succ_le_succ (min_le_left r s))
  have hext : (∑ l ∈ Finset.range (min r s + 1), F l) =
      ∑ l ∈ Finset.range (r + 1), F l := by
    apply Finset.sum_subset hsub
    intro l hlr hls
    have hsl : s < l := by
      have hlr' : l ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hlr)
      by_contra h
      exact hls (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (le_min hlr' (Nat.le_of_not_gt h))))
    simp [F, Nat.choose_eq_zero_of_lt hsl]
  rw [show (∑ l ∈ Finset.range (min r s + 1),
      ((-1 : ℤ) ^ l) * (Nat.choose r l : ℤ) * (Nat.choose s l : ℤ) *
        (l.factorial : ℤ) * (((q - k) + (r - l)).factorial : ℤ)) =
      ∑ l ∈ Finset.range (min r s + 1), F l by rfl, hext]
  have hFG : ∀ l ∈ Finset.range (r + 1), F l = G l := by
    intro l hl
    dsimp [F, G]
    have hlr : l ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    by_cases hls : l ≤ s
    · have hM : (q - k) + (r - l) = (p - k) + (s - l) := by omega
      have hfac := factorial_choose_balance s l (p - k)
        ((q - k) + (r - l)) hls hM
      have hfacZ := congrArg (fun x : ℕ => (x : ℤ)) hfac
      push_cast at hfacZ
      have hfacZ' : (Nat.choose s l : ℤ) * (l.factorial : ℤ) *
          (((q - k) + (r - l)).factorial : ℤ) =
          (s.factorial : ℤ) * ((p - k).factorial : ℤ) *
            (Nat.choose ((q - k) + (r - l)) (p - k) : ℤ) := by
        rw [← hfacZ]
        ring
      rw [show (q - k) + r - l = (q - k) + (r - l) by omega]
      calc
        _ = ((-1 : ℤ) ^ l) * (Nat.choose r l : ℤ) *
            ((Nat.choose s l : ℤ) * (l.factorial : ℤ) *
              (((q - k) + (r - l)).factorial : ℤ)) := by ring
        _ = ((-1 : ℤ) ^ l) * (Nat.choose r l : ℤ) *
            ((s.factorial : ℤ) * ((p - k).factorial : ℤ) *
              (Nat.choose ((q - k) + (r - l)) (p - k) : ℤ)) := by rw [hfacZ']
        _ = _ := by ring
    · have hsl : s < l := Nat.lt_of_not_ge hls
      have hsmall : (q - k) + r - l < p - k := by omega
      simp [Nat.choose_eq_zero_of_lt hsl,
        Nat.choose_eq_zero_of_lt hsmall]
  rw [Finset.sum_congr rfl hFG]
  unfold G
  calc
    _ = (s.factorial : ℤ) * ((p - k).factorial : ℤ) *
        ∑ x ∈ Finset.range (r + 1),
          (((-1 : ℤ) ^ x) * (Nat.choose r x : ℤ) *
            (Nat.choose ((q - k) + r - x) (p - k) : ℤ)) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      push_cast
      ring
    _ = _ := by rw [alternating_vandermonde (q - k) (p - k) r]

private theorem outer_hermite_alternating (p q r s : ℕ)
    (hbal : p + s = q + r) :
    (∑ k ∈ Finset.range (min p q + 1),
      ((-1 : ℤ) ^ k) * (Nat.choose p k : ℤ) * (Nat.choose q k : ℤ) *
        (k.factorial : ℤ) * (s.factorial : ℤ) * ((p - k).factorial : ℤ) *
          (if r ≤ p - k then (Nat.choose (q - k) (p - k - r) : ℤ) else 0)) =
      if p = r then (p.factorial : ℤ) * (q.factorial : ℤ) else 0 := by
  by_cases hrp : r ≤ p
  · let d := p - r
    have hdP : d ≤ p := Nat.sub_le _ _
    have hdQ : d ≤ q := by
      dsimp [d]
      omega
    have hdmin : Finset.range (d + 1) ⊆ Finset.range (min p q + 1) :=
      Finset.range_mono (Nat.succ_le_succ (le_min hdP hdQ))
    rw [show (∑ k ∈ Finset.range (min p q + 1),
        ((-1 : ℤ) ^ k) * (Nat.choose p k : ℤ) * (Nat.choose q k : ℤ) *
          (k.factorial : ℤ) * (s.factorial : ℤ) * ((p - k).factorial : ℤ) *
            (if r ≤ p - k then
              (Nat.choose (q - k) (p - k - r) : ℤ) else 0)) =
        ∑ k ∈ Finset.range (d + 1),
          ((-1 : ℤ) ^ k) * (Nat.choose p k : ℤ) * (Nat.choose q k : ℤ) *
            (k.factorial : ℤ) * (s.factorial : ℤ) * ((p - k).factorial : ℤ) *
              (if r ≤ p - k then
                (Nat.choose (q - k) (p - k - r) : ℤ) else 0) by
      symm
      apply Finset.sum_subset hdmin
      intro k hk hkd
      have hdk : d < k := by
        by_contra h
        exact hkd (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_not_gt h)))
      have hkp : k ≤ p := (le_min_iff.mp
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).1
      have hnot : ¬r ≤ p - k := by omega
      simp [hnot]]
    have hterm : ∀ k ∈ Finset.range (d + 1),
        ((-1 : ℤ) ^ k) * (Nat.choose p k : ℤ) * (Nat.choose q k : ℤ) *
            (k.factorial : ℤ) * (s.factorial : ℤ) * ((p - k).factorial : ℤ) *
              (if r ≤ p - k then
                (Nat.choose (q - k) (p - k - r) : ℤ) else 0) =
          (p.factorial : ℤ) * (s.factorial : ℤ) * (Nat.choose q d : ℤ) *
            (((-1 : ℤ) ^ k) * (Nat.choose d k : ℤ)) := by
      intro k hk
      have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hkp : k ≤ p := hkd.trans hdP
      have hkq : k ≤ q := hkd.trans hdQ
      have hrpk : r ≤ p - k := by omega
      have hchoose := Nat.choose_mul (n := q) (k := d) (s := k) hkd
      have hpfac := Nat.choose_mul_factorial_mul_factorial hkp
      simp only [ite_eq_left hrpk]
      rw [show p - k - r = d - k by dsimp [d]; omega]
      have hchooseZ := congrArg (fun x : ℕ => (x : ℤ)) hchoose
      have hpfacZ := congrArg (fun x : ℕ => (x : ℤ)) hpfac
      push_cast at hchooseZ hpfacZ
      calc
        _ = ((-1 : ℤ) ^ k) * (s.factorial : ℤ) *
            ((Nat.choose p k : ℤ) * (k.factorial : ℤ) *
              ((p - k).factorial : ℤ)) *
            ((Nat.choose q k : ℤ) *
              (Nat.choose (q - k) (d - k) : ℤ)) := by ring
        _ = ((-1 : ℤ) ^ k) * (s.factorial : ℤ) *
            (p.factorial : ℤ) *
            ((Nat.choose q d : ℤ) * (Nat.choose d k : ℤ)) := by
              rw [hpfacZ, ← hchooseZ]
        _ = _ := by ring
    rw [Finset.sum_congr rfl hterm]
    rw [show (∑ k ∈ Finset.range (d + 1),
        (p.factorial : ℤ) * (s.factorial : ℤ) * (Nat.choose q d : ℤ) *
          (((-1 : ℤ) ^ k) * (Nat.choose d k : ℤ))) =
        (p.factorial : ℤ) * (s.factorial : ℤ) * (Nat.choose q d : ℤ) *
          ∑ k ∈ Finset.range (d + 1),
            (((-1 : ℤ) ^ k) * (Nat.choose d k : ℤ)) by
      simp_rw [Finset.mul_sum]
      ]
    rw [Int.alternating_sum_range_choose]
    by_cases hpr : p = r
    · subst r
      have hs : s = q := by omega
      subst s
      simp [d]
    · have hd0 : d ≠ 0 := by omega
      simp [hpr, hd0]
  · have hpr : p ≠ r := by omega
    rw [ite_eq_right hpr]
    apply Finset.sum_eq_zero
    intro k hk
    have hnot : ¬r ≤ p - k := by omega
    simp [hnot]

/-- Evaluation of the finite moment sum before applying the square-root
normalization factors. -/
theorem hermiteInnerMomentSum_eq (n p q r s : ℕ) :
    hermiteInnerMomentSum n p q r s =
      if p = r ∧ q = s then
        (p.factorial : ℂ) * (q.factorial : ℂ) *
          ((n : ℂ)⁻¹) ^ (p + q)
      else 0 := by
  by_cases hbal : p + s = q + r
  · unfold hermiteInnerMomentSum diagonalRawCoeff
    rw [show (∑ k ∈ Finset.range (min p q + 1),
        ∑ l ∈ Finset.range (min r s + 1),
          conj ((-((n : ℝ)⁻¹ : ℂ)) ^ k * (k.factorial : ℂ) *
              (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
            ((-((n : ℝ)⁻¹ : ℂ)) ^ l * (l.factorial : ℂ) *
              (Nat.choose r l : ℂ) * (Nat.choose s l : ℂ)) *
            (if q - k + (r - l) = p - k + (s - l) then
              ((q - k + (r - l)).factorial : ℂ) *
                (n : ℂ)⁻¹ ^ (q - k + (r - l))
            else 0)) =
        ((n : ℂ)⁻¹) ^ (q + r) *
          ∑ k ∈ Finset.range (min p q + 1),
            ((-1 : ℂ) ^ k) * (Nat.choose p k : ℂ) *
              (Nat.choose q k : ℂ) * (k.factorial : ℂ) *
              (∑ l ∈ Finset.range (min r s + 1),
                ((-1 : ℂ) ^ l) * (Nat.choose r l : ℂ) *
                  (Nat.choose s l : ℂ) * (l.factorial : ℂ) *
                    ((q - k + (r - l)).factorial : ℂ)) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkp : k ≤ p := (le_min_iff.mp
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).1
      have hkq : k ≤ q := (le_min_iff.mp
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).2
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      have hlr : l ≤ r := (le_min_iff.mp
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))).1
      have hls : l ≤ s := (le_min_iff.mp
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))).2
      have heq : q - k + (r - l) = p - k + (s - l) := by omega
      simp only [ite_eq_left heq, map_mul, map_pow,
        Complex.conj_natCast, Complex.conj_ofReal, map_neg, map_inv₀]
      have hexp : k + l + (q - k + (r - l)) = q + r := by omega
      rw [show (((n : ℝ)⁻¹ : ℂ)) = (n : ℂ)⁻¹ by push_cast; rfl]
      have hpows :
          (-(n : ℂ)⁻¹) ^ k * (-(n : ℂ)⁻¹) ^ l *
              (n : ℂ)⁻¹ ^ (q - k + (r - l)) =
            (-1 : ℂ) ^ k * (-1 : ℂ) ^ l * (n : ℂ)⁻¹ ^ (q + r) := by
        have hnexp :
            (n : ℂ)⁻¹ ^ k * (n : ℂ)⁻¹ ^ l *
                (n : ℂ)⁻¹ ^ (q - k + (r - l)) =
              (n : ℂ)⁻¹ ^ (q + r) := by
          rw [← pow_add, ← pow_add]
          congr 1
        rw [neg_pow, neg_pow]
        calc
          _ = ((n : ℂ)⁻¹ ^ k * (n : ℂ)⁻¹ ^ l *
                (n : ℂ)⁻¹ ^ (q - k + (r - l))) *
                (-1 : ℂ) ^ k * (-1 : ℂ) ^ l := by ring
          _ = _ := by rw [hnexp]; ring
      calc
        _ = ((-(n : ℂ)⁻¹) ^ k * (-(n : ℂ)⁻¹) ^ l *
              (n : ℂ)⁻¹ ^ (q - k + (r - l))) *
              (k.factorial : ℂ) * (Nat.choose p k : ℂ) *
              (Nat.choose q k : ℂ) * (l.factorial : ℂ) *
              (Nat.choose r l : ℂ) * (Nat.choose s l : ℂ) *
              ((q - k + (r - l)).factorial : ℂ) := by ring
        _ = _ := by rw [hpows]; ring]
    have hinner : ∀ k ∈ Finset.range (min p q + 1),
        (∑ l ∈ Finset.range (min r s + 1),
          ((-1 : ℂ) ^ l) * (Nat.choose r l : ℂ) *
            (Nat.choose s l : ℂ) * (l.factorial : ℂ) *
              ((q - k + (r - l)).factorial : ℂ)) =
          (s.factorial : ℂ) * ((p - k).factorial : ℂ) *
            (if r ≤ p - k then
              (Nat.choose (q - k) (p - k - r) : ℂ) else 0) := by
      intro k hk
      have hkp : k ≤ p := (le_min_iff.mp
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).1
      have hkq : k ≤ q := (le_min_iff.mp
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).2
      exact_mod_cast inner_hermite_alternating p q r s k hbal hkp hkq
    rw [Finset.sum_congr rfl (fun k hk => by rw [hinner k hk])]
    have houter := outer_hermite_alternating p q r s hbal
    have houterC := congrArg (fun z : ℤ => (z : ℂ)) houter
    push_cast at houterC
    have hsum :
        (∑ k ∈ Finset.range (min p q + 1),
          ((-1 : ℂ) ^ k) * (Nat.choose p k : ℂ) *
            (Nat.choose q k : ℂ) * (k.factorial : ℂ) *
            ((s.factorial : ℂ) * ((p - k).factorial : ℂ) *
              (if r ≤ p - k then
                (Nat.choose (q - k) (p - k - r) : ℂ) else 0))) =
          if p = r then (p.factorial : ℂ) * (q.factorial : ℂ) else 0 := by
      calc
        _ = ∑ k ∈ Finset.range (min p q + 1),
            ((-1 : ℂ) ^ k) * (Nat.choose p k : ℂ) *
              (Nat.choose q k : ℂ) * (k.factorial : ℂ) *
              (s.factorial : ℂ) * ((p - k).factorial : ℂ) *
                (if r ≤ p - k then
                  (Nat.choose (q - k) (p - k - r) : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
        _ = _ := houterC
    rw [hsum]
    by_cases hpr : p = r
    · subst r
      have hqs : q = s := by omega
      subst s
      simp
      ring
    · have hqs : ¬(p = r ∧ q = s) := by simp [hpr]
      simp [hpr]
  · unfold hermiteInnerMomentSum
    have hdelta : ¬(p = r ∧ q = s) := by
      rintro ⟨rfl, rfl⟩
      exact hbal (Nat.add_comm _ _)
    rw [ite_eq_right hdelta]
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro l hl
    have hkp : k ≤ p := (le_min_iff.mp
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).1
    have hkq : k ≤ q := (le_min_iff.mp
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).2
    have hlr : l ≤ r := (le_min_iff.mp
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))).1
    have hls : l ≤ s := (le_min_iff.mp
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))).2
    have hne : q - k + (r - l) ≠ p - k + (s - l) := by omega
    simp [hne]

private theorem oneDimNormalization_square_mul (n p : ℕ) (hn : 0 < n) :
    (oneDimNormalization n p) ^ 2 * (p.factorial : ℝ) *
        ((n : ℝ)⁻¹) ^ p = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsqrtfac : Real.sqrt (p.factorial : ℝ) ≠ 0 := by positivity
  have hsqrtn : Real.sqrt (n : ℝ) ^ 2 = n := by
    rw [sq, Real.mul_self_sqrt]
    positivity
  have hsqrtfac_sq : Real.sqrt (p.factorial : ℝ) ^ 2 = p.factorial := by
    rw [sq, Real.mul_self_sqrt]
    positivity
  unfold oneDimNormalization
  rw [div_pow]
  rw [← pow_mul, mul_comm p 2, pow_mul, hsqrtn, hsqrtfac_sq]
  field_simp
  rw [← mul_pow]
  field_simp
  norm_num

/-- The mixed-moment formula implies exact orthonormality of the normalized
one-coordinate complex Hermite system. -/
theorem normalizedEval_orthogonal_of_mixedMoments
    (n : ℕ) (hn : 0 < n) (hMom : MixedMomentFormula n)
    (p q r s : ℕ) :
    ∫ z : ℂ, conj (normalizedEval n hn p q z) *
        normalizedEval n hn r s z
      ∂(complexCoordinateGaussianProbability n : MeasureTheory.Measure ℂ) =
      if p = r ∧ q = s then 1 else 0 := by
  rw [normalizedEval_inner_eq_momentSum_of_mixedMoments n hn hMom,
    hermiteInnerMomentSum_eq]
  by_cases h : p = r ∧ q = s
  · rcases h with ⟨rfl, rfl⟩
    simp only [Complex.ofReal_mul, and_self, ↓reduceIte, inv_pow]
    have hp := oneDimNormalization_square_mul n p hn
    have hq := oneDimNormalization_square_mul n q hn
    have hpC :
        (oneDimNormalization n p : ℂ) ^ 2 * (p.factorial : ℂ) *
            ((n : ℂ)⁻¹) ^ p = 1 := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
        Complex.ofReal_natCast, Complex.ofReal_one] using
          congrArg (fun x : ℝ => (x : ℂ)) hp
    have hqC :
        (oneDimNormalization n q : ℂ) ^ 2 * (q.factorial : ℂ) *
            ((n : ℂ)⁻¹) ^ q = 1 := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
        Complex.ofReal_natCast, Complex.ofReal_one] using
          congrArg (fun x : ℝ => (x : ℂ)) hq
    calc
      _ = ((oneDimNormalization n p : ℂ) ^ 2 * (p.factorial : ℂ) *
            ((n : ℂ)⁻¹) ^ p) *
          ((oneDimNormalization n q : ℂ) ^ 2 * (q.factorial : ℂ) *
            ((n : ℂ)⁻¹) ^ q) := by rw [pow_add]; ring
      _ = 1 := by rw [hpC, hqC]; norm_num
  · simp [h]

/-- Exact multivariate orthonormality follows from the coordinate mixed
moments and the previously established product-measure factorization. -/
theorem multivariate_orthogonality_of_mixedMoments
    (n : ℕ) (hn : 0 < n) (hMom : MixedMomentFormula n)
    (p q r s : Fin n → ℕ) :
    ∫ z, conj (multivariateNormalized n hn p q z) *
        multivariateNormalized n hn r s z ∂complexGaussianMeasure n =
      if p = r ∧ q = s then 1 else 0 :=
  multivariate_orthogonality_of_oneCoordinate n hn
    (normalizedEval_orthogonal_of_mixedMoments n hn hMom) p q r s

end ComplexHermite
end GinibrePoincare
