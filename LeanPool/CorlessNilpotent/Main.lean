/-
Copyright (c) 2026 Marcel Blattner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Blattner
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import LeanPool.CorlessNilpotent.Parity

/-!
# Modulo 4 the condition `D = 1` forces the folded shape, and the classification follows
-/

@[expose] public section

open Polynomial Finset

namespace Corless

/-! ### Telescoping between two sign sequences -/

/-- `s` before position `j`, `t` from position `j` on. -/
def hyb (s t : ℕ → ℤ) (j : ℕ) : ℕ → ℤ := fun i => if i < j then s i else t i

lemma IsSign.hyb {s t : ℕ → ℤ} (hs : IsSign s) (ht : IsSign t) (j : ℕ) : IsSign (hyb s t j) :=
  fun i => by unfold Corless.hyb; split_ifs; exacts [hs i, ht i]

lemma IsSign.shift {s : ℕ → ℤ} (hs : IsSign s) (k : ℕ) : IsSign (fun i => s (i + k)) :=
  fun i => hs (i + k)

/-- Changing the weight of edge `j` changes `D` by `(new - old) · X · D(left) · D(right)`. -/
lemma Dv_hyb_step (s t : ℕ → ℤ) (j m : ℕ) :
    Dv (hyb s t (j + 1)) (j + m + 2) - Dv (hyb s t j) (j + m + 2)
      = C (s j - t j) * X * Dv (hyb s t j) j * Dv (fun i => hyb s t j (i + j + 2)) m := by
  rw [Dv_split (hyb s t (j + 1)) j m, Dv_split (hyb s t j) j m]
  have e1 : Dv (hyb s t (j + 1)) (j + 1) = Dv (hyb s t j) (j + 1) :=
    Dv_congr fun i hi => by simp [hyb, show i < j by omega, show i < j + 1 by omega]
  have e2 : Dv (hyb s t (j + 1)) j = Dv (hyb s t j) j :=
    Dv_congr fun i hi => by simp [hyb, show i < j by omega, show i < j + 1 by omega]
  have e3 : Dv (fun i => hyb s t (j + 1) (i + j + 1)) (m + 1)
      = Dv (fun i => hyb s t j (i + j + 1)) (m + 1) :=
    Dv_congr fun i _ => by simp only [hyb]; split_ifs <;> first | rfl | omega
  have e4 : Dv (fun i => hyb s t (j + 1) (i + j + 2)) m = Dv (fun i => hyb s t j (i + j + 2)) m :=
    Dv_congr fun i _ => by simp only [hyb]; split_ifs <;> first | rfl | omega
  have e5 : hyb s t (j + 1) j = s j := by simp [hyb]
  have e6 : hyb s t j j = t j := by simp [hyb]
  rw [e1, e2, e3, e4, e5, e6, C_sub]
  ring

/-- Exact telescoping over the edges of a path with `M` vertices. -/
lemma Dv_sub_eq (s t : ℕ → ℤ) (M : ℕ) :
    Dv s M - Dv t M = ∑ j ∈ range (M - 1),
      C (s j - t j) * X * Dv (hyb s t j) j * Dv (fun i => hyb s t j (i + j + 2)) (M - 2 - j) := by
  have hs : Dv s M = Dv (hyb s t (M - 1)) M :=
    Dv_congr fun i hi => by simp [hyb, show i < M - 1 by omega]
  have ht : Dv t M = Dv (hyb s t 0) M := Dv_congr fun i _ => by simp [hyb]
  rw [hs, ht, ← Finset.sum_range_sub (fun j => Dv (hyb s t j) M)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have := Dv_hyb_step s t j (M - 2 - j)
  rwa [show j + (M - 2 - j) + 2 = M by omega] at this

/-- Modulo 4, the difference only sees which signs differ: with `s j - t j = 2 δ j`,
`D s - D t ≡ 2 ∑ δ j · X · f j · f (M - 2 - j)`. -/
lemma Dv_sub_mod4 {s t : ℕ → ℤ} (hs : IsSign s) (ht : IsSign t) (δ : ℕ → ℤ)
    (hδ : ∀ j, s j - t j = 2 * δ j) (M : ℕ) :
    ∃ R : ℤ[X], Dv s M - Dv t M
      = 2 * ∑ j ∈ range (M - 1), C (δ j) * X * f j * f (M - 2 - j) + 4 * R := by
  rw [Dv_sub_eq]
  have key : ∀ j, ∃ R : ℤ[X],
      C (s j - t j) * X * Dv (hyb s t j) j * Dv (fun i => hyb s t j (i + j + 2)) (M - 2 - j)
        = 2 * (C (δ j) * X * f j * f (M - 2 - j)) + 4 * R := by
    intro j
    obtain ⟨A, hA⟩ := Dv_parity (hs.hyb ht j) j
    obtain ⟨B, hB⟩ := Dv_parity ((hs.hyb ht j).shift (j + 2)) (M - 2 - j)
    refine ⟨C (δ j) * X * (A * f (M - 2 - j) + f j * B + 2 * A * B), ?_⟩
    have hB' : Dv (fun i => hyb s t j (i + j + 2)) (M - 2 - j) = f (M - 2 - j) + 2 * B := by
      rw [← hB]
      congr 1
    rw [hA, hB', hδ, C_mul, show (C (2 : ℤ) : ℤ[X]) = 2 by simp]
    ring
  choose R hR using key
  refine ⟨∑ j ∈ range (M - 1), R j, ?_⟩
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => hR j

/-! ### Independence over 𝔽₂ -/

lemma coeff_P_zero (N j : ℕ) (hj : j < N) :
    (((1 + X : (ZMod 2)[X]) ^ (j + 1) + X ^ (j + 1))
      * ((1 + X) ^ (2 * N - j) + X ^ (2 * N - j))).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_mul]
  have hright : 2 * N - j ≠ 0 := by omega
  simp [hright]

lemma coeff_P_succ (N j i : ℕ) (hj : j < N) (hi : i < N) :
    (((1 + X : (ZMod 2)[X]) ^ (j + 1) + X ^ (j + 1))
      * ((1 + X) ^ (2 * N - j) + X ^ (2 * N - j))).coeff (i + 1)
      = ((2 * N + 1).choose (i + 1) : ZMod 2)
        + if j ≤ i then ((2 * N - j).choose (i - j) : ZMod 2) else 0 := by
  have h : ((1 + X : (ZMod 2)[X]) ^ (j + 1) + X ^ (j + 1))
      * ((1 + X) ^ (2 * N - j) + X ^ (2 * N - j))
      = (1 + X) ^ (2 * N + 1) + X ^ (j + 1) * (1 + X) ^ (2 * N - j)
        + X ^ (2 * N - j) * (1 + X) ^ (j + 1) + X ^ (2 * N + 1) := by
    rw [show 2 * N + 1 = (j + 1) + (2 * N - j) by omega, pow_add, pow_add]
    ring
  rw [h]
  simp only [coeff_add, coeff_one_add_X_pow, coeff_X_pow_mul', coeff_X_pow]
  have h1 : ¬ (2 * N - j ≤ i + 1) := by omega
  have h2 : i ≠ 2 * N := by omega
  by_cases hji : j ≤ i
  · have h3 : j + 1 ≤ i + 1 := by omega
    simp [h1, h2, hji, h3, show i + 1 - (j + 1) = i - j by omega]
  · have h3 : ¬ (j + 1 ≤ i + 1) := by omega
    simp [h1, h2, hji, h3]

/-- Lemma 3 (independence): the polynomials `fbar j * fbar (2N - 1 - j)`, `j < N`, are linearly
independent over 𝔽₂. -/
lemma indep (N : ℕ) (w : ℕ → ZMod 2)
    (h : ∑ j ∈ range N, C (w j) * (fbar j * fbar (2 * N - 1 - j)) = 0) : ∀ j < N, w j = 0 := by
  -- substitute x = y + y²
  have hc := congrArg (fun p => p.comp (X + X ^ 2 : (ZMod 2)[X])) h
  simp only [zero_comp] at hc
  rw [Polynomial.sum_comp] at hc
  have hterm : ∀ j ∈ range N, (C (w j) * (fbar j * fbar (2 * N - 1 - j))).comp (X + X ^ 2)
      = C (w j) * (((1 + X) ^ (j + 1) + X ^ (j + 1))
        * ((1 + X) ^ (2 * N - j) + X ^ (2 * N - j))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mul_comp, C_comp, mul_comp, fbar_comp, fbar_comp,
      show 2 * N - 1 - j + 1 = 2 * N - j by omega]
  rw [Finset.sum_congr rfl hterm] at hc
  -- the constant coefficient: ∑ w j = 0
  have hsum : ∑ j ∈ range N, w j = 0 := by
    have := congrArg (fun p : (ZMod 2)[X] => p.coeff 0) hc
    simp only [finsetSum_coeff, coeff_C_mul, coeff_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j hj => by
      rw [coeff_P_zero N j (Finset.mem_range.mp hj), mul_one]
  -- the coefficient of y^(i+1) kills w i, by strong induction
  intro i hi
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have := congrArg (fun p : (ZMod 2)[X] => p.coeff (i + 1)) hc
    simp only [finsetSum_coeff, coeff_C_mul, coeff_zero] at this
    rw [Finset.sum_congr rfl fun j hj => by
      rw [coeff_P_succ N j i (Finset.mem_range.mp hj) hi]] at this
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul, zero_add] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro j hj hji
      by_cases hle : j ≤ i
      · rw [ih j (by omega) (by omega), zero_mul]
      · simp [hle]
    · intro hi'
      exact absurd (Finset.mem_range.mpr hi) hi'

/-! ### Modulo 4 forces the folded shape -/

/-- Lemma 4. On a path with `2^(k+2) - 1` vertices, `D ≡ 1 (mod 4)` forces the two middle signs to
be opposite and the two halves to be mirror images. -/
theorem fold_of_mod4 (k : ℕ) {s : ℕ → ℤ} (hs : IsSign s)
    (h : ∃ R : ℤ[X], Dv s (2 ^ (k + 2) - 1) = 1 + 4 * R) :
    s (2 ^ (k + 1) - 1) = -s (2 ^ (k + 1) - 2) ∧
      ∀ i < 2 ^ (k + 1) - 2, s (2 * (2 ^ (k + 1) - 1) - 1 - i) = s i := by
  set n := 2 ^ (k + 1) - 2
  obtain ⟨hN, hM⟩ : 2 ^ (k + 1) - 1 = n + 1 ∧ 2 ^ (k + 2) - 1 = 2 * n + 3 :=
    folded_sizes k
  rw [hN, show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  rw [hM] at h
  obtain ⟨R, hR⟩ := h
  -- D(star) ≡ 1 (mod 4)
  obtain ⟨A, hA⟩ := f_pow_two k
  rw [hN] at hA
  have hstar : Dv (star n) (2 * n + 3) = 1 + 4 * (A + A ^ 2) := by
    rw [Dv_star, hA]; ring
  -- the halved differences
  let δ : ℕ → ℤ := fun j => (s j - star n j) / 2
  have hδ : ∀ j, s j - star n j = 2 * δ j := by
    intro j
    simp only [δ]
    by_cases h2 : j = n + 1
    · subst h2
      rcases hs (n + 1) with h1 | h1 <;> simp [star, h1]
    · rcases hs j with h1 | h1 <;> simp [star, h1, h2]
  obtain ⟨R', hR'⟩ := Dv_sub_mod4 hs (isSign_star n) δ hδ (2 * n + 3)
  rw [hR, hstar, show 2 * n + 3 - 1 = 2 * (n + 1) by omega] at hR'
  -- divide by 2 and reduce modulo 2
  have hsum2 : ∑ j ∈ range (2 * (n + 1)), C (δ j) * X * f j * f (2 * n + 3 - 2 - j)
      = 2 * (R - (A + A ^ 2) - R') := by
    have h2 : (2 : ℤ[X]) * (∑ j ∈ range (2 * (n + 1)), C (δ j) * X * f j * f (2 * n + 3 - 2 - j)
        - 2 * (R - (A + A ^ 2) - R')) = 0 := by
      linear_combination -hR'
    rcases mul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 two_ne_zero
    · exact sub_eq_zero.mp h2
  have hbar := congrArg (Polynomial.map (Int.castRingHom (ZMod 2))) hsum2
  rw [Polynomial.map_mul, show Polynomial.map (Int.castRingHom (ZMod 2)) (2 : ℤ[X]) = 2 by simp,
    two_eq_zero_Z2X, zero_mul, Polynomial.map_sum] at hbar
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X] at hbar
  set w : ℕ → ZMod 2 := fun j => Int.castRingHom (ZMod 2) (δ j) with hw
  change ∑ j ∈ range (2 * (n + 1)), C (w j) * X * fbar j * fbar (2 * n + 3 - 2 - j) = 0 at hbar
  -- pair j with 2N - 1 - j
  rw [two_mul, Finset.sum_range_add] at hbar
  rw [← Finset.sum_range_reflect (fun j => C (w (n + 1 + j)) * X * fbar (n + 1 + j)
    * fbar (2 * n + 3 - 2 - (n + 1 + j))) (n + 1)] at hbar
  rw [← Finset.sum_add_distrib] at hbar
  have hpair : ∑ j ∈ range (n + 1),
      C (w j + w (2 * n + 1 - j)) * (fbar j * fbar (2 * (n + 1) - 1 - j)) = 0 := by
    have hX : (X : (ZMod 2)[X]) * ∑ j ∈ range (n + 1),
        C (w j + w (2 * n + 1 - j)) * (fbar j * fbar (2 * (n + 1) - 1 - j)) = 0 := by
      rw [← hbar, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show n + 1 + (n + 1 - 1 - j) = 2 * n + 1 - j by omega,
        show 2 * n + 3 - 2 - (2 * n + 1 - j) = j by omega,
        show 2 * n + 3 - 2 - j = 2 * n + 1 - j by omega,
        show 2 * (n + 1) - 1 - j = 2 * n + 1 - j by omega, C_add]
      ring
    rcases mul_eq_zero.mp hX with h0 | h0
    · exact absurd h0 X_ne_zero
    · exact h0
  have hw0 := indep (n + 1) (fun j => w j + w (2 * n + 1 - j)) hpair
  -- read off the signs: w j = 1 exactly where s differs from the reference sequence
  constructor
  · -- middle: j = n, partner 2n + 1 - n = n + 1
    have h0 := hw0 n (by omega)
    rw [show 2 * n + 1 - n = n + 1 by omega] at h0
    rcases hs n with h1 | h1 <;> rcases hs (n + 1) with h2 | h2 <;>
      simp [hw, δ, star, h1, h2] at h0 ⊢
  · intro i hi
    have h0 := hw0 i (by omega)
    have hi1 : i ≠ n + 1 := by omega
    have hi2 : 2 * n + 1 - i ≠ n + 1 := by omega
    rcases hs i with h1 | h1 <;> rcases hs (2 * n + 1 - i) with h2 | h2 <;>
      simp [hw, δ, star, hi1, hi2, h1, h2] at h0 ⊢

/-! ### The classification -/

lemma Dv_coeff_zero (s : ℕ → ℤ) : ∀ j, (Dv s j).coeff 0 = 1
  | 0 => by simp
  | 1 => by simp
  | j + 2 => by
      rw [Dv_succ_succ, coeff_add, Dv_coeff_zero s (j + 1), mul_assoc, coeff_C_mul,
        coeff_X_mul_zero]
      simp

lemma eq_one_of_sq {p : ℤ[X]} (h : p ^ 2 = 1) (h0 : p.coeff 0 = 1) : p = 1 := by
  have : (p - 1) * (p + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact sub_eq_zero.mp h1
  · have := congrArg (fun q => q.coeff 0) h1
    simp [h0] at this

/-- Corless's family at dimension `2^(k+1) - 1`, as a property of the first `2^(k+1) - 2` signs. -/
def Fam : ℕ → (ℕ → ℤ) → Prop
  | 0, _ => True
  | k + 1, s => s (2 ^ (k + 1) - 1) = -s (2 ^ (k + 1) - 2) ∧
      (∀ i < 2 ^ (k + 1) - 2, s (2 * (2 ^ (k + 1) - 1) - 1 - i) = s i) ∧ Fam k s

lemma fold_eq {k : ℕ} {s : ℕ → ℤ} (hmid : s (2 ^ (k + 1) - 1) = -s (2 ^ (k + 1) - 2))
    (hmir : ∀ i < 2 ^ (k + 1) - 2, s (2 * (2 ^ (k + 1) - 1) - 1 - i) = s i) :
    Dv s (2 ^ (k + 2) - 1) = Dv s (2 ^ (k + 1) - 1) ^ 2 := by
  set n := 2 ^ (k + 1) - 2
  obtain ⟨hN, hM⟩ : 2 ^ (k + 1) - 1 = n + 1 ∧ 2 ^ (k + 2) - 1 = 2 * n + 3 :=
    folded_sizes k
  rw [hM, hN]
  rw [hN] at hmid hmir
  exact Dv_fold s n hmid fun i hi => by
    have := hmir i hi
    rwa [show 2 * (n + 1) - 1 - i = 2 * n + 1 - i by omega] at this

lemma one_of_fam {s : ℕ → ℤ} : ∀ k, Fam k s → Dv s (2 ^ (k + 1) - 1) = 1
  | 0, _ => by simp
  | k + 1, ⟨hmid, hmir, hk⟩ => by
      rw [fold_eq hmid hmir, one_of_fam k hk, one_pow]

lemma fam_of_one {s : ℕ → ℤ} (hs : IsSign s) : ∀ k, Dv s (2 ^ (k + 1) - 1) = 1 → Fam k s
  | 0, _ => trivial
  | k + 1, h => by
      obtain ⟨hmid, hmir⟩ := fold_of_mod4 k hs ⟨0, by rw [h]; ring⟩
      refine ⟨hmid, hmir, fam_of_one hs k ?_⟩
      apply eq_one_of_sq _ (Dv_coeff_zero s _)
      rw [← fold_eq hmid hmir, h]

/-- **Corless's conjecture.** For a sign sequence `s`, the weighted path with `m ≥ 1` vertices has
`D = 1` (equivalently: the skew-symmetric tridiagonal matrix with superdiagonal `u`, `u² = s`, is
nilpotent) exactly when `m = 2^(k+1) - 1` and the signs form one of Corless's sequences. -/
theorem corless {s : ℕ → ℤ} (hs : IsSign s) {m : ℕ} (hm : 1 ≤ m) :
    Dv s m = 1 ↔ ∃ k, m = 2 ^ (k + 1) - 1 ∧ Fam k s := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := dimension hs hm h
    exact ⟨k, rfl, fam_of_one hs k h⟩
  · rintro ⟨k, rfl, hk⟩
    exact one_of_fam k hk

end Corless
