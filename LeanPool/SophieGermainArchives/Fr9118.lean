/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Data.Int.Interval
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.FLT.Three
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Ring

/-!
# Français 9118: the drafts to Gauss, reading notes, the lever, the centroid, Legendre's notes

Adapted from `lean/Germain/Fr9118.lean` of
https://github.com/Commutator-IO/germain-project
at commit `167c171` (CC0, same author).

The arithmetic of the drafts to Gauss, three reading notes, the lever, the centre of gravity of
a triangle, and two notes of Legendre on Euler's lamina.

The modernised reading `transcripts/fr-9118/fr-9118.modern.tex` makes a number of precise
mathematical statements about the leaves of this volume. This file proves those that can be
stated without the lost enclosures.

* « L'arithmétique : les deux brouillons à Gauss » (views 43–46).
  - `art357_three`, `art357_five`, `art357_seven`: `4 Φ_p = Y² − p* Z²` for `p = 3, 5, 7`.
  - `generalisation`: if `4 (Xⁿ − 1)/(X − 1) = Y² − c Z²` in `ℤ[X]` with `c` odd, then for
    every `s` there are `Y_s, Z_s ∈ ℤ[X]` with `4 (X^{n^s} − 1)/(X − 1) = Y_s² − c Z_s²`.
    This is Germain's generalisation of art. 357, deduced from art. 357 as the reading does
    (factorisation, then composition with the parity argument). Neither `n` prime nor `c = ±n`
    is used. `generalisation_three`, `_five`, `_seven` make it unconditional for `n = 3, 5, 7`.
  - `passage_neg`: the passage from `Y, Z` to `Y', Z'` is `x ↦ −x` (`n` odd), with
    `coeff_comp_neg_X` (change the sign of odd-degree terms); `not_dvd_of_even` shows that
    `n` odd cannot be dropped.
  - `fermat_first_case`, `mod_eight_seven`, `seven_mod_eight_iff`, `flt_of_three_dvd`,
    `first_primes_seven_mod_eight`: on Fermat's equation for `n = p − 1`, `p ≡ 7 (mod 8)`.
  - `det_adjugate_fin`, `gauss_ternary_adjoint`, `radical_of_det_eq_zero`: the determinant of
    the adjoint, and the radical of a form of determinant zero.
* « Trois notes de lecture d'arithmétique » (views 91–93).
  - `p4_add_four_reps`, `p4_add_four_prime_iff`, `same_pair_iff`; Sophie Germain's identity
    itself is Mathlib's `pow_four_add_four_mul_pow_four'`.
  - `p4_add_q4_identities`, `fermat_number_eq`, `three_five_not_sum_fourth`,
    `seventeen_unique`, `two_fifty_seven_unique`, `x_sq_sub_two_y_sq_not_unique`,
    `pell_step`.
  - Composition of binary forms (Gauss's `(a, b, c)` is `ax² + 2bxy + cy²`, here the modern
    `(a, 2b, c)`): `dirichlet_identity`, `composite_one`, `composite_two`, `composite_three`,
    `composite_four`, `opposite_equiv`, `not_equiv_8_13`, `reduced_forms_295`.
* « Le levier, l'infini et l'hyperbole » (views 40–42): `indeterminate_product`,
  `indeterminate_quotient`.
* « Le centre de gravité du triangle » (views 91, 98, 99): `centroid_equation`,
  `centroid_decomposition`, `centroid_on_median`, `small_centroid_homothety`.
* Legendre's note « Pag. 155 » (views 63–64): `parasite_root`, `parasite_H_ne_zero`,
  `euler_large_omega`, `eps_tendsto_zero`, `lambda_third`.
* Legendre's lamina test (view 54): `indep_of_deriv_zero`.

Not formalised: art. 357 itself for general `p` (Gauss sums), the Lagrange quantity of 1775
(the two copies on the leaf disagree), Euler's theorem on two representations as sums of two
squares, the uniqueness of `x² + 2y²` for all primes, the well-definedness of composition on
classes and the class number `8`, the limits of the parasite-root discussion, and anything that
needs Euler's text.
-/

@[expose] public section

namespace LeanPool.SophieGermainArchives.Fr9118

open Polynomial Filter Topology

/-! ## Article 357 and the generalisation -/

/-- `G m = ∑_{i<m} Xⁱ = (X^m − 1)/(X − 1)` in `ℤ[X]`. -/
noncomputable def G (m : ℕ) : ℤ[X] := ∑ i ∈ Finset.range m, X ^ i

lemma X_sub_one_mul_G (m : ℕ) : (X - 1) * G m = X ^ m - 1 := mul_geom_sum X m

lemma G_prime (p : ℕ) [Fact p.Prime] : G p = cyclotomic p ℤ := by
  rw [cyclotomic_prime]; rfl

theorem art357_three : 4 * G 3 = (2 * X + 1) ^ 2 - C (-3) * 1 ^ 2 := by
  simp [G, Finset.sum_range_succ]; ring

theorem art357_five : 4 * G 5 = (2 * X ^ 2 + X + 2) ^ 2 - C 5 * X ^ 2 := by
  simp [G, Finset.sum_range_succ]; ring

theorem art357_seven :
    4 * G 7 = (2 * X ^ 3 + X ^ 2 - X - 2) ^ 2 - C (-7) * (X ^ 2 + X) ^ 2 := by
  simp [G, Finset.sum_range_succ]; ring

lemma X_sub_one_ne_zero : (X - 1 : ℤ[X]) ≠ 0 := by
  simpa using X_sub_C_ne_zero (1 : ℤ)

/-- `(X^{ab} − 1)/(X − 1) = (X^a − 1)/(X − 1) · Φ(X^a)` with `Φ = (X^b − 1)/(X − 1)`. -/
lemma G_mul (a b : ℕ) : G (a * b) = G a * expand ℤ a (G b) := by
  apply mul_left_cancel₀ X_sub_one_ne_zero
  have h := congrArg (expand ℤ a) (X_sub_one_mul_G b)
  simp only [map_mul, map_sub, map_one, map_pow, expand_X] at h
  rw [X_sub_one_mul_G, ← mul_assoc, X_sub_one_mul_G, h, pow_mul]

lemma two_eq_zero_zmod2X : (2 : (ZMod 2)[X]) = 0 := by
  rw [← map_ofNat C 2, show (2 : ZMod 2) = 0 from rfl, C_0]

/-- Parity: if `4 A = Y² − c Z²` with `c` odd, then `Y ≡ Z (mod 2)` coefficientwise. -/
lemma parity (A Y Z k : ℤ[X]) (h : 4 * A = Y ^ 2 - (2 * k + 1) * Z ^ 2) :
    ∃ W, Y = Z + 2 * W := by
  let φ := mapRingHom (Int.castRingHom (ZMod 2))
  have h2 := two_eq_zero_zmod2X
  have hφ : φ (Y - Z) ^ 2 = 0 := by
    have := congrArg φ h
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_ofNat] at this
    rw [map_sub]
    linear_combination (-1 : (ZMod 2)[X]) * this +
      (-(φ Y * φ Z) + φ Z ^ 2 + φ k * φ Z ^ 2 + 2 * φ A) * h2
  have hmem : Y - Z ∈ RingHom.ker φ := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hφ
  rw [ker_mapRingHom, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hmem
  obtain ⟨W, hW⟩ := hmem
  exact ⟨W, by rw [← sub_eq_iff_eq_add', hW]; simp⟩

/-- Composition: `4A = Y₁² − cZ₁²` and `4B = Y₂² − cZ₂²` with `c` odd give `4AB = Y² − cZ²`. -/
lemma compose (A B Y₁ Z₁ Y₂ Z₂ k : ℤ[X])
    (h₁ : 4 * A = Y₁ ^ 2 - (2 * k + 1) * Z₁ ^ 2) (h₂ : 4 * B = Y₂ ^ 2 - (2 * k + 1) * Z₂ ^ 2) :
    ∃ Y Z, 4 * (A * B) = Y ^ 2 - (2 * k + 1) * Z ^ 2 := by
  obtain ⟨W₁, rfl⟩ := parity A Y₁ Z₁ k h₁
  obtain ⟨W₂, rfl⟩ := parity B Y₂ Z₂ k h₂
  refine ⟨Z₁ * Z₂ * (k + 1) + W₁ * Z₂ + Z₁ * W₂ + 2 * W₁ * W₂, Z₁ * Z₂ + W₁ * Z₂ + Z₁ * W₂, ?_⟩
  apply mul_left_cancel₀ (show (4 : ℤ[X]) ≠ 0 by
    rw [show (4 : ℤ[X]) = C 4 by simp]; exact C_ne_zero.mpr (by norm_num))
  linear_combination (4 * A) * h₂ + ((Z₂ + 2 * W₂) ^ 2 - (2 * k + 1) * Z₂ ^ 2) * h₁

/-- **Germain's generalisation of art. 357**, deduced from art. 357. For any `n` and any odd
integer `c`: if `4 (Xⁿ − 1)/(X − 1) = Y² − c Z²`, then for every `s`,
`4 (X^{n^s} − 1)/(X − 1) = Y_s² − c Z_s²` for some `Y_s, Z_s ∈ ℤ[X]`. -/
theorem generalisation (n : ℕ) (k : ℤ) (Y Z : ℤ[X])
    (h : 4 * G n = Y ^ 2 - C (2 * k + 1) * Z ^ 2) (s : ℕ) :
    ∃ Y' Z' : ℤ[X], 4 * G (n ^ s) = Y' ^ 2 - C (2 * k + 1) * Z' ^ 2 := by
  have hC : C (2 * k + 1) = 2 * C k + 1 := by simp
  rw [hC] at h ⊢
  induction s with
  | zero => exact ⟨2, 0, by simp [G]; ring⟩
  | succ s ih =>
    obtain ⟨Y₁, Z₁, h₁⟩ := ih
    have h₂ := congrArg (expand ℤ (n ^ s)) h
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_ofNat, expand_C] at h₂
    rw [pow_succ, G_mul]
    exact compose _ _ Y₁ Z₁ _ _ (C k) h₁ h₂

theorem generalisation_three (s : ℕ) :
    ∃ Y Z : ℤ[X], 4 * G (3 ^ s) = Y ^ 2 + 3 * Z ^ 2 := by
  obtain ⟨Y, Z, h⟩ := generalisation 3 (-2) (2 * X + 1) 1
    (by rw [art357_three]; norm_num) s
  exact ⟨Y, Z, by rw [h]; simp⟩

theorem generalisation_five (s : ℕ) :
    ∃ Y Z : ℤ[X], 4 * G (5 ^ s) = Y ^ 2 - 5 * Z ^ 2 := by
  obtain ⟨Y, Z, h⟩ := generalisation 5 2 (2 * X ^ 2 + X + 2) X
    (by rw [art357_five]; norm_num) s
  exact ⟨Y, Z, by rw [h]; simp⟩

theorem generalisation_seven (s : ℕ) :
    ∃ Y Z : ℤ[X], 4 * G (7 ^ s) = Y ^ 2 + 7 * Z ^ 2 := by
  obtain ⟨Y, Z, h⟩ := generalisation 7 (-4) (2 * X ^ 3 + X ^ 2 - X - 2) (X ^ 2 + X)
    (by rw [art357_seven]; norm_num) s
  exact ⟨Y, Z, by rw [h]; simp⟩

/-! ## From `Y, Z` to `Y', Z'` -/

/-- `∑_{i<n} (−X)ⁱ`, which is `(Xⁿ + 1)/(X + 1)` for `n` odd. -/
noncomputable def Gneg (n : ℕ) : ℤ[X] := ∑ i ∈ Finset.range n, (-X) ^ i

lemma X_add_one_mul_Gneg {n : ℕ} (hn : Odd n) : (X + 1) * Gneg n = X ^ n + 1 := by
  have h := mul_geom_sum (-X : ℤ[X]) n
  rw [hn.neg_pow] at h
  unfold Gneg
  linear_combination (-1 : ℤ[X]) * h

/-- **The passage from `Y, Z` to `Y', Z'`.** For `n` odd, if `4 (Xⁿ − 1)/(X − 1) = Y² − cZ²`,
then `4 (Xⁿ + 1)/(X + 1) = Y(−X)² − c Z(−X)²`. -/
theorem passage_neg {n : ℕ} (hn : Odd n) (c : ℤ) (Y Z : ℤ[X])
    (h : 4 * G n = Y ^ 2 - C c * Z ^ 2) :
    (X + 1) * Gneg n = X ^ n + 1 ∧
      4 * Gneg n = (Y.comp (-X)) ^ 2 - C c * (Z.comp (-X)) ^ 2 := by
  refine ⟨X_add_one_mul_Gneg hn, ?_⟩
  have hG : (G n).comp (-X) = Gneg n := by
    simp only [G, Gneg, comp, eval₂_finsetSum, eval₂_X_pow]
  have h' := congrArg (aeval (-X : ℤ[X])) h
  simp only [map_mul, map_sub, map_pow, map_ofNat, ← comp_eq_aeval, C_comp, hG] at h'
  exact h'

/-- `Y(−X)` is `Y` with the signs of its odd-degree terms changed. -/
theorem coeff_comp_neg_X (Y : ℤ[X]) (i : ℕ) : (Y.comp (-X)).coeff i = (-1) ^ i * Y.coeff i := by
  induction Y using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, coeff_add, hp, hq, mul_add]
  | monomial n a =>
    have e : (monomial n a).comp (-X) = C (a * (-1) ^ n) * X ^ n := by
      rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow, C_mul, C_pow, C_neg,
        C_1]
      ring
    rw [e, coeff_C_mul_X_pow, coeff_monomial]
    by_cases h : i = n
    · subst h; simp; ring
    · simp [h]

/-- The hypothesis `n` odd is needed: `(X² + 1)/(X + 1)` is not a polynomial. -/
theorem not_dvd_of_even {n : ℕ} (hn : Even n) : ¬ (X + 1 : ℤ[X]) ∣ X ^ n + 1 := by
  rintro ⟨q, hq⟩
  have := congrArg (eval (-1)) hq
  simp [hn.neg_one_pow] at this

/-! ## Fermat's equation for `n = p − 1` -/

/-- **The first case is immediate.** If the prime `p` divides none of `x, y, z`, then
`x^{p−1} + y^{p−1} ≠ z^{p−1}`. No condition `p ≡ 7 (mod 8)` is used. -/
theorem fermat_first_case (p : ℕ) [hp : Fact p.Prime] (x y z : ℤ) (hx : ¬ (p : ℤ) ∣ x)
    (hy : ¬ (p : ℤ) ∣ y) (hz : ¬ (p : ℤ) ∣ z) : x ^ (p - 1) + y ^ (p - 1) ≠ z ^ (p - 1) := by
  intro h
  have h' := congrArg (fun t : ℤ => (t : ZMod p)) h
  simp only [Int.cast_add, Int.cast_pow] at h'
  have nz : ∀ t : ℤ, ¬ (p : ℤ) ∣ t → (t : ZMod p) ≠ 0 := fun t ht h0 =>
    ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp h0)
  rw [ZMod.pow_card_sub_one_eq_one (nz x hx), ZMod.pow_card_sub_one_eq_one (nz y hy),
    ZMod.pow_card_sub_one_eq_one (nz z hz)] at h'
  exact one_ne_zero (by linear_combination h' : (1 : ZMod p) = 0)

/-- `p ≡ 7 (mod 8)` gives `n = p − 1 ≡ 6 (mod 8)`, so `4 ∤ n`, and `m = (p − 1)/2` is odd,
`≡ 3 (mod 4)`, with `p = 2m + 1`. -/
theorem mod_eight_seven (p : ℕ) (h : p % 8 = 7) :
    (p - 1) % 8 = 6 ∧ ¬ 4 ∣ p - 1 ∧ (p - 1) / 2 % 4 = 3 ∧ p = 2 * ((p - 1) / 2) + 1 := by
  omega

/-- For an odd prime `p`, `p ≡ 7 (mod 8)` iff `2` is a square and `−1` is not, mod `p`. -/
theorem seven_mod_eight_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    p % 8 = 7 ↔ IsSquare (2 : ZMod p) ∧ ¬ IsSquare (-1 : ZMod p) := by
  rw [ZMod.exists_sq_eq_two_iff hp, ZMod.exists_sq_eq_neg_one_iff]
  omega

/-- When `3 ∣ p − 1` the announcement follows from the case `n = 3`. -/
theorem flt_of_three_dvd (p : ℕ) (h : 3 ∣ p - 1) : FermatLastTheoremFor (p - 1) :=
  fermatLastTheoremThree.mono h

/-- The primes `p ≡ 7 (mod 8)` below `48` are `7, 23, 31, 47`; `3 ∣ p − 1` for `7` and `31`. -/
theorem first_primes_seven_mod_eight (p : ℕ) (hp : p.Prime) (h8 : p % 8 = 7) (h48 : p < 48) :
    (p = 7 ∨ p = 31) ∧ 3 ∣ p - 1 ∨ (p = 23 ∨ p = 47) ∧ ¬ 3 ∣ p - 1 := by
  interval_cases p <;> first | omega | (norm_num at hp)

/-! ## The determinant of the adjoint -/

/-- **`det (adj A) = (det A)^{n−1}`** for an `n × n` matrix over any commutative ring. -/
theorem det_adjugate_fin {R : Type*} [CommRing R] (n : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    A.adjugate.det = A.det ^ (n - 1) := by
  simpa using Matrix.det_adjugate A

/-- Gauss's ternary convention: his determinant is `D = −det M` and his adjoint is `−adj M`;
the determinant of the adjoint in his convention is then `D²`. -/
theorem gauss_ternary_adjoint {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    -(-M.adjugate).det = (-M.det) ^ 2 := by
  rw [Matrix.det_neg, det_adjugate_fin]
  simp; ring

open Matrix in
/-- A symmetric matrix of determinant zero over a field has a nonzero vector `v` in the
radical of its form: `Q(x + t v) = Q(x)` for all `x`, `t`. -/
theorem radical_of_det_eq_zero {K : Type*} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : M.IsSymm) (h : M.det = 0) :
    ∃ v : Fin n → K, v ≠ 0 ∧ ∀ (x : Fin n → K) (t : K),
      (x + t • v) ⬝ᵥ (M *ᵥ (x + t • v)) = x ⬝ᵥ (M *ᵥ x) := by
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨v, hv, fun x t => ?_⟩
  have hvx : v ⬝ᵥ (M *ᵥ x) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, hMv, zero_dotProduct]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hMv, smul_zero, add_zero, add_dotProduct,
    smul_dotProduct, hvx, smul_eq_mul, mul_zero]

/-! ## `p⁴ + 4` -/

/-- The two representations of the leaf. -/
theorem p4_add_four_reps (p : ℤ) :
    p ^ 4 + 4 = (p ^ 2) ^ 2 + 2 ^ 2 ∧ p ^ 4 + 4 = (p ^ 2 - 2) ^ 2 + (2 * p) ^ 2 := by
  constructor <;> ring

/-- **`p⁴ + 4` is prime only for `p = 1`.** -/
theorem p4_add_four_prime_iff (p : ℕ) : (p ^ 4 + 4).Prime ↔ p = 1 := by
  constructor
  · intro hp
    rcases Nat.eq_zero_or_pos p with rfl | hpos
    · norm_num at hp
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have hf : (q + 1) ^ 4 + 4 = (q ^ 2 + 1) * ((q + 2) ^ 2 + 1) := by ring
    rw [hf] at hp
    rcases (Nat.prime_mul_iff.mp hp) with ⟨_, h⟩ | ⟨_, h⟩
    · nlinarith
    · have : q ^ 2 = 0 := by omega
      simpa using this
  · rintro rfl; norm_num

/-- The two pairs `{p², 2}` and `{|p² − 2|, 2p}` coincide exactly for `p ≤ 2`
(the leaf names `p = 1`; `p = 2`, and `p = 0`, also give one pair). -/
theorem same_pair_iff (p : ℕ) :
    (((p : ℤ) ^ 2 = |(p : ℤ) ^ 2 - 2| ∧ (2 : ℤ) = 2 * p) ∨
      ((p : ℤ) ^ 2 = 2 * p ∧ (2 : ℤ) = |(p : ℤ) ^ 2 - 2|)) ↔ p ≤ 2 := by
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · omega
    · have : (p : ℤ) * (p - 2) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h | h <;> omega
  · intro hp
    interval_cases p <;> norm_num

/-! ## `p⁴ + q⁴` and the Fermat numbers -/

theorem p4_add_q4_identities {R : Type*} [CommRing R] (p q : R) :
    p ^ 4 + q ^ 4 = (p ^ 2 - q ^ 2) ^ 2 + 2 * (p * q) ^ 2 ∧
      p ^ 4 + q ^ 4 = (p ^ 2 + q ^ 2) ^ 2 - 2 * (p * q) ^ 2 := by
  constructor <;> ring

/-- `2^{2^i} + 1 = (2^{2^{i−2}})⁴ + 1⁴` for `i ≥ 2`. -/
theorem fermat_number_eq (i : ℕ) (hi : 2 ≤ i) :
    2 ^ 2 ^ i + 1 = (2 ^ 2 ^ (i - 2)) ^ 4 + 1 ^ 4 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  rw [Nat.add_sub_cancel, ← pow_mul, pow_add]
  ring

/-- `3` and `5` (`i = 0, 1`) are not sums of two fourth powers. -/
theorem three_five_not_sum_fourth (p q : ℕ) : p ^ 4 + q ^ 4 ≠ 3 ∧ p ^ 4 + q ^ 4 ≠ 5 := by
  have hp : p ≤ 1 ∨ 16 ≤ p ^ 4 := by
    rcases Nat.lt_or_ge p 2 with h | h
    · left; omega
    · right; calc 16 = 2 ^ 4 := by norm_num
        _ ≤ p ^ 4 := Nat.pow_le_pow_left h 4
  have hq : q ≤ 1 ∨ 16 ≤ q ^ 4 := by
    rcases Nat.lt_or_ge q 2 with h | h
    · left; omega
    · right; calc 16 = 2 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left h 4
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · interval_cases p <;> interval_cases q <;> norm_num
  all_goals omega

/-- `17 = 3² + 2·2²` is its only representation as `x² + 2y²` (`x, y ≥ 0`). -/
theorem seventeen_unique (x y : ℕ) (h : x ^ 2 + 2 * y ^ 2 = 17) : x = 3 ∧ y = 2 := by
  have hx : x ≤ 4 := by nlinarith
  have hy : y ≤ 2 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

/-- `257 = 15² + 2·4²` is its only representation as `x² + 2y²` (`x, y ≥ 0`). -/
theorem two_fifty_seven_unique (x y : ℕ) (h : x ^ 2 + 2 * y ^ 2 = 257) : x = 15 ∧ y = 4 := by
  have hx : x ≤ 16 := by nlinarith
  have hy : y ≤ 11 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

/-- **The representation by `x² − 2y²` is not unique.** `17 = 2⁴ + 1⁴` is prime and is
`5² − 2·2² = 23² − 2·16²`; the second is not `(p² + q²)² − 2(pq)²`. -/
theorem x_sq_sub_two_y_sq_not_unique :
    (17 : ℤ) = 5 ^ 2 - 2 * 2 ^ 2 ∧ (17 : ℤ) = 23 ^ 2 - 2 * 16 ^ 2 ∧ Nat.Prime 17 := by
  norm_num

/-- Each representation by `x² − 2y²` gives another, through the unit `3 + 2√2`. -/
theorem pell_step (x y : ℤ) :
    (3 * x + 4 * y) ^ 2 - 2 * (2 * x + 3 * y) ^ 2 = x ^ 2 - 2 * y ^ 2 := by ring

/-! ## Composition of binary forms

A form is a triple `(a, b, c)`, standing for `ax² + bxy + cy²` (modern notation; Gauss's
`(a, b, c)` is the modern `(a, 2b, c)`, of determinant `b² − ac`). -/

/-- The value of the form `f` at `(x, y)`. -/
def ev (f : ℤ × ℤ × ℤ) (x y : ℤ) : ℤ := f.1 * x ^ 2 + f.2.1 * x * y + f.2.2 * y ^ 2

/-- `g` is obtained from `f` by a substitution of determinant `1`. -/
def ProperEquiv (f g : ℤ × ℤ × ℤ) : Prop :=
  ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧ ∀ x y, ev g x y = ev f (α * x + β * y) (γ * x + δ * y)

/-- `g` is obtained from `f` by a substitution of determinant `±1`. -/
def Equiv (f g : ℤ × ℤ × ℤ) : Prop :=
  ∃ α β γ δ : ℤ, (α * δ - β * γ = 1 ∨ α * δ - β * γ = -1) ∧
    ∀ x y, ev g x y = ev f (α * x + β * y) (γ * x + δ * y)

/-- Dirichlet's composition identity for united forms `(a₁, B, a₂c)` and `(a₂, B, a₁c)`. -/
theorem dirichlet_identity (a₁ a₂ B c x y z w : ℤ) :
    ev (a₁, B, a₂ * c) x y * ev (a₂, B, a₁ * c) z w =
      ev (a₁ * a₂, B, c) (x * z - c * y * w) (a₁ * x * w + a₂ * y * z + B * y * w) := by
  simp only [ev]; ring

/-- `F` is the Dirichlet composite of `f` and `g`: they are properly equivalent to united
forms `(a₁, B, a₂c)`, `(a₂, B, a₁c)` with `gcd(a₁, a₂) = 1`, and `F` to `(a₁a₂, B, c)`. -/
def DirichletComposite (f g F : ℤ × ℤ × ℤ) : Prop :=
  ∃ a₁ a₂ B c : ℤ, Int.gcd a₁ a₂ = 1 ∧ ProperEquiv f (a₁, B, a₂ * c) ∧
    ProperEquiv g (a₂, B, a₁ * c) ∧ ProperEquiv (a₁ * a₂, B, c) F

/-- Gauss's `(16, 3, 19) ∘ (8, 1, 37) = (8, −1, 37)`. -/
theorem composite_one : DirichletComposite (16, 6, 19) (8, 2, 37) (8, -2, 37) :=
  ⟨19, 8, 146, 37, by norm_num,
    ⟨0, -1, 1, 4, by norm_num, fun x y => by simp only [ev]; ring⟩,
    ⟨1, 9, 0, 1, by norm_num, fun x y => by simp only [ev]; ring⟩,
    ⟨-1, 0, 2, -1, by norm_num, fun x y => by simp only [ev]; ring⟩⟩

/-- Germain's `(13, −2, 23)` is the composite of the *opposite* `(16, −3, 19)` with
`(8, 1, 37)`. -/
theorem composite_two : DirichletComposite (16, -6, 19) (8, 2, 37) (13, -4, 23) :=
  ⟨19, 8, 82, 13, by norm_num,
    ⟨0, -1, 1, 2, by norm_num, fun x y => by simp only [ev]; ring⟩,
    ⟨1, 5, 0, 1, by norm_num, fun x y => by simp only [ev]; ring⟩,
    ⟨0, -1, 1, 3, by norm_num, fun x y => by simp only [ev]; ring⟩⟩

/-- `(13, −2, 23) = (8, −1, 37) ∘ (5, 0, 59)`. -/
theorem composite_three : DirichletComposite (8, -2, 37) (5, 0, 59) (13, -4, 23) :=
  ⟨8, 5, 30, 13, by norm_num,
    ⟨1, 2, 0, 1, by norm_num, fun x y => by simp only [ev]; ring⟩,
    ⟨1, 3, 0, 1, by norm_num, fun x y => by simp only [ev]; ring⟩,
    ⟨0, -1, 1, 1, by norm_num, fun x y => by simp only [ev]; ring⟩⟩

/-- `(5, 0, 59)` composed with itself is the principal form: it has order `2`. -/
theorem composite_four : DirichletComposite (5, 0, 59) (5, 0, 59) (1, 0, 295) :=
  ⟨5, 59, 0, 1, by norm_num,
    ⟨1, 0, 0, 1, by norm_num, fun x y => by simp only [ev]; ring⟩,
    ⟨0, -1, 1, 0, by norm_num, fun x y => by simp only [ev]; ring⟩,
    ⟨0, -1, 1, 0, by norm_num, fun x y => by simp only [ev]; ring⟩⟩

/-- The opposite forms `(16, ±3, 19)` are improperly equivalent. -/
theorem opposite_equiv : Equiv (16, 6, 19) (16, -6, 19) :=
  ⟨1, 0, 0, -1, Or.inr (by norm_num), fun x y => by simp only [ev]; ring⟩

/-- **`(8, −1, 37)` and `(13, −2, 23)` are not equivalent, properly or improperly**: the first
represents `8`, the second does not. -/
theorem not_equiv_8_13 : ¬ Equiv (13, -4, 23) (8, -2, 37) := by
  rintro ⟨α, β, γ, δ, -, h⟩
  have h8 := h 1 0
  simp only [ev] at h8
  have : (13 * (α * 1 + β * 0) - 2 * (γ * 1 + δ * 0)) ^ 2 + 295 * (γ * 1 + δ * 0) ^ 2 = 104 := by
    linear_combination (-13) * h8
  have hγ : γ = 0 := by nlinarith [sq_nonneg (13 * α - 2 * γ), sq_nonneg γ]
  subst hγ
  have : 169 * α ^ 2 = 104 := by linear_combination this
  have : α ^ 2 ≤ 1 := by nlinarith
  have : α ^ 2 = 0 ∨ α ^ 2 = 1 := by
    have := sq_nonneg α; omega
  omega

/-- **The reduced properly primitive forms of determinant `−295`** (Gauss's convention
`(a, b, c)`, `b² − ac = −295`, `|2b| ≤ a ≤ c`, `b ≥ 0` if `|2b| = a` or `a = c`,
`gcd(a, 2b, c) = 1`) are the eight `(1,0,295)`, `(5,0,59)`, `(8,±1,37)`, `(13,±2,23)`,
`(16,±3,19)`. -/
theorem reduced_forms_295 (a b c : ℤ) (hD : b ^ 2 - a * c = -295) (ha : 0 < a)
    (hb : |2 * b| ≤ a) (hac : a ≤ c) (hbd : |2 * b| = a ∨ a = c → 0 ≤ b)
    (hprim : Int.gcd (Int.gcd a (2 * b)) c = 1) :
    (a, b, c) ∈ ({(1, 0, 295), (5, 0, 59), (8, 1, 37), (8, -1, 37), (13, 2, 23), (13, -2, 23),
      (16, 3, 19), (16, -3, 19)} : Finset (ℤ × ℤ × ℤ)) := by
  have hb' : -a ≤ 2 * b ∧ 2 * b ≤ a := abs_le.mp hb
  have ha19 : a ≤ 19 := by nlinarith
  have hc : c = (b ^ 2 + 295) / a := by
    rw [show b ^ 2 + 295 = a * c by linarith, Int.mul_ediv_cancel_left _ ha.ne']
  subst hc
  -- `1 ≤ a ≤ 19` and `-9 ≤ b ≤ 9`: a finite check, left to the kernel
  have key : ∀ a ∈ Finset.Icc (1 : ℤ) 19, ∀ b ∈ Finset.Icc (-9 : ℤ) 9,
      b ^ 2 - a * ((b ^ 2 + 295) / a) = -295 → |2 * b| ≤ a → a ≤ (b ^ 2 + 295) / a →
      (|2 * b| = a ∨ a = (b ^ 2 + 295) / a → 0 ≤ b) →
      Int.gcd (Int.gcd a (2 * b)) ((b ^ 2 + 295) / a) = 1 →
      (a, b, (b ^ 2 + 295) / a) ∈ ({(1, 0, 295), (5, 0, 59), (8, 1, 37), (8, -1, 37),
        (13, 2, 23), (13, -2, 23), (16, 3, 19), (16, -3, 19)} : Finset (ℤ × ℤ × ℤ)) := by
    decide +kernel
  exact key a (Finset.mem_Icc.2 ⟨by omega, ha19⟩) b (Finset.mem_Icc.2 ⟨by omega, by omega⟩) hD hb
    hac hbd hprim

/-! ## The lever, the infinite and the hyperbola -/

/-- **`0 × ∞` is indeterminate.** For every `c`, `c/x → 0` and `x → ∞`, while their product
tends to `c` (the hyperbola `xy = c`). -/
theorem indeterminate_product (c : ℝ) :
    Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) ∧ Tendsto (fun x : ℝ => x) atTop atTop ∧
      Tendsto (fun x : ℝ => c / x * x) atTop (𝓝 c) := by
  refine ⟨tendsto_const_nhds.div_atTop tendsto_id, tendsto_id, ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp

/-- **`0/0` « égal à tout ce qu'on veut ».** For every `c`, `c/x → 0` and `1/x → 0` while
their quotient tends to `c`. -/
theorem indeterminate_quotient (c : ℝ) :
    Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) ∧ Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) ∧
      Tendsto (fun x : ℝ => (c / x) / (1 / x)) atTop (𝓝 c) := by
  refine ⟨tendsto_const_nhds.div_atTop tendsto_id, tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp

/-! ## The centre of gravity of the triangle -/

/-- The leaf's equation `2x = (a + x)/2` gives `x = a/3`. -/
theorem centroid_equation (a x : ℝ) : 2 * x = (a + x) / 2 ↔ x = a / 3 := by
  constructor <;> intro h <;> linarith

/-- The centroid of three points. -/
noncomputable def cg {V : Type*} [AddCommGroup V] [Module ℝ V] (P Q R : V) : V :=
  (1 / 3 : ℝ) • (P + Q + R)

/-- The decomposition of the leaf: with `D, E, F` the midpoints of `BC, CA, AB`, the triangle
`ABC` is the parallelogram `AFDE` (half the area, centre the midpoint of `AD`) and the two
triangles `BFD`, `CED` (a quarter each). The weighted centre is the centroid of `ABC`. -/
theorem centroid_decomposition {V : Type*} [AddCommGroup V] [Module ℝ V] (A B C : V) :
    let D := (1 / 2 : ℝ) • (B + C)
    let E := (1 / 2 : ℝ) • (C + A)
    let F := (1 / 2 : ℝ) • (A + B)
    (1 / 4 : ℝ) • cg B F D + (1 / 4 : ℝ) • cg C E D + (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (A + D)) =
      cg A B C := by
  simp only [cg]; module

/-- The centroid lies on the median `AD` at a third of it from the base. -/
theorem centroid_on_median {V : Type*} [AddCommGroup V] [Module ℝ V] (A B C : V) :
    cg A B C = (1 / 2 : ℝ) • (B + C) + (1 / 3 : ℝ) • (A - (1 / 2 : ℝ) • (B + C)) := by
  simp only [cg]; module

/-- The small triangle `BFD` is the image of `ABC` by the homothety of centre `B`, ratio `1/2`,
and so is its centroid. -/
theorem small_centroid_homothety {V : Type*} [AddCommGroup V] [Module ℝ V] (A B C : V) :
    cg B ((1 / 2 : ℝ) • (A + B)) ((1 / 2 : ℝ) • (B + C)) = B + (1 / 2 : ℝ) • (cg A B C - B) := by
  simp only [cg]; module

/-! ## Legendre, « Pag. 155 »: the parasite root and the case `λ = 1/3` -/

/-- Euler's equation as Legendre writes it, right-hand side. -/
noncomputable def eulerF (l ω : ℝ) : ℝ :=
  2 - 2 * Real.exp (2 * ω) - (Real.exp (l * ω) - Real.exp ((2 - l) * ω)) *
    (Real.exp (l * ω) - Real.exp (-(l * ω))) * (Real.cot (l * ω) + Real.cot ((1 - l) * ω))

/-- `eulerF (1/2)` with the denominator `sin(ω/2)` cleared. -/
noncomputable def parasiteH (ω : ℝ) : ℝ :=
  Real.sin (ω / 2) * (2 - 2 * Real.exp (2 * ω)) - 2 * (Real.exp (ω / 2) - Real.exp (3 / 2 * ω)) *
    (Real.exp (ω / 2) - Real.exp (-(ω / 2))) * Real.cos (ω / 2)

/-- For `λ = 1/2`, `F(ω) = H(ω)/sin(ω/2)` wherever `sin(ω/2) ≠ 0`. -/
theorem parasite_root (ω : ℝ) (hs : Real.sin (ω / 2) ≠ 0) :
    eulerF (1 / 2) ω = parasiteH ω / Real.sin (ω / 2) := by
  have e1 : (1 / 2 : ℝ) * ω = ω / 2 := by ring
  have e2 : (1 - 1 / 2 : ℝ) * ω = ω / 2 := by ring
  have e3 : (2 - 1 / 2 : ℝ) * ω = 3 / 2 * ω := by ring
  rw [eulerF, e1, e2, e3, parasiteH, Real.cot_eq_cos_div_sin]
  field_simp
  ring

/-- **The root `sin(ω/2) = 0` is parasitic.** At `ω = 2kπ`, `k ≠ 0`, the factor `sin(ω/2)`
vanishes but `H` does not: the zero of the cleared equation `sin(ω/2) H(ω) = 0` there comes
from the factor introduced by the multiplication. -/
theorem parasite_H_ne_zero (k : ℤ) (hk : k ≠ 0) :
    Real.sin (2 * k * Real.pi / 2) = 0 ∧ parasiteH (2 * k * Real.pi) ≠ 0 := by
  have e : 2 * (k : ℝ) * Real.pi / 2 = k * Real.pi := by ring
  refine ⟨by rw [e]; exact Real.sin_int_mul_pi k, ?_⟩
  rw [parasiteH, e, Real.sin_int_mul_pi, zero_mul, zero_sub, neg_ne_zero]
  have hkπ : (k : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Real.pi_ne_zero
  have h1 : Real.exp (k * Real.pi) - Real.exp (3 / 2 * (2 * k * Real.pi)) ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have := Real.exp_injective h
    exact hkπ (by linarith)
  have h2 : Real.exp (k * Real.pi) - Real.exp (-(k * Real.pi)) ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have := Real.exp_injective h
    exact hkπ (by linarith)
  have h3 : Real.cos (k * Real.pi) ≠ 0 := by
    intro h
    have := Real.sin_sq_add_cos_sq (k * Real.pi)
    rw [Real.sin_int_mul_pi, h] at this
    norm_num at this
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h1) h2) h3

/-- The small term `ε` of Legendre's reduction. -/
noncomputable def eps (l ω : ℝ) : ℝ :=
  Real.exp ((2 * l - 2) * ω) - Real.exp (-(2 * ω)) + Real.exp (-(2 * l * ω))

/-- **Legendre's reduction, exactly.** `e^{−2ω} F(ω) = 2e^{−2ω} − 2 + (1 − ε(ω)) S(ω)` with
`S = cot λω + cot (1 − λ)ω`. -/
theorem euler_large_omega (l ω : ℝ) :
    Real.exp (-(2 * ω)) * eulerF l ω = 2 * Real.exp (-(2 * ω)) - 2 +
      (1 - eps l ω) * (Real.cot (l * ω) + Real.cot ((1 - l) * ω)) := by
  have f1 : Real.exp (-(2 * ω)) * Real.exp (l * ω) * Real.exp (l * ω) =
      Real.exp ((2 * l - 2) * ω) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have f2 : Real.exp (-(2 * ω)) * Real.exp (l * ω) * Real.exp (-(l * ω)) =
      Real.exp (-(2 * ω)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have f3 : Real.exp (-(2 * ω)) * Real.exp ((2 - l) * ω) * Real.exp (l * ω) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_eq_one_iff]; ring
  have f4 : Real.exp (-(2 * ω)) * Real.exp ((2 - l) * ω) * Real.exp (-(l * ω)) =
      Real.exp (-(2 * l * ω)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have key : Real.exp (-(2 * ω)) * ((Real.exp (l * ω) - Real.exp ((2 - l) * ω)) *
      (Real.exp (l * ω) - Real.exp (-(l * ω)))) = -(1 - eps l ω) := by
    rw [eps]; linear_combination f1 - f2 - f3 + f4
  have h2 : Real.exp (-(2 * ω)) * Real.exp (2 * ω) = 1 := by
    rw [← Real.exp_add]; simp
  rw [eulerF]
  linear_combination (-(Real.cot (l * ω) + Real.cot ((1 - l) * ω))) * key - 2 * h2

/-- For `0 < λ < 1`, `ε(ω) → 0` as `ω → ∞`: hence `cot λω + cot (1 − λ)ω = 2` in the limit. -/
theorem eps_tendsto_zero (l : ℝ) (h0 : 0 < l) (h1 : l < 1) :
    Tendsto (eps l) atTop (𝓝 0) := by
  have t : ∀ a : ℝ, a < 0 → Tendsto (fun ω : ℝ => Real.exp (a * ω)) atTop (𝓝 0) := fun a ha =>
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg ha)
  have := ((t (2 * l - 2) (by linarith)).sub (t (-2) (by norm_num))).add
    (t (-(2 * l)) (by linarith))
  simp only [sub_zero, add_zero] at this
  refine this.congr fun ω => ?_
  simp only [eps]; ring_nf

/-- **The case `λ = 1/3`.** With `x = cot θ` (`θ = ω/3`) and `sin 2θ ≠ 0`,
`cot θ + cot 2θ = 2` iff `3x² − 4x − 1 = 0` iff `x = (2 ± √7)/3`. -/
theorem lambda_third (θ : ℝ) (hs : Real.sin (2 * θ) ≠ 0) :
    (Real.cot θ + Real.cot (2 * θ) = 2 ↔ 3 * Real.cot θ ^ 2 - 4 * Real.cot θ - 1 = 0) ∧
      (3 * Real.cot θ ^ 2 - 4 * Real.cot θ - 1 = 0 ↔
        Real.cot θ = (2 + Real.sqrt 7) / 3 ∨ Real.cot θ = (2 - Real.sqrt 7) / 3) := by
  rw [Real.sin_two_mul] at hs
  have hsin : Real.sin θ ≠ 0 := fun h => hs (by rw [h]; ring)
  have hcos : Real.cos θ ≠ 0 := fun h => hs (by rw [h]; ring)
  have hx : Real.cot θ ≠ 0 := by
    rw [Real.cot_eq_cos_div_sin]; exact div_ne_zero hcos hsin
  have hcot2 : Real.cot (2 * θ) = (Real.cot θ ^ 2 - 1) / (2 * Real.cot θ) := by
    have hc2 : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := by
      rw [Real.cos_two_mul]; linear_combination Real.sin_sq_add_cos_sq θ
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.sin_two_mul, hc2]
    field_simp
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  constructor
  · rw [hcot2]
    constructor
    · intro h; field_simp at h; linear_combination h
    · intro h; field_simp; linear_combination h
  · constructor
    · intro h
      have : (Real.cot θ - (2 + Real.sqrt 7) / 3) * (Real.cot θ - (2 - Real.sqrt 7) / 3) = 0 := by
        linear_combination h / 3 - h7 / 9
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> rw [h] <;> linear_combination (1 / 3 : ℝ) * h7

/-! ## Legendre's lamina test -/

/-- If `∂z/∂y` vanishes identically, `z` does not depend on `y`: the condition `dz/dy = 0` of
the letter of 4 December 1811, read as an identity, is enough. -/
theorem indep_of_deriv_zero (z : ℝ → ℝ → ℝ) (hd : ∀ x, Differentiable ℝ (z x))
    (h : ∀ x y, deriv (z x) y = 0) (x y : ℝ) : z x y = z x 0 :=
  is_const_of_deriv_eq_zero (hd x) (h x) y 0

end LeanPool.SophieGermainArchives.Fr9118
