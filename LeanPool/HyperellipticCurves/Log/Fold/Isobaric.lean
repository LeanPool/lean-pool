/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

import Mathlib.Tactic.LinearCombination

/-!
# Isobarity for polynomials over weighted variables

The isobarity predicate of the fold-witness route (`lem:fold-universal`):
`ChabautyColeman.IsIsobaric w n p` says that the `i`-th coefficient of
`p : (MvPolynomial σ R)[X]` is weighted-homogeneous of weight `n - 2i` — the polynomial
variable (the `x`-coordinate of the curve) carries weight `2`. Weights and the isobarity
degree are *integers*, so the coefficient shift never truncates; with positive weights,
coefficients above the isobarity degree vanish automatically
(`MvPolynomial.IsWeightedHomogeneous.eq_zero_of_neg`).

The closure API covers ring operations, `Polynomial.C`/`X`, `derivative`, evaluation at a
weight-`2` value, and — the substantial fact — **unconditional monic division**
(`ChabautyColeman.IsIsobaric.divByMonic`): the `/ₘ`-quotient by a monic isobaric divisor
is isobaric with *no exactness hypothesis*, so it applies to the numerator fold's
truncated divisions at the universal instance, where the curve equation does not hold.
The division characterizations `ChabautyColeman.modByMonic_eq_of_dvd_sub_of_degree_lt` and
`ChabautyColeman.divByMonic_eq_of_eq_add` support the peeling induction.

## Main statements

* `ChabautyColeman.IsIsobaric`: the predicate.
* `ChabautyColeman.IsIsobaric.divByMonic`: unconditional isobarity of monic division.
* `ChabautyColeman.modByMonic_eq_of_dvd_sub_of_degree_lt`,
  `ChabautyColeman.divByMonic_eq_of_eq_add`:
  `%ₘ` and `/ₘ` are characterized by congruence/identity plus a degree bound.
* `MvPolynomial.IsWeightedHomogeneous.eq_zero_of_neg`: with nonnegative weights, only `0`
  is weighted-homogeneous of negative weight.
-/

@[expose] public section

open Polynomial MvPolynomial

namespace ChabautyColeman

/-! ### Small additions to the weighted-homogeneity API -/

section WeightedHomogeneous

variable {R σ M : Type*} [CommSemiring R] [AddCommMonoid M] {w : σ → M} {φ : MvPolynomial σ R}
  {m : M}

theorem _root_.MvPolynomial.IsWeightedHomogeneous.of_weight_eq {n : M}
    (hφ : φ.IsWeightedHomogeneous w m) (h : m = n) : φ.IsWeightedHomogeneous w n :=
  h ▸ hφ

/-- With nonnegative weights, only the zero polynomial is weighted-homogeneous of
negative weight. -/
theorem _root_.MvPolynomial.IsWeightedHomogeneous.eq_zero_of_neg {w : σ → ℤ} {n : ℤ}
    (hw : ∀ s, 0 ≤ w s) (hn : n < 0) (hφ : φ.IsWeightedHomogeneous w n) : φ = 0 := by
  by_contra h0
  obtain ⟨d, hd⟩ := ne_zero_iff.mp h0
  refine absurd (hφ hd) (ne_of_gt (lt_of_lt_of_le hn ?_))
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_nonneg fun s _ ↦ nsmul_nonneg (hw s) _

end WeightedHomogeneous

section Transport

variable {R σ τ M : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} {w' : τ → M}
  {φ : MvPolynomial σ R} {n : M}

/-- **Weighted homogeneity transports along variable substitutions**: if every variable
maps to a weighted-homogeneous value of its own weight, the image of a
weighted-homogeneous polynomial is weighted-homogeneous of the same weight. -/
theorem _root_.MvPolynomial.IsWeightedHomogeneous.aeval {ψ : σ → MvPolynomial τ R}
    (hψ : ∀ s, (ψ s).IsWeightedHomogeneous w' (w s)) (hφ : φ.IsWeightedHomogeneous w n) :
    (MvPolynomial.aeval ψ φ).IsWeightedHomogeneous w' n := by
  classical
  rw [φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd ↦ ?_
  rw [aeval_monomial]
  have h1 : (algebraMap R (MvPolynomial τ R) (φ.coeff d)).IsWeightedHomogeneous w' 0 := by
    rw [MvPolynomial.algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  have h2 : (d.prod fun s k ↦ ψ s ^ k).IsWeightedHomogeneous w' (Finsupp.weight w d) := by
    rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
    exact IsWeightedHomogeneous.prod _ _ _ fun s _ ↦ (hψ s).pow (d s)
  exact (h1.mul h2).of_weight_eq (by rw [zero_add, hφ (mem_support_iff.mp hd)])

end Transport

/-! ### Division characterization -/

section ModUnique

variable {S : Type*} [CommRing S]

/-- `%ₘ` is characterized by congruence and degree. Unlike Mathlib's
`Polynomial.modByMonic_eq_of_dvd_sub`, which only compares the two remainders, the degree
bound identifies the remainder itself. -/
theorem modByMonic_eq_of_dvd_sub_of_degree_lt {p q r : S[X]} (hq : q.Monic) (hdvd : q ∣ p - r)
    (hdeg : r.degree < q.degree) : p %ₘ q = r := by
  obtain ⟨D, hD⟩ := hdvd
  exact (div_modByMonic_unique D r hq ⟨by linear_combination -hD, hdeg⟩).2

/-- `/ₘ` is characterized by the division identity with a small remainder. -/
theorem divByMonic_eq_of_eq_add {p q D r : S[X]} (hq : q.Monic) (h : p = q * D + r)
    (hdeg : r.degree < q.degree) : p /ₘ q = D :=
  (div_modByMonic_unique D r hq ⟨by linear_combination -h, hdeg⟩).1

end ModUnique

/-! ### Isobarity -/

section Isobaric

variable {R σ : Type*} [CommRing R] {w : σ → ℤ} {m n : ℤ} {p q : (MvPolynomial σ R)[X]}

/-- **Isobarity** for polynomials over a weighted multivariate polynomial ring: the `i`-th
coefficient is weighted-homogeneous of weight `n - 2i` — the polynomial variable carries
weight `2` (the `x`-coordinate weight of the fold). Integer weights make the shift exact:
with positive weights, coefficients above the isobarity degree vanish
(`ChabautyColeman.IsIsobaric.coeff_eq_zero`). -/
def IsIsobaric (w : σ → ℤ) (n : ℤ) (p : (MvPolynomial σ R)[X]) : Prop :=
  ∀ i : ℕ, (p.coeff i).IsWeightedHomogeneous w (n - 2 * i)

theorem isIsobaric_zero : IsIsobaric w n (0 : (MvPolynomial σ R)[X]) :=
  fun _ ↦ by simpa using isWeightedHomogeneous_zero _ _ _

theorem IsIsobaric.of_weight_eq (hp : IsIsobaric w m p) (h : m = n) : IsIsobaric w n p :=
  h ▸ hp

theorem IsIsobaric.add (hp : IsIsobaric w n p) (hq : IsIsobaric w n q) :
    IsIsobaric w n (p + q) :=
  fun i ↦ by simpa using (hp i).add (hq i)

theorem IsIsobaric.neg (hp : IsIsobaric w n p) : IsIsobaric w n (-p) :=
  fun i ↦ by simpa using (hp i).neg

theorem IsIsobaric.sub (hp : IsIsobaric w n p) (hq : IsIsobaric w n q) :
    IsIsobaric w n (p - q) :=
  fun i ↦ by simpa using (hp i).sub (hq i)

theorem IsIsobaric.mul (hp : IsIsobaric w m p) (hq : IsIsobaric w n q) :
    IsIsobaric w (m + n) (p * q) := by
  intro i
  rw [Polynomial.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd ↦ ?_
  have h2 : (m - 2 * d.1) + (n - 2 * d.2) = m + n - 2 * i := by
    have h3 := Finset.mem_antidiagonal.mp hd
    push_cast [← h3]
    ring
  exact h2 ▸ (hp d.1).mul (hq d.2)

theorem isIsobaric_C {φ : MvPolynomial σ R} (hφ : φ.IsWeightedHomogeneous w n) :
    IsIsobaric w n (Polynomial.C φ) := by
  intro i
  rcases i with - | i
  · simpa using hφ
  · simpa [Polynomial.coeff_C] using isWeightedHomogeneous_zero _ _ _

theorem isIsobaric_one : IsIsobaric w 0 (1 : (MvPolynomial σ R)[X]) := by
  simpa [map_one] using isIsobaric_C (w := w) (isWeightedHomogeneous_one (R := R) w)

theorem IsIsobaric.sum {ι : Type*} (s : Finset ι) (φ : ι → (MvPolynomial σ R)[X])
    (h : ∀ i ∈ s, IsIsobaric w n (φ i)) : IsIsobaric w n (∑ i ∈ s, φ i) := fun k ↦ by
  rw [Polynomial.finsetSum_coeff]
  exact IsWeightedHomogeneous.sum _ _ _ fun i hi ↦ h i hi k

theorem IsIsobaric.prod {ι : Type*} (s : Finset ι) (φ : ι → (MvPolynomial σ R)[X])
    (n : ι → ℤ) (h : ∀ i ∈ s, IsIsobaric w (n i) (φ i)) :
    IsIsobaric w (∑ i ∈ s, n i) (∏ i ∈ s, φ i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using isIsobaric_one
  | cons i s his ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact (h i (Finset.mem_cons_self ..)).mul
      (ih fun j hj ↦ h j (Finset.mem_cons_of_mem hj))

theorem isIsobaric_X_pow (k : ℕ) :
    IsIsobaric w (2 * k) (Polynomial.X ^ k : (MvPolynomial σ R)[X]) := by
  intro i
  rw [Polynomial.coeff_X_pow]
  split_ifs with hik
  · rw [hik, show 2 * (k : ℤ) - 2 * k = 0 by ring]
    exact isWeightedHomogeneous_one ..
  · exact isWeightedHomogeneous_zero _ _ _

theorem isIsobaric_X : IsIsobaric w 2 (Polynomial.X : (MvPolynomial σ R)[X]) := by
  simpa using isIsobaric_X_pow (R := R) (w := w) 1

theorem isIsobaric_X_sub_C {v : MvPolynomial σ R} (hv : v.IsWeightedHomogeneous w 2) :
    IsIsobaric w 2 (Polynomial.X - Polynomial.C v) :=
  isIsobaric_X.sub (isIsobaric_C hv)

theorem IsIsobaric.derivative (hp : IsIsobaric w n p) :
    IsIsobaric w (n - 2) p.derivative := by
  intro i
  rw [Polynomial.coeff_derivative]
  have h1 : MvPolynomial.C ((i : R) + 1) = (i : MvPolynomial σ R) + 1 := by
    rw [map_add, map_natCast, map_one]
  have h2 : (n - 2 * (i + 1 : ℕ)) + 0 = n - 2 - 2 * i := by push_cast; ring
  have h5 := (hp (i + 1)).mul (isWeightedHomogeneous_C w ((i : R) + 1))
  rw [h1] at h5
  exact h2 ▸ h5

theorem IsIsobaric.eval {v : MvPolynomial σ R} (hp : IsIsobaric w n p)
    (hv : v.IsWeightedHomogeneous w 2) : (p.eval v).IsWeightedHomogeneous w n := by
  rw [eval_eq_sum, Polynomial.sum_def]
  refine IsWeightedHomogeneous.sum _ _ _ fun i _ ↦ ?_
  have h2 : (n - 2 * i) + i • (2 : ℤ) = n := by ring
  exact h2 ▸ (hp i).mul (hv.pow i)

/-- **Unconditional isobarity of monic division**: the `/ₘ`-quotient by a monic isobaric
divisor (necessarily of weight twice its degree) is isobaric, with no exactness
hypothesis — the truncated quotient is isobaric even when a remainder is discarded. -/
theorem IsIsobaric.divByMonic [Nontrivial R] {d : ℕ} (hp : IsIsobaric w n p)
    (hq : IsIsobaric w (2 * d) q) (hqm : q.Monic) (hqd : q.natDegree = d) :
    IsIsobaric w (n - 2 * d) (p /ₘ q) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [hqm.natDegree_eq_zero.mp hqd, divByMonic_one]
    exact hp.of_weight_eq (by ring)
  have hqdeg : q.degree = (d : WithBot ℕ) := by rw [degree_eq_natDegree hqm.ne_zero, hqd]
  suffices H : ∀ N : ℕ, ∀ p : (MvPolynomial σ R)[X], p.natDegree ≤ N → IsIsobaric w n p →
      IsIsobaric w (n - 2 * d) (p /ₘ q) from H p.natDegree p le_rfl hp
  intro N
  induction N with
  | zero =>
    intro p hpN hp
    rw [divByMonic_eq_zero_iff hqm |>.mpr (by
      rw [hqdeg]
      exact degree_le_natDegree.trans_lt (mod_cast by lia))]
    exact isIsobaric_zero
  | succ N ih =>
    intro p hpN hp
    by_cases hlt : p.degree < q.degree
    · rw [(divByMonic_eq_zero_iff hqm).mpr hlt]
      exact isIsobaric_zero
    -- the leading term of the quotient, peeled off
    have hdN : d ≤ p.natDegree := by
      by_contra! hc
      exact hlt (by rw [hqdeg]; exact degree_le_natDegree.trans_lt (mod_cast hc))
    have hp0 : p ≠ 0 := fun h0 ↦ by
      rw [h0, natDegree_zero] at hdN
      lia
    have ha := hp p.natDegree
    set p₁ := p - Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - d) * q
      with hp1def
    have hterm : IsIsobaric w n
        (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - d) * q) := by
      refine (((isIsobaric_C ha).mul (isIsobaric_X_pow _)).mul hq).of_weight_eq ?_
      push_cast [Nat.cast_sub hdN]
      ring
    have hp₁ : IsIsobaric w n p₁ := hp.sub hterm
    obtain ⟨k, hk⟩ : ∃ k, p.natDegree = d + k := ⟨p.natDegree - d, by lia⟩
    -- the degree drops: the leading terms cancel
    have hc0 : p₁.coeff p.natDegree = 0 := by
      rw [hp1def, Polynomial.coeff_sub, show p.natDegree - d = k by lia, mul_right_comm,
        hk, Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul, ← hqd, hqm.coeff_natDegree,
        mul_one, hqd, ← hk, ← Polynomial.leadingCoeff, sub_self]
    have hdeg₁ : p₁.natDegree < p.natDegree := by
      have h7 := Nat.sub_add_cancel hdN
      have hup : p₁.natDegree ≤ p.natDegree := by
        refine (natDegree_sub_le _ _).trans (max_le le_rfl (natDegree_mul_le.trans ?_))
        have h6 := natDegree_C_mul_le p.leadingCoeff
          (Polynomial.X ^ (p.natDegree - d) : (MvPolynomial σ R)[X])
        rw [natDegree_X_pow] at h6
        rw [hqd]
        lia
      rcases eq_or_ne p₁ 0 with h0 | h0
      · rw [h0, natDegree_zero]
        lia
      · refine lt_of_le_of_ne hup fun hEQ ↦ h0 ?_
        rwa [← leadingCoeff_eq_zero, Polynomial.leadingCoeff, hEQ]
    -- peel the leading term of the quotient and recurse
    have hdiv : p /ₘ q
        = Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - d) + p₁ /ₘ q := by
      refine divByMonic_eq_of_eq_add (r := p₁ %ₘ q) hqm ?_ (degree_modByMonic_lt _ hqm)
      have h8 := modByMonic_add_div p₁ q
      linear_combination -h8 - hp1def
    rw [hdiv]
    refine (((isIsobaric_C ha).mul (isIsobaric_X_pow _)).of_weight_eq ?_).add
      (ih p₁ (by lia) hp₁)
    push_cast [Nat.cast_sub hdN]
    ring

end Isobaric

end ChabautyColeman

end
