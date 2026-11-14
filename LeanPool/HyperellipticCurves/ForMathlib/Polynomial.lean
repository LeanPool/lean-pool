/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.LinearAlgebra.Lagrange

/-!
# General facts about polynomials

Mathlib-gap lemmas about polynomials collected here: behaviour of `Polynomial.reflect` under
`+1` shifts, root multiplicities of reflected/`taylor`-shifted polynomials and of `Xᵈ · q`,
finiteness of the set of `n`-th roots of a ring element, the (finite) sum of root multiplicities
compared with the degree, degree and coefficients of a polynomial written in the monomial basis
indexed by `Fin n`, the two-evaluation criterion for a square factor
(`Polynomial.X_sub_C_sq_dvd_iff`), simplicity of the roots of a squarefree polynomial
(`Polynomial.eval_derivative_ne_zero_of_squarefree`), and the *top-coefficient functional*
`Polynomial.topCoeffMod` of a monic polynomial (the coefficient of `X^(deg u - 1)` in
`p mod u`, the elementary form of the trace form `Tr(p/u')`) with its vanishing and
localization lemmas.
-/

@[expose] public section

namespace Polynomial

/-- **A ring element in a domain has finitely many `n`-th roots** — they are the roots of
`X ^ n - a`, listed by `Polynomial.nthRoots`. -/
theorem finite_setOf_pow_eq {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} (hn : 0 < n)
    (a : R) :
    {y : R | y ^ n = a}.Finite :=
  (nthRoots n a).finite_toSet.subset fun _ hy ↦ by
    simpa only [Multiset.mem_coe, mem_nthRoots hn] using hy

/-- The multiplicity of `0` as a root of `X ^ d · q`, with `q(0) ≠ 0`, is `d`. -/
theorem rootMultiplicity_zero_X_pow_mul {F : Type*} [Field F] (d : ℕ)
    {q : F[X]} (hq : q.coeff 0 ≠ 0) : ((X : F[X]) ^ d * q).rootMultiplicity 0 = d := by
  have hqne : q ≠ 0 := fun h ↦ hq (by rw [h, coeff_zero])
  have h0 : q.rootMultiplicity 0 = 0 :=
    rootMultiplicity_eq_zero fun hr ↦ hq (by rwa [IsRoot, ← coeff_zero_eq_eval_zero] at hr)
  rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero d X_ne_zero) hqne),
    rootMultiplicity_eq_natTrailingDegree', natTrailingDegree_X_pow, h0, add_zero]

section TopCoeff

variable {R : Type*} [CommRing R] {u w p q : R[X]}

/-- The **top-coefficient functional** of a monic polynomial: the coefficient of
`X^(deg u - 1)` in `p mod u`. Classically it is the trace form `Tr(p / u')` — Euler's
identity — but the coefficient description needs neither the trace nor separability of `u`. -/
noncomputable def topCoeffMod (u p : R[X]) : R := (p %ₘ u).coeff (u.natDegree - 1)

@[simp] theorem topCoeffMod_zero (u : R[X]) : topCoeffMod u 0 = 0 := by simp [topCoeffMod]

theorem topCoeffMod_add (p q : R[X]) :
    topCoeffMod u (p + q) = topCoeffMod u p + topCoeffMod u q := by
  simp [topCoeffMod, add_modByMonic]

@[simp] theorem topCoeffMod_neg (p : R[X]) : topCoeffMod u (-p) = -topCoeffMod u p := by
  simp [topCoeffMod, neg_modByMonic]

/-- The functional only sees `p` modulo `u`. -/
theorem topCoeffMod_congr (hu : u.Monic) (h : u ∣ p - q) :
    topCoeffMod u p = topCoeffMod u q := by
  rw [topCoeffMod, topCoeffMod, modByMonic_eq_of_dvd_sub hu h]

theorem topCoeffMod_sum {ι : Type*} (s : Finset ι) (p : ι → R[X]) :
    topCoeffMod u (∑ i ∈ s, p i) = ∑ i ∈ s, topCoeffMod u (p i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, topCoeffMod_add, ih]

/-- The functional is `R`-linear; only additivity and this are needed to expand it along a
chart decomposition of the modulus. -/
theorem topCoeffMod_C_mul (a : R) (p : R[X]) :
    topCoeffMod u (C a * p) = a * topCoeffMod u p := by
  rw [topCoeffMod, topCoeffMod, ← smul_eq_C_mul, smul_modByMonic, coeff_smul, smul_eq_mul]

/-- The functional commutes with base change, the modulus being monic. -/
theorem topCoeffMod_map {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S) (hu : u.Monic)
    (p : R[X]) : topCoeffMod (u.map φ) (p.map φ) = φ (topCoeffMod u p) := by
  rw [topCoeffMod, topCoeffMod, ← Polynomial.map_modByMonic φ hu, coeff_map, hu.natDegree_map]

variable [Nontrivial R]

/-- Below the top degree the functional vanishes — the elementary form of Euler's identity
`Tr(p / u') = 0` for `deg p ≤ deg u - 2`. -/
theorem topCoeffMod_eq_zero_of_natDegree_lt (hu : u.Monic) (hp : p.natDegree + 1 < u.natDegree) :
    topCoeffMod u p = 0 := by
  have hlt : p.degree < u.degree := by
    refine degree_le_natDegree.trans_lt ?_
    rw [degree_eq_natDegree hu.ne_zero]
    exact_mod_cast Nat.lt_of_succ_lt hp
  rw [topCoeffMod, (modByMonic_eq_self_iff hu).mpr hlt]
  exact coeff_eq_zero_of_natDegree_lt (by lia)

/-- The functional separates residues: a nonzero residue modulo `u` is detected by `X^m` for
some `m < deg u`. Choose `m` so that `X^m·(p mod u)` has degree exactly `deg u - 1`; then no
reduction happens and the top coefficient is the leading coefficient of `p mod u`. -/
theorem exists_topCoeffMod_ne_zero (hu : u.Monic) (hp : p %ₘ u ≠ 0) :
    ∃ m < u.natDegree, topCoeffMod u (X ^ m * p) ≠ 0 := by
  have hlt : (p %ₘ u).natDegree < u.natDegree := by
    have h := degree_modByMonic_lt p hu
    rw [degree_eq_natDegree hp, degree_eq_natDegree hu.ne_zero] at h
    exact_mod_cast h
  set d := (p %ₘ u).natDegree with hd
  set m := u.natDegree - 1 - d
  have hsum : d + m = u.natDegree - 1 := by lia
  refine ⟨m, by lia, ?_⟩
  have hcongr : topCoeffMod u (X ^ m * p) = topCoeffMod u (X ^ m * (p %ₘ u)) := by
    refine topCoeffMod_congr hu ?_
    rw [← mul_sub]
    exact (dvd_sub_comm.mp (dvd_modByMonic_sub p u)).mul_left _
  have hdeg : (X ^ m * (p %ₘ u)).degree < u.degree := by
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    rw [degree_X_pow, degree_eq_natDegree hp, degree_eq_natDegree hu.ne_zero, ← hd]
    exact_mod_cast by lia
  rw [hcongr, topCoeffMod, (modByMonic_eq_self_iff hu).mpr hdeg, ← hsum, coeff_X_pow_mul]
  exact leadingCoeff_ne_zero.mpr hp

/-- Reduction modulo a monic product, after multiplying by one of the factors: the second
factor comes out of the reduction. -/
theorem mul_modByMonic_mul (hu : u.Monic) (hw : w.Monic) (q : R[X]) :
    (q * w) %ₘ (u * w) = (q %ₘ u) * w := by
  rcases eq_or_ne u 1 with rfl | hu1
  · rw [one_mul, modByMonic_one, zero_mul,
      (modByMonic_eq_zero_iff_dvd hw).mpr (dvd_mul_left w q)]
  have hr := natDegree_modByMonic_lt q hu hu1
  have hdeg : ((q %ₘ u) * w).degree < (u * w).degree := by
    refine (degree_mul_le _ _).trans_lt ?_
    rw [degree_eq_natDegree (hu.mul hw).ne_zero, hu.natDegree_mul hw,
      degree_eq_natDegree hw.ne_zero]
    have hqd : ((q %ₘ u).degree) ≤ ((u.natDegree - 1 : ℕ) : WithBot ℕ) :=
      degree_le_natDegree.trans (Nat.cast_le.mpr (by lia))
    calc (q %ₘ u).degree + (w.natDegree : WithBot ℕ)
        ≤ ((u.natDegree - 1 : ℕ) : WithBot ℕ) + (w.natDegree : WithBot ℕ) := by gcongr
      _ < ((u.natDegree + w.natDegree : ℕ) : WithBot ℕ) := by
          rw [← Nat.cast_add]
          exact_mod_cast by lia
  refine (div_modByMonic_unique (q /ₘ u) _ (hu.mul hw) ⟨?_, hdeg⟩).2
  conv_rhs => rw [← modByMonic_add_div q u]
  ring

private theorem natDegree_sub_X_pow_lt (hw : w.Monic) (hw0 : 0 < w.natDegree) :
    (w - X ^ w.natDegree).natDegree < w.natDegree := by
  rcases eq_or_ne (w - X ^ w.natDegree) 0 with h0 | h0
  · rw [h0, natDegree_zero]
    exact hw0
  · have hdeg : w.degree = (X ^ w.natDegree : R[X]).degree := by
      rw [degree_X_pow, degree_eq_natDegree hw.ne_zero]
    have h := degree_sub_lt_left hdeg hw.ne_zero
      (by rw [hw.leadingCoeff, monic_X_pow _ |>.leadingCoeff])
    rw [degree_eq_natDegree h0, degree_eq_natDegree hw.ne_zero] at h
    exact_mod_cast h

/-- **The localization lemma**: multiplying by a monic `w` and passing from `u` to `u*w` does
not change the functional. No coprimality is needed — in particular `w = u` is allowed, which
is what the doubling case of Cantor composition requires. Both degenerate cases `u = 1` and
`w = 1` are included: there both sides are `0`. -/
theorem topCoeffMod_mul_monic (hu : u.Monic) (hw : w.Monic) (q : R[X]) :
    topCoeffMod (u * w) (q * w) = topCoeffMod u q := by
  rcases eq_or_ne u 1 with rfl | hu1
  · rw [one_mul, topCoeffMod, topCoeffMod, modByMonic_one,
      (modByMonic_eq_zero_iff_dvd hw).mpr (dvd_mul_left w q)]
    simp
  rcases Nat.eq_zero_or_pos w.natDegree with hw0 | hw0
  · rw [eq_one_of_monic_natDegree_zero hw hw0, mul_one, mul_one]
  have hu0 : 0 < u.natDegree :=
    Nat.pos_of_ne_zero fun h ↦ hu1 (eq_one_of_monic_natDegree_zero hu h)
  have hr := natDegree_modByMonic_lt q hu hu1
  rw [topCoeffMod, mul_modByMonic_mul hu hw, hu.natDegree_mul hw,
    show (q %ₘ u) * w = (q %ₘ u) * (w - X ^ w.natDegree) + (q %ₘ u) * X ^ w.natDegree by
      ring, coeff_add, coeff_mul_X_pow']
  -- only the leading term of `w` reaches the top coefficient
  have hlow : ((q %ₘ u) * (w - X ^ w.natDegree)).natDegree < u.natDegree + w.natDegree - 1 := by
    refine natDegree_mul_le.trans_lt ?_
    lia [natDegree_sub_X_pow_lt hw hw0]
  rw [coeff_eq_zero_of_natDegree_lt hlow, zero_add, ite_eq_left (by lia)]
  congr 1
  lia

end TopCoeff

section SqSub

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {f : R[X]}

/-- The degree of the curve relation of a Mumford datum on `y² = f`:
`deg(v² - f) = max (2 deg v) (deg f)`, the two arguments of the maximum never coinciding
because `deg f` is odd. -/
theorem natDegree_sq_sub_of_odd (hf : Odd f.natDegree) (v : R[X]) :
    (v ^ 2 - f).natDegree = max (2 * v.natDegree) f.natDegree := by
  obtain ⟨g, hg⟩ := hf
  have hsq : (v ^ 2).natDegree = 2 * v.natDegree := natDegree_pow v 2
  rcases lt_trichotomy (2 * v.natDegree) f.natDegree with h | h | h
  · rw [natDegree_sub_eq_right_of_natDegree_lt (by lia)]
    lia
  · lia
  · rw [natDegree_sub_eq_left_of_natDegree_lt (by lia), hsq]
    lia

/-- A polynomial of odd degree is not a square times a square: the two sides of
`A² f = B²` have degrees of opposite parity. -/
theorem sq_mul_ne_sq_of_odd_natDegree (hf0 : f ≠ 0) (hf : Odd f.natDegree) {A B : R[X]}
    (hB : B ≠ 0) : A ^ 2 * f ≠ B ^ 2 := fun h ↦ by
  have hA : A ≠ 0 := fun h0 ↦ hB (by simpa [h0, pow_eq_zero_iff] using h.symm)
  have hdeg := congrArg natDegree h
  rw [natDegree_mul (pow_ne_zero 2 hA) hf0, natDegree_pow, natDegree_pow] at hdeg
  obtain ⟨k, hk⟩ := hf
  lia

end SqSub

/-- `reflect (M+1) p = X · reflect M p` when `deg p ≤ M` (reversing within a longer window shifts
the reflected polynomial up by one). -/
theorem reflect_succ {O : Type*} [CommRing O] {p : O[X]} {M : ℕ} (hp : p.natDegree ≤ M) :
    reflect (M + 1) p = Polynomial.X * reflect M p := by
  ext i
  rw [coeff_reflect]
  rcases i with _ | n
  · rw [coeff_X_mul_zero, revAt_le (Nat.zero_le _), coeff_eq_zero_of_natDegree_lt (by lia)]
  · rw [coeff_X_mul, coeff_reflect]
    rcases le_or_gt n M with hn | hn
    · rw [revAt_le (by lia), revAt_le hn]; congr 1; lia
    · rw [revAt_eq_self_of_lt (by lia), revAt_eq_self_of_lt hn,
        coeff_eq_zero_of_natDegree_lt (by lia), coeff_eq_zero_of_natDegree_lt (by lia)]

/-- The root multiplicity at `0` of a reflected polynomial: `rootMult 0 (reflect N p) = N - deg p`
for `deg p ≤ N` and `p ≠ 0` (the lowest term of `reflect N p` is `leadingCoeff p · X^(N-deg p)`). -/
theorem rootMultiplicity_zero_reflect {R : Type*} [CommRing R] {p : R[X]} (hp : p ≠ 0) {N : ℕ}
    (hN : p.natDegree ≤ N) :
    (reflect N p).rootMultiplicity 0 = N - p.natDegree := by
  have hrefl : reflect N p ≠ 0 := fun h ↦ hp (reflect_eq_zero_iff.mp h)
  rw [rootMultiplicity_eq_natTrailingDegree']
  refine le_antisymm (natTrailingDegree_le_of_ne_zero ?_) (le_natTrailingDegree hrefl fun m hm ↦ ?_)
  · rw [coeff_reflect, revAt_le (by lia), show N - (N - p.natDegree) = p.natDegree by lia]
    exact leadingCoeff_ne_zero.mpr hp
  · rw [coeff_reflect, revAt_le (by lia)]
    exact coeff_eq_zero_of_natDegree_lt (by lia)

/-- The formal derivative commutes with the Taylor shift. -/
theorem derivative_taylor {R : Type*} [CommRing R] (p : R[X]) (r : R) :
    Polynomial.derivative (Polynomial.taylor r p) = Polynomial.taylor r p.derivative := by
  rw [Polynomial.taylor_apply, Polynomial.derivative_comp, Polynomial.taylor_apply]
  simp

/-- Root multiplicities shift under `taylor`. -/
theorem rootMultiplicity_taylor {R : Type*} [CommRing R] (p : R[X]) (r z : R) :
    (taylor r p).rootMultiplicity z = p.rootMultiplicity (z + r) := by
  rw [taylor_apply,
    show (Polynomial.X + Polynomial.C r : R[X])
      = Polynomial.C 1 * Polynomial.X + Polynomial.C r by rw [map_one, one_mul],
    rootMultiplicity_comp_C_mul_X_add_C p 1 r z isUnit_one, one_mul]

/-- The support of `x₀ ↦ rootMultiplicity x₀ h` is contained in the (finite) set of roots of `h`
(needs `classical` in scope for `DecidableEq`). -/
theorem support_rootMultiplicity_subset {κ : Type*} [Field κ] [DecidableEq κ] (h : κ[X]) :
    Function.support (fun x₀ : κ ↦ rootMultiplicity x₀ h) ⊆ ↑h.roots.toFinset := by
  intro x hx
  simp only [Function.mem_support] at hx
  rw [Finset.mem_coe, Multiset.mem_toFinset]
  exact Multiset.count_pos.mp (by rw [count_roots]; exact Nat.pos_of_ne_zero hx)

/-- The sum of root multiplicities over any field is at most the degree. -/
theorem finsum_rootMultiplicity_le {κ : Type*} [Field κ] (h : κ[X]) :
    ∑ᶠ x₀ : κ, rootMultiplicity x₀ h ≤ h.natDegree := by
  classical
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  rw [finsum_eq_finsetSum_of_support_subset _ (support_rootMultiplicity_subset h)]
  calc ∑ x ∈ h.roots.toFinset, rootMultiplicity x h
      = ∑ x ∈ h.roots.toFinset, h.roots.count x :=
        Finset.sum_congr rfl fun x _ ↦ (count_roots h).symm
    _ = Multiset.card h.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ h.natDegree := card_roots' h

section Coeffs

/-- The coefficients of a polynomial written in the monomial basis indexed by `Fin n` are
the coefficients it is written with. -/
theorem coeff_sum_C_mul_X_pow {R : Type*} [Semiring R] {n : ℕ} (c : Fin n → R) (i : Fin n) :
    (∑ j : Fin n, C (c j) * X ^ (j : ℕ)).coeff (i : ℕ) = c i := by
  rw [finsetSum_coeff, Finset.sum_eq_single i
    (fun j _ hj ↦ by
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right fun h ↦ hj (Fin.val_injective h.symm), mul_zero])
    fun h ↦ absurd (Finset.mem_univ i) h]
  simp

/-- The `i`-th coefficient of a polynomial displaced by coordinates `c`, after base change:
the displacement contributes exactly `φ (c i)`. -/
theorem coeff_map_add_sum_C_mul_X_pow {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (p : R[X]) (c : Fin n → R) (i : Fin n) :
    ((p + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).map φ).coeff (i : ℕ)
      = (p.map φ).coeff (i : ℕ) + φ (c i) := by
  rw [Polynomial.map_add, coeff_add, Polynomial.map_sum,
    Finset.sum_congr rfl fun j _ ↦ (by rw [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X] :
      ((C (c j) * X ^ (j : ℕ)).map φ) = C (φ (c j)) * X ^ (j : ℕ)),
    coeff_sum_C_mul_X_pow]

end Coeffs

/-- The degree of a product of powers of monic linear factors is the total multiplicity.
(The exponent-free case is closed by `simp`.) -/
theorem natDegree_prod_X_sub_C_pow {R : Type*} [CommRing R] [Nontrivial R] {ι : Type*}
    (s : Finset ι) (x : ι → R) (k : ι → ℕ) :
    (∏ i ∈ s, (X - C (x i)) ^ k i).natDegree = ∑ i ∈ s, k i := by
  rw [natDegree_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C (x i)).pow (k i)]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [(monic_X_sub_C (x i)).natDegree_pow, natDegree_X_sub_C, mul_one]

/-- If a product of powers of monic linear factors with nonzero exponents is squarefree, then
every exponent is `1` and the roots are pairwise distinct. -/
theorem eq_one_and_inj_of_squarefree_prod_X_sub_C_pow {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} {s : Finset ι} {x : ι → R} {k : ι → ℕ} (hk : ∀ i ∈ s, k i ≠ 0)
    (hsq : Squarefree (∏ i ∈ s, (X - C (x i)) ^ k i)) :
    (∀ i ∈ s, k i = 1) ∧ ∀ i ∈ s, ∀ j ∈ s, x i = x j → i = j := by
  classical
  have key {a : R} (h : (X - C a) * (X - C a) ∣ ∏ i ∈ s, (X - C (x i)) ^ k i) : False :=
    not_isUnit_X_sub_C _ (hsq _ h)
  have h1 i (hi : i ∈ s) : k i = 1 := by
    by_contra hne
    refine key (a := x i) ?_
    rw [← sq]
    exact (pow_dvd_pow _ ((Nat.two_le_iff _).mpr ⟨hk i hi, hne⟩)).trans
      (Finset.dvd_prod_of_mem _ hi)
  refine ⟨h1, fun i hi j hj hxij ↦ ?_⟩
  by_contra hne
  refine key (a := x i) ?_
  rw [← Finset.mul_prod_erase _ _ hi, h1 i hi, pow_one]
  refine mul_dvd_mul dvd_rfl ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨fun h ↦ hne h.symm, hj⟩),
    h1 j hj, pow_one, hxij]
  exact dvd_mul_right _ _

open Function in
/-- **Interpolation through unit-separated points**: over any commutative ring, values
prescribed at points whose differences are units are attained by a polynomial of degree below
`∏ (X - C (x i))`. Unit separation makes the linear factors pairwise comaximal, so the
Chinese remainder theorem applies. -/
theorem exists_degree_lt_eval_eq {R : Type*} [CommRing R] [Nontrivial R] {ι : Type*} [Fintype ι]
    {x : ι → R} (hx : ∀ i j, i ≠ j → IsUnit (x i - x j)) (y : ι → R) :
    ∃ w : R[X], w.degree < (∏ i, (X - C (x i))).degree ∧ ∀ i, w.eval (x i) = y i := by
  set u : R[X] := ∏ i, (X - C (x i))
  have hum : u.Monic := monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)
  have hpair : Pairwise (IsCoprime on fun i : ι ↦ Ideal.span {X - C (x i)}) := fun i j hij ↦ by
    rw [onFun, Ideal.isCoprime_span_singleton_iff]
    exact isCoprime_X_sub_C_of_isUnit_sub (hx i j hij)
  obtain ⟨w, hw⟩ := Ideal.exists_forall_sub_mem_ideal hpair fun i ↦ C (y i)
  refine ⟨w %ₘ u, degree_modByMonic_lt w hum, fun i ↦ ?_⟩
  have hu0 : u.eval (x i) = 0 :=
    eval_eq_zero_of_dvd_of_eval_eq_zero (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
      (by rw [eval_sub, eval_X, eval_C, sub_self])
  have heq := congrArg (Polynomial.eval (x i)) (modByMonic_add_div w u)
  rw [eval_add, eval_mul, hu0, zero_mul, add_zero] at heq
  have h0 := dvd_iff_isRoot.mp (Ideal.mem_span_singleton.mp (hw i))
  rw [IsRoot, eval_sub, eval_C] at h0
  exact heq.trans (sub_eq_zero.mp h0)

/-- Base change preserves a strict degree inequality below a monic polynomial: the larger
degree is unchanged, the smaller one can only drop. -/
theorem Monic.degree_map_lt_degree_map {R S : Type*} [Semiring R] [Semiring S] [Nontrivial S]
    {p q : R[X]} (hq : q.Monic) (φ : R →+* S) (h : p.degree < q.degree) :
    (p.map φ).degree < (q.map φ).degree :=
  degree_map_le.trans_lt (h.trans_eq (hq.degree_map φ).symm)

/-- Two polynomials agreeing at more points than the degree of their difference are equal.
Thin adapter (NOT Mathlib-bound) over `Polynomial.eq_of_degree_sub_lt_of_eval_index_eq`,
in the `Function.Injective`/`Fintype` currency the call sites spend. -/
theorem eq_of_degree_sub_lt_card_of_eval_eq {R : Type*} [CommRing R] [IsDomain R] {p q : R[X]}
    {ι : Type*} [Fintype ι] {x : ι → R} (hx : Function.Injective x)
    (heval : ∀ i, p.eval (x i) = q.eval (x i)) (hdeg : (p - q).degree < Fintype.card ι) :
    p = q :=
  Polynomial.eq_of_degree_sub_lt_of_eval_index_eq Finset.univ hx.injOn
    (by rw [Finset.card_univ]; exact hdeg) fun i _ ↦ heval i

/-- Scaling a nonzero polynomial to be monic does not change what it divides. -/
theorem mul_leadingCoeff_inv_dvd_iff {K : Type*} [Field K] {u w : K[X]} (hu : u ≠ 0) :
    u * C u.leadingCoeff⁻¹ ∣ w ↔ u ∣ w :=
  (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
    (inv_ne_zero (leadingCoeff_ne_zero.mpr hu)))).mul_right_dvd

/-- A monic polynomial dividing a regular constant multiple divides the polynomial itself. -/
theorem Monic.dvd_of_C_mul_dvd {R : Type*} [CommRing R] [IsDomain R] {U W : R[X]} {a : R}
    (hU : U.Monic) (ha : a ≠ 0) (h : U ∣ C a * W) : U ∣ W := by
  rw [← modByMonic_eq_zero_iff_dvd hU] at h ⊢
  rw [show (C a * W : R[X]) = a • W by rw [smul_eq_C_mul], smul_modByMonic] at h
  have h2 : ∀ i, a * (W %ₘ U).coeff i = 0 := fun i ↦ by
    have := congrArg (fun p ↦ Polynomial.coeff p i) h
    simpa [coeff_smul, smul_eq_mul] using this
  ext i
  rw [coeff_zero]
  exact (mul_eq_zero.mp (h2 i)).resolve_left ha

/-- A unit `2` of the base ring stays a unit in the polynomial ring, as the constant `C 2`. -/
theorem isUnit_two {R : Type*} [CommRing R] (h : IsUnit (2 : R)) : IsUnit (2 : R[X]) := by
  rw [← map_ofNat (C : R →+* R[X]) 2]
  exact h.map C

/-- **A square factor `(X - a)²` is detected by two evaluations**: the polynomial and its
derivative both vanish at `a`. -/
theorem X_sub_C_sq_dvd_iff {R : Type*} [CommRing R] {p : R[X]} {a : R} :
    (X - C a) ^ 2 ∣ p ↔ p.eval a = 0 ∧ p.derivative.eval a = 0 := by
  refine ⟨fun ⟨q, hq⟩ ↦ ⟨by simp [hq], by simp [hq, derivative_mul, derivative_pow]⟩,
    fun ⟨h0, h1⟩ ↦ ?_⟩
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr h0
  have hqa : q.eval a = 0 := by
    simpa [derivative_mul, h1] using (congrArg (fun r ↦ (derivative r).eval a) hq).symm
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hqa
  exact ⟨r, by rw [hq, hr]; ring⟩

/-- **The reflected point lies on the curve**: if `A = Z² · g^rev(A)` for a polynomial `g` of
degree `2n + 1` and nonzero `A`, `Z` in an extension field, then `(Z⁻¹ A⁻ⁿ)² = g(A⁻¹)`. -/
theorem sq_inv_mul_inv_pow_eq_eval₂_inv {K L : Type*} [Field K] [Field L] [Algebra K L]
    {g : K[X]} {n : ℕ} (hdeg : g.natDegree = 2 * n + 1) {A Z : L} (hA : A ≠ 0) (hZ : Z ≠ 0)
    (hAeq : A = Z ^ 2 * eval₂ (algebraMap K L) A g.reverse) :
    (Z⁻¹ * A⁻¹ ^ n) ^ 2 = eval₂ (algebraMap K L) A⁻¹ g := by
  let : Invertible A := invertibleOfNonzero hA
  have hrev : g.reverse = reflect (2 * n + 1) g := by rw [Polynomial.reverse, hdeg]
  have hrefl := eval₂_reflect_mul_pow (algebraMap K L) A (2 * n + 1) (reflect (2 * n + 1) g)
    (natDegree_reflect_le.trans (max_le le_rfl hdeg.le))
  rw [reflect_reflect, invOf_eq_inv, ← hrev] at hrefl
  refine mul_right_cancel₀ (mul_ne_zero (pow_ne_zero (2 * n + 1) hA) (pow_ne_zero 2 hZ)) ?_
  calc (Z⁻¹ * A⁻¹ ^ n) ^ 2 * (A ^ (2 * n + 1) * Z ^ 2)
      = (A⁻¹ * A) ^ (2 * n) * (Z⁻¹ * Z) ^ 2 * A := by ring
    _ = A := by
        rw [inv_mul_cancel₀ hA, inv_mul_cancel₀ hZ, one_pow, one_pow, one_mul, one_mul]
    _ = eval₂ (algebraMap K L) A⁻¹ g * (A ^ (2 * n + 1) * Z ^ 2) := by
        rw [← mul_assoc, hrefl]
        linear_combination hAeq

variable {K : Type*} [Field K]

/-- A root of a squarefree polynomial is a simple root. -/
theorem eval_derivative_ne_zero_of_squarefree {f : K[X]} (hsq : Squarefree f) {r : K}
    (hr : f.eval r = 0) : f.derivative.eval r ≠ 0 := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr
  intro h0
  have hd : f.derivative.eval r = q.eval r := by
    rw [hq, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp
  rw [hd] at h0
  obtain ⟨p, hp⟩ := dvd_iff_isRoot.mpr h0
  exact not_isUnit_X_sub_C r (hsq (X - C r) ⟨p, by rw [hq, hp]; ring⟩)

/-- Coprimality over an algebraically closed field from disjoint zero sets. -/
theorem isCoprime_of_forall_eval_ne_zero [IsAlgClosed K] {p q : K[X]} (hq : q ≠ 0)
    (h : ∀ x, p.eval x = 0 → q.eval x ≠ 0) : IsCoprime p q := by
  classical
  by_contra hcop
  rw [← EuclideanDomain.gcd_isUnit_iff] at hcop
  have hg0 : EuclideanDomain.gcd p q ≠ 0 := fun h0 ↦
    hq (EuclideanDomain.gcd_eq_zero_iff.mp h0).2
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (EuclideanDomain.gcd p q)
    (fun hdeg ↦ hcop (isUnit_iff_degree_eq_zero.mpr hdeg))
  exact h x (eval_eq_zero_of_dvd_of_eval_eq_zero (EuclideanDomain.gcd_dvd_left p q) hx)
    (eval_eq_zero_of_dvd_of_eval_eq_zero (EuclideanDomain.gcd_dvd_right p q) hx)

/-- Coprimality with a linear factor from an invertible value. Over a ring the value need not
be a unit on the nose — this is the form that applies after localizing to make it one. -/
theorem isCoprime_X_sub_C_of_isUnit_eval {R : Type*} [CommRing R] {P : R[X]} {x : R}
    (h : IsUnit (P.eval x)) : IsCoprime P (X - C x) := by
  obtain ⟨Q, hQ⟩ := X_sub_C_dvd_sub_C_eval (a := x) (p := P)
  obtain ⟨c, hc⟩ := h.exists_left_inv
  have hc' : (C c : R[X]) * C (P.eval x) = 1 := by rw [← C_mul, hc, map_one]
  exact ⟨C c, -(C c * Q), by linear_combination (C c : R[X]) * hQ + hc'⟩

/-- Coprimality with a linear factor from a nonzero evaluation. -/
theorem isCoprime_X_sub_C_of_eval_ne_zero {P : K[X]} {x : K} (h : P.eval x ≠ 0) :
    IsCoprime P (X - C x) := isCoprime_X_sub_C_of_isUnit_eval h.isUnit

/-- A polynomial vanishing at two distinct points is divisible by the pair. -/
theorem pair_dvd_of_eval {p : K[X]} {a c : K} (hne : a ≠ c) (h₁ : p.eval a = 0)
    (h₂ : p.eval c = 0) : (X - C a) * (X - C c) ∣ p :=
  IsCoprime.mul_dvd
    (isCoprime_X_sub_C_of_eval_ne_zero (by simpa using sub_ne_zero.mpr (Ne.symm hne)))
    (dvd_iff_isRoot.mpr h₁) (dvd_iff_isRoot.mpr h₂)

variable {S : Type*} [CommRing S] [Nontrivial S]

/-- Two monic polynomials of the same degree `n` differ by their lower-order coefficients:
`P = Q + ∑_{i<n} (P - Q)ᵢ Xⁱ`. -/
theorem Monic.eq_add_sum_coeff_sub {P Q : Polynomial S} {n : ℕ}
    (hP : P.Monic) (hQ : Q.Monic) (hPn : P.natDegree = n) (hQn : Q.natDegree = n) :
    P = Q + ∑ i : Fin n, C ((P - Q).coeff (i : ℕ)) * X ^ (i : ℕ) := by
  have hdP : P.degree = (n : WithBot ℕ) := by rw [degree_eq_natDegree hP.ne_zero, hPn]
  have hdQ : Q.degree = (n : WithBot ℕ) := by rw [degree_eq_natDegree hQ.ne_zero, hQn]
  have hdeg : (P - Q).degree < (n : WithBot ℕ) := by
    have h := degree_sub_lt_left (hdP.trans hdQ.symm) hP.ne_zero
      (by rw [hP.leadingCoeff, hQ.leadingCoeff])
    rwa [hdP] at h
  suffices h : P - Q = ∑ i : Fin n, C ((P - Q).coeff (i : ℕ)) * X ^ (i : ℕ) by
    linear_combination h
  by_cases hD : P - Q = 0
  · rw [hD]
    exact (Finset.sum_eq_zero fun i _ ↦ by simp).symm
  · have hlt : (P - Q).natDegree < n := (natDegree_lt_iff_degree_lt hD).mpr hdeg
    calc P - Q = ∑ i ∈ Finset.range n, monomial i ((P - Q).coeff i) :=
          as_sum_range' _ n hlt
      _ = ∑ i : Fin n, C ((P - Q).coeff (i : ℕ)) * X ^ (i : ℕ) := by
          rw [Finset.sum_range fun i ↦ monomial i ((P - Q).coeff i)]
          exact Finset.sum_congr rfl fun i _ ↦ (C_mul_X_pow_eq_monomial).symm

/-- Over any commutative ring, a multiple of a monic polynomial of smaller degree is
zero. -/
theorem Monic.eq_zero_of_dvd_of_degree_lt {R : Type*} [CommRing R] {p q : R[X]}
    (hp : p.Monic) (h₁ : p ∣ q) (h₂ : q.degree < p.degree) : q = 0 := by
  obtain ⟨c, rfl⟩ := h₁
  rcases eq_or_ne c 0 with rfl | hc
  · rw [mul_zero]
  refine absurd h₂ (not_lt.mpr ?_)
  have hd : (p * c).degree = p.degree + c.degree :=
    degree_mul' (by rw [hp.leadingCoeff, one_mul]; exact leadingCoeff_ne_zero.mpr hc)
  rw [hd]
  exact le_add_of_nonneg_right (zero_le_degree_iff.mpr hc)

end Polynomial

end
