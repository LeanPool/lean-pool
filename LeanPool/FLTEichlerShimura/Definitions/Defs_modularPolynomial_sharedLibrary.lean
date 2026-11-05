/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

/-
Extracted from the proof of Prove2Me node ModularCurve.exists_phiIrreducible
(85c90cda-9166-5cf9-a245-c0442a624673), by Claude (2026-09-05), submission
25e72fb1-74d8-5410-94ca-a5536b5cd327; locally adapted.

Additional helpers extracted from the rational and arbitrary-field proofs of
`ModularCurve.minpoly_jqN_map_eq_prod_slots`, `ModularCurve.jqN_prime_not_mem_full`,
`ModularCurve.minpoly_jqNModC_map_eq_prod_slots`, and `ModularCurve.jqNModC_prime_not_mem_fullC`.
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_JqCoeff
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_PhiGen

public import Mathlib.NumberTheory.Cyclotomic.Basic

import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_coeffEmb_qExpand
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_dedekindPsi_prime
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_of_mul_eq_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_order_jqModC
import Mathlib.Algebra.Order.Algebra

/-!
# Shared modular-polynomial and Laurent-series helpers

`ModularCurve.W1.TS` is the Laurent series `j(u q^e)` over an arbitrary field, including
positive characteristic. Its coefficients recover the parameters, and its substitution
lemmas describe rescaling and expansion of `q`. Over a ℚ-algebra, `TS_eq_coeffEmb` identifies
it with the coefficientwise image of the rational series.

`ModularCurve.W1.phiAtSeed` specializes the first variable of a modular polynomial.
The accompanying lemmas preserve monicity and degree and transport specialization
and roots along ring homomorphisms.

Further helpers identify the rational and arbitrary-field series, specialize modular equations,
and count primitive slots, whose number is Dedekind's ψ function. These are shared by the
minimal-polynomial and prime-level nonmembership proofs.
-/

@[expose] public noncomputable section publicSection

namespace ModularCurve.W1

variable {K : Type*} [Field K]

/-- The twisted and expanded `j`-series obtained by applying `qTwist u` and then `qExpand e`. -/
def TS (K : Type*) [Field K] (e : ℕ) [NeZero e] (u : Kˣ) : LaurentSeries K :=
  qExpand K e (qTwist u (jqModC K))

private theorem TS_coeff_mul (e : ℕ) [NeZero e] (u : Kˣ) (n : ℤ) :
    (TS K e u).coeff ((e : ℤ) * n) = ((u ^ n : Kˣ) : K) * (jqModC K).coeff n := by
  rw [TS, qExpand_coeff_mul, qTwist_coeff]

private theorem TS_coeff_of_not_dvd (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ}
    (hk : ¬ (e : ℤ) ∣ k) :
    (TS K e u).coeff k = 0 := by
  exact qExpand_coeff_of_not_dvd (R := K) (N := e) _ hk

theorem TS_coeff_neg (e : ℕ) [NeZero e] (u : Kˣ) :
    (TS K e u).coeff (-(e : ℤ)) = ((u⁻¹ : Kˣ) : K) := by
  have h := TS_coeff_mul (K := K) e u (-1)
  rw [mul_neg_one] at h
  rw [h, coeff_jqModC_neg_one, mul_one, zpow_neg_one]

private theorem coeff_jqModC_of_lt {n : ℤ} (hn : n < -1) : (jqModC K).coeff n = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [order_jqModC]
  exact hn

theorem TS_coeff_of_lt (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : k < -(e : ℤ)) :
    (TS K e u).coeff k = 0 := by
  by_cases hd : (e : ℤ) ∣ k
  · obtain ⟨n, rfl⟩ := hd
    have he : (0 : ℤ) < e := by grind
    have hn : n < -1 := by
      by_contra hcon
      have : -(e : ℤ) ≤ (e : ℤ) * n := by nlinarith
      grind
    rw [TS_coeff_mul, coeff_jqModC_of_lt hn, mul_zero]
  · exact TS_coeff_of_not_dvd e u hd

theorem TS_ne_zero (e : ℕ) [NeZero e] (u : Kˣ) : TS K e u ≠ 0 := by
  intro h
  have := TS_coeff_neg (K := K) e u
  rw [h, HahnSeries.coeff_zero] at this
  exact (u⁻¹).ne_zero this.symm

theorem TS_injective {e e' : ℕ} [NeZero e] [NeZero e'] {u u' : Kˣ}
    (h : TS K e u = TS K e' u') :
    e = e' ∧ u = u' := by
  have key : ∀ {a a' : ℕ} [NeZero a] [NeZero a'] {v v' : Kˣ}, TS K a v = TS K a' v' → a ≤ a' := by
    intro a a' _ _ v v' hh
    by_contra hlt
    push Not at hlt
    have h1 := TS_coeff_neg (K := K) a v
    have hlt' : (-(a : ℤ)) < -(a' : ℤ) := by grind
    have h2 : (TS K a' v').coeff (-(a : ℤ)) = 0 := TS_coeff_of_lt a' v' hlt'
    rw [← hh, h1] at h2
    exact (v⁻¹).ne_zero h2
  have hee : e = e' := le_antisymm (key h) (key h.symm)
  subst hee
  refine ⟨rfl, ?_⟩
  have h1 := TS_coeff_neg (K := K) e u
  rw [h, TS_coeff_neg] at h1
  exact (inv_injective (Units.val_injective h1)).symm

theorem qTwist_TS (v : Kˣ) (e : ℕ) [NeZero e] (u : Kˣ) :
    qTwist v (TS K e u) = TS K e (v ^ (e : ℤ) * u) := by
  rw [TS, qTwist_qExpand, qTwist_qTwist]; rfl

theorem qExpand_TS (m e : ℕ) [NeZero m] [NeZero e] (u : Kˣ) :
    qExpand K m (TS K e u) = TS K (m * e) u := by
  rw [TS, qExpand_qExpand]; rfl

theorem TS_congr {e e' : ℕ} [NeZero e] [NeZero e'] (h : e = e') (u : Kˣ) :
    TS K e u = TS K e' u := by
  subst h; rfl

theorem TS_eq_coeffEmb [Algebra ℚ K] (e : ℕ) [NeZero e] (u : Kˣ) :
    TS K e u = qExpand K e (qTwist u (coeffEmb K jq)) := by
  have h : coeffEmb K jq = jqModC K := by
    rw [coeffEmb, ← jqModC_rat]
    exact map_jqModC (algebraMap ℚ K)
  rw [TS, h]

/-- The polynomial in the second variable obtained by specializing the modular polynomial's first
variable at the supplied seed. -/
def phiAtSeed {R : Type*} [CommRing R] {n : ℕ} [NeZero n] (data : ModularPolynomialData n) (x : R) :
    Polynomial R :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)

theorem phiAtSeed_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) (f : R →+* S) :
    (phiAtSeed data x).map f = phiAtSeed data (f x) := by
  rw [phiAtSeed, phiAtSeed, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact RingHom.ext_int _ _
  · simp

theorem phiAtSeed_monic {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) : (phiAtSeed data x).Monic :=
  data.monic.map _

theorem phiAtSeed_natDegree {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) : (phiAtSeed data x).natDegree = dedekindPsi n := by
  rw [phiAtSeed, data.monic.natDegree_map, data.natDegree_eq]

theorem phiAtSeed_eval_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x y : R) (f : R →+* S) (h : (phiAtSeed data x).eval y = 0) :
    (phiAtSeed data (f x)).eval (f y) = 0 := by
  rw [← phiAtSeed_map, Polynomial.eval_map, Polynomial.eval₂_hom, h, map_zero]


end ModularCurve.W1

namespace ModularCurve.ModularPolynomialHelpers

open W1

variable {K : Type*} [Field K]

/-! ## Series identities and roots of unity -/

private theorem jqNModC_eq_TS (d : ℕ) [NeZero d] : jqNModC K d = TS K d 1 := by
  rw [jqNModC, TS, qTwist_one_apply]

theorem qExpand_jqNModC (A d : ℕ) [NeZero A] [NeZero d] :
    qExpand K A (jqNModC K d) = TS K (A * d) 1 := by
  rw [jqNModC_eq_TS, qExpand_TS]

theorem qExpand_jqModC_eq_TS (A : ℕ) [NeZero A] : qExpand K A (jqModC K) = TS K A 1 := by
  rw [TS, qTwist_one_apply]

theorem isPrimitiveRoot_pow_div {N : ℕ} [NeZero N] {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) N)
    {p : ℕ} (hpN : p ∣ N) : IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p := by
  have hN : N ≠ 0 := NeZero.ne N
  have hd0 : N / p ≠ 0 := by
    intro h0
    have hc := Nat.div_mul_cancel hpN
    grind
  have h := hζ.pow_of_dvd hd0 (Nat.div_dvd_of_dvd hpN)
  rw [Nat.div_div_self hpN hN] at h
  rwa [← Units.val_pow_eq_pow_val] at h

theorem TS_congr' {e e' : ℕ} [NeZero e] [NeZero e'] {u u' : Kˣ} (he : e = e')
    (hu : u = u') : TS K e u = TS K e' u' := by
  subst he
  rw [hu]

theorem jqNModC_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    jqNModC K n = jqNModC K m := by
  subst h
  rfl

section RationalCoefficients

variable [Algebra ℚ K]

theorem iota_jqN (N d : ℕ) [NeZero N] [NeZero d] :
    coeffEmb K (qExpand ℚ N (jqN d)) = TS K (N * d) 1 := by
  rw [jqN, coeffEmb_qExpand, coeffEmb_qExpand,
    qExpand_qExpand, TS_eq_coeffEmb, qTwist_one_apply]

private theorem exists_isPrimitiveRoot_cyclotomicField (N : ℕ) [NeZero N] :
    ∃ z : CyclotomicField N ℚ, IsPrimitiveRoot z N := by
  have : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  have : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  exact IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField N ℚ) (Set.mem_singleton N)
    (NeZero.ne N)

/-- A chosen primitive `N`th root of unity in the cyclotomic field, bundled as a unit. -/
@[no_expose] def cycUnit (N : ℕ) [NeZero N] : (CyclotomicField N ℚ)ˣ :=
  ((exists_isPrimitiveRoot_cyclotomicField N).choose_spec.isUnit (NeZero.ne N)).unit

theorem cycUnit_spec (N : ℕ) [NeZero N] :
    IsPrimitiveRoot ((cycUnit N : (CyclotomicField N ℚ)ˣ) : CyclotomicField N ℚ) N := by
  rw [cycUnit, IsUnit.unit_spec]
  exact (exists_isPrimitiveRoot_cyclotomicField N).choose_spec

theorem jqN_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) : jqN n = jqN m := by
  subst h
  rfl

end RationalCoefficients

/-! ## Specialization of modular equations -/

theorem phiAtSeed_jqNModC_eval {R : Type*} [CommRing R] (n : ℕ) [NeZero n]
    (data : ModularPolynomialData n)
    (d : ℕ) [NeZero d] : (phiAtSeed data (jqNModC R d)).eval (jqNModC R (d * n)) = 0 := by
  have h := data.eval_jqNModC_mul_eq_zero R d
  rw [phiAtSeed, Polynomial.eval_map]
  convert h using 2
  exact Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

theorem phiAtSeed_jqNModC_eval_symm {R : Type*} [CommRing R] (n : ℕ) [NeZero n]
    (data : ModularPolynomialData n)
    (hsymm : EvalSymm data.Φ) (d : ℕ) [NeZero d] :
    (phiAtSeed data (jqNModC R (d * n))).eval (jqNModC R d) = 0 := by
  have h := data.eval_jqNModC_of_mul_eq_zero hsymm R d
  rw [phiAtSeed, Polynomial.eval_map]
  convert h using 2
  exact Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

theorem aeval_intermediateField_eq_zero {F₀ L : Type*} [Field F₀] [Field L]
    [Algebra F₀ L] {E : IntermediateField F₀ L} {P : Polynomial F₀} {x : E}
    (h : Polynomial.aeval (E.val x) P = 0) : Polynomial.aeval x P = 0 := by
  have h1 := Polynomial.aeval_algHom_apply E.val x P
  rw [h] at h1
  have h2 : E.val (Polynomial.aeval x P) = E.val 0 := by rw [← h1, map_zero]
  exact RingHom.injective (E.val : E →+* L) h2

theorem phiAtSeed_eval_of_injective {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    [NeZero n] (data : ModularPolynomialData n) (x y : R) (f : R →+* S)
    (hf : Function.Injective f) (h : (phiAtSeed data (f x)).eval (f y) = 0) :
    (phiAtSeed data x).eval y = 0 := by
  rw [← phiAtSeed_map, Polynomial.eval_map, Polynomial.eval₂_hom] at h
  exact (injective_iff_map_eq_zero f).mp hf _ h

private theorem phiAtSeed_jq_eval (n : ℕ) [NeZero n] (data : ModularPolynomialData n) :
    (phiAtSeed data jq).eval (jqN n) = 0 := by
  have h := data.eval_eq_zero
  rw [phiAtSeed, Polynomial.eval_map]
  convert h using 2
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact RingHom.ext_int _ _
  · simp [evalAtJ_X]

theorem phiAtSeed_jqN_eval (n : ℕ) [NeZero n] (data : ModularPolynomialData n) (M : ℕ) [NeZero M] :
    (phiAtSeed data (jqN M)).eval (jqN (M * n)) = 0 := by
  have h := phiAtSeed_eval_map data jq (jqN n) (qExpand ℚ M) (phiAtSeed_jq_eval n data)
  rwa [jqN, qExpand_qExpand] at h

theorem phiAtSeed_eval_symm {n : ℕ} [NeZero n] (data : ModularPolynomialData n)
    (hsym : EvalSymm data.Φ) (x y : LaurentSeries ℚ) :
    (phiAtSeed data x).eval y = (phiAtSeed data y).eval x := by
  have hhom : ∀ z : LaurentSeries ℚ,
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) z
        = (Polynomial.aeval (R := ℤ) z).toRingHom := by
    intro z
    refine Polynomial.ringHom_ext' ?_ ?_
    · exact RingHom.ext_int _ _
    · simp [Polynomial.coe_eval₂RingHom]
  rw [phiAtSeed, phiAtSeed, Polynomial.eval_map, Polynomial.eval_map, hhom x, hhom y]
  exact hsym x y

/-! ## Counting primitive slots -/

/-- Count residues `b` modulo `d` for which the triple `(n / d, b, d)` is primitive. -/
def slotAt (n d : ℕ) : ℕ :=
  ((Finset.range d).filter fun b => Nat.gcd (Nat.gcd (n / d) b) d = 1).card

/-- The total number of primitive coset slots, summed over divisors of the level. -/
def slots (n : ℕ) : ℕ := ∑ d ∈ n.divisors, slotAt n d

private theorem slotCond_iff (x d b : ℕ) :
    Nat.gcd (Nat.gcd x b) d = 1 ↔ Nat.Coprime (Nat.gcd x d) b := by
  grind

private theorem gcd_eq_of_modEq {a b n : ℕ} (h : a ≡ b [MOD n]) :
    Nat.gcd n a = Nat.gcd n b := by
  have h' : a % n = b % n := h
  rw [Nat.gcd_rec n a, Nat.gcd_rec n b, h']

private theorem slotCond_mod_iff (x d b : ℕ) :
    Nat.Coprime (Nat.gcd x d) (b % d) ↔ Nat.Coprime (Nat.gcd x d) b := by
  unfold Nat.Coprime
  rw [gcd_eq_of_modEq ((Nat.mod_modEq b d).of_dvd (Nat.gcd_dvd_right x d))]

private theorem slotAt_one (n : ℕ) : slotAt n 1 = 1 := by
  unfold slotAt
  simp [Nat.gcd_one_right]

private theorem slotAt_self (n : ℕ) (hn : 0 < n) : slotAt n n = n := by
  unfold slotAt
  simp [Nat.div_self hn, Nat.gcd_one_left]

private theorem slotAt_prime_pow_mid {p : ℕ} (hp : p.Prime) {i k : ℕ} (hi0 : 0 < i)
    (hik : i < k) : slotAt (p ^ k) (p ^ i) = Nat.totient (p ^ i) := by
  unfold slotAt
  rw [Nat.totient_eq_card_coprime]
  congr 1
  refine Finset.filter_congr fun b _ => ?_
  rw [slotCond_iff]
  constructor
  · intro h
    have hpg : p ∣ Nat.gcd (p ^ k / p ^ i) (p ^ i) := by
      refine Nat.dvd_gcd ?_ (dvd_pow_self p hi0.ne')
      rw [Nat.pow_div hik.le hp.pos]
      exact dvd_pow_self p (by omega)
    exact Nat.Coprime.pow_left i (Nat.Coprime.coprime_dvd_left hpg h)
  · intro h
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) h

private theorem slots_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    slots (p ^ (k + 1)) = p ^ (k + 1) + p ^ k := by
  unfold slots
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ]
  have hrest : ∀ x ∈ Finset.range (k + 1),
      slotAt (p ^ (k + 1)) (p ^ x) = Nat.totient (p ^ x) := by
    intro x hx
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · rw [pow_zero, slotAt_one, Nat.totient_one]
    · exact slotAt_prime_pow_mid hp hx0 (Finset.mem_range.mp hx)
  rw [Finset.sum_congr rfl hrest, slotAt_self _ (pow_pos hp.pos _),
    ← Nat.sum_divisors_prime_pow (f := Nat.totient) hp, Nat.sum_totient, Nat.add_comm]

private theorem dedekindPsi_prime_pow' {p : ℕ} (hp : p.Prime) (k : ℕ) :
    dedekindPsi (p ^ (k + 1)) = p ^ (k + 1) + p ^ k := by
  unfold dedekindPsi
  have hfil : Finset.filter (fun d => Squarefree d) (p ^ (k + 1)).divisors = {1, p} := by
    ext x
    simp only [Finset.mem_filter, Nat.mem_divisors_prime_pow hp, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨j, -, rfl⟩, hsq⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · grind
      · obtain rfl : j = 1 := ((Nat.squarefree_pow_iff hp.ne_one hj0.ne').mp hsq).2
        grind
    · rintro (rfl | rfl)
      · exact ⟨⟨0, Nat.zero_le _, (pow_zero p).symm⟩, squarefree_one⟩
      · exact ⟨⟨1, by omega, (pow_one _).symm⟩, hp.prime.squarefree⟩
  rw [hfil, Finset.sum_pair hp.one_lt.ne, Nat.div_one, pow_succ,
    Nat.mul_div_cancel _ hp.pos]

private theorem slotAt_mul (M M' d₁ d₂ : ℕ) (hM : M ≠ 0) (hM' : M' ≠ 0)
    (hco : Nat.Coprime M M') (hd₁ : d₁ ∣ M) (hd₂ : d₂ ∣ M') :
    slotAt (M * M') (d₁ * d₂) = slotAt M d₁ * slotAt M' d₂ := by
  have hd₁0 : 0 < d₁ :=
    Nat.pos_of_ne_zero (by rintro rfl; exact hM (Nat.eq_zero_of_zero_dvd hd₁))
  have hd₂0 : 0 < d₂ :=
    Nat.pos_of_ne_zero (by rintro rfl; exact hM' (Nat.eq_zero_of_zero_dvd hd₂))
  have hcod : Nat.Coprime d₁ d₂ :=
    Nat.Coprime.coprime_dvd_left hd₁ (Nat.Coprime.coprime_dvd_right hd₂ hco)
  have hxM : M / d₁ ∣ M := ⟨d₁, (Nat.div_mul_cancel hd₁).symm⟩
  have hyM' : M' / d₂ ∣ M' := ⟨d₂, (Nat.div_mul_cancel hd₂).symm⟩
  have hxy : (M * M') / (d₁ * d₂) = (M / d₁) * (M' / d₂) :=
    (Nat.div_mul_div_comm hd₁ hd₂).symm
  have hyd₁ : Nat.Coprime (M' / d₂) d₁ :=
    Nat.Coprime.coprime_dvd_left hyM' (Nat.Coprime.coprime_dvd_right hd₁ hco.symm)
  have hxd₂ : Nat.Coprime (M / d₁) d₂ :=
    Nat.Coprime.coprime_dvd_left hxM (Nat.Coprime.coprime_dvd_right hd₂ hco)
  have hg₁g : Nat.gcd (M / d₁) d₁ ∣ Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂) := by
    rw [hxy]
    exact Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).mul_right _) ((Nat.gcd_dvd_right _ _).mul_right _)
  have hg₂g : Nat.gcd (M' / d₂) d₂ ∣ Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂) := by
    rw [hxy]
    exact Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).mul_left _) ((Nat.gcd_dvd_right _ _).mul_left _)
  have hgg : Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂) ∣
      Nat.gcd (M / d₁) d₁ * Nat.gcd (M' / d₂) d₂ := by
    have hgdd : Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂) ∣ d₁ * d₂ := Nat.gcd_dvd_right _ _
    have hgxy : Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂) ∣ (M / d₁) * (M' / d₂) := by
      rw [← hxy]
      exact Nat.gcd_dvd_left _ _
    have hgyx : Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂) ∣ (M' / d₂) * (M / d₁) :=
      hgxy.trans (dvd_of_eq (Nat.mul_comm (M / d₁) (M' / d₂)))
    have hsplit : Nat.gcd (Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂)) d₁ *
        Nat.gcd (Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂)) d₂ =
        Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂) :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcod).mpr hgdd
    rw [← hsplit]
    refine Nat.mul_dvd_mul ?_ ?_
    · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ d₁)
      have h2 : Nat.Coprime (Nat.gcd (Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂)) d₁)
          (M' / d₂) := Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ d₁) hyd₁.symm
      exact h2.dvd_of_dvd_mul_right ((Nat.gcd_dvd_left _ d₁).trans hgxy)
    · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ d₂)
      have h2 : Nat.Coprime (Nat.gcd (Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂)) d₂)
          (M / d₁) := Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ d₂) hxd₂.symm
      exact h2.dvd_of_dvd_mul_right ((Nat.gcd_dvd_left _ d₂).trans hgyx)
  have hfwd : ∀ b : ℕ, Nat.gcd (Nat.gcd ((M * M') / (d₁ * d₂)) b) (d₁ * d₂) = 1 →
      Nat.gcd (Nat.gcd (M / d₁) (b % d₁)) d₁ = 1 ∧
        Nat.gcd (Nat.gcd (M' / d₂) (b % d₂)) d₂ = 1 := by
    intro b hb
    rw [slotCond_iff] at hb
    constructor
    · rw [slotCond_iff, slotCond_mod_iff]
      exact Nat.Coprime.coprime_dvd_left hg₁g hb
    · rw [slotCond_iff, slotCond_mod_iff]
      exact Nat.Coprime.coprime_dvd_left hg₂g hb
  have hbwd : ∀ b₁ b₂ k : ℕ, Nat.gcd (Nat.gcd (M / d₁) b₁) d₁ = 1 →
      Nat.gcd (Nat.gcd (M' / d₂) b₂) d₂ = 1 → k ≡ b₁ [MOD d₁] → k ≡ b₂ [MOD d₂] →
      Nat.gcd (Nat.gcd ((M * M') / (d₁ * d₂)) k) (d₁ * d₂) = 1 := by
    intro b₁ b₂ k h₁ h₂ hk₁ hk₂
    rw [slotCond_iff] at h₁ h₂ ⊢
    have hc₁ : Nat.Coprime (Nat.gcd (M / d₁) d₁) k := by
      unfold Nat.Coprime
      rw [gcd_eq_of_modEq (hk₁.of_dvd (Nat.gcd_dvd_right (M / d₁) d₁))]
      exact h₁
    have hc₂ : Nat.Coprime (Nat.gcd (M' / d₂) d₂) k := by
      unfold Nat.Coprime
      rw [gcd_eq_of_modEq (hk₂.of_dvd (Nat.gcd_dvd_right (M' / d₂) d₂))]
      exact h₂
    exact Nat.Coprime.coprime_dvd_left hgg (Nat.coprime_mul_iff_left.mpr ⟨hc₁, hc₂⟩)
  unfold slotAt
  rw [← Finset.card_product]
  refine Finset.card_bij' (fun b _ => (b % d₁, b % d₂))
    (fun q _ => (Nat.chineseRemainder hcod q.1 q.2 : ℕ)) ?_ ?_ ?_ ?_
  · intro b hb
    obtain ⟨hbr, hbc⟩ := Finset.mem_filter.mp hb
    obtain ⟨h₁, h₂⟩ := hfwd b hbc
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt b hd₁0), h₁⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt b hd₂0), h₂⟩⟩
  · intro q hq
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
    have hcrt := (Nat.chineseRemainder hcod q.1 q.2).prop
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.chineseRemainder_lt_mul hcod q.1 q.2 hd₁0.ne' hd₂0.ne'), ?_⟩
    exact hbwd q.1 q.2 _ (Finset.mem_filter.mp hq₁).2 (Finset.mem_filter.mp hq₂).2
      hcrt.1 hcrt.2
  · intro b hb
    have hb' : b < d₁ * d₂ := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hcrt := (Nat.chineseRemainder hcod (b % d₁) (b % d₂)).prop
    have h₁ : (Nat.chineseRemainder hcod (b % d₁) (b % d₂) : ℕ) ≡ b [MOD d₁] :=
      hcrt.1.trans (Nat.mod_modEq b d₁)
    have h₂ : (Nat.chineseRemainder hcod (b % d₁) (b % d₂) : ℕ) ≡ b [MOD d₂] :=
      hcrt.2.trans (Nat.mod_modEq b d₂)
    exact ((Nat.modEq_and_modEq_iff_modEq_mul hcod).mp ⟨h₁, h₂⟩).eq_of_lt_of_lt
      (Nat.chineseRemainder_lt_mul hcod _ _ hd₁0.ne' hd₂0.ne') hb'
  · intro q hq
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
    have hb₁ : q.1 < d₁ := Finset.mem_range.mp (Finset.mem_filter.mp hq₁).1
    have hb₂ : q.2 < d₂ := Finset.mem_range.mp (Finset.mem_filter.mp hq₂).1
    have hcrt := (Nat.chineseRemainder hcod q.1 q.2).prop
    have h₁ : (Nat.chineseRemainder hcod q.1 q.2 : ℕ) % d₁ = q.1 := by
      have h' : (Nat.chineseRemainder hcod q.1 q.2 : ℕ) % d₁ = q.1 % d₁ := hcrt.1
      rw [h', Nat.mod_eq_of_lt hb₁]
    have h₂ : (Nat.chineseRemainder hcod q.1 q.2 : ℕ) % d₂ = q.2 := by
      have h' : (Nat.chineseRemainder hcod q.1 q.2 : ℕ) % d₂ = q.2 % d₂ := hcrt.2
      rw [h', Nat.mod_eq_of_lt hb₂]
    exact Prod.ext h₁ h₂

private theorem gcd_mul_left_of_dvd (M M' : ℕ) (hco : Nat.Coprime M M') {e₁ e₂ : ℕ}
    (he₁ : e₁ ∣ M) (he₂ : e₂ ∣ M') : Nat.gcd (e₁ * e₂) M = e₁ := by
  refine Nat.dvd_antisymm ?_ (Nat.dvd_gcd (dvd_mul_right e₁ e₂) he₁)
  have hc : Nat.Coprime (Nat.gcd (e₁ * e₂) M) e₂ :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
      (Nat.Coprime.coprime_dvd_right he₂ hco)
  exact hc.dvd_of_dvd_mul_right (Nat.gcd_dvd_left _ _)

private theorem gcd_mul_right_of_dvd (M M' : ℕ) (hco : Nat.Coprime M M') {e₁ e₂ : ℕ}
    (he₁ : e₁ ∣ M) (he₂ : e₂ ∣ M') : Nat.gcd (e₁ * e₂) M' = e₂ := by
  refine Nat.dvd_antisymm ?_ (Nat.dvd_gcd (dvd_mul_left e₂ e₁) he₂)
  have hc : Nat.Coprime (Nat.gcd (e₁ * e₂) M') e₁ :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
      (Nat.Coprime.coprime_dvd_right he₁ hco.symm)
  have h1 : Nat.gcd (e₁ * e₂) M' ∣ e₂ * e₁ :=
    (Nat.gcd_dvd_left (e₁ * e₂) M').trans (dvd_of_eq (Nat.mul_comm e₁ e₂))
  exact hc.dvd_of_dvd_mul_right h1

private theorem slots_mul (M M' : ℕ) (hM : M ≠ 0) (hM' : M' ≠ 0)
    (hco : Nat.Coprime M M') : slots (M * M') = slots M * slots M' := by
  unfold slots
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij' (fun d _ => (Nat.gcd d M, Nat.gcd d M')) (fun q _ => q.1 * q.2)
    ?_ ?_ ?_ ?_ ?_
  · intro d hd
    exact Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d M, hM⟩,
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d M', hM'⟩⟩
  · intro q hq
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
    exact Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul (Nat.mem_divisors.mp hq₁).1 (Nat.mem_divisors.mp hq₂).1,
        Nat.mul_ne_zero hM hM'⟩
  · intro d hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hco).mpr (Nat.mem_divisors.mp hd).1
  · intro q hq
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
    exact Prod.ext
      (gcd_mul_left_of_dvd M M' hco (Nat.mem_divisors.mp hq₁).1 (Nat.mem_divisors.mp hq₂).1)
      (gcd_mul_right_of_dvd M M' hco (Nat.mem_divisors.mp hq₁).1 (Nat.mem_divisors.mp hq₂).1)
  · intro d hd
    have hsplit : Nat.gcd d M * Nat.gcd d M' = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hco).mpr (Nat.mem_divisors.mp hd).1
    conv_lhs => rw [← hsplit]
    exact slotAt_mul M M' (Nat.gcd d M) (Nat.gcd d M') hM hM' hco
      (Nat.gcd_dvd_right d M) (Nat.gcd_dvd_right d M')

theorem slots_eq_dedekindPsi : ∀ n : ℕ, n ≠ 0 → slots n = dedekindPsi n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [slots_prime_pow hp j, dedekindPsi_prime_pow' hp j]
  | zero => simp
  | one =>
    intro _
    rw [dedekindPsi_one]
    unfold slots
    rw [Nat.divisors_one, Finset.sum_singleton]
    exact slotAt_one 1
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [slots_mul a b (by omega) (by omega) hab, iha (by omega), ihb (by omega),
      dedekindPsi_mul_of_coprime a b hab]

theorem dedekindPsi_mul_prime_not_dvd {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    dedekindPsi (m * p) = dedekindPsi m * (p + 1) := by
  have hco : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  rw [dedekindPsi_mul_of_coprime m p hco, dedekindPsi_prime hp]

theorem dedekindPsi_mul_prime_dvd {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hpm : p ∣ m) : dedekindPsi (m * p) = dedekindPsi m * p := by
  obtain ⟨k, u, hpu, hmu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    rcases k with - | k' <;> grind
  subst hmu
  have hcou : ∀ j : ℕ, j ≠ 0 → Nat.Coprime (p ^ j) u :=
    fun j _ => Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpu)
  have h1 : p ^ (k' + 1) * u * p = p ^ (k' + 2) * u := by ring
  rw [h1, dedekindPsi_mul_of_coprime _ u (hcou _ (Nat.succ_ne_zero _)),
    dedekindPsi_mul_of_coprime _ u (hcou _ (Nat.succ_ne_zero _)),
    dedekindPsi_prime_pow p (k' + 2) hp (Nat.succ_ne_zero _),
    dedekindPsi_prime_pow p (k' + 1) hp (Nat.succ_ne_zero _)]
  grind

end ModularCurve.ModularPolynomialHelpers

end publicSection
