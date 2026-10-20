/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

Extracted from the proof of Prove2Me node ModularCurve.exists_phiIrreducible
(85c90cda-9166-5cf9-a245-c0442a624673), by Claude (2026-09-05), submission
25e72fb1-74d8-5410-94ca-a5536b5cd327; locally adapted.
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_JqCoeff
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_PhiGen

import Mathlib.Tactic.Linarith
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_order_jqModC

/-!
# Shared modular-polynomial and Laurent-series helpers

`ModularCurve.W1.TS` is the Laurent series `j(u q^e)` over an arbitrary field, including
positive characteristic. Its coefficients recover the parameters, and its substitution
lemmas describe rescaling and expansion of `q`. Over a ℚ-algebra, `TS_eq_coeffEmb` identifies
it with the coefficientwise image of the rational series.

`ModularCurve.W1.phiAtSeed` specializes the first variable of a modular polynomial.
The accompanying lemmas preserve monicity and degree and transport specialization
and roots along ring homomorphisms.
-/

@[expose] public noncomputable section publicSection

namespace ModularCurve.W1

variable {K : Type*} [Field K]

def TS (K : Type*) [Field K] (e : ℕ) [NeZero e] (u : Kˣ) : LaurentSeries K :=
  qExpand K e (qTwist u (jqModC K))

theorem TS_coeff_mul (e : ℕ) [NeZero e] (u : Kˣ) (n : ℤ) :
    (TS K e u).coeff ((e : ℤ) * n) = ((u ^ n : Kˣ) : K) * (jqModC K).coeff n := by
  rw [TS, qExpand_coeff_mul, qTwist_coeff]

theorem TS_coeff_of_not_dvd (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : ¬ (e : ℤ) ∣ k) :
    (TS K e u).coeff k = 0 := by
  exact qExpand_coeff_of_not_dvd (R := K) (N := e) _ hk

theorem TS_coeff_neg (e : ℕ) [NeZero e] (u : Kˣ) :
    (TS K e u).coeff (-(e : ℤ)) = ((u⁻¹ : Kˣ) : K) := by
  have h := TS_coeff_mul (K := K) e u (-1)
  rw [mul_neg_one] at h
  rw [h, ModularCurve.coeff_jqModC_neg_one, mul_one, zpow_neg_one]

private theorem coeff_jqModC_of_lt {n : ℤ} (hn : n < -1) : (jqModC K).coeff n = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [ModularCurve.order_jqModC]
  exact hn

theorem TS_coeff_of_lt (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : k < -(e : ℤ)) :
    (TS K e u).coeff k = 0 := by
  by_cases hd : (e : ℤ) ∣ k
  · obtain ⟨n, rfl⟩ := hd
    have he : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
    have hn : n < -1 := by
      by_contra hcon
      push Not at hcon
      have : -(e : ℤ) ≤ (e : ℤ) * n := by nlinarith
      exact absurd hk (not_lt.mpr this)
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
    have hlt' : (-(a : ℤ)) < -(a' : ℤ) := by
      have : (a' : ℤ) < a := by exact_mod_cast hlt
      omega
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

theorem phiAtSeed_monic {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
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

end publicSection
