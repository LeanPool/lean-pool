/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Prime Kloosterman sums and normalization

Additive-character conventions and elementary identities for the classical prime sums.
References: Weil (1948); Harcos (2015), equation (1).
-/

@[expose] public section

namespace KloostermanWeil

noncomputable def kloostermanSumPrime (p : ℕ) [Fact p.Prime]
    (a b : ZMod p) : ℂ :=
  ∑ x : ZMod p, if x = 0 then 0 else ZMod.stdAddChar (b * x + a * x⁻¹)

noncomputable def zmodInvEquiv (p : ℕ) [Fact p.Prime] : ZMod p ≃ ZMod p where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv

lemma kloostermanSumPrime_zero_left (p : ℕ) [Fact p.Prime]
    (b : ZMod p) (hb : b ≠ 0) :
    kloostermanSumPrime p 0 b = -1 := by
  unfold kloostermanSumPrime
  rw [← gaussSum_one_left (ψ := (ZMod.stdAddChar (N := p)).mulShift b)]
  · rw [gaussSum]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h0 : x = 0
    · subst x
      simp [MulChar.map_zero]
    · have hxunit : IsUnit x := isUnit_iff_ne_zero.mpr h0
      simp [h0, AddChar.mulShift_apply, MulChar.one_apply hxunit]
  · intro h
    have hp : (ZMod.stdAddChar (N := p)).IsPrimitive :=
      ZMod.isPrimitive_stdAddChar p
    exact hp hb h

lemma kloostermanSumPrime_comm (p : ℕ) [Fact p.Prime]
    (a b : ZMod p) :
    kloostermanSumPrime p a b = kloostermanSumPrime p b a := by
  unfold kloostermanSumPrime
  apply Fintype.sum_equiv (zmodInvEquiv p)
  intro x
  by_cases h0 : x = 0
  · subst x
    simp [zmodInvEquiv]
  · have hinv0 : x⁻¹ ≠ 0 := inv_ne_zero h0
    simp [zmodInvEquiv, h0, hinv0, add_comm]

lemma kloostermanSumPrime_zero_right (p : ℕ) [Fact p.Prime]
    (a : ZMod p) (ha : a ≠ 0) :
    kloostermanSumPrime p a 0 = -1 := by
  rw [kloostermanSumPrime_comm]
  exact kloostermanSumPrime_zero_left p a ha

lemma kloostermanSumPrime_zero_zero (p : ℕ) [Fact p.Prime] :
    kloostermanSumPrime p 0 0 = (p : ℂ) - 1 := by
  unfold kloostermanSumPrime
  simp only [zero_mul, add_zero, AddChar.map_zero_eq_one]
  have hone :
      (∑ x : ZMod p, if x = 0 then (1 : ℂ) else 0) = 1 := by
    exact Fintype.sum_ite_eq' 0 (fun _ : ZMod p => (1 : ℂ))
  calc
    (∑ x : ZMod p, if x = 0 then 0 else (1 : ℂ)) =
        ∑ x : ZMod p, ((1 : ℂ) - if x = 0 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h0 : x = 0 <;> simp [h0]
    _ = (∑ _x : ZMod p, (1 : ℂ)) -
        (∑ x : ZMod p, if x = 0 then (1 : ℂ) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = (p : ℂ) - 1 := by
          rw [hone]
          simp

def PrimeNondegenerateWeil : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p),
    a ≠ 0 → b ≠ 0 →
      ‖kloostermanSumPrime p a b‖ ≤ 2 * Real.sqrt p


/-- Classical prime Kloosterman sum in conventional coefficient order:
    S(m,n;p) = ∑_{x mod p, x ≠ 0} e_p(m x + n x⁻¹).
This matches Weil (1948), up to the standard additive-character notation. -/
noncomputable def weilKloostermanPrime
    (p : ℕ) [Fact p.Prime] (m n : ZMod p) : ℂ :=
  ∑ x : ZMod p,
    if x = 0 then 0 else ZMod.stdAddChar (m * x + n * x⁻¹)

/-- Exact normalization bridge: the prime sum agrees with the classical
Kloosterman sum with the two coefficients named in the opposite order. -/
theorem kloostermanSumPrime_eq_weilKloostermanPrime
    (p : ℕ) [Fact p.Prime] (a b : ZMod p) :
    kloostermanSumPrime p a b = weilKloostermanPrime p b a := by
  rfl

/-- Classical prime Kloosterman–Weil bound in conventional coefficient order.
This proposition is proved in `rml.weil.prime_kloosterman` using a
Carlitz recurrence and a Stepanov point-count estimate.

Source: André Weil, "On Some Exponential Sums",
Proc. Natl. Acad. Sci. U.S.A. 34 (1948), 204-207,
DOI 10.1073/pnas.34.5.204. -/
def Weil1948PrimeKloostermanBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m n : ZMod p),
    m ≠ 0 → n ≠ 0 →
      ‖weilKloostermanPrime p m n‖ ≤ 2 * Real.sqrt p

/-- The nondegenerate formulation and the classical Weil statement are exactly
equivalent; there is no remaining normalization or convention gap. -/
theorem primeNondegenerateWeil_iff_weil1948 :
    PrimeNondegenerateWeil ↔ Weil1948PrimeKloostermanBound := by
  constructor
  · intro h p _ m n hm hn
    rw [← kloostermanSumPrime_eq_weilKloostermanPrime p n m]
    exact h p n m hn hm
  · intro h p _ a b ha hb
    rw [kloostermanSumPrime_eq_weilKloostermanPrime]
    exact h p b a hb ha


/-- Elementary nonzero scaling reduction:
for nonzero m,n mod p, K_p(n,m) = K_p(m*n,1), equivalently in the
source-normalized order S(m,n;p) = S(1,m*n;p). -/
theorem weilKloostermanPrime_scaling
    (p : ℕ) [Fact p.Prime] (m n : ZMod p)
    (hm : m ≠ 0) :
    weilKloostermanPrime p m n =
      weilKloostermanPrime p 1 (m * n) := by
  unfold weilKloostermanPrime
  let e : ZMod p ≃ ZMod p :=
    Equiv.mulLeft₀ m hm
  apply Fintype.sum_equiv e
  intro x
  by_cases hx : x = 0
  · subst x
    simp [e, Equiv.mulLeft₀]
  · have hmx : m * x ≠ 0 := mul_ne_zero hm hx
    have hminv : m * m⁻¹ = (1 : ZMod p) := mul_inv_cancel₀ hm
    change
      (if x = 0 then 0 else ZMod.stdAddChar (m * x + n * x⁻¹)) =
      (if m * x = 0 then 0
       else ZMod.stdAddChar (1 * (m * x) + (m * n) * (m * x)⁻¹))
    rw [ite_eq_right hx, ite_eq_right hmx, one_mul, mul_inv_rev]
    congr 2
    calc
      n * x⁻¹ = (n * x⁻¹) * 1 := by rw [mul_one]
      _ = (n * x⁻¹) * (m * m⁻¹) := by rw [hminv]
      _ = m * n * (x⁻¹ * m⁻¹) := by ac_rfl

theorem kloostermanSumPrime_scaling
    (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    (hb : b ≠ 0) :
    kloostermanSumPrime p a b =
      kloostermanSumPrime p (b * a) 1 := by
  rw [kloostermanSumPrime_eq_weilKloostermanPrime]
  rw [weilKloostermanPrime_scaling p b a hb]
  rfl

def OneParameterPrimeWeil : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a : ZMod p),
    a ≠ 0 →
      ‖kloostermanSumPrime p a 1‖ ≤ 2 * Real.sqrt p

theorem primeNondegenerateWeil_iff_oneParameter :
    PrimeNondegenerateWeil ↔ OneParameterPrimeWeil := by
  constructor
  · intro h p _ a ha
    exact h p a 1 ha one_ne_zero
  · intro h p _ a b ha hb
    rw [kloostermanSumPrime_scaling p a b hb]
    exact h p (b * a) (mul_ne_zero hb ha)

end KloostermanWeil
