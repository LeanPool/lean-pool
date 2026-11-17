/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.RedJ.RedIdeal
public import LeanPool.HyperellipticCurves.Specialization.Content

import LeanPool.HyperellipticCurves.Disks.OrdMatchElement
import Mathlib.RingTheory.Ideal.IsPrincipal

/-!
# The reduction of a split principal ideal is principal

For the coordinate ring `A_K` of `y² = f(x)` over the fraction field `K` of a discrete valuation
ring `O` with algebraically closed residue field, we show that the reduction `redIdeal f (z)` of a
*split* principal ideal `(z)` is again principal
(`ChabautyColeman.isPrincipal_redIdeal_span`).

The generator `z = P + Q·y` is normalized by splitting off the content: writing
`d = gcd(z.re, z.im)`, the ideal `(z)` factors (up to a unit scalar) as `(D)·(P + Q·y)` with `P, Q`
coprime and jointly primitive over `O` and `D` a lift of `d`. The reduction of the coprime factor
is principal by `thm:spec` in ideal form (`ChabautyColeman.redIdeal_span`), while the reduction of
`(D)` is principal because `D` splits into linear factors, each of which reduces to a product of two
opposite point ideals — i.e. a principal `(x - x_bar₀)` — over the residue curve.

This is the well-definedness mechanism of the reduction homomorphism `thm:redJ-hom`: the class of
`(z)` in the Jacobian reduces to a *principal* class, hence to the identity of the residue Jacobian.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

/-! ### A norm polynomial of odd-degree data is nonzero -/

section NormNeZero

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The norm polynomial `P² - g·Q²` of odd-degree `g` is nonzero unless `P = Q = 0`: a degree
count (`2·deg P = deg g + 2·deg Q`) contradicts the parity of `deg g`. -/
theorem sq_sub_mul_sq_ne_zero {g p q : R[X]} (hodd : Odd g.natDegree)
    (hpq : ¬(p = 0 ∧ q = 0)) : p ^ 2 - g * q ^ 2 ≠ 0 := by
  intro h
  have hpe : p ^ 2 = g * q ^ 2 := by linear_combination h
  rcases eq_or_ne q 0 with rfl | hq
  · rw [zero_pow (by norm_num), mul_zero] at hpe
    exact hpq ⟨(pow_eq_zero_iff (by norm_num)).mp hpe, rfl⟩
  · have hg : g ≠ 0 := by rintro rfl; simp at hodd
    have hdeg := congrArg natDegree hpe
    rw [natDegree_pow, natDegree_mul hg (pow_ne_zero 2 hq), natDegree_pow] at hdeg
    rcases hodd with ⟨k, hk⟩
    lia

end NormNeZero

/-! ### Scaling the generator of a principal ideal by a nonzero constant -/

section ScalarSpan

variable {K : Type*} [Field K]

/-- Multiplying the generator of a principal ideal by a nonzero scalar leaves the ideal
unchanged (the scalar becomes a unit of the algebra). -/
theorem span_singleton_algebraMap_mul {A : Type*} [CommRing A] [Algebra K A] {c : K}
    (hc : c ≠ 0) (w : A) :
    Ideal.span {algebraMap K A c * w} = Ideal.span {w} :=
  Ideal.span_singleton_mul_left_unit (hc.isUnit.map (algebraMap K A)) w

/-- A factorization `w₁ * w₂ = c·z` of an element up to a nonzero scalar `c` is a
factorization of the principal ideal it generates. -/
theorem span_singleton_eq_mul_of_mul_eq {A : Type*} [CommRing A] [Algebra K A] {c : K}
    (hc : c ≠ 0) {z w₁ w₂ : A} (h : w₁ * w₂ = algebraMap K A c * z) :
    Ideal.span {z} = Ideal.span {w₁} * Ideal.span {w₂} := by
  rw [← span_singleton_algebraMap_mul hc z, ← h, Ideal.span_singleton_mul_span_singleton]

/-- A principal ideal with nonzero generator is nonzero. -/
theorem span_singleton_ne_zero {A : Type*} [CommRing A] {w : A} (hw : w ≠ 0) :
    Ideal.span {w} ≠ 0 := by
  rwa [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]

end ScalarSpan

/-! ### Lifting `v`-integral / primitive polynomials from `K` to `O` -/

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- The `𝔪`-adic valuation on the fraction field `K` of the discrete valuation ring `O`. -/
local notation:max "𝓋" =>
  IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal O)

/-- A polynomial over `K` with content `≤ 1` lifts to a polynomial over `O`. -/
theorem exists_map_eq_of_contentVal_le_one {p : K[X]} (hp : contentVal 𝓋 p ≤ 1) :
    ∃ p₀ : O[X], p₀.map (algebraMap O K) = p := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  exact fun n ↦ IsDiscreteValuationRing.exists_lift_of_le_one
    ((coeff_le_contentVal _ p n).trans hp)

/-- If two `O`-polynomials with jointly primitive `K`-images (content sup `= 1`) both reduced to
zero over the residue field, then every coefficient would lie in the maximal ideal, forcing both
contents below `1` — a contradiction. Hence at least one reduction is nonzero. -/
theorem not_map_residue_eq_zero_of_contentVal {p₀ q₀ : O[X]}
    (hprim : contentVal 𝓋 (p₀.map (algebraMap O K))
      ⊔ contentVal 𝓋 (q₀.map (algebraMap O K)) = 1) :
    ¬(p₀.map (residue O) = 0 ∧ q₀.map (residue O) = 0) := by
  intro ⟨hp, hq⟩
  have hlt : ∀ r₀ : O[X], r₀.map (residue O) = 0 →
      contentVal 𝓋 (r₀.map (algebraMap O K)) < 1 := by
    intro r₀ hr
    rcases eq_or_ne (r₀.map (algebraMap O K)) 0 with h0 | h0
    · rw [h0, contentVal_zero]; exact zero_lt_one
    · rw [contentVal, Finset.sup_lt_iff (by simp)]
      intro i _
      rw [coeff_map]
      refine ((IsDiscreteValuationRing.maximalIdeal O).valuation_lt_one_iff_mem
        (r₀.coeff i)).mpr ?_
      have hcoeff0 : residue O (r₀.coeff i) = 0 := by
        have := congrArg (fun s ↦ Polynomial.coeff s i) hr
        simpa [coeff_map] using this
      exact (residue_eq_zero_iff _).mp hcoeff0
  have := sup_lt_iff.mpr ⟨hlt p₀ hp, hlt q₀ hq⟩
  rw [hprim] at this
  exact lt_irrefl _ this

end DVR

/-! ### The reduction of `(algebraMap d)` is principal for split `d` -/

section SplitFactor

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  {f : O[X]}
  [NeZero (2 : K)] [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]

/-- The reduction of a constant (unit) generator is the unit ideal, hence principal. -/
theorem isPrincipal_redIdeal_span_C {c : K} (hc : c ≠ 0) :
    (redIdeal f (Ideal.span
      {algebraMap K[X] (HypRing K (f.map (algebraMap O K))) (C c)})).IsPrincipal := by
  rw [← HypRing.algebraMap_eq_C,
    Ideal.span_singleton_eq_top.mpr
      (hc.isUnit.map (algebraMap K (HypRing K (f.map (algebraMap O K))))),
    redIdeal_top]
  infer_instance

section LinearFactor

variable [NeZero (2 : ResidueField O)] [Fact (Squarefree (f.map (residue O)))]

/-- The reduction of `(x - a)` is principal: for non-integral `a` it is the unit ideal, and for
integral `a` with a square `f`-value it is the product of the two opposite reduced point ideals,
i.e. the principal ideal `(x - ā)` on the residue curve. -/
theorem isPrincipal_redIdeal_span_X_sub_C {a : K}
    (hsq : IsIntegral O a → ∃ b : K, b ^ 2 = (f.map (algebraMap O K)).eval a) :
    (redIdeal f (Ideal.span
      {algebraMap K[X] (HypRing K (f.map (algebraMap O K))) (X - C a)})).IsPrincipal := by
  by_cases ha : IsIntegral O a
  · obtain ⟨a₀, ha₀⟩ := IsIntegrallyClosed.isIntegral_iff.mp ha
    obtain ⟨b, hbpt⟩ := hsq ha
    have hfa : (f.map (algebraMap O K)).eval a = algebraMap O K (f.eval a₀) := by
      rw [← ha₀, eval_map_apply]
    have hbsq : b ^ 2 = algebraMap O K (f.eval a₀) := hbpt.trans hfa
    have hbint : IsIntegral O b :=
      IsIntegral.of_pow (n := 2) (by norm_num) (by rw [hbsq]; exact isIntegral_algebraMap)
    obtain ⟨b₀, hb₀⟩ := IsIntegrallyClosed.isIntegral_iff.mp hbint
    have hb₀sq : b₀ ^ 2 = f.eval a₀ :=
      IsFractionRing.injective O K (by rw [map_pow, hb₀, hbsq])
    have hxle : (IsDiscreteValuationRing.maximalIdeal O).valuation K a ≤ 1 := by
      rw [← ha₀]; exact (IsDiscreteValuationRing.maximalIdeal O).valuation_le_one a₀
    have hyle : (IsDiscreteValuationRing.maximalIdeal O).valuation K b ≤ 1 := by
      rw [← hb₀]; exact (IsDiscreteValuationRing.maximalIdeal O).valuation_le_one b₀
    have hbneg : (-b) ^ 2 = (f.map (algebraMap O K)).eval a := (neg_sq b).trans hbpt
    have hynegle : (IsDiscreteValuationRing.maximalIdeal O).valuation K (-b) ≤ 1 := by
      rwa [Valuation.map_neg]
    have hbb : (residue O b₀) ^ 2 = (f.map (residue O)).eval (residue O a₀) := by
      rw [← map_pow, hb₀sq, eval_map_apply]
    have hbbneg : (-(residue O b₀)) ^ 2 = (f.map (residue O)).eval (residue O a₀) :=
      (neg_sq _).trans hbb
    have hred1 : redPoint (.affine a b hbpt)
        = .affine (residue O a₀) (residue O b₀) hbb := by
      rw [redPoint_affine hbpt hxle hyle]
      exact CurvePoint.affine_congr (by rw [← ha₀, redK_algebraMap])
        (by rw [← hb₀, redK_algebraMap]) _ _
    have hred2 : redPoint (.affine a (-b) hbneg)
        = .affine (residue O a₀) (-(residue O b₀)) hbbneg := by
      rw [redPoint_affine hbneg hxle hynegle]
      refine CurvePoint.affine_congr (by rw [← ha₀, redK_algebraMap]) ?_ _ _
      rw [← hb₀, ← map_neg, redK_algebraMap, map_neg]
    have hne1 : pointIdeal (f.map (algebraMap O K)) a b ≠ 0 :=
      pointIdeal_ne_zero (f.map (algebraMap O K)) a b
    have hne2 : pointIdeal (f.map (algebraMap O K)) a (-b) ≠ 0 :=
      pointIdeal_ne_zero (f.map (algebraMap O K)) a (-b)
    rw [← pointIdeal_mul_pointIdeal_neg (f.map (algebraMap O K)) Fact.out two_ne_zero hbpt,
      redIdeal_mul hne1 hne2,
      redIdeal_pointIdeal_of_redPoint_eq hbpt hred1,
      redIdeal_pointIdeal_of_redPoint_eq hbneg hred2,
      pointIdeal_mul_pointIdeal_neg (f.map (residue O)) Fact.out two_ne_zero hbb]
    infer_instance
  · rw [redIdeal_span_X_sub_C_of_not_isIntegral ha]; infer_instance

private theorem isPrincipal_redIdeal_span_algebraMap_aux (n : ℕ) {d : K[X]}
    (hdle : d.natDegree ≤ n) (hd : d ≠ 0) (hdsplit : d.Splits)
    (hdsq : ∀ x : K, IsIntegral O x → d.eval x = 0 →
      ∃ b : K, b ^ 2 = (f.map (algebraMap O K)).eval x) :
    (redIdeal f (Ideal.span
      {algebraMap K[X] (HypRing K (f.map (algebraMap O K))) d})).IsPrincipal := by
  induction n generalizing d with
  | zero =>
    have h0deg : d.natDegree = 0 := Nat.le_zero.mp hdle
    have hdC : d = C (d.coeff 0) := eq_C_of_natDegree_eq_zero h0deg
    have hc0 : d.coeff 0 ≠ 0 := fun h ↦ hd (by rw [hdC, h, map_zero])
    rw [hdC]; exact isPrincipal_redIdeal_span_C hc0
  | succ n ih =>
    rcases Nat.eq_zero_or_pos d.natDegree with h0deg | hpos
    · exact ih (h0deg.le.trans n.zero_le) hd hdsplit hdsq
    · obtain ⟨a, ha⟩ := hdsplit.exists_eval_eq_zero (natDegree_pos_iff_degree_pos.mp hpos).ne'
      have hdvd : (X - C a) ∣ d := dvd_iff_isRoot.mpr ha
      set d₁ := d / (X - C a)
      have hdfac : (X - C a) * d₁ = d :=
        EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero a) hdvd
      have hd₁ : d₁ ≠ 0 := right_ne_zero_of_mul (by rw [hdfac]; exact hd)
      have hdeg₁ : d₁.natDegree ≤ n := by
        have hnd := natDegree_mul (X_sub_C_ne_zero a) hd₁
        rw [hdfac, natDegree_X_sub_C] at hnd
        lia
      have hdsplit₁ : d₁.Splits := hdsplit.of_dvd hd (Dvd.intro_left _ hdfac)
      have hdsq₁ : ∀ x : K, IsIntegral O x → d₁.eval x = 0 →
          ∃ b : K, b ^ 2 = (f.map (algebraMap O K)).eval x :=
        fun x hx hev ↦ hdsq x hx (by rw [← hdfac, eval_mul, hev, mul_zero])
      have hlin := isPrincipal_redIdeal_span_X_sub_C (f := f) (a := a)
        (fun hai ↦ hdsq a hai ha)
      have hspan : Ideal.span {algebraMap K[X] (HypRing K (f.map (algebraMap O K))) d}
          = Ideal.span {algebraMap K[X] (HypRing K (f.map (algebraMap O K))) (X - C a)}
            * Ideal.span {algebraMap K[X] (HypRing K (f.map (algebraMap O K))) d₁} := by
        rw [← hdfac, map_mul, Ideal.span_singleton_mul_span_singleton]
      have hne1 : Ideal.span
          {algebraMap K[X] (HypRing K (f.map (algebraMap O K))) (X - C a)} ≠ 0 :=
        span_singleton_algebraMap_ne_zero _ (X_sub_C_ne_zero a)
      have hne2 : Ideal.span
          {algebraMap K[X] (HypRing K (f.map (algebraMap O K))) d₁} ≠ 0 :=
        span_singleton_algebraMap_ne_zero _ hd₁
      rw [hspan, redIdeal_mul hne1 hne2]
      exact (Ideal.isPrincipalSubmonoid _).mul_mem hlin (ih hdeg₁ hd₁ hdsplit₁ hdsq₁)

/-- The reduction of `(D)` is principal whenever `D` splits over `K` and has a square `f`-value at
each of its integral roots: split `D` into linear factors and reduce each via
`isPrincipal_redIdeal_span_X_sub_C`. -/
theorem isPrincipal_redIdeal_span_algebraMap {d : K[X]} (hd : d ≠ 0) (hdsplit : d.Splits)
    (hdsq : ∀ x : K, IsIntegral O x → d.eval x = 0 →
      ∃ b : K, b ^ 2 = (f.map (algebraMap O K)).eval x) :
    (redIdeal f (Ideal.span
      {algebraMap K[X] (HypRing K (f.map (algebraMap O K))) d})).IsPrincipal :=
  isPrincipal_redIdeal_span_algebraMap_aux d.natDegree le_rfl hd hdsplit hdsq

end LinearFactor

end SplitFactor

/-! ### Content splitting and the square-value transport onto the coprime factor -/

section ContentSplit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  {f : O[X]}

/-- The `𝔪`-adic valuation on the fraction field `K` of the discrete valuation ring `O`. -/
local notation:max "𝓋" =>
  IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal O)

/-- Residue-lifting for the coprime factor: if the norm `P² - f·Q²` of the primitive factor has
a square value in `K` at every integral point, then at a maximal-ideal translate `ω + w` of a
root `ω` of `f` the square root lies in the maximal ideal. -/
theorem exists_mem_maximalIdeal_sq_eq {P Q : O[X]}
    (hsqf : ∀ x : K, IsIntegral O x → ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).eval x = 0 →
      ∃ b : K, b ^ 2 = (f.map (algebraMap O K)).eval x)
    (ω : O) (hω : f.eval ω = 0) (w : maximalIdeal O)
    (hev : ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).eval (algebraMap O K (ω + w.1)) = 0) :
    ∃ y ∈ maximalIdeal O, y ^ 2 = f.eval (ω + w.1) := by
  set x := algebraMap O K (ω + w.1) with hxdef
  obtain ⟨b, hbpt⟩ := hsqf x isIntegral_algebraMap hev
  have hfx : (f.map (algebraMap O K)).eval x = algebraMap O K (f.eval (ω + w.1)) := by
    rw [hxdef, eval_map_apply]
  have hbsq : b ^ 2 = algebraMap O K (f.eval (ω + w.1)) := hbpt.trans hfx
  have hbint : IsIntegral O b :=
    IsIntegral.of_pow (n := 2) (by norm_num) (by rw [hbsq]; exact isIntegral_algebraMap)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hbint
  have hysq : y ^ 2 = f.eval (ω + w.1) :=
    IsFractionRing.injective O K (by rw [map_pow, hy, hbsq])
  refine ⟨y, ?_, hysq⟩
  rw [← residue_eq_zero_iff]
  have hcomm : residue O (f.eval ω) = (f.map (residue O)).eval (residue O ω) :=
    (eval_map_apply _ _).symm
  have hcomm2 : residue O (f.eval (ω + w.1))
      = (f.map (residue O)).eval (residue O (ω + w.1)) := (eval_map_apply _ _).symm
  have hry2 : (residue O y) ^ 2 = 0 := by
    rw [← map_pow, hysq, hcomm2, map_add, (residue_eq_zero_iff _).mpr w.2, add_zero,
      ← hcomm, hω, map_zero]
  exact (pow_eq_zero_iff (by norm_num)).mp hry2

variable [Fact (Odd (f.map (residue O)).natDegree)]

/-- The common factor of the two components divides the norm form. -/
private lemma dvd_sq_sub_mul_sq {A : Type*} [CommRing A] {d p q r i g : A}
    (hp : d * p = r) (hq : d * q = i) :
    d ∣ r ^ 2 - g * i ^ 2 :=
  ⟨d * (p ^ 2 - g * q ^ 2), by rw [← hp, ← hq]; ring⟩

/-- The norm form of the primitive part divides the norm form. -/
private lemma sq_sub_mul_sq_dvd {A : Type*} [CommRing A] {d p q r i g : A}
    (hp : d * p = r) (hq : d * q = i) :
    p ^ 2 - g * q ^ 2 ∣ r ^ 2 - g * i ^ 2 :=
  ⟨d ^ 2, by rw [← hp, ← hq]; ring⟩

/-- **Content splitting of a generator.** A nonzero element `z = z.re + z.im·y` of the
coordinate ring factors, up to a unit scalar, as `(D)·(P + Q·y)` with `D, P, Q ∈ O[X]`, where
`D` is a lift of the content `gcd(z.re, z.im)` and `(P, Q)` is jointly primitive and coprime.
This yields the ideal factorization together with the primitivity and divisibility data used to
reduce each factor separately. -/
theorem exists_content_split {z : HypRing K (f.map (algebraMap O K))} (hz : z ≠ 0) :
    ∃ P Q D : O[X],
      Ideal.span {z} = Ideal.span {(algebraMap K[X] (HypRing K (f.map (algebraMap O K)))
          (D.map (algebraMap O K)))}
        * Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
            HypRing K (f.map (algebraMap O K)))}
      ∧ D.map (algebraMap O K) ≠ 0
      ∧ (⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
          HypRing K (f.map (algebraMap O K))) ≠ 0
      ∧ IsCoprime (P.map (algebraMap O K)) (Q.map (algebraMap O K))
      ∧ (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0
      ∧ D.map (algebraMap O K) ∣ z.re ^ 2 - f.map (algebraMap O K) * z.im ^ 2
      ∧ (P ^ 2 - f * Q ^ 2).map (algebraMap O K)
          ∣ z.re ^ 2 - f.map (algebraMap O K) * z.im ^ 2 := by
  classical
  have hre_im := QuadraticAlgebra.not_re_eq_zero_and_im_eq_zero hz
  set d := GCDMonoid.gcd z.re z.im
  have hd : d ≠ 0 := fun h ↦ hre_im ((gcd_eq_zero_iff z.re z.im).mp h)
  set P₁ := z.re / d
  set Q₁ := z.im / d
  have hP₁fac : d * P₁ = z.re := EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left z.re z.im)
  have hQ₁fac : d * Q₁ = z.im := EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right z.re z.im)
  have hnotboth₁ : ¬(P₁ = 0 ∧ Q₁ = 0) := fun ⟨h1, h2⟩ ↦
    hre_im ⟨by rw [← hP₁fac, h1, mul_zero], by rw [← hQ₁fac, h2, mul_zero]⟩
  obtain ⟨c, hc_prim⟩ := exists_primitive_smul_pair 𝓋 hnotboth₁
  obtain ⟨c', hc'_prim⟩ := exists_primitive_smul 𝓋 hd
  obtain ⟨P, hP⟩ := exists_map_eq_of_contentVal_le_one (le_sup_left.trans hc_prim.le)
  obtain ⟨Q, hQ⟩ := exists_map_eq_of_contentVal_le_one (le_sup_right.trans hc_prim.le)
  obtain ⟨D, hD⟩ := exists_map_eq_of_contentVal_le_one hc'_prim.le
  have hident : algebraMap K[X] (HypRing K (f.map (algebraMap O K))) (D.map (algebraMap O K))
        * (⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
            HypRing K (f.map (algebraMap O K)))
      = algebraMap K (HypRing K (f.map (algebraMap O K))) ((c' : K) * (c : K)) * z := by
    rw [HypRing.algebraMap_eq_C]
    refine QuadraticAlgebra.ext ?_ ?_
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_algebraMap,
        QuadraticAlgebra.im_algebraMap, Algebra.algebraMap_self_apply, mul_zero, add_zero, zero_mul]
      rw [hD, hP, ← hP₁fac, map_mul]; ring
    · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_algebraMap,
        QuadraticAlgebra.im_algebraMap, Algebra.algebraMap_self_apply, mul_zero, add_zero, zero_mul]
      rw [hD, hQ, ← hQ₁fac, map_mul]; ring
  have hspanz := span_singleton_eq_mul_of_mul_eq
    (mul_ne_zero (Units.ne_zero c') (Units.ne_zero c)) hident
  have hDmap0 : D.map (algebraMap O K) ≠ 0 := by
    rw [hD]; exact mul_ne_zero (C_ne_zero.mpr (Units.ne_zero c')) hd
  have hzPQ0 : (⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
      HypRing K (f.map (algebraMap O K))) ≠ 0 := by
    intro h0
    obtain ⟨hre, him⟩ := QuadraticAlgebra.mk_eq_zero.mp h0
    rw [hP] at hre; rw [hQ] at him
    exact hnotboth₁ ⟨(mul_eq_zero.mp hre).resolve_left (C_ne_zero.mpr (Units.ne_zero c)),
      (mul_eq_zero.mp him).resolve_left (C_ne_zero.mpr (Units.ne_zero c))⟩
  have hNmapK : (P ^ 2 - f * Q ^ 2).map (algebraMap O K)
      = C (c : K) ^ 2 * (P₁ ^ 2 - f.map (algebraMap O K) * Q₁ ^ 2) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_pow, hP, hQ]
    ring
  have hcop2 : IsCoprime (P.map (algebraMap O K)) (Q.map (algebraMap O K)) := by
    rw [hP, hQ, isCoprime_mul_unit_left_left (isUnit_C.mpr c.isUnit),
      isCoprime_mul_unit_left_right (isUnit_C.mpr c.isUnit)]
    exact isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hd
  have hbothres : ¬(P.map (residue O) = 0 ∧ Q.map (residue O) = 0) :=
    not_map_residue_eq_zero_of_contentVal (by rw [hP, hQ]; exact hc_prim)
  have hN2 : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_pow]
    exact sq_sub_mul_sq_ne_zero (Fact.out : Odd (f.map (residue O)).natDegree) hbothres
  have hDdvd : D.map (algebraMap O K) ∣ z.re ^ 2 - f.map (algebraMap O K) * z.im ^ 2 := by
    rw [hD]
    exact (isUnit_C.mpr c'.isUnit).mul_left_dvd.mpr (dvd_sq_sub_mul_sq hP₁fac hQ₁fac)
  have hPQdvd : (P ^ 2 - f * Q ^ 2).map (algebraMap O K)
      ∣ z.re ^ 2 - f.map (algebraMap O K) * z.im ^ 2 := by
    rw [hNmapK]
    exact ((isUnit_C.mpr c.isUnit).pow 2).mul_left_dvd.mpr (sq_sub_mul_sq_dvd hP₁fac hQ₁fac)
  exact ⟨P, Q, D, hspanz, hDmap0, hzPQ0, hcop2, hN2, hDdvd, hPQdvd⟩

end ContentSplit

/-! ### The main theorem: reduction of a split principal ideal is principal -/

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  {f : O[X]}
  [NeZero (2 : K)] [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]
  [NeZero (2 : ResidueField O)] [Fact (Odd (f.map (residue O)).natDegree)]
  [Fact (Squarefree (f.map (residue O)))] [IsAlgClosed (ResidueField O)]

/-- The `𝔪`-adic valuation on the fraction field `K` of the discrete valuation ring `O`. -/
local notation:max "𝓋" =>
  IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal O)

/-- **Principal ideals reduce to principal ideals** (split data): if the norm of `z` splits
over `K` and has square `f`-values at its integral roots, the reduction of `(z)` is
principal. This is the well-definedness mechanism of `thm:redJ-hom`. -/
theorem isPrincipal_redIdeal_span (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (h2 : IsUnit (2 : O)) {z : HypRing K (f.map (algebraMap O K))} (hz : z ≠ 0)
    (hsplit : (z.re ^ 2 - f.map (algebraMap O K) * z.im ^ 2).Splits)
    (hsq : ∀ x : K, IsIntegral O x →
      (z.re ^ 2 - f.map (algebraMap O K) * z.im ^ 2).eval x = 0 →
        ∃ b : K, b ^ 2 = (f.map (algebraMap O K)).eval x) :
    (redIdeal f (Ideal.span {z})).IsPrincipal := by
  obtain ⟨P, Q, D, hspanz, hDmap0, hzPQ0, hcop2, hN2, hDdvd, hPQdvd⟩ :=
    exists_content_split hz
  have hDne := span_singleton_ne_zero ((map_ne_zero_iff
    (algebraMap K[X] (HypRing K (f.map (algebraMap O K))))
    QuadraticAlgebra.algebraMap_injective).mpr hDmap0)
  have hzPQne := span_singleton_ne_zero hzPQ0
  have hN0ne : z.re ^ 2 - f.map (algebraMap O K) * z.im ^ 2 ≠ 0 :=
    sq_sub_mul_sq_ne_zero (Fact.out : Odd (f.map (algebraMap O K)).natDegree)
      (QuadraticAlgebra.not_re_eq_zero_and_im_eq_zero hz)
  have hfactor1 : (redIdeal f (Ideal.span {(algebraMap K[X]
      (HypRing K (f.map (algebraMap O K))) (D.map (algebraMap O K)))})).IsPrincipal :=
    isPrincipal_redIdeal_span_algebraMap hDmap0 (hsplit.of_dvd hN0ne hDdvd)
      fun x hx hev ↦ hsq x hx (eval_eq_zero_of_dvd_of_eval_eq_zero hDdvd hev)
  have hfactor2 : (redIdeal f (Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
      HypRing K (f.map (algebraMap O K)))})).IsPrincipal := by
    rw [redIdeal_span hf hdeg h2 hN2 hcop2
      (exists_mem_maximalIdeal_sq_eq fun x hx hev ↦
        hsq x hx (eval_eq_zero_of_dvd_of_eval_eq_zero hPQdvd hev))
      (hsplit.of_dvd hN0ne hPQdvd)]
    infer_instance
  rw [hspanz, redIdeal_mul hDne hzPQne]
  exact (Ideal.isPrincipalSubmonoid _).mul_mem hfactor1 hfactor2

end Main

end ChabautyColeman

end
