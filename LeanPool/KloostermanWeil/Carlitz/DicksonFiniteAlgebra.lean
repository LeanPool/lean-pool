/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.RingTheory.Polynomial.Dickson


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Finite-field and Dickson-polynomial algebra

The finite-field notation, elementary Kloosterman sums and Dickson-polynomial
identities used in the Carlitz recurrence. See Carlitz (1969) for the method.
-/

@[expose] public section

namespace KloostermanWeil.Dickson

open Polynomial

/-- The prime residue ring used as the base field when `p` is prime. -/
abbrev Fp (p : ℕ) := ZMod p
/-- Polynomials over the prime residue ring. -/
abbrev FpPoly (p : ℕ) := Polynomial (Fp p)

/-- Base-field one-parameter Kloosterman sum in the source-normalized sign convention. -/
noncomputable def baseKloosterman
    (p : ℕ) [Fact p.Prime] (t : Fp p) : ℂ :=
  ∑ x : Fp p,
    if x = 0 then 0 else
      ZMod.stdAddChar (x + t * x⁻¹)

/-- Carlitz's multiplicative polynomial weight, specialized to K(1,t).
It is only used on monic polynomials; the zero-constant case is extended by zero. -/
noncomputable def etaPoly
    (p : ℕ) [Fact p.Prime] (t : Fp p) (f : FpPoly p) : ℂ :=
  if f.coeff 0 = 0 then 0
  else ZMod.stdAddChar
    (-f.nextCoeff - t * (f.coeff 1 / f.coeff 0))

lemma etaPoly_one
    (p : ℕ) [Fact p.Prime] (t : Fp p) :
    etaPoly p t 1 = 1 := by
  have h0 : (1 : FpPoly p).coeff 0 = 1 := by
    rw [Polynomial.coeff_one]
    norm_num
  have h1 : (1 : FpPoly p).coeff 1 = 0 := by
    rw [Polynomial.coeff_one]
    norm_num
  have hn : (1 : FpPoly p).nextCoeff = 0 := by
    simp [Polynomial.nextCoeff]
  rw [etaPoly, ite_eq_right (by simp [h0])]
  rw [hn, h1, h0]
  simp

lemma etaPoly_mul_of_monic
    (p : ℕ) [Fact p.Prime] (t : Fp p)
    {f g : FpPoly p} (hf : f.Monic) (hg : g.Monic) :
    etaPoly p t (f * g) = etaPoly p t f * etaPoly p t g := by
  by_cases hf0 : f.coeff 0 = 0
  · have hfg0 : (f * g).coeff 0 = 0 := by
      rw [mul_coeff_zero, hf0, zero_mul]
    simp [etaPoly, hf0, hfg0]
  · by_cases hg0 : g.coeff 0 = 0
    · have hfg0 : (f * g).coeff 0 = 0 := by
        rw [mul_coeff_zero, hg0, mul_zero]
      simp [etaPoly, hg0, hfg0]
    · have hfg0 : (f * g).coeff 0 ≠ 0 := by
        rw [mul_coeff_zero]
        exact mul_ne_zero hf0 hg0
      rw [etaPoly, ite_eq_right hfg0,
        etaPoly, ite_eq_right hf0,
        etaPoly, ite_eq_right hg0]
      have harg :
          -(f * g).nextCoeff -
              t * ((f * g).coeff 1 / (f * g).coeff 0) =
            (-f.nextCoeff - t * (f.coeff 1 / f.coeff 0)) +
            (-g.nextCoeff - t * (g.coeff 1 / g.coeff 0)) := by
        rw [hf.nextCoeff_mul hg, mul_coeff_zero, mul_coeff_one]
        field_simp [hf0, hg0]
        ring
      rw [harg, AddChar.map_add_eq_mul]

/-- Canonical monic polynomial with prescribed lower coefficients. -/
noncomputable def monicFromCoeffs
    (p n : ℕ) [Fact p.Prime] (a : Fin n → Fp p) : FpPoly p :=
  X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)

lemma monicFromCoeffs_monic
    (p n : ℕ) [Fact p.Prime] (a : Fin n → Fp p) :
    (monicFromCoeffs p n a).Monic := by
  unfold monicFromCoeffs
  apply (monic_X_pow n).add_of_left
  simpa [degree_X_pow] using
    (degree_sum_fin_lt (fun i : Fin n => a i))

/-- The degree-n coefficient sum in the Carlitz L-polynomial. -/
noncomputable def A
    (p : ℕ) [Fact p.Prime] (t : Fp p) (n : ℕ) : ℂ :=
  ∑ a : Fin n → Fp p, etaPoly p t (monicFromCoeffs p n a)

/-- Degree one coefficient is the base Kloosterman sum. -/
theorem A_one_eq_K
    (p : ℕ) [Fact p.Prime] (t : Fp p) :
    A p t 1 = baseKloosterman p t := by
  unfold A baseKloosterman monicFromCoeffs
  simp only [Fin.sum_univ_one]
  let e1 : (Fin 1 → Fp p) ≃ Fp p := Equiv.funUnique (Fin 1) (Fp p)
  let e : (Fin 1 → Fp p) ≃ Fp p := e1.trans (Equiv.neg (Fp p))
  refine Fintype.sum_equiv e _ _ ?_
  intro a
  change etaPoly p t (X ^ 1 + C (a 0) * X ^ 0) =
    if e a = 0 then 0 else ZMod.stdAddChar (e a + t * (e a)⁻¹)
  simp only [pow_one, pow_zero, mul_one]
  change etaPoly p t (X + C (a 0)) =
    if -a 0 = 0 then 0 else ZMod.stdAddChar (-a 0 + t * (-a 0)⁻¹)
  by_cases ha : a 0 = 0
  · simp [etaPoly, ha]
  · have hna : -a 0 ≠ 0 := neg_ne_zero.mpr ha
    simp [etaPoly, ha, hna, Polynomial.nextCoeff]
    congr 2
    field_simp [ha]
    ring

end KloostermanWeil.Dickson


namespace KloostermanWeil.Dickson

open Polynomial

theorem A_zero_eq_one
    (p : ℕ) [Fact p.Prime] (t : Fp p) :
    A p t 0 = 1 := by
  unfold A monicFromCoeffs
  simp [etaPoly_one]

/-- The monic quadratic with linear coefficient `b` and constant coefficient `c`. -/
noncomputable def monicQuadratic
    {p : ℕ} [Fact p.Prime] (b c : Fp p) : FpPoly p :=
  X ^ 2 + C b * X + C c

lemma monicQuadratic_monic
    {p : ℕ} [Fact p.Prime] (b c : Fp p) :
    (monicQuadratic b c).Monic := by
  unfold monicQuadratic
  rw [add_assoc]
  apply (monic_X_pow 2).add_of_left
  apply (degree_add_le _ _).trans_lt
  apply max_lt
  · exact (degree_C_mul_X_le b).trans_lt (by norm_num)
  · exact degree_C_le.trans_lt (by norm_num)

lemma monicQuadratic_coeff_zero
    {p : ℕ} [Fact p.Prime] (b c : Fp p) :
    (monicQuadratic b c).coeff 0 = c := by
  simp [monicQuadratic]

lemma monicQuadratic_coeff_one
    {p : ℕ} [Fact p.Prime] (b c : Fp p) :
    (monicQuadratic b c).coeff 1 = b := by
  simp [monicQuadratic]

lemma monicQuadratic_nextCoeff
    {p : ℕ} [Fact p.Prime] (b c : Fp p) :
    (monicQuadratic b c).nextCoeff = b := by
  have hdegD : (monicQuadratic b c).degree = (2 : WithBot ℕ) := by
    unfold monicQuadratic
    rw [add_assoc, degree_add_eq_left_of_degree_lt]
    · exact degree_X_pow 2
    · apply (degree_add_le _ _).trans_lt
      apply max_lt
      · exact (degree_C_mul_X_le b).trans_lt (by norm_num)
      · exact degree_C_le.trans_lt (by norm_num)
  have hdeg : (monicQuadratic b c).natDegree = 2 :=
    natDegree_eq_of_degree_eq_some hdegD
  simp [Polynomial.nextCoeff, hdeg, monicQuadratic_coeff_one]

lemma etaPoly_monicQuadratic
    (p : ℕ) [Fact p.Prime] (t b c : Fp p) :
    etaPoly p t (monicQuadratic b c) =
      if c = 0 then 0
      else ZMod.stdAddChar (-(1 + t / c) * b) := by
  rw [etaPoly]
  rw [monicQuadratic_coeff_zero, monicQuadratic_coeff_one,
    monicQuadratic_nextCoeff]
  by_cases hc : c = 0
  · simp [hc]
  · simp [hc]
    congr 2
    field_simp [hc]
    ring

lemma sum_etaPoly_monicQuadratic
    (p : ℕ) [Fact p.Prime] {t c : Fp p} (ht : t ≠ 0) :
    (∑ b : Fp p, etaPoly p t (monicQuadratic b c)) =
      if c = -t then (p : ℂ) else 0 := by
  by_cases hc0 : c = 0
  · have hcnt : c ≠ -t := by
      intro h
      apply ht
      exact neg_eq_zero.mp (h.symm.trans hc0)
    rw [ite_eq_right hcnt]
    simp [etaPoly_monicQuadratic, hc0]
  · rw [show (∑ b : Fp p, etaPoly p t (monicQuadratic b c)) =
      ∑ b : Fp p, ZMod.stdAddChar (-(1 + t / c) * b) by
        apply Fintype.sum_congr
        intro b
        rw [etaPoly_monicQuadratic]
        simp [hc0]]
    by_cases hct : c = -t
    · subst c
      have ht0 : (-t : Fp p) ≠ 0 := neg_ne_zero.mpr ht
      have hcoef : -(1 + t / (-t)) = (0 : Fp p) := by
        have hdiv : t / (-t) = (-1 : Fp p) := by
          field_simp [ht]
        rw [hdiv]
        ring
      simp [hcoef, ZMod.card]
    · have hcoef : -(1 + t / c) ≠ (0 : Fp p) := by
        intro hz
        have hz' : 1 + t / c = 0 := neg_eq_zero.mp hz
        have : c = -t := by
          field_simp [hc0] at hz'
          linear_combination hz'
        exact hct this
      have hnontriv :
          ZMod.stdAddChar.mulShift (-(1 + t / c)) ≠ 1 :=
        ZMod.isPrimitive_stdAddChar p hcoef
      have hsum :=
        AddChar.sum_eq_zero_of_ne_one
          (R := Fp p) (R' := ℂ) hnontriv
      rw [ite_eq_right hct]
      simpa [AddChar.mulShift_apply] using hsum

end KloostermanWeil.Dickson


namespace KloostermanWeil.Dickson

/-- Identify a two-entry coefficient vector with an ordered pair. -/
noncomputable def finTwoCoeffEquiv
    (p : ℕ) :
    (Fin 2 → Fp p) ≃ (Fp p × Fp p) :=
  (Fin.consEquiv (fun _ : Fin 2 => Fp p)).symm |>.trans
    (Equiv.prodCongr (Equiv.refl (Fp p)) (Equiv.funUnique (Fin 1) (Fp p)))

lemma finTwoCoeffEquiv_apply
    (p : ℕ) (a : Fin 2 → Fp p) :
    finTwoCoeffEquiv p a = (a 0, a 1) := by
  rfl

lemma monicFromCoeffs_two
    (p : ℕ) [Fact p.Prime] (a : Fin 2 → Fp p) :
    monicFromCoeffs p 2 a = monicQuadratic (a 1) (a 0) := by
  unfold monicFromCoeffs monicQuadratic
  rw [Fin.sum_univ_two]
  norm_num
  ring

theorem A_two_eq_card
    (p : ℕ) [Fact p.Prime] {t : Fp p} (ht : t ≠ 0) :
    A p t 2 = (p : ℂ) := by
  unfold A
  let e := finTwoCoeffEquiv p
  calc
    (∑ a : Fin 2 → Fp p, etaPoly p t (monicFromCoeffs p 2 a)) =
        ∑ z : Fp p × Fp p, etaPoly p t (monicQuadratic z.2 z.1) := by
          apply Fintype.sum_equiv e
          intro a
          rw [monicFromCoeffs_two, finTwoCoeffEquiv_apply]
    _ = ∑ c : Fp p, ∑ b : Fp p, etaPoly p t (monicQuadratic b c) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ c : Fp p, if c = -t then (p : ℂ) else 0 := by
          apply Fintype.sum_congr
          intro c
          exact sum_etaPoly_monicQuadratic p ht
    _ = (p : ℂ) := by
          simp

end KloostermanWeil.Dickson


namespace KloostermanWeil.Dickson

open Polynomial

lemma coeff_fintype_sum
    {R ι : Type*} [Semiring R] [Fintype ι]
    (f : ι → Polynomial R) (j : ℕ) :
    (∑ i : ι, f i).coeff j = ∑ i : ι, (f i).coeff j := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

lemma monicFromCoeffs_degree
    (p n : ℕ) [Fact p.Prime] (a : Fin n → Fp p) :
    (monicFromCoeffs p n a).degree = n := by
  unfold monicFromCoeffs
  rw [degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow n
  · rw [degree_X_pow]
    exact degree_sum_fin_lt a

lemma monicFromCoeffs_coeff_lt
    (p n j : ℕ) [Fact p.Prime] (hj : j < n)
    (a : Fin n → Fp p) :
    (monicFromCoeffs p n a).coeff j = a ⟨j, hj⟩ := by
  unfold monicFromCoeffs
  rw [coeff_add, coeff_X_pow]
  rw [ite_eq_right (Nat.ne_of_lt hj)]
  rw [zero_add, coeff_fintype_sum]
  simp_rw [coeff_C_mul_X_pow]
  let idx : Fin n := ⟨j, hj⟩
  calc
    (∑ x : Fin n, if j = (x : ℕ) then a x else 0) =
        ∑ x : Fin n, if x = idx then a x else 0 := by
          apply Fintype.sum_congr
          intro x
          by_cases h : x = idx
          · subst x
            simp [idx]
          · have hv : j ≠ (x : ℕ) := by
              intro heq
              apply h
              apply Fin.ext
              exact heq.symm
            simp [h, hv]
    _ = a idx := Fintype.sum_ite_eq' idx a
    _ = a ⟨j, hj⟩ := rfl

/-- The index of the final lower coefficient of a positive-degree monic polynomial. -/
noncomputable def lastIndex (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt hn (by norm_num)⟩

lemma monicFromCoeffs_nextCoeff
    (p n : ℕ) [Fact p.Prime] (hn : 0 < n)
    (a : Fin n → Fp p) :
    (monicFromCoeffs p n a).nextCoeff = a (lastIndex n hn) := by
  have hd : (monicFromCoeffs p n a).natDegree = n :=
    natDegree_eq_of_degree_eq_some (monicFromCoeffs_degree p n a)
  rw [Polynomial.nextCoeff, hd, ite_eq_right hn.ne']
  exact monicFromCoeffs_coeff_lt p n (n - 1)
    (Nat.sub_lt hn (by norm_num)) a

end KloostermanWeil.Dickson


namespace KloostermanWeil.Dickson

/-- Translate the final lower coefficient by `u`, keeping the other coefficients fixed. -/
noncomputable def shiftLastEquiv
    (p n : ℕ) [Fact p.Prime] (hn : 0 < n) (u : Fp p) :
    (Fin n → Fp p) ≃ (Fin n → Fp p) where
  toFun a i :=
    if i = lastIndex n hn then a i + u else a i
  invFun a i :=
    if i = lastIndex n hn then a i - u else a i
  left_inv a := by
    funext i
    by_cases hi : i = lastIndex n hn
    · simp [hi]
    · simp [hi]
  right_inv a := by
    funext i
    by_cases hi : i = lastIndex n hn
    · simp [hi]
    · simp [hi]

lemma shiftLastEquiv_at_last
    (p n : ℕ) [Fact p.Prime] (hn : 0 < n) (u : Fp p)
    (a : Fin n → Fp p) :
    shiftLastEquiv p n hn u a (lastIndex n hn) =
      a (lastIndex n hn) + u := by
  simp [shiftLastEquiv]

lemma shiftLastEquiv_at_zero
    (p n : ℕ) [Fact p.Prime] (hn2 : 2 ≤ n) (u : Fp p)
    (a : Fin n → Fp p) :
    shiftLastEquiv p n (lt_of_lt_of_le (by norm_num) hn2) u a
        ⟨0, lt_of_lt_of_le (by norm_num) hn2⟩ =
      a ⟨0, lt_of_lt_of_le (by norm_num) hn2⟩ := by
  let hn : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  have hne :
      (⟨0, hn⟩ : Fin n) ≠ lastIndex n hn := by
    intro h
    have hv := congrArg Fin.val h
    simp [lastIndex] at hv
    omega
  simp [shiftLastEquiv, hne]

lemma shiftLastEquiv_at_one
    (p n : ℕ) [Fact p.Prime] (hn3 : 3 ≤ n) (u : Fp p)
    (a : Fin n → Fp p) :
    shiftLastEquiv p n (lt_of_lt_of_le (by norm_num) hn3) u a
        ⟨1, lt_of_lt_of_le (by norm_num) hn3⟩ =
      a ⟨1, lt_of_lt_of_le (by norm_num) hn3⟩ := by
  let hn : 0 < n := lt_of_lt_of_le (by norm_num) hn3
  have hne :
      (⟨1, by omega⟩ : Fin n) ≠ lastIndex n hn := by
    intro h
    have hv := congrArg Fin.val h
    simp [lastIndex] at hv
    omega
  simp [shiftLastEquiv, hne]

lemma etaPoly_shiftLast
    (p n : ℕ) [Fact p.Prime] (hn3 : 3 ≤ n)
    (t u : Fp p) (a : Fin n → Fp p) :
    etaPoly p t
        (monicFromCoeffs p n
          (shiftLastEquiv p n (lt_of_lt_of_le (by norm_num) hn3) u a)) =
      ZMod.stdAddChar (-u) * etaPoly p t (monicFromCoeffs p n a) := by
  let hn : 0 < n := lt_of_lt_of_le (by norm_num) hn3
  let sh := shiftLastEquiv p n hn u a
  have h0lt : 0 < n := hn
  have h1lt : 1 < n := by omega
  have hsh0 : sh ⟨0, h0lt⟩ = a ⟨0, h0lt⟩ := by
    dsimp [sh]
    exact shiftLastEquiv_at_zero p n (by omega) u a
  have hsh1 : sh ⟨1, h1lt⟩ = a ⟨1, h1lt⟩ := by
    dsimp [sh]
    exact shiftLastEquiv_at_one p n hn3 u a
  have hshL :
      sh (lastIndex n hn) = a (lastIndex n hn) + u := by
    dsimp [sh]
    exact shiftLastEquiv_at_last p n hn u a
  have hc0 :
      (monicFromCoeffs p n sh).coeff 0 =
        (monicFromCoeffs p n a).coeff 0 := by
    rw [monicFromCoeffs_coeff_lt p n 0 h0lt,
      monicFromCoeffs_coeff_lt p n 0 h0lt, hsh0]
  have hc1 :
      (monicFromCoeffs p n sh).coeff 1 =
        (monicFromCoeffs p n a).coeff 1 := by
    rw [monicFromCoeffs_coeff_lt p n 1 h1lt,
      monicFromCoeffs_coeff_lt p n 1 h1lt, hsh1]
  have hnxt :
      (monicFromCoeffs p n sh).nextCoeff =
        (monicFromCoeffs p n a).nextCoeff + u := by
    rw [monicFromCoeffs_nextCoeff p n hn sh,
      monicFromCoeffs_nextCoeff p n hn a, hshL]
  change etaPoly p t (monicFromCoeffs p n sh) =
    ZMod.stdAddChar (-u) * etaPoly p t (monicFromCoeffs p n a)
  by_cases hzero : (monicFromCoeffs p n a).coeff 0 = 0
  · have hzero' : (monicFromCoeffs p n sh).coeff 0 = 0 := by
      rwa [hc0]
    simp [etaPoly, hzero, hzero']
  · have hzero' : (monicFromCoeffs p n sh).coeff 0 ≠ 0 := by
      rwa [hc0]
    rw [etaPoly, ite_eq_right hzero', etaPoly, ite_eq_right hzero]
    rw [hnxt, hc1, hc0]
    have harg :
        (-( (monicFromCoeffs p n a).nextCoeff + u) -
            t * ((monicFromCoeffs p n a).coeff 1 /
              (monicFromCoeffs p n a).coeff 0)) =
          -u +
            (-(monicFromCoeffs p n a).nextCoeff -
              t * ((monicFromCoeffs p n a).coeff 1 /
                (monicFromCoeffs p n a).coeff 0)) := by
      ring
    rw [harg, AddChar.map_add_eq_mul]

theorem A_eq_zero_of_three_le
    (p n : ℕ) [Fact p.Prime] (hn3 : 3 ≤ n) (t : Fp p) :
    A p t n = 0 := by
  let hn : 0 < n := lt_of_lt_of_le (by norm_num) hn3
  let e := shiftLastEquiv p n hn (1 : Fp p)
  let S : ℂ := A p t n
  have hperm :
      (∑ a : Fin n → Fp p,
        etaPoly p t (monicFromCoeffs p n (e a))) = S := by
    unfold S A
    exact Equiv.sum_comp e
      (fun a : Fin n → Fp p => etaPoly p t (monicFromCoeffs p n a))
  have hphase :
      S = ZMod.stdAddChar (-1 : Fp p) * S := by
    calc
      S = ∑ a : Fin n → Fp p,
          etaPoly p t (monicFromCoeffs p n (e a)) := hperm.symm
      _ = ∑ a : Fin n → Fp p,
          ZMod.stdAddChar (-1 : Fp p) *
            etaPoly p t (monicFromCoeffs p n a) := by
            apply Fintype.sum_congr
            intro a
            exact etaPoly_shiftLast p n hn3 t 1 a
      _ = ZMod.stdAddChar (-1 : Fp p) *
          (∑ a : Fin n → Fp p,
            etaPoly p t (monicFromCoeffs p n a)) := by
            rw [Finset.mul_sum]
      _ = ZMod.stdAddChar (-1 : Fp p) * S := rfl
  have hne : ZMod.stdAddChar (-1 : Fp p) ≠ 1 := by
    intro h
    have hz :
        (-1 : Fp p) = 0 :=
      ((ZMod.isPrimitive_stdAddChar p).zmod_char_eq_one_iff p (-1)).mp h
    simp at hz
  have hzero :
      (ZMod.stdAddChar (-1 : Fp p) - 1) * S = 0 := by
    calc
      (ZMod.stdAddChar (-1 : Fp p) - 1) * S =
          ZMod.stdAddChar (-1 : Fp p) * S - S := by ring
      _ = 0 := by rw [← hphase, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

end KloostermanWeil.Dickson


namespace KloostermanWeil.Dickson

open Polynomial

theorem dickson_one_eval_add_of_mul
    {R : Type*} [CommRing R] (x y a : R) (hxy : x * y = a) :
    ∀ n : ℕ, (Polynomial.dickson 1 a n).eval (x + y) = x ^ n + y ^ n
  | 0 => by norm_num [Polynomial.dickson_zero]
  | 1 => by simp [Polynomial.dickson_one]
  | n + 2 => by
      rw [Polynomial.dickson_add_two, eval_sub, eval_mul, eval_X]
      simp only [eval_mul, eval_C]
      rw [dickson_one_eval_add_of_mul x y a hxy (n + 1),
        dickson_one_eval_add_of_mul x y a hxy n]
      rw [← hxy]
      simp only [pow_succ]
      ring

end KloostermanWeil.Dickson
