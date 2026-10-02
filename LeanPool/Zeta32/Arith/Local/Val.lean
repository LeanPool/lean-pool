/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Div

/-!
# A small `p`-adic valuation toolkit on `ℚ` and `ℚ[X]`

* `VG p q r` : `q = 0 ∨ r ≤ v_p(q)`;
* `GV p f r` : every coefficient of `f ∈ ℚ[X]` satisfies `VG p · r`;
* `det_GV` : if `M i j` has Gauss valuation `≥ ρ i + κ j`, then `det M` has `≥ ∑ ρ + ∑ κ`.
-/

@[expose] public section

-- adapted from dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/Valuation.lean
-- and .../Li2Unified/Modular/Base/IntegralPolynomials.lean, which are in turn
-- adapted from Apery/Arith/Val.lean and Apery/Arith/IntPoly.lean in mo271/Zeta5 by Moritz Firsching
-- (https://github.com/mo271/Zeta5), Apache-2.0.
-- `factor_roots` and `VG.eval_zero` adapted from
-- mo271/Zeta5@f19a196:Apery/Arith/IntPoly.lean

open Finset Polynomial

namespace Zeta32.Arith.Local

variable {p : ℕ}

/-- Valuation is additive on a finite product of nonzero rational factors. -/
lemma padicValRat_finset_prod {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        padicValRat.mul (hf a (Finset.mem_insert_self _ _))
          (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- `v_p(q) ≥ r` (vacuous for `q = 0`). -/
def VG (p : ℕ) (q : ℚ) (r : ℚ) : Prop := q = 0 ∨ r ≤ (padicValRat p q : ℚ)

namespace VG

lemma zero (r : ℚ) : VG p 0 r := Or.inl rfl

lemma mono {q r s : ℚ} (h : VG p q r) (hs : s ≤ r) : VG p q s :=
  h.imp id fun h => hs.trans h

lemma neg {q r : ℚ} (h : VG p q r) : VG p (-q) r := by
  rcases h with h | h
  · left; simp [h]
  · right; rwa [padicValRat.neg]

lemma add [Fact p.Prime] {q q' r : ℚ} (h : VG p q r) (h' : VG p q' r) : VG p (q + q') r := by
  by_cases hq : q = 0
  · simpa [hq] using h'
  by_cases hq' : q' = 0
  · simpa [hq'] using h
  by_cases hs : q + q' = 0
  · exact Or.inl hs
  right
  have h1 := h.resolve_left hq
  have h2 := h'.resolve_left hq'
  have := padicValRat.min_le_padicValRat_add (p := p) hs
  have h3 : (min (padicValRat p q) (padicValRat p q') : ℚ) ≤ padicValRat p (q + q') := by
    exact_mod_cast this
  exact (le_min h1 h2).trans h3

lemma sub [Fact p.Prime] {q q' r : ℚ} (h : VG p q r) (h' : VG p q' r) : VG p (q - q') r := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

lemma mul [Fact p.Prime] {q q' r r' : ℚ} (h : VG p q r) (h' : VG p q' r') :
    VG p (q * q') (r + r') := by
  by_cases hq : q = 0
  · left; simp [hq]
  by_cases hq' : q' = 0
  · left; simp [hq']
  right
  rw [padicValRat.mul hq hq']
  push_cast
  exact add_le_add (h.resolve_left hq) (h'.resolve_left hq')

lemma sum [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ} {r : ℚ}
    (h : ∀ i ∈ s, VG p (f i) r) : VG p (∑ i ∈ s, f i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact zero r
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma prod [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ} {r : ι → ℚ}
    (h : ∀ i ∈ s, VG p (f i) (r i)) : VG p (∏ i ∈ s, f i) (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => right; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma intCast (z : ℤ) : VG p (z : ℚ) 0 := by
  by_cases hz : z = 0
  · left; simp [hz]
  right
  rw [padicValRat.of_int]
  exact_mod_cast Nat.zero_le _

lemma natCast (n : ℕ) : VG p (n : ℚ) 0 := by exact_mod_cast intCast (p := p) (n : ℤ)

lemma one : VG p 1 0 := by exact_mod_cast natCast (p := p) 1

lemma inv [Fact p.Prime] {q r : ℚ} (hv : (padicValRat p q : ℚ) ≤ r) :
    VG p q⁻¹ (-r) := by
  right
  rw [padicValRat.inv]
  push_cast
  linarith

lemma of_eq {q : ℚ} (r : ℚ) (h : q ≠ 0 → r ≤ (padicValRat p q : ℚ)) : VG p q r := by
  by_cases hq : q = 0
  · exact Or.inl hq
  · exact Or.inr (h hq)

/-- `v_p(p^k) = k`. -/
lemma primePow [hp : Fact p.Prime] (k : ℤ) : VG p ((p : ℚ) ^ k) k := by
  right
  have : padicValRat p ((p : ℚ) ^ k) = k := by
    cases k with
    | ofNat n => simp [padicValRat.pow, padicValRat.self hp.out.one_lt]
    | negSucc n => simp [zpow_negSucc, padicValRat.inv, padicValRat.pow,
        padicValRat.self hp.out.one_lt]; omega
  rw [this]

lemma pow [Fact p.Prime] {q r : ℚ} (h : VG p q r) (n : ℕ) : VG p (q ^ n) (n * r) := by
  induction n with
  | zero => right; simp
  | succ n ih => rw [pow_succ]; convert ih.mul h using 1; push_cast; ring

/-- A lower bound on the valuation of `1 / j` for `1 ≤ j ≤ n`. -/
lemma inv_nat [hp : Fact p.Prime] {j n : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    VG p ((j : ℚ)⁻¹) (-(Nat.log p n : ℚ)) := by
  apply inv
  rw [padicValRat.of_nat]
  have h1 : padicValNat p j ≤ Nat.log p j := by
    rcases Nat.eq_zero_or_pos (padicValNat p j) with h | h
    · rw [h]; exact Nat.zero_le _
    · have hdvd : p ^ padicValNat p j ∣ j := pow_padicValNat_dvd
      exact Nat.le_log_of_pow_le hp.out.one_lt (Nat.le_of_dvd (by omega) hdvd)
  have h2 : Nat.log p j ≤ Nat.log p n := Nat.log_mono_right hjn
  exact_mod_cast h1.trans h2

end VG

/-- Gauss valuation bound for polynomials in `X`. -/
def GV (p : ℕ) (f : ℚ[X]) (r : ℚ) : Prop := ∀ n, VG p (f.coeff n) r

namespace GV

lemma zero (r : ℚ) : GV p 0 r := fun n => by simpa using VG.zero (p := p) r

lemma mono {f : ℚ[X]} {r s : ℚ} (h : GV p f r) (hs : s ≤ r) : GV p f s := fun n => (h n).mono hs

lemma add [Fact p.Prime] {f g : ℚ[X]} {r : ℚ} (hf : GV p f r) (hg : GV p g r) :
    GV p (f + g) r := fun n => by
  rw [coeff_add]; exact (hf n).add (hg n)

lemma neg {f : ℚ[X]} {r : ℚ} (hf : GV p f r) : GV p (-f) r := fun n => by
  rw [coeff_neg]; exact (hf n).neg

lemma sub [Fact p.Prime] {f g : ℚ[X]} {r : ℚ} (hf : GV p f r) (hg : GV p g r) :
    GV p (f - g) r := fun n => by
  rw [coeff_sub]; exact (hf n).sub (hg n)

lemma C {q r : ℚ} (h : VG p q r) : GV p (Polynomial.C q) r := fun n => by
  rw [coeff_C]; split_ifs
  · exact h
  · exact VG.zero r

lemma X : GV p (X : ℚ[X]) 0 := fun n => by
  rw [coeff_X]; split_ifs
  · exact VG.one
  · exact VG.zero 0

lemma mul [Fact p.Prime] {f g : ℚ[X]} {r s : ℚ} (hf : GV p f r) (hg : GV p g s) :
    GV p (f * g) (r + s) :=
  fun n => by
    rw [coeff_mul]
    exact VG.sum _ fun x _ => (hf x.1).mul (hg x.2)

lemma C_mul [Fact p.Prime] {q r s : ℚ} {f : ℚ[X]} (hq : VG p q r) (hf : GV p f s) :
    GV p (Polynomial.C q * f) (r + s) := (C hq).mul hf

lemma sum [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ[X]} {r : ℚ}
    (h : ∀ i ∈ s, GV p (f i) r) : GV p (∑ i ∈ s, f i) r := fun n => by
  rw [finsetSum_coeff]; exact VG.sum s fun i hi => h i hi n

lemma prod [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ[X]} {r : ι → ℚ}
    (h : ∀ i ∈ s, GV p (f i) (r i)) : GV p (∏ i ∈ s, f i) (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    simpa using C (p := p) (VG.one (p := p))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma pow [Fact p.Prime] {F : ℚ[X]} {r : ℚ} (h : GV p F r) (n : ℕ) : GV p (F ^ n) (n * r) := by
  induction n with
  | zero => simpa using GV.C (p := p) (VG.one (p := p))
  | succ n ih => rw [pow_succ]; convert ih.mul h using 1; push_cast; ring

lemma comp [Fact p.Prime] {F G : ℚ[X]} (hF : GV p F 0) (hG : GV p G 0) : GV p (F.comp G) 0 := by
  rw [comp_eq_sum_left, Polynomial.sum]
  refine GV.sum _ fun n _ => ?_
  have := GV.C_mul (hF n) (hG.pow n)
  simpa using this

lemma divByMonic_X_sub_C [Fact p.Prime] {F : ℚ[X]} {a : ℚ} (hF : GV p F 0) (ha : VG p a 0) :
    GV p (F /ₘ (Polynomial.X - Polynomial.C a)) 0 := fun n => by
  rw [coeff_divByMonic_X_sub_C]
  refine VG.sum _ fun i _ => ?_
  have := (ha.pow (i - (n + 1))).mul (hF i)
  simpa using this

end GV

lemma VG.eval [Fact p.Prime] {F : ℚ[X]} {z : ℚ} (hF : GV p F 0) (hz : VG p z 0) :
    VG p (F.eval z) 0 := by
  rw [eval_eq_sum, Polynomial.sum]
  refine VG.sum _ fun n _ => ?_
  have := (hF n).mul (hz.pow n)
  simpa using this

lemma VG.eval_zero {F : ℚ[X]} {r : ℚ} (hF : GV p F r) : VG p (F.eval 0) r := by
  rw [← coeff_zero_eq_eval_zero]; exact hF 0

/-- An integral polynomial vanishing at `p`-integral distinct points is divisible by
`∏ (X - ρ)` with an integral quotient. -/
theorem factor_roots [Fact p.Prime] (ρs : Finset ℚ) (hρ : ∀ ρ ∈ ρs, VG p ρ 0) {F : ℚ[X]}
    (hF : GV p F 0) (hroot : ∀ ρ ∈ ρs, F.eval ρ = 0) :
    ∃ S : ℚ[X], GV p S 0 ∧ F = (∏ ρ ∈ ρs, (Polynomial.X - Polynomial.C ρ)) * S := by
  classical
  induction ρs using Finset.induction_on generalizing F with
  | empty => exact ⟨F, hF, by simp⟩
  | insert a ρs ha ih =>
    have hra : F.IsRoot a := hroot a (Finset.mem_insert_self _ _)
    set F1 := F /ₘ (Polynomial.X - Polynomial.C a) with hF1
    have hFeq : F = (Polynomial.X - Polynomial.C a) * F1 :=
      ((mul_divByMonic_eq_iff_isRoot).mpr hra).symm
    have hF1int : GV p F1 0 := GV.divByMonic_X_sub_C hF (hρ a (Finset.mem_insert_self _ _))
    have hF1root : ∀ ρ ∈ ρs, F1.eval ρ = 0 := by
      intro ρ hρs
      have h1 := hroot ρ (Finset.mem_insert_of_mem hρs)
      rw [hFeq, eval_mul, eval_sub, eval_X, eval_C] at h1
      have hne : ρ - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ hρs)
      exact (mul_eq_zero.mp h1).resolve_left hne
    obtain ⟨S, hS, hSeq⟩ := ih (fun ρ h => hρ ρ (Finset.mem_insert_of_mem h)) hF1int hF1root
    exact ⟨S, hS, by rw [hFeq, hSeq, Finset.prod_insert ha, mul_assoc]⟩

/-- **Determinant bound with row and column weights.** -/
theorem det_GV [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ[X])
    (ρ κ : ι → ℚ) (h : ∀ i j, GV p (M i j) (ρ i + κ j)) : GV p M.det (∑ i, ρ i + ∑ j, κ j) := by
  rw [Matrix.det_apply]
  refine GV.sum _ fun σ _ => ?_
  have hprod : GV p (∏ i, M (σ i) i) (∑ i, (ρ (σ i) + κ i)) :=
    GV.prod _ fun i _ => h (σ i) i
  have e : ∑ i, (ρ (σ i) + κ i) = ∑ i, ρ i + ∑ j, κ j := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ ρ]
  rw [e] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hprod
  · rw [hs, Units.neg_smul, one_smul]; exact hprod.neg

end Zeta32.Arith.Local

end
