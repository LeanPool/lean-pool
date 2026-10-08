/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Model.HNNModel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import LeanPool.SmallUndecidableGroups.Borisov.Model.Intersections

/-!
The small exponent-separation facts used in Borisov's Assertion IV.  They
are consequences of the two homomorphisms from the free base `<d,e>` to
`Z`, and keep the later Britton-pinch proof independent of word syntax.
-/

@[expose] public section

namespace Undecidability
namespace BorisovPowerArithmetic

open Function
open BorisovHNNModel

noncomputable section

/-- The homomorphism recording the total exponent of `d` in the free base group. -/
def dExponent : Base →* Multiplicative ℤ :=
  FreeGroup.lift ![Multiplicative.ofAdd 1, 1]

/-- The homomorphism recording the total exponent of `e` in the free base group. -/
def eExponent : Base →* Multiplicative ℤ :=
  FreeGroup.lift ![1, Multiplicative.ofAdd 1]

@[simp] theorem dExponent_d :
    Multiplicative.toAdd (dExponent d) = 1 := by
  simp [dExponent, d]

@[simp] theorem eExponent_e :
    Multiplicative.toAdd (eExponent e) = 1 := by
  simp [eExponent, e]

/-- The cyclic-group homomorphism multiplying an exponent by four. -/
abbrev scaleFour : Multiplicative ℤ →* Multiplicative ℤ := intFour

@[simp] theorem eExponent_alpha (x : Base) :
    Multiplicative.toAdd (eExponent (alpha x)) =
      4 * Multiplicative.toAdd (eExponent x) := by
  have hhom : eExponent.comp alpha = intFour.comp eExponent := by
    rw [alpha_eq_lift]
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp only [eExponent, Nat.succ_eq_add_one, Nat.reduceAdd, d, Fin.isValue,
      e, Fin.zero_eta,
      MonoidHom.coe_comp, comp_apply, FreeGroup.lift_apply_of, Matrix.cons_val_zero, intFour,
      Int.ofAdd_mul, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_one, zpow_ofNat, pow_zero,
      Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_pow, toAdd_ofAdd, pow_one]
    all_goals apply Multiplicative.toAdd.injective
    all_goals norm_num
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hhom x)

@[simp] theorem dExponent_beta (x : Base) :
    Multiplicative.toAdd (dExponent (beta x)) =
      4 * Multiplicative.toAdd (dExponent x) := by
  have hhom : dExponent.comp beta = intFour.comp dExponent := by
    rw [beta_eq_lift]
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp only [dExponent, Nat.succ_eq_add_one, Nat.reduceAdd, d, Fin.isValue,
      e, Fin.zero_eta,
      MonoidHom.coe_comp, comp_apply, FreeGroup.lift_apply_of, Matrix.cons_val_zero, map_pow,
      intFour, Int.ofAdd_mul, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, zpow_ofNat,
      pow_one, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, toAdd_one, pow_zero]
    all_goals apply Multiplicative.toAdd.injective
    all_goals norm_num
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hhom x)

theorem e_pow_mem_A0_dvd (n : ℤ) (h : e ^ n ∈ A0) : (4 : ℤ) ∣ n := by
  rcases h with ⟨x, hx⟩
  have hm := congrArg (fun z => Multiplicative.toAdd (eExponent z)) hx
  refine ⟨Multiplicative.toAdd (eExponent x), ?_⟩
  simpa using hm.symm

theorem d_pow_mem_B0_dvd (n : ℤ) (h : d ^ n ∈ B0) : (4 : ℤ) ∣ n := by
  rcases h with ⟨x, hx⟩
  have hm := congrArg (fun z => Multiplicative.toAdd (dExponent z)) hx
  refine ⟨Multiplicative.toAdd (dExponent x), ?_⟩
  simpa using hm.symm

theorem fin3_succ_sub_eq_zero_of_abs_lt
    (i j : Fin 3)
    (hdiv : (4 : ℤ) ∣ ((i.val : ℤ) + 1 - ((j.val : ℤ) + 1))) :
    i = j := by
  rcases hdiv with ⟨k, hk⟩
  apply Fin.ext
  omega

/-- Distinct rule exponents `1,2,3` cannot differ by a nonzero multiple of
four in the right associated subgroup `<d,e⁴>`. -/
theorem e_rule_difference_mem_A0_imp_eq (i j : Fin 3)
    (hmem : e ^ ((i.val : ℤ) + 1 - ((j.val : ℤ) + 1)) ∈ A0) :
    i = j :=
  fin3_succ_sub_eq_zero_of_abs_lt i j (e_pow_mem_A0_dvd _ hmem)

/-- The symmetric exponent-separation fact in `<d⁴,e>`. -/
theorem d_rule_difference_mem_B0_imp_eq (i j : Fin 3)
    (hmem : d ^ ((i.val : ℤ) + 1 - ((j.val : ℤ) + 1)) ∈ B0) :
    i = j :=
  fin3_succ_sub_eq_zero_of_abs_lt i j (d_pow_mem_B0_dvd _ hmem)

theorem e_rule_power_not_mem_A0 (i : Fin 3) :
    e ^ ((i.val : ℤ) + 1) ∉ A0 := by
  intro hmem
  rcases e_pow_mem_A0_dvd _ hmem with ⟨k, hk⟩
  omega

theorem d_rule_power_not_mem_B0 (i : Fin 3) :
    d ^ ((i.val : ℤ) + 1) ∉ B0 := by
  intro hmem
  rcases d_pow_mem_B0_dvd _ hmem with ⟨k, hk⟩
  omega

end

end BorisovPowerArithmetic
end Undecidability

/-!
# Borisov Assertion IV: the four boundary cases

This file formalizes the finite case analysis on page 770 of Borisov's
paper.  A displayed basis factor is either one of the stable letters or a
decorated rule word `d^i W_i e^i`; its Boolean sign records whether the
factor or its inverse occurs.  The theorem `boundary_pinch_forces_inverse`
says that a Britton pinch between consecutive factors forces those factors
to be formal inverses.  Consequently no such boundary pinch occurs in a
freely reduced word on the displayed basis.
-/

namespace Undecidability
namespace BorisovAssertionIVBoundary

open BorisovHNNModel
open BorisovIntersections
open BorisovPowerArithmetic

noncomputable section

/-- The nonzero integer exponent `i + 1` associated with a rewriting rule. -/
def rulePower (i : Fin 3) : ℤ := (i.val : ℤ) + 1

/-- The first letter of the indicated nonempty rule word. -/
def ruleFirst (rules : Fin 3 → List (Fin 2))
    (hne : ∀ i, rules i ≠ []) (i : Fin 3) : Fin 2 :=
  (rules i).head (hne i)

/-- The last letter of the indicated nonempty rule word. -/
def ruleLast (rules : Fin 3 → List (Fin 2))
    (hne : ∀ i, rules i ≠ []) (i : Fin 3) : Fin 2 :=
  (rules i).getLast (hne i)

/-- The first stable letter in the literal expansion of a signed displayed
basis factor. -/
def firstStable (rules : Fin 3 → List (Fin 2))
    (hne : ∀ i, rules i ≠ []) : Basis × Bool → Fin 2
  | (.inl beta, _) => beta
  | (.inr i, true) => ruleFirst rules hne i
  | (.inr i, false) => ruleLast rules hne i

/-- The last stable letter in the literal expansion of a signed displayed
basis factor. -/
def lastStable (rules : Fin 3 → List (Fin 2))
    (hne : ∀ i, rules i ≠ []) : Basis × Bool → Fin 2
  | (.inl beta, _) => beta
  | (.inr i, true) => ruleLast rules hne i
  | (.inr i, false) => ruleFirst rules hne i

/-- Base coefficient before the first stable letter of a factor. -/
def factorPrefix : Basis × Bool → Base
  | (.inl _, _) => 1
  | (.inr i, true) => BorisovHNNModel.d ^ rulePower i
  | (.inr i, false) => BorisovHNNModel.e ^ (-rulePower i)

/-- Base coefficient after the last stable letter of a factor. -/
def suffix : Basis × Bool → Base
  | (.inl _, _) => 1
  | (.inr i, true) => BorisovHNNModel.e ^ rulePower i
  | (.inr i, false) => BorisovHNNModel.d ^ (-rulePower i)

/-- The base-group coefficient at the boundary between two expanded basis letters. -/
def boundaryCoefficient (x y : Basis × Bool) : Base :=
  suffix x * factorPrefix y

/-- The associated subgroup for a stable letter with the indicated orientation. -/
def associatedForSign (positive : Bool) : Subgroup Base :=
  if positive then A0 else B0

private theorem pos_neg_factor_eq
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (qx qy : Basis)
    (hstable :
      lastStable rules hne (qx, true) = firstStable rules hne (qy, false))
    (hmem : boundaryCoefficient (qx, true) (qy, false) ∈ A0) :
    qx = qy := by
  cases qx with
  | inl beta =>
      cases qy with
      | inl gamma =>
          simpa [lastStable, firstStable] using hstable
      | inr j =>
          have heNeg : BorisovHNNModel.e ^ (-rulePower j) ∈ A0 := by
            simpa [boundaryCoefficient, suffix, factorPrefix] using hmem
          have hePos : BorisovHNNModel.e ^ rulePower j ∈ A0 := by
            have := A0.inv_mem heNeg
            simpa using this
          exact (e_rule_power_not_mem_A0 j (by simpa [rulePower] using hePos)).elim
  | inr i =>
      cases qy with
      | inl gamma =>
          have hePos : BorisovHNNModel.e ^ rulePower i ∈ A0 := by
            simpa [boundaryCoefficient, suffix, factorPrefix] using hmem
          exact (e_rule_power_not_mem_A0 i (by simpa [rulePower] using hePos)).elim
      | inr j =>
          have hdiff :
              BorisovHNNModel.e ^ (rulePower i - rulePower j) ∈ A0 := by
            simpa [boundaryCoefficient, suffix, factorPrefix, zpow_sub] using hmem
          have hij := e_rule_difference_mem_A0_imp_eq i j
            (by simpa [rulePower] using hdiff)
          exact congrArg Sum.inr hij

private theorem neg_pos_factor_eq
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (qx qy : Basis)
    (hstable :
      lastStable rules hne (qx, false) = firstStable rules hne (qy, true))
    (hmem : boundaryCoefficient (qx, false) (qy, true) ∈ B0) :
    qx = qy := by
  cases qx with
  | inl beta =>
      cases qy with
      | inl gamma =>
          simpa [lastStable, firstStable] using hstable
      | inr j =>
          have hdPos : BorisovHNNModel.d ^ rulePower j ∈ B0 := by
            simpa [boundaryCoefficient, suffix, factorPrefix] using hmem
          exact (d_rule_power_not_mem_B0 j (by simpa [rulePower] using hdPos)).elim
  | inr i =>
      cases qy with
      | inl gamma =>
          have hdNeg : BorisovHNNModel.d ^ (-rulePower i) ∈ B0 := by
            simpa [boundaryCoefficient, suffix, factorPrefix] using hmem
          have hdPos : BorisovHNNModel.d ^ rulePower i ∈ B0 := by
            have := B0.inv_mem hdNeg
            simpa using this
          exact (d_rule_power_not_mem_B0 i (by simpa [rulePower] using hdPos)).elim
      | inr j =>
          have hsum :
              BorisovHNNModel.d ^
                (-rulePower i + rulePower j) ∈ B0 := by
            rw [zpow_add]
            simpa [boundaryCoefficient, suffix, factorPrefix] using hmem
          have hdiff :
              BorisovHNNModel.d ^ (rulePower j - rulePower i) ∈ B0 := by
            simpa [sub_eq_add_neg, add_comm] using hsum
          have hji := d_rule_difference_mem_B0_imp_eq j i
            (by simpa [rulePower] using hdiff)
          exact congrArg Sum.inr hji.symm

/-- The four cases in Borisov's proof of Assertion IV.  If consecutive
signed displayed factors have opposite signs and their touching stable
letters form a Britton pinch, their basis indices are equal. -/
theorem boundary_pinch_forces_same_factor
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (x y : Basis × Bool)
    (hsign : x.2 ≠ y.2)
    (hstable : lastStable rules hne x = firstStable rules hne y)
    (hmem : boundaryCoefficient x y ∈ associatedForSign x.2) :
    x.1 = y.1 := by
  rcases x with ⟨qx, sx⟩
  rcases y with ⟨qy, sy⟩
  cases sx <;> cases sy
  · exact (hsign rfl).elim
  · apply neg_pos_factor_eq rules hne qx qy hstable
    simpa [associatedForSign] using hmem
  · apply pos_neg_factor_eq rules hne qx qy hstable
    simpa [associatedForSign] using hmem
  · exact (hsign rfl).elim

/-- A freely reduced adjacent pair of displayed factors cannot have a
Britton pinch across its boundary. -/
theorem no_boundary_pinch_of_reduced_pair
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (x y : Basis × Bool)
    (hreduced : x.1 = y.1 → x.2 = y.2)
    (hsign : x.2 ≠ y.2)
    (hstable : lastStable rules hne x = firstStable rules hne y) :
    boundaryCoefficient x y ∉ associatedForSign x.2 := by
  intro hmem
  exact hsign (hreduced
    (boundary_pinch_forces_same_factor rules hne x y hsign hstable hmem))

end

end BorisovAssertionIVBoundary
end Undecidability
