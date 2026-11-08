/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Statements

/-!
# Checks of the definitions: flips, degree zero, the dictator

`flipSet` / `diffSet` are mutually inverse, `HasDegreeLE` is monotone, degree `0` means constant,
and the dictator `x ↦ (-1)^{x_j}` has degree exactly `1`, variance `1` and influence `1`; so the
hypotheses of `MainTheorem` are satisfiable (`aa_hyps_satisfiable`).
These are checks of the definitions of `Defs.lean`; the proofs of `Chain.lean` do not depend on
them.
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset

section NoFintype

variable {ι : Type*} [DecidableEq ι]

theorem flipSet_flipSet (x : Cube ι) (S : Finset ι) : flipSet (flipSet x S) S = x := by
  funext i
  by_cases h : i ∈ S <;> simp [flipSet, h]

theorem flipSet_empty (x : Cube ι) : flipSet x ∅ = x := by
  funext i
  simp [flipSet]

theorem flipSet_singleton_self (x : Cube ι) (j : ι) : flipSet x {j} j = !(x j) := by
  simp [flipSet]

theorem flipSet_singleton_ne (x : Cube ι) {i j : ι} (h : i ≠ j) : flipSet x {j} i = x i := by
  simp [flipSet, h]

end NoFintype

section DictPlain

variable {ι : Type*}

/-- The dictator `x ↦ (-1)^{x_j}`. -/
noncomputable def dict (j : ι) : Cube ι → ℝ := fun x => if x j then -1 else 1

theorem dict_abs_le_one (j : ι) (x : Cube ι) : |dict j x| ≤ 1 := by
  unfold dict
  split_ifs <;> simp

theorem dict_sq (j : ι) (x : Cube ι) : dict j x ^ 2 = 1 := by
  unfold dict
  split_ifs <;> norm_num

theorem dict_flip [DecidableEq ι] (j : ι) (x : Cube ι) : dict j (flipSet x {j}) = -dict j x := by
  unfold dict
  rw [flipSet_singleton_self]
  cases x j <;> simp

end DictPlain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Δ(x, x^S) = S`. -/
theorem diffSet_flipSet (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by
  ext i
  by_cases h : i ∈ S <;> simp [diffSet, flipSet, h]

/-- `x^{Δ(x,y)} = y`. -/
theorem flipSet_diffSet (x y : Cube ι) : flipSet x (diffSet x y) = y := by
  funext i
  by_cases h : x i = y i
  · simp [flipSet, diffSet, h]
  · have h' : (!(x i)) = y i := by
      cases hx : x i <;> cases hy : y i <;> simp_all
    simp [flipSet, diffSet, h, h']

/-- `antipode x = x^{[n]}`. -/
theorem antipode_eq_flipSet_univ (x : Cube ι) : antipode x = flipSet x univ := by
  funext i
  simp [antipode, flipSet]

/-- The cube over `ι` has `2^n` points. -/
theorem card_cube : (Fintype.card (Cube ι) : ℝ) = 2 ^ Fintype.card ι := by
  change (Fintype.card (ι → Bool) : ℝ) = 2 ^ Fintype.card ι
  rw [Fintype.card_fun, Fintype.card_bool]
  norm_num

omit [DecidableEq ι] in
/-- Monotonicity of `HasDegreeLE` in the degree. -/
theorem hasDegreeLE_mono {f : Cube ι → ℝ} {d d' : ℕ} (h : HasDegreeLE f d) (hdd : d ≤ d') :
    HasDegreeLE f d' := by
  obtain ⟨c, hc, hf⟩ := h
  exact ⟨c, fun S hS => hc S (lt_of_le_of_lt hdd hS), hf⟩

omit [Fintype ι] [DecidableEq ι] in
theorem chi_empty (x : Cube ι) : chi (∅ : Finset ι) x = 1 := by
  simp [chi]

omit [DecidableEq ι] in
/-- Degree at most `0` is the same as constant. -/
theorem hasDegreeLE_zero_iff {f : Cube ι → ℝ} : HasDegreeLE f 0 ↔ ∃ a : ℝ, ∀ x, f x = a := by
  classical
  constructor
  · rintro ⟨c, hc, hf⟩
    refine ⟨c ∅, fun x => ?_⟩
    rw [hf x, Finset.sum_eq_single (∅ : Finset ι)]
    · simp [chi]
    · intro S _ hS
      rw [hc S (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rintro ⟨a, ha⟩
    refine ⟨fun S => if S = ∅ then a else 0, ?_, fun x => ?_⟩
    · intro S hS
      have hne : S ≠ ∅ := by
        rintro rfl
        simp at hS
      simp [hne]
    · rw [ha x, Finset.sum_eq_single (∅ : Finset ι)]
      · simp [chi]
      · intro S _ hS
        simp [hS]
      · intro h
        exact absurd (Finset.mem_univ _) h

omit [DecidableEq ι] in
/-- `HasDegreeLE f 0` implies `f` constant. -/
theorem hasDegreeLE_zero_const {f : Cube ι → ℝ} (h : HasDegreeLE f 0) (x y : Cube ι) :
    f x = f y := by
  classical
  obtain ⟨a, ha⟩ := hasDegreeLE_zero_iff.mp h
  rw [ha x, ha y]

/-! ### The dictator -/

omit [Fintype ι] [DecidableEq ι] in
theorem dict_eq_chi (j : ι) (x : Cube ι) : dict j x = chi {j} x := by
  simp [dict, chi]

omit [DecidableEq ι] in
theorem dict_hasDegreeLE_one (j : ι) : HasDegreeLE (dict j) 1 := by
  classical
  refine ⟨fun S => if S = {j} then 1 else 0, ?_, fun x => ?_⟩
  · intro S hS
    have hne : S ≠ {j} := by
      rintro rfl
      simp at hS
    simp [hne]
  · rw [Finset.sum_eq_single ({j} : Finset ι)]
    · simp [dict_eq_chi]
    · intro S _ hS
      simp [hS]
    · intro h
      exact absurd (Finset.mem_univ _) h

omit [DecidableEq ι] in
/-- A dictator does not have degree at most `0`. -/
theorem dict_not_hasDegreeLE_zero (j : ι) : ¬ HasDegreeLE (dict j) 0 := by
  classical
  intro h
  have h1 := hasDegreeLE_zero_const h (fun _ => false) (flipSet (fun _ => false) {j})
  rw [dict_flip] at h1
  have h2 : dict j (fun _ => false) = 1 := by simp [dict]
  rw [h2] at h1
  norm_num at h1

theorem sum_dict (j : ι) : ∑ x : Cube ι, dict j x = 0 := by
  have h : ∑ x : Cube ι, dict j (flipSet x {j}) = ∑ x : Cube ι, dict j x :=
    Equiv.sum_comp
      (Function.Involutive.toPerm (fun x : Cube ι => flipSet x {j})
        (fun x => flipSet_flipSet x {j})) (dict j)
  simp only [dict_flip, Finset.sum_neg_distrib] at h
  linarith

theorem mean_dict (j : ι) : mean (dict j) = 0 := by
  simp [mean, sum_dict]

theorem variance_dict (j : ι) : variance (dict j) = 1 := by
  simp only [variance, mean_dict, sub_zero, dict_sq, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [card_cube]
  exact div_self (by positivity)

theorem inflR_dict_self (j : ι) : inflR (dict j) j = 1 := by
  have h : ∀ x : Cube ι, ((dict j x - dict j (flipSet x {j})) / 2) ^ 2 = 1 := by
    intro x
    rw [dict_flip]
    have h2 : (dict j x - -dict j x) / 2 = dict j x := by ring
    rw [h2, dict_sq]
  simp only [inflR, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [card_cube]
  exact div_self (by positivity)

/-- Non-vacuity of `MainTheorem`: on any index type with a chosen coordinate `j`, the dictator
satisfies all three hypotheses with `d = 1`, has variance `1` and influence `1` at `j`. -/
theorem aa_hyps_dict (j : ι) :
    (∀ x, |dict j x| ≤ 1) ∧ HasDegreeLE (dict j) 1 ∧ 0 < variance (dict j) ∧
      variance (dict j) = 1 ∧ inflR (dict j) j = 1 :=
  ⟨dict_abs_le_one j, dict_hasDegreeLE_one j, by rw [variance_dict]; norm_num,
    variance_dict j, inflR_dict_self j⟩

/-- Same, on the concrete index type `Fin 1`. -/
theorem aa_hyps_satisfiable :
    ∃ f : Cube (Fin 1) → ℝ, (∀ x, |f x| ≤ 1) ∧ HasDegreeLE f 1 ∧ 0 < variance f ∧
      variance f = 1 ∧ inflR f 0 = 1 :=
  ⟨dict 0, aa_hyps_dict 0⟩

/-- The conclusion of `MainTheorem` (with `d = 1`) is true for the dictator. -/
theorem aa_conclusion_dict (j : ι) :
    ∃ j', 3 * variance (dict j) ^ 5
      ≤ 50000 * Real.pi ^ 8 * ((1 : ℕ) : ℝ) ^ 12 * inflR (dict j) j' ^ 2 := by
  refine ⟨j, ?_⟩
  rw [variance_dict, inflR_dict_self]
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h1 : (1 : ℝ) ≤ Real.pi ^ 8 := one_le_pow₀ hpi
  simp only [Nat.cast_one, one_pow, mul_one]
  linarith

omit [DecidableEq ι] in
/-- The conclusion of `RowBound` (with `d = 1`) is true for `h = (1 + dictator)/2`,
with the weights `c x i = [i = j]`. -/
theorem rowBound_conclusion_dict (j : ι) :
    ∃ c : Cube ι → ι → ℝ,
      (∀ x y, |(1 + dict j x) / 2 - (1 + dict j y) / 2| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * ((1 : ℕ) : ℝ) ^ 2) := by
  classical
  refine ⟨fun _ i => if i = j then 1 else 0, fun x y => ?_, fun x => ?_⟩
  · by_cases h : x j = y j
    · have hxy : dict j x = dict j y := by simp [dict, h]
      rw [hxy, sub_self, abs_zero]
      refine Finset.sum_nonneg (fun i _ => ?_)
      change (0 : ℝ) ≤ if i = j then 1 else 0
      split_ifs <;> norm_num
    · have hj : j ∈ diffSet x y := by simp [diffSet, h]
      rw [Finset.sum_ite_eq', ite_eq_left hj]
      unfold dict
      split_ifs <;> norm_num
  · rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ j)]
    have hpi := Real.pi_gt_three
    norm_num
    nlinarith

end AaronsonAmbainis.Bridge
