/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Bridge.Basic
public import LeanPool.AaronsonAmbainis.Row.Chi

/-!
# The Fourier expansion on the cube and the meaning of `HasDegreeLE`

The characters `chi S` are an orthogonal basis of the functions on the cube. Consequences:

* every `f` has `HasDegreeLE f (Fintype.card ι)`                       (`hasDegreeLE_card`);
* the coefficients in `HasDegreeLE` are unique                          (`fourier_unique`);
* `HasDegreeLE f d ↔` all Fourier coefficients above level `d` vanish   (`hasDegreeLE_iff_fourier`);
* `HasDegreeLE (chi S) d ↔ S.card ≤ d`                                  (`hasDegreeLE_chi_iff`),
  so `HasDegreeLE` separates every degree level and is not accidentally trivial.
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset

/-- Sign of a bit: `false ↦ 1`, `true ↦ -1`. -/
noncomputable def sg (b : Bool) : ℝ := Row.sgn b

theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by
  exact Row.sgn_mul_self b

theorem sg_not (b : Bool) : sg (!b) = -sg b := by
  exact Row.sgn_not b

theorem sg_mul_of_ne {a b : Bool} (h : a ≠ b) : sg a * sg b = -1 := by
  cases a <;> cases b <;> simp_all [sg, Row.sgn]

theorem chi_eq_prod_sg {ι : Type*} (S : Finset ι) (x : Cube ι) : chi S x = ∏ i ∈ S, sg (x i) :=
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem chi_eq_prod_univ (S : Finset ι) (x : Cube ι) :
    chi S x = ∏ i, (if i ∈ S then sg (x i) else 1) := by
  rw [chi_eq_prod_sg, Fintype.prod_ite_mem]

omit [Fintype ι] in
/-- `χ_S χ_T = χ_{S Δ T}`. -/
theorem chi_mul_chi [Finite ι] (S T : Finset ι) (x : Cube ι) :
    chi S x * chi T x = chi (symmDiff S T) x := by
  exact Row.chi_mul_chi S T x

omit [Fintype ι] in
/-- Flipping a coordinate in `U` negates `χ_U`. -/
theorem chi_flip_mem {U : Finset ι} {j : ι} (hj : j ∈ U) (x : Cube ι) :
    chi U (flipSet x {j}) = -chi U x := by
  have h : ∏ i ∈ U.erase j, sg (flipSet x {j} i) = ∏ i ∈ U.erase j, sg (x i) :=
    Finset.prod_congr rfl
      (fun i hi => by rw [flipSet_singleton_ne x (Finset.ne_of_mem_erase hi)])
  rw [chi_eq_prod_sg, chi_eq_prod_sg,
    ← Finset.mul_prod_erase U (fun i => sg (flipSet x {j} i)) hj,
    ← Finset.mul_prod_erase U (fun i => sg (x i)) hj, h, flipSet_singleton_self, sg_not, neg_mul]

omit [DecidableEq ι] in
/-- Orthogonality, summing over the characters. -/
theorem sum_chi_mul_chi (x y : Cube ι) :
    ∑ S : Finset ι, chi S x * chi S y = if x = y then (2 : ℝ) ^ Fintype.card ι else 0 := by
  have h1 : ∑ S : Finset ι, chi S x * chi S y = ∏ i : ι, (1 + sg (x i) * sg (y i)) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [chi_eq_prod_sg, chi_eq_prod_sg, ← Finset.prod_mul_distrib]
  rw [h1]
  split_ifs with h
  · have h2 : ∀ i : ι, (1 + sg (x i) * sg (y i)) = 2 := fun i => by
      rw [← h, sg_mul_self]
      norm_num
    simp only [h2, Finset.prod_const, Finset.card_univ]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [sg_mul_of_ne hi]
    norm_num

/-- `∑_x χ_U(x) = 2^n [U = ∅]`. -/
theorem sum_chi (U : Finset ι) :
    ∑ x : Cube ι, chi U x = if U = ∅ then (2 : ℝ) ^ Fintype.card ι else 0 := by
  split_ifs with h
  · subst h
    simp only [chi_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact card_cube
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr h
    have h1 : ∑ x : Cube ι, chi U (flipSet x {j}) = ∑ x : Cube ι, chi U x :=
      Equiv.sum_comp
        (Function.Involutive.toPerm (fun x : Cube ι => flipSet x {j})
          (fun x => flipSet_flipSet x {j})) (chi U)
    simp only [chi_flip_mem hj, Finset.sum_neg_distrib] at h1
    linarith

/-- Orthogonality, summing over the cube. -/
theorem sum_chi_mul_chi_cube (S T : Finset ι) :
    ∑ x : Cube ι, chi S x * chi T x = if S = T then (2 : ℝ) ^ Fintype.card ι else 0 := by
  simp only [chi_mul_chi, sum_chi, Finset.symmDiff_eq_empty]

/-- The Fourier coefficient of `f` at `S`. -/
noncomputable def fourier (f : Cube ι → ℝ) (S : Finset ι) : ℝ :=
  (∑ y, f y * chi S y) / 2 ^ Fintype.card ι

/-- Fourier inversion. -/
theorem fourier_inversion (f : Cube ι → ℝ) (x : Cube ι) :
    ∑ S, fourier f S * chi S x = f x := by
  have hne : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  calc ∑ S : Finset ι, fourier f S * chi S x
      = ∑ S : Finset ι, (∑ y, f y * (chi S x * chi S y)) / 2 ^ Fintype.card ι := by
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [fourier, div_mul_eq_mul_div, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl (fun y _ => ?_)
        ring
    _ = (∑ y, ∑ S : Finset ι, f y * (chi S x * chi S y)) / 2 ^ Fintype.card ι := by
        rw [← Finset.sum_div, Finset.sum_comm]
    _ = (∑ y, f y * (if x = y then (2 : ℝ) ^ Fintype.card ι else 0)) / 2 ^ Fintype.card ι := by
        congr 1
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← Finset.mul_sum, sum_chi_mul_chi]
    _ = f x := by
        rw [Finset.sum_eq_single x]
        · rw [ite_eq_left rfl, mul_div_assoc, div_self hne, mul_one]
        · intro y _ hy
          rw [ite_eq_right (Ne.symm hy), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ x) h

omit [DecidableEq ι] in
/-- Every function on the cube has degree at most the number of coordinates. -/
theorem hasDegreeLE_card (f : Cube ι → ℝ) : HasDegreeLE f (Fintype.card ι) := by
  classical
  exact ⟨fourier f, fun S hS => absurd (Finset.card_le_univ S) (not_le.mpr hS),
    fun x => (fourier_inversion f x).symm⟩

/-- The coefficients of a character expansion are unique: they are the Fourier coefficients. -/
theorem fourier_unique {f : Cube ι → ℝ} {c : Finset ι → ℝ}
    (hf : ∀ x, f x = ∑ S, c S * chi S x) (T : Finset ι) : c T = fourier f T := by
  have hne : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  have h1 : ∑ y, f y * chi T y = c T * 2 ^ Fintype.card ι := by
    calc ∑ y, f y * chi T y
        = ∑ y, ∑ S : Finset ι, c S * (chi S y * chi T y) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [hf y, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun S _ => ?_)
          ring
      _ = ∑ S : Finset ι, c S * ∑ y, chi S y * chi T y := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ S : Finset ι, c S * (if S = T then (2 : ℝ) ^ Fintype.card ι else 0) := by
          simp only [sum_chi_mul_chi_cube]
      _ = c T * 2 ^ Fintype.card ι := by
          rw [Finset.sum_eq_single T]
          · rw [ite_eq_left rfl]
          · intro S _ hS
            rw [ite_eq_right hS, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ T) h
  rw [fourier, h1, mul_div_assoc, div_self hne, mul_one]

/-- `HasDegreeLE f d` says exactly that the Fourier coefficients above level `d` vanish. -/
theorem hasDegreeLE_iff_fourier {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔ ∀ S : Finset ι, d < S.card → fourier f S = 0 := by
  constructor
  · rintro ⟨c, hc, hf⟩ S hS
    rw [← fourier_unique hf S]
    exact hc S hS
  · intro h
    exact ⟨fourier f, h, fun x => (fourier_inversion f x).symm⟩

theorem fourier_chi (S T : Finset ι) : fourier (chi S) T = if S = T then 1 else 0 := by
  rw [fourier, sum_chi_mul_chi_cube]
  split_ifs
  · exact div_self (by positivity)
  · exact zero_div _

omit [DecidableEq ι] in
/-- A character `χ_S` has degree at most `d` exactly when `|S| ≤ d`. -/
theorem hasDegreeLE_chi_iff (S : Finset ι) (d : ℕ) : HasDegreeLE (chi S) d ↔ S.card ≤ d := by
  classical
  rw [hasDegreeLE_iff_fourier]
  constructor
  · intro h
    by_contra hlt
    have h1 := h S (not_le.mp hlt)
    rw [fourier_chi, ite_eq_left rfl] at h1
    exact one_ne_zero h1
  · intro h T hT
    rw [fourier_chi, ite_eq_right]
    rintro rfl
    exact absurd h (not_le.mpr hT)

omit [DecidableEq ι] in
/-- The full parity does not have degree `< n`: `HasDegreeLE` is not trivially true. -/
theorem parity_not_hasDegreeLE {d : ℕ} (hd : d < Fintype.card ι) :
    ¬ HasDegreeLE (chi (univ : Finset ι)) d := by
  classical
  rw [hasDegreeLE_chi_iff, Finset.card_univ]
  exact not_le.mpr hd

end AaronsonAmbainis.Bridge
