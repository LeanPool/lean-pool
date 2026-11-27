/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

module
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Smooth correction of finitely many height moments
-/

@[expose] public section
open Finset
open scoped ContDiff Nat

namespace VenRateUpper

private theorem grid_below_prod (i : ℕ) :
    (∏ j ∈ range i, |(i : ℝ) - (j : ℝ)|) = (i ! : ℝ) := by
  calc
    _ = ∏ j ∈ range i, ((j : ℝ) + 1) := by
      refine Finset.prod_bij' (fun j _ => i - 1 - j) (fun j _ => i - 1 - j) ?_ ?_ ?_ ?_ ?_
      · intro j hj
        have hj' := mem_range.mp hj
        exact mem_range.mpr (by omega)
      · intro j hj
        have hj' := mem_range.mp hj
        exact mem_range.mpr (by omega)
      · intro j hj
        have hj' := mem_range.mp hj
        omega
      · intro j hj
        have hj' := mem_range.mp hj
        omega
      · intro j hj
        have hj' := mem_range.mp hj
        have hij : (i : ℝ) - (j : ℝ) = ((i - 1 - j : ℕ) : ℝ) + 1 := by
          have he : (i - 1 - j : ℕ) + j + 1 = i := by omega
          have herm : ((i - 1 - j : ℕ) : ℝ) + (j : ℝ) + 1 = (i : ℝ) := by exact_mod_cast he
          linarith
        rw [hij, abs_of_nonneg]
        positivity
    _ = _ := by exact_mod_cast Finset.prod_range_add_one_eq_factorial i

private theorem grid_above_prod (n i : ℕ) (hi : i ≤ n) :
    (∏ j ∈ Ico (i + 1) (n + 1), |(i : ℝ) - (j : ℝ)|) = ((n - i)! : ℝ) := by
  calc
    _ = ∏ j ∈ range (n - i), ((j : ℝ) + 1) := by
      refine Finset.prod_bij' (fun j _ => j - i - 1) (fun j _ => j + i + 1) ?_ ?_ ?_ ?_ ?_
      · intro j hj
        have H := mem_Ico.mp hj
        exact mem_range.mpr (by omega)
      · intro j hj
        have H := mem_range.mp hj
        exact mem_Ico.mpr ⟨by omega, by omega⟩
      · intro j hj
        have H := mem_Ico.mp hj
        omega
      · intro j hj
        have H := mem_range.mp hj
        omega
      · intro j hj
        have H := mem_Ico.mp hj
        have hej : (i : ℝ) + ((j - i - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
          exact_mod_cast (show i + (j - i - 1) + 1 = j by omega)
        rw [abs_of_nonpos] <;> linarith [show (0 : ℝ) ≤ ((j - i - 1 : ℕ) : ℝ) by positivity]
    _ = _ := by exact_mod_cast Finset.prod_range_add_one_eq_factorial (n - i)

theorem absolute_grid_denominator (n i : ℕ) (hi : i ≤ n) :
    (∏ j ∈ (range (n + 1)).erase i, |(i : ℝ) - (j : ℝ)|) =
      (i ! : ℝ) * ((n - i)! : ℝ) := by
  classical
  have hs : (range (n + 1)).erase i = range i ∪ Ico (i + 1) (n + 1) := by
    ext j
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    omega
  have hd : Disjoint (range i) (Ico (i + 1) (n + 1)) := by
    refine Finset.disjoint_left.mpr ?_
    intro j h1 h2
    have h1' := mem_range.mp h1
    have h2' := mem_Ico.mp h2
    omega
  rw [hs, Finset.prod_union hd, grid_below_prod, grid_above_prod n i hi]

private theorem factorial_ratio_bound (n i : ℕ) (hi : i ≤ n) :
    (n : ℝ) ^ n / ((i ! : ℝ) * ((n - i)! : ℝ)) ≤ (2 * Real.exp 1) ^ n := by
  have hF : 0 < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hDi : 0 < (i ! : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hDj : 0 < ((n - i)! : ℝ) := by exact_mod_cast Nat.factorial_pos (n - i)
  have hD : 0 < (i ! : ℝ) * ((n - i)! : ℝ) := mul_pos hDi hDj
  have hN : (n : ℝ) ^ n / (n ! : ℝ) ≤ Real.exp 1 ^ n := by
    calc
      _ ≤ ∑ j ∈ range (n + 1), (n : ℝ) ^ j / (j ! : ℝ) := by
        apply Finset.single_le_sum (f := fun j : ℕ => (n : ℝ) ^ j / (j ! : ℝ))
        · intro j _
          positivity
        · exact mem_range.mpr (by omega)
      _ ≤ Real.exp (n : ℝ) := Real.sum_le_exp_of_nonneg (by positivity) _
      _ = _ := by rw [← Real.exp_nat_mul]; simp
  have hQ : (n ! : ℝ) / ((i ! : ℝ) * ((n - i)! : ℝ)) = (n.choose i : ℝ) := by
    apply (div_eq_iff hD.ne').2
    have hh := Nat.choose_mul_factorial_mul_factorial hi
    exact_mod_cast (show n ! = n.choose i * (i ! * (n - i)!) by simpa [Nat.mul_assoc] using hh.symm)
  have hB : (n.choose i : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.choose_le_two_pow n i
  calc
    _ = ((n : ℝ) ^ n / (n ! : ℝ)) * ((n ! : ℝ) / ((i ! : ℝ) * ((n - i)! : ℝ))) := by
      field_simp
    _ ≤ (Real.exp 1) ^ n * (2 : ℝ) ^ n := by
      rw [hQ]
      gcongr
    _ = _ := by rw [← mul_pow, mul_comm]

/-- Exponential, not n^n, growth of Lagrange interpolation after translating an equally
spaced grid of fixed total diameter. The parameter s is a common translation. -/
theorem translated_grid_lagrange_bound
    (n i : ℕ) (hn : n ≠ 0) (hi : i ≤ n) (ℓ s u B : ℝ) (hℓ : 0 < ℓ) (hB : 0 ≤ B)
    (hyp : ∀ j ≤ n, |u - (s + ℓ * j / n)| ≤ B) :
    |(Lagrange.basis (range (n + 1)) (fun j : ℕ => s + ℓ * j / n) i).eval u|
      ≤ (B * (2 * Real.exp 1) / ℓ) ^ n := by
  classical
  have hn' : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  let T := (range (n + 1)).erase i
  have hcard : #T = n := by
    dsimp [T]
    rw [card_erase_of_mem (mem_range.mpr (by omega)), card_range, Nat.add_sub_cancel]
  have hdiff (j : ℕ) : |(s + ℓ * (i : ℝ) / n) - (s + ℓ * (j : ℝ) / n)| =
      (ℓ / n) * |(i : ℝ) - (j : ℝ)| := by
    rw [← abs_of_pos (div_pos hℓ hn'), ← abs_mul]
    congr 1
    ring
  change |(∏ j ∈ T, Lagrange.basisDivisor (s + ℓ * i / n) (s + ℓ * j / n)).eval u| ≤ _
  simp only [Polynomial.eval_prod, Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, abs_prod, abs_mul, abs_inv]
  rw [show (∏ j ∈ T, |s + ℓ * (i : ℝ) / n - (s + ℓ * (j : ℝ) / n)|⁻¹ *
        |u - (s + ℓ * (j : ℝ) / n)|) =
      (∏ j ∈ T, |u - (s + ℓ * (j : ℝ) / n)|) /
        (∏ j ∈ T, |s + ℓ * (i : ℝ) / n - (s + ℓ * (j : ℝ) / n)|) by
      simp_rw [mul_comm (_⁻¹)]
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      exact (div_eq_mul_inv _ _).symm]
  have hden : (∏ j ∈ T, |s + ℓ * (i : ℝ) / n - (s + ℓ * (j : ℝ) / n)|) =
      (ℓ / n) ^ n * ((i ! : ℝ) * ((n - i)! : ℝ)) := by
    simp_rw [hdiff]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, absolute_grid_denominator n i hi]
  rw [hden]
  have hDi : 0 < (i ! : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hDj : 0 < ((n - i)! : ℝ) := by exact_mod_cast Nat.factorial_pos (n - i)
  have hgood : 0 < (ℓ / (n : ℝ)) ^ n * ((i ! : ℝ) * ((n - i)! : ℝ)) := by positivity
  have hnum : (∏ j ∈ T, |u - (s + ℓ * (j : ℝ) / n)|) ≤ B ^ n := by
    calc
      _ ≤ ∏ _j ∈ T, B := by
        refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j hj => hyp j ?_)
        exact Nat.lt_succ_iff.mp (mem_range.mp (mem_erase.mp hj).2)
      _ = _ := by rw [Finset.prod_const, hcard]
  calc
    _ ≤ B ^ n / ((ℓ / (n : ℝ)) ^ n * ((i ! : ℝ) * ((n - i)! : ℝ))) :=
      div_le_div_of_nonneg_right hnum hgood.le
    _ = (B / ℓ) ^ n * ((n : ℝ) ^ n / ((i ! : ℝ) * ((n - i)! : ℝ))) := by
      rw [div_pow, div_pow]
      field_simp
    _ ≤ (B / ℓ) ^ n * (2 * Real.exp 1) ^ n := by
      exact mul_le_mul_of_nonneg_left (factorial_ratio_bound n i hi) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

/-- Pointwise exact redistribution of a polynomial linear functional onto each
translated grid. Smooth averaging over translations does not alter any of these moments. -/
theorem translated_grid_moment_identity
    (n : ℕ) (hn : n ≠ 0) (ℓ s : ℝ) (hℓ : 0 < ℓ)
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (P : Polynomial ℝ)
    (hP : P.degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    (∑ j ∈ range (n + 1), P.eval (s + ℓ * j / n) *
      L (Lagrange.basis (range (n + 1)) (fun i : ℕ => s + ℓ * i / n) j)) = L P := by
  classical
  let nodes := fun i : ℕ => s + ℓ * (i : ℝ) / (n : ℝ)
  have hdiv : 0 < (ℓ / (n : ℝ)) := div_pos hℓ (by exact_mod_cast Nat.pos_of_ne_zero hn)
  have hinj : Function.Injective nodes := by
    intro i j h
    have heq : (ℓ / (n : ℝ)) * (i : ℝ) = (ℓ / (n : ℝ)) * (j : ℝ) := by
      dsimp [nodes] at h
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      linarith
    exact_mod_cast ((mul_right_inj' (ne_of_gt hdiv)).mp heq)
  have interp : Lagrange.interpolate (range (n + 1)) nodes (fun j => P.eval (nodes j)) = P := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq _ hinj.injOn
    · exact Lagrange.degree_interpolate_lt _ hinj.injOn
    · simpa only [Finset.card_range] using hP
    · intro j hj
      exact Lagrange.eval_interpolate_at_node _ hinj.injOn hj
  have res := congrArg L interp
  dsimp [nodes] at res ⊢
  simpa only [Lagrange.interpolate_apply, ← Polynomial.smul_eq_C_mul,
    map_sum, map_smul, smul_eq_mul] using res

open MeasureTheory

/-- Integrating a translated family of exact moment identities gives an exact Lebesgue
redistribution density. This statement deals only with height, not the spherical lift. -/
theorem averaged_grid_moments {ι : Type*} (T : Finset ι) (x : ι → ℝ)
    (ψ : ℝ → ℝ) (v : ι → ℝ → ℝ) (P : Polynomial ℝ) (m : ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hψ₁ : ∫ s, ψ s = (1 : ℝ))
    (hv : ∀ i ∈ T, Continuous (v i))
    (hm : ∀ s, (∑ i ∈ T, P.eval (s + x i) * v i s) = m) :
    (∫ t : ℝ, P.eval t * ∑ i ∈ T, (ψ (t - x i) * v i (t - x i))) = m := by
  let f (i : ι) (s : ℝ) := P.eval (s + x i) * (ψ s * v i s)
  have hf (i) (hi : i ∈ T) : Integrable (f i) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (P.continuous.comp (continuous_id.add continuous_const)).mul (hψ.mul (hv i hi))
    · change HasCompactSupport (fun s => P.eval (s + x i) * (ψ s * v i s))
      exact (hc.mul_right (f' := v i)).mul_left
  have hs (i) (y : ℝ) : f i (y - x i) = P.eval y * (ψ (y - x i) * v i (y - x i)) := by
    simp [f]
  simp_rw [Finset.mul_sum, ← hs]
  rw [integral_finsetSum _ (fun i hi => (hf i hi).comp_sub_right (x i))]
  simp_rw [integral_sub_right_eq_self]
  rw [← integral_finsetSum _ hf]
  have H (s : ℝ) : (∑ i ∈ T, f i s) = m * ψ s := by
    calc
      _ = (∑ i ∈ T, P.eval (s + x i) * v i s) * ψ s := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by dsimp [f]; ring
      _ = _ := by rw [hm]
  simp_rw [H, integral_const_mul, hψ₁, mul_one]

/-- Translating every node has the same effect as translating the evaluation variable backwards. -/
theorem basis_shift {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (x : ι → ℝ) (s : ℝ) (i : ι) :
    Lagrange.basis T (fun j => s + x j) i =
      (Lagrange.basis T x i).comp (Polynomial.X - Polynomial.C s) := by
  simp only [Lagrange.basis, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Lagrange.basisDivisor, Polynomial.mul_comp, Polynomial.sub_comp,
    Polynomial.C_comp, Polynomial.X_comp,
    show s + x i - (s + x j) = x i - x j by ring]
  congr 1
  rw [map_add]
  ring

/-- Applying an arbitrary polynomial linear functional after translating the evaluation variable
gives a polynomial in the amount of translation. No topology on the space of polynomials is used. -/
theorem functional_polynomial_shift (L : Polynomial ℝ →ₗ[ℝ] ℝ) (P : Polynomial ℝ) :
    ∃ Q : Polynomial ℝ, ∀ s, Q.eval s =
      L (P.comp (Polynomial.X - Polynomial.C s)) := by
  classical
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      obtain ⟨U, hU⟩ := hP
      obtain ⟨V, hV⟩ := hQ
      exact ⟨U + V, fun s => by simp [Polynomial.add_comp, hU s, hV s]⟩
  | monomial n a =>
      let R : Polynomial ℝ := ∑ j ∈ range (n + 1),
        Polynomial.C ((n.choose j : ℝ) * L (Polynomial.C a * Polynomial.X ^ j)) *
          (-Polynomial.X) ^ (n - j)
      refine ⟨R, fun s => ?_⟩
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.pow_comp, Polynomial.X_comp, sub_eq_add_neg, add_pow,
        Finset.mul_sum, map_sum]
      simp only [R, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_X]
      refine Finset.sum_congr rfl fun j _ => ?_
      -- Pull all scalar factors outside the arbitrary linear functional.
      rw [← Polynomial.C_neg, ← Polynomial.C_pow, ← Polynomial.C_eq_natCast]
      conv_rhs =>
        rw [show Polynomial.C a * (Polynomial.X ^ j * Polynomial.C ((-s) ^ (n - j)) *
          Polynomial.C (n.choose j : ℝ)) =
          Polynomial.C (((-s) ^ (n - j)) * (n.choose j : ℝ)) *
            (Polynomial.C a * Polynomial.X ^ j) by rw [Polynomial.C_mul]; ring]
      simp_rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
      ring

private theorem smooth_eval {order : ℕ∞ω} (P : Polynomial ℝ) : ContDiff ℝ order (fun x =>
  P.eval x) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add] using hP.add hQ
  | monomial n a => simpa only [Polynomial.eval_monomial] using
      (contDiff_const.mul (contDiff_id.pow n) : ContDiff ℝ order (fun x : ℝ => a * x ^ n))

/-- A signed height correction with exact moments and exponential uniform cost. The bump
may have any differentiability order, including `∞` for smooth functions, and is normalized
and supported in the chosen translation interval. The correction has the same regularity.
The source linear functional is bounded on `[-1, 1]`. -/
theorem smooth_height_moment_correction {order : ℕ∞ω}
    (n : ℕ) (hn : n ≠ 0) (ℓ t₀ t₁ B N : ℝ) (hℓ : 0 < ℓ)
    (ht₀ : -1 ≤ t₀) (ht₁ : t₁ + ℓ ≤ 1) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ (P : Polynomial ℝ) (A : ℝ),
      (∀ u ∈ Set.Icc (-1 : ℝ) 1, |P.eval u| ≤ A) → |L P| ≤ N * A)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ order ψ) (hψ₁ : ∫ s, ψ s = (1 : ℝ))
    (hψsup : ∀ s, |ψ s| ≤ B) (hψsupp : ∀ s ∉ Set.Icc t₀ t₁, ψ s = 0) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ order ρ ∧
      (∀ t ∉ Set.Icc t₀ (t₁ + ℓ), ρ t = 0) ∧
      (∀ t, |ρ t| ≤ (n + 1 : ℕ) * (B * (N * (4 * Real.exp 1 / ℓ) ^ n))) ∧
      (∀ (P : Polynomial ℝ), P.degree < ((n + 1 : ℕ) : WithBot ℕ) →
        (∫ t, P.eval t * ρ t) = L P) := by
  classical
  let T := range (n + 1)
  let x : ℕ → ℝ := fun i => ℓ * (i : ℝ) / (n : ℝ)
  let k : ℕ → ℝ → ℝ := fun i s => L (Lagrange.basis T (fun j => s + x j) i)
  let term : ℕ → ℝ → ℝ := fun i t => ψ (t - x i) * k i (t - x i)
  let ρ : ℝ → ℝ := fun t => ∑ i ∈ T, term i t
  have hnk : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hxi (i : ℕ) (hi : i ∈ T) : x i ∈ Set.Icc 0 ℓ := by
    refine ⟨by dsimp [x]; positivity, ?_⟩
    have Hin : i ≤ n := by simpa [T] using hi
    have HR : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast Hin
    dsimp [x]
    exact (div_le_iff₀ hnk).2 (mul_le_mul_of_nonneg_left HR hℓ.le)
  have hk (i : ℕ) : ContDiff ℝ order (k i) := by
    obtain ⟨Q, hQ⟩ := functional_polynomial_shift L (Lagrange.basis T x i)
    have hh : k i = fun s => Q.eval s := by
      funext s
      exact ((hQ s).trans (congrArg L (basis_shift T x s i).symm)).symm
    rw [hh]
    exact smooth_eval Q
  have hcψ : HasCompactSupport ψ :=
    HasCompactSupport.intro' isCompact_Icc isClosed_Icc hψsupp
  refine ⟨ρ, ContDiff.sum fun i _ => ?_, ?_, ?_, ?_⟩
  · have hs : ContDiff ℝ order (fun t : ℝ => t - x i) := contDiff_id.sub contDiff_const
    exact (hψ.comp hs).mul ((hk i).comp hs)
  · intro t ht
    apply Finset.sum_eq_zero
    intro i hi
    have hx := hxi i hi
    have ht' : t - x i ∉ Set.Icc t₀ t₁ := by
      intro hm
      exact ht ⟨by linarith [hm.1, hx.1], by linarith [hm.2, hx.2]⟩
    dsimp [term]
    rw [hψsupp _ ht', zero_mul]
  · intro t
    calc
      _ ≤ ∑ i ∈ T, |term i t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ T, B * (N * (4 * Real.exp 1 / ℓ) ^ n) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hs : t - x i ∈ Set.Icc t₀ t₁
        · have Hin : i ≤ n := by simpa [T] using hi
          have hd : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ j ≤ n, |u - ((t - x i) + x j)| ≤ 2 := by
            intro u hu j hj
            have hx := hxi j (by simpa [T] using hj)
            exact abs_le.mpr ⟨by linarith [hu.1, hs.2, hx.2],
              by linarith [hu.2, hs.1, hx.1]⟩
          have hb : |k i (t - x i)| ≤ N * (4 * Real.exp 1 / ℓ) ^ n := by
            apply hL
            intro u hu
            convert translated_grid_lagrange_bound n i hn Hin ℓ (t - x i) u 2 hℓ
              (by norm_num) (hd u hu) using 1
            ring
          dsimp [term]
          rw [abs_mul]
          gcongr
          exact hψsup _
        · dsimp [term]
          rw [hψsupp _ hs, zero_mul, abs_zero]
          positivity
      _ = _ := by simp [T, mul_left_comm]
  · intro P hP
    exact averaged_grid_moments T x ψ k P (L P) hψ.continuous hcψ hψ₁
      (fun i _ => (hk i).continuous) (fun s =>
        translated_grid_moment_identity n hn ℓ s hℓ L P hP)

end VenRateUpper
end
