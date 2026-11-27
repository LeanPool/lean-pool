/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt module imports and source presentation. -/

module

public import LeanPool.VenNullClockRoundRates.VenRateUpperHeight
public import LeanPool.VenNullClockRoundRates.VenRateUpperPositive
public import LeanPool.VenNullClockRoundRates.VenRateUpperTaylor
public import LeanPool.VenNullClockRoundRates.VenRateUpperBudget
public import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Assembly of the exponential bound from two opposite pushforward cutoffs.
The chart law supplying the two integral identities is used separately. -/

@[expose] public section
open MeasureTheory
open scoped ContDiff

namespace VenRateUpper

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]

private theorem compact_integrable [OpensMeasurableSpace Ω] [CompactSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {g : Ω → ℝ} (hg : Continuous g) : Integrable g μ :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

private noncomputable def correctionFunctional [OpensMeasurableSpace Ω] [CompactSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {q F : Ω → ℝ} (hq : Continuous q) (hF : Continuous F) :
    Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun P := -(∫ y, q y * 2 * P.eval (F y) ∂μ)
  map_add' P Q := by
    simp only [Polynomial.eval_add]
    simp_rw [mul_add]
    have hp : Integrable (fun y => q y * 2 * P.eval (F y)) μ :=
      compact_integrable μ ((hq.mul continuous_const).mul (P.continuous.comp hF))
    have hq' : Integrable (fun y => q y * 2 * Q.eval (F y)) μ :=
      compact_integrable μ ((hq.mul continuous_const).mul (Q.continuous.comp hF))
    rw [integral_add hp hq', neg_add]
  map_smul' a P := by
    change -(∫ y, q y * 2 * (a • P).eval (F y) ∂μ) =
      a * -(∫ y, q y * 2 * P.eval (F y) ∂μ)
    simp only [Polynomial.eval_smul, smul_eq_mul]
    have eqHere : (fun y => q y * 2 * (a * P.eval (F y))) =
        fun y => a * (q y * 2 * P.eval (F y)) := by
      funext y
      ring
    rw [eqHere, integral_const_mul, mul_neg]

private theorem correctionFunctional_bounded [OpensMeasurableSpace Ω] [CompactSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q F : Ω → ℝ} (hq : Continuous q) (hF : Continuous F) {Q : ℝ}
    (qBdd : ∀ y, |q y| ≤ Q) (height : ∀ y, F y ∈ Set.Icc (-1 : ℝ) 1)
    (P : Polynomial ℝ) (A : ℝ)
    (hP : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |P.eval u| ≤ A) :
    |correctionFunctional μ hq hF P| ≤ (2 * Q) * A := by
  have hA : 0 ≤ A := (abs_nonneg (P.eval 0)).trans (hP 0 (by norm_num))
  change |-(∫ y, q y * 2 * P.eval (F y) ∂μ)| ≤ _
  rw [abs_neg]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ _ : Ω, (2 * Q) * A ∂μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall fun y => ?_)
      change |q y * 2 * P.eval (F y)| ≤ _
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_comm |q y| 2]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (qBdd y) (by norm_num)) (hP _ (height y))
        (abs_nonneg _) (by
          have hQ := (abs_nonneg (q y)).trans (qBdd y)
          positivity)
    _ = _ := by simp

private theorem succ_le_pow_two (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < 2 ^ n := by positivity
    omega

theorem exponential_upper_of_twoStripIdentities [OpensMeasurableSpace Ω] [CompactSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F H q chiPlus chiMinus : Ω → ℝ}
    {η ψ : ℝ → ℝ} {t₀ t₁ ℓ B Q Aplus Aminus a : ℝ}
    (hF : Continuous F) (hH : Continuous H) (hq : Continuous q) (hPlus : Continuous chiPlus)
    (hMinus : Continuous chiMinus) (hη : Continuous η) (suppη : HasCompactSupport η)
    (hψ : ContDiff ℝ ∞ ψ) (normψ : (∫ t, ψ t) = 1)
    (supψ : ∀ t, |ψ t| ≤ B) (suppψ : ∀ t ∉ Set.Icc t₀ t₁, ψ t = 0)
    (hℓ : 0 < ℓ) (h₀ : -1 ≤ t₀) (h₁ : t₁ + ℓ ≤ 1)
    (hfη : ∀ t ∈ Set.Icc t₀ (t₁ + ℓ), η t = 1)
    (height : ∀ y, F y ∈ Set.Icc (0 : ℝ) 1)
    (rangeH : ∀ y, H y ∈ Set.Icc (-1 : ℝ) 1)
    (heightRelation : ∀ y, F y = (1 - (H y) ^ 2) ^ 2) (qBdd : ∀ y, |q y| ≤ Q)
    (plusBdd : ∀ y, chiPlus y ∈ Set.Icc (0 : ℝ) Aplus)
    (minusBdd : ∀ y, chiMinus y ∈ Set.Icc (0 : ℝ) Aminus)
    (hQ : 0 ≤ Q)
    (ha : 0 ≤ a)
    (identityPlus : ∀ g : ℝ → ℝ, Continuous g →
      (∫ y, q y * chiPlus y * g (H y) ∂μ) = ∫ t, η t * g t)
    (identityMinus : ∀ g : ℝ → ℝ, Continuous g →
      (∫ y, q y * chiMinus y * g (H y) ∂μ) = -(∫ t, η t * g t)) :
    ∃ c M₁ : ℝ, 0 < c ∧ 1 < M₁ ∧ ∀ M ≥ M₁, ∃ (ρ : ℝ → ℝ) (K : ℝ),
      ContDiff ℝ ∞ ρ ∧ (∀ y, twoStripProfile H chiPlus chiMinus ρ K y ∈ Set.Icc (2 : ℝ) M) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) a,
        |∫ y, (q y * twoStripProfile H chiPlus chiMinus ρ K y) *
           Real.exp (x * F y) ∂μ| ≤ Real.exp (-c * Real.log M * Real.log (Real.log M)) := by
  let L := correctionFunctional μ hq hH
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (supψ 0)
  let Kbase := B * (2 * Q)
  let R := max 1 (4 * Real.exp 1 / ℓ)
  let D := (2 * R) ^ 4
  let A := max D (2 + (2 * Aplus + Aminus) * Kbase)
  have R1 : 1 ≤ R := le_max_left _ _
  have D2 : 2 ≤ D := by
    have Hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (show (2 : ℝ) ≤ 2 * R by linarith only [R1]) 4
    calc
      (2 : ℝ) ≤ 2 ^ 4 := by norm_num
      _ ≤ D := Hpower
  have Agt : 1 < A := (by norm_num : (1 : ℝ) < 2).trans_le (D2.trans (le_max_left _ _))
  have Kbase0 : 0 ≤ Kbase := mul_nonneg hB (mul_nonneg (by norm_num) hQ)
  obtain ⟨c, M₁, hc, hM₁, budget⟩ := exists_factorial_budget_with_kernel
    Agt ha (show 0 ≤ Q * Real.exp a from mul_nonneg hQ (Real.exp_pos a).le)
  refine ⟨c, M₁, hc, hM₁,?_⟩
  intro M hM
  obtain ⟨n, hn, cost, tail⟩ := budget M hM
  obtain ⟨ρ, hρ, suppρ, supρ, momρ⟩ := smooth_height_moment_correction
    (4 * n) (by omega) ℓ t₀ t₁ B (2 * Q) hℓ h₀ h₁ hB (mul_nonneg (by norm_num) hQ)
    L (correctionFunctional_bounded μ hq hH qBdd rangeH) ψ hψ normψ supψ suppψ
  let K := Kbase * D ^ n
  have hK : 0 ≤ K := mul_nonneg Kbase0 (pow_nonneg (by linarith only [D2]) _)
  have supρ' (t : ℝ) : |ρ t| ≤ K := by
    have hn2 : ((4 * n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (4 * n) := by
      exact_mod_cast succ_le_pow_two (4 * n)
    have hpow : (4 * Real.exp 1 / ℓ) ^ (4 * n) ≤ R ^ (4 * n) :=
      pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
    calc
      _ ≤ ((4 * n + 1 : ℕ) : ℝ) * (B * ((2 * Q) * (4 * Real.exp 1 / ℓ) ^ (4 * n))) := supρ t
      _ = Kbase * (((4 * n + 1 : ℕ) : ℝ) * (4 * Real.exp 1 / ℓ) ^ (4 * n)) := by dsimp [Kbase]; ring
      _ ≤ Kbase * ((2 : ℝ) ^ (4 * n) * R ^ (4 * n)) := by
        apply mul_le_mul_of_nonneg_left _ Kbase0
        exact mul_le_mul hn2 hpow (by positivity) (by positivity)
      _ = K := by rw [← mul_pow, pow_mul]
  let w := twoStripProfile H chiPlus chiMinus ρ K
  have Dn : 1 ≤ D ^ n := one_le_pow₀ ((by norm_num : (1 : ℝ) ≤ 2).trans D2)
  have Apow : D ^ n ≤ A ^ n := pow_le_pow_left₀ (by linarith only [D2]) (le_max_left _ _) _
  have cap : 2 + Aplus * (2 * K) + Aminus * K ≤ A ^ (n + 1) := by
    rw [pow_succ']
    calc
      _ = 2 + ((2 * Aplus + Aminus) * Kbase) * D ^ n := by dsimp [K]; ring
      _ ≤ (2 + (2 * Aplus + Aminus) * Kbase) * D ^ n := by nlinarith only [Dn]
      _ ≤ A * A ^ n := mul_le_mul (le_max_right _ _) Apow (by positivity)
        (zero_lt_one.trans Agt).le
  have hw (y : Ω) : w y ∈ Set.Icc (2 : ℝ) (A ^ (n + 1)) := by
    obtain ⟨hl, hu⟩ := twoStripProfile_bounds H chiPlus chiMinus ρ hK supρ' plusBdd minusBdd y
    exact ⟨hl, hu.trans cap⟩
  have eta_rho (t : ℝ) : η t * ρ t = ρ t := by
    by_cases hi : t ∈ Set.Icc t₀ (t₁ + ℓ)
    · rw [hfη t hi, one_mul]
    · rw [suppρ t hi, mul_zero]
  have moments (j : ℕ) (hj : j < n + 1) : (∫ y, (q y * w y) * F y ^ j ∂μ) = 0 := by
    let P : Polynomial ℝ := ((1 - Polynomial.X ^ 2) ^ 2) ^ j
    have Pval (t : ℝ) : P.eval t = ((1 - t ^ 2) ^ 2) ^ j := by simp [P]
    have Ph (y : Ω) : F y ^ j = P.eval (H y) := by rw [heightRelation y, Pval]
    have Psub : (1 - (Polynomial.X : Polynomial ℝ) ^ 2).natDegree ≤ 2 :=
      (Polynomial.natDegree_sub_le _ _).trans (by simp)
    have Pnat : P.natDegree ≤ 4 * j := by
      dsimp [P]
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow]
      calc
        _ ≤ j * (2 * 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ Psub)
        _ = 4 * j := by omega
    have Pdeg : P.degree < ((4 * n + 1 : ℕ) : WithBot ℕ) := by
      apply Polynomial.degree_le_natDegree.trans_lt
      exact_mod_cast (show P.natDegree < 4 * n + 1 by omega)
    have hstrip := integral_twoStripProfile (f := fun t : ℝ => P.eval t) μ K hH hq hPlus hMinus hη
      suppη hρ.continuous P.continuous eta_rho identityPlus identityMinus
    simp_rw [Ph]
    change (∫ y, q y * twoStripProfile H chiPlus chiMinus ρ K y * P.eval (H y) ∂μ) = 0
    rw [hstrip, momρ P Pdeg]
    change (∫ y, q y * 2 * P.eval (H y) ∂μ) + -(∫ y, q y * 2 * P.eval (H y) ∂μ) = 0
    exact add_neg_cancel _
  have wCont : Continuous w :=
    (continuous_const.add (hPlus.mul (continuous_const.add (hρ.continuous.comp hH)))).add
      (hMinus.mul continuous_const)
  have supQ (y : Ω) : |q y * w y| ≤ Q * A ^ (n + 1) := by
    have hw0 : 0 ≤ w y := (by norm_num : (0 : ℝ) ≤ 2).trans (hw y).1
    rw [abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul (qBdd y) (hw y).2 hw0 hQ
  refine ⟨ρ, K, hρ, fun y => ⟨(hw y).1, (hw y).2.trans cost⟩,?_⟩
  intro x hx
  have est := exponential_integral_le_of_zero_moments μ F (fun y => q y * w y) hF.measurable
    height (compact_integrable μ (hq.mul wCont)) (by positivity : 0 ≤ Q * A ^ (n + 1))
    supQ (n + 1) moments hx.1 hx.2
  calc
    _ ≤ Q * A ^ (n + 1) * (a ^ (n + 1) / ((n + 1).factorial : ℝ) * Real.exp a) := est
    _ = Q * Real.exp a * A ^ (n + 1) * a ^ (n + 1) / ((n + 1).factorial : ℝ) := by ring
    _ ≤ _ := tail

end VenRateUpper
