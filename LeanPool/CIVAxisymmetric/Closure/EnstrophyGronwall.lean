/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.L4L6
public import LeanPool.CIVAxisymmetric.Closure.SmallnessFromPower
public import LeanPool.CIVAxisymmetric.Analysis.GronwallVariable
public import LeanPool.CIVAxisymmetric.Analysis.TimeWeights
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Enstrophy Gronwall

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The substitution step that turns the localized energy inequality
`eq:aniso:closure:energy` into the differential inequality `closure_gronwall_bound`
consumes. Dropping the nonnegative dissipation `M` and inserting the two bounds
`G ≤ η/(-t)` of `eq:aniso:G:bound` and `W ≤ Cη (-t)^{-η}` of `eq:aniso:closure:w`
replaces the coefficient `Cstar (G + W² + 1)` by `Cstar (η/(-t) + Cη² (-t)^{-2η} + 1)`,
which is the integrand of the exponential in `lem:aniso:closure`. The squared swirl bound
uses `0 ≤ W`, which holds since `W` is a supremum norm, together with the identity
`((-t)^{-η})² = (-t)^{-2η}`, valid since `-t > 0`. -/
theorem deriv_le_of_closure_energy {Y M G W : ℝ → ℝ} {tη Cstar η Cη : ℝ}
    (hC : 0 ≤ Cstar)
    (hM : ∀ t ∈ Ioo tη 0, 0 ≤ M t)
    (hY : ∀ t ∈ Ioo tη 0, 0 ≤ Y t)
    (hG : ∀ t ∈ Ioo tη 0, G t ≤ η / (-t))
    (hW0 : ∀ t ∈ Ioo tη 0, 0 ≤ W t)
    (hW : ∀ t ∈ Ioo tη 0, W t ≤ Cη * (-t) ^ (-η))
    (henergy : ∀ t ∈ Ioo tη 0, deriv Y t + M t ≤ Cstar * (G t + W t ^ 2 + 1) * (Y t + 1)) :
    ∀ t ∈ Ioo tη 0,
      deriv Y t ≤ Cstar * (η / (-t) + Cη ^ 2 * (-t) ^ (-(2 * η)) + 1) * (Y t + 1) := by
  intro t ht
  have hneg : (0 : ℝ) < -t := neg_pos.mpr ht.2
  have hpow : ((-t) ^ (-η)) ^ 2 = (-t) ^ (-(2 * η)) := by
    rw [← Real.rpow_natCast ((-t) ^ (-η)) 2, ← Real.rpow_mul hneg.le]
    congr 1
    push_cast
    ring
  have hWsq : W t ^ 2 ≤ Cη ^ 2 * (-t) ^ (-(2 * η)) := by
    have hsq : W t ^ 2 ≤ (Cη * (-t) ^ (-η)) ^ 2 := by
      have hmul := mul_self_le_mul_self (hW0 t ht) (hW t ht)
      simpa [sq] using hmul
    rw [mul_pow, hpow] at hsq
    exact hsq
  have hsum : G t + W t ^ 2 + 1 ≤ η / (-t) + Cη ^ 2 * (-t) ^ (-(2 * η)) + 1 := by
    linarith only [hG t ht, hWsq]
  have hY1 : (0 : ℝ) ≤ Y t + 1 := by linarith only [hY t ht]
  have hmul : Cstar * (G t + W t ^ 2 + 1) * (Y t + 1)
      ≤ Cstar * (η / (-t) + Cη ^ 2 * (-t) ^ (-(2 * η)) + 1) * (Y t + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hC) hY1
  linarith only [henergy t ht, hM t ht, hmul]

private theorem closure_exponential_bound {tη Cstar η Cη : ℝ}
    (htη : tη < 0) (hC : 0 ≤ Cstar) (h2η_lt_one : 2 * η < 1) (hCη : 0 ≤ Cη)
    {t : ℝ} (ht : t ∈ Ioo tη 0) :
    Real.exp (∫ s in tη..t, Cstar * (η / (-s) + Cη ^ 2 * (-s) ^ (-(2 * η)) + 1)) ≤
      ((-tη) / (-t)) ^ (Cstar * η) *
        Real.exp (Cstar * Cη ^ 2 * (-tη) ^ (1 - 2 * η) / (1 - 2 * η)) *
        Real.exp (Cstar * (-tη)) := by
  set k : ℝ → ℝ := fun s => Cstar * (η / (-s) + Cη ^ 2 * (-s) ^ (-(2 * η)) + 1)
  have h_neg_tη_pos : 0 < -tη := neg_pos.mpr htη
  have hCη_sq : 0 ≤ Cη ^ 2 := pow_nonneg hCη 2
  have h_one_minus_2η_pos : 0 < 1 - 2 * η := by linarith only [h2η_lt_one]
  obtain ⟨ht_left, ht_right⟩ := ht
  have h_le : tη ≤ t := ht_left.le
  have h_neg_t_pos : 0 < -t := neg_pos.mpr ht_right
  have h_ne : ∀ s ∈ Icc tη t, -s ≠ 0 := by
    intro s hs
    exact (neg_pos.mpr (lt_of_le_of_lt hs.2 ht_right)).ne'
  have h_cont_neg : ContinuousOn (fun s : ℝ => -s) (Icc tη t) := continuous_neg.continuousOn
  -- integrability of the three pieces of k
  have h_cont_inv : ContinuousOn (fun s : ℝ => (-s)⁻¹) (Icc tη t) := h_cont_neg.inv₀ h_ne
  have h_intble_inv : IntervalIntegrable (fun s : ℝ => (-s)⁻¹) volume tη t :=
    h_cont_inv.intervalIntegrable_of_Icc h_le
  have h_cont_rpow : ContinuousOn (fun s : ℝ => (-s) ^ (-(2 * η))) (Icc tη t) :=
    h_cont_neg.rpow_const (fun s hs => Or.inl (h_ne s hs))
  have h_intble_rpow : IntervalIntegrable (fun s : ℝ => (-s) ^ (-(2 * η))) volume tη t :=
    h_cont_rpow.intervalIntegrable_of_Icc h_le
  have h_intble_one : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume tη t :=
    continuousOn_const.intervalIntegrable_of_Icc h_le
  have h_intble_div : IntervalIntegrable (fun s : ℝ => η / (-s)) volume tη t := by
    have h_fun : (fun s : ℝ => η / (-s)) = fun s : ℝ => η * (-s)⁻¹ := by
      funext s
      rw [div_eq_mul_inv]
    rw [h_fun]
    exact h_intble_inv.const_mul η
  have h_intble_term2 : IntervalIntegrable (fun s : ℝ => Cη ^ 2 * (-s) ^ (-(2 * η))) volume tη t :=
    h_intble_rpow.const_mul (Cη ^ 2)
  -- compute the integral of k
  have h_int_inv : ∫ s in tη..t, (-s)⁻¹ = Real.log (-tη) - Real.log (-t) :=
    integral_inv_neg ht_left ht_right
  have h_int_rpow : ∫ s in tη..t, (-s) ^ (-(2 * η)) = ((-tη) ^ (1 - 2 * η) - (-t) ^ (1 - 2 * η))
    / (1 - 2 * η) :=
    integral_neg_rpow ht_left ht_right.le h2η_lt_one
  have h_int_one : ∫ s in tη..t, (1 : ℝ) = t - tη := by simp
  have h_int_div : ∫ s in tη..t, η / (-s) = η * (Real.log (-tη) - Real.log (-t)) := by
    have h_fun : (∫ s in tη..t, η / (-s)) = ∫ s in tη..t, η * (-s)⁻¹ := by
      simp only [div_eq_mul_inv]
    rw [h_fun, intervalIntegral.integral_const_mul, h_int_inv]
  have h_int_term2 : ∫ s in tη..t, Cη ^ 2 * (-s) ^ (-(2 * η)) =
      Cη ^ 2 * (((-tη) ^ (1 - 2 * η) - (-t) ^ (1 - 2 * η)) / (1 - 2 * η)) := by
    rw [intervalIntegral.integral_const_mul, h_int_rpow]
  have h_int_k : ∫ s in tη..t, k s = Cstar * η * (Real.log (-tη) - Real.log (-t)) + Cstar * Cη ^
    2 * (((-tη) ^ (1 - 2 * η) - (-t) ^ (1 - 2 * η)) / (1 - 2 * η)) + Cstar * (t - tη) := by
    change (∫ s in tη..t, Cstar * (η / (-s) + Cη ^ 2 * (-s) ^ (-(2 * η)) + 1)) =
      Cstar * η * (Real.log (-tη) - Real.log (-t)) +
        Cstar * Cη ^ 2 * (((-tη) ^ (1 - 2 * η) - (-t) ^ (1 - 2 * η)) / (1 - 2 * η)) +
        Cstar * (t - tη)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (h_intble_div.add h_intble_term2) h_intble_one,
      intervalIntegral.integral_add h_intble_div h_intble_term2,
      h_int_div, h_int_term2, h_int_one]
    ring
  rw [h_int_k]
  -- expand exp(A + B + C) = exp A * exp B * exp C
  rw [Real.exp_add, Real.exp_add]
  -- the first factor is exactly ((-tη)/(-t))^(Cstar*η)
  have h_exp1 : Real.exp (Cstar * η * (Real.log (-tη) - Real.log (-t))) = ((-tη) / (-t)) ^
    (Cstar * η) := by
    rw [← Real.log_div h_neg_tη_pos.ne' h_neg_t_pos.ne',
      Real.rpow_def_of_pos (div_pos h_neg_tη_pos h_neg_t_pos) (Cstar * η),
      mul_comm (Cstar * η) (Real.log ((-tη) / (-t)))]
  -- bound the second factor
  have h_exp2 : Real.exp (Cstar * Cη ^ 2 * (((-tη) ^ (1 - 2 * η) - (-t) ^ (1 - 2 * η)) / (1 - 2
    * η))) ≤
      Real.exp (Cstar * Cη ^ 2 * (-tη) ^ (1 - 2 * η) / (1 - 2 * η)) := by
    have h_split : Cstar * Cη ^ 2 * (((-tη) ^ (1 - 2 * η) - (-t) ^ (1 - 2 * η)) / (1 - 2 * η)) =
        (Cstar * Cη ^ 2 * (-tη) ^ (1 - 2 * η) / (1 - 2 * η)) + (-Cstar * Cη ^ 2 * (-t) ^ (1 - 2
          * η) / (1 - 2 * η)) := by ring
    have h_nonneg : 0 ≤ Cstar * Cη ^ 2 * (-t) ^ (1 - 2 * η) :=
      mul_nonneg (mul_nonneg hC hCη_sq) (Real.rpow_nonneg h_neg_t_pos.le _)
    have h_quot_nonneg : 0 ≤ Cstar * Cη ^ 2 * (-t) ^ (1 - 2 * η) / (1 - 2 * η) :=
      div_nonneg h_nonneg h_one_minus_2η_pos.le
    have h_nonpos : -Cstar * Cη ^ 2 * (-t) ^ (1 - 2 * η) / (1 - 2 * η) ≤ 0 := by
      have h_neg_eq : -Cstar * Cη ^ 2 * (-t) ^ (1 - 2 * η) / (1 - 2 * η) =
          -(Cstar * Cη ^ 2 * (-t) ^ (1 - 2 * η) / (1 - 2 * η)) := by ring
      rw [h_neg_eq]
      linarith only [h_quot_nonneg]
    have h_exp_le_one : Real.exp (-Cstar * Cη ^ 2 * (-t) ^ (1 - 2 * η) / (1 - 2 * η)) ≤ 1 :=
      Real.exp_le_one_iff.mpr h_nonpos
    rw [h_split, Real.exp_add]
    exact mul_le_of_le_one_right (Real.exp_pos _).le h_exp_le_one
  -- bound the third factor
  have h_exp3 : Real.exp (Cstar * (t - tη)) ≤ Real.exp (Cstar * (-tη)) := by
    have h_split : Cstar * (t - tη) = Cstar * t + Cstar * (-tη) := by ring
    have h_prod_nonneg : 0 ≤ Cstar * (-t) := mul_nonneg hC h_neg_t_pos.le
    have h_nonpos : Cstar * t ≤ 0 := by linarith only [h_prod_nonneg]
    have h_exp_le_one : Real.exp (Cstar * t) ≤ 1 := Real.exp_le_one_iff.mpr h_nonpos
    rw [h_split, Real.exp_add]
    exact mul_le_of_le_one_left (Real.exp_pos _).le h_exp_le_one
  -- combine the bounds
  calc
    Real.exp (Cstar * η * (Real.log (-tη) - Real.log (-t))) * Real.exp (Cstar * Cη ^ 2 * (((-tη)
      ^ (1 - 2 * η) - (-t) ^ (1 - 2 * η)) / (1 - 2 * η))) * Real.exp (Cstar * (t - tη))
        ≤ Real.exp (Cstar * η * (Real.log (-tη) - Real.log (-t))) * Real.exp (Cstar * Cη ^ 2 *
          (-tη) ^ (1 - 2 * η) / (1 - 2 * η)) * Real.exp (Cstar * (t - tη)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h_exp2 (Real.exp_pos _).le) (Real.exp_pos _).le
    _ ≤ Real.exp (Cstar * η * (Real.log (-tη) - Real.log (-t))) * Real.exp (Cstar * Cη ^ 2 *
      (-tη) ^ (1 - 2 * η) / (1 - 2 * η)) * Real.exp (Cstar * (-tη)) :=
      mul_le_mul_of_nonneg_left h_exp3
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = ((-tη) / (-t)) ^ (Cstar * η) * Real.exp (Cstar * Cη ^ 2 * (-tη) ^ (1 - 2 * η) / (1 - 2 *
      η)) * Real.exp (Cstar * (-tη)) := by
      rw [h_exp1]

/-- Time-weighted Gronwall bound: if `Y` satisfies a differential inequality on `(tη, 0)`
with a singular weight `(-t)^(-Cstar*η)`, then `Y(t)+1` is bounded by a constant times
`(-t)^(-Cstar*η)`. This is the key estimate in the proof of
`lem:aniso:closure` in arXiv:2609.20803. -/
theorem closure_gronwall_bound {Y : ℝ → ℝ} {tη Cstar η Cη : ℝ} (htη : tη < 0) (hC : 0 ≤ Cstar)
    (hη : 0 < η ∧ 2 * η < 1) (hCη : 0 ≤ Cη)
    (hcont : ∀ t ∈ Ico tη 0, ContinuousOn Y (Icc tη t))
    (hderiv : ∀ t ∈ Ioo tη 0, HasDerivWithinAt Y (deriv Y t) (Ici t) t)
    (hY0 : 0 ≤ Y tη)
    (hineq : ∀ t ∈ Ioo tη 0,
      deriv Y t ≤ Cstar * (η / (-t) + Cη ^ 2 * (-t) ^ (-(2 * η)) + 1) * (Y t + 1)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Ioo tη 0, Y t + 1 ≤ C' * (-t) ^ (-(Cstar * η)) := by
  rcases hη with ⟨hη_pos, hη_lt_half⟩
  have h2η_lt_one : 2 * η < 1 := hη_lt_half
  have h_one_minus_2η_pos : 0 < 1 - 2 * η := by linarith only [h2η_lt_one]
  have hCη_sq : 0 ≤ Cη ^ 2 := pow_nonneg hCη 2
  set φ : ℝ → ℝ := fun t => Y t + 1 with hφ_def
  set k : ℝ → ℝ := fun s => Cstar * (η / (-s) + Cη ^ 2 * (-s) ^ (-(2 * η)) + 1) with hk_def
  have hφ0 : 0 ≤ φ tη := by
    rw [hφ_def]
    linarith only [hY0]
  have h_neg_tη_pos : 0 < -tη := neg_pos.mpr htη
  -- `deriv φ` and `deriv Y` agree, since `φ` differs from `Y` by a constant
  have h_deriv_eq : ∀ x : ℝ, deriv φ x = deriv Y x := by
    intro x
    rw [hφ_def]
    exact deriv_add_const 1
  -- φ has right derivative on Ioo tη 0
  have hderiv_φ : ∀ x ∈ Ioo tη 0, HasDerivWithinAt φ (deriv φ x) (Ici x) x := by
    intro x hx
    rw [h_deriv_eq x, hφ_def]
    exact (hderiv x hx).add_const 1
  -- inequality for deriv φ on Ioo tη 0
  have h_ineq_φ : ∀ x ∈ Ioo tη 0, deriv φ x ≤ k x * φ x := by
    intro x hx
    rw [h_deriv_eq x]
    change deriv Y x ≤ Cstar * (η / (-x) + Cη ^ 2 * (-x) ^ (-(2 * η)) + 1) * (Y x + 1)
    exact hineq x hx
  -- φ is continuous on [tη, t] for any t ∈ Ioo tη 0
  have h_cont_φ : ∀ t ∈ Ioo tη 0, ContinuousOn φ (Icc tη t) := by
    intro t ht
    have h_cont_Y : ContinuousOn Y (Icc tη t) := hcont t ⟨ht.1.le, ht.2⟩
    have h_cont_add : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc tη t) := continuousOn_const
    exact h_cont_Y.add h_cont_add
  -- k is continuous on [tη, t] for any t ∈ Ioo tη 0
  have h_cont_k : ∀ t ∈ Ioo tη 0, ContinuousOn k (Icc tη t) := by
    intro t ht
    have h_neg_ne_zero : ∀ s ∈ Icc tη t, -s ≠ 0 := by
      intro s hs
      exact (neg_pos.mpr (lt_of_le_of_lt hs.2 ht.2)).ne'
    have h_cont_neg : ContinuousOn (fun s : ℝ => -s) (Icc tη t) := continuous_neg.continuousOn
    have h_cont_div : ContinuousOn (fun s => η / (-s)) (Icc tη t) :=
      ContinuousOn.div continuousOn_const h_cont_neg h_neg_ne_zero
    have h_cont_rpow : ContinuousOn (fun s => (-s) ^ (-(2 * η))) (Icc tη t) :=
      h_cont_neg.rpow_const (fun s hs => Or.inl (h_neg_ne_zero s hs))
    have h_cont_term2 : ContinuousOn (fun s => Cη ^ 2 * (-s) ^ (-(2 * η))) (Icc tη t) :=
      continuousOn_const.mul h_cont_rpow
    have h_cont_sum : ContinuousOn (fun s => η / (-s) + Cη ^ 2 * (-s) ^ (-(2 * η)) + 1) (Icc tη
      t) :=
      (h_cont_div.add h_cont_term2).add continuousOn_const
    exact continuousOn_const.mul h_cont_sum
  -- k is nonnegative on [tη, t]
  have hk_nonneg : ∀ t ∈ Ioo tη 0, ∀ s ∈ Icc tη t, 0 ≤ k s := by
    intro t ht s hs
    have hs_lt_0 : s < 0 := lt_of_le_of_lt hs.2 ht.2
    have h_neg_pos : 0 < -s := neg_pos.mpr hs_lt_0
    change 0 ≤ Cstar * (η / (-s) + Cη ^ 2 * (-s) ^ (-(2 * η)) + 1)
    have h2 : 0 ≤ η / (-s) := div_nonneg hη_pos.le h_neg_pos.le
    have h3 : 0 ≤ Cη ^ 2 * (-s) ^ (-(2 * η)) :=
      mul_nonneg hCη_sq (Real.rpow_nonneg h_neg_pos.le _)
    have h4 : 0 ≤ η / (-s) + Cη ^ 2 * (-s) ^ (-(2 * η)) + 1 := by linarith only [h2, h3]
    exact mul_nonneg hC h4
  -- Define Φ(t) = φ(t) * exp(-∫_{tη}^{t} k)
  set Φ : ℝ → ℝ := fun x => φ x * Real.exp (-(∫ s in tη..x, k s)) with hΦ_def
  have hΦ_at_tη : Φ tη = φ tη := by
    change φ tη * Real.exp (-(∫ s in tη..tη, k s)) = φ tη
    rw [intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one]
  -- Φ is continuous on [tη, t] for any t ∈ Ioo tη 0
  have hΦ_cont : ∀ t ∈ Ioo tη 0, ContinuousOn Φ (Icc tη t) := by
    intro t ht
    have h_le : tη ≤ t := ht.1.le
    have h_cont_k_t : ContinuousOn k (Icc tη t) := h_cont_k t ht
    have h_intble : IntervalIntegrable k volume tη t :=
      h_cont_k_t.intervalIntegrable_of_Icc h_le
    have h_int_cont : ContinuousOn (fun x => ∫ s in tη..x, k s) (Icc tη t) := by
      have h_int_cont' : ContinuousOn (fun x => ∫ s in tη..x, k s) (Set.uIcc tη t) :=
        intervalIntegral.continuousOn_primitive_interval' h_intble left_mem_uIcc
      rwa [Set.uIcc_of_le h_le] at h_int_cont'
    have h_exp_cont : ContinuousOn (fun x => Real.exp (-(∫ s in tη..x, k s))) (Icc tη t) :=
      Real.continuous_exp.comp_continuousOn h_int_cont.neg
    exact (h_cont_φ t ht).mul h_exp_cont
  -- Φ is continuous at tη from the right
  have ht0_lt : tη < tη / 2 := by linarith only [htη]
  have ht0_mem : tη / 2 ∈ Ioo tη 0 := ⟨ht0_lt, by linarith only [htη]⟩
  have h_nhds_mem : Icc tη (tη / 2) ∈ 𝓝[≥] tη := by
    have h1 : Iic (tη / 2) ∈ 𝓝 tη := Iic_mem_nhds ht0_lt
    have h2 : Ici tη ∩ Iic (tη / 2) ∈ 𝓝[Ici tη] tη := inter_mem_nhdsWithin _ h1
    rwa [Set.Ici_inter_Iic] at h2
  have hΦ_cont_at : ContinuousWithinAt Φ (Ici tη) tη := by
    have h_cont_Φ_t0 : ContinuousOn Φ (Icc tη (tη / 2)) := hΦ_cont (tη / 2) ht0_mem
    exact (h_cont_Φ_t0 tη ⟨le_refl tη, ht0_lt.le⟩).mono_of_mem_nhdsWithin h_nhds_mem
  -- For each t ∈ Ioo tη 0, prove Φ t ≤ Φ tη by a limiting argument from the right
  have hΦ_le_φη : ∀ t ∈ Ioo tη 0, Φ t ≤ φ tη := by
    intro t ht
    obtain ⟨ht_left, ht_right⟩ := ht
    have h_cont_φ_t : ContinuousOn φ (Icc tη t) := h_cont_φ t ⟨ht_left, ht_right⟩
    have h_cont_k_t : ContinuousOn k (Icc tη t) := h_cont_k t ⟨ht_left, ht_right⟩
    -- For s in Ioo tη t we have Φ t ≤ Φ s, by the variable-coefficient Gronwall lemma on [s, t]
    have h_bound_aux : ∀ s, tη < s → s < t → Φ t ≤ Φ s := by
      intro s hs_gt_tη hs_lt_t
      have h_le : s ≤ t := hs_lt_t.le
      have h_sub : Icc s t ⊆ Icc tη t := Set.Icc_subset_Icc_left hs_gt_tη.le
      have h_gronwall_s := le_mul_exp_integral_of_deriv_le h_le
        (h_cont_φ_t.mono h_sub)
        (h_cont_k_t.mono h_sub)
        (fun x hx => hk_nonneg t ⟨ht_left, ht_right⟩ x (h_sub hx))
        (fun x hx => hderiv_φ x ⟨lt_of_lt_of_le hs_gt_tη hx.1, lt_trans hx.2 ht_right⟩)
        (fun x hx => h_ineq_φ x ⟨lt_of_lt_of_le hs_gt_tη hx.1, lt_trans hx.2 ht_right⟩)
        t ⟨h_le, le_refl t⟩
      -- h_gronwall_s : φ t ≤ φ s * Real.exp (∫ x in s..t, k x)
      have h_int_s : IntervalIntegrable k volume tη s :=
        (h_cont_k_t.mono (Set.Icc_subset_Icc_right h_le)).intervalIntegrable_of_Icc hs_gt_tη.le
      have h_int_st : IntervalIntegrable k volume s t :=
        (h_cont_k_t.mono h_sub).intervalIntegrable_of_Icc h_le
      have h_int_add : (∫ x in tη..t, k x) = (∫ x in tη..s, k x) + (∫ x in s..t, k x) :=
        (intervalIntegral.integral_add_adjacent_intervals h_int_s h_int_st).symm
      have h_arg : (∫ x in s..t, k x) + (-(∫ x in tη..t, k x)) = -(∫ x in tη..s, k x) := by
        rw [h_int_add]; ring
      calc
        Φ t = φ t * Real.exp (-(∫ x in tη..t, k x)) := rfl
        _ ≤ (φ s * Real.exp (∫ x in s..t, k x)) * Real.exp (-(∫ x in tη..t, k x)) :=
          mul_le_mul_of_nonneg_right h_gronwall_s (Real.exp_pos _).le
        _ = φ s * (Real.exp (∫ x in s..t, k x) * Real.exp (-(∫ x in tη..t, k x))) := by ring
        _ = φ s * Real.exp ((∫ x in s..t, k x) + (-(∫ x in tη..t, k x))) := by rw [Real.exp_add]
        _ = φ s * Real.exp (-(∫ x in tη..s, k x)) := by rw [h_arg]
        _ = Φ s := rfl
    -- Now construct the filter condition and pass to the limit s → tη⁺
    have h_mem : Ioo tη t ∈ 𝓝[>] tη := by
      rw [mem_nhdsGT_iff_exists_Ioo_subset' ht_left]
      exact ⟨t, ht_left, fun _ hy => hy⟩
    have h_bound : ∀ᶠ s in 𝓝[>] tη, Φ t ≤ Φ s := by
      filter_upwards [h_mem] with s hs_mem
      exact h_bound_aux s hs_mem.1 hs_mem.2
    have h_tendsto : Tendsto Φ (𝓝[>] tη) (𝓝 (Φ tη)) := by
      have htend : Tendsto Φ (𝓝[≥] tη) (𝓝 (Φ tη)) := hΦ_cont_at
      exact htend.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    have h_le_lim : Φ t ≤ Φ tη := ge_of_tendsto h_tendsto h_bound
    rwa [hΦ_at_tη] at h_le_lim
  -- From Φ t ≤ φ tη we get φ t ≤ φ tη * exp(∫ k)
  have h_gronwall : ∀ t ∈ Ioo tη 0, φ t ≤ φ tη * Real.exp (∫ s in tη..t, k s) := by
    intro t ht
    have hΦt : Φ t ≤ φ tη := hΦ_le_φη t ht
    have h_eq : φ t = Φ t * Real.exp (∫ s in tη..t, k s) := by
      have hΦval : Φ t = φ t * Real.exp (-(∫ s in tη..t, k s)) := rfl
      rw [hΦval, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [h_eq]
    exact mul_le_mul_of_nonneg_right hΦt (Real.exp_pos _).le
  -- Now bound the exponential factor
  have h_exp_bound : ∀ t ∈ Ioo tη 0, Real.exp (∫ s in tη..t, k s) ≤
      ((-tη) / (-t)) ^ (Cstar * η) *
        Real.exp (Cstar * Cη ^ 2 * (-tη) ^ (1 - 2 * η) / (1 - 2 * η)) *
        Real.exp (Cstar * (-tη)) :=
    fun _ ht => closure_exponential_bound htη hC h2η_lt_one hCη ht
  -- assemble the final bound
  set C' : ℝ := φ tη * (-tη) ^ (Cstar * η) * Real.exp (Cstar * Cη ^ 2 * (-tη) ^ (1 - 2 * η) / (1
    - 2 * η)) * Real.exp (Cstar * (-tη)) with hC'_def
  have hC'_nonneg : 0 ≤ C' := by
    rw [hC'_def]
    have h_rpow_nonneg : 0 ≤ (-tη) ^ (Cstar * η) := Real.rpow_nonneg h_neg_tη_pos.le _
    have h_exp1_nonneg : 0 ≤ Real.exp (Cstar * Cη ^ 2 * (-tη) ^ (1 - 2 * η) / (1 - 2 * η)) :=
      (Real.exp_pos _).le
    have h_exp2_nonneg : 0 ≤ Real.exp (Cstar * (-tη)) := (Real.exp_pos _).le
    exact mul_nonneg (mul_nonneg (mul_nonneg hφ0 h_rpow_nonneg) h_exp1_nonneg) h_exp2_nonneg
  refine ⟨C', hC'_nonneg, ?_⟩
  intro t ht
  have h_gronwall_t := h_gronwall t ht
  have h_exp_bound_t := h_exp_bound t ht
  obtain ⟨ht_left, ht_right⟩ := ht
  have h_neg_t_pos : 0 < -t := neg_pos.mpr ht_right
  have h_key : ((-tη) / (-t)) ^ (Cstar * η) = (-tη) ^ (Cstar * η) * (-t) ^ (-(Cstar * η)) := by
    rw [Real.div_rpow h_neg_tη_pos.le h_neg_t_pos.le, Real.rpow_neg h_neg_t_pos.le,
      div_eq_mul_inv]
  calc
    Y t + 1 = φ t := rfl
    _ ≤ φ tη * Real.exp (∫ s in tη..t, k s) := h_gronwall_t
    _ ≤ φ tη * (((-tη) / (-t)) ^ (Cstar * η) * Real.exp (Cstar * Cη ^ 2 * (-tη) ^ (1 - 2 * η) /
      (1 - 2 * η)) * Real.exp (Cstar * (-tη))) :=
      mul_le_mul_of_nonneg_left h_exp_bound_t hφ0
    _ = C' * (-t) ^ (-(Cstar * η)) := by
      rw [hC'_def, h_key]
      ring

end CIV
