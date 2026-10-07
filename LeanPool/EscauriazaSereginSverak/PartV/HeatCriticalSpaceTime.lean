/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalEstimate
public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalMeasurable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Heat Critical Space Time

As the regularization vanishes, the initial regularized entropies converge
to one third of the cubic integral, as used in `lem:pv-heat-critical`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

private theorem heatVec3_norm_bdd {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, vec3EuclideanNorm (b x) ≤ M := by
  obtain ⟨M, hM, htail⟩ := heatConvVec3_norm_decay hb hbc
  refine ⟨3 * M, by positivity, ?_⟩
  intro x
  have hcomponent (i : Fin 3) : |b x i| ≤ M := by
    have hlim := heatConv_tendsto_self_nhdsWithin_zero_smooth
      (hb i) (hbc i) x
    have hlimabs := hlim.abs
    have hbound : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
        |heatConv t (fun y => b y i) x| ≤ M := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : 0 < t := ht
      have hvector := htail htpos x
      have hcoord := abs_apply_le_vec3EuclideanNorm (heatConvVec3 t b x) i
      have hden : 1 ≤ (1 + vec3EuclideanNorm x) ^ 3 := by
        have hone : 1 ≤ 1 + vec3EuclideanNorm x := by
          linarith only [vec3EuclideanNorm_nonneg x]
        exact one_le_pow₀ hone
      have htail' : M / (1 + vec3EuclideanNorm x) ^ 3 ≤ M := by
        apply (div_le_iff₀ (by positivity)).2
        calc
          M = M * 1 := by ring
          _ ≤ M * (1 + vec3EuclideanNorm x) ^ 3 :=
            mul_le_mul_of_nonneg_left hden hM
      calc
        |heatConv t (fun y => b y i) x| ≤
            vec3EuclideanNorm (heatConvVec3 t b x) := by
          simpa [heatConvVec3] using hcoord
        _ ≤ M / (1 + vec3EuclideanNorm x) ^ 3 := hvector
        _ ≤ M := htail'
    exact le_of_tendsto hlimabs hbound
  calc
    vec3EuclideanNorm (b x) ≤ ∑ i : Fin 3, |b x i| :=
      vec3EuclideanNorm_le_sum_abs (b x)
    _ ≤ ∑ _i : Fin 3, M := Finset.sum_le_sum fun i _ => hcomponent i
    _ = 3 * M := by norm_num

private theorem heatRegEnergy_tendsto_zero (v : Vec3) :
    Tendsto (fun η : ℝ => heatRegEnergy η v) (nhds 0)
      (nhds ((1 / 3 : ℝ) * vec3EuclideanNorm v ^ 3)) := by
  have hq : ContinuousAt (fun η : ℝ => heatRegSq η v) 0 := by
    unfold heatRegSq
    fun_prop
  have hpow : ContinuousAt
      (fun η : ℝ => heatRegSq η v ^ (3 / 2 : ℝ)) 0 :=
    (Real.continuous_rpow_const (q := (3 / 2 : ℝ))
      (by norm_num)).continuousAt.comp hq
  have hcont : ContinuousAt (fun η : ℝ =>
      (1 / 3 : ℝ) * heatRegSq η v ^ (3 / 2 : ℝ) -
        (η / 2) * heatRegSq η v + η ^ 3 / 6) 0 := by
    fun_prop
  have hnorm : (∑ i : Fin 3, v i ^ 2) = vec3EuclideanNorm v ^ 2 := by
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))]
  have hpowNorm : (∑ i : Fin 3, v i ^ 2) ^ (3 / 2 : ℝ) =
      vec3EuclideanNorm v ^ 3 := by
    rw [hnorm]
    have hvnorm : 0 ≤ vec3EuclideanNorm v := vec3EuclideanNorm_nonneg v
    rw [show (3 : ℝ) = (3 / 2 : ℝ) * 2 by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul hvnorm]
    norm_num [Real.rpow_natCast]
  change Tendsto (fun η : ℝ =>
    (1 / 3 : ℝ) * heatRegSq η v ^ (3 / 2 : ℝ) -
      (η / 2) * heatRegSq η v + η ^ 3 / 6) (nhds 0) _
  have hlimit := hcont.tendsto
  rw [show heatRegSq 0 v = ∑ i : Fin 3, v i ^ 2 by
    simp [heatRegSq]] at hlimit
  rw [hpowNorm] at hlimit
  simpa using hlimit

/-- As the regularization vanishes, the initial regularized entropies converge
to one third of the cubic integral, as used in `lem:pv-heat-critical`. -/
theorem heatRegEnergy_initial_tendsto_l3 {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    Tendsto (fun n : ℕ => ∫ x : Vec3,
      heatRegEnergy (1 / (n + 1 : ℝ)) (b x)) atTop
      (nhds ((1 / 3 : ℝ) * ∫ x : Vec3, vec3EuclideanNorm (b x) ^ 3)) := by
  let η : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hη : Tendsto η atTop (nhds 0) := by
    simpa only [η] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨M, hM, hbound⟩ := heatVec3_norm_bdd hb hbc
  let q : Vec3 → ℝ := fun x => ∑ i : Fin 3, (b x i) ^ 2
  have hqterm (i : Fin 3) : Integrable (fun x : Vec3 => (b x i) ^ 2) volume := by
    exact ((hb i).continuous.pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two] using (hbc i).mul_right)
  have hq : Integrable q volume := by
    dsimp [q]
    exact integrable_finsetSum Finset.univ (fun i _ => hqterm i)
  let C : ℝ := (3 + 2 * M) / 6
  have hmajor : Integrable (fun x : Vec3 => C * q x) volume := by
    simpa only [smul_eq_mul, mul_comm] using hq.const_mul C
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun x : Vec3 => heatRegEnergy (η n) (b x)) volume := by
    have hbvec : ContDiff ℝ (⊤ : ℕ∞) b := by
      rw [contDiff_pi]
      exact hb
    have hcont := ((heatRegEnergy_contDiff
      (by positivity : 0 < η n)).comp hbvec).continuous
    exact hcont.aestronglyMeasurable
  have hboundn (n : ℕ) : ∀ᵐ x : Vec3 ∂volume,
      ‖heatRegEnergy (η n) (b x)‖ ≤ C * q x := by
    filter_upwards [] with x
    have hηpos : 0 < η n := by dsimp [η]; positivity
    have hηle : η n ≤ 1 := by
      dsimp [η]
      rw [div_le_one (by positivity : (0 : ℝ) < n + 1)]
      exact_mod_cast
        (show 1 ≤ n + 1 from Nat.succ_le_succ (Nat.zero_le n))
    have henergy := heatRegEnergy_le_mul_sum_sq hηpos hM (b x) (hbound x)
    have hcoeff : (3 * η n + 2 * M) / 6 ≤ C := by
      dsimp [C]
      apply div_le_div_of_nonneg_right ?_ (by norm_num : (0 : ℝ) ≤ 6)
      have hηterm : 3 * η n ≤ 3 := by
        calc
          3 * η n ≤ 3 * 1 :=
            mul_le_mul_of_nonneg_left hηle (by norm_num : (0 : ℝ) ≤ 3)
          _ = 3 := by ring
      exact add_le_add hηterm le_rfl
    have hpoint : heatRegEnergy (η n) (b x) ≤ C * q x := by
      calc
        heatRegEnergy (η n) (b x) ≤ ((3 * η n + 2 * M) / 6) * q x := by
          simpa [q] using henergy
        _ ≤ C * q x := mul_le_mul_of_nonneg_right hcoeff
          (Finset.sum_nonneg fun i _ => sq_nonneg (b x i))
    rw [Real.norm_eq_abs, abs_of_nonneg (heatRegEnergy_nonneg hηpos (b x))]
    exact hpoint
  have hpointLimit (x : Vec3) :
      Tendsto (fun n : ℕ => heatRegEnergy (η n) (b x)) atTop
        (nhds ((1 / 3 : ℝ) * vec3EuclideanNorm (b x) ^ 3)) := by
    simpa [Function.comp_def, η] using (heatRegEnergy_tendsto_zero (b x)).comp hη
  have hlimit : Tendsto
      (fun n : ℕ => ∫ x : Vec3, heatRegEnergy (η n) (b x)) atTop
      (nhds (∫ x : Vec3, (1 / 3 : ℝ) * vec3EuclideanNorm (b x) ^ 3)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => C * q x)
    · exact hmeas
    · exact hmajor
    · exact hboundn
    · exact Filter.Eventually.of_forall hpointLimit
  simpa [η, integral_const_mul] using hlimit

end ESS

end
