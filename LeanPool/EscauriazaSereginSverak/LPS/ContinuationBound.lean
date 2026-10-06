/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationEnergy
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSource

/-!
# A uniform `H¹` bound along strong continuations

A strong solution that agrees on `(t₀, t₁)`, `t₁ ≤ T`, with a Leray–Hopf solution
of finite Serrin norm has `H¹` norm at time `t₁` bounded independently of `t₁` by
the `H¹` estimate (`lem:lps-H1-estimate`, `lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The `H¹` norm at time `t₁` is at most the sum of the `L²` norm and the gradient
norm, each controlled by its value at the initial time. -/
theorem lps_h1_norm_le_of_parts {t₀ t₁ : ℝ} {U : ParabolicPoint → Vec3}
    {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {e f : ℝ}
    (hU : IsLpsStrongSolution t₀ t₁ U DU p)
    (hL2 : (∫ x : Vec3, ∑ i : Fin 3, (U (x, t₁) i) ^ 2) ≤ e)
    (hH1 : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2) ≤ f) :
    (∫ x : Vec3, (∑ i : Fin 3, (U (x, t₁) i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2) ≤ e + f := by
  have ht : t₁ ∈ Icc t₀ t₁ := ⟨hU.1.le, le_rfl⟩
  obtain ⟨hm, hDm⟩ := lps_strong_solution_slice_memLp_two hU ht
  have h1 : Integrable (fun x : Vec3 => ∑ i : Fin 3, (U (x, t₁) i) ^ 2) volume :=
    integrable_finsetSum _ fun i _ => (memLp_pi_iff.1 hm i).integrable_sq
  have h2 : Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2) volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (memLp_pi_iff.1 (memLp_pi_iff.1 hDm i) j).integrable_sq
  rw [integral_add h1 h2]
  exact add_le_add hL2 hH1

/-- The `L²` norm of a strong solution does not increase (`prop:lps-local-strong`). -/
theorem lps_strong_l2_le_initial {t₀ t₁ : ℝ} {U : ParabolicPoint → Vec3}
    {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ t₁ U DU p) :
    (∫ x : Vec3, ∑ i : Fin 3, (U (x, t₁) i) ^ 2) ≤
      ∫ x : Vec3, ∑ i : Fin 3, (U (x, t₀) i) ^ 2 := by
  obtain ⟨-, -, -, -, -, -, hkin⟩ := ESS.LPS.lps_unregularised_h1_energy_identity hU
  have h := hkin t₀ t₁ ⟨le_rfl, hU.1.le⟩ ⟨hU.1.le, le_rfl⟩ hU.1.le
  have hnn : 0 ≤ ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁),
      ∑ i : Fin 3, ∑ j : Fin 3, (DU z i j) ^ 2 :=
    setIntegral_nonneg (MeasurableSet.univ.prod measurableSet_Ioo) fun z _ =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith only [h, hnn]

/-- Transfer of the finite mixed Serrin norm from a Leray–Hopf solution to a strong
solution agreeing with it on the time interval. -/
theorem lps_mixed_finite_transfer {T t₀ t₁ s : ℝ} {u U : ParabolicPoint → Vec3}
    (ht₀ : 0 ≤ t₀) (ht₁ : t₁ ≤ T)
    (hae : U =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] u)
    (hmix : (∫⁻ t in Ioo (0 : ℝ) T,
      (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
        ((2 * s / (s - 3)) / s)) < ⊤) :
    (∫⁻ t in Ioo t₀ t₁,
      (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (U (x, t))) ^ s) ^
        ((2 * s / (s - 3)) / s)) < ⊤ := by
  have hsub : Ioo t₀ t₁ ⊆ Ioo 0 T := fun t ht => ⟨lt_of_le_of_lt ht₀ ht.1, lt_of_lt_of_le ht.2 ht₁⟩
  have hsl := lps_slices_ae_eq_of_slab hae
  have : (∫⁻ t in Ioo t₀ t₁,
      (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (U (x, t))) ^ s) ^
        ((2 * s / (s - 3)) / s)) =
      ∫⁻ t in Ioo t₀ t₁,
      (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
        ((2 * s / (s - 3)) / s) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hsl] with t ht
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ht] with x hx
    rw [hx]
  rw [this]
  exact lt_of_le_of_lt (lintegral_mono_set hsub) hmix

/-- Transfer of the endpoint Serrin norm from a Leray–Hopf solution to a strong
solution agreeing with it on the time interval. -/
theorem lps_mixed_endpoint_transfer {T t₀ t₁ : ℝ} {u U : ParabolicPoint → Vec3}
    (ht₀ : 0 ≤ t₀) (ht₁ : t₁ ≤ T)
    (hae : U =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] u)
    (hmix : (∫⁻ t in Ioo (0 : ℝ) T,
      (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
        (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) :
    (∫⁻ t in Ioo t₀ t₁,
      (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (U (x, t))))
        (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤ := by
  have hsub : Ioo t₀ t₁ ⊆ Ioo 0 T := fun t ht => ⟨lt_of_le_of_lt ht₀ ht.1, lt_of_lt_of_le ht.2 ht₁⟩
  have hsl := lps_slices_ae_eq_of_slab hae
  have : (∫⁻ t in Ioo t₀ t₁,
      (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (U (x, t))))
        (volume : Measure Vec3)) ^ (2 : ℝ)) =
      ∫⁻ t in Ioo t₀ t₁,
      (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
        (volume : Measure Vec3)) ^ (2 : ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hsl] with t ht
    congr 1
    refine essSup_congr_ae ?_
    filter_upwards [ht] with x hx
    rw [hx]
  rw [this]
  exact lt_of_le_of_lt (lintegral_mono_set hsub) hmix

/-- A bound on the `H¹` norm of every strong solution that agrees with a Leray–Hopf
solution of finite Serrin norm on an initial time interval (`lem:lps-H1-estimate`,
`lem:lps-continuation`). -/
theorem lps_continuation_bound {T t₀ : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} (hLH : IsLerayHopfSolution T a u Du)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
            ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤)
    (ht₀ : 0 ≤ t₀) :
    ∃ S : ℝ, ∀ {t₁ : ℝ} {U : ParabolicPoint → Vec3} {DU : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ},
      IsLpsStrongSolution t₀ t₁ U DU p → t₁ ≤ T →
      (fun x : Vec3 => U (x, t₀)) =ᵐ[volume] (fun x : Vec3 => u (x, t₀)) →
      (fun x : Vec3 => DU (x, t₀)) =ᵐ[volume] (fun x : Vec3 => Du (x, t₀)) →
      U =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] u →
      (∫ x : Vec3, (∑ i : Fin 3, (U (x, t₁) i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2) ≤ S := by
  have hsubT : Ioo t₀ T ⊆ Ioo 0 T := fun t ht => ⟨lt_of_le_of_lt ht₀ ht.1, ht.2⟩
  have hQsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := fun z hz => ⟨hz.1, hsubT hz.2⟩
  have hu_meas : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) :=
    (lps_lh_memLp_slab hLH).1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hQsub le_rfl)
  set e₀ : ℝ := ∫ x : Vec3, ∑ i : Fin 3, (u (x, t₀) i) ^ 2 with he₀
  set f₀ : ℝ := ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2 with hf₀
  have hf₀nn : 0 ≤ f₀ := integral_nonneg fun x =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- the two initial-slice identifications
  have hL2 : ∀ {t₁ : ℝ} {U : ParabolicPoint → Vec3} {DU : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ}, IsLpsStrongSolution t₀ t₁ U DU p →
      (fun x : Vec3 => U (x, t₀)) =ᵐ[volume] (fun x : Vec3 => u (x, t₀)) →
      (∫ x : Vec3, ∑ i : Fin 3, (U (x, t₁) i) ^ 2) ≤ e₀ := by
    intro t₁ U DU p hU hU0
    refine (lps_strong_l2_le_initial hU).trans (le_of_eq ?_)
    refine integral_congr_ae ?_
    filter_upwards [hU0] with x hx
    simp only [hx]
  have hgrad0 : ∀ {DU : ParabolicPoint → Fin 3 → Vec3},
      (fun x : Vec3 => DU (x, t₀)) =ᵐ[volume] (fun x : Vec3 => Du (x, t₀)) →
      (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₀) i j) ^ 2) = f₀ := by
    intro DU hDU0
    refine integral_congr_ae ?_
    filter_upwards [hDU0] with x hx
    simp only [hx]
  rcases hSerrin with ⟨s, hs, hmix⟩ | hmix
  · obtain ⟨C, hC, hEst⟩ := lps_h1_estimate hs
    have hmixT : (∫⁻ t in Ioo t₀ T,
        (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono_set hsubT) hmix
    have hIu := lps_h1_finite_time_moment_integrable_closed hu_meas hs hmixT
    set m : ℝ → ℝ := fun t => (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal s) volume).toReal ^ (2 * s / (s - 3)) with hm
    set I₀ : ℝ := ∫ τ in t₀..T, m τ with hI₀
    refine ⟨e₀ + f₀ * Real.exp (C * I₀), ?_⟩
    intro t₁ U DU p hU ht₁ hU0 hDU0 hae
    have hle : t₀ ≤ t₁ := hU.1.le
    have hmixU := lps_mixed_finite_transfer ht₀ ht₁ hae hmix
    obtain ⟨D2, Dt, -, -, -, hb⟩ := hEst hU hmixU
    have hb1 := hb t₁ ⟨hle, le_rfl⟩
    have hd0 : 0 ≤ ∫ τ in t₀..t₁, ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2 (x, τ) i j j) ^ 2 :=
      intervalIntegral.integral_nonneg hle fun τ _ => integral_nonneg fun x =>
        Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsl := lps_slices_ae_eq_of_slab hae
    have hcongr : (∫ τ in t₀..t₁, (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (U (x, τ)))
        (ENNReal.ofReal s) volume).toReal ^ (2 * s / (s - 3))) = ∫ τ in t₀..t₁, m τ := by
      rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      refine integral_congr_ae ?_
      filter_upwards [hsl] with τ hτ
      simp only [hm]
      congr 2
      refine eLpNorm_congr_ae ?_
      filter_upwards [hτ] with x hx
      rw [hx]
    have hmono : (∫ τ in t₀..t₁, m τ) ≤ I₀ :=
      intervalIntegral.integral_mono_interval le_rfl hle ht₁
        (Eventually.of_forall fun τ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
        ((intervalIntegrable_iff_integrableOn_Icc_of_le (hle.trans ht₁)).2 hIu)
    have hexp : Real.exp (C * ∫ τ in t₀..t₁, (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (U (x, τ)))
        (ENNReal.ofReal s) volume).toReal ^ (2 * s / (s - 3))) ≤ Real.exp (C * I₀) := by
      rw [hcongr]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmono hC)
    rw [hgrad0 hDU0] at hb1
    have hH1 : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2) ≤
        f₀ * Real.exp (C * I₀) := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hexp hf₀nn)
      linarith only [hb1, hd0]
    exact lps_h1_norm_le_of_parts hU (hL2 hU hU0) hH1
  · obtain ⟨C, hC, hEst⟩ := lps_h1_estimate_endpoint
    have hmixT : (∫⁻ t in Ioo t₀ T,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono_set hsubT) hmix
    obtain ⟨-, -, -, hIu⟩ := lps_endpoint_norm_slice_facts hu_meas hmixT
    set m : ℝ → ℝ := fun t => (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) ⊤
      volume).toReal ^ 2 with hm
    set I₀ : ℝ := ∫ τ in t₀..T, m τ with hI₀
    refine ⟨e₀ + f₀ * Real.exp (C * I₀), ?_⟩
    intro t₁ U DU p hU ht₁ hU0 hDU0 hae
    have hle : t₀ ≤ t₁ := hU.1.le
    have hmixU := lps_mixed_endpoint_transfer ht₀ ht₁ hae hmix
    obtain ⟨D2, Dt, -, -, -, hb⟩ := hEst hU hmixU
    have hb1 := hb t₁ ⟨hle, le_rfl⟩
    have hd0 : 0 ≤ ∫ τ in t₀..t₁, ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2 (x, τ) i j j) ^ 2 :=
      intervalIntegral.integral_nonneg hle fun τ _ => integral_nonneg fun x =>
        Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsl := lps_slices_ae_eq_of_slab hae
    have hcongr : (∫ τ in t₀..t₁, (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (U (x, τ))) ⊤
        volume).toReal ^ 2) = ∫ τ in t₀..t₁, m τ := by
      rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      refine integral_congr_ae ?_
      filter_upwards [hsl] with τ hτ
      simp only [hm]
      congr 2
      refine eLpNorm_congr_ae ?_
      filter_upwards [hτ] with x hx
      rw [hx]
    have hmono : (∫ τ in t₀..t₁, m τ) ≤ I₀ :=
      intervalIntegral.integral_mono_interval le_rfl hle ht₁
        (Eventually.of_forall fun τ => sq_nonneg _)
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le (hle.trans ht₁)).2 hIu)
    have hexp : Real.exp (C * ∫ τ in t₀..t₁, (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (U (x, τ))) ⊤
        volume).toReal ^ 2) ≤ Real.exp (C * I₀) := by
      rw [hcongr]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmono hC)
    rw [hgrad0 hDU0] at hb1
    have hH1 : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2) ≤
        f₀ * Real.exp (C * I₀) := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hexp hf₀nn)
      linarith only [hb1, hd0]
    exact lps_h1_norm_le_of_parts hU (hL2 hU hU0) hH1

end ESS

end
