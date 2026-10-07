/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Convection
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureSlice
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Finite Serrin control of a strong solution

A strong solution has uniformly bounded gradient `L²` norms on its closed time
interval, so the whole-space Sobolev inequality bounds the `L⁶` norm of the
velocity uniformly in time. This is the finite Serrin condition with `s = 6`,
`ℓ = 4` used to compare two strong solutions (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_abs_toReal_eLpNorm_sub_le {α E : Type*} [NormedAddCommGroup E]
    {m : MeasurableSpace α} {μ : Measure α} {f g : α → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |(eLpNorm f 2 μ).toReal - (eLpNorm g 2 μ).toReal| ≤ (eLpNorm (f - g) 2 μ).toReal := by
  have h := abs_norm_sub_norm_le (hf.toLp f) (hg.toLp g)
  rw [← MemLp.toLp_sub, Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp] at h
  exact h

/-- Each time slice of a strong solution has square-integrable velocity and
gradient, with the componentwise `H¹` representation. -/
theorem lps_strong_solution_slice_h1 {t₀ T t : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) (ht : t ∈ Icc t₀ T) :
    MemLp (fun x : Vec3 => u (x,t)) 2 volume ∧
    MemLp (fun x : Vec3 => Du (x,t)) 2 volume ∧
    ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x : Vec3 => u (x,t) i) ∧
      h.grad = (fun x j => Du (x,t) i j) := by
  have hh := (hU.2.1 t ht).2
  choose h h1 h2 using hh
  refine ⟨?_, ?_, fun i => ⟨h i, h1 i, h2 i⟩⟩
  · refine memLp_pi_iff.mpr fun i => ?_
    have := (h i).memL2
    rw [h1 i] at this
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using this
  · refine memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun j => ?_
    have := (h i).gradMemL2 j
    rw [h2 i] at this
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using this

/-- The gradient `L²` norms of a strong solution are bounded on its closed
time interval. -/
theorem lps_strong_solution_gradient_bound {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) :
    ∃ M : ℝ, ∀ t ∈ Icc t₀ T, (eLpNorm (fun x : Vec3 => Du (x,t)) 2 volume).toReal ≤ M := by
  let g : ℝ → ℝ := fun t => (eLpNorm (fun x : Vec3 => Du (x,t)) 2 volume).toReal
  have hcont : ContinuousOn g (Icc t₀ T) := by
    intro t ht
    have hclause := (hU.2.2.1 t ht).2
    have hlim : Tendsto (fun s : ℝ => (eLpNorm (fun x : Vec3 => Du (x,s) - Du (x,t)) 2
        volume).toReal) (nhdsWithin t (Icc t₀ T)) (nhds 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hclause
      simpa [Function.comp_def] using this
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with s hs
    have h := lps_abs_toReal_eLpNorm_sub_le (lps_strong_solution_slice_h1 hU hs).2.1
      (lps_strong_solution_slice_h1 hU ht).2.1
    have h' : |g s - g t| ≤ (eLpNorm (fun x : Vec3 => Du (x,s) - Du (x,t)) 2 volume).toReal := h
    simpa [Real.norm_eq_abs] using h'
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨M, fun t ht => (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hM t ht)⟩

/-- The `L⁶` norms of the velocity of a strong solution are bounded on its
closed time interval. -/
theorem lps_strong_solution_l6_bound {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ t ∈ Icc t₀ T,
      ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (6 : ℝ) ≤ C := by
  obtain ⟨M, hM⟩ := lps_strong_solution_gradient_bound hU
  let Cs : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt 3) *
    (6 * gagliardoNirenbergSobolevConstant * ENNReal.ofReal M)
  have hCs : Cs ≠ ⊤ := by
    have h1 := CKN.Leray.gagliardoNirenbergSobolevConstant_ne_top
    dsimp only [Cs]
    finiteness
  refine ⟨Cs ^ (6 : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCs, fun t ht => ?_⟩
  obtain ⟨hw2, hDw2, hH1⟩ := lps_strong_solution_slice_h1 hU ht
  have h6 := ESS.LPS.lps_regularised_h1_vector_six_bound hw2 hDw2 hH1
  have hgrad : eLpNorm (fun x : Vec3 => Du (x,t)) 2 volume ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_toReal hDw2.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (hM t ht)
  have hmeas : AEStronglyMeasurable (fun x : Vec3 => vec3EuclideanNorm (u (x,t))) volume :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hw2.aestronglyMeasurable
  have hEuc : eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,t))) 6 volume ≤ Cs := by
    calc eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,t))) 6 volume
        ≤ eLpNorm (fun x : Vec3 => Real.sqrt 3 * ‖u (x,t)‖) 6 volume := by
          refine eLpNorm_mono_ae_real hmeas (Eventually.of_forall fun x => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
          exact vec3EuclideanNorm_le_sqrt_three_mul_norm _
      _ = ENNReal.ofReal (Real.sqrt 3) * eLpNorm (fun x : Vec3 => u (x,t)) 6 volume := by
          have := eLpNorm_const_smul (p := (6 : ℝ≥0∞)) (μ := volume) (Real.sqrt 3)
            (fun x : Vec3 => ‖u (x,t)‖)
          simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg 3)] at this
          rw [eLpNorm_norm _ hw2.aestronglyMeasurable] at this
          exact this
      _ ≤ ENNReal.ofReal (Real.sqrt 3) * (6 * gagliardoNirenbergSobolevConstant *
          eLpNorm (fun x : Vec3 => Du (x,t)) 2 volume) := by gcongr
      _ ≤ Cs := by dsimp only [Cs]; gcongr
  have hform := eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (6 : ℝ≥0∞)) (μ := volume)
    (by norm_num) (by norm_num) hmeas
  rw [show (6 : ℝ≥0∞).toReal = 6 by norm_num] at hform
  have hint : (∫⁻ x : Vec3, ‖vec3EuclideanNorm (u (x,t))‖ₑ ^ (6 : ℝ)) =
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,t))) 6 volume ^ (6 : ℝ) := by
    rw [hform, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (6 : ℝ))
      = ∫⁻ x : Vec3, ‖vec3EuclideanNorm (u (x,t))‖ₑ ^ (6 : ℝ) := by
        refine lintegral_congr fun x => ?_
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    _ = _ := hint
    _ ≤ Cs ^ (6 : ℝ) := ENNReal.rpow_le_rpow hEuc (by norm_num)

/-- A strong solution satisfies the finite Serrin condition with `s = 6` on
every time interval inside its lifespan (`prop:lps-local-strong` and
`thm:lps`). -/
theorem lps_strong_solution_serrin_finite {t₀ T σ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) (hσT : σ ≤ T - t₀) :
    ∃ s : ℝ, 3 < s ∧
      (∫⁻ t in Ioo (0 : ℝ) σ,
        (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀ + t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤ := by
  obtain ⟨C, hC, hbound⟩ := lps_strong_solution_l6_bound hU
  refine ⟨6, by norm_num, ?_⟩
  have hexp : (0 : ℝ) ≤ (2 * 6 / (6 - 3)) / 6 := by norm_num
  calc (∫⁻ t in Ioo (0 : ℝ) σ,
        (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀ + t))) ^ (6 : ℝ)) ^
          ((2 * 6 / (6 - 3)) / 6 : ℝ))
      ≤ ∫⁻ t in Ioo (0 : ℝ) σ, C ^ ((2 * 6 / (6 - 3)) / 6 : ℝ) := by
        refine lintegral_mono_ae ?_
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Eventually.of_forall fun t ht => ?_
        refine ENNReal.rpow_le_rpow (hbound (t₀ + t) ⟨by linarith only [ht.1], ?_⟩) hexp
        linarith only [ht.2, hσT]
    _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hexp hC) measure_Ioo_lt_top

end ESS

end
