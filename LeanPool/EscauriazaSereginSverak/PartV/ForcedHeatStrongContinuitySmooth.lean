/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatSmooth
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatNorms
public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbitStrongContinuity

/-!
# Strong continuity for smooth forced responses

Smooth compactly supported tensors produce forced heat responses whose spatial
slices belong to `L²` and `L³` at every time. Their time dependence is strong in
both spaces, by dominated convergence and the uniform spatial decay estimate.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A smooth forced response has an `L^r` spatial slice for every `r ≥ 2`. -/
theorem forcedHeat_smooth_slice_memLp {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p))
    {r : ℝ} (hr : 2 ≤ r) (t : ℝ) :
    MemLp (fun x : Vec3 => forcedHeat G (x, t)) (ENNReal.ofReal r) volume := by
  have hr0 : 0 < r := by linarith only [hr]
  obtain ⟨M, hM, hdec⟩ := vecTimeDiv_response_decay
    (g := fun i j (p : Vec3 × ℝ) => G i j p) hG hGc
  have hcomponent (i : Fin 3) :
      MemLp (fun x : Vec3 => forcedHeat G (x, t) i) (ENNReal.ofReal r) volume := by
    have hcont : Continuous (fun x : Vec3 => forcedHeat G (x, t) i) :=
      ((forcedHeat_contDiff hG hGc i).continuous.comp
        (continuous_id.prodMk continuous_const))
    have hbound (x : Vec3) :
        |forcedHeat G (x, t) i| ≤ M / (1 + vec3EuclideanNorm x) ^ 3 := by
      rw [forcedHeat_eq_causalHeatConv_vecTimeDiv hG hGc i (x, t)]
      exact (hdec i i i (x, t)).1
    have hint : Integrable (fun x : Vec3 =>
        (‖forcedHeat G (x, t) i‖) ^ r) volume := by
      refine (heatStrong_decay_rpow_integrable hM hr).mono' ?_ ?_
      · exact (hcont.norm.rpow_const fun _ => Or.inr hr0.le).aestronglyMeasurable
      · filter_upwards [] with x
        rw [Real.norm_eq_abs, abs_of_nonneg
          (Real.rpow_nonneg (norm_nonneg _) _)]
        exact Real.rpow_le_rpow (norm_nonneg _) (by
          rw [Real.norm_eq_abs]
          exact hbound x) hr0.le
    have hp0 : ENNReal.ofReal r ≠ 0 := by positivity
    have hint' : Integrable (fun x : Vec3 =>
        (‖forcedHeat G (x, t) i‖) ^ (ENNReal.ofReal r).toReal) volume := by
      simpa only [ENNReal.toReal_ofReal hr0.le] using hint
    exact (integrable_norm_rpow_iff hcont.aestronglyMeasurable hp0
      ENNReal.ofReal_ne_top).1 hint'
  exact memLp_pi_iff.2 hcomponent

/-- A smooth forced response is continuous in each scalar spatial `L^r` norm. -/
private theorem forcedHeat_smooth_component_tendsto {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p))
    {r : ℝ} (hr : 2 ≤ r) (t₀ : ℝ) (i : Fin 3) :
    Tendsto (fun t : ℝ => eLpNorm (fun x : Vec3 =>
      forcedHeat G (x, t) i - forcedHeat G (x, t₀) i) (ENNReal.ofReal r) volume)
      (𝓝 t₀) (𝓝 0) := by
  have hr0 : 0 < r := by linarith only [hr]
  obtain ⟨M, hM, hdec⟩ := vecTimeDiv_response_decay
    (g := fun i j (p : Vec3 × ℝ) => G i j p) hG hGc
  have hM2 : 0 ≤ 2 * M := by positivity
  refine heatStrong_eLpNorm_tendsto_zero hr0 ?_ ?_
    (heatStrong_decay_rpow_integrable hM2 hr) fun x => ?_
  · filter_upwards [] with t
    have hct : Continuous (fun x : Vec3 => forcedHeat G (x, t) i) :=
      (forcedHeat_contDiff hG hGc i).continuous.comp
        (continuous_id.prodMk continuous_const)
    have hct₀ : Continuous (fun x : Vec3 => forcedHeat G (x, t₀) i) :=
      (forcedHeat_contDiff hG hGc i).continuous.comp
        (continuous_id.prodMk continuous_const)
    exact (hct.sub hct₀).aestronglyMeasurable
  · filter_upwards [] with t x
    have h1 : |forcedHeat G (x, t) i| ≤ M / (1 + vec3EuclideanNorm x) ^ 3 := by
      rw [forcedHeat_eq_causalHeatConv_vecTimeDiv hG hGc i (x, t)]
      exact (hdec i i i (x, t)).1
    have h2 : |forcedHeat G (x, t₀) i| ≤ M / (1 + vec3EuclideanNorm x) ^ 3 := by
      rw [forcedHeat_eq_causalHeatConv_vecTimeDiv hG hGc i (x, t₀)]
      exact (hdec i i i (x, t₀)).1
    calc
      |forcedHeat G (x, t) i - forcedHeat G (x, t₀) i| ≤
          |forcedHeat G (x, t) i| + |forcedHeat G (x, t₀) i| := abs_sub _ _
      _ ≤ M / (1 + vec3EuclideanNorm x) ^ 3 +
          M / (1 + vec3EuclideanNorm x) ^ 3 := add_le_add h1 h2
      _ = 2 * M / (1 + vec3EuclideanNorm x) ^ 3 := by ring
  · have hc : ContinuousAt (fun t : ℝ => forcedHeat G (x, t) i) t₀ :=
      (forcedHeat_contDiff hG hGc i).continuous.continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)
    simpa only [sub_self] using hc.tendsto.sub_const (forcedHeat G (x, t₀) i)

/-- A smooth forced response is continuous as a vector-valued spatial `L^r` path. -/
private theorem forcedHeat_smooth_slice_tendsto {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p))
    {r : ℝ} (hr : 2 ≤ r) (t₀ : ℝ) :
    Tendsto (fun t : ℝ => eLpNorm (fun x : Vec3 =>
      forcedHeat G (x, t) - forcedHeat G (x, t₀)) (ENNReal.ofReal r) volume)
      (𝓝 t₀) (𝓝 0) := by
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r :=
    ENNReal.one_le_ofReal.2 (by linarith only [hr])
  have hsum : Tendsto (fun t : ℝ => ∑ i : Fin 3, eLpNorm (fun x : Vec3 =>
      forcedHeat G (x, t) i - forcedHeat G (x, t₀) i) (ENNReal.ofReal r) volume)
      (𝓝 t₀) (𝓝 0) := by
    simpa using tendsto_finsetSum (s := Finset.univ) fun i _ =>
      forcedHeat_smooth_component_tendsto hG hGc hr t₀ i
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [] with t
  exact heatStrong_vec_eLpNorm_le hr1
    ((forcedHeat_smooth_slice_memLp hG hGc hr t).sub
      (forcedHeat_smooth_slice_memLp hG hGc hr t₀)).aestronglyMeasurable

/-- The spatial `L^r` class of a smooth forced response varies continuously in time. -/
theorem forcedHeat_smooth_lp_path_continuous {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p))
    {r : ℝ} (hr : 2 ≤ r) [Fact (1 ≤ ENNReal.ofReal r)] :
    Continuous (fun t : ℝ =>
      (forcedHeat_smooth_slice_memLp hG hGc hr t).toLp
        (fun x : Vec3 => forcedHeat G (x, t))) := by
  apply continuous_iff_continuousAt.2
  intro t₀
  change Tendsto (fun t : ℝ =>
    (forcedHeat_smooth_slice_memLp hG hGc hr t).toLp
      (fun x : Vec3 => forcedHeat G (x, t))) (𝓝 t₀)
    (𝓝 ((forcedHeat_smooth_slice_memLp hG hGc hr t₀).toLp
      (fun x : Vec3 => forcedHeat G (x, t₀))))
  have hiff := Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fi := 𝓝 t₀)
    (f := fun t : ℝ => fun x : Vec3 => forcedHeat G (x, t))
    (f_ℒp := fun t => forcedHeat_smooth_slice_memLp hG hGc hr t)
    (f_lim := fun x : Vec3 => forcedHeat G (x, t₀))
    (f_lim_ℒp := forcedHeat_smooth_slice_memLp hG hGc hr t₀)
  exact hiff.mpr (forcedHeat_smooth_slice_tendsto hG hGc hr t₀)

end ESS

end
