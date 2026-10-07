/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbitSolutionDuality

/-!
# Weak continuity and initial trace of the heat orbit

The Gaussian kernel is even, so the pairing of the heat orbit of an `L²` datum
with an integrable test field equals the pairing of the datum with the heat
orbit of the test field.  For a smooth compactly supported test field the
latter heat orbit is continuous in time, converges to the test field as time
decreases to zero, and has a cubic spatial tail uniformly in time, so dominated
convergence gives the weak continuity and the initial trace of the heat orbit
required in `prop:pv-local-solution`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

/-- The Gaussian convolution is symmetric: pairing the heat orbit of an `L²`
datum with an integrable function equals pairing the datum with the heat
orbit of that function. -/
theorem integral_heatConv_mul_eq {f g : Vec3 → ℝ} (hf : MemLp f 2 volume)
    (hg : Integrable g volume) {t : ℝ} (ht : 0 < t) :
    ∫ x : Vec3, heatConv t f x * g x = ∫ y : Vec3, f y * heatConv t g y := by
  obtain ⟨hK, -⟩ := heatKernel_memLp_two ht
  set C : ℝ := (eLpNorm (fun y : Vec3 => heatKernel y t) 2 volume * eLpNorm f 2 volume).toReal
  let F : Vec3 × Vec3 → ℝ := fun p => heatKernel (p.1 - p.2) t * f p.2 * g p.1
  have hFm : AEStronglyMeasurable F ((volume : Measure Vec3).prod volume) := by
    have hKm : Measurable (fun p : Vec3 × Vec3 => heatKernel (p.1 - p.2) t) :=
      heatKernel_vecTime_measurable.comp ((measurable_fst.sub measurable_snd).prodMk
        measurable_const)
    exact (hKm.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).mul
      hg.aestronglyMeasurable.comp_fst
  have hFint : Integrable F ((volume : Measure Vec3).prod volume) := by
    rw [integrable_prod_iff hFm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · have h1 := (integrable_mul_sub_enorm_le hK hf x).1.comp_sub_left x
      simp only [sub_sub_cancel] at h1
      exact h1.mul_const (g x)
    · refine (hg.norm.const_mul C).mono' hFm.norm.integral_prod_right'
        (Eventually.of_forall fun x => ?_)
      have hnn : 0 ≤ ∫ y : Vec3, ‖F (x, y)‖ := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hnn]
      have heq : (fun y : Vec3 => ‖F (x, y)‖) =
          fun y => ‖heatKernel (x - y) t * f y‖ * ‖g x‖ := by
        funext y
        simp only [F, norm_mul]
      rw [heq, integral_mul_const]
      exact mul_le_mul_of_nonneg_right (integral_norm_kernel_le hK hf x) (norm_nonneg _)
  have heven (x y : Vec3) : heatKernel (x - y) t = heatKernel (y - x) t := by
    rw [← neg_sub]
    unfold heatKernel
    simp only [Pi.neg_apply, neg_sq]
  calc
    ∫ x : Vec3, heatConv t f x * g x = ∫ x : Vec3, ∫ y : Vec3, F (x, y) := by
      congr 1
      funext x
      rw [heatConv_eq_integral_sub, ← integral_mul_const]
    _ = ∫ y : Vec3, ∫ x : Vec3, F (x, y) := integral_integral_swap hFint
    _ = ∫ y : Vec3, f y * heatConv t g y := by
      congr 1
      funext y
      rw [heatConv_eq_integral_sub, ← integral_const_mul]
      congr 1
      funext x
      simp only [F, heven x y]
      ring

/-- The pairing of the datum with the heat orbit of a smooth compactly
supported test function is continuous in positive time and converges to the
pairing with the test function as time decreases to zero. -/
theorem integral_mul_heatConv_continuous_tendsto {f g : Vec3 → ℝ} (hf : MemLp f 2 volume)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ContinuousOn (fun t => ∫ y : Vec3, f y * heatConv t g y) (Ioi 0) ∧
      Tendsto (fun t => ∫ y : Vec3, f y * heatConv t g y) (𝓝[>] 0)
        (𝓝 (∫ y : Vec3, f y * g y)) := by
  obtain ⟨C, hC, htail⟩ := heatConv_abs_le_spatial_decay hg hgc
  have hw : MemLp (fun y : Vec3 => C * ((1 + ‖y‖) ^ 3)⁻¹) 2 volume :=
    one_add_norm_inv_cube_memLp_two C
  let bound : Vec3 → ℝ := fun y => ‖f y‖ * (C * ((1 + ‖y‖) ^ 3)⁻¹)
  have hbound : Integrable bound volume := by
    have h := hf.norm.integrable_mul hw
    exact h
  have hdecay {t : ℝ} (ht : 0 < t) (y : Vec3) :
      ‖f y * heatConv t g y‖ ≤ bound y := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.norm_eq_abs]
    refine (htail ht y).trans ?_
    have hn : ‖y‖ ≤ vec3EuclideanNorm y := norm_le_vec3EuclideanNorm y
    have hpos : 0 < 1 + ‖y‖ := by positivity
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hC
    exact inv_anti₀ (pow_pos hpos 3) (pow_le_pow_left₀ hpos.le (by linarith only [hn]) 3)
  have hmeas {t : ℝ} (ht : 0 < t) :
      AEStronglyMeasurable (fun y : Vec3 => f y * heatConv t g y) volume :=
    hf.aestronglyMeasurable.mul (heatConv_smooth_input hg hgc ht).continuous.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · refine continuousOn_of_dominated (bound := bound) (fun t ht => hmeas ht)
      (fun t ht => Eventually.of_forall (hdecay ht)) hbound (Eventually.of_forall fun y => ?_)
    intro t ht
    exact (continuousAt_const.mul
      (heatConv_hasDerivAt_laplacianInput hg hgc ht y).continuousAt).continuousWithinAt
  · refine tendsto_integral_filter_of_dominated_convergence bound
      (eventually_mem_nhdsWithin.mono fun t ht => hmeas ht)
      (eventually_mem_nhdsWithin.mono fun t ht => Eventually.of_forall (hdecay ht)) hbound
      (Eventually.of_forall fun y => ?_)
    exact tendsto_const_nhds.mul (heatConv_tendsto_self_nhdsWithin_zero_smooth hg hgc y)

/-- (h7) The heat orbit of a datum in `J` is weakly continuous on `(0, τ]` and
attains the datum weakly as time decreases to zero. -/
theorem heatOrbit_weak_continuity_initial {a : Vec3 → Vec3} (ha : IsInJ a) (τ : ℝ)
    {ψ : Vec3 → Vec3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ContinuousOn (fun t => ∫ x : Vec3, ∑ i : Fin 3, heatOrbit a (x, t) i * ψ x i) (Ioc 0 τ) ∧
      Tendsto (fun t => ∫ x : Vec3, ∑ i : Fin 3, heatOrbit a (x, t) i * ψ x i) (𝓝[>] 0)
        (𝓝 (∫ x : Vec3, ∑ i : Fin 3, a x i * ψ x i)) := by
  have hai (i : Fin 3) : MemLp (fun y => a y i) 2 volume := memLp_pi_iff.1 ha.1 i
  have hψi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x i) := contDiff_pi.1 hψ i
  have hψic (i : Fin 3) : HasCompactSupport (fun x => ψ x i) :=
    hψc.comp_left (g := fun v : Vec3 => v i) rfl
  have hψI (i : Fin 3) : Integrable (fun x => ψ x i) volume :=
    (hψi i).continuous.integrable_of_hasCompactSupport (hψic i)
  have hpair {t : ℝ} (ht : 0 < t) :
      ∫ x : Vec3, ∑ i : Fin 3, heatOrbit a (x, t) i * ψ x i =
        ∑ i : Fin 3, ∫ y : Vec3, a y i * heatConv t (fun x => ψ x i) y := by
    have hint (i : Fin 3) : Integrable (fun x => heatOrbit a (x, t) i * ψ x i) volume := by
      obtain ⟨M, -, hM⟩ := heatConv_heatConvGrad_bound ht (hai i)
      have hd : Differentiable ℝ (fun x => heatOrbit a (x, t) i) := fun x =>
        (heatConv_hasFDerivAt_of_memLp (hai i) ht x).differentiableAt
      exact (hψI i).bdd_mul (c := M) hd.continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          exact (hM t le_rfl x).1)
    rw [integral_finsetSum _ fun i _ => hint i]
    exact Finset.sum_congr rfl fun i _ => integral_heatConv_mul_eq (hai i) (hψI i) ht
  have hG (i : Fin 3) := integral_mul_heatConv_continuous_tendsto (hai i) (hψi i) (hψic i)
  refine ⟨?_, ?_⟩
  · have hcont : ContinuousOn (fun t => ∑ i : Fin 3,
        ∫ y : Vec3, a y i * heatConv t (fun x => ψ x i) y) (Ioi 0) :=
      continuousOn_finsetSum _ fun i _ => (hG i).1
    exact (hcont.congr fun t ht => hpair ht).mono Ioc_subset_Ioi_self
  · have hlim : Tendsto (fun t => ∑ i : Fin 3,
        ∫ y : Vec3, a y i * heatConv t (fun x => ψ x i) y) (𝓝[>] 0)
        (𝓝 (∑ i : Fin 3, ∫ y : Vec3, a y i * ψ y i)) :=
      tendsto_finsetSum _ fun i _ => (hG i).2
    have hsum : ∫ x : Vec3, ∑ i : Fin 3, a x i * ψ x i =
        ∑ i : Fin 3, ∫ y : Vec3, a y i * ψ y i :=
      integral_finsetSum _ fun i _ =>
        (hai i).integrable_mul ((hψi i).continuous.memLp_of_hasCompactSupport (p := 2) (hψic i))
    rw [hsum]
    exact hlim.congr' (eventually_mem_nhdsWithin.mono fun t ht => (hpair ht).symm)

end ESS

end
