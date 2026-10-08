/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRough

/-!
# The slicewise weak gradient of the rough forced heat response

Along a smooth approximation whose responses converge in the weighted `L¹`
sense and whose spatial gradients converge in `L²(Q_τ)`, a fast subsequence
converges on almost every time slice; passing the classical slice identities to
the limit shows that for almost every time the limit gradient is the weak
spatial gradient of the slice of the rough response, as required by the
finite-energy class of `prop:pv-local-solution`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Almost every time slice of a measurable space-time function is measurable. -/
theorem ae_slice_aestronglyMeasurable {X : Type*} [TopologicalSpace X]
    {ν : Measure ℝ} [SFinite ν] {f : Vec3 × ℝ → X}
    (hf : AEStronglyMeasurable f ((volume : Measure Vec3).prod ν)) :
    ∀ᵐ s ∂ν, AEStronglyMeasurable (fun x : Vec3 => f (x, s)) volume := by
  have hswap : AEStronglyMeasurable (fun q : ℝ × Vec3 => f (q.2, q.1))
      (ν.prod (volume : Measure Vec3)) :=
    hf.comp_measurePreserving (Measure.measurePreserving_swap (μ := ν)
      (ν := (volume : Measure Vec3)))
  exact hswap.prodMk_left

/-- A property holding almost everywhere on `Vec3 × ℝ` holds on almost every time
slice. -/
theorem ae_slice_of_ae {ν : Measure ℝ} [SFinite ν] {P : Vec3 × ℝ → Prop}
    (h : ∀ᵐ z ∂((volume : Measure Vec3).prod ν), P z) :
    ∀ᵐ s ∂ν, ∀ᵐ x ∂(volume : Measure Vec3), P (x, s) := by
  have hswap := (Measure.measurePreserving_swap (μ := ν)
    (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod hswap

/-- A continuous compactly supported function on Vec3 is dominated by a multiple
of the weight `forcedHeatWeight`. -/
theorem abs_le_mul_forcedHeatWeight_space {χ : Vec3 → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |χ x| ≤ c * forcedHeatWeight x := by
  obtain ⟨R, _, hRball⟩ := hχc.isCompact.isBounded.subset_closedBall_lt 0 (0 : Vec3)
  have hBdd : BddAbove (Set.range (fun p : Vec3 => ‖χ p‖)) :=
    hχ.norm.bddAbove_range_of_hasCompactSupport hχc.norm
  let B : ℝ := ⨆ p : Vec3, ‖χ p‖
  have hB (p : Vec3) : ‖χ p‖ ≤ B := le_ciSup hBdd p
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B * (1 + R) ^ 2, by positivity, fun x => ?_⟩
  by_cases hx : χ x = 0
  · rw [hx, abs_zero]
    exact mul_nonneg (by positivity) (forcedHeatWeight_pos _).le
  · have hmem := hRball (subset_tsupport χ hx)
    have hnorm : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hmem
    have hw : ((1 + R) ^ 2)⁻¹ ≤ forcedHeatWeight x := by
      unfold forcedHeatWeight
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith only [hnorm]) 2
    have hR : 0 ≤ R := (norm_nonneg _).trans hnorm
    calc
      |χ x| ≤ B := by rw [← Real.norm_eq_abs]; exact hB x
      _ = B * (1 + R) ^ 2 * ((1 + R) ^ 2)⁻¹ := by field_simp
      _ ≤ B * (1 + R) ^ 2 * forcedHeatWeight x :=
        mul_le_mul_of_nonneg_left hw (by positivity)

/-- A sequence of nonnegative space-time functions whose integrals tend to zero
has a subsequence whose slice integrals tend to zero for almost every time. -/
theorem exists_subseq_slice_tendsto {ν : Measure ℝ} [SFinite ν]
    {f : ℕ → Vec3 × ℝ → ℝ≥0∞} (hf : ∀ k, AEMeasurable (f k) ((volume : Measure Vec3).prod ν))
    (hlim : Tendsto (fun k => ∫⁻ z, f k z ∂((volume : Measure Vec3).prod ν)) atTop (𝓝 0)) :
    ∃ m : ℕ → ℕ, ∀ᵐ s ∂ν, Tendsto (fun n => ∫⁻ x, f (m n) (x, s)) atTop (𝓝 0) := by
  have hpos (n : ℕ) : (0 : ℝ≥0∞) < 2⁻¹ ^ n := ENNReal.pow_pos (by simp) n
  choose m hm using fun n : ℕ => (hlim.eventually (ge_mem_nhds (hpos n))).exists
  refine ⟨m, ?_⟩
  let F : ℕ → ℝ → ℝ≥0∞ := fun n s => ∫⁻ x, f (m n) (x, s)
  have hFm (n : ℕ) : AEMeasurable (F n) ν := (hf (m n)).lintegral_prod_left'
  have hFint (n : ℕ) : ∫⁻ s, F n s ∂ν ≤ 2⁻¹ ^ n := by
    rw [← lintegral_prod_symm _ (hf (m n))]
    exact hm n
  have hsum : ∫⁻ s, ∑' n, F n s ∂ν ≠ ∞ := by
    rw [lintegral_tsum hFm]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hFint)
    rw [ENNReal.tsum_geometric]
    refine ENNReal.inv_ne_top.2 (tsub_pos_of_lt ?_).ne'
    exact ENNReal.inv_lt_one.2 (by norm_num)
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hFm) hsum] with s hs
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hs.ne

/-- The slices of smooth forced heat responses are square integrable in space
together with their spatial gradients. -/
theorem forcedHeat_slice_grad_memLp {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p)) (s : ℝ) (i j : Fin 3) :
    MemLp (fun x : Vec3 => CKN.spatialPartial (fun w => forcedHeat G w i) j (x, s)) 2 volume := by
  let g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j p => G i j p
  obtain ⟨M, hM, hdec⟩ := vecTimeDiv_response_decay (g := g) hG hGc
  have hU : ContDiff ℝ (⊤ : ℕ∞) (causalHeatConv (vecTimeDiv g i)) :=
    causalHeatConv_contDiff (vecTimeDiv_contDiff hG i) (vecTimeDiv_hasCompactSupport hGc i)
  have hc : Continuous (fun x : Vec3 => fderiv ℝ (causalHeatConv (vecTimeDiv g i)) (x, s)
      (CKN.basisVec j, 0)) :=
    ((hU.continuous_fderiv (by simp)).clm_apply continuous_const).comp
      (continuous_id.prodMk continuous_const)
  have heq : (fun x : Vec3 => CKN.spatialPartial (fun w => forcedHeat G w i) j (x, s)) =
      fun x => fderiv ℝ (causalHeatConv (vecTimeDiv g i)) (x, s) (CKN.basisVec j, 0) :=
    funext fun x => spatialPartial_forcedHeat_eq hG hGc i j (x, s)
  rw [heq, memLp_two_iff_integrable_sq hc.aestronglyMeasurable]
  refine integrable_of_abs_le_decay_six' (sq_nonneg M) (hc.pow 2) fun x => ?_
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := pow_le_pow_left₀ (abs_nonneg _) (hdec i j j (x, s)).2.1 2
  rw [sq_abs, div_pow, ← pow_mul] at h
  exact h

end ESS

end
