/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionPairingKernel
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionPairingWeights

/-!
# Time continuity of the forced heat response against a test field

For a tensor `G ∈ L^{5/2}` supported in `ℝ³ × (0, τ)` and a smooth compactly
supported test field `ψ`, the pairing `t ↦ ∫ Z(x, t) · ψ(x) dx` of the forced
heat response `Z = forcedHeat G` is defined for every `t ∈ [0, τ]`, continuous
there, and zero at `t = 0` (`prop:pv-local-solution`).

For each `t` the triple integral of `|ψ_i(x)| |∂_jΓ(x - y, t - s)| |G_ij(y, s)|`
is finite: the `x`-integral is at most `C (t - s)^{-1/2} (1 + |y|)^{-3}`, and
Hölder's inequality with exponents `5/2` and `5/3` closes the bound. Fubini's
theorem then writes the pairing as `∫ ∑ K_ij(y, t - s) G_ij(y, s)`, where
`K_ij = testKernelPairing ψ i j` is bounded by `C (1 + |y|)^{-3}` uniformly in
time and continuous away from `t = s`; dominated convergence gives continuity.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The integrand of the pairing, after the change of variables `p = (x, t) - q`,
is integrable in `(x, q)`. -/
private theorem pairing_integrand_integrable {τ : ℝ} (hτ : 0 < τ) {t : ℝ} (ht : t ∈ Icc 0 τ)
    {g : Vec3 × ℝ → ℝ} (hg : MemLp g (ENNReal.ofReal (5 / 2)) volume)
    (hsupp : ∀ q : Vec3 × ℝ, q.2 ∉ Ioo 0 τ → g q = 0)
    {ψ : Vec3 → Vec3} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (i j : Fin 3) :
    Integrable (fun w : Vec3 × (Vec3 × ℝ) =>
      ψ w.1 i * heatKernelSpaceDerivative (w.1 - w.2.1) (t - w.2.2) j * g w.2)
      ((volume : Measure Vec3).prod (volume : Measure (Vec3 × ℝ))) := by
  obtain ⟨M, hM0, hM⟩ := testKernelPairing_lintegral_le hψ hψc i j
  have hmeas : AEStronglyMeasurable (fun w : Vec3 × (Vec3 × ℝ) =>
      ψ w.1 i * heatKernelSpaceDerivative (w.1 - w.2.1) (t - w.2.2) j * g w.2)
      ((volume : Measure Vec3).prod (volume : Measure (Vec3 × ℝ))) := by
    refine AEStronglyMeasurable.mul ?_
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.mul ?_ ?_
    · exact ((continuous_apply i).comp hψ).measurable.comp measurable_fst
    · exact (heatKernelSpaceDerivative_vecTime_measurable j).comp
        ((measurable_fst.sub (measurable_fst.comp measurable_snd)).prodMk
          (measurable_const.sub (measurable_snd.comp measurable_snd)))
  refine ⟨hmeas, ?_⟩
  -- the dominating weight
  set b : ℝ → ℝ := fun s => M * (Ioo 0 τ).indicator (fun r => (Real.sqrt r)⁻¹) (t - s)
    with hbdef
  have hb : MemLp b (ENNReal.ofReal (5 / 3)) volume :=
    ((memLp_inv_sqrt_indicator hτ).comp_measurePreserving
      (Measure.measurePreserving_sub_left volume t)).const_mul M
  have hW := integrable_mul_spaceTime_weight hg hb
  have hkey (q : Vec3 × ℝ) (hq : g q ≠ 0) :
      (Real.sqrt (t - q.2))⁻¹ = (Ioo 0 τ).indicator (fun r => (Real.sqrt r)⁻¹) (t - q.2) := by
    have hq2 : q.2 ∈ Ioo 0 τ := by
      by_contra h
      exact hq (hsupp q h)
    by_cases hpos : 0 < t - q.2
    · rw [indicator_of_mem]
      exact ⟨hpos, by linarith only [hq2.1, ht.2]⟩
    · rw [indicator_of_notMem (fun h => hpos h.1),
        Real.sqrt_eq_zero'.2 (le_of_not_gt hpos), inv_zero]
  have hbound (q : Vec3 × ℝ) :
      ∫⁻ x : Vec3, ‖ψ x i * heatKernelSpaceDerivative (x - q.1) (t - q.2) j * g q‖ₑ ≤
        ‖g q * (b q.2 * (1 + ‖q.1‖) ^ (-3 : ℝ))‖ₑ := by
    simp_rw [enorm_mul (ψ _ i * _) (g q)]
    rw [lintegral_mul_const' _ _ enorm_ne_top]
    by_cases hq : g q = 0
    · rw [hq, enorm_zero, mul_zero]
      exact zero_le
    calc
      (∫⁻ x : Vec3, ‖ψ x i * heatKernelSpaceDerivative (x - q.1) (t - q.2) j‖ₑ) * ‖g q‖ₑ ≤
          ENNReal.ofReal (M * (Real.sqrt (t - q.2))⁻¹ * (1 + ‖q.1‖) ^ (-3 : ℝ)) * ‖g q‖ₑ :=
        mul_le_mul_left (hM q.1 (t - q.2)) _
      _ = ‖g q * (b q.2 * (1 + ‖q.1‖) ^ (-3 : ℝ))‖ₑ := by
        have hind : 0 ≤ (Ioo 0 τ).indicator (fun r => (Real.sqrt r)⁻¹) (t - q.2) :=
          indicator_nonneg (fun r _ => by positivity) _
        have hnn : 0 ≤ b q.2 * (1 + ‖q.1‖) ^ (-3 : ℝ) := by
          simp only [hbdef]
          positivity
        rw [enorm_mul, mul_comm, hkey q hq, Real.enorm_eq_ofReal hnn]
  refine lt_of_eq_of_lt (lintegral_prod_symm _ hmeas.enorm) ?_
  calc
    ∫⁻ q : Vec3 × ℝ, ∫⁻ x : Vec3,
        ‖ψ x i * heatKernelSpaceDerivative (x - q.1) (t - q.2) j * g q‖ₑ ≤
        ∫⁻ q : Vec3 × ℝ, ‖g q * (b q.2 * (1 + ‖q.1‖) ^ (-3 : ℝ))‖ₑ := lintegral_mono hbound
    _ < ∞ := hW.2

/-- Fubini form of the pairing at a fixed time `t ∈ [0, τ]`: the pairing is
integrable in space and equals `∫ ∑ K_ij(y, t - s) G_ij(y, s)`. -/
private theorem forcedHeat_pairing_eq {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, MemLp (fun q : Vec3 × ℝ => G i j q) (ENNReal.ofReal (5 / 2)) volume)
    (hsupp : ∀ i j (q : Vec3 × ℝ), q.2 ∉ Ioo 0 τ → G i j q = 0)
    {ψ : Vec3 → Vec3} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {t : ℝ}
    (ht : t ∈ Icc 0 τ) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, forcedHeat G (x, t) i * ψ x i) ∧
    (∫ x : Vec3, ∑ i : Fin 3, forcedHeat G (x, t) i * ψ x i) =
      ∫ q : Vec3 × ℝ, ∑ i : Fin 3, ∑ j : Fin 3,
        testKernelPairing ψ i j q.1 (t - q.2) * G i j q := by
  set F : Fin 3 → Fin 3 → Vec3 × (Vec3 × ℝ) → ℝ := fun i j w =>
    ψ w.1 i * heatKernelSpaceDerivative (w.1 - w.2.1) (t - w.2.2) j * G i j w.2 with hFdef
  have hF (i j : Fin 3) :
      Integrable (F i j) ((volume : Measure Vec3).prod (volume : Measure (Vec3 × ℝ))) :=
    pairing_integrand_integrable hτ ht (hG i j) (hsupp i j) hψ hψc i j
  have hFi (i : Fin 3) : Integrable (fun w => ∑ j : Fin 3, F i j w)
      ((volume : Measure Vec3).prod (volume : Measure (Vec3 × ℝ))) :=
    integrable_finsetSum _ fun j _ => hF i j
  have hFt : Integrable (fun w => ∑ i : Fin 3, ∑ j : Fin 3, F i j w)
      ((volume : Measure Vec3).prod (volume : Measure (Vec3 × ℝ))) :=
    integrable_finsetSum _ fun i _ => hFi i
  have hpoint (x : Vec3) (i : Fin 3) :
      forcedHeat G (x, t) i * ψ x i = ∫ q : Vec3 × ℝ, ∑ j : Fin 3, F i j (x, q) := by
    set h : Vec3 × ℝ → ℝ := fun p => ψ x i * ∑ j : Fin 3,
      heatKernelSpaceDerivative p.1 p.2 j * G i j (((x, t) : Vec3 × ℝ) - p) with hhdef
    have hZ : forcedHeat G (x, t) i = ∫ p : Vec3 × ℝ, ∑ j : Fin 3,
        heatKernelSpaceDerivative p.1 p.2 j * G i j (((x, t) : Vec3 × ℝ) - p) := rfl
    calc
      forcedHeat G (x, t) i * ψ x i = ∫ p : Vec3 × ℝ, h p := by
        rw [hZ, mul_comm, ← integral_const_mul]
      _ = ∫ q : Vec3 × ℝ, h (((x, t) : Vec3 × ℝ) - q) :=
        (integral_sub_left_eq_self h (volume : Measure (Vec3 × ℝ)) ((x, t) : Vec3 × ℝ)).symm
      _ = ∫ q : Vec3 × ℝ, ∑ j : Fin 3, F i j (x, q) := by
        congr 1
        funext q
        simp only [hhdef, hFdef, Finset.mul_sum, Prod.fst_sub, Prod.snd_sub, sub_sub_cancel]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
  have hae_x : ∀ᵐ x ∂(volume : Measure Vec3), ∀ i : Fin 3,
      Integrable (fun q : Vec3 × ℝ => ∑ j : Fin 3, F i j (x, q)) :=
    ae_all_iff.2 fun i => (hFi i).prod_right_ae
  have hsum_x : ∀ᵐ x ∂(volume : Measure Vec3),
      ∑ i : Fin 3, forcedHeat G (x, t) i * ψ x i =
        ∫ q : Vec3 × ℝ, ∑ i : Fin 3, ∑ j : Fin 3, F i j (x, q) := by
    filter_upwards [hae_x] with x hx
    rw [integral_finsetSum _ fun i _ => hx i]
    exact Finset.sum_congr rfl fun i _ => hpoint x i
  have hint : Integrable (fun x : Vec3 => ∫ q : Vec3 × ℝ, ∑ i : Fin 3, ∑ j : Fin 3, F i j (x, q)) :=
    hFt.integral_prod_left
  refine ⟨hint.congr (hsum_x.mono fun x hx => hx.symm), ?_⟩
  rw [integral_congr_ae hsum_x,
    integral_integral_swap (f := fun x q => ∑ i : Fin 3, ∑ j : Fin 3, F i j (x, q)) hFt]
  apply integral_congr_ae
  have hae_q : ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)), ∀ i j : Fin 3,
      Integrable (fun x : Vec3 => F i j (x, q)) := by
    have h := fun ij : Fin 3 × Fin 3 => (hF ij.1 ij.2).prod_left_ae
    filter_upwards [ae_all_iff.2 h] with q hq i j
    exact hq (i, j)
  filter_upwards [hae_q] with q hq
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hq i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hq i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hFdef]
  rw [integral_mul_const]
  rfl

/-- The Fubini form of the pairing is continuous in time: the kernels are bounded
by `C (1 + |y|)^{-3}` uniformly in time and continuous away from `t = s`. -/
private theorem pairing_formula_continuous {τ : ℝ}
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, MemLp (fun q : Vec3 × ℝ => G i j q) (ENNReal.ofReal (5 / 2)) volume)
    (hsupp : ∀ i j (q : Vec3 × ℝ), q.2 ∉ Ioo 0 τ → G i j q = 0)
    {ψ : Vec3 → Vec3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    Continuous (fun t : ℝ => ∫ q : Vec3 × ℝ, ∑ i : Fin 3, ∑ j : Fin 3,
      testKernelPairing ψ i j q.1 (t - q.2) * G i j q) := by
  choose M hM0 hM using fun i j => testKernelPairing_abs_le hψ hψc i j
  set ind : ℝ → ℝ := fun s => (Ioo 0 τ).indicator (fun _ => (1 : ℝ)) s with hinddef
  have hindL (i j : Fin 3) :
      MemLp (fun s => M i j * ind s) (ENNReal.ofReal (5 / 3)) volume :=
    (memLp_indicator_const _ measurableSet_Ioo (1 : ℝ)
      (Or.inr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))).const_mul (M i j)
  set bound : Vec3 × ℝ → ℝ := fun q => ∑ i : Fin 3, ∑ j : Fin 3,
    ‖G i j q * (M i j * ind q.2 * (1 + ‖q.1‖) ^ (-3 : ℝ))‖ with hbounddef
  have hbound_int : Integrable bound :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_mul_spaceTime_weight (hG i j) (hindL i j)).norm
  have hnull (t₀ : ℝ) : (volume : Measure (Vec3 × ℝ)) {q | q.2 = t₀} = 0 := by
    have hset : {q : Vec3 × ℝ | q.2 = t₀} = (univ : Set Vec3) ×ˢ {t₀} := by
      ext q
      simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  rw [continuous_iff_continuousAt]
  intro t₀
  refine continuousAt_of_dominated (bound := bound) ?_ ?_ hbound_int ?_
  · refine Eventually.of_forall fun t => ?_
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    exact ((testKernelPairing_measurable ψ hψ.continuous i j).comp
      (measurable_fst.prodMk (measurable_const.sub measurable_snd))).aestronglyMeasurable.mul
      (hG i j).aestronglyMeasurable
  · refine Eventually.of_forall fun t => Eventually.of_forall fun q => ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    by_cases hq : G i j q = 0
    · simp [hq]
    have hq2 : q.2 ∈ Ioo 0 τ := by
      by_contra h
      exact hq (hsupp i j q h)
    have hind1 : ind q.2 = 1 := indicator_of_mem hq2 _
    rw [hind1, mul_one, norm_mul, norm_mul, mul_comm ‖G i j q‖]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hMa : 0 ≤ M i j * (1 + ‖q.1‖) ^ (-3 : ℝ) := by
      have := hM0 i j
      positivity
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hMa]
    exact hM i j q.1 (t - q.2)
  · have hae : ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)), q.2 ≠ t₀ := by
      refine ae_iff.2 ?_
      simp only [ne_eq, not_not]
      exact hnull t₀
    filter_upwards [hae] with q hq
    have hr : t₀ - q.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    exact (ContinuousAt.comp (g := fun r => testKernelPairing ψ i j q.1 r)
      (f := fun t => t - q.2) (x := t₀) (testKernelPairing_continuousAt hψ hψc i j q.1 hr)
      ((continuous_sub_right q.2).continuousAt)).mul continuousAt_const

/-- Time continuity of the forced heat response against a fixed test field
(`prop:pv-local-solution`): for a tensor `G ∈ L^{5/2}` supported in
`ℝ³ × (0, τ)` and a smooth compactly supported test field `ψ`, the pairing
`∫ Z(x, t) · ψ(x) dx` of `Z = forcedHeat G` is defined for every `t ∈ [0, τ]`,
continuous on `[0, τ]`, and zero at `t = 0`. -/
theorem forcedHeat_pairing_continuous {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume)
    (hsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0)
    {ψ : Vec3 → Vec3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∀ t ∈ Icc 0 τ, Integrable (fun x : Vec3 => ∑ i : Fin 3, forcedHeat G (x, t) i * ψ x i)) ∧
    ContinuousOn (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, forcedHeat G (x, t) i * ψ x i)
      (Icc 0 τ) ∧
    (∫ x : Vec3, ∑ i : Fin 3, forcedHeat G (x, 0) i * ψ x i) = 0 := by
  have hG' (i j : Fin 3) :
      MemLp (fun q : Vec3 × ℝ => G i j q) (ENNReal.ofReal (5 / 2)) volume := hG i j
  have hsupp' (i j : Fin 3) (q : Vec3 × ℝ) (hq : q.2 ∉ Ioo 0 τ) : G i j q = 0 :=
    hsupp i j q fun hmem => hq (Set.mem_prod.1 hmem).2
  refine ⟨fun t ht => (forcedHeat_pairing_eq hτ hG' hsupp' hψ.continuous hψc ht).1, ?_, ?_⟩
  · exact (pairing_formula_continuous hG' hsupp' hψ hψc).continuousOn.congr fun t ht =>
      (forcedHeat_pairing_eq hτ hG' hsupp' hψ.continuous hψc ht).2
  · have hGpos : ∀ i j (p : ParabolicPoint), G i j p ≠ 0 → 0 < p.2 := fun i j p hp => by
      by_contra hneg
      exact hp (hsupp' i j p fun h => hneg h.1)
    have hzero (x : Vec3) : forcedHeat G (x, 0) = 0 :=
      forcedHeat_eq_zero_of_nonpos hGpos (z := (x, 0)) le_rfl
    simp [hzero]

end ESS

end
