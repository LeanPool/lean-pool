/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughSlices

/-!
# Weak gradients on time slices of the rough forced heat response

For almost every time, the `L²(Q_τ)` limit of the spatial gradients of smooth
forced heat responses is the weak spatial gradient of the time slice of the
rough response. This is the slicewise weak gradient clause of the
finite-energy class used in `prop:pv-local-solution`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private lemma forcedHeat_square_error_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hm : ∀ k, AEStronglyMeasurable (fun z => f k z - g z) μ)
    (hlim : Tendsto (fun k => eLpNorm (fun z => f k z - g z) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ z, ‖f k z - g z‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
  have h := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0 |>.comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hm k),
    ← ENNReal.rpow_mul]
  norm_num

private lemma forcedHeat_square_slice_finite
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {ν : Measure ℝ} [SFinite ν] {g : α × ℝ → ℝ}
    (hg : MemLp g 2 (μ.prod ν)) :
    ∀ᵐ s ∂ν, ∫⁻ x, ‖g (x, s)‖ₑ ^ (2 : ℝ) ∂μ < ∞ := by
  have hjoint := hg.aestronglyMeasurable.enorm.pow_const (2 : ℝ)
  have hfin : ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) ≠ ∞ := by
    have h := hg.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hg.aestronglyMeasurable] at h
    intro htop
    rw [ENNReal.toReal_ofNat, htop, ENNReal.top_rpow_of_pos (by norm_num)] at h
    exact lt_irrefl _ h
  rw [lintegral_prod_symm _ hjoint] at hfin
  exact ae_lt_top' hjoint.lintegral_prod_left' hfin

private lemma forcedHeat_weighted_component_pairing_bound
    (i : Fin 3) {v w : Vec3} {a c W : ℝ} (hc : 0 ≤ c) (ha : |a| ≤ c * W) :
    ‖(v i - w i) * a‖ₑ ≤
      ENNReal.ofReal c * (ENNReal.ofReal W * ‖v - w‖ₑ) := by
  rw [enorm_mul, Real.enorm_eq_ofReal_abs a]
  have h1 : ‖v i - w i‖ₑ ≤ ‖v - w‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm (v - w) i)
  have h2 : ENNReal.ofReal |a| ≤ ENNReal.ofReal c * ENNReal.ofReal W := by
    rw [← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal ha
  calc
    _ ≤ ‖v - w‖ₑ * (ENNReal.ofReal c * ENNReal.ofReal W) := mul_le_mul' h1 h2
    _ = _ := by ring

/-- Slicewise weak gradients of the rough forced heat response along a smooth
approximation whose spatial gradients converge in `L²(Q_τ)`. -/
theorem forcedHeat_slice_weakGradient_of_approx {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ} (hG2 : ∀ i j, MemLp (G i j) 2 volume)
    (hGsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0)
    {Gs : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ} {DZ : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hGs : ∀ k i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => Gs k i j p))
    (hGsc : ∀ k i j, HasCompactSupport (fun p : Vec3 × ℝ => Gs k i j p))
    (hGspos : ∀ k i j, tsupport (fun p : Vec3 × ℝ => Gs k i j p) ⊆ {p | 0 < p.2})
    (hGsconv : ∀ i j, Tendsto (fun k => eLpNorm (fun p : Vec3 × ℝ => Gs k i j p - G i j p) 2
      volume) atTop (𝓝 0))
    (hDZmem : ∀ i j, MemLp (DZ i j) 2
      (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hDZlim : ∀ i j, Tendsto (fun k => eLpNorm
      ((fun z => CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z) - DZ i j) 2
        (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) atTop (𝓝 0)) :
    ∀ᵐ s ∂(volume.restrict (Ioo 0 τ)), ∀ i : Fin 3,
      CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcedHeat G (x, s) i)
        (fun x => fun j => DZ i j (x, s)) := by
  set ν : Measure ℝ := volume.restrict (Ioo 0 τ)
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 τ) =
      (volume : Measure Vec3).prod ν := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  let g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j p => G i j p
  let gs : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun k i j p => Gs k i j p
  have hg2 (i j : Fin 3) : MemLp (g i j) 2 volume := hG2 i j
  have hgsupp (i j : Fin 3) (z : Vec3 × ℝ) (hz : g i j z ≠ 0) : 0 < z.2 := by
    by_contra hneg
    apply hz
    apply hGsupp i j z
    intro hmem
    exact hneg hmem.2.1
  have hconv (i j : Fin 3) : Tendsto (fun k => eLpNorm (gs k i j - g i j) 2 volume) atTop
      (𝓝 0) := hGsconv i j
  have hW := kernelResponse_weighted_tendsto hτ hg2 hgsupp (gn := gs) (fun k => hGs k)
    (fun k => hGsc k) (fun k => hGspos k) hconv
  rw [hprod] at hW
  -- the gradient differences
  let DZs : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun k i j z =>
    CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z
  have hDZm (i j : Fin 3) : AEStronglyMeasurable (fun z : Vec3 × ℝ => DZ i j z)
      ((volume : Measure Vec3).prod ν) := by
    have h := (hDZmem i j).aestronglyMeasurable
    rw [← hprod]
    exact h
  have hT : ContDiff ℝ 1 (heatRegTest 1) := (heatRegTest_contDiff one_pos).of_le (by simp)
  have hDZsc (k : ℕ) (i j : Fin 3) : Continuous (DZs k i j) := by
    have h := (continuous_apply i).comp ((response_continuity (hGs k) (hGsc k) hT).2.1 j)
    refine h.congr fun z => ?_
    exact (spatialPartial_forcedHeat_eq (hGs k) (hGsc k) i j z).symm
  have hE (i j : Fin 3) : Tendsto (fun k => ∫⁻ z, ‖DZs k i j z - DZ i j z‖ₑ ^ (2 : ℝ)
      ∂((volume : Measure Vec3).prod ν)) atTop (𝓝 0) := by
    apply forcedHeat_square_error_tendsto
      (fun k => (hDZsc k i j).aestronglyMeasurable.sub (hDZm i j))
    simpa only [← hprod] using hDZlim i j
  -- the combined slice quantity
  let F : ℕ → Vec3 × ℝ → ℝ≥0∞ := fun k z =>
    ENNReal.ofReal (forcedHeatWeight z.1) * ‖kernelResponse (gs k) z - kernelResponse g z‖ₑ +
      ∑ i : Fin 3, ∑ j : Fin 3, ‖DZs k i j z - DZ i j z‖ₑ ^ (2 : ℝ)
  have hZm : AEStronglyMeasurable (kernelResponse g) ((volume : Measure Vec3).prod ν) := by
    have h : AEStronglyMeasurable (kernelResponse g) volume :=
      (aemeasurable_pi_iff.2 fun i => (kernelResponse_component_aestronglyMeasurable
        (fun i j => (hg2 i j).aestronglyMeasurable) i).aemeasurable).aestronglyMeasurable
    rw [← hprod]
    exact h.restrict
  have hZkc (k : ℕ) : Continuous (kernelResponse (gs k)) :=
    continuous_pi fun i => (forcedHeat_contDiff (hGs k) (hGsc k) i).continuous
  have hWm (k : ℕ) : AEMeasurable (fun z : Vec3 × ℝ => ENNReal.ofReal (forcedHeatWeight z.1) *
      ‖kernelResponse (gs k) z - kernelResponse g z‖ₑ) ((volume : Measure Vec3).prod ν) :=
    (ENNReal.measurable_ofReal.comp (forcedHeatWeight_continuous.measurable.comp
      measurable_fst)).aemeasurable.mul ((hZkc k).aestronglyMeasurable.sub hZm).enorm
  have hDm (k : ℕ) (i j : Fin 3) : AEMeasurable (fun z : Vec3 × ℝ =>
      ‖DZs k i j z - DZ i j z‖ₑ ^ (2 : ℝ)) ((volume : Measure Vec3).prod ν) :=
    ((hDZsc k i j).aestronglyMeasurable.sub (hDZm i j)).enorm.pow_const _
  have hFm (k : ℕ) : AEMeasurable (F k) ((volume : Measure Vec3).prod ν) :=
    (hWm k).add (Finset.aemeasurable_fun_sum _ fun i _ =>
      Finset.aemeasurable_fun_sum _ fun j _ => hDm k i j)
  have hFlim : Tendsto (fun k => ∫⁻ z, F k z ∂((volume : Measure Vec3).prod ν)) atTop (𝓝 0) := by
    have hsplit (k : ℕ) : ∫⁻ z, F k z ∂((volume : Measure Vec3).prod ν) =
        (∫⁻ z, ENNReal.ofReal (forcedHeatWeight z.1) *
          ‖kernelResponse (gs k) z - kernelResponse g z‖ₑ ∂((volume : Measure Vec3).prod ν)) +
        ∑ i : Fin 3, ∑ j : Fin 3, ∫⁻ z, ‖DZs k i j z - DZ i j z‖ₑ ^ (2 : ℝ)
          ∂((volume : Measure Vec3).prod ν) := by
      simp only [F]
      rw [lintegral_add_left' (hWm k), lintegral_finsetSum' _ fun i _ =>
        Finset.aemeasurable_fun_sum _ fun j _ => hDm k i j]
      congr 1
      exact Finset.sum_congr rfl fun i _ => lintegral_finsetSum' _ fun j _ => hDm k i j
    simp_rw [hsplit]
    have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => hE i j
    have h := hW.add h2
    simpa only [Finset.sum_const_zero, add_zero] using h
  obtain ⟨m, hm⟩ := exists_subseq_slice_tendsto hFm hFlim
  -- almost every slice is measurable with a square integrable limit gradient
  have hA2 : ∀ᵐ s ∂ν, ∀ ij : Fin 3 × Fin 3,
      ∫⁻ x, ‖DZ ij.1 ij.2 (x, s)‖ₑ ^ (2 : ℝ) < ∞ :=
    ae_all_iff.2 fun ij => forcedHeat_square_slice_finite
      (by simpa only [← hprod] using hDZmem ij.1 ij.2)
  have hA3 : ∀ᵐ s ∂ν, ∀ ij : Fin 3 × Fin 3,
      AEStronglyMeasurable (fun x : Vec3 => DZ ij.1 ij.2 (x, s)) volume :=
    ae_all_iff.2 fun ij => ae_slice_aestronglyMeasurable (hDZm ij.1 ij.2)
  have hA4 : ∀ᵐ s ∂ν, AEStronglyMeasurable (fun x : Vec3 => kernelResponse g (x, s)) volume :=
    ae_slice_aestronglyMeasurable hZm
  filter_upwards [hm, hA2, hA3, hA4] with s hs hfin hmeas hzmeas
  intro i j χ hχ hχc _
  simp only [Measure.restrict_univ]
  -- slice convergence
  have hS : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (forcedHeatWeight x) *
      ‖kernelResponse (gs (m n)) (x, s) - kernelResponse g (x, s)‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun n => bot_le)
      fun n => lintegral_mono fun x => le_self_add
  have hTn : Tendsto (fun n => ∫⁻ x, ‖DZs (m n) i j (x, s) - DZ i j (x, s)‖ₑ ^ (2 : ℝ))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun n => bot_le)
      fun n => lintegral_mono fun x => ?_
    refine le_trans ?_ le_add_self
    refine le_trans ?_ (Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3,
      ‖DZs (m n) i' j' (x, s) - DZ i' j' (x, s)‖ₑ ^ (2 : ℝ)) (fun _ _ => bot_le)
      (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' =>
      ‖DZs (m n) i j' (x, s) - DZ i j' (x, s)‖ₑ ^ (2 : ℝ)) (fun _ _ => bot_le) (Finset.mem_univ j)
  -- the test function and its derivative
  have hDχc : Continuous (fun x => fderiv ℝ χ x (CKN.basisVec j)) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDχs : HasCompactSupport (fun x => fderiv ℝ χ x (CKN.basisVec j)) :=
    hχc.fderiv_apply (𝕜 := ℝ) _
  obtain ⟨c, hc0, hcχ⟩ := abs_le_mul_forcedHeatWeight_space hDχc hDχs
  -- smooth slice identities
  have hZn (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => kernelResponse (gs (m n)) (x, s) i) :=
    (forcedHeat_contDiff (hGs (m n)) (hGsc (m n)) i).comp (contDiff_id.prodMk contDiff_const)
  have hsmooth (n : ℕ) : ∫ x, kernelResponse (gs (m n)) (x, s) i * fderiv ℝ χ x (CKN.basisVec j) =
      -∫ x, DZs (m n) i j (x, s) * χ x := by
    have hZnd := (hZn n).continuous_fderiv (by simp)
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((((hZnd.clm_apply continuous_const)).mul hχ.continuous).integrable_of_hasCompactSupport
        hχc.mul_left)
      (((hZn n).continuous.mul hDχc).integrable_of_hasCompactSupport hDχs.mul_left)
      (((hZn n).continuous.mul hχ.continuous).integrable_of_hasCompactSupport hχc.mul_left)
      (fun x _ => (hZn n).differentiable (by simp) x) (fun x _ => hχ.differentiable (by simp) x)
  -- the left-hand side converges
  have hint_n (n : ℕ) : Integrable (fun x => kernelResponse (gs (m n)) (x, s) i *
      fderiv ℝ χ x (CKN.basisVec j)) :=
    ((hZn n).continuous.mul hDχc).integrable_of_hasCompactSupport hDχs.mul_left
  have hdiff (n : ℕ) (x : Vec3) :
      ‖(kernelResponse (gs (m n)) (x, s) i - kernelResponse g (x, s) i) *
        fderiv ℝ χ x (CKN.basisVec j)‖ₑ ≤ ENNReal.ofReal c * (ENNReal.ofReal (forcedHeatWeight x) *
          ‖kernelResponse (gs (m n)) (x, s) - kernelResponse g (x, s)‖ₑ) := by
    exact forcedHeat_weighted_component_pairing_bound i hc0 (hcχ x)
  have hlint (n : ℕ) : ∫⁻ x, ‖(kernelResponse (gs (m n)) (x, s) i - kernelResponse g (x, s) i) *
      fderiv ℝ χ x (CKN.basisVec j)‖ₑ ≤ ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal
        (forcedHeatWeight x) * ‖kernelResponse (gs (m n)) (x, s) - kernelResponse g (x, s)‖ₑ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun x => hdiff n x
  obtain ⟨n0, hn0⟩ := (hS.eventually (gt_mem_nhds zero_lt_one)).exists
  have hint : Integrable (fun x => kernelResponse g (x, s) i * fderiv ℝ χ x (CKN.basisVec j)) := by
    have hcomp : AEStronglyMeasurable (fun x : Vec3 => kernelResponse g (x, s) i) volume :=
      (continuous_apply i).comp_aestronglyMeasurable hzmeas
    refine ⟨hcomp.mul hDχc.aestronglyMeasurable, ?_⟩
    have hsplit (x : Vec3) : ‖kernelResponse g (x, s) i * fderiv ℝ χ x (CKN.basisVec j)‖ₑ ≤
        ‖(kernelResponse (gs (m n0)) (x, s) i - kernelResponse g (x, s) i) *
          fderiv ℝ χ x (CKN.basisVec j)‖ₑ +
        ‖kernelResponse (gs (m n0)) (x, s) i * fderiv ℝ χ x (CKN.basisVec j)‖ₑ := by
      rw [← enorm_neg ((kernelResponse (gs (m n0)) (x, s) i - kernelResponse g (x, s) i) *
        fderiv ℝ χ x (CKN.basisVec j))]
      refine le_trans (le_of_eq ?_) (enorm_add_le _ _)
      congr 1
      ring
    refine lt_of_le_of_lt (lintegral_mono hsplit) ?_
    rw [lintegral_add_right' _ (hint_n n0).aestronglyMeasurable.enorm]
    refine ENNReal.add_lt_top.2 ⟨?_, (hint_n n0).hasFiniteIntegral⟩
    exact lt_of_le_of_lt (hlint n0) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_trans hn0 ENNReal.one_lt_top))
  have hLHS : Tendsto (fun n => ∫ x, kernelResponse (gs (m n)) (x, s) i *
      fderiv ℝ χ x (CKN.basisVec j)) atTop
      (𝓝 (∫ x, kernelResponse g (x, s) i * fderiv ℝ χ x (CKN.basisVec j))) := by
    rw [tendsto_iff_edist_tendsto_0]
    have hbound (n : ℕ) : edist (∫ x, kernelResponse (gs (m n)) (x, s) i *
        fderiv ℝ χ x (CKN.basisVec j))
        (∫ x, kernelResponse g (x, s) i * fderiv ℝ χ x (CKN.basisVec j)) ≤
        ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (forcedHeatWeight x) *
          ‖kernelResponse (gs (m n)) (x, s) - kernelResponse g (x, s)‖ₑ := by
      rw [edist_eq_enorm_sub, ← integral_sub (hint_n n) hint]
      have hpt : (fun x => kernelResponse (gs (m n)) (x, s) i * fderiv ℝ χ x (CKN.basisVec j) -
          kernelResponse g (x, s) i * fderiv ℝ χ x (CKN.basisVec j)) =
          fun x => (kernelResponse (gs (m n)) (x, s) i - kernelResponse g (x, s) i) *
            fderiv ℝ χ x (CKN.basisVec j) := by
        funext x
        ring
      rw [hpt]
      exact (enorm_integral_le_lintegral_enorm _).trans (hlint n)
    have hzero := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c) hS
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hzero
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
      (fun n => bot_le) hbound
  -- the right-hand side converges
  have hDZslice : MemLp (fun x : Vec3 => DZ i j (x, s)) 2 volume := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (hmeas (i, j))]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by simpa using (hfin (i, j)).ne)
  have hRHS : Tendsto (fun n => -∫ x, DZs (m n) i j (x, s) * χ x) atTop
      (𝓝 (-∫ x, DZ i j (x, s) * χ x)) := by
    refine Tendsto.neg (tendsto_integral_mul_of_eLpNorm_two
      (f := fun n x => DZs (m n) i j (x, s)) (F := fun x => DZ i j (x, s))
      (fun n => forcedHeat_slice_grad_memLp (hGs (m n)) (hGsc (m n)) s i j) hDZslice
      (hχ.continuous.memLp_of_hasCompactSupport hχc) ?_)
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp hTn
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2)
      (f := (fun x : Vec3 => DZs (m n) i j (x, s)) - fun x => DZ i j (x, s)) two_ne_zero
      ENNReal.ofNat_ne_top
      ((((hDZsc (m n) i j).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable).sub
        (hmeas (i, j)))]
    norm_num
  have hLHS' : Tendsto (fun n => ∫ x, kernelResponse (gs (m n)) (x, s) i *
      fderiv ℝ χ x (CKN.basisVec j)) atTop (𝓝 (-∫ x, DZ i j (x, s) * χ x)) := by
    simp_rw [hsmooth]
    exact hRHS
  exact tendsto_nhds_unique hLHS hLHS'

end ESS

end
