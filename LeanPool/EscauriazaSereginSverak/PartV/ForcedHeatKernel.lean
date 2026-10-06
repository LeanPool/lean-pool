/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatConv
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Integrability
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus

/-!
# The zero-data forced heat response in kernel form

For a tensor source `G`, the response `Z_i = ∑_j ∂_j W₊ ⋆ G_ij` solves the
componentwise heat equation `∂_t Z_i - Δ Z_i = ∑_j ∂_j G_ij` with zero data;
this is the scalar reformulation of `lem:pv-stokes` once the pressure is
folded into the source. For smooth compactly supported sources an integration
by parts in space moves the derivative onto the source, which identifies the
response with the causal heat potential of the divergence.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The zero-data forced heat response of a space-time tensor `G`:
`Z_i(z) = ∫ ∑_j ∂_j W₊(p) G_ij(z - p) dp`, the kernel form of the Duhamel
formula used in `lem:pv-stokes`. -/
@[expose] def forcedHeat (G : Fin 3 → Fin 3 → ParabolicPoint → ℝ) (z : ParabolicPoint) : Vec3 :=
  fun i => ∫ p : ParabolicPoint, ∑ j : Fin 3,
    heatKernelSpaceDerivative p.1 p.2 j * G i j (z.1 - p.1, z.2 - p.2)

private theorem heatKernelGradientNorm_locallyIntegrable_vecTime :
    LocallyIntegrable (fun p : Vec3 × ℝ => heatKernelGradientNorm p.1 p.2) volume := by
  intro z
  obtain ⟨U, hU, hint⟩ :=
    heatKernelGradientNorm_locallyIntegrable (parabolicHomeomorph.symm z)
  refine ⟨parabolicHomeomorph '' U, ?_, ?_⟩
  · have h : parabolicHomeomorph '' U ∈
        Filter.map (⇑parabolicHomeomorph) (nhds (parabolicHomeomorph.symm z)) :=
      Filter.image_mem_map hU
    rwa [parabolicHomeomorph.map_nhds_eq, parabolicHomeomorph.apply_symm_apply] at h
  · have himg : parabolicHomeomorph '' U = U := by
      ext w
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact hp
      · intro hw
        exact ⟨w, hw, rfl⟩
    rw [himg]
    exact hint

/-- Each spatial derivative of the causal heat kernel is measurable on `Vec3 × ℝ`. -/
theorem heatKernelSpaceDerivative_vecTime_measurable (j : Fin 3) :
    Measurable (fun p : Vec3 × ℝ => heatKernelSpaceDerivative p.1 p.2 j) := by
  unfold heatKernelSpaceDerivative heatKernel
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd) ?_ measurable_const
  apply Measurable.mul (by fun_prop)
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd) ?_ measurable_const
  fun_prop

/-- Each spatial derivative of the causal heat kernel is locally integrable on
`Vec3 × ℝ`. -/
theorem heatKernelSpaceDerivative_locallyIntegrable (j : Fin 3) :
    LocallyIntegrable (fun p : Vec3 × ℝ => heatKernelSpaceDerivative p.1 p.2 j) volume :=
  heatKernelGradientNorm_locallyIntegrable_vecTime.mono
    (heatKernelSpaceDerivative_vecTime_measurable j).aestronglyMeasurable
    (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      refine le_trans ?_ (le_abs_self _)
      exact Finset.single_le_sum (f := fun k => |heatKernelSpaceDerivative p.1 p.2 k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ j))

private theorem heatKernel_slice_contDiff {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => heatKernel y s) := by
  have heq : (fun y : Vec3 => heatKernel y s) = fun y : Vec3 =>
      (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) * Real.exp (-(∑ i, y i ^ 2) / (4 * s)) := by
    funext y
    exact heatKernel_eq_formula_sum hs
  rw [heq]
  fun_prop

private theorem kernel_slice_ibp {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (v : Vec3 × ℝ) (j : Fin 3) {s : ℝ} (hs : 0 < s) :
    ∫ y : Vec3, heatKernelSpaceDerivative y s j * g (v - (y, s)) =
      ∫ y : Vec3, heatKernel y s * fderiv ℝ g (v - (y, s)) (CKN.basisVec j, 0) := by
  let ψ : Vec3 × ℝ → ℝ := fun w => g (v - w)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hg.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hgc.comp_homeomorph (Homeomorph.subLeft v)
  let Gs : Vec3 → ℝ := fun y => ψ (y, s)
  have hGs : ContDiff ℝ (⊤ : ℕ∞) Gs := test_slice_contDiff hψ s
  have hGsc : HasCompactSupport Gs := test_slice_hasCompactSupport hψc s
  let F : Vec3 → ℝ := fun y => heatKernel y s
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := heatKernel_slice_contDiff hs
  have hDF (y : Vec3) : fderiv ℝ F y (CKN.basisVec j) = heatKernelSpaceDerivative y s j :=
    heatKernel_fderiv_apply_basisVec hs j
  have hDGs (y : Vec3) : fderiv ℝ Gs y (CKN.basisVec j) =
      -fderiv ℝ g (v - (y, s)) (CKN.basisVec j, 0) := by
    have hpartial : fderiv ℝ Gs y (CKN.basisVec j) =
        CKN.spatialPartial (show ParabolicPoint → ℝ from ψ) j (y, s) := rfl
    rw [hpartial, spatialPartial_eq_fderiv_apply hψ j y s,
      fderiv_comp_sub_left_apply (hg.differentiable (by simp))]
  have hFc : Continuous F := hF.continuous
  have hDFc : Continuous (fun y => fderiv ℝ F y (CKN.basisVec j)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDGsc : Continuous (fun y => fderiv ℝ Gs y (CKN.basisVec j)) :=
    (hGs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDGscs : HasCompactSupport (fun y => fderiv ℝ Gs y (CKN.basisVec j)) :=
    hGsc.fderiv_apply (𝕜 := ℝ) _
  have h1 : Integrable (fun y => fderiv ℝ F y (CKN.basisVec j) * Gs y) :=
    (hDFc.mul hGs.continuous).integrable_of_hasCompactSupport hGsc.mul_left
  have h2 : Integrable (fun y => F y * fderiv ℝ Gs y (CKN.basisVec j)) :=
    (hFc.mul hDGsc).integrable_of_hasCompactSupport hDGscs.mul_left
  have h3 : Integrable (fun y => F y * Gs y) :=
    (hFc.mul hGs.continuous).integrable_of_hasCompactSupport hGsc.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun y _ => (hF.differentiable (by simp)) y)
    (fun y _ => (hGs.differentiable (by simp)) y)
  have hleft : (fun y : Vec3 => heatKernelSpaceDerivative y s j * g (v - (y, s))) =
      fun y => fderiv ℝ F y (CKN.basisVec j) * Gs y := by
    funext y
    rw [hDF]
  have hright : (fun y : Vec3 => F y * fderiv ℝ Gs y (CKN.basisVec j)) =
      fun y => -(heatKernel y s * fderiv ℝ g (v - (y, s)) (CKN.basisVec j, 0)) := by
    funext y
    rw [hDGs]
    ring
  rw [hleft, ← neg_neg (∫ y, fderiv ℝ F y (CKN.basisVec j) * Gs y), ← hibp, hright,
    integral_neg, neg_neg]

/-- Integration by parts in space: the spatial-derivative kernel against a
smooth compactly supported source equals the causal heat kernel against the
spatial derivative of the source. -/
theorem heatKernelSpaceDerivative_convolution_eq {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (v : Vec3 × ℝ) (j : Fin 3) :
    ∫ p : Vec3 × ℝ, heatKernelSpaceDerivative p.1 p.2 j * g (v - p) =
      ∫ p : Vec3 × ℝ, heatKernelPlus p * fderiv ℝ g (v - p) (CKN.basisVec j, 0) := by
  have hshift : Continuous (fun p : Vec3 × ℝ => g (v - p)) :=
    hg.continuous.comp (continuous_const.sub continuous_id)
  have hshiftc : HasCompactSupport (fun p : Vec3 × ℝ => g (v - p)) :=
    hgc.comp_homeomorph (Homeomorph.subLeft v)
  have hDg : Continuous (fun q => fderiv ℝ g q (CKN.basisVec j, 0)) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDgc : HasCompactSupport (fun p : Vec3 × ℝ => fderiv ℝ g (v - p) (CKN.basisVec j, 0)) :=
    (hgc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j, 0)).comp_homeomorph (Homeomorph.subLeft v)
  have hL : Integrable (fun p : Vec3 × ℝ =>
      heatKernelSpaceDerivative p.1 p.2 j * g (v - p)) :=
    (heatKernelSpaceDerivative_locallyIntegrable j).integrable_smul_right_of_hasCompactSupport
      hshift hshiftc
  have hR : Integrable (fun p : Vec3 × ℝ =>
      heatKernelPlus p * fderiv ℝ g (v - p) (CKN.basisVec j, 0)) :=
    heatKernelPlus_locallyIntegrable_prod_volume.integrable_smul_right_of_hasCompactSupport
      (hDg.comp (continuous_const.sub continuous_id)) hDgc
  rw [Measure.volume_eq_prod] at hL hR ⊢
  rw [integral_prod_symm _ hL, integral_prod_symm _ hR]
  congr 1
  funext s
  by_cases hs : 0 < s
  · have hplus : (fun y : Vec3 => heatKernelPlus (show ParabolicPoint from (y, s)) *
        fderiv ℝ g (v - (y, s)) (CKN.basisVec j, 0)) =
        fun y => heatKernel y s * fderiv ℝ g (v - (y, s)) (CKN.basisVec j, 0) := by
      funext y
      rw [heatKernelPlus_eq_heatKernel]
    exact (kernel_slice_ibp hg hgc v j hs).trans (congrArg _ hplus.symm)
  · have hzeroL : (fun y : Vec3 => heatKernelSpaceDerivative y s j * g (v - (y, s))) =
        fun _ => 0 := by
      funext y
      simp [heatKernelSpaceDerivative, hs]
    have hzeroR : (fun y : Vec3 => heatKernelPlus (show ParabolicPoint from (y, s)) *
        fderiv ℝ g (v - (y, s)) (CKN.basisVec j, 0)) = fun _ => 0 := by
      funext y
      rw [heatKernelPlus_eq_zero_of_nonpos (le_of_not_gt hs), zero_mul]
    exact (congrArg _ hzeroL).trans ((congrArg _ hzeroR).symm)

private theorem spatialPartial_eq_fderiv_vecTime {g : ParabolicPoint → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => g p)) (j : Fin 3) (q : Vec3 × ℝ) :
    CKN.spatialPartial g j q = fderiv ℝ (fun p : Vec3 × ℝ => g p) q (CKN.basisVec j, 0) :=
  spatialPartial_eq_fderiv_apply hg j q.1 q.2

/-- For a smooth compactly supported tensor, the forced heat response is the
causal heat potential of the tensor divergence `∑_j ∂_j G_ij`. -/
theorem forcedHeat_eq_causalHeatConv {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p)) (i : Fin 3) :
    (fun z : Vec3 × ℝ => forcedHeat G z i) =
      causalHeatConv (fun q => ∑ j : Fin 3, CKN.spatialPartial (G i j) j q) := by
  funext z
  have hint (j : Fin 3) : Integrable (fun p : Vec3 × ℝ =>
      heatKernelSpaceDerivative p.1 p.2 j * G i j (z - p)) :=
    (heatKernelSpaceDerivative_locallyIntegrable j).integrable_smul_right_of_hasCompactSupport
      ((hG i j).continuous.comp (continuous_const.sub continuous_id))
      ((hGc i j).comp_homeomorph (Homeomorph.subLeft z))
  have hintR (j : Fin 3) : Integrable (fun p : Vec3 × ℝ =>
      heatKernelPlus p * fderiv ℝ (fun q : Vec3 × ℝ => G i j q) (z - p)
        (CKN.basisVec j, 0)) :=
    heatKernelPlus_locallyIntegrable_prod_volume.integrable_smul_right_of_hasCompactSupport
      ((((hG i j).continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_const.sub continuous_id))
      (((hGc i j).fderiv_apply (𝕜 := ℝ) (CKN.basisVec j, 0)).comp_homeomorph
        (Homeomorph.subLeft z))
  change (∫ p : Vec3 × ℝ, ∑ j : Fin 3,
      heatKernelSpaceDerivative p.1 p.2 j * G i j (z - p)) = _
  rw [integral_finsetSum _ fun j _ => hint j, causalHeatConv_eq_integral]
  have hsource (p : Vec3 × ℝ) : heatKernelPlus p *
      ∑ j : Fin 3, CKN.spatialPartial (G i j) j (z - p) =
      ∑ j : Fin 3, heatKernelPlus p *
        fderiv ℝ (fun q : Vec3 × ℝ => G i j q) (z - p) (CKN.basisVec j, 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [spatialPartial_eq_fderiv_vecTime (hG i j)]
  simp_rw [hsource]
  rw [integral_finsetSum _ fun j _ => hintR j]
  apply Finset.sum_congr rfl
  intro j _
  exact heatKernelSpaceDerivative_convolution_eq (hG i j) (hGc i j) z j

/-- The tensor divergence of a smooth compactly supported tensor is smooth. -/
theorem tensorDivergence_contDiff {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => ∑ j : Fin 3, CKN.spatialPartial (G i j) j q) :=
  ContDiff.sum fun j _ => CKN.spatialPartial_contDiff (ψ := fun p : Vec3 × ℝ => G i j p) (hG i j) j

/-- The tensor divergence of a compactly supported smooth tensor has compact
support. -/
theorem tensorDivergence_hasCompactSupport {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p)) (i : Fin 3) :
    HasCompactSupport (fun q : Vec3 × ℝ => ∑ j : Fin 3, CKN.spatialPartial (G i j) j q) := by
  have heq : (fun q : Vec3 × ℝ => ∑ j : Fin 3, CKN.spatialPartial (G i j) j q) =
      fun q => ∑ j : Fin 3, fderiv ℝ (fun p : Vec3 × ℝ => G i j p) q (CKN.basisVec j, 0) := by
    funext q
    exact Finset.sum_congr rfl fun j _ => spatialPartial_eq_fderiv_vecTime (hG i j) j q
  rw [heq]
  have hsum := HasCompactSupport.finset_sum (s := Finset.univ)
    (f := fun j (q : Vec3 × ℝ) => fderiv ℝ (fun p : Vec3 × ℝ => G i j p) q (CKN.basisVec j, 0))
    (fun j _ => (hGc i j).fderiv_apply (𝕜 := ℝ) _)
  convert hsum using 1
  funext q
  simp only [Finset.sum_apply]

/-- The forced heat response of a smooth compactly supported tensor is smooth
on `Vec3 × ℝ`. -/
theorem forcedHeat_contDiff {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => forcedHeat G z i) := by
  rw [forcedHeat_eq_causalHeatConv hG hGc]
  exact causalHeatConv_contDiff (tensorDivergence_contDiff hG i)
    (tensorDivergence_hasCompactSupport hG hGc i)

/-- The forced heat response of a tensor vanishing at nonpositive times is zero
at nonpositive times: the response has zero initial data. -/
theorem forcedHeat_eq_zero_of_nonpos {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hGpos : ∀ i j (p : ParabolicPoint), G i j p ≠ 0 → 0 < p.2)
    {z : ParabolicPoint} (hz : z.2 ≤ 0) : forcedHeat G z = 0 := by
  funext i
  have hzero : (fun p : ParabolicPoint => ∑ j : Fin 3,
      heatKernelSpaceDerivative p.1 p.2 j * G i j (z.1 - p.1, z.2 - p.2)) = fun _ => 0 := by
    funext p
    apply Finset.sum_eq_zero
    intro j _
    by_cases hp : 0 < p.2
    · have hG0 : G i j (z.1 - p.1, z.2 - p.2) = 0 := by
        by_contra hne
        have := hGpos i j _ hne
        change 0 < z.2 - p.2 at this
        linarith only [this, hz, hp]
      rw [hG0, mul_zero]
    · simp [heatKernelSpaceDerivative, hp]
  change (∫ p : ParabolicPoint, ∑ j : Fin 3,
      heatKernelSpaceDerivative p.1 p.2 j * G i j (z.1 - p.1, z.2 - p.2)) = 0
  rw [hzero, integral_zero]

end ESS

end
