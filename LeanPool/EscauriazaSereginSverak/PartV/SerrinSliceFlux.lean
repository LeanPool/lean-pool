/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSpaceTimeMollify
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative.ProductH1
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.SmoothIBP

/-!
# Mollified fluxes at a fixed time

At a fixed time the tested momentum flux of a mollified component is rewritten
with the weak product rule, the weak-gradient transport through mollification
and integrations by parts in the mollification variable. The result expresses
the cross-testing integrand of `lem:pv-serrin-uniqueness` through mollified
velocities, gradients, convection terms and pressures.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval Convolution
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The spatial derivative of a mollification is the integral against the
differentiated kernel. -/
theorem serrin_mollify_spatialDeriv {f : Vec3 → ℝ} (hf : LocallyIntegrable f volume)
    {ε : ℝ} (hε : 0 < ε) (j : Fin 3) (y : Vec3) :
    spatialDeriv (CKN.mollify f ε hε) j y =
      ∫ x : Vec3, f x * spatialDeriv (CKN.mollifier (d := 3) ε hε) j (y - x) := by
  have hfd := (CKN.mollifier_hasCompactSupport (d := 3) hε).hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (CKN.mollifier_contDiff hε (n := 1)) hf y
  have hderiv : fderiv ℝ (CKN.mollify f ε hε) y =
      (MeasureTheory.convolution (fderiv ℝ (CKN.mollifier (d := 3) ε hε)) f
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec 3)) volume) y := by
    simpa [CKN.mollify] using hfd.fderiv
  have hconv : ConvolutionExists (fderiv ℝ (CKN.mollifier (d := 3) ε hε)) f
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec 3)) volume :=
    HasCompactSupport.convolutionExists_left
      (𝕜 := ℝ) (G := Vec 3) (E := Vec 3 →L[ℝ] ℝ) (E' := ℝ) (F := Vec 3 →L[ℝ] ℝ)
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec 3))
      ((CKN.mollifier_hasCompactSupport (d := 3) hε).fderiv (𝕜 := ℝ))
      ((CKN.mollifier_contDiff (d := 3) hε (n := 2)).continuous_fderiv (by simp)) hf
  unfold spatialDeriv
  rw [hderiv]
  simp only [MeasureTheory.convolution]
  rw [ContinuousLinearMap.integral_apply (hconv y) (basisVec j)]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  change (∫ t, (fderiv ℝ (CKN.mollifier (d := 3) ε hε) t) (basisVec j) * f (y - t)) = _
  have h := integral_sub_left_eq_self
    (fun t : Vec3 => (fderiv ℝ (CKN.mollifier (d := 3) ε hε) (y - t)) (basisVec j) *
      f (y - (y - t))) (μ := (volume : Measure Vec3)) y
  simp only [sub_sub_cancel] at h
  rw [h]
  congr 1
  funext x
  ring

/-- The mollification of an almost everywhere vanishing function vanishes. -/
theorem serrin_mollify_of_ae_zero {f : Vec3 → ℝ} (hf : f =ᵐ[volume] 0)
    {ε : ℝ} (hε : 0 < ε) (y : Vec3) : CKN.mollify f ε hε y = 0 := by
  rw [serrin_mollify_eq_integral]
  have h : (fun x => f x * CKN.mollifier (d := 3) ε hε (y - x)) =ᵐ[volume] 0 := by
    filter_upwards [hf] with x hx
    simp [hx]
  rw [integral_congr_ae h]
  simp

/-- The convection part of a tested flux, rewritten with the weak product rule
and the divergence condition. -/
theorem serrin_slice_convection {w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    (hw2 : MemLp w 2 volume) (hDw2 : MemLp Dw 2 volume)
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => w x i) (fun x => Dw x i))
    (htr : ∀ᵐ x ∂volume, ∑ j : Fin 3, Dw x j j = 0)
    {ρ : Vec3 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (k : Fin 3) (y : Vec3) :
    (∑ j : Fin 3, ∫ x : Vec3, w x k * w x j * spatialDeriv ρ j (y - x)) =
      ∫ x : Vec3, (∑ j : Fin 3, w x j * Dw x k j) * ρ (y - x) := by
  let φ : Vec3 → ℝ := fun x => ρ (y - x)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hρ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := by
    have h := hρc.comp_homeomorph (Homeomorph.subLeft y)
    exact h
  obtain ⟨Cφ, hCφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have hwi (i : Fin 3) : MemLp (fun x => w x i) 2 (volume.restrict (Set.univ : Set Vec3)) := by
    rw [Measure.restrict_univ]
    exact hw2.eval i
  have hDwi (i j : Fin 3) : MemLp (fun x => Dw x i j) 2
      (volume.restrict (Set.univ : Set Vec3)) := by
    rw [Measure.restrict_univ]
    exact (hDw2.eval i).eval j
  have hprodInt (i j l m : Fin 3) :
      Integrable (fun x => Dw x i j * w x l * φ x) volume := by
    have h1 : Integrable (fun x => Dw x i j * w x l) volume :=
      ((hDw2.eval i).eval j).integrable_mul (hw2.eval l)
    exact h1.mul_bdd hφ.continuous.aestronglyMeasurable (Eventually.of_forall hCφ)
  have hterm (j : Fin 3) : (∫ x : Vec3, w x k * w x j * spatialDeriv ρ j (y - x)) =
      ∫ x : Vec3, (Dw x k j * w x j + w x k * Dw x j j) * φ x := by
    have hprod := CKN.HasWeakGradientOn.mul_of_memLp_two isOpen_univ (hwi k) (hwi j)
      (fun m => hDwi k m) (fun m => hDwi j m) (hgrad k) (hgrad j)
    have hweak := hprod j φ hφ hφc (Set.subset_univ _)
    simp only [Measure.restrict_univ] at hweak
    have hderφ (x : Vec3) : (fderiv ℝ φ x) (basisVec j) = -spatialDeriv ρ j (y - x) :=
      spatialDeriv_reflect hρ y j x
    simp only [hderφ] at hweak
    have hneg : (∫ x : Vec3, w x k * w x j * spatialDeriv ρ j (y - x)) =
        -∫ x : Vec3, w x k * w x j * -spatialDeriv ρ j (y - x) := by
      rw [← integral_neg]
      congr 1
      funext x
      ring
    rw [hneg, hweak, neg_neg]
  simp_rw [hterm]
  have hsumInt (j : Fin 3) : Integrable
      (fun x => (Dw x k j * w x j + w x k * Dw x j j) * φ x) volume := by
    have h2 : Integrable (fun x => w x k * Dw x j j * φ x) volume := by
      have h1 : Integrable (fun x => w x k * Dw x j j) volume :=
        (hw2.eval k).integrable_mul ((hDw2.eval j).eval j)
      exact h1.mul_bdd hφ.continuous.aestronglyMeasurable (Eventually.of_forall hCφ)
    refine ((hprodInt k j j j).add h2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← integral_finsetSum _ fun j _ => hsumInt j]
  apply integral_congr_ae
  filter_upwards [htr] with x hx
  have hsplit : (∑ j : Fin 3, (Dw x k j * w x j + w x k * Dw x j j) * φ x) =
      (∑ j : Fin 3, w x j * Dw x k j) * φ x + w x k * (∑ j : Fin 3, Dw x j j) * φ x := by
    simp only [Fin.sum_univ_three]
    ring
  rw [hsplit, hx]
  simp [φ]

private theorem serrin_spatialDeriv_mul {f g : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : Fin 3) (y : Vec3) :
    spatialDeriv (fun x => f x * g x) j y =
      spatialDeriv f j y * g y + f y * spatialDeriv g j y := by
  have hfd := ((hf.differentiable (by simp)) y).hasFDerivAt
  have hgd := ((hg.differentiable (by simp)) y).hasFDerivAt
  have h := (hfd.mul hgd).fderiv
  change (fderiv ℝ (f * g) y) (basisVec j) = _
  rw [h]
  simp only [add_apply, smul_apply, smul_eq_mul, spatialDeriv]
  ring

private theorem serrin_contDiff_spatialDeriv {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f j) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  exact h.clm_apply contDiff_const

private theorem serrin_hasCompactSupport_spatialDeriv {f : Vec3 → ℝ}
    (hfc : HasCompactSupport f) (j : Fin 3) : HasCompactSupport (spatialDeriv f j) :=
  hfc.fderiv_apply (𝕜 := ℝ) (basisVec j)

/-- The tested flux of a mollified component, integrated in the mollification
point: convection, diffusion and pressure contributions. -/
theorem serrin_slice_flux_integral (n : ℕ) {w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    {pw : Vec3 → ℝ}
    (hw2 : MemLp w 2 volume) (hDw2 : MemLp Dw 2 volume)
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => w x i) (fun x => Dw x i))
    (htr : ∀ᵐ x ∂volume, ∑ j : Fin 3, Dw x j j = 0)
    (hpw : LocallyIntegrable pw volume) (k : Fin 3) (y : Vec3) :
    (∫ x : Vec3, (-(∑ j : Fin 3, w x k * w x j * spatialDeriv (serrinKernel n) j (y - x))
        + (∑ j : Fin 3, Dw x k j * spatialDeriv (serrinKernel n) j (y - x))
        - pw x * spatialDeriv (serrinKernel n) k (y - x))) =
      -CKN.mollify (fun x => ∑ j : Fin 3, w x j * Dw x k j) (serrinRadius n)
          (serrinRadius_pos n) y
        + (∑ j : Fin 3, spatialDeriv (CKN.mollify (fun x => Dw x k j) (serrinRadius n)
            (serrinRadius_pos n)) j y)
        - spatialDeriv (CKN.mollify pw (serrinRadius n) (serrinRadius_pos n)) k y := by
  set ρ := serrinKernel n with hρdef
  have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := CKN.mollifier_contDiff (d := 3) (serrinRadius_pos n)
  have hρc : HasCompactSupport ρ := CKN.mollifier_hasCompactSupport (d := 3) (serrinRadius_pos n)
  have hdρ (j : Fin 3) : Continuous (fun x : Vec3 => spatialDeriv ρ j (y - x)) :=
    (serrin_contDiff_spatialDeriv hρ j).continuous.comp (continuous_const.sub continuous_id)
  have hdρc (j : Fin 3) : HasCompactSupport (fun x : Vec3 => spatialDeriv ρ j (y - x)) := by
    have h := (serrin_hasCompactSupport_spatialDeriv hρc j).comp_homeomorph
      (Homeomorph.subLeft y)
    exact h
  have hbd (j : Fin 3) : ∃ C, ∀ x : Vec3, ‖spatialDeriv ρ j (y - x)‖ ≤ C :=
    (hdρc j).exists_bound_of_continuous (hdρ j)
  have hA (j : Fin 3) : Integrable (fun x => w x k * w x j * spatialDeriv ρ j (y - x)) volume := by
    obtain ⟨C, hC⟩ := hbd j
    exact ((hw2.eval k).integrable_mul (hw2.eval j)).mul_bdd (hdρ j).aestronglyMeasurable
      (Eventually.of_forall hC)
  have hB (j : Fin 3) : Integrable (fun x => Dw x k j * spatialDeriv ρ j (y - x)) volume := by
    have h2 : MemLp (fun x : Vec3 => spatialDeriv ρ j (y - x)) 2 volume :=
      (hdρ j).memLp_of_hasCompactSupport (hdρc j)
    exact ((hDw2.eval k).eval j).integrable_mul h2
  have hC : Integrable (fun x => pw x * spatialDeriv ρ k (y - x)) volume := by
    have h := hpw.integrable_smul_right_of_hasCompactSupport (hdρ k) (hdρc k)
    simpa only [smul_eq_mul] using h
  have hAs : Integrable (fun x => ∑ j : Fin 3, w x k * w x j * spatialDeriv ρ j (y - x))
      volume := integrable_finsetSum _ fun j _ => hA j
  have hBs : Integrable (fun x => ∑ j : Fin 3, Dw x k j * spatialDeriv ρ j (y - x))
      volume := integrable_finsetSum _ fun j _ => hB j
  have hnegA : Integrable
      (fun x => -(∑ j : Fin 3, w x k * w x j * spatialDeriv ρ j (y - x))) volume := hAs.neg
  have hAB : Integrable (fun x => -(∑ j : Fin 3, w x k * w x j * spatialDeriv ρ j (y - x)) +
      ∑ j : Fin 3, Dw x k j * spatialDeriv ρ j (y - x)) volume := hnegA.add hBs
  rw [integral_sub hAB hC, integral_add hnegA hBs, integral_neg,
    integral_finsetSum _ fun j _ => hA j, integral_finsetSum _ fun j _ => hB j]
  have hconv := serrin_slice_convection hw2 hDw2 hgrad htr hρ hρc k y
  rw [hconv]
  have hN : (∫ x : Vec3, (∑ j : Fin 3, w x j * Dw x k j) * ρ (y - x)) =
      CKN.mollify (fun x => ∑ j : Fin 3, w x j * Dw x k j) (serrinRadius n)
        (serrinRadius_pos n) y :=
    (serrin_mollify_eq_integral _ _ y).symm
  have hDer (j : Fin 3) : (∫ x : Vec3, Dw x k j * spatialDeriv ρ j (y - x)) =
      spatialDeriv (CKN.mollify (fun x => Dw x k j) (serrinRadius n)
        (serrinRadius_pos n)) j y :=
    (serrin_mollify_spatialDeriv (((hDw2.eval k).eval j).locallyIntegrable (by norm_num))
      (serrinRadius_pos n) j y).symm
  have hP : (∫ x : Vec3, pw x * spatialDeriv ρ k (y - x)) =
      spatialDeriv (CKN.mollify pw (serrinRadius n) (serrinRadius_pos n)) k y :=
    (serrin_mollify_spatialDeriv hpw (serrinRadius_pos n) k y).symm
  rw [hN, hP]
  simp_rw [hDer]

private theorem serrin_integral_spatialDeriv_eq_zero {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) (j : Fin 3) :
    ∫ y : Vec3, spatialDeriv F j y = 0 := by
  have h := CKN.integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
    (u := fun _ : Vec3 => (1 : ℝ)) contDiff_const hF hFc j
  have hzero : spatialDeriv (fun _ : Vec3 => (1 : ℝ)) j = fun _ => 0 := by
    funext y
    simp [spatialDeriv]
  simpa [hzero] using h

/-- The cutoff-weighted pairing of the tested fluxes of one field with the
mollified components of another, at a fixed time, in integrated-by-parts form. -/
theorem serrin_slice_flux_pairing (n : ℕ) {w z : Vec3 → Vec3} {Dw Dz : Vec3 → Fin 3 → Vec3}
    {pw : Vec3 → ℝ}
    (hw2 : MemLp w 2 volume) (hDw2 : MemLp Dw 2 volume)
    (hwgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => w x i) (fun x => Dw x i))
    (hwtr : ∀ᵐ x ∂volume, ∑ j : Fin 3, Dw x j j = 0)
    (hpw : LocallyIntegrable pw volume)
    (hz2 : MemLp z 2 volume) (hDz2 : MemLp Dz 2 volume)
    (hzgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => z x i) (fun x => Dz x i))
    (hztr : ∀ᵐ x ∂volume, ∑ j : Fin 3, Dz x j j = 0)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    (∫ y : Vec3, η y * ∑ k : Fin 3,
      (∫ x : Vec3, (-(∑ j : Fin 3, w x k * w x j * spatialDeriv (serrinKernel n) j (y - x))
        + (∑ j : Fin 3, Dw x k j * spatialDeriv (serrinKernel n) j (y - x))
        - pw x * spatialDeriv (serrinKernel n) k (y - x))) *
      (∫ x : Vec3, z x k * serrinKernel n (y - x))) =
    ∫ y : Vec3,
      (-(η y * ∑ k : Fin 3,
          CKN.mollify (fun x => z x k) (serrinRadius n) (serrinRadius_pos n) y *
          CKN.mollify (fun x => ∑ j : Fin 3, w x j * Dw x k j) (serrinRadius n)
            (serrinRadius_pos n) y)
        - η y * ∑ k : Fin 3, ∑ j : Fin 3,
          CKN.mollify (fun x => Dz x k j) (serrinRadius n) (serrinRadius_pos n) y *
          CKN.mollify (fun x => Dw x k j) (serrinRadius n) (serrinRadius_pos n) y
        - ∑ k : Fin 3, ∑ j : Fin 3, spatialDeriv η j y *
          CKN.mollify (fun x => z x k) (serrinRadius n) (serrinRadius_pos n) y *
          CKN.mollify (fun x => Dw x k j) (serrinRadius n) (serrinRadius_pos n) y
        + ∑ k : Fin 3, spatialDeriv η k y *
          CKN.mollify (fun x => z x k) (serrinRadius n) (serrinRadius_pos n) y *
          CKN.mollify pw (serrinRadius n) (serrinRadius_pos n) y) := by
  set ε := serrinRadius n
  have hε := serrinRadius_pos n
  let M : (Vec3 → ℝ) → Vec3 → ℝ := fun f => CKN.mollify f ε hε
  have hMs {f : Vec3 → ℝ} (hf : LocallyIntegrable f volume) :
      ContDiff ℝ (⊤ : ℕ∞) (M f) := CKN.mollify_contDiff hε hf
  have hzl (k : Fin 3) : LocallyIntegrable (fun x => z x k) volume :=
    (hz2.eval k).locallyIntegrable (by norm_num)
  have hDzl (k j : Fin 3) : LocallyIntegrable (fun x => Dz x k j) volume :=
    ((hDz2.eval k).eval j).locallyIntegrable (by norm_num)
  have hDwl (k j : Fin 3) : LocallyIntegrable (fun x => Dw x k j) volume :=
    ((hDw2.eval k).eval j).locallyIntegrable (by norm_num)
  have hNl (k : Fin 3) : LocallyIntegrable (fun x => ∑ j : Fin 3, w x j * Dw x k j) volume :=
    (integrable_finsetSum _ fun j _ =>
      (hw2.eval j).integrable_mul ((hDw2.eval k).eval j)).locallyIntegrable
  -- transport of the weak gradient of `z` through the mollifier
  have htrans (k j : Fin 3) (y : Vec3) : spatialDeriv (M fun x => z x k) j y =
      M (fun x => Dz x k j) y :=
    CKN.fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ (hzl k) (hDzl k j)
      (hzgrad k j) hε (Set.subset_univ _)
  have htrace (y : Vec3) : (∑ k : Fin 3, M (fun x => Dz x k k) y) = 0 := by
    have hsum : (∑ k : Fin 3, M (fun x => Dz x k k) y) =
        M (fun x => ∑ k : Fin 3, Dz x k k) y := by
      simp only [M, serrin_mollify_eq_integral]
      rw [← integral_finsetSum]
      · congr 1
        funext x
        rw [Finset.sum_mul]
      · intro k _
        exact (hDzl k k).integrable_smul_right_of_hasCompactSupport
          ((CKN.mollifier_contDiff (d := 3) hε (n := 0)).continuous.comp
            (continuous_const.sub continuous_id))
          (by
            have h := (CKN.mollifier_hasCompactSupport (d := 3) hε).comp_homeomorph
              (Homeomorph.subLeft y)
            exact h) |>.congr (Eventually.of_forall fun x => rfl)
    rw [hsum]
    exact serrin_mollify_of_ae_zero hztr hε y
  -- rewrite the inner integrals
  have hinner (k : Fin 3) (y : Vec3) :
      (∫ x : Vec3, (-(∑ j : Fin 3, w x k * w x j * spatialDeriv (serrinKernel n) j (y - x))
        + (∑ j : Fin 3, Dw x k j * spatialDeriv (serrinKernel n) j (y - x))
        - pw x * spatialDeriv (serrinKernel n) k (y - x))) *
      (∫ x : Vec3, z x k * serrinKernel n (y - x)) =
      (-M (fun x => ∑ j : Fin 3, w x j * Dw x k j) y
        + (∑ j : Fin 3, spatialDeriv (M fun x => Dw x k j) j y)
        - spatialDeriv (M pw) k y) * M (fun x => z x k) y := by
    rw [serrin_slice_flux_integral n hw2 hDw2 hwgrad hwtr hpw k y]
    congr 1
    exact (serrin_mollify_eq_integral _ hε y).symm
  simp_rw [hinner]
  -- smoothness of the mollified fields
  have hMz (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (M fun x => z x k) := hMs (hzl k)
  have hMDz (k j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (M fun x => Dz x k j) := hMs (hDzl k j)
  have hMDw (k j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (M fun x => Dw x k j) := hMs (hDwl k j)
  have hMN (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (M fun x => ∑ j : Fin 3, w x j * Dw x k j) :=
    hMs (hNl k)
  have hMp : ContDiff ℝ (⊤ : ℕ∞) (M pw) := hMs hpw
  have hdη (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η j) :=
    serrin_contDiff_spatialDeriv hη j
  have hdηc (j : Fin 3) : HasCompactSupport (spatialDeriv η j) :=
    serrin_hasCompactSupport_spatialDeriv hηc j
  let F : Fin 3 → Fin 3 → Vec3 → ℝ := fun k j y =>
    η y * (M (fun x => z x k) y * M (fun x => Dw x k j) y)
  let G : Fin 3 → Vec3 → ℝ := fun k y => η y * (M (fun x => z x k) y * M pw y)
  have hF (k j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (F k j) := hη.mul ((hMz k).mul (hMDw k j))
  have hFc (k j : Fin 3) : HasCompactSupport (F k j) := hηc.mul_right
  have hG (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (G k) := hη.mul ((hMz k).mul hMp)
  have hGc (k : Fin 3) : HasCompactSupport (G k) := hηc.mul_right
  have hdF (k j : Fin 3) (y : Vec3) : spatialDeriv (F k j) j y =
      spatialDeriv η j y * (M (fun x => z x k) y * M (fun x => Dw x k j) y) +
      η y * (M (fun x => Dz x k j) y * M (fun x => Dw x k j) y +
        M (fun x => z x k) y * spatialDeriv (M fun x => Dw x k j) j y) := by
    have h1 := serrin_spatialDeriv_mul hη ((hMz k).mul (hMDw k j)) j y
    have h2 := serrin_spatialDeriv_mul (hMz k) (hMDw k j) j y
    simp only [F]
    rw [h1, h2, htrans]
  have hdG (k : Fin 3) (y : Vec3) : spatialDeriv (G k) k y =
      spatialDeriv η k y * (M (fun x => z x k) y * M pw y) +
      η y * (M (fun x => Dz x k k) y * M pw y +
        M (fun x => z x k) y * spatialDeriv (M pw) k y) := by
    have h1 := serrin_spatialDeriv_mul hη ((hMz k).mul hMp) k y
    have h2 := serrin_spatialDeriv_mul (hMz k) hMp k y
    simp only [G]
    rw [h1, h2, htrans]
  -- the pointwise identity
  set R : Vec3 → ℝ := fun y =>
      (-(η y * ∑ k : Fin 3,
          M (fun x => z x k) y * M (fun x => ∑ j : Fin 3, w x j * Dw x k j) y)
        - η y * ∑ k : Fin 3, ∑ j : Fin 3,
          M (fun x => Dz x k j) y * M (fun x => Dw x k j) y
        - ∑ k : Fin 3, ∑ j : Fin 3, spatialDeriv η j y *
          M (fun x => z x k) y * M (fun x => Dw x k j) y
        + ∑ k : Fin 3, spatialDeriv η k y * M (fun x => z x k) y * M pw y) with hRdef
  have hpt (y : Vec3) :
      η y * ∑ k : Fin 3, (-M (fun x => ∑ j : Fin 3, w x j * Dw x k j) y
        + (∑ j : Fin 3, spatialDeriv (M fun x => Dw x k j) j y)
        - spatialDeriv (M pw) k y) * M (fun x => z x k) y =
      R y + (∑ k : Fin 3, ∑ j : Fin 3, spatialDeriv (F k j) j y)
        - ∑ k : Fin 3, spatialDeriv (G k) k y := by
    have htr := htrace y
    simp only [Fin.sum_univ_three] at htr
    simp only [hdF, hdG, hRdef, Fin.sum_univ_three]
    linear_combination (η y * M pw y) * htr
  have hRint : Integrable R volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · simp only [hRdef]
      have hA : Continuous (fun y => ∑ k : Fin 3,
          M (fun x => z x k) y * M (fun x => ∑ j : Fin 3, w x j * Dw x k j) y) :=
        continuous_finsetSum _ fun k _ => (hMz k).continuous.mul (hMN k).continuous
      have hB : Continuous (fun y => ∑ k : Fin 3, ∑ j : Fin 3,
          M (fun x => Dz x k j) y * M (fun x => Dw x k j) y) :=
        continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun j _ =>
          (hMDz k j).continuous.mul (hMDw k j).continuous
      have hC : Continuous (fun y => ∑ k : Fin 3, ∑ j : Fin 3,
          spatialDeriv η j y * M (fun x => z x k) y * M (fun x => Dw x k j) y) :=
        continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun j _ =>
          ((hdη j).continuous.mul (hMz k).continuous).mul (hMDw k j).continuous
      have hD : Continuous (fun y => ∑ k : Fin 3,
          spatialDeriv η k y * M (fun x => z x k) y * M pw y) :=
        continuous_finsetSum _ fun k _ =>
          ((hdη k).continuous.mul (hMz k).continuous).mul hMp.continuous
      exact (((hη.continuous.mul hA).neg).sub (hη.continuous.mul hB)).sub hC |>.add hD
    · refine HasCompactSupport.intro hηc.isCompact fun y hy => ?_
      have hη0 : η y = 0 := image_eq_zero_of_notMem_tsupport hy
      have hdη0 (j : Fin 3) : spatialDeriv η j y = 0 :=
        serrin_spatialDeriv_eq_zero_of_not_mem_tsupport hy j
      simp [hRdef, hη0, hdη0]
  have hDF (k j : Fin 3) : Integrable (spatialDeriv (F k j) j) volume :=
    (serrin_contDiff_spatialDeriv (hF k j) j).continuous.integrable_of_hasCompactSupport
      (serrin_hasCompactSupport_spatialDeriv (hFc k j) j)
  have hDG (k : Fin 3) : Integrable (spatialDeriv (G k) k) volume :=
    (serrin_contDiff_spatialDeriv (hG k) k).continuous.integrable_of_hasCompactSupport
      (serrin_hasCompactSupport_spatialDeriv (hGc k) k)
  have hD1 : Integrable (fun y => ∑ k : Fin 3, ∑ j : Fin 3, spatialDeriv (F k j) j y) volume :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hDF k j
  have hD2 : Integrable (fun y => ∑ k : Fin 3, spatialDeriv (G k) k y) volume :=
    integrable_finsetSum _ fun k _ => hDG k
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  have hsplit : (∫ y : Vec3, R y + (∑ k : Fin 3, ∑ j : Fin 3, spatialDeriv (F k j) j y)
      - ∑ k : Fin 3, spatialDeriv (G k) k y) =
      (∫ y : Vec3, R y) + (∫ y : Vec3, ∑ k : Fin 3, ∑ j : Fin 3, spatialDeriv (F k j) j y)
        - ∫ y : Vec3, ∑ k : Fin 3, spatialDeriv (G k) k y := by
    have hRD1 : Integrable
        (fun y => R y + ∑ k : Fin 3, ∑ j : Fin 3, spatialDeriv (F k j) j y) volume :=
      hRint.add hD1
    rw [integral_sub hRD1 hD2, integral_add hRint hD1]
  rw [hsplit, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hDF k j,
    integral_finsetSum _ fun k _ => hDG k]
  simp only [integral_finsetSum _ fun j _ => hDF _ j,
    serrin_integral_spatialDeriv_eq_zero (hF _ _) (hFc _ _),
    serrin_integral_spatialDeriv_eq_zero (hG _) (hGc _), Finset.sum_const_zero,
    add_zero, sub_zero]

end ESS
