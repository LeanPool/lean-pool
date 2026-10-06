/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.BackwardPotentialIdentity
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# The forward heat representation of a compactly supported test function

For a smooth, compactly supported `ζ : Vec3 × ℝ → ℝ`, the value `ζ (x, s)` is recovered from the
image of `ζ` under the forward heat operator `∂ₜ - Δ`, convolved against the causal heat kernel
run backward from `(x, s)`: `ζ (x, s) = ∫ Γ(x - z.1, s - z.2) (∂ₜζ - Δζ) z`. Since `heatKernel`
vanishes for a nonpositive second argument, the integral is effectively over the past
`{z | z.2 < s}`. This is the base case of the pointwise heat-potential bound used for the
interior estimates in the proof of `lem:aniso:annulus`.

The proof reduces to CKN's `backwardTestPotential_heat_equation` (which differentiates the
*potential* of a compactly supported source) applied to the time-reflection of `ζ`, combined with
the (heat-equation-free) fact that differentiation commutes with `backwardTestPotential`. This
converts CKN's "potential of a derivative recovers a delta-tested value" statement about the
future-integrating kernel into the forward, past-integrating representation stated here; no
uniqueness argument for the heat equation is used anywhere.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat CKN.Core.Step3

noncomputable section

namespace CIV



/-- Time-reflection of a space-time function. -/
@[expose] def reflectTime (ζ : ParabolicPoint → ℝ) : Vec3 × ℝ → ℝ := fun z => ζ (z.1, -z.2)

theorem contDiff_reflectTime {ζ : ParabolicPoint → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ζ z)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => reflectTime ζ z) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ((z.1, -z.2) : Vec3 × ℝ)) := by
    fun_prop
  exact hζ.comp hmap

theorem hasCompactSupport_reflectTime {ζ : ParabolicPoint → ℝ}
    (hζc : HasCompactSupport (fun z : Vec3 × ℝ => ζ z)) :
    HasCompactSupport (fun z : Vec3 × ℝ => reflectTime ζ z) := by
  have he : (fun z : Vec3 × ℝ => reflectTime ζ z) =
      (fun z : Vec3 × ℝ => ζ z) ∘
        ((Homeomorph.refl Vec3).prodCongr (Homeomorph.neg ℝ)) := by
    funext z
    rfl
  rw [he]
  exact hζc.comp_homeomorph _

theorem timePartial_reflectTime {ζ : ParabolicPoint → ℝ} (z : ParabolicPoint) :
    CKN.timePartial (reflectTime ζ) z = -(CKN.timePartial ζ (z.1, -z.2)) := by
  exact deriv_comp_neg (fun s' => ζ (z.1, s')) z.2

theorem spatialPartial_reflectTime {ζ : ParabolicPoint → ℝ} (i : Fin 3) (z : ParabolicPoint) :
    CKN.spatialPartial (reflectTime ζ) i z = CKN.spatialPartial ζ i (z.1, -z.2) := rfl

theorem spatialSecondPartial_reflectTime {ζ : ParabolicPoint → ℝ} (i j : Fin 3)
    (z : ParabolicPoint) :
    CKN.spatialSecondPartial (reflectTime ζ) i j z =
      CKN.spatialSecondPartial ζ i j (z.1, -z.2) := by
  have hcongr : (fun w : ParabolicPoint => CKN.spatialPartial (reflectTime ζ) i w) =
      reflectTime (CKN.spatialPartial ζ i) := by
    funext w
    exact spatialPartial_reflectTime i w
  show CKN.spatialPartial (fun w => CKN.spatialPartial (reflectTime ζ) i w) j z = _
  rw [hcongr]
  exact spatialPartial_reflectTime j z

private theorem heatKernel_neg_fst (y : Vec3) (t : ℝ) : heatKernel (-y) t = heatKernel y t := by
  by_cases ht : 0 < t
  · rw [heatKernel_eq_formula_sum ht, heatKernel_eq_formula_sum ht]
    congr 2
    simp only [Pi.neg_apply, neg_sq]
  · rw [heatKernel_eq_zero_of_nonpos (le_of_not_gt ht),
      heatKernel_eq_zero_of_nonpos (le_of_not_gt ht)]

/-- The map `t ↦ (x - t.1, t.2 - r)` is measure preserving on `Vec3 × ℝ`. -/
theorem measurePreserving_reflectShift (x : Vec3) (r : ℝ) :
    MeasurePreserving (fun t : Vec3 × ℝ => (x - t.1, t.2 - r))
      (volume : Measure (Vec3 × ℝ)) (volume : Measure (Vec3 × ℝ)) := by
  have h1 : MeasurePreserving (fun t : Vec3 => x - t) volume volume :=
    volume.measurePreserving_sub_left x
  have h2 : MeasurePreserving (fun t : ℝ => t - r) volume volume := by
    have h2' := measurePreserving_add_right volume (-r)
    simpa only [sub_eq_add_neg] using h2'
  have hprod := h1.prod h2
  rw [← MeasureTheory.Measure.volume_eq_prod] at hprod
  exact hprod

theorem measurableEmbedding_reflectShift (x : Vec3) (r : ℝ) :
    MeasurableEmbedding (fun t : Vec3 × ℝ => (x - t.1, t.2 - r)) := by
  have h1 : MeasurableEmbedding (fun t : Vec3 => x - t) := measurableEmbedding_subLeft x
  have h2 : MeasurableEmbedding (fun t : ℝ => t - r) := by
    have h2' := measurableEmbedding_addRight (-r)
    simpa only [sub_eq_add_neg] using h2'
  exact h1.prodMap h2

private theorem reflectTime_potential_integrand_eq (φ : ParabolicPoint → ℝ) (x : Vec3) (r : ℝ)
    (t : Vec3 × ℝ) :
    (ContinuousLinearMap.lsmul ℝ ℝ) (backwardTestKernel t) (reflectTime φ ((x, r) - t)) =
      heatKernel (-t.1) (-t.2) * φ (x - t.1, t.2 - r) := by
  have hbtk : backwardTestKernel t = heatKernel (-t.1) (-t.2) := by
    unfold backwardTestKernel
    rw [heatKernelPlus_eq_heatKernel]
    simp only [Prod.fst_neg, Prod.snd_neg]
  have hreflect : reflectTime φ ((x, r) - t) = φ (x - t.1, t.2 - r) := by
    simp only [reflectTime, Prod.fst_sub, Prod.snd_sub, neg_sub]
  rw [hbtk, hreflect]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

private theorem heatKernel_reflectShift_eq (x : Vec3) (r : ℝ) (t : Vec3 × ℝ) :
    heatKernel (x - (x - t.1)) (-r - (t.2 - r)) = heatKernel (-t.1) (-t.2) := by
  have h1 : x - (x - t.1) = t.1 := by abel
  have h2 : -r - (t.2 - r) = -t.2 := by ring
  rw [h1, h2, heatKernel_neg_fst]

theorem backwardTestPotential_reflectTime_eq (φ : ParabolicPoint → ℝ) (x : Vec3) (r : ℝ) :
    backwardTestPotential (reflectTime φ) (x, r) =
      ∫ z : Vec3 × ℝ, heatKernel (x - z.1) (-r - z.2) * φ z := by
  have hcd0 : backwardTestPotential (reflectTime φ) (x, r) =
      MeasureTheory.convolution backwardTestKernel (reflectTime φ)
        (ContinuousLinearMap.lsmul ℝ ℝ) backwardProductVolume (x, r) := rfl
  have hcd := hcd0.trans (MeasureTheory.convolution_def
    (f := backwardTestKernel) (g := reflectTime φ) (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := backwardProductVolume) (x := (x, r)))
  have hmeas : backwardProductVolume = (volume : Measure (Vec3 × ℝ)) := by
    unfold backwardProductVolume
    exact (MeasureTheory.Measure.volume_eq_prod Vec3 ℝ).symm
  have hunfold : backwardTestPotential (reflectTime φ) (x, r) =
      ∫ t : Vec3 × ℝ, heatKernel (-t.1) (-t.2) * φ (x - t.1, t.2 - r) := by
    rw [hcd, hmeas]
    exact integral_congr_ae
      (Filter.Eventually.of_forall (reflectTime_potential_integrand_eq φ x r))
  have hcomp := (measurePreserving_reflectShift x r).integral_comp
    (measurableEmbedding_reflectShift x r)
    (fun z : Vec3 × ℝ => heatKernel (x - z.1) (-r - z.2) * φ z)
  simp only at hcomp
  rw [hunfold, ← hcomp]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [heatKernel_reflectShift_eq]

theorem integrable_reflectTime_potential {φ : ParabolicPoint → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => φ z))
    (hφc : HasCompactSupport (fun z : Vec3 × ℝ => φ z)) (x : Vec3) (r : ℝ) :
    Integrable (fun z : Vec3 × ℝ => heatKernel (x - z.1) (-r - z.2) * φ z) := by
  have hexists : ConvolutionExists backwardTestKernel (reflectTime φ)
      (ContinuousLinearMap.lsmul ℝ ℝ) backwardProductVolume :=
    (hasCompactSupport_reflectTime hφc).convolutionExists_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) backwardTestKernel_locallyIntegrable
      (contDiff_reflectTime hφ).continuous
  have hint : Integrable (fun t : Vec3 × ℝ => (ContinuousLinearMap.lsmul ℝ ℝ)
      (backwardTestKernel t) (reflectTime φ ((x, r) - t))) backwardProductVolume :=
    (hexists (x, r)).integrable
  have hmeas : backwardProductVolume = (volume : Measure (Vec3 × ℝ)) := by
    unfold backwardProductVolume
    exact (MeasureTheory.Measure.volume_eq_prod Vec3 ℝ).symm
  rw [hmeas] at hint
  have hF : Integrable (fun t : Vec3 × ℝ => heatKernel (-t.1) (-t.2) * φ (x - t.1, t.2 - r)) :=
    hint.congr (Filter.Eventually.of_forall (reflectTime_potential_integrand_eq φ x r))
  have hiff := (measurePreserving_reflectShift x r).integrable_comp_emb
    (measurableEmbedding_reflectShift x r)
    (g := fun z : Vec3 × ℝ => heatKernel (x - z.1) (-r - z.2) * φ z)
  refine hiff.mp (hF.congr (Filter.Eventually.of_forall (fun t => ?_)))
  simp only [Function.comp_apply, heatKernel_reflectShift_eq]

theorem HB1_forward_representation {ζ : ParabolicPoint → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ζ z))
    (hζc : HasCompactSupport (fun z : Vec3 × ℝ => ζ z)) (x : Vec3) (s : ℝ) :
    ζ (x, s) = ∫ z : ParabolicPoint, heatKernel (x - z.1) (s - z.2) *
      (timePartial ζ z - ∑ i, spatialSecondPartial ζ i i z) := by
  have hη : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => reflectTime ζ z) := contDiff_reflectTime hζ
  have hηc : HasCompactSupport (fun z : Vec3 × ℝ => reflectTime ζ z) :=
    hasCompactSupport_reflectTime hζc
  have hmain := backwardTestPotential_heat_equation hη hηc x (-s)
  rw [backwardTestPotential_timePartial hη hηc x (-s)] at hmain
  simp_rw [backwardTestPotential_spatialSecondPartial hη hηc] at hmain
  have heq1 : (fun z : Vec3 × ℝ => CKN.timePartial (reflectTime ζ) z) =
      reflectTime (fun w => -(CKN.timePartial ζ w)) := by
    funext z; exact timePartial_reflectTime z
  have heq2 : ∀ i : Fin 3,
      (fun z : Vec3 × ℝ => CKN.spatialSecondPartial (reflectTime ζ) i i z) =
        reflectTime (CKN.spatialSecondPartial ζ i i) := by
    intro i; funext z; exact spatialSecondPartial_reflectTime i i z
  rw [heq1] at hmain
  simp_rw [heq2] at hmain
  rw [backwardTestPotential_reflectTime_eq] at hmain
  simp_rw [backwardTestPotential_reflectTime_eq] at hmain
  have hreflectζ : reflectTime ζ (x, -s) = ζ (x, s) := by
    simp only [reflectTime, neg_neg]
  rw [hreflectζ] at hmain
  have hnegs : -(-s) = s := neg_neg s
  simp only [hnegs] at hmain
  -- `hmain` now reads:
  -- `-∫ z, K z * (-(timePartial ζ z)) - ∑ i, ∫ z, K z * spatialSecondPartial ζ i i z = ζ (x, s)`
  have htimeCD : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => CKN.timePartial ζ z) :=
    timePartial_contDiff_full hζ
  have htimeCS : HasCompactSupport (fun z : Vec3 × ℝ => CKN.timePartial ζ z) := by
    rw [show (fun z : Vec3 × ℝ => CKN.timePartial ζ z) =
        (fun z : Vec3 × ℝ => (fderiv ℝ (fun w : Vec3 × ℝ => ζ w) z) ((0, 1) : Vec3 × ℝ)) from
      funext (fun z => timePartial_eq_fderiv_apply hζ z.1 z.2)]
    exact hζc.fderiv_apply (𝕜 := ℝ) ((0, 1) : Vec3 × ℝ)
  have hsecondCS : ∀ i : Fin 3,
      HasCompactSupport (fun z : Vec3 × ℝ => CKN.spatialSecondPartial ζ i i z) := by
    intro i
    have hηCS : HasCompactSupport (fun z : Vec3 × ℝ => CKN.spatialPartial ζ i z) := by
      rw [show (fun z : Vec3 × ℝ => CKN.spatialPartial ζ i z) =
          (fun z : Vec3 × ℝ =>
            (fderiv ℝ (fun w : Vec3 × ℝ => ζ w) z) ((CKN.basisVec i, 0) : Vec3 × ℝ)) from
        funext (fun z => spatialPartial_eq_fderiv_apply hζ i z.1 z.2)]
      exact hζc.fderiv_apply (𝕜 := ℝ) ((CKN.basisVec i, 0) : Vec3 × ℝ)
    rw [show (fun z : Vec3 × ℝ => CKN.spatialSecondPartial ζ i i z) =
        (fun z : Vec3 × ℝ =>
          (fderiv ℝ (fun w : Vec3 × ℝ => CKN.spatialPartial ζ i w) z)
            ((CKN.basisVec i, 0) : Vec3 × ℝ)) from
      funext (fun z => spatialPartial_eq_fderiv_apply (spatialPartial_contDiff hζ i) i z.1 z.2)]
    exact hηCS.fderiv_apply (𝕜 := ℝ) ((CKN.basisVec i, 0) : Vec3 × ℝ)
  have hintTime : Integrable (fun z : Vec3 × ℝ => heatKernel (x - z.1) (s - z.2) *
      CKN.timePartial ζ z) := by
    have h := integrable_reflectTime_potential (φ := CKN.timePartial ζ) htimeCD htimeCS x (-s)
    simpa only [hnegs] using h
  have hintSecond : ∀ i : Fin 3, Integrable (fun z : Vec3 × ℝ => heatKernel (x - z.1) (s - z.2) *
      CKN.spatialSecondPartial ζ i i z) := by
    intro i
    have h := integrable_reflectTime_potential (φ := CKN.spatialSecondPartial ζ i i)
      (spatialSecondPartial_contDiff_full hζ i i) (hsecondCS i) x (-s)
    simpa only [hnegs] using h
  have hintSum : Integrable (fun z : Vec3 × ℝ => heatKernel (x - z.1) (s - z.2) *
      ∑ i : Fin 3, CKN.spatialSecondPartial ζ i i z) := by
    have hraw := integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (fun i (_ : i ∈ Finset.univ) => hintSecond i)
    refine hraw.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Finset.mul_sum]
  have hsumSwap : ∑ i : Fin 3, ∫ z : Vec3 × ℝ, heatKernel (x - z.1) (s - z.2) *
      CKN.spatialSecondPartial ζ i i z =
        ∫ z : Vec3 × ℝ, heatKernel (x - z.1) (s - z.2) *
          ∑ i : Fin 3, CKN.spatialSecondPartial ζ i i z := by
    rw [← integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hintSecond i)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Finset.mul_sum]
  have hcombine :
      (-∫ z : Vec3 × ℝ, heatKernel (x - z.1) (s - z.2) * (-(CKN.timePartial ζ z))) -
        ∑ i : Fin 3, ∫ z : Vec3 × ℝ, heatKernel (x - z.1) (s - z.2) *
          CKN.spatialSecondPartial ζ i i z =
      ∫ z : Vec3 × ℝ, heatKernel (x - z.1) (s - z.2) *
        (CKN.timePartial ζ z - ∑ i : Fin 3, CKN.spatialSecondPartial ζ i i z) := by
    rw [hsumSwap]
    have hneg1 : (-∫ z : Vec3 × ℝ, heatKernel (x - z.1) (s - z.2) * (-(CKN.timePartial ζ z))) =
        ∫ z : Vec3 × ℝ, heatKernel (x - z.1) (s - z.2) * CKN.timePartial ζ z := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      ring
    rw [hneg1, ← integral_sub hintTime hintSum]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    ring
  rw [hcombine] at hmain
  exact hmain.symm

end CIV
