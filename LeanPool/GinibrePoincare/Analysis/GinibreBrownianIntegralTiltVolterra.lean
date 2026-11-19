/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltVolterra.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInteractionTilt
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalCausality
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltPathLaw

/-!
# Ginibre Brownian integral tilt volterra

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownianEmbeddingCLM_apply`, `ginibreOUPath_corrected_canonical_prefix`,
`ginibreInteractionCorrectedBrownian_noise_continuous`,
`ginibreOUPath_correctedBrownian_original_volterra`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The interaction tilt assembled into a configuration: coordinate `j` is
`√(2α/n²) • (θ (j, 0) + I * θ (j, 1))` with `θ = ginibreInteractionBrownianTilt n α z`. -/
def ginibreInteractionConfigurationTilt (n : ℕ) (α : ℝ) (z : Configuration n) : Configuration n :=
  fun j => Real.sqrt (2*α/(n : ℝ)^2) •
    ((ginibreInteractionBrownianTilt n α z (j, 0) : ℂ)+
      Complex.I*(ginibreInteractionBrownianTilt n α z (j, 1) : ℂ))

/-- The continuous linear map sending real coordinates `x` to the configuration whose
coordinate `j` is `√(2α/n²) • (x (j, 0) + I * x (j, 1))`. -/
def ginibreBrownianEmbeddingCLM (n : ℕ) (α : ℝ) :
    ((Fin n × Fin 2) → ℝ) →L[ℝ] Configuration n :=
  ContinuousLinearMap.pi fun j => Real.sqrt (2*α/(n : ℝ)^2) •
    ((Complex.ofRealCLM.comp (ContinuousLinearMap.proj (j, 0)))+
      Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (j, 1))))

@[simp] theorem ginibreBrownianEmbeddingCLM_apply (n : ℕ) (α : ℝ)
    (v : (Fin n × Fin 2) → ℝ) (j : Fin n) :
    ginibreBrownianEmbeddingCLM n α v j = Real.sqrt (2*α/(n : ℝ)^2) •
      ((v (j, 0) : ℂ)+Complex.I*(v (j, 1) : ℂ)) := by
  simp [ginibreBrownianEmbeddingCLM, smul_eq_mul]

/-- The actual Brownian interaction tilt changes the stationary OU drift
into precisely the original paper-normalized Ginibre Langevin drift. -/
theorem ginibreInteractionConfigurationTilt_eq_drift (n : ℕ) (α : ℝ)
    (hα : 0 ≤ α) (z : Configuration n) (hz : CollisionFree z) :
    ginibreInteractionConfigurationTilt n α z = ginibreLangevinDrift n α z-(-2*α/(n : ℝ)) • z := by
  ext j
  apply Complex.ext
  · have ht := ginibreInteractionBrownianTilt_noise_drift n α hα z (j, 0)
    have hd := ginibreInteractionPotential_originalDrift_real α z hz j
    simpa [ginibreInteractionConfigurationTilt, Complex.smul_re, smul_eq_mul,
      ginibreCoordinateDirection, realCoordinateDirection, Pi.sub_apply, Pi.smul_apply] using
          ht.trans hd.symm
  · have ht := ginibreInteractionBrownianTilt_noise_drift n α hα z (j, 1)
    have hd := ginibreInteractionPotential_originalDrift_imaginary α z hz j
    simpa [ginibreInteractionConfigurationTilt, Complex.smul_im, smul_eq_mul,
      ginibreCoordinateDirection, imaginaryCoordinateDirection, Pi.sub_apply, Pi.smul_apply] using
          ht.trans hd.symm

/-- Literal correction of the reference driving noise by the actual
interaction drift, without stochastic-integral or law assumptions. -/
def ginibreInteractionCorrectedNoise (n : ℕ) (α : ℝ)
    (N Y : ℝ → Configuration n) (t : ℝ) : Configuration n :=
  N t-∫ u in (0 : ℝ)..t, ginibreInteractionConfigurationTilt n α (Y u)

/-- Exact configuration-valued identity for the literal corrected Brownian
coordinates, proved by commuting a real linear embedding with time integration. -/
theorem ginibreCorrectedBrownianNoise_eq {Ω : Type*} (n : ℕ) (α : ℝ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (F : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) (ht : 0 ≤ t)
    (hi : IntervalIntegrable (fun s : ℝ => fun i => F i (Real.toNNReal s) ω) volume 0 t) :
    ginibreConfigurationBrownianNoise n
      (fun i r ω => B i r ω-B i 0 ω-∫ s in (0 : ℝ)..(r : ℝ), F i (Real.toNNReal s) ω) α ω t =
    ginibreConfigurationBrownianNoise n B α ω t-ginibreConfigurationBrownianNoise n B α ω 0-
      ∫ s in (0 : ℝ)..t, ginibreBrownianEmbeddingCLM n α (fun i => F i (Real.toNNReal s) ω) := by
  let L := ginibreBrownianEmbeddingCLM n α
  have he (i : Fin n × Fin 2) :
      (∫ s in (0 : ℝ)..t, (fun i => F i (Real.toNNReal s) ω)) i =
      ∫ s in (0 : ℝ)..t, F i (Real.toNNReal s) ω :=
    by simpa only [ContinuousLinearMap.proj_apply] using
      ((ContinuousLinearMap.proj i : (((Fin n × Fin 2) → ℝ) →L[ℝ] ℝ)).intervalIntegral_comp_comm
          hi).symm
  have hv : (fun i => B i t.toNNReal ω-B i 0 ω-
      ∫ s in (0 : ℝ)..t, F i (Real.toNNReal s) ω) =
      (fun i => B i t.toNNReal ω)-(fun i => B i 0 ω)-
        ∫ s in (0 : ℝ)..t, (fun i => F i (Real.toNNReal s) ω) := by
    funext i
    simp only [Pi.sub_apply, he]
  have hL := L.intervalIntegral_comp_comm hi
  change L (fun i => B i t.toNNReal ω-B i 0 ω-
    ∫ s in (0 : ℝ)..(t.toNNReal : ℝ), F i (Real.toNNReal s) ω) =
      L (fun i => B i t.toNNReal ω)-L (fun i => B i (0 : ℝ).toNNReal ω)-_
  rw [Real.coe_toNNReal _ ht, Real.toNNReal_zero, hv, map_sub, map_sub,← hL]

/-- Every genuine compact collision-free OU reference solution obeys the
original Volterra equation with its literal interaction-corrected noise. -/
theorem ginibreOUPath_corrected_original_volterra {n : ℕ} (α : ℝ) (hα : 0 ≤ α)
    (z : Configuration n) (N Y : ℝ → Configuration n) (T : ℝ≥0)
    (hY : ContinuousOn Y (Icc 0 (T : ℝ))) (hcf : ∀ t ∈ Icc 0 (T : ℝ), CollisionFree (Y t))
    (hEq : ∀ t ∈ Icc 0 (T : ℝ), Y t = z + N t +
      ∫ u in (0 : ℝ)..t, (-2 * α / (n : ℝ)) • Y u) :
    ∀ t∈Icc 0 (T : ℝ), Y t=z+ginibreInteractionCorrectedNoise n α N Y t+
      ∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (Y u) := by
  intro t ht
  have hDrift : ContinuousOn (fun u => ginibreLangevinDrift n α (Y u)) (Icc 0 (T : ℝ)) :=
    fun u hu => (ginibreLangevinDrift_contDiffAt n α (Y u) (hcf u
        hu)).continuousAt.comp_continuousWithinAt (hY u hu)
  have hOU : ContinuousOn (fun u => (-2*α/(n : ℝ)) • Y u) (Icc 0 (T : ℝ)) := by
    exact hY.const_smul (-2*α/(n : ℝ))
  have hiD : IntervalIntegrable (fun u => ginibreLangevinDrift n α (Y u)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hDrift.mono (Icc_subset_Icc_right ht.2)
  have hiOU : IntervalIntegrable (fun u => (-2*α/(n : ℝ)) • Y u) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hOU.mono (Icc_subset_Icc_right ht.2)
  have hc : (∫ u in (0 : ℝ)..t, ginibreInteractionConfigurationTilt n α (Y u)) =
      (∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (Y u))-
      ∫ u in (0 : ℝ)..t, (-2*α/(n : ℝ)) • Y u := by
    rw [← intervalIntegral.integral_sub hiD hiOU]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact ginibreInteractionConfigurationTilt_eq_drift n α hα (Y u) (hcf u ⟨hu.1, hu.2.trans ht.2⟩)
  rw [hEq t ht]
  unfold ginibreInteractionCorrectedNoise
  rw [hc]
  abel

/-- Canonical original maximal solution identification on every genuine
collision-free OU prefix after correcting its actual interaction noise. -/
theorem ginibreOUPath_corrected_canonical_prefix {n : ℕ} (α : ℝ) (hα : 0 ≤ α)
    (z : Configuration n) (N Y : ℝ → Configuration n) (T : ℝ≥0)
    (hY : ContinuousOn Y (Icc 0 (T : ℝ))) (hY0 : Y 0 = z)
    (hcf : ∀ t ∈ Icc 0 (T : ℝ), CollisionFree (Y t))
    (hEq : ∀ t ∈ Icc 0 (T : ℝ), Y t = z + N t +
      ∫ u in (0 : ℝ)..t, (-2 * α / (n : ℝ)) • Y u) :
    (T : ℝ≥0∞) ≤ ginibreDrivenMaximalLifetime n α (ginibreInteractionCorrectedNoise n α N Y) z ∧
      ∀ t : ℝ≥0, t<T → ginibreDrivenMaximalValue n α
        (ginibreInteractionCorrectedNoise n α N Y) z t = Y t := by
  have hD : ContinuousOn (fun u => ginibreLangevinDrift n α (Y u)) (Icc 0 (T : ℝ)) :=
    fun u hu => (ginibreLangevinDrift_contDiffAt n α (Y u) (hcf u
        hu)).continuousAt.comp_continuousWithinAt (hY u hu)
  have hseg : GinibreDrivenSegment n α (ginibreInteractionCorrectedNoise n α N Y) z T Y := by
    refine ⟨hY, hY0,?_⟩
    intro t ht
    refine ⟨hcf t ht,?_, ginibreOUPath_corrected_original_volterra α hα z N Y T hY hcf hEq t ht⟩
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hD.mono (Icc_subset_Icc_right ht.2)
  have hL : (T : ℝ≥0∞)≤ginibreDrivenMaximalLifetime n α (ginibreInteractionCorrectedNoise n α N Y) z
      :=
    le_iSup_of_le (⟨T, ⟨Y, hseg⟩⟩ : ginibreDrivenHorizons n α (ginibreInteractionCorrectedNoise n α
        N Y) z) le_rfl
  refine ⟨hL,?_⟩
  intro t ht
  exact ginibreDrivenMaximalValue_eq_segment hseg t ht.le ((ENNReal.coe_lt_coe.mpr ht).trans_le hL)

/-- Actual coordinate Brownian correction for the stationary OU interaction. -/
def ginibreInteractionCorrectedBrownian {Ω : Type*} (n : ℕ) (α : ℝ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (Y : ℝ≥0 → Ω → Configuration n) : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ :=
  fun i r ω => B i r ω-B i 0 ω-∫ s in (0 : ℝ)..(r : ℝ),
    ginibreInteractionBrownianTilt n α (Y s.toNNReal ω) i

theorem ginibreInteractionCorrectedBrownian_noise_continuous {Ω : Type*}
    (n : ℕ) (α : ℝ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (Y : ℝ≥0 → Ω → Configuration n) (ω : Ω)
    (hB : ∀ i, Continuous (fun t => B i t ω))
    (hY : Continuous (fun t => Y t ω)) (hCF : ∀ t, CollisionFree (Y t ω)) :
    Continuous (ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α
        ω) ∧
      ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω 0=0 :=
          by
  have hc (i : Fin n × Fin 2) : Continuous (fun t : ℝ => ginibreInteractionBrownianTilt n α (Y
      t.toNNReal ω) i) :=
    ((ginibreInteractionBrownianTilt_continuousOn n α i).comp_continuous hY hCF).comp
        continuous_real_toNNReal
  have hp (i : Fin n × Fin 2) : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t,
      ginibreInteractionBrownianTilt n α (Y s.toNNReal ω) i) :=
    intervalIntegral.continuous_primitive (fun a b => (hc i).intervalIntegrable a b) 0
  constructor
  · change Continuous (fun t : ℝ => ginibreBrownianEmbeddingCLM n α
      (fun i => ginibreInteractionCorrectedBrownian n α B Y i t.toNNReal ω))
    apply (ginibreBrownianEmbeddingCLM n α).continuous.comp
    apply continuous_pi
    intro i
    exact ((hB i).comp continuous_real_toNNReal).sub continuous_const |>.sub
      ((hp i).comp (continuous_subtype_val.comp continuous_real_toNNReal))
  · ext j
    simp [ginibreConfigurationBrownianNoise, ginibreInteractionCorrectedBrownian]

/-- A genuine reference OU prefix becomes the actual original Ginibre
Volterra prefix under its literal coordinate Brownian Girsanov correction. -/
theorem ginibreOUPath_correctedBrownian_original_volterra {Ω : Type*}
    (n : ℕ) (α : ℝ) (hα : 0 ≤ α)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (Y : ℝ≥0 → Ω → Configuration n) (ω : Ω) (z : Configuration n) (θ : ℝ≥0)
    (hYC : Continuous (fun t => Y t ω)) (hcf : ∀ t, CollisionFree (Y t ω))
    (hN0 : ginibreConfigurationBrownianNoise n B α ω 0 = 0)
    (hEq : ∀ t ≤ θ, Y t ω = z + ginibreConfigurationBrownianNoise n B α ω t +
      ∫ s in (0 : ℝ)..(t : ℝ), (-2 * α / (n : ℝ)) • Y s.toNNReal ω) :
    ∀ t ≤ θ, Y t ω = z + ginibreConfigurationBrownianNoise n
      (ginibreInteractionCorrectedBrownian n α B Y) α ω t +
      ∫ s in (0 : ℝ)..(t : ℝ), ginibreLangevinDrift n α (Y s.toNNReal ω) := by
  let y := fun s : ℝ => Y s.toNNReal ω
  have hcont : Continuous y := hYC.comp continuous_real_toNNReal
  have hF : Continuous (fun s : ℝ => fun i => ginibreInteractionBrownianTilt n α (Y s.toNNReal ω) i)
      := by
    apply continuous_pi
    intro i
    exact ((ginibreInteractionBrownianTilt_continuousOn n α i).comp_continuous hYC hcf).comp
        continuous_real_toNNReal
  have hEqR : ∀ t∈Icc (0 : ℝ) (θ : ℝ), y t=z+ginibreConfigurationBrownianNoise n B α ω t+
      ∫ s in (0 : ℝ)..t, (-2*α/(n : ℝ)) • y s := by
    intro t ht
    have he := hEq t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2)
    simpa only [y, Real.coe_toNNReal _ ht.1] using he
  have hV := ginibreOUPath_corrected_original_volterra α hα z
    (ginibreConfigurationBrownianNoise n B α ω) y θ hcont.continuousOn
    (fun t ht => hcf _) hEqR
  intro t ht
  have hnoise := ginibreCorrectedBrownianNoise_eq n α B
    (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) ω (t : ℝ) t.property
        (hF.intervalIntegrable 0 t)
  rw [hN0, sub_zero] at hnoise
  have hcor : (∫ s in (0 : ℝ)..(t : ℝ), ginibreBrownianEmbeddingCLM n α
      (fun i => ginibreInteractionBrownianTilt n α (Y s.toNNReal ω) i)) =
      ∫ s in (0 : ℝ)..(t : ℝ), ginibreInteractionConfigurationTilt n α (y s) := by
    congr 1
  rw [hcor] at hnoise
  have he := hV t ⟨t.property, by exact_mod_cast ht⟩
  change Y t ω=z+ginibreConfigurationBrownianNoise n
    (fun i r ω => B i r ω-B i 0 ω-∫ s in (0 : ℝ)..(r : ℝ),
      ginibreInteractionBrownianTilt n α (Y s.toNNReal ω) i) α ω t+_
  simpa only [y, Real.toNNReal_coe, ginibreInteractionCorrectedNoise,← hnoise] using he

end
end GinibrePoincare
