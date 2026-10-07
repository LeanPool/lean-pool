/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGain

/-!
# Time cutoffs of whole-space heat solutions

The whole-space form of `lem:local-heat-gain`, used in `prop:lps-smoothing`,
multiplies a solution of `∂ₜ z - Δ z = G` on `ℝ³ × I` by a smooth cutoff
`c(t)` depending on time only. Spatial derivatives commute with the cutoff, so
a space-time derivative family `D` of `z` gives the family `c D` of `c z`, and
`c z` solves `∂ₜ (c z) - Δ (c z) = c G + c' z` on `ℝ³ × I`. The squared norms
are controlled by the bounds for `c` and `c'`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A function of time alone has vanishing spatial derivatives. -/
theorem spatialPartial_timeFun (c : ℝ → ℝ) (j : Fin 3) (p : Vec3 × ℝ) :
    spatialPartial (fun q : Vec3 × ℝ => c q.2) j p = 0 := by
  change (fderiv ℝ (fun _ : Vec3 => c p.2) p.1) (basisVec j) = 0
  simp

/-- The distributional spatial derivative of `c(t) f` is `c(t) ∂_j f`. -/
theorem IsSpaceTimeWeakPartial.time_mul {V : Set (Vec3 × ℝ)} {j : Fin 3}
    {f g : Vec3 × ℝ → ℝ} (h : IsSpaceTimeWeakPartial V j f g) {c : ℝ → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hf : MemLp f 2 (volume.restrict V))
    (hg : MemLp g 2 (volume.restrict V)) :
    IsSpaceTimeWeakPartial V j (fun p => c p.2 * f p) (fun p => c p.2 * g p) := by
  have h1 := h.smooth_mul (ζ := fun q : Vec3 × ℝ => c q.2) (hc.comp contDiff_snd) hf hg
  have e : (fun p : Vec3 × ℝ =>
      spatialPartial (fun q : Vec3 × ℝ => c q.2) j p * f p + c p.2 * g p) =
      fun p => c p.2 * g p :=
    funext fun p => by rw [spatialPartial_timeFun, zero_mul, zero_add]
  rw [e] at h1
  exact h1

/-- A bounded continuous function of time keeps square integrability. -/
theorem memLp_time_mul {V : Set (Vec3 × ℝ)} {f : Vec3 × ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict V)) {c : ℝ → ℝ} (hc : Continuous c) {L : ℝ}
    (hcL : ∀ t, |c t| ≤ L) :
    MemLp (fun p : Vec3 × ℝ => c p.2 * f p) 2 (volume.restrict V) := by
  have hcm : AEStronglyMeasurable (fun p : Vec3 × ℝ => c p.2) (volume.restrict V) :=
    (hc.comp continuous_snd).aestronglyMeasurable
  refine (hf.const_mul L).of_le (hcm.mul hf.aestronglyMeasurable) (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hcL p.2).trans (le_abs_self L)) (abs_nonneg _)

/-- Multiplication by a smooth bounded function of time maps a space-time
derivative family to a space-time derivative family. -/
theorem IsSpaceTimeFamily.time_mul {n : ℕ} {V : Set (Vec3 × ℝ)}
    {B : List (Fin 3) → Vec3 × ℝ → ℝ} (hB : IsSpaceTimeFamily n V B) {c : ℝ → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) {L : ℝ} (hcL : ∀ t, |c t| ≤ L) :
    IsSpaceTimeFamily n V (fun α p => c p.2 * B α p) :=
  ⟨fun α hα => memLp_time_mul (hB.memL2 α hα) hc.continuous hcL,
    fun α j hα => (hB.weak α j hα).time_mul hc (hB.memL2 α hα.le)
      (hB.memL2 _ (by simp only [List.length_append, List.length_singleton]; omega))⟩

/-- `lem:local-heat-gain` on the whole space, first step: if `∂ₜ z - Δ z = G`
on `ℝ³ × I` and `c` is a smooth function of time, then
`∂ₜ (c z) - Δ (c z) = c G + c' z` on `ℝ³ × I`. -/
theorem _root_.CKN.IsHeatSolutionOn.time_mul {I : Set ℝ} {z G : Vec3 × ℝ → ℝ}
    (hz : MemLp z 2 (volume.restrict ((univ : Set Vec3) ×ˢ I)))
    (hG : MemLp G 2 (volume.restrict ((univ : Set Vec3) ×ˢ I)))
    (hheat : IsHeatSolutionOn univ I z G) {c : ℝ → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    IsHeatSolutionOn univ I (fun p => c p.2 * z p)
      (fun p => c p.2 * G p + deriv c p.2 * z p) := by
  intro φ hφ hφc hφV
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => c q.2) := hc.comp contDiff_snd
  have hc' : ContDiff ℝ (⊤ : ℕ∞) (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
  -- the test function `c(t) φ`
  let ψ : Vec3 × ℝ → ℝ := fun q => c q.2 * φ q
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hA.mul hφ
  have hψc : HasCompactSupport ψ := hφc.mul_left
  have hψV : tsupport ψ ⊆ (univ : Set Vec3) ×ˢ I :=
    (tsupport_mul_subset_right (f := fun q : Vec3 × ℝ => c q.2) (g := φ)).trans hφV
  have hψt (p : Vec3 × ℝ) :
      timePartial ψ p = c p.2 * timePartial φ p + φ p * deriv c p.2 :=
    vorticityHeatSmooth_timePartial_mul hA hφ p
  have hφj (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => spatialPartial φ j q) :=
    vorticityHeatSmooth_spatialPartial_contDiff hφ j
  have hψj (j : Fin 3) : (fun w : Vec3 × ℝ => spatialPartial ψ j w) =
      fun w => c w.2 * spatialPartial φ j w := by
    funext w
    have e : spatialPartial ψ j w = c w.2 * spatialPartial φ j w +
        φ w * spatialPartial (fun q : Vec3 × ℝ => c q.2) j w :=
      vorticityHeatSmooth_spatialPartial_mul hA hφ j w
    rw [e, spatialPartial_timeFun, mul_zero, add_zero]
  have hψjj (j : Fin 3) (p : Vec3 × ℝ) :
      spatialSecondPartial ψ j j p = c p.2 * spatialSecondPartial φ j j p := by
    change spatialPartial (fun w : Vec3 × ℝ => spatialPartial ψ j w) j p = _
    rw [hψj j]
    have e : spatialPartial (fun w : Vec3 × ℝ => c w.2 * spatialPartial φ j w) j p =
        c p.2 * spatialPartial (fun w : Vec3 × ℝ => spatialPartial φ j w) j p +
          spatialPartial φ j p * spatialPartial (fun q : Vec3 × ℝ => c q.2) j p :=
      vorticityHeatSmooth_spatialPartial_mul hA (hφj j) j p
    rw [spatialPartial_timeFun, mul_zero, add_zero] at e
    exact e
  -- integrability
  set μ : Measure (Vec3 × ℝ) := volume.restrict ((univ : Set Vec3) ×ˢ I) with hμ
  have hL2 {f : Vec3 × ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
      MemLp f 2 μ := memLp_two_restrict_of_test hf hfc _
  let T : Vec3 × ℝ → ℝ := fun p => -timePartial ψ p - ∑ j : Fin 3, spatialSecondPartial ψ j j p
  have hT : Integrable (fun p => z p * T p) μ := by
    have h1 : Continuous (fun p : Vec3 × ℝ => timePartial ψ p) :=
      (vorticityHeatSmooth_timePartial_contDiff hψ).continuous
    have h2 (j : Fin 3) : Continuous (fun p : Vec3 × ℝ => spatialSecondPartial ψ j j p) :=
      (vorticityHeatSmooth_spatialPartial_contDiff
        (vorticityHeatSmooth_spatialPartial_contDiff hψ j) j).continuous
    have hTc : Continuous T := h1.neg.sub (continuous_finsetSum _ fun j _ => h2 j)
    have hTs : HasCompactSupport T := by
      refine hψc.mono' fun p hp => ?_
      by_contra hpt
      apply hp
      simp only [T, CKN.timePartial_eq_zero_off_tsupport hpt,
        fun j => CKN.spatialSecondPartial_eq_zero_off_tsupport hpt j j,
        Finset.sum_const_zero, neg_zero, sub_zero]
    exact hz.integrable_mul (hL2 hTc hTs)
  have hdφ : Integrable (fun p => z p * (deriv c p.2 * φ p)) μ :=
    hz.integrable_mul (hL2 ((hc'.continuous.comp continuous_snd).mul hφ.continuous)
      hφc.mul_left)
  have hGψ : Integrable (fun p => G p * ψ p) μ := hG.integrable_mul (hL2 hψ.continuous hψc)
  -- the pointwise identities
  have hL (p : Vec3 × ℝ) :
      c p.2 * z p * (-timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) =
        z p * T p + z p * (deriv c p.2 * φ p) := by
    simp only [T, hψt p, Finset.sum_congr rfl fun j _ => hψjj j p, ← Finset.mul_sum]
    ring
  have hR (p : Vec3 × ℝ) :
      (c p.2 * G p + deriv c p.2 * z p) * φ p = G p * ψ p + z p * (deriv c p.2 * φ p) := by
    simp only [ψ]
    ring
  change ∫ p in (univ : Set Vec3) ×ˢ I, c p.2 * z p *
      (-timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) =
    ∫ p in (univ : Set Vec3) ×ˢ I, (c p.2 * G p + deriv c p.2 * z p) * φ p
  rw [integral_congr_ae (ae_of_all _ hL), integral_congr_ae (ae_of_all _ hR),
    integral_add hT hdφ, integral_add hGψ hdφ]
  have hkey : ∫ p in (univ : Set Vec3) ×ˢ I, z p * T p =
      ∫ p in (univ : Set Vec3) ×ˢ I, G p * ψ p := hheat ψ hψ hψc hψV
  rw [hkey]

/-- The square integral of `c(t) f` with `|c| ≤ 1` is at most that of `f`. -/
theorem integral_sq_time_mul_le {V : Set (Vec3 × ℝ)} {f : Vec3 × ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict V)) {c : ℝ → ℝ} (hc : Continuous c)
    (hc1 : ∀ t, |c t| ≤ 1) :
    ∫ p in V, (c p.2 * f p) ^ 2 ≤ ∫ p in V, f p ^ 2 := by
  refine integral_mono (memLp_time_mul hf hc hc1).integrable_sq hf.integrable_sq fun p => ?_
  have hc2 : c p.2 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (hc1 p.2)
  rw [mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) hc2

/-- The square integral of `c(t) g + d(t) f` with `|c| ≤ 1` and `|d| ≤ L` is at
most `2 ‖g‖² + 2 L² ‖f‖²`. -/
theorem integral_sq_time_mul_add_le {V : Set (Vec3 × ℝ)} {f g : Vec3 × ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict V)) (hg : MemLp g 2 (volume.restrict V))
    {c d : ℝ → ℝ} (hc : Continuous c) (hd : Continuous d) (hc1 : ∀ t, |c t| ≤ 1) {L : ℝ}
    (hdL : ∀ t, |d t| ≤ L) :
    ∫ p in V, (c p.2 * g p + d p.2 * f p) ^ 2 ≤
      2 * (∫ p in V, g p ^ 2) + 2 * L ^ 2 * ∫ p in V, f p ^ 2 := by
  have hcg := memLp_time_mul hg hc hc1
  have hdf := memLp_time_mul hf hd hdL
  have i1 := hg.integrable_sq
  have i2 := hf.integrable_sq
  have hR : Integrable (fun p => 2 * g p ^ 2 + 2 * L ^ 2 * f p ^ 2) (volume.restrict V) :=
    (i1.const_mul 2).add (i2.const_mul (2 * L ^ 2))
  refine (integral_mono (hcg.add hdf).integrable_sq hR fun p => ?_).trans (le_of_eq ?_)
  · have hc2 : c p.2 ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (hc1 p.2)
    have hd2 : d p.2 ^ 2 ≤ L ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hdL p.2) 2
    have h1 : (c p.2 * g p) ^ 2 ≤ g p ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) hc2
    have h2 : (d p.2 * f p) ^ 2 ≤ L ^ 2 * f p ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)
    change (c p.2 * g p + d p.2 * f p) ^ 2 ≤ 2 * g p ^ 2 + 2 * L ^ 2 * f p ^ 2
    nlinarith only [h1, h2, sq_nonneg (c p.2 * g p - d p.2 * f p)]
  · rw [integral_add (i1.const_mul 2) (i2.const_mul (2 * L ^ 2)), integral_const_mul,
      integral_const_mul]

end ESS
