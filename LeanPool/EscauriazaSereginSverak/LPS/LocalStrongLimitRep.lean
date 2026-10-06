/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedPressure

/-!
# Jointly measurable representatives of continuous `L²` curves

A continuous curve in `L²(ℝ³)` over a compact time interval has a jointly measurable space-time
representative whose time slices represent the curve at every time: the limit of the spatial
mollifications (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Convolution
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- A continuous `L²` curve over a closed time interval has a jointly strongly measurable
representative whose slice at every time of the interval represents the curve. -/
theorem lps_curve_measurable_rep {a b : ℝ} (hab : a ≤ b)
    {L : Icc a b → Lp ℝ 2 (volume : Measure Vec3)} (hL : Continuous L) :
    ∃ f : Vec3 × ℝ → ℝ, StronglyMeasurable f ∧
      ∀ (t : ℝ) (ht : t ∈ Icc a b),
        (fun x => f (x, t)) =ᵐ[volume]
          ((L ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) := by
  classical
  let proj : ℝ → Icc a b := Set.projIcc a b hab
  let g : ℝ → Vec3 → ℝ := fun t => ((L (proj t) : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ)
  have hg : ∀ t, MemLp (g t) 2 volume := fun t => Lp.memLp (L (proj t))
  let f : Vec3 × ℝ → ℝ := fun z =>
    limUnder atTop fun n : ℕ =>
      CKN.mollify (g z.2) (1 / ((n : ℝ) + 1)) (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) z.1
  refine ⟨f, ?_, ?_⟩
  · refine StronglyMeasurable.limUnder fun n => ?_
    let δ : ℝ := 1 / ((n : ℝ) + 1)
    have hδ : 0 < δ := (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    refine (measurable_uncurry_of_continuous_of_measurable
      (u := fun (x : Vec3) (t : ℝ) => CKN.mollify (g t) δ hδ x) (fun t => ?_)
      (fun x => ?_)).stronglyMeasurable
    · exact CKN.mollify_continuous hδ ((hg t).locallyIntegrable (by norm_num))
    · refine Continuous.measurable ?_
      rw [continuous_iff_continuousAt]
      intro t₀
      have hLc : Continuous (fun t : ℝ => L (proj t)) := hL.comp continuous_projIcc
      have hlim : Tendsto (fun t => ‖L (proj t) - L (proj t₀)‖) (𝓝 t₀) (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.1 (hLc.tendsto t₀)
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
      have hC := hlim.const_mul (eLpNorm (CKN.mollifier (d := 3) δ hδ) 2 volume).toReal
      rw [mul_zero] at hC
      refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) hC
      rw [Real.norm_eq_abs]
      refine (CKN.Leray.abs_mollify_sub_le (hg t) (hg t₀) hδ x).trans (le_of_eq ?_)
      rw [ENNReal.toReal_mul]
      congr 1
      have hsub : (g t - g t₀) =ᵐ[volume]
          ((L (proj t) - L (proj t₀) : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) := by
        filter_upwards [Lp.coeFn_sub (L (proj t)) (L (proj t₀))] with x hx
        show g t x - g t₀ x = _
        rw [hx]
        rfl
      rw [eLpNorm_congr_ae hsub, ← Lp.norm_def]
  · intro t ht
    have hloc := (hg t).locallyIntegrable (by norm_num)
    have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := (volume : Measure Vec3)) (l := atTop) (K := 2)
      (φ := fun n : ℕ => CKN.standardMollifier (d := 3) (1 / ((n : ℝ) + 1))
        (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
      (by simpa only [CKN.standardMollifier] using
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      (Eventually.of_forall fun n => by
        simp only [CKN.standardMollifier]
        linarith only [(by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))])
      hloc
    have hp : proj t = ⟨t, ht⟩ := Set.projIcc_of_mem hab ht
    filter_upwards [hconv] with x hx
    have h1 : (limUnder atTop fun n : ℕ => CKN.mollify (g t) (1 / ((n : ℝ) + 1))
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) x) = g t x := hx.limUnder_eq
    change (limUnder atTop fun n : ℕ => CKN.mollify (g t) (1 / ((n : ℝ) + 1))
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) x) = _
    rw [h1]
    simp only [g, hp]

end ESS.LPS

end
