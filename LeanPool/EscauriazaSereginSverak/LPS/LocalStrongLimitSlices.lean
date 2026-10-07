/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitRegularity

/-!
# Continuous curves coincide with continuous slices

A continuous `L²` curve that represents a slice family for almost every time
represents it at every time, whenever the slice family itself is continuous in
`L²` (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The squared norm of an `L²` class is the integral of the square of any
representative. -/
theorem lps_lp_norm_sq_eq {L : Lp ℝ 2 (volume : Measure Vec3)} {f : Vec3 → ℝ}
    (h : ((L : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume] f)
    (hf : MemLp f 2 volume) : ‖L‖ ^ 2 = ∫ x, f x ^ 2 := by
  rw [Lp.norm_def, eLpNorm_congr_ae h]
  exact (vl_integral_sq_eq hf).symm

/-- A continuous curve representing a continuous slice family almost
everywhere represents it everywhere. -/
theorem lps_curve_eq_of_continuous {a b : ℝ} (hab : a < b) {F : Vec3 × ℝ → ℝ}
    {L : Icc a b → Lp ℝ 2 (volume : Measure Vec3)} (hL : Continuous L)
    (hLF : ∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ hs : s ∈ Icc a b,
      ((L ⟨s, hs⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
        fun x => F (x, s))
    (hFmem : ∀ t ∈ Icc a b, MemLp (fun x => F (x, t)) 2 volume)
    (hFc : ∀ t ∈ Icc a b,
      Tendsto (fun s => eLpNorm (fun x => F (x, s) - F (x, t)) 2 volume)
        (nhdsWithin t (Icc a b)) (𝓝 0)) :
    ∀ (t : ℝ) (ht : t ∈ Icc a b),
      ((L ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
        fun x => F (x, t) := by
  classical
  let G : Icc a b → Lp ℝ 2 (volume : Measure Vec3) :=
    fun t => (hFmem t.1 t.2).toLp _
  have hGc : Continuous G := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    have hval : Tendsto (fun s : Icc a b => (s : ℝ)) (𝓝 t) (nhdsWithin t.1 (Icc a b)) :=
      tendsto_nhdsWithin_iff.2 ⟨continuous_subtype_val.tendsto t,
        Eventually.of_forall fun s => s.2⟩
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ((hFc t.1 t.2).comp hval)
    rw [ENNReal.toReal_zero] at h1
    refine h1.congr fun s => ?_
    simp only [Function.comp_apply, G, dist_eq_norm]
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  let proj : ℝ → Icc a b := Set.projIcc a b hab.le
  have hproj : Continuous proj := continuous_projIcc
  have hLr : Continuous (fun t : ℝ => L (proj t)) := hL.comp hproj
  have hGr : Continuous (fun t : ℝ => G (proj t)) := hGc.comp hproj
  have hae : (fun t : ℝ => L (proj t)) =ᵐ[volume.restrict (Ioo a b)]
      fun t => G (proj t) := by
    filter_upwards [hLF, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    have hsI' : s ∈ Icc a b := Ioo_subset_Icc_self hsI
    have hp : proj s = ⟨s, hsI'⟩ := Set.projIcc_of_mem hab.le hsI'
    rw [hp]
    apply Lp.ext
    have h1 := hs hsI'
    have h2 := (hFmem s hsI').coeFn_toLp
    exact h1.trans h2.symm
  have hEqIoo := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hLr.continuousOn hGr.continuousOn
  have hEqIcc : EqOn (fun t : ℝ => L (proj t)) (fun t => G (proj t)) (Icc a b) :=
    hEqIoo.of_subset_closure hLr.continuousOn hGr.continuousOn Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
  intro t ht
  have hp : proj t = ⟨t, ht⟩ := Set.projIcc_of_mem hab.le ht
  have h := hEqIcc ht
  simp only [hp] at h
  rw [h]
  exact (hFmem t ht).coeFn_toLp

end ESS.LPS

end
