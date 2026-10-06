/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitWeak
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongSlices
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitIBP

/-!
# Time regularity of the slices of the compactness limit

Continuity in `L²` of a curve which represents slices at every time gives the continuity of the
slices, and weak partial derivatives of almost every slice extend to every slice when the weak
derivative is represented by a continuous curve (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The slices of a function represented at every time by a continuous `L²` curve are continuous
in `L²`. -/
theorem lps_curve_slices_tendsto {a b : ℝ} (hab : a < b) {F : Vec3 × ℝ → ℝ}
    {L : Icc a b → Lp ℝ 2 (volume : Measure Vec3)} (hL : Continuous L)
    (hrep : ∀ (t : ℝ) (ht : t ∈ Icc a b),
      ((L ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume] fun x => F (x, t))
    {t : ℝ} (ht : t ∈ Icc a b) :
    Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => F (x, s) - F (x, t)) 2 volume)
      (nhdsWithin t (Icc a b)) (𝓝 0) := by
  let proj : ℝ → Icc a b := Set.projIcc a b hab.le
  have hLr : Continuous (fun s : ℝ => L (proj s)) := hL.comp continuous_projIcc
  have hlim : Tendsto (fun s : ℝ => ‖L (proj s) - L (proj t)‖) (𝓝 t) (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.1 (hLr.tendsto t)
    exact this
  have hlim' : Tendsto (fun s : ℝ => ENNReal.ofReal ‖L (proj s) - L (proj t)‖)
      (nhdsWithin t (Icc a b)) (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hlim.mono_left (nhdsWithin_le_nhds (s := Icc a b)))
    simpa using this
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hps : proj s = ⟨s, hs⟩ := Set.projIcc_of_mem hab.le hs
  have hpt : proj t = ⟨t, ht⟩ := Set.projIcc_of_mem hab.le ht
  rw [hps, hpt]
  have hsub : (fun x : Vec3 => F (x, s) - F (x, t)) =ᵐ[volume]
      ((L ⟨s, hs⟩ - L ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) := by
    filter_upwards [Lp.coeFn_sub (L ⟨s, hs⟩) (L ⟨t, ht⟩), hrep s hs, hrep t ht] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  rw [eLpNorm_congr_ae hsub, Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp _).eLpNorm_ne_top]

/-- A weak spatial derivative of almost every slice, represented by a continuous `L²` curve, is a
weak spatial derivative of every slice when the slices are weakly continuous. -/
theorem lps_weak_partial_all_times {a b : ℝ} (hab : a < b) (j : Fin 3) {F G : Vec3 × ℝ → ℝ}
    {L : Icc a b → Lp ℝ 2 (volume : Measure Vec3)} (hL : Continuous L)
    (hLG : ∀ (t : ℝ) (ht : t ∈ Icc a b),
      ((L ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume] fun x => G (x, t))
    (hFweak : ∀ w : Vec3 → ℝ, MemLp w 2 volume →
      ContinuousOn (fun t : ℝ => ∫ x, F (x, t) * w x) (Icc a b))
    (hslice : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      HasWeakPartialDerivOn (Set.univ : Set Vec3) j (fun x => F (x, t)) (fun x => G (x, t))) :
    ∀ t ∈ Icc a b,
      HasWeakPartialDerivOn (Set.univ : Set Vec3) j (fun x => F (x, t)) (fun x => G (x, t)) := by
  classical
  intro t ht φ hφ hφc _
  let proj : ℝ → Icc a b := Set.projIcc a b hab.le
  have hLr : Continuous (fun s : ℝ => L (proj s)) := hL.comp continuous_projIcc
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hdφ : MemLp (fun x => (fderiv ℝ φ x) (basisVec j)) 2 volume :=
    ((contDiff_spatialDeriv_smooth hφ j).continuous).memLp_of_hasCompactSupport
      (hφc.fderiv_apply (𝕜 := ℝ) (basisVec j))
  have hc1 := hFweak _ hdφ
  have hc2 : Continuous (fun s : ℝ => -inner ℝ (L (proj s)) (hφ2.toLp φ)) :=
    (hLr.inner continuous_const).neg
  have hEq := lps_eqOn_Icc_of_ae_eq hab hc1 hc2.continuousOn (by
    filter_upwards [hslice, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    have hsI' : s ∈ Icc a b := Ioo_subset_Icc_self hsI
    have hp : proj s = ⟨s, hsI'⟩ := Set.projIcc_of_mem hab.le hsI'
    have h1 := hs φ hφ hφc (Set.subset_univ _)
    simp only [Measure.restrict_univ] at h1
    rw [h1, hp, lps_scalar_lp_inner_left_eq_integral hφ2]
    congr 1
    exact integral_congr_ae ((hLG s hsI').mono fun x hx => by
      show G (x, s) * φ x = ((L ⟨s, hsI'⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) x * φ x
      rw [hx]))
  have h := hEq ht
  have hp : proj t = ⟨t, ht⟩ := Set.projIcc_of_mem hab.le ht
  simp only [Measure.restrict_univ]
  refine h.trans ?_
  show -inner ℝ (L (proj t)) (hφ2.toLp φ) = _
  rw [hp, lps_scalar_lp_inner_left_eq_integral hφ2]
  congr 1
  exact integral_congr_ae ((hLG t ht).mono fun x hx => by
    show ((L ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) x * φ x = G (x, t) * φ x
    rw [hx])

end ESS.LPS

end
