/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Grönwall estimate with an integrable coefficient

An absolutely continuous energy satisfying a differential inequality with a
nonnegative integrable coefficient is bounded by the corresponding
exponential factor (`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set
open scoped Interval


noncomputable section

namespace ESS.LPS

/-- The absolutely continuous form of Grönwall's inequality used to integrate
the finite and endpoint differential estimates in `lem:lps-H1-estimate`. -/
theorem lps_ac_gronwall {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntegrableOn g (Icc a b) volume)
    (hgpos : ∀ᵐ t ∂(volume.restrict (Icc a b)), 0 ≤ g t)
    (hderiv : ∀ᵐ t ∂(volume.restrict (Icc a b)), deriv f t ≤ g t * f t) :
    ∀ t ∈ Icc a b,
      f t ≤ f a * Real.exp (∫ s in a..t, g s) := by
  let B : ℝ → ℝ := fun t => ∫ s in a..t, g s
  have hgint : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hg
  have hBac : AbsolutelyContinuousOnInterval B a b := by
    simpa [B] using hgint.absolutelyContinuousOnInterval_intervalIntegral
      (c := a) (by simp)
  have hBcont : ContinuousOn B (Icc a b) := by
    rw [← uIcc_of_le hab]
    exact hBac.continuousOn
  have hBnonneg : ∀ t ∈ Icc a b, 0 ≤ B t := by
    intro t ht
    have hsubset : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
    filter_upwards [(ae_mono (Measure.restrict_mono_set volume hsubset)) hgpos,
      ae_restrict_mem measurableSet_Icc] with s hs hsmem
    exact hs
  have hBbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a b, B t ≤ M := by
    have himage : IsCompact (B '' Icc a b) := isCompact_Icc.image_of_continuousOn hBcont
    obtain ⟨M, hM⟩ := himage.bddAbove
    refine ⟨M, ?_, ?_⟩
    · have hzero : B a ∈ B '' Icc a b := ⟨a, ⟨le_rfl, hab⟩, rfl⟩
      have hMa := hM hzero
      have hBa : B a = 0 := by simp [B]
      simpa [hBa] using hMa
    · intro t ht
      exact hM ⟨t, ht, rfl⟩
  obtain ⟨M, _hMnonneg, hMbound⟩ := hBbound
  let E : ℝ → ℝ := fun t => Real.exp (-B t)
  have harg : MapsTo (fun t => -B t) (Icc a b) (Icc (-M) 0) := by
    intro t ht
    constructor
    · linarith only [hMbound t ht]
    · exact neg_nonpos.mpr (hBnonneg t ht)
  have hexpLip : ∃ K, LipschitzOnWith K Real.exp (Icc (-M) 0) := by
    exact (Real.contDiff_exp (n := 1)).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc _ _) isCompact_Icc
  obtain ⟨K, hK⟩ := hexpLip
  have hEac : AbsolutelyContinuousOnInterval E a b := by
    change AbsolutelyContinuousOnInterval (Real.exp ∘ fun t => -B t) a b
    have harg' : MapsTo (fun t => -B t) (uIcc a b) (Icc (-M) 0) := by
      rw [uIcc_of_le hab]
      exact harg
    exact hK.comp_absolutelyContinuousOnInterval harg' (hBac.neg)
  have hfEac : AbsolutelyContinuousOnInterval (fun t => f t * E t) a b :=
    hf.fun_mul hEac
  have hgderiv : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      HasDerivAt B (g t) t := by
    filter_upwards [hgint.ae_hasDerivAt_integral.filter_mono ae_restrict_le,
      ae_restrict_mem measurableSet_Icc] with t hBt ht
    have ht' : t ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ht
    have ha' : a ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩
    have h := hBt ht' a ha'
    simpa [B] using h
  have hprodderiv : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      deriv (fun s => f s * E s) t ≤ 0 := by
    filter_upwards [hf.ae_differentiableAt.filter_mono ae_restrict_le,
      hgderiv, hgpos, hderiv,
      ae_restrict_mem measurableSet_Icc] with t hft hBt _hgt hineq ht
    have hfd : HasDerivAt f (deriv f t) t := by
      have hmem : t ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ht
      exact (hft hmem).hasDerivAt
    have hEd : HasDerivAt E (-E t * g t) t := by
      have h := (Real.hasDerivAt_exp (-B t)).comp t (hBt.neg)
      have h' : HasDerivAt E (Real.exp (-B t) * (-g t)) t := by
        change HasDerivAt (Real.exp ∘ (-B)) _ _
        exact h
      convert h' using 1
      simp [E, mul_comm]
    have hder := (hfd.mul hEd).deriv
    change deriv (f * E) t ≤ 0
    rw [hder]
    have hEpos : 0 < E t := by simp [E, Real.exp_pos]
    have hmul := mul_le_mul_of_nonneg_right hineq hEpos.le
    have : deriv f t * E t + f t * (-E t * g t) ≤ 0 := by
      calc
        _ = deriv f t * E t - (g t * f t) * E t := by ring
        _ ≤ 0 := by nlinarith only [hmul]
    exact this
  have hmonotone : ∀ t ∈ Icc a b, f t * E t ≤ f a * E a := by
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le hab, uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hac := hfEac.mono hsub
    have hderivNonpos : ∀ᵐ s ∂(volume.restrict (Icc a t)),
        deriv (fun s => f s * E s) s ≤ 0 := by
      filter_upwards [(ae_mono (Measure.restrict_mono_set volume
        (Icc_subset_Icc le_rfl ht.2))) hprodderiv] with s hs
      exact hs
    have hnonneg : 0 ≤ ∫ s in a..t, -deriv (fun s => f s * E s) s := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
      filter_upwards [hderivNonpos] with s hs
      exact neg_nonneg.mpr hs
    have hnonpos : ∫ s in a..t, deriv (fun s => f s * E s) s ≤ 0 := by
      have hn : 0 ≤ -(∫ s in a..t, deriv (fun s => f s * E s) s) := by
        simpa only [intervalIntegral.integral_neg] using hnonneg
      linarith only [hn]
    have hFTC := hac.integral_deriv_eq_sub
    have hle : (f t * E t) - (f a * E a) ≤ 0 := by
      rw [← hFTC]
      exact hnonpos
    linarith only [hle]
  intro t ht
  have hEt : E t = Real.exp (-B t) := rfl
  have hEa : E a = 1 := by simp [E, B]
  have h := hmonotone t ht
  rw [hEt, hEa] at h
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (B t))
  have hexpcancel : Real.exp (-B t) * Real.exp (B t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    f t = f t * (Real.exp (-B t) * Real.exp (B t)) := by rw [hexpcancel, mul_one]
    _ = (f t * Real.exp (-B t)) * Real.exp (B t) := by ring
    _ ≤ f a * Real.exp (B t) := by simpa using hmul
    _ = f a * Real.exp (∫ s in a..t, g s) := by rfl

/-- Grönwall with a nonnegative dissipation term carried on the left. If the
derivative of the energy plus the dissipation is controlled by an integrable
coefficient times the energy, the time integral of the dissipation obeys the
same exponential bound (`lem:lps-H1-estimate`). -/
theorem lps_ac_gronwall_dissipation {a b : ℝ} {f d g : ℝ → ℝ}
    (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : IntegrableOn d (Icc a b) volume)
    (hdpos : ∀ᵐ t ∂(volume.restrict (Icc a b)), 0 ≤ d t)
    (hg : IntegrableOn g (Icc a b) volume)
    (hgpos : ∀ᵐ t ∂(volume.restrict (Icc a b)), 0 ≤ g t)
    (hfpos : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hdiff : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      deriv f t + d t ≤ g t * f t) :
    ∀ t ∈ Icc a b,
      f t + ∫ s in a..t, d s ≤ f a * Real.exp (∫ s in a..t, g s) := by
  let I : ℝ → ℝ := fun t => ∫ s in a..t, d s
  let F : ℝ → ℝ := fun t => f t + I t
  have hdint : IntervalIntegrable d volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hd
  have hIac : AbsolutelyContinuousOnInterval I a b := by
    simpa [I] using hdint.absolutelyContinuousOnInterval_intervalIntegral
      (c := a) (by simp)
  have hFac : AbsolutelyContinuousOnInterval F a b := by
    change AbsolutelyContinuousOnInterval (f + I) a b
    exact hf.add hIac
  have hIderiv : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      HasDerivAt I (d t) t := by
    filter_upwards [hdint.ae_hasDerivAt_integral.filter_mono ae_restrict_le,
      ae_restrict_mem measurableSet_Icc] with t hIt ht
    have ht' : t ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ht
    have ha' : a ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩
    have h := hIt ht' a ha'
    simpa [I] using h
  have hIpos : ∀ t ∈ Icc a b, 0 ≤ I t := by
    intro t ht
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    filter_upwards [(ae_mono (Measure.restrict_mono_set volume hsub)) hdpos,
      ae_restrict_mem measurableSet_Icc] with s hs _
    exact hs
  have hFpos : ∀ t ∈ Icc a b, 0 ≤ F t := by
    intro t ht
    exact add_nonneg (hfpos t ht) (hIpos t ht)
  have hFderiv : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      deriv F t ≤ g t * F t := by
    filter_upwards [hf.ae_differentiableAt.filter_mono ae_restrict_le,
      hIderiv, hdiff, hgpos,
      ae_restrict_mem measurableSet_Icc] with t hfd hIt hineq hgt ht
    have hfd' : HasDerivAt f (deriv f t) t := by
      have hmem : t ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ht
      exact (hfd hmem).hasDerivAt
    have hF' := hfd'.add hIt
    have hFderivValue : deriv F t = deriv f t + d t := by
      change deriv (f + I) t = deriv f t + d t
      rw [hF'.deriv]
    rw [hFderivValue]
    have hle : f t ≤ F t := by
      dsimp [F]
      linarith only [hIpos t ht]
    have hmul := mul_le_mul_of_nonneg_left hle hgt
    linarith only [hineq, hmul]
  have hbound := lps_ac_gronwall hab hFac hg hgpos hFderiv
  intro t ht
  have hItA : I a = 0 := by simp [I]
  simpa [F, I, hItA] using hbound t ht

/-- The finite Serrin branch integrates the differential inequality with its
critical `L^s` time coefficient (`lem:lps-H1-estimate`). -/
theorem lps_h1_finite_branch_gronwall {a b C : ℝ} {f d m : ℝ → ℝ}
    (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : IntegrableOn d (Icc a b) volume)
    (hdpos : ∀ᵐ t ∂(volume.restrict (Icc a b)), 0 ≤ d t)
    (hm : IntegrableOn m (Icc a b) volume)
    (hmpos : ∀ᵐ t ∂(volume.restrict (Icc a b)), 0 ≤ m t)
    (hC : 0 ≤ C)
    (hfpos : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hDiff : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      deriv f t + d t ≤ C * m t * f t) :
    ∀ t ∈ Icc a b,
      f t + ∫ s in a..t, d s ≤
        f a * Real.exp (C * ∫ s in a..t, m s) := by
  let g : ℝ → ℝ := fun t => C * m t
  have hg : IntegrableOn g (Icc a b) volume := by
    exact hm.const_mul C
  have hgpos : ∀ᵐ t ∂(volume.restrict (Icc a b)), 0 ≤ g t := by
    filter_upwards [hmpos] with t ht
    exact mul_nonneg hC ht
  have hDiff' : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      deriv f t + d t ≤ g t * f t := by
    filter_upwards [hDiff] with t ht
    simpa [g, mul_assoc] using ht
  have hbound := lps_ac_gronwall_dissipation hab hf hd hdpos hg hgpos hfpos hDiff'
  intro t ht
  have hInt : (∫ s in a..t, g s) = C * ∫ s in a..t, m s := by
    simp [g, intervalIntegral.integral_const_mul]
  have hboundt := hbound t ht
  rw [hInt] at hboundt
  exact hboundt

/-- The endpoint Serrin branch integrates with the square of the spatial
essential supremum (`lem:lps-H1-estimate`). -/
theorem lps_h1_endpoint_branch_gronwall {a b : ℝ} {f d m : ℝ → ℝ}
    (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : IntegrableOn d (Icc a b) volume)
    (hdpos : ∀ᵐ t ∂(volume.restrict (Icc a b)), 0 ≤ d t)
    (hm : IntegrableOn m (Icc a b) volume)
    (hmpos : ∀ᵐ t ∂(volume.restrict (Icc a b)), 0 ≤ m t)
    (hfpos : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hDiff : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      deriv f t + d t ≤ m t * f t) :
    ∀ t ∈ Icc a b,
      f t + ∫ s in a..t, d s ≤
        f a * Real.exp (∫ s in a..t, m s) := by
  exact lps_ac_gronwall_dissipation hab hf hd hdpos hm hmpos hfpos hDiff

end ESS.LPS

end
