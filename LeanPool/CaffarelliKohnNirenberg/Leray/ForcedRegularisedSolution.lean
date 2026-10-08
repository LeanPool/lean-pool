/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedContraction
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedPairing
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedSolutionJ

/-!
# The forced regularized solution on a bounded interval

The fixed point of the truncated map satisfies the energy balance of
`lem:regularised-forced` without its transport term, since the transport
pairing vanishes. With `2⟨u, f⟩ ≤ |u|² + |f|²` and Grönwall this bounds the
solution independently of the truncation radius, as in
`eq:reg-energy-forced-gronwall`; for a large radius the truncation is
inactive and the fixed point solves `eq:reg-mild-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- Grönwall's inequality in integral form for a continuous function. -/
theorem le_mul_exp_of_le_add_integral {φ : ℝ → ℝ} (hφ : Continuous φ) {A T : ℝ}
    (h : ∀ t ∈ Icc 0 T, φ t ≤ A + ∫ s in Ioc 0 t, φ s) :
    ∀ t ∈ Icc 0 T, φ t ≤ A * Real.exp t := by
  let I : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, φ s
  have hI : ∀ t, HasDerivAt I (φ t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hφ.intervalIntegrable 0 t)
      (hφ.stronglyMeasurableAtFilter _ _) hφ.continuousAt
  let Ψ : ℝ → ℝ := fun t => Real.exp (-t) * (A + I t)
  have hΨ : ∀ t, HasDerivAt Ψ (-Real.exp (-t) * (A + I t) + Real.exp (-t) * φ t) t := by
    intro t
    have h1 : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    have h2 := h1.fun_mul ((hI t).const_add A)
    convert h2 using 1
  have hanti : AntitoneOn Ψ (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
      (fun t _ => (hΨ t).continuousAt.continuousWithinAt)
      (fun t _ => (hΨ t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Icc] at ht
    rw [(hΨ t).deriv]
    have hle := h t (Ioo_subset_Icc_self ht)
    rw [← intervalIntegral.integral_of_le ht.1.le] at hle
    have he := Real.exp_pos (-t)
    nlinarith only [hle, he]
  intro t ht
  have hΨt := hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  have hΨ0 : Ψ 0 = A := by simp [Ψ, I]
  have hle := h t ht
  rw [← intervalIntegral.integral_of_le ht.1] at hle
  rw [hΨ0] at hΨt
  have hexp : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hA : A + I t ≤ A * Real.exp t := by
    have h1 : Real.exp (-t) * (A + I t) ≤ A := hΨt
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le
    calc A + I t = Real.exp (-t) * (A + I t) * Real.exp t := by
          rw [mul_comm (Real.exp (-t)), mul_assoc, hexp, mul_one]
      _ ≤ A * Real.exp t := h2
  exact hle.trans hA

/-- The Stokes Duhamel integral at time `t` depends only on the tensor curve
up to time `t`. -/
theorem regularizedMildStokesIntegral_congr_Icc {F G : ℝ → RealTensorL2} {t : ℝ}
    (hFG : ∀ s ∈ Icc 0 t, F s = G s) :
    regularizedMildStokesIntegral F t = regularizedMildStokesIntegral G t := by
  unfold regularizedMildStokesIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  simp only [regularizedMildStokesIntegrand, hFG s hs]

/-- The right-hand side of `eq:reg-mild-forced` at time `t` depends only on the
tensor curve up to time `t`. -/
theorem forcedMildRHS_congr_Icc (b : RealVectorL2) (h : ℝ → RealVectorL2)
    {F G : ℝ → RealTensorL2} {t : ℝ} (ht : 0 ≤ t) (hFG : ∀ s ∈ Icc 0 t, F s = G s) :
    forcedMildRHS b h F t ht = forcedMildRHS b h G t ht := by
  unfold forcedMildRHS
  rw [regularizedMildStokesIntegral_congr_Icc hFG]

theorem forcedFourierDissipation_nonneg (v : ComplexVectorL2) : 0 ≤ forcedFourierDissipation v :=
  integral_nonneg fun ξ => mul_nonneg (forcedFourierLam_nonneg ξ) (sq_nonneg _)

/-- Square integrability of the frequency gradient from integrability of the
weighted square of the transform. -/
theorem memLp_forcedFourierGradHat_of_integrable (v : ComplexVectorL2)
    (hv : Integrable (fun ξ => forcedFourierLam ξ *
      ‖(Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 v : L2Vec3 → ComplexVec3) ξ‖ ^ 2)) :
    MemLp (forcedFourierGradHat v) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (measurable_forcedFourierGradHat v).aestronglyMeasurable]
  simp_rw [norm_sq_forcedFourierGradHat]
  exact hv

/-- The truncated forced mild map evaluated at an interior time is the
forced mild curve of its tensor curve. -/
theorem forcedMildMap_eq_forcedMildCurve (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) {h : ℝ → RealVectorL2} (hh : StronglyMeasurable h)
    (hH : ∀ T : ℝ, IntegrableOn (fun s => ‖h s‖) (Ioc 0 T)) {R : ℝ} (hR : 0 ≤ R)
    (T : ℝ) (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (hu : forcedMildMap ρ ε hε b hh hH hR T hT u = u) {s : ℝ}
    (hs : s ∈ RegularizedMildTimeInterval T) :
    forcedMildCurve b h (forcedTensorCurve ρ ε hε R T hT u) s = u ⟨s, hs⟩ := by
  unfold forcedMildCurve
  rw [dite_eq_left hs.1]
  conv_rhs => rw [← hu]
  rfl

/-- The energy inequality of the truncated forced solution: the transport
pairing drops out of the energy balance. -/
theorem forcedTruncSolution_energy (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b) {h : ℝ → RealVectorL2}
    (hh : StronglyMeasurable h) (hH2 : ∀ T : ℝ, IntegrableOn (fun s => ‖h s‖ ^ 2) (Ioc 0 T))
    {R : ℝ} (hR : 0 ≤ R) (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (hu : forcedMildMap ρ ε hε b hh (fun T => integrableOn_norm_of_sq hh (hH2 T)) hR T hT u = u)
    {τ : ℝ} (hτ : τ ∈ RegularizedMildTimeInterval T) :
    let v := forcedComplexCurve b (forcedTensorCurve ρ ε hε R T hT u) h
    (∀ᵐ s ∂(volume.restrict (Ioc 0 τ)), MemLp (forcedFourierGradHat (v s)) 2 volume) ∧
    IntegrableOn (fun s => forcedFourierDissipation (v s)) (Ioc 0 τ) ∧
    (∀ s (hs : s ∈ RegularizedMildTimeInterval T), realPartVectorL2 (v s) = u ⟨s, hs⟩) ∧
    ‖u ⟨τ, hτ⟩‖ ^ 2 + 2 * ∫ s in Ioc 0 τ, forcedFourierDissipation (v s) ≤
      ‖b‖ ^ 2 + 2 * ∫ s in Ioc 0 τ, inner ℝ (u (regularizedMildTimeClamp T hT s)) (h s) := by
  intro v
  set hH := fun T => integrableOn_norm_of_sq hh (hH2 T) with hHdef
  set F := forcedTensorCurve ρ ε hε R T hT u with hFdef
  set C := regularizedMildMollifierConstant ρ ε * R ^ 2 with hCdef
  have hC : 0 ≤ C :=
    mul_nonneg (ENNReal.toReal_nonneg : 0 ≤ regularizedMildMollifierConstant ρ ε) (sq_nonneg R)
  have hFm : StronglyMeasurable F :=
    (continuous_forcedTensorCurve ρ ε hε hR T hT u).stronglyMeasurable
  have hFC : ∀ s ∈ Ioc 0 T, ‖F s‖ ≤ C := fun s _ => norm_forcedTensorCurve_le ρ ε hε hR T hT u s
  have hcurve : ∀ s (hs : s ∈ RegularizedMildTimeInterval T),
      forcedMildCurve b h F s = u ⟨s, hs⟩ := fun s hs =>
    forcedMildMap_eq_forcedMildCurve ρ ε hε b hh hH hR T hT u hu hs
  have hre : ∀ s (hs : s ∈ RegularizedMildTimeInterval T),
      realPartVectorL2 (v s) = u ⟨s, hs⟩ := by
    intro s hs
    rw [← hcurve s hs, forcedMildCurve_eq_realPart b hFm hh hs.1
      (fun r hr => hFC r ⟨hr.1, hr.2.trans hs.2⟩) ((hH T).mono_set (Ioc_subset_Ioc_right hs.2))]
  obtain ⟨hae, hDint, hbal⟩ := forcedMild_energy_balance b hb hFm hh hC hFC (hH2 T) hτ.1 hτ.2
  have hmem : ∀ᵐ s ∂(volume.restrict (Ioc 0 τ)), MemLp (forcedFourierGradHat (v s)) 2 volume := by
    filter_upwards [hae] with s hsint
    exact memLp_forcedFourierGradHat_of_integrable _ hsint
  refine ⟨hmem, hDint, hre, ?_⟩
  have hpair : ∫ s in Ioc 0 τ, forcedStokesPairing (v s) (complexifyTensorL2 (F s)) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hmem, ae_restrict_mem measurableSet_Ioc] with s hv hs
    have hsT : s ∈ RegularizedMildTimeInterval T := ⟨hs.1.le, hs.2.trans hτ.2⟩
    have hJ : RegularizedMildJData (realPartVectorL2 (v s)) := by
      rw [hre s hsT, ← hcurve s hsT]
      exact forcedMildCurve_mildJData b hb hFm hh hFC (hH2 T) hs.1.le hsT.2
    have hFs : F s = forcedTruncTensor ρ ε hε R (realPartVectorL2 (v s)) := by
      rw [hre s hsT, hFdef]
      simp only [forcedTensorCurve, regularizedMildTimeClamp_eq_of_mem T hT hsT]
    simp only [Pi.zero_apply]
    rw [hFs]
    exact forcedStokesPairing_truncTensor_eq_zero ρ ε hε _ hv hJ
  rw [hpair, mul_zero, add_zero] at hbal
  have hnorm : ‖u ⟨τ, hτ⟩‖ ^ 2 ≤ ‖v τ‖ ^ 2 := by
    rw [← hre τ hτ]
    exact pow_le_pow_left₀ (norm_nonneg _) (realPartVectorL2_norm_le _) 2
  have hinner : ∫ s in Ioc 0 τ, inner ℝ (forcedMildCurve b h F s) (h s) =
      ∫ s in Ioc 0 τ, inner ℝ (u (regularizedMildTimeClamp T hT s)) (h s) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hsT : s ∈ RegularizedMildTimeInterval T := ⟨hs.1.le, hs.2.trans hτ.2⟩
    rw [hcurve s hsT, regularizedMildTimeClamp_eq_of_mem T hT hsT]
  rw [hinner] at hbal
  linarith only [hbal, hnorm]

/-- The Grönwall bound for the truncated forced solution, independent of the
truncation radius. -/
theorem forcedTruncSolution_norm_sq_le (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b) {h : ℝ → RealVectorL2}
    (hh : StronglyMeasurable h) (hH2 : ∀ T : ℝ, IntegrableOn (fun s => ‖h s‖ ^ 2) (Ioc 0 T))
    {R : ℝ} (hR : 0 ≤ R) (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (hu : forcedMildMap ρ ε hε b hh (fun T => integrableOn_norm_of_sq hh (hH2 T)) hR T hT u = u)
    (t : RegularizedMildTimeInterval T) :
    ‖u t‖ ^ 2 ≤ (‖b‖ ^ 2 + ∫ s in Ioc 0 T, ‖h s‖ ^ 2) * Real.exp t := by
  set φ : ℝ → ℝ := fun s => ‖u (regularizedMildTimeClamp T hT s)‖ ^ 2 with hφdef
  have hφc : Continuous φ :=
    ((u.continuous.comp (regularizedMildTimeClamp_continuous T hT)).norm).pow 2
  have hφs : ∀ s (hs : s ∈ RegularizedMildTimeInterval T), φ s = ‖u ⟨s, hs⟩‖ ^ 2 := by
    intro s hs
    simp only [hφdef, regularizedMildTimeClamp_eq_of_mem T hT hs]
  have hmain : ∀ τ ∈ Icc 0 T, φ τ ≤ (‖b‖ ^ 2 + ∫ s in Ioc 0 T, ‖h s‖ ^ 2) +
      ∫ s in Ioc 0 τ, φ s := by
    intro τ hτ
    obtain ⟨_, _, _, hbal⟩ := forcedTruncSolution_energy ρ ε hε b hb hh hH2 hR T hT u hu hτ
    have hD : 0 ≤ ∫ s in Ioc 0 τ, forcedFourierDissipation
        (forcedComplexCurve b (forcedTensorCurve ρ ε hε R T hT u) h s) :=
      setIntegral_nonneg measurableSet_Ioc fun s _ => forcedFourierDissipation_nonneg _
    have hφint : IntegrableOn φ (Ioc 0 τ) := hφc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hhint : IntegrableOn (fun s => ‖h s‖ ^ 2) (Ioc 0 τ) :=
      (hH2 T).mono_set (Ioc_subset_Ioc_right hτ.2)
    have hinner_int : IntegrableOn (fun s => inner ℝ (u (regularizedMildTimeClamp T hT s)) (h s))
        (Ioc 0 τ) := by
      refine Integrable.mono'
        (((integrableOn_norm_of_sq hh (hH2 T)).mono_set
          (Ioc_subset_Ioc_right hτ.2)).const_mul ‖u‖) ?_ ?_
      · exact ((u.continuous.comp
          (regularizedMildTimeClamp_continuous T hT)).aestronglyMeasurable.inner
            hh.aestronglyMeasurable)
      · refine Eventually.of_forall fun s => ?_
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (u.norm_coe_le_norm _) (norm_nonneg _))
    have hint_le : 2 * ∫ s in Ioc 0 τ, inner ℝ (u (regularizedMildTimeClamp T hT s)) (h s) ≤
        (∫ s in Ioc 0 τ, φ s) + ∫ s in Ioc 0 τ, ‖h s‖ ^ 2 := by
      rw [← integral_const_mul, ← integral_add hφint hhint]
      refine setIntegral_mono_on (hinner_int.const_mul 2) (hφint.add hhint) measurableSet_Ioc
        fun s _ => ?_
      have h1 := real_inner_le_norm (u (regularizedMildTimeClamp T hT s)) (h s)
      simp only [hφdef]
      nlinarith only [h1, sq_nonneg (‖u (regularizedMildTimeClamp T hT s)‖ - ‖h s‖)]
    have hhT : ∫ s in Ioc 0 τ, ‖h s‖ ^ 2 ≤ ∫ s in Ioc 0 T, ‖h s‖ ^ 2 :=
      setIntegral_mono_set (hH2 T) (Eventually.of_forall fun s => sq_nonneg _)
        (Eventually.of_forall (Ioc_subset_Ioc_right hτ.2))
    rw [hφs τ hτ]
    linarith only [hbal, hD, hint_le, hhT]
  have hG := le_mul_exp_of_le_add_integral hφc hmain t t.2
  rw [hφs t.1 t.2] at hG
  exact hG

theorem forcedTensorCurve_eq_clamped (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {R : ℝ}
    (T : ℝ) (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (hbound : ∀ t, ‖u t‖ ≤ R) :
    forcedTensorCurve ρ ε hε R T hT u = regularizedMildClampedTensorTrajectory ρ ε hε T hT u := by
  funext s
  simp only [forcedTensorCurve, regularizedMildClampedTensorTrajectory, forcedTruncTensor,
    forcedTrunc_of_norm_le (hbound _)]

theorem forcedMildMap_eq_self_of_solution (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) {h : ℝ → RealVectorL2} (hh : StronglyMeasurable h)
    (hH : ∀ T : ℝ, IntegrableOn (fun s => ‖h s‖) (Ioc 0 T)) {R : ℝ} (hR : 0 ≤ R)
    (T : ℝ) (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (hu : ∀ t : RegularizedMildTimeInterval T, u t = forcedMildRHS b h
      (regularizedMildClampedTensorTrajectory ρ ε hε T hT u) t.1 t.2.1)
    (hbound : ∀ t, ‖u t‖ ≤ R) :
    forcedMildMap ρ ε hε b hh hH hR T hT u = u := by
  ext1 t
  rw [forcedMildMap_apply, forcedTensorCurve_eq_clamped ρ ε hε T hT u hbound, ← hu t]

/-- Existence of a continuous `L²` solution of `eq:reg-mild-forced` on `[0, T]`
obeying the Grönwall bound `eq:reg-energy-forced-gronwall`. -/
theorem exists_forcedMildSolution (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b) {h : ℝ → RealVectorL2}
    (hh : StronglyMeasurable h) (hH2 : ∀ T : ℝ, IntegrableOn (fun s => ‖h s‖ ^ 2) (Ioc 0 T))
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ u : C(RegularizedMildTimeInterval T, RealVectorL2),
      (∀ t : RegularizedMildTimeInterval T, u t = forcedMildRHS b h
        (regularizedMildClampedTensorTrajectory ρ ε hε T hT u) t.1 t.2.1) ∧
      ∀ t, ‖u t‖ ^ 2 ≤ (‖b‖ ^ 2 + ∫ s in Ioc 0 T, ‖h s‖ ^ 2) * Real.exp T := by
  set E := (‖b‖ ^ 2 + ∫ s in Ioc 0 T, ‖h s‖ ^ 2) * Real.exp T with hEdef
  set R := Real.sqrt E + 1 with hRdef
  have hR : 0 ≤ R := by positivity
  obtain ⟨u, hu, -⟩ := forcedMildMap_existsUnique_fixedPoint ρ ε hε b hh
    (fun T => integrableOn_norm_of_sq hh (hH2 T)) hR T hT
  have hA : 0 ≤ ‖b‖ ^ 2 + ∫ s in Ioc 0 T, ‖h s‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioc fun s _ => sq_nonneg _)
  have hbound : ∀ t, ‖u t‖ ^ 2 ≤ E := by
    intro t
    refine (forcedTruncSolution_norm_sq_le ρ ε hε b hb hh hH2 hR T hT u hu t).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 t.2.2) hA
  have hnorm : ∀ t, ‖u t‖ ≤ R := by
    intro t
    have h1 : ‖u t‖ ≤ Real.sqrt E := Real.le_sqrt_of_sq_le (hbound t)
    linarith only [h1, hRdef]
  refine ⟨u, fun t => ?_, hbound⟩
  conv_lhs => rw [← hu]
  rw [forcedMildMap_apply, forcedTensorCurve_eq_clamped ρ ε hε T hT u hnorm]

/-- Uniqueness of continuous `L²` solutions of `eq:reg-mild-forced` on `[0, T]`. -/
theorem forcedMildSolution_unique (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) {h : ℝ → RealVectorL2} (hh : StronglyMeasurable h)
    (hH : ∀ T : ℝ, IntegrableOn (fun s => ‖h s‖) (Ioc 0 T)) (T : ℝ) (hT : 0 ≤ T)
    (u u' : C(RegularizedMildTimeInterval T, RealVectorL2))
    (hu : ∀ t : RegularizedMildTimeInterval T, u t = forcedMildRHS b h
      (regularizedMildClampedTensorTrajectory ρ ε hε T hT u) t.1 t.2.1)
    (hu' : ∀ t : RegularizedMildTimeInterval T, u' t = forcedMildRHS b h
      (regularizedMildClampedTensorTrajectory ρ ε hε T hT u') t.1 t.2.1) :
    u = u' := by
  set R := max ‖u‖ ‖u'‖ with hRdef
  have hR : 0 ≤ R := le_max_of_le_left (norm_nonneg _)
  obtain ⟨w, -, hw⟩ := forcedMildMap_existsUnique_fixedPoint ρ ε hε b hh hH hR T hT
  have h1 := hw u (forcedMildMap_eq_self_of_solution ρ ε hε b hh hH hR T hT u hu
    fun t => (u.norm_coe_le_norm t).trans (le_max_left _ _))
  have h2 := hw u' (forcedMildMap_eq_self_of_solution ρ ε hε b hh hH hR T hT u' hu'
    fun t => (u'.norm_coe_le_norm t).trans (le_max_right _ _))
  rw [h1, h2]

/-- The energy inequality `eq:reg-energy-forced` for the solution on
`[0, T]`, with the frequency dissipation of a complex solution curve whose
real part is the solution. -/
theorem forcedMildSolution_energy (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b) {h : ℝ → RealVectorL2}
    (hh : StronglyMeasurable h) (hH2 : ∀ T : ℝ, IntegrableOn (fun s => ‖h s‖ ^ 2) (Ioc 0 T))
    (T : ℝ) (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (hu : ∀ t : RegularizedMildTimeInterval T, u t = forcedMildRHS b h
      (regularizedMildClampedTensorTrajectory ρ ε hε T hT u) t.1 t.2.1) :
    ∃ v : ℝ → ComplexVectorL2,
      (∀ s (hs : s ∈ RegularizedMildTimeInterval T), realPartVectorL2 (v s) = u ⟨s, hs⟩) ∧
      (∀ᵐ s ∂(volume.restrict (Ioc 0 T)), MemLp (forcedFourierGradHat (v s)) 2 volume) ∧
      IntegrableOn (fun s => forcedFourierDissipation (v s)) (Ioc 0 T) ∧
      ∀ τ (hτ : τ ∈ RegularizedMildTimeInterval T),
        ‖u ⟨τ, hτ⟩‖ ^ 2 + 2 * ∫ s in Ioc 0 τ, forcedFourierDissipation (v s) ≤
          ‖b‖ ^ 2 + 2 * ∫ s in Ioc 0 τ, inner ℝ (u (regularizedMildTimeClamp T hT s)) (h s) := by
  set R := ‖u‖ with hRdef
  have hR : 0 ≤ R := norm_nonneg _
  have hfix := forcedMildMap_eq_self_of_solution ρ ε hε b hh
    (fun T => integrableOn_norm_of_sq hh (hH2 T)) hR T hT u hu (fun t => u.norm_coe_le_norm t)
  obtain ⟨hmem, hint, hre, -⟩ := forcedTruncSolution_energy ρ ε hε b hb hh hH2 hR T hT u hfix
    (τ := T) ⟨hT, le_rfl⟩
  refine ⟨_, hre, hmem, hint, fun τ hτ => ?_⟩
  exact (forcedTruncSolution_energy ρ ε hε b hb hh hH2 hR T hT u hfix hτ).2.2.2

end CKN.Leray

end
