/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumGood

/-!
# The forced regularized momentum identity

`eq:reg-momentum-forced`: the forced regularized velocity, its weak gradient
and the pressure `P[J_εu_ε ⊗ u_ε] + p_f` satisfy the weak momentum identity
against every smooth compactly supported test on positive times. The space-time
integral is an integral over the time slices, each slice is a combination of
frequency pairings, and their time integral vanishes by the frequency weak form
of the forced mild equation.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

theorem exists_time_bound {φ : Vec3 × ℝ → Vec3} (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ tsupport φ, z.2 ∈ Ioo 0 T := by
  obtain ⟨b, hb⟩ := (hφc.image continuous_snd).bddAbove
  refine ⟨max b 0 + 1, by positivity, fun z hz => ⟨(hφs hz).2, ?_⟩⟩
  have h1 : z.2 ≤ b := hb ⟨z, hz, rfl⟩
  have h2 := le_max_left b 0
  linarith only [h1, h2]

theorem fderiv_eq_zero_of_notMem_tsupport' {φ : Vec3 × ℝ → Vec3} {z : Vec3 × ℝ}
    (hz : z ∉ tsupport φ) : fderiv ℝ φ z = 0 := by
  by_contra h
  exact hz (support_fderiv_subset ℝ h)

theorem forcedMomentumIntegrand_eq_zero (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) (f : ParabolicPoint → Vec3)
    (hf : CKN.IsLocallySquareIntegrableForce f) {φ : Vec3 × ℝ → Vec3} {z : Vec3 × ℝ}
    (hz : z ∉ tsupport φ) : forcedMomentumIntegrand ρ ε hε ha f hf φ z = 0 := by
  have hd := fderiv_eq_zero_of_notMem_tsupport' hz
  have h0 : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
  simp [forcedMomentumIntegrand, timeDeriv, spaceDeriv, stDiv, hd, h0]

theorem integrable_lam_testHat_sq {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (T : ℝ) :
    Integrable (fun p : L2Vec3 × ℝ => (forcedFourierLam p.1 * ‖testHat φ p‖) ^ 2)
      (volume.prod (volume.restrict (Ioc 0 T))) := by
  have hj : ∀ j : Fin 3, Integrable
      (fun p => ‖testHat (spaceDeriv j (spaceDeriv j φ)) p‖ ^ 2)
      (volume.prod (volume.restrict (Ioc 0 T))) := fun j =>
    integrable_testHat_sq (contDiff_spaceDeriv (contDiff_spaceDeriv hφ j) j)
      (hasCompactSupport_spaceDeriv (hasCompactSupport_spaceDeriv hφc j) j) T
  refine Integrable.mono' ((((hj 0).add (hj 1)).add (hj 2)).const_mul 3) ?_
    (Eventually.of_forall fun p => ?_)
  · have hc := continuous_testHat hφ hφc
    have hl : Continuous fun p : L2Vec3 × ℝ => forcedFourierLam p.1 := by
      unfold forcedFourierLam; fun_prop
    exact ((hl.mul hc.norm).pow 2).aestronglyMeasurable
  · have heq : forcedFourierLam p.1 * ‖testHat φ p‖ =
        ‖∑ j : Fin 3, testHat (spaceDeriv j (spaceDeriv j φ)) p‖ := by
      rw [← norm_lam_smul, lam_smul_testHat hφ hφc p, norm_neg]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), heq, Fin.sum_univ_three]
    simp only [Pi.add_apply]
    set A := testHat (spaceDeriv 0 (spaceDeriv 0 φ)) p
    set B := testHat (spaceDeriv 1 (spaceDeriv 1 φ)) p
    set C := testHat (spaceDeriv 2 (spaceDeriv 2 φ)) p
    have htri : ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := norm_add₃_le
    have h0 := norm_nonneg (A + B + C)
    have ha := norm_nonneg A
    have hb := norm_nonneg B
    have hc := norm_nonneg C
    nlinarith only [htri, h0, ha, hb, hc, sq_nonneg (‖A‖ - ‖B‖), sq_nonneg (‖B‖ - ‖C‖),
      sq_nonneg (‖A‖ - ‖C‖)]

theorem integrable_six_sum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A1 A2 A3 A4 A5 A6 : α → ℝ} (h1 : Integrable A1 μ) (h2 : Integrable A2 μ)
    (h3 : Integrable A3 μ) (h4 : Integrable A4 μ) (h5 : Integrable A5 μ) (h6 : Integrable A6 μ) :
    Integrable (fun z => -A1 z - A2 z + A3 z - (A4 z + A5 z) - A6 z) μ := by
  have j1 : Integrable (fun z => -A1 z) μ := h1.neg
  have j2 : Integrable (fun z => -A1 z - A2 z) μ := j1.sub h2
  have j3 : Integrable (fun z => -A1 z - A2 z + A3 z) μ := j2.add h3
  have j45 : Integrable (fun z => A4 z + A5 z) μ := h4.add h5
  have j5 : Integrable (fun z => -A1 z - A2 z + A3 z - (A4 z + A5 z)) μ := j3.sub j45
  exact j5.sub h6

theorem integrable_forcedMomentumIntegrand (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) {f : ParabolicPoint → Vec3}
    (hf : CKN.IsLocallySquareIntegrableForce f) {φ : Vec3 × ℝ → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) {T : ℝ} (hT : 0 < T) :
    Integrable (forcedMomentumIntegrand ρ ε hε ha f hf φ)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  have h1 := integrable_time_term ρ ε hε ha hf hφ hφc T
  have h2 := integrable_transport_term ρ ε hε ha hf hφ hφc T
  have h3 := integrable_viscous_term ρ ε hε ha hf hφ hφc T hT.le
  have h4 := integrable_quadPressure_term ρ ε hε ha hf hφ hφc T
  have h5 := integrable_forcePressure_term hf hφ hφc T hT
  have h6 := integrable_force_term hf hφ hφc T hT
  have k := integrable_six_sum h1 h2 h3 h4 h5 h6
  refine k.congr (Eventually.of_forall fun z => ?_)
  simp only [forcedMomentumIntegrand]
  ring

/-- The frequency weak form of the forced regularized solution against the
transforms of a test. -/
theorem forcedReg_weak_form (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) {f : ParabolicPoint → Vec3}
    (hf : CKN.IsLocallySquareIntegrableForce f) {φ : Vec3 × ℝ → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) {T : ℝ} (hT : 0 < T)
    (hTs : ∀ z ∈ tsupport φ, z.2 ∈ Ioo 0 T) :
    ∫ t in Ioo 0 T, ∫ x, forcedMomentumIntegrand ρ ε hε ha f hf φ (x, t) = 0 := by
  obtain ⟨B, Fh, Hh, hBm, hFhm, hHhm, hY2, hF2, hH2, hZ, hFrep, hHrep⟩ :=
    forcedReg_fourier_representation ρ ε hε ha hf hT.le
  have hslice0 : ∀ s : ℝ, s ∉ Ioo 0 T → ∀ x, φ (x, s) = 0 := fun s hs x =>
    image_eq_zero_of_notMem_tsupport fun h => hs (hTs _ h)
  have hΦtc := continuous_testHat (contDiff_timeDeriv hφ) (hasCompactSupport_timeDeriv hφc)
  obtain ⟨hAi, hBi, hCi, hDi, hid⟩ := forcedFourierRep_weak_identity hBm hFhm hHhm hT.le
    (continuous_testHat hφ hφc).measurable hΦtc.measurable (hasDerivAt_testHat hφ hφc)
    (fun ξ => hΦtc.comp (continuous_const.prodMk continuous_id))
    (fun ξ => testHat_eq_zero (hslice0 0 fun h => lt_irrefl _ h.1) ξ)
    (fun ξ => testHat_eq_zero (hslice0 T fun h => lt_irrefl _ h.2) ξ)
    hY2 hF2 hH2 (integrable_testHat_sq hφ hφc T)
    (integrable_testHat_sq (contDiff_timeDeriv hφ) (hasCompactSupport_timeDeriv hφc) T)
    (integrable_lam_testHat_sq hφ hφc T)
  set Y := forcedFourierRep B Fh Hh with hYdef
  set A : ℝ → ℝ := fun t => ∫ ξ, (inner ℂ (Y (ξ, t)) (testHat (timeDeriv φ) (ξ, t))).re with hA
  set Bt : ℝ → ℝ := fun t => ∫ ξ, (inner ℂ (Y (ξ, t))
    (((forcedFourierLam ξ : ℝ) : ℂ) • testHat φ (ξ, t))).re with hB
  set C : ℝ → ℝ := fun t => ∫ ξ, (inner ℂ (-((2 * Real.pi * Complex.I : ℂ) •
    tensorDivergenceLinear ξ (Fh (ξ, t)))) (leraySymbol ξ (testHat φ (ξ, t)))).re with hC
  set D : ℝ → ℝ := fun t => ∫ ξ, (inner ℂ (Hh (ξ, t)) (leraySymbol ξ (testHat φ (ξ, t)))).re
    with hD
  have hgood : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
      ∫ x, forcedMomentumIntegrand ρ ε hε ha f hf φ (x, t) = -A t + Bt t - C t - D t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self
        (forcedRegRep_weakGradient ρ ε hε ha hf),
      ae_forcedRegGrad_slice ρ ε hε ha hf hT.le, ae_forcedForceMod_slice hf hT,
      ae_forcePressure_slice hf hT] with t ht hw hDu hFF hPF
    obtain ⟨hF2t, hFft⟩ := hFF
    obtain ⟨hpfl, hft, hpf⟩ := hPF
    exact integral_forcedMomentumIntegrand_slice ρ ε hε ha hf hφ hφc (hZ t ⟨ht.1, ht.2.le⟩)
      (hFrep t ⟨ht.1, ht.2.le⟩) (hHrep t) hw hDu hF2t hFft hft hpf hpfl
  have hIoo : (volume : Measure ℝ).restrict (Ioo 0 T) = (volume : Measure ℝ).restrict (Ioc 0 T) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [integral_congr_ae hgood, hIoo]
  have j1 : IntegrableOn (fun t => -A t) (Ioc 0 T) := hAi.neg
  have j2 : IntegrableOn (fun t => -A t + Bt t) (Ioc 0 T) := j1.add hBi
  have j3 : IntegrableOn (fun t => -A t + Bt t - C t) (Ioc 0 T) := j2.sub hCi
  rw [integral_sub j3 hDi, integral_sub j2 hCi, integral_add j1 hBi, integral_neg]
  linarith only [hid]

/-- The weak momentum identity of the forced regularized solution. -/
theorem integral_forcedMomentumIntegrand_eq_zero (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) {f : ParabolicPoint → Vec3}
    (hf : CKN.IsLocallySquareIntegrableForce f) {φ : Vec3 × ℝ → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      forcedMomentumIntegrand ρ ε hε ha f hf φ z = 0 := by
  obtain ⟨T, hT, hTs⟩ := exists_time_bound hφc hφs
  have hvan : ∀ z : Vec3 × ℝ, z.2 ∉ Ioo 0 T → forcedMomentumIntegrand ρ ε hε ha f hf φ z = 0 :=
    fun z hz => forcedMomentumIntegrand_eq_zero ρ ε hε ha f hf fun h => hz (hTs z h)
  have e1 : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      forcedMomentumIntegrand ρ ε hε ha f hf φ z =
      ∫ z : ParabolicPoint, forcedMomentumIntegrand ρ ε hε ha f hf φ z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      hvan z fun h => hz ⟨mem_univ _, h.1⟩
  have e2 : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      forcedMomentumIntegrand ρ ε hε ha f hf φ z =
      ∫ z : ParabolicPoint, forcedMomentumIntegrand ρ ε hε ha f hf φ z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      hvan z fun h => hz ⟨mem_univ _, h⟩
  rw [e1, ← e2, integral_slab_eq_prod (forcedMomentumIntegrand ρ ε hε ha f hf φ),
    integral_prod_symm _ (integrable_forcedMomentumIntegrand ρ ε hε ha hf hφ hφc hT)]
  exact forcedReg_weak_form ρ ε hε ha hf hφ hφc hT hTs

theorem forcedRegPressure_apply (ρ : RegMollifierProfile) {a : Vec3 → Vec3} (ha : IsInJ a)
    {f : ParabolicPoint → Vec3} (hf : IsLocallySquareIntegrableForce f) {ε : ℝ} (hε : 0 < ε)
    (z : ParabolicPoint) :
    forcedRegPressure ρ a ha f hf ε z =
      forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) z + forcePressure f hf z := by
  unfold forcedRegPressure
  simp only [hε, ↓reduceDIte]

theorem timePartial_eq_timeDeriv' {φ : ParabolicPoint → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => φ z))
    (i : Fin 3) (z : ParabolicPoint) : timePartial (fun y => φ y i) z = timeDeriv φ z i :=
  timePartial_eq_timeDeriv hφ i z

theorem spatialPartial_eq_spaceDeriv' {φ : ParabolicPoint → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => φ z))
    (i j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun y => φ y i) j z = spaceDeriv j φ z i :=
  spatialPartial_eq_spaceDeriv hφ i j z

/-- `eq:reg-momentum-forced`: the weak momentum identity of the forced
regularized solutions, in the form used by the limiting argument of
`thm:leray-forced`. -/
theorem forcedRegMomentum (ρ : RegMollifierProfile) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (ε : ℝ) (hε : 0 < ε) (φ : ParabolicPoint → Vec3),
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε
                (forcedRegVelocity ρ a ha f hf ε) z j * forcedRegVelocity ρ a ha f hf ε z i *
                spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              forcedRegGradient ρ a ha f hf ε z i j * spatialPartial (fun y => φ y i) j z
          - forcedRegPressure ρ a ha f hf ε z *
              (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
          - ∑ i : Fin 3, f z i * φ z i = 0 := by
  intro a ha f hf ε hε φ hφtest
  obtain ⟨hφ, hφc, hφs⟩ := hφtest
  refine (integral_congr_ae (μ := (volume : Measure ParabolicPoint).restrict
    (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) (Eventually.of_forall fun z => ?_)).trans
    (integral_forcedMomentumIntegrand_eq_zero ρ ε hε ha hf hφ hφc hφs)
  simp only [forcedRegGradient, forcedRegVelocity_eq ρ ha hf hε, forcedRegPressure_apply ρ ha hf hε,
    timePartial_eq_timeDeriv' hφ, spatialPartial_eq_spaceDeriv' hφ, forcedMomentumIntegrand,
    stDiv]

end CKN.Leray

end
