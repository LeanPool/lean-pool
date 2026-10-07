/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainDeriv
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyScalarEnergy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim

/-!
# Zero initial trace for solutions vanishing near the initial time

A square-integrable distributional solution of `∂ₜ u - Δ u = div H + f` on
`ℝ³ × (a, b)` that vanishes for `t < a + δ` has, for every spatial test `ψ`, a
spatial pairing `t ↦ ∫ u(x, t) ψ(x) dx` with a continuous version on `[a, b]`
vanishing at `a`: the pairing has an integrable distributional time
derivative. This is the zero initial trace used with the energy estimate of
`lem:localized-vorticity-energy` in the proof of `lem:local-heat-gain`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

section ProductTest

variable {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}

/-- The time derivative of a separated test `ψ(x) θ(t)`. -/
theorem separatedTest_timePartial (hθ : Differentiable ℝ θ) (p : Vec3 × ℝ) :
    timePartial (fun q : Vec3 × ℝ => ψ q.1 * θ q.2) p = ψ p.1 * deriv θ p.2 := by
  change (fderiv ℝ (fun s : ℝ => ψ p.1 * θ s) p.2) 1 = _
  rw [fderiv_const_mul (hθ p.2)]
  simp

/-- The spatial derivative of a separated test `ψ(x) θ(t)`. -/
theorem separatedTest_spatialPartial (hψ : Differentiable ℝ ψ) (j : Fin 3) (p : Vec3 × ℝ) :
    spatialPartial (fun q : Vec3 × ℝ => ψ q.1 * θ q.2) j p = θ p.2 * spatialDeriv ψ j p.1 := by
  change (fderiv ℝ (fun y : Vec3 => ψ y * θ p.2) p.1) (basisVec j) = _
  rw [fderiv_mul_const (hψ p.1)]
  simp [spatialDeriv]

/-- The second spatial derivative of a separated test `ψ(x) θ(t)`. -/
theorem separatedTest_spatialSecondPartial (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (j : Fin 3)
    (p : Vec3 × ℝ) :
    spatialSecondPartial (fun q : Vec3 × ℝ => ψ q.1 * θ q.2) j j p =
      θ p.2 * spatialDeriv (spatialDeriv ψ j) j p.1 := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hdψ : Differentiable ℝ (spatialDeriv ψ j) :=
    (contDiff_spatialDeriv_smooth hψ j).differentiable (by simp)
  have h1 : (fun w : ParabolicPoint =>
      spatialPartial (fun q : Vec3 × ℝ => ψ q.1 * θ q.2) j w) =
      fun w : ParabolicPoint => θ w.2 * spatialDeriv ψ j w.1 :=
    funext fun w => separatedTest_spatialPartial hψd j w
  unfold spatialSecondPartial
  rw [h1]
  change (fderiv ℝ (fun y : Vec3 => θ p.2 * spatialDeriv ψ j y) p.1) (basisVec j) = _
  rw [fderiv_const_mul (hdψ p.1)]
  simp [spatialDeriv]

end ProductTest

/-- `(x, t) ↦ g(x)` is square integrable on a slab for square integrable `g`. -/
theorem memLp_slab_of_space {a b : ℝ} {g : Vec3 → ℝ} (hg : MemLp g 2 volume) :
    MemLp (fun p : Vec3 × ℝ => g p.1) 2 (volume.restrict (vlSlab a b)) := by
  rw [vlSlab_measure]
  have hm : AEStronglyMeasurable (fun p : Vec3 × ℝ => g p.1)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    hg.aestronglyMeasurable.comp_fst
  rw [memLp_two_iff_integrable_sq hm]
  have h1 : Integrable (fun x : Vec3 => g x ^ 2) volume := hg.integrable_sq
  have h2 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo a b)) :=
    integrable_const _
  have h := h1.mul_prod h2
  simpa using h

/-- Continuous compactly supported spatial functions are square integrable on
slabs. -/
theorem memLp_slab_of_test {a b : ℝ} {g : Vec3 → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    MemLp (fun p : Vec3 × ℝ => g p.1) 2 (volume.restrict (vlSlab a b)) :=
  memLp_slab_of_space (hg.memLp_of_hasCompactSupport hgc)

/-- A function on `(a, b)` with an integrable distributional derivative that
vanishes near `a` has a continuous version on `[a, b]` vanishing at `a`. -/
theorem exists_continuous_version_zero_trace {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    {P Q : ℝ → ℝ} (hPint : Integrable P (volume.restrict (Ioo a b)))
    (hQint : Integrable Q (volume.restrict (Ioo a b))) (hweakP : HasWeakDerivOn (Ioo a b) P Q)
    (hP0 : ∀ t, t < a + δ → P t = 0) :
    ∃ c : ℝ → ℝ, ContinuousOn c (Icc a b) ∧ c a = 0 ∧
      ∀ᵐ t ∂(volume.restrict (Ioo a b)), c t = P t := by
  -- the continuous version
  have hab' : a ≤ b := hab.le
  have ht₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith only [hab], by linarith only [hab]⟩
  obtain ⟨C, hC⟩ := exists_ae_eq_const_add_intervalIntegral_of_weakDeriv hab ht₀
    ((show IntegrableOn P (Ioo a b) volume from hPint).locallyIntegrableOn)
    ((show IntegrableOn Q (Ioo a b) volume from hQint).locallyIntegrableOn) hweakP
  let c : ℝ → ℝ := fun t => C + ∫ s in (a + b) / 2..t, Q s
  have hQii : IntervalIntegrable Q volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab']
    exact (integrableOn_Ioc_iff_integrableOn_Ioo).2 hQint
  have hc : ContinuousOn c (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hQii
      (by rw [uIcc_of_le hab']; exact Ioo_subset_Icc_self ht₀)
    rw [uIcc_of_le hab'] at h
    exact continuousOn_const.add h
  have hcP : ∀ᵐ t ∂(volume.restrict (Ioo a b)), c t = P t := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hC] with t ht htI
    exact (ht htI).symm
  refine ⟨c, hc, ?_, hcP⟩
  -- the value at `a`
  have ha' : a < min (a + δ) b := lt_min (by linarith only [hδ]) hab
  have hc0 : c =ᵐ[volume.restrict (Icc a (min (a + δ) b))] fun _ => 0 := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := a) (b := min (a + δ) b)),
      Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    have hsub : Ioo a (min (a + δ) b) ⊆ Ioo a b := Ioo_subset_Ioo_right (min_le_right _ _)
    have hcP' := ae_restrict_of_ae_restrict_of_subset hsub hcP
    rw [ae_restrict_iff' measurableSet_Ioo] at hcP'
    filter_upwards [hcP'] with t ht htI
    rw [ht htI]
    have hlt : t < a + δ := htI.2.trans_le (min_le_left _ _)
    exact hP0 t hlt
  have heq := Measure.eqOn_of_ae_eq hc0 (hc.mono (Icc_subset_Icc_right (min_le_right _ _)))
    continuousOn_const (by rw [interior_Icc, closure_Ioo ha'.ne])
  exact heq (left_mem_Icc.2 ha'.le)

/-- A distributional solution on a slab vanishing near the initial time has a
zero initial trace. -/
theorem heatSolution_trace_zero {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    {u f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (vlSlab a b)))
    (hH : ∀ j, MemLp (H j) 2 (volume.restrict (vlSlab a b)))
    (hf : MemLp f 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, u p * (-CKN.timePartial φ p -
          ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p) =
        ∫ p in vlSlab a b, (-(∑ j : Fin 3, H j p * CKN.spatialPartial φ j p) + f p * φ p))
    (hzero : ∀ p : Vec3 × ℝ, p.2 < a + δ → u p = 0) :
    ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ c : ℝ → ℝ, ContinuousOn c (Icc a b) ∧ c a = ∫ x, (fun _ : Vec3 => (0 : ℝ)) x * ψ x ∧
        ∀ᵐ t ∂(volume.restrict (Ioo a b)), c t = ∫ x, u (x, t) * ψ x := by
  intro ψ hψ hψc
  have hμ : (volume : Measure (Vec3 × ℝ)).restrict (vlSlab a b) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) := vlSlab_measure a b
  -- the spatial factors
  let Δψ : Vec3 → ℝ := fun x => ∑ j : Fin 3, spatialDeriv (spatialDeriv ψ j) j x
  have hΔψ : Continuous Δψ := continuous_finsetSum _ fun j _ =>
    (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hψ j) j).continuous
  have hΔψc : HasCompactSupport Δψ := by
    refine hψc.mono' fun x hx => ?_
    by_contra hxt
    apply hx
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 : x ∉ tsupport (spatialDeriv ψ j) := fun h =>
      hxt (tsupport_fderiv_apply_subset ℝ (basisVec j) h)
    exact image_eq_zero_of_notMem_tsupport fun h =>
      h1 (tsupport_fderiv_apply_subset ℝ (basisVec j) h)
  have hdψ (j : Fin 3) : Continuous (spatialDeriv ψ j) :=
    (contDiff_spatialDeriv_smooth hψ j).continuous
  have hdψc (j : Fin 3) : HasCompactSupport (spatialDeriv ψ j) :=
    hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  -- the pairing and its derivative
  let P : ℝ → ℝ := fun t => ∫ x, u (x, t) * ψ x
  let q : Vec3 × ℝ → ℝ := fun p =>
    u p * Δψ p.1 - ∑ j : Fin 3, H j p * spatialDeriv ψ j p.1 + f p * ψ p.1
  let Q : ℝ → ℝ := fun t => ∫ x, q (x, t)
  have huψ : Integrable (fun p : Vec3 × ℝ => u p * ψ p.1) (volume.restrict (vlSlab a b)) :=
    hu.integrable_mul (memLp_slab_of_test hψ.continuous hψc)
  have i1 : Integrable (fun p : Vec3 × ℝ => u p * Δψ p.1) (volume.restrict (vlSlab a b)) :=
    hu.integrable_mul (memLp_slab_of_test hΔψ hΔψc)
  have i2 : Integrable (fun p : Vec3 × ℝ => ∑ j : Fin 3, H j p * spatialDeriv ψ j p.1)
      (volume.restrict (vlSlab a b)) :=
    integrable_finsetSum _ fun j _ =>
      (hH j).integrable_mul (memLp_slab_of_test (hdψ j) (hdψc j))
  have i3 : Integrable (fun p : Vec3 × ℝ => f p * ψ p.1) (volume.restrict (vlSlab a b)) :=
    hf.integrable_mul (memLp_slab_of_test hψ.continuous hψc)
  have hq : Integrable q (volume.restrict (vlSlab a b)) := (i1.sub i2).add i3
  rw [hμ] at huψ hq
  have hPint : Integrable P (volume.restrict (Ioo a b)) := huψ.integral_prod_right
  have hQint : Integrable Q (volume.restrict (Ioo a b)) := hq.integral_prod_right
  -- the weak derivative
  have hweakP : HasWeakDerivOn (Ioo a b) P Q := by
    intro θ ⟨hθ, hθc, hθI⟩
    have hθd : Differentiable ℝ θ := hθ.differentiable (by simp)
    let φ : Vec3 × ℝ → ℝ := fun p => ψ p.1 * θ p.2
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := (hψ.comp contDiff_fst).mul (hθ.comp contDiff_snd)
    have hφc : HasCompactSupport φ := by
      refine HasCompactSupport.intro (hψc.isCompact.prod hθc.isCompact) fun p hp => ?_
      rcases not_and_or.1 hp with h | h
      · simp [φ, image_eq_zero_of_notMem_tsupport h]
      · simp [φ, image_eq_zero_of_notMem_tsupport h]
    have hφV : tsupport φ ⊆ spaceTimeSet (univ : Set Vec3) (Ioo a b) := by
      have hsupp : Function.support φ ⊆ (univ : Set Vec3) ×ˢ tsupport θ := by
        intro p hp
        refine ⟨mem_univ _, subset_tsupport θ fun h => hp ?_⟩
        simp [φ, h]
      exact (closure_minimal hsupp (isClosed_univ.prod (isClosed_tsupport θ))).trans
        (prod_mono subset_rfl hθI)
    have hw := hweak φ ⟨hφ, hφc, hφV⟩
    -- the integrands
    let Lf : Vec3 × ℝ → ℝ := fun p =>
      u p * (-CKN.timePartial φ p - ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p)
    let Rf : Vec3 × ℝ → ℝ := fun p =>
      -(∑ j : Fin 3, H j p * CKN.spatialPartial φ j p) + f p * φ p
    have hφt : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => timePartial φ p) :=
      vorticityHeatSmooth_timePartial_contDiff hφ
    have hφj (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => spatialPartial φ j p) :=
      vorticityHeatSmooth_spatialPartial_contDiff hφ j
    have hφjj (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : Vec3 × ℝ => spatialSecondPartial φ j j p) :=
      vorticityHeatSmooth_spatialPartial_contDiff (hφj j) j
    have hLf : Integrable Lf (volume.restrict (vlSlab a b)) := by
      have hc : Continuous (fun p : Vec3 × ℝ =>
          -timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) :=
        hφt.continuous.neg.sub (continuous_finsetSum _ fun j _ => (hφjj j).continuous)
      have hcs : HasCompactSupport (fun p : Vec3 × ℝ =>
          -timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) := by
        refine hφc.mono' fun p hp => ?_
        by_contra hpt
        apply hp
        simp only [CKN.timePartial_eq_zero_off_tsupport hpt,
          fun j => CKN.spatialSecondPartial_eq_zero_off_tsupport hpt j j,
          Finset.sum_const_zero, neg_zero, sub_zero]
      exact hu.integrable_mul (memLp_two_restrict_of_test hc hcs _)
    have hRf : Integrable Rf (volume.restrict (vlSlab a b)) := by
      have h1 : Integrable (fun p => ∑ j : Fin 3, H j p * CKN.spatialPartial φ j p)
          (volume.restrict (vlSlab a b)) :=
        integrable_finsetSum _ fun j _ => (hH j).integrable_mul
          (memLp_two_restrict_of_test (hφj j).continuous
            (CKN.hasCompactSupport_spatialPartial hφc j) _)
      have h2 : Integrable (fun p => f p * φ p) (volume.restrict (vlSlab a b)) :=
        hf.integrable_mul (memLp_two_restrict_of_test hφ.continuous hφc _)
      exact h1.neg.add h2
    -- pointwise form
    have hG (p : Vec3 × ℝ) : Lf p - Rf p = -(u p * ψ p.1 * deriv θ p.2 + θ p.2 * q p) := by
      simp only [Lf, Rf, q, Δψ, φ]
      rw [separatedTest_timePartial hθd p]
      simp only [fun j => separatedTest_spatialSecondPartial (θ := θ) hψ j p,
        fun j => separatedTest_spatialPartial (θ := θ) (hψ.differentiable (by simp)) j p]
      simp only [Fin.sum_univ_three]
      ring
    have hGint : Integrable (fun p => u p * ψ p.1 * deriv θ p.2 + θ p.2 * q p)
        (volume.restrict (vlSlab a b)) := by
      have h := (hLf.sub hRf).neg
      refine h.congr (ae_of_all _ fun p => ?_)
      simp only [Pi.neg_apply, Pi.sub_apply]
      rw [hG p, neg_neg]
    have hGzero : ∫ p in vlSlab a b, (u p * ψ p.1 * deriv θ p.2 + θ p.2 * q p) = 0 := by
      have h1 : ∫ p in vlSlab a b, (u p * ψ p.1 * deriv θ p.2 + θ p.2 * q p) =
          -∫ p in vlSlab a b, (Lf p - Rf p) := by
        rw [← integral_neg]
        exact integral_congr_ae (ae_of_all _ fun p => by
          change u p * ψ p.1 * deriv θ p.2 + θ p.2 * q p = -(Lf p - Rf p)
          rw [hG p, neg_neg])
      rw [h1, integral_sub hLf hRf]
      change -((∫ p in vlSlab a b, Lf p) - ∫ p in vlSlab a b, Rf p) = 0
      have hw' : ∫ p in vlSlab a b, Lf p = ∫ p in vlSlab a b, Rf p := hw
      rw [hw', sub_self, neg_zero]
    -- Fubini
    rw [hμ] at hGint hGzero
    rw [integral_prod_symm _ hGint] at hGzero
    have hinner : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
        ∫ x, (u (x, t) * ψ x * deriv θ t + θ t * q (x, t)) = P t * deriv θ t + θ t * Q t := by
      filter_upwards [huψ.prod_left_ae, hq.prod_left_ae] with t h1 h2
      rw [integral_add (h1.mul_const _) (h2.const_mul _), integral_mul_const, integral_const_mul]
    rw [integral_congr_ae hinner] at hGzero
    obtain ⟨Cθ, hCθ⟩ := hθ.continuous.bounded_above_of_compact_support hθc
    obtain ⟨Cθ', hCθ'⟩ := (hθ.continuous_deriv (by simp)).bounded_above_of_compact_support
      hθc.deriv
    have hPθ : Integrable (fun t => P t * deriv θ t) (volume.restrict (Ioo a b)) :=
      hPint.mul_bdd (hθ.continuous_deriv (by simp)).aestronglyMeasurable (ae_of_all _ hCθ')
    have hθQ : Integrable (fun t => θ t * Q t) (volume.restrict (Ioo a b)) :=
      hQint.bdd_mul hθ.continuous.aestronglyMeasurable (ae_of_all _ hCθ)
    rw [integral_add hPθ hθQ] at hGzero
    have hQθ : ∫ t in Ioo a b, Q t * θ t = ∫ t in Ioo a b, θ t * Q t :=
      integral_congr_ae (ae_of_all _ fun t => mul_comm _ _)
    change ∫ t in Ioo a b, P t * deriv θ t = -∫ t in Ioo a b, Q t * θ t
    rw [hQθ]
    linarith only [hGzero]
  obtain ⟨c, hc, hca, hcP⟩ := exists_continuous_version_zero_trace hab hδ hPint hQint hweakP
    (fun t ht => by
      have hfun : (fun x : Vec3 => u (x, t) * ψ x) = fun _ => 0 :=
        funext fun x => by rw [hzero (x, t) ht, zero_mul]
      change ∫ x, u (x, t) * ψ x = 0
      rw [hfun, integral_zero])
  exact ⟨c, hc, by simp [hca], hcP⟩

end ESS
