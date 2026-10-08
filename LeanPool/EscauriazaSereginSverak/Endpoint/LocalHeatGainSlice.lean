/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainTrace

/-!
# Weak derivatives at every time for continuous curves

If a space-time family has a distributional spatial derivative on a slab and
its time slices agree almost everywhere with curves continuous in `L²`, then
the curves satisfy the weak derivative relation at every time of the closed
interval: the tested relation is continuous in time and vanishes after
integration against every time test.
-/

public section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Fubini for a square-integrable field against a separated test. -/
theorem integral_slab_separated {a b : ℝ} {F : Vec3 × ℝ → ℝ} {g : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict (vlSlab a b))) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hθ : Continuous θ) (hθb : ∃ C, ∀ t, ‖θ t‖ ≤ C) :
    ∫ p in vlSlab a b, F p * (g p.1 * θ p.2) =
      ∫ t in Ioo a b, θ t * ∫ x, F (x, t) * g x := by
  have hFg : Integrable (fun p : Vec3 × ℝ => F p * g p.1) (volume.restrict (vlSlab a b)) :=
    hF.integrable_mul (memLp_slab_of_test hg hgc)
  obtain ⟨C, hC⟩ := hθb
  have hFgθ : Integrable (fun p : Vec3 × ℝ => F p * (g p.1 * θ p.2))
      (volume.restrict (vlSlab a b)) := by
    have h := hFg.mul_bdd (hθ.comp continuous_snd).aestronglyMeasurable
      (ae_of_all _ fun p => hC p.2)
    refine h.congr (ae_of_all _ fun p => ?_)
    simp only [Function.comp_apply]
    ring
  rw [vlSlab_measure] at hFg hFgθ ⊢
  rw [integral_prod_symm _ hFgθ]
  refine integral_congr_ae ?_
  filter_upwards [hFg.prod_left_ae] with t ht
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  ring

/-- The weak derivative relation for continuous curves at every time. -/
theorem curve_weakPartial_of_slab {a b : ℝ} (hab : a < b) {j : Fin 3}
    {F₁ F₂ : Vec3 × ℝ → ℝ}
    (hF₁ : MemLp F₁ 2 (volume.restrict (vlSlab a b)))
    (hF₂ : MemLp F₂ 2 (volume.restrict (vlSlab a b)))
    (hweak : IsSpaceTimeWeakPartial (vlSlab a b) j F₁ F₂)
    {Z₁ Z₂ : Icc a b → Lp ℝ 2 (volume : Measure Vec3)} (hZ₁ : Continuous Z₁)
    (hZ₂ : Continuous Z₂)
    (h₁ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ ht : t ∈ Icc a b,
      (Z₁ ⟨t, ht⟩ : Vec3 → ℝ) =ᵐ[volume] fun x => F₁ (x, t))
    (h₂ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ ht : t ∈ Icc a b,
      (Z₂ ⟨t, ht⟩ : Vec3 → ℝ) =ᵐ[volume] fun x => F₂ (x, t))
    (ψ : Vec3 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (t : Icc a b) :
    ∫ x, (Z₁ t : Vec3 → ℝ) x * spatialDeriv ψ j x = -∫ x, (Z₂ t : Vec3 → ℝ) x * ψ x := by
  have hdψ : Continuous (spatialDeriv ψ j) := (contDiff_spatialDeriv_smooth hψ j).continuous
  have hdψc : HasCompactSupport (spatialDeriv ψ j) := hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have g₁L : MemLp (spatialDeriv ψ j) 2 volume := hdψ.memLp_of_hasCompactSupport hdψc
  have g₂L : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  -- the tested relation along the curves
  let R : Icc a b → ℝ := fun s =>
    ⟪Z₁ s, g₁L.toLp (spatialDeriv ψ j)⟫ + ⟪Z₂ s, g₂L.toLp ψ⟫
  have hR : Continuous R :=
    (hZ₁.inner continuous_const).add (hZ₂.inner continuous_const)
  have hRint (s : Icc a b) : R s =
      (∫ x, (Z₁ s : Vec3 → ℝ) x * spatialDeriv ψ j x) + ∫ x, (Z₂ s : Vec3 → ℝ) x * ψ x := by
    simp only [R]
    rw [vl_integral_mul_eq_inner (Lp.memLp _) g₁L, vl_integral_mul_eq_inner (Lp.memLp _) g₂L,
      Lp.toLp_coeFn, Lp.toLp_coeFn]
  let R' : ℝ → ℝ := fun s => if hs : s ∈ Icc a b then R ⟨s, hs⟩ else 0
  have hR' : ContinuousOn R' (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine hR.congr fun s => ?_
    simp only [R', Set.domRestrict_apply, s.2, ↓reduceDIte]
  -- vanishing after integration against time tests
  have hzero : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
      tsupport θ ⊆ Ioo a b → ∫ s, θ s • R' s = 0 := by
    intro θ hθ hθc hθI
    have hθb := hθ.continuous.bounded_above_of_compact_support hθc
    have hsupp : ∀ s, s ∉ Ioo a b → θ s • R' s = 0 := fun s hs => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hs (hθI h), zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    have hae : ∀ᵐ s ∂(volume.restrict (Ioo a b)), θ s • R' s =
        θ s * ((∫ x, F₁ (x, s) * spatialDeriv ψ j x) + ∫ x, F₂ (x, s) * ψ x) := by
      rw [ae_restrict_iff' measurableSet_Ioo] at h₁ h₂ ⊢
      filter_upwards [h₁, h₂] with s hs₁ hs₂ hs
      have hsI : s ∈ Icc a b := Ioo_subset_Icc_self hs
      rw [smul_eq_mul]
      congr 1
      simp only [R', hsI, ↓reduceDIte]
      rw [hRint]
      congr 1
      · exact integral_congr_ae (by
          filter_upwards [hs₁ hs hsI] with x hx
          rw [hx])
      · exact integral_congr_ae (by
          filter_upwards [hs₂ hs hsI] with x hx
          rw [hx])
    rw [integral_congr_ae hae]
    -- back to the slab
    let φ : Vec3 × ℝ → ℝ := fun p => ψ p.1 * θ p.2
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := (hψ.comp contDiff_fst).mul (hθ.comp contDiff_snd)
    have hφc : HasCompactSupport φ := by
      refine HasCompactSupport.intro (hψc.isCompact.prod hθc.isCompact) fun p hp => ?_
      rcases not_and_or.1 hp with h | h
      · simp [φ, image_eq_zero_of_notMem_tsupport h]
      · simp [φ, image_eq_zero_of_notMem_tsupport h]
    have hφV : tsupport φ ⊆ vlSlab a b := by
      have hsupp : Function.support φ ⊆ (univ : Set Vec3) ×ˢ tsupport θ := by
        intro p hp
        refine ⟨mem_univ _, subset_tsupport θ fun h => hp ?_⟩
        simp [φ, h]
      exact (closure_minimal hsupp (isClosed_univ.prod (isClosed_tsupport θ))).trans
        (prod_mono subset_rfl hθI)
    have hw := hweak φ hφ hφc hφV
    have e1 : ∫ p in vlSlab a b, F₁ p * spatialPartial φ j p =
        ∫ p in vlSlab a b, F₁ p * (spatialDeriv ψ j p.1 * θ p.2) :=
      integral_congr_ae (ae_of_all _ fun p => by
        change F₁ p * spatialPartial (fun q : Vec3 × ℝ => ψ q.1 * θ q.2) j p = _
        rw [separatedTest_spatialPartial (hψ.differentiable (by simp)) j p, mul_comm (θ p.2)])
    rw [e1, integral_slab_separated hF₁ hdψ hdψc hθ.continuous hθb] at hw
    have e2 : ∫ p in vlSlab a b, F₂ p * φ p = ∫ t in Ioo a b, θ t * ∫ x, F₂ (x, t) * ψ x :=
      integral_slab_separated hF₂ hψ.continuous hψc hθ.continuous hθb
    rw [e2] at hw
    have hi1 : Integrable (fun s => θ s * ∫ x, F₁ (x, s) * spatialDeriv ψ j x)
        (volume.restrict (Ioo a b)) := by
      have h := hF₁.integrable_mul (memLp_slab_of_test hdψ hdψc)
      rw [vlSlab_measure] at h
      obtain ⟨C, hC⟩ := hθb
      exact h.integral_prod_right.bdd_mul hθ.continuous.aestronglyMeasurable
        (ae_of_all _ hC)
    have hi2 : Integrable (fun s => θ s * ∫ x, F₂ (x, s) * ψ x)
        (volume.restrict (Ioo a b)) := by
      have h := hF₂.integrable_mul (memLp_slab_of_test hψ.continuous hψc)
      rw [vlSlab_measure] at h
      obtain ⟨C, hC⟩ := hθb
      exact h.integral_prod_right.bdd_mul hθ.continuous.aestronglyMeasurable
        (ae_of_all _ hC)
    have e3 : (fun s => θ s * ((∫ x, F₁ (x, s) * spatialDeriv ψ j x) +
        ∫ x, F₂ (x, s) * ψ x)) = fun s => θ s * (∫ x, F₁ (x, s) * spatialDeriv ψ j x) +
        θ s * ∫ x, F₂ (x, s) * ψ x := funext fun s => mul_add _ _ _
    rw [e3, integral_add hi1 hi2, hw, neg_add_cancel]
  -- conclusion
  have hloc : LocallyIntegrableOn R' (Ioo a b) volume :=
    (hR'.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hzero
  have hae' : R' =ᵐ[volume.restrict (Icc a b)] fun _ => 0 := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := a) (b := b)), Filter.EventuallyEq,
      ae_restrict_iff' measurableSet_Ioo]
    exact hae
  have heq := Measure.eqOn_of_ae_eq hae' hR' continuousOn_const
    (by rw [interior_Icc, closure_Ioo hab.ne])
  have ht := heq t.2
  simp only [R', t.2, ↓reduceDIte] at ht
  rw [hRint] at ht
  linarith only [ht]

end ESS
