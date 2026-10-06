/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularity
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTopTrace

/-!
# Tools for the terminal value of the vorticity

The curl of a smooth compactly supported spatial test, the weak curl identity on a time slice,
the continuity of the vorticity pairing up to the top time, the slice form of an almost
everywhere space-time identity, and the identification of a limit through an almost everywhere
equal function (`lem:vorticity-top-extension`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A component of a vector test is supported in the support of the test. -/
theorem vorticityTopZero_component_tsupport (ψ : Vec3 → Vec3) (i : Fin 3) :
    tsupport (fun x : Vec3 => ψ x i) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro x hx
  by_contra hnot
  apply hx
  have hzero : ψ x = 0 := image_eq_zero_of_notMem_tsupport hnot
  simp [hzero]

/-- The derivative of a component of a vector test vanishes off the support of the test. -/
theorem vorticityTopZero_deriv_eq_zero {ψ : Vec3 → Vec3} {x : Vec3} (hx : x ∉ tsupport ψ)
    (i j : Fin 3) : CKN.spatialDeriv (fun y => ψ y i) j x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hx' =>
    hx (vorticityTopZero_component_tsupport ψ i (CKN.tsupport_spatialDeriv_subset j hx'))

/-- The curl of a vector test vanishes off the support of the test. -/
theorem vorticityTopZero_curl_eq_zero {ψ : Vec3 → Vec3} {x : Vec3} (hx : x ∉ tsupport ψ) :
    spatialTestCurl ψ x = 0 := by
  funext i
  fin_cases i
  · simp [vorticityTopZero_deriv_eq_zero hx]
  · simp [vorticityTopZero_deriv_eq_zero hx]
  · simp [vorticityTopZero_deriv_eq_zero hx]

/-- The integral of a combination of six integrable functions. -/
theorem vorticityTopZero_integral_six {μ : Measure Vec3} {A B C D E F : Vec3 → ℝ}
    (hA : Integrable A μ) (hB : Integrable B μ) (hC : Integrable C μ) (hD : Integrable D μ)
    (hE : Integrable E μ) (hF : Integrable F μ) :
    ∫ x, ((A x - B x) + (C x - D x) + (E x - F x)) ∂μ =
      ((∫ x, A x ∂μ) - ∫ x, B x ∂μ) + ((∫ x, C x ∂μ) - ∫ x, D x ∂μ) +
        ((∫ x, E x ∂μ) - ∫ x, F x ∂μ) := by
  have h1 : Integrable (fun x => A x - B x) μ := hA.sub hB
  have h2 : Integrable (fun x => C x - D x) μ := hC.sub hD
  have h3 : Integrable (fun x => E x - F x) μ := hE.sub hF
  have h12 : Integrable (fun x => (A x - B x) + (C x - D x)) μ := h1.add h2
  rw [integral_add h12 h3, integral_add h1 h2, integral_sub hA hB, integral_sub hC hD,
    integral_sub hE hF]

/-- The weak curl identity on a spatial slice: pairing the curl of a weak gradient with a vector
test is pairing the field with the curl of the test. -/
theorem vorticityTopZero_slice_pairing {Ω' : Set Vec3} (hfin : volume Ω' ≠ ⊤)
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    (hu : MemLp u 2 (volume.restrict Ω')) (hDu : MemLp Du 2 (volume.restrict Ω'))
    (hw : ∀ i, CKN.HasWeakGradientOn Ω' (fun x => u x i) (fun x => Du x i))
    {φ : Vec3 → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω') :
    ∫ x, ∑ i : Fin 3, spatialWeakVorticity Du x i * φ x i =
      ∫ x, ∑ i : Fin 3, u x i * spatialTestCurl φ x i := by
  have : IsFiniteMeasure (volume.restrict Ω') := isFiniteMeasure_restrict.2 hfin
  have hui : ∀ a, Integrable (fun x => u x a) (volume.restrict Ω') := fun a =>
    ((memLp_pi_iff.mp hu) a).integrable (by norm_num)
  have hDi : ∀ a b, Integrable (fun x => Du x a b) (volume.restrict Ω') := fun a b =>
    ((memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) a)) b).integrable (by norm_num)
  set φc : Fin 3 → Vec3 → ℝ := fun c y => φ y c with hφcdef
  have hφcs : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (φc c) := fun c => (contDiff_apply ℝ ℝ c).comp hφ
  have hφcsupp : ∀ c, tsupport (φc c) ⊆ tsupport φ := fun c =>
    vorticityTopZero_component_tsupport φ c
  have hφcc : ∀ c, HasCompactSupport (φc c) := fun c =>
    hφc.mono' ((subset_tsupport _).trans (hφcsupp c))
  have hdcont : ∀ c b, Continuous (fun x => CKN.spatialDeriv (φc c) b x) := fun c b =>
    ((hφcs c).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : ∀ c b, HasCompactSupport (fun x => CKN.spatialDeriv (φc c) b x) := fun c b =>
    (hφcc c).mono' ((subset_tsupport _).trans (CKN.tsupport_spatialDeriv_subset b))
  have IU : ∀ a c b, Integrable (fun x => u x a * CKN.spatialDeriv (φc c) b x)
      (volume.restrict Ω') := fun a c b => by
    obtain ⟨K, hK⟩ := (hdcont c b).bounded_above_of_compact_support (hdc c b)
    exact (hui a).mul_bdd (hdcont c b).aestronglyMeasurable (Eventually.of_forall hK)
  have ID : ∀ a b c, Integrable (fun x => Du x a b * φc c x) (volume.restrict Ω') :=
    fun a b c => by
      obtain ⟨K, hK⟩ := (hφcs c).continuous.bounded_above_of_compact_support (hφcc c)
      exact (hDi a b).mul_bdd (hφcs c).continuous.aestronglyMeasurable (Eventually.of_forall hK)
  have E : ∀ a b c, ∫ x in Ω', u x a * CKN.spatialDeriv (φc c) b x =
      -∫ x in Ω', Du x a b * φc c x := fun a b c =>
    hw a b (φc c) (hφcs c) (hφcc c) ((hφcsupp c).trans hφΩ)
  have hL : ∫ x, ∑ i : Fin 3, spatialWeakVorticity Du x i * φ x i =
      ∫ x in Ω', ((Du x 2 1 * φc 0 x - Du x 1 2 * φc 0 x) +
        (Du x 0 2 * φc 1 x - Du x 2 0 * φc 1 x) +
          (Du x 1 0 * φc 2 x - Du x 0 1 * φc 2 x)) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω') fun x hx => by
      have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hφΩ h)
      simp [h0]]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Fin.sum_univ_three, spatialWeakVorticity_zero, spatialWeakVorticity_one,
      spatialWeakVorticity_two, hφcdef]
    ring
  have hR : ∫ x, ∑ i : Fin 3, u x i * spatialTestCurl φ x i =
      ∫ x in Ω', ((u x 0 * CKN.spatialDeriv (φc 2) 1 x - u x 0 * CKN.spatialDeriv (φc 1) 2 x) +
        (u x 1 * CKN.spatialDeriv (φc 0) 2 x - u x 1 * CKN.spatialDeriv (φc 2) 0 x) +
          (u x 2 * CKN.spatialDeriv (φc 1) 0 x - u x 2 * CKN.spatialDeriv (φc 0) 1 x)) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω') fun x hx => by
      have h0 : spatialTestCurl φ x = 0 :=
        vorticityTopZero_curl_eq_zero fun h => hx (hφΩ h)
      simp [h0]]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Fin.sum_univ_three, spatialTestCurl_zero, spatialTestCurl_one,
      spatialTestCurl_two, hφcdef]
    ring
  rw [hL, hR, vorticityTopZero_integral_six (ID 2 1 0) (ID 1 2 0) (ID 0 2 1) (ID 2 0 1)
      (ID 1 0 2) (ID 0 1 2),
    vorticityTopZero_integral_six (IU 0 2 1) (IU 0 1 2) (IU 1 0 2) (IU 1 2 0) (IU 2 1 0)
      (IU 2 0 1),
    E 0 1 2, E 0 2 1, E 1 2 0, E 1 0 2, E 2 0 1, E 2 1 0]
  ring

/-- An almost everywhere space-time identity of the vorticity pairs identically with a test on
almost every time slice. -/
theorem vorticityTopZero_ae_rep {A : Set Vec3} {B : Set ℝ} {ω : Fin 3 → Vec3 × ℝ → ℝ}
    {w : Vec3 × ℝ → Vec3}
    (hωae : ∀ i, ω i =ᵐ[volume.restrict (A ×ˢ B)] fun z => w z i)
    {φ : Vec3 → Vec3} (hφA : tsupport φ ⊆ A) :
    ∀ᵐ t, t ∈ B → ∫ x, ∑ k : Fin 3, ω k (x, t) * φ x k =
      ∫ x, ∑ k : Fin 3, w (x, t) k * φ x k := by
  have h : ∀ᵐ z ∂((volume.restrict A).prod (volume.restrict B)), ∀ i, ω i z = w z i := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ae_all_iff.2 hωae
  have h' := (Measure.measurePreserving_swap (μ := volume.restrict B)
    (ν := volume.restrict A)).quasiMeasurePreserving.ae h
  filter_upwards [ae_imp_of_ae_restrict (Measure.ae_ae_of_ae_prod h')] with t ht htB
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (ht htB)] with x hx
  by_cases hxA : x ∈ A
  · have hx' := hx hxA
    simp only [Prod.swap_prod_mk] at hx'
    simp only [hx']
  · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxA (hφA h)
    simp [h0]

/-- A limit from negative times is determined by an almost everywhere equal function. -/
theorem vorticityTopZero_limit_eq {f g : ℝ → ℝ} {a L : ℝ} (ha : a < 0)
    (hf : Tendsto f (𝓝[<] 0) (𝓝 L)) (hg : Tendsto g (𝓝[<] 0) (𝓝 0))
    (hfg : ∀ᵐ t, t ∈ Ioo a 0 → f t = g t) : L = 0 := by
  have hD : Dense {t : ℝ | t ∈ Ioo a 0 → f t = g t} := Measure.dense_of_ae hfg
  set S := Ioo a 0 ∩ {t : ℝ | t ∈ Ioo a 0 → f t = g t} with hSdef
  have hcl : (0 : ℝ) ∈ closure S := by
    have h1 : Ioo a 0 ⊆ closure S := hD.open_subset_closure_inter isOpen_Ioo
    have h2 : closure (Ioo a 0) ⊆ closure S := closure_minimal h1 isClosed_closure
    exact h2 (by rw [closure_Ioo ha.ne]; exact ⟨ha.le, le_rfl⟩)
  have hne : (𝓝[S] (0 : ℝ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hsub : S ⊆ Iio 0 := fun t ht => ht.1.2
  have hf' : Tendsto f (𝓝[S] 0) (𝓝 L) := hf.mono_left (nhdsWithin_mono _ hsub)
  have hg' : Tendsto f (𝓝[S] 0) (𝓝 0) :=
    (hg.mono_left (nhdsWithin_mono _ hsub)).congr'
      (eventually_nhdsWithin_of_forall fun t ht => (ht.2 ht.1).symm)
  exact tendsto_nhds_unique hf' hg'

/-- The pairing of a vorticity continuous up to the top time with a spatial test is continuous
from below at the top time. -/
theorem vorticityTopZero_tendsto {x₁ : Vec3} {r a C : ℝ} (ha : a < 0)
    {ω : Fin 3 → Vec3 × ℝ → ℝ}
    (hωc : ∀ i, ContinuousOn (ω i) ({x : Vec3 | vec3EuclideanNorm (x - x₁) ≤ r} ×ˢ Icc a 0))
    (hωb : ∀ i, ∀ z ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₁) ≤ r} ×ˢ Icc a 0 :
      Set (Vec3 × ℝ)), |ω i z| ≤ C)
    {φ : Vec3 → Vec3} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφB : tsupport φ ⊆ vec3Ball x₁ r) :
    Tendsto (fun t => ∫ x, ∑ k : Fin 3, ω k (x, t) * φ x k) (𝓝[<] 0)
      (𝓝 (∫ x, ∑ k : Fin 3, ω k (x, 0) * φ x k)) := by
  have hin : ∀ x k, φ x k ≠ 0 → x ∈ vec3Ball x₁ r := fun x k hx =>
    hφB (subset_tsupport _ fun h => hx (by rw [h]; rfl))
  have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ), t ∈ Icc a 0 :=
    mem_of_superset (Ioo_mem_nhdsLT ha) Ioo_subset_Icc_self
  have hcl : ∀ y, y ∈ vec3Ball x₁ r → y ∈ {x : Vec3 | vec3EuclideanNorm (x - x₁) ≤ r} :=
    fun y hy => show vec3EuclideanNorm (y - x₁) ≤ r from le_of_lt hy
  have hcomp : ∀ k, Continuous (fun x => φ x k) := fun k => (continuous_apply k).comp hφ
  have hcompc : ∀ k, HasCompactSupport (fun x => φ x k) := fun k =>
    hφc.mono' ((subset_tsupport _).trans (vorticityTopZero_component_tsupport φ k))
  have hterm : ∀ t ∈ Icc a 0, ∀ k, Continuous (fun x => ω k (x, t) * φ x k) := by
    intro t ht k
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ vec3Ball x₁ r
    · have hcont : ContinuousOn (fun x => ω k (x, t))
          {x : Vec3 | vec3EuclideanNorm (x - x₁) ≤ r} :=
        (hωc k).comp (continuous_id.prodMk continuous_const).continuousOn fun y hy => ⟨hy, ht⟩
      exact (hcont.continuousAt (mem_of_superset ((isOpen_vec3Ball x₁ r).mem_nhds hx)
        hcl)).mul (hcomp k).continuousAt
    · have hxt : x ∉ tsupport φ := fun h => hx (hφB h)
      have hzero : (fun x => ω k (x, t) * φ x k) =ᶠ[𝓝 x] fun _ => 0 :=
        (notMem_tsupport_iff_eventuallyEq.1 hxt).mono fun y hy => by
          simp only [Pi.zero_apply] at hy
          simp [hy]
      exact continuousAt_const.congr hzero.symm
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ∑ k : Fin 3, |C| * |φ x k|) ?_ ?_ ?_ ?_
  · filter_upwards [hev] with t ht
    exact (continuous_finsetSum _ fun k _ => hterm t ht k).aestronglyMeasurable
  · filter_upwards [hev] with t ht
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    by_cases h0 : φ x k = 0
    · simp [h0]
    · have hb := hωb k (x, t) ⟨hcl _ (hin x k h0), ht⟩
      exact mul_le_mul_of_nonneg_right (hb.trans (le_abs_self C)) (abs_nonneg _)
  · exact integrable_finsetSum _ fun k _ =>
      (((hcomp k).integrable_of_hasCompactSupport (hcompc k)).abs).const_mul _
  · refine Eventually.of_forall fun x => tendsto_finsetSum _ fun k _ => ?_
    by_cases h0 : φ x k = 0
    · simp only [h0, mul_zero]
      exact tendsto_const_nhds
    · have hmem : (x, (0 : ℝ)) ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₁) ≤ r} ×ˢ Icc a 0 :
          Set (Vec3 × ℝ)) := ⟨hcl _ (hin x k h0), ha.le, le_rfl⟩
      have hpath : Tendsto (fun t : ℝ => (x, t)) (𝓝[<] 0)
          (𝓝[{x : Vec3 | vec3EuclideanNorm (x - x₁) ≤ r} ×ˢ Icc a 0] (x, 0)) :=
        tendsto_nhdsWithin_iff.2 ⟨((continuous_const.prodMk continuous_id).tendsto' 0 (x, 0)
          rfl).mono_left nhdsWithin_le_nhds,
          hev.mono fun t ht => ⟨hcl _ (hin x k h0), ht⟩⟩
      exact ((hωc k (x, 0) hmem).tendsto.comp hpath).mul_const _

end ESS
