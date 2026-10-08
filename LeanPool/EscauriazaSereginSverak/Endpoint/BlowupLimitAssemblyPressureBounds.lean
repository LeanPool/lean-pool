/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyPressureIdentity
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupVelocityTime
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszLocalSplitLp
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszFarVelocity
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureTwoRadius

/-!
# Bounds for the pressure limit

Uniform slice and space-time L³ bounds for the blow-up velocities and their
limit, and the bookkeeping between L^(3/2) classes and seminorms used in
the pressure-limit step of `prop:blowup-limit`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The canonical Riesz pressure depends only on the almost-everywhere class
of its tensor. -/
theorem blowupLimitAssemblyPressure_rieszPressure_congr_ae
    {F G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (h : ∀ i j, F i j =ᵐ[volume] G i j) :
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF =
      CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) G hG := by
  unfold CKN.Leray.rieszPressureSpaceTime
  congr 1
  unfold CKN.Leray.rieszPressureSpaceTimeTensorToLp
  funext i j
  exact MemLp.toLp_congr (hF i j) (hG i j) (h i j)

/-- Convergence of L^p classes is convergence of the L^p seminorm of the
differences. -/
theorem blowupLimitAssemblyPressure_eLpNorm_sub_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ k, MemLp (f k) p μ) (hg : MemLp g p μ)
    (h : Tendsto (fun k => (hf k).toLp (f k)) atTop (nhds (hg.toLp g))) :
    Tendsto (fun k => eLpNorm (fun x => f k x - g x) p μ) atTop (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  have hfinite (k : ℕ) : eLpNorm (fun x => f k x - g x) p μ ≠ ⊤ :=
    ((hf k).sub hg).eLpNorm_ne_top
  rw [← ENNReal.tendsto_toReal_zero_iff hfinite]
  convert h using 1
  funext k
  rw [← MemLp.toLp_sub (hf k) hg, Lp.norm_toLp]
  rfl

/-- The zero-extended rescaled velocities have uniformly bounded global L³
slices at almost every time. -/
theorem blowupLimitAssemblyPressure_velocity_slice_bound
    (u : ParabolicPoint → Vec3) (Mᵤ : ℝ≥0∞)
    (hsourceU : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => (goodPointDomain.indicator u) (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ Mᵤ)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (blowupVelocity x₀ t₀ r u (x,t)))
        3 volume ≤ Mᵤ := by
  set J : Set ℝ := CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0)
  have hJ : MeasurableSet J := by
    have hmeas : Measurable (CKN.scalingTime r t₀) := by
      unfold CKN.scalingTime
      fun_prop
    exact measurableSet_Ioo.preimage hmeas
  have h1 := blowupRescaledVelocity_slice_bound_ae (goodPointDomain.indicator u)
    x₀ t₀ r hr J subset_rfl Mᵤ hsourceU
  have h2 := (ae_restrict_iff' hJ).1 h1
  filter_upwards [h2] with t ht
  by_cases htJ : t ∈ J
  · exact ht htJ
  · have hzero : ∀ x : Vec3, blowupVelocity x₀ t₀ r u (x,t) = 0 := by
      intro x
      let w : ParabolicPoint := (x₀ + r • x, t₀ + r ^ 2 * t)
      have hvw : blowupVelocity x₀ t₀ r u (x,t) = r • goodPointDomain.indicator u w := rfl
      have hnot : w ∉ goodPointDomain := fun hmem => htJ hmem.2
      rw [hvw, indicator_of_notMem hnot, smul_zero]
    simp [hzero, vec3EuclideanNorm_zero]

/-- A measurable space-time field whose slices are uniformly bounded in L³
on a finite time interval is in L³ on every product set with that time
interval, with a uniform bound. -/
theorem blowupLimitAssemblyPressure_memLp_three_of_slices
    {w : Vec3 × ℝ → Vec3} (hw : Measurable w) {I : Set ℝ}
    {N : ℝ≥0∞}
    (hslice : ∀ᵐ t ∂volume.restrict I, eLpNorm (fun x : Vec3 => w (x,t)) 3 volume ≤ N)
    (S : Set Vec3) :
    eLpNorm w 3 ((volume : Measure (Vec3 × ℝ)).restrict (S ×ˢ I)) ≤
      (volume I * N ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
  have hmeasE : Measurable (fun z : Vec3 × ℝ => ‖w z‖ₑ ^ (3 : ℝ)) :=
    hw.enorm.pow_const _
  have hslice' : ∀ᵐ t ∂volume.restrict I,
      (∫⁻ x, ‖w (x,t)‖ₑ ^ (3 : ℝ)) ≤ N ^ (3 : ℝ) := by
    filter_upwards [hslice] with t ht
    have hmeas : AEStronglyMeasurable (fun x : Vec3 => w (x,t)) volume :=
      (hw.comp measurable_prodMk_right).aestronglyMeasurable
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)]
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmeas] at ht
    simpa using ENNReal.rpow_le_rpow ht (by norm_num : (0 : ℝ) ≤ 3)
  have hint : (∫⁻ z in S ×ˢ I, ‖w z‖ₑ ^ (3 : ℝ)) ≤ volume I * N ^ (3 : ℝ) := by
    calc
      (∫⁻ z in S ×ˢ I, ‖w z‖ₑ ^ (3 : ℝ)) ≤
          ∫⁻ z in (Set.univ : Set Vec3) ×ˢ I, ‖w z‖ₑ ^ (3 : ℝ) :=
        lintegral_mono_set (prod_mono (subset_univ S) subset_rfl)
      _ = ∫⁻ t in I, ∫⁻ x, ‖w (x,t)‖ₑ ^ (3 : ℝ) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
          lintegral_prod_symm _ hmeasE.aemeasurable]
      _ ≤ ∫⁻ _t in I, N ^ (3 : ℝ) := lintegral_mono_ae hslice'
      _ = volume I * N ^ (3 : ℝ) := by
        rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hw.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow hint (by norm_num)

end ESS

end
