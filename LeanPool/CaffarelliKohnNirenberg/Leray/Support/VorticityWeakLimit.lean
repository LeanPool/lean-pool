/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityBackMollify
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.FactorIBP
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Weak derivatives as limits of smooth approximations

The bootstrap of `thm:vorticity-regularity` of the Escauriaza–Seregin–Šverák manuscript produces weak derivatives as `L²` limits of
derivatives of smooth approximations. This file records the completeness step, the passage to the
limit in the weak identities, and the pointwise form of constant-coefficient weak identities for
backward mollifications at points whose kernel support lies inside the domain.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- A sequence which is Cauchy in `L²` has an `L²` limit. -/
theorem vorticityL2_exists_limit {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    (hcauchy : Tendsto (fun p : ℕ × ℕ => eLpNorm (f p.1 - f p.2) 2 μ) atTop (𝓝 0)) :
    ∃ g : α → ℝ, MemLp g 2 μ ∧ Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let F : ℕ → Lp ℝ 2 μ := fun n => (hf n).toLp (f n)
  have hdist : ∀ m n, dist (F m) (F n) = (eLpNorm (f m - f n) 2 μ).toReal := by
    intro m n
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [(hf m).coeFn_toLp, (hf n).coeFn_toLp] with x hm hn
    simp only [Pi.sub_apply, F, hm, hn]
  have hcau : CauchySeq F := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcauchy
    simp only [ENNReal.toReal_zero] at hreal
    refine hreal.congr fun p => ?_
    simp only [Function.comp_apply, hdist]
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨G, Lp.memLp G, ?_⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hG
  refine hG.congr fun n => ?_
  apply eLpNorm_congr_ae
  filter_upwards [(hf n).coeFn_toLp] with x hx
  simp only [Pi.sub_apply, F, hx]

/-- Pairings against a fixed square-integrable function pass to `L²` limits. -/
theorem vorticity_tendsto_integral_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a : ℕ → α → ℝ} {A φ : α → ℝ} (ha : ∀ n, MemLp (a n) 2 μ) (hA : MemLp A 2 μ)
    (hφ : MemLp φ 2 μ) (hconv : Tendsto (fun n => eLpNorm (a n - A) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, a n x * φ x ∂μ) atTop (𝓝 (∫ x, A x * φ x ∂μ)) := by
  have : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have hint (g : α → ℝ) (hg : MemLp g 2 μ) : Integrable (fun x => g x * φ x) μ := by
    have h : MemLp (g * φ) 1 μ := hg.mul (r := 1) hφ
    exact memLp_one_iff_integrable.mp h
  apply tendsto_integral_of_L1 _ (hint A hA).aestronglyMeasurable
    (Eventually.of_forall fun n => hint (a n) (ha n))
  have hbound : ∀ n, ∫⁻ x, ‖a n x * φ x - A x * φ x‖ₑ ∂μ ≤
      eLpNorm (a n - A) 2 μ * eLpNorm φ 2 μ := by
    intro n
    have heq : (fun x => a n x * φ x - A x * φ x) = (a n - A) * φ := by
      funext x
      simp only [Pi.mul_apply, Pi.sub_apply]
      ring
    have hmeas : AEStronglyMeasurable (fun x => a n x * φ x - A x * φ x) μ :=
      ((ha n).aestronglyMeasurable.mul hφ.aestronglyMeasurable).sub
        (hA.aestronglyMeasurable.mul hφ.aestronglyMeasurable)
    rw [← eLpNorm_one_eq_lintegral_enorm hmeas, heq]
    have hsmul := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      ((ha n).aestronglyMeasurable.sub hA.aestronglyMeasurable) hφ.aestronglyMeasurable
    have hfun : (a n - A) • φ = (a n - A) * φ := by
      funext x
      simp only [Pi.smul_apply', Pi.mul_apply, smul_eq_mul]
    rwa [hfun] at hsmul
  have hlim : Tendsto (fun n => eLpNorm (a n - A) 2 μ * eLpNorm φ 2 μ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const hconv (Or.inr hφ.eLpNorm_ne_top)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound

/-- A continuous compactly supported function is square integrable for every restriction of
Lebesgue measure. -/
theorem vorticity_memLp_two_of_continuous_compact {W : Set (Vec3 × ℝ)} {φ : Vec3 × ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    MemLp φ 2 (volume.restrict W) :=
  (hφ.memLp_of_hasCompactSupport hφc).restrict W

/-- Smooth integration by parts in a spatial direction, restricted to a set containing the
support of the test. -/
theorem vorticity_setIntegral_mul_spatialPartial {W : Set (Vec3 × ℝ)}
    {F ψ : Vec3 × ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψW : tsupport ψ ⊆ W) (j : Fin 3) :
    ∫ z in W, F z * spatialPartial ψ j z = -∫ z in W, spatialPartial F j z * ψ z := by
  have hleft : ∫ z in W, F z * spatialPartial ψ j z = ∫ z, F z * spatialPartial ψ j z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzψ : z ∉ tsupport ψ := fun h => hz (hψW h)
    have hzero : spatialPartial ψ j z = 0 := by
      have hsub := CKN.tsupport_spatialPartial_subset (ψ := ψ) j
      exact image_eq_zero_of_notMem_tsupport (fun h => hzψ (hsub h))
    rw [hzero, mul_zero]
  have hright : ∫ z in W, spatialPartial F j z * ψ z = ∫ z, spatialPartial F j z * ψ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzψ : z ∉ tsupport ψ := fun h => hz (hψW h)
    rw [image_eq_zero_of_notMem_tsupport hzψ, mul_zero]
  rw [hleft, hright]
  exact CKN.integral_mul_spatialPartial_eq_neg_spatialPartial_mul hF hψ hψc j

/-- If smooth functions converge in `L²(W)` together with one spatial derivative, then the limit
of the derivatives is the weak derivative of the limit on `W`. -/
theorem vorticity_weakPartial_of_tendsto {W : Set (Vec3 × ℝ)}
    {w : ℕ → Vec3 × ℝ → ℝ} (hw : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (w n))
    {f g : Vec3 × ℝ → ℝ} {j : Fin 3}
    (hwL2 : ∀ n, MemLp (w n) 2 (volume.restrict W))
    (hdwL2 : ∀ n, MemLp (fun z : Vec3 × ℝ => spatialPartial (w n) j z) 2 (volume.restrict W))
    (hfL2 : MemLp f 2 (volume.restrict W)) (hgL2 : MemLp g 2 (volume.restrict W))
    (hf : Tendsto (fun n => eLpNorm (w n - f) 2 (volume.restrict W)) atTop (𝓝 0))
    (hg : Tendsto (fun n => eLpNorm ((fun z : Vec3 × ℝ => spatialPartial (w n) j z) - g) 2
      (volume.restrict W)) atTop (𝓝 0)) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∫ z in W, f z * spatialPartial ψ j z = -∫ z in W, g z * ψ z := by
  intro ψ hψ hψc hψW
  have hdψ : MemLp (fun z => spatialPartial ψ j z) 2 (volume.restrict W) :=
    vorticity_memLp_two_of_continuous_compact (CKN.spatialPartial_contDiff hψ j).continuous
      (CKN.hasCompactSupport_spatialPartial hψc j)
  have hψL2 : MemLp ψ 2 (volume.restrict W) :=
    vorticity_memLp_two_of_continuous_compact hψ.continuous hψc
  have hleft := vorticity_tendsto_integral_mul hwL2 hfL2 hdψ hf
  have hright := vorticity_tendsto_integral_mul hdwL2 hgL2 hψL2 hg
  have heq : ∀ n, ∫ z in W, w n z * spatialPartial ψ j z =
      -∫ z in W, spatialPartial (w n) j z * ψ z := fun n =>
    vorticity_setIntegral_mul_spatialPartial (hw n) hψ hψc hψW j
  have hright' := hright.neg.congr (fun n => (heq n).symm)
  exact tendsto_nhds_unique hleft hright'

end CKN
