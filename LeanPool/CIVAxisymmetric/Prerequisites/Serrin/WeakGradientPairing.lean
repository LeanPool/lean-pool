/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Reduction.SuitableWeakSolutionRestrict
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The weak gradient of a suitable weak solution pairs as the distributional gradient

For a suitable weak solution on the unit cylinder, the weak gradient `Du` satisfies
`∫ Du_{kj} ∂ⱼψ = -∫ u_k ∂ⱼ∂ⱼψ` for every smooth test function `ψ` supported in the cylinder.
The proof works on a local box containing the support of `ψ`, applies the weak derivative on
almost every time slice, and integrates in time. This identifies the viscous term of the weak
momentum equation in the passage to the classical equations used in the proof of
`lem:aniso:annulus`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem continuous_vec3EuclideanNorm_fst :
    Continuous (fun z : Vec3 × ℝ => vec3EuclideanNorm z.1) := by
  unfold vec3EuclideanNorm
  fun_prop

/-- A compact subset of the unit cylinder lies in a local box `B(0, r) × (a, b)`. -/
theorem exists_localBox_of_isCompact_subset_unitCylinder {K : Set (Vec3 × ℝ)}
    (hK : IsCompact K) (hKQ : K ⊆ unitCylinder) :
    ∃ r a b : ℝ, 0 < r ∧ r < 1 ∧ -1 < a ∧ a < b ∧ b < 0 ∧
      K ⊆ vec3Ball 0 r ×ˢ Ioo a b := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨1 / 2, -1 / 2, -1 / 4, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by simp [hE]⟩
  obtain ⟨z₁, hz₁K, hz₁⟩ := hK.exists_isMaxOn hne continuous_vec3EuclideanNorm_fst.continuousOn
  obtain ⟨z₂, hz₂K, hz₂⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
  obtain ⟨z₃, hz₃K, hz₃⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
  have h₁ : vec3EuclideanNorm z₁.1 < 1 := by
    have := (hKQ hz₁K).1
    simpa [vec3Ball] using this
  have h₂ : -1 < z₂.2 := (hKQ hz₂K).2.1
  have h₃ : z₃.2 < 0 := (hKQ hz₃K).2.2
  have h0 : 0 ≤ vec3EuclideanNorm z₁.1 := vec3EuclideanNorm_nonneg _
  refine ⟨(vec3EuclideanNorm z₁.1 + 1) / 2, (z₂.2 - 1) / 2, z₃.2 / 2, by linarith only [h0],
    by linarith only [h₁], by linarith only [h₂], ?_, by linarith only [h₃], ?_⟩
  · have := hz₂ hz₃K
    simp only [mem_ofPred_eq] at this
    linarith only [this, h₂, h₃]
  · intro z hz
    have hn := hz₁ hz
    have hlo := hz₂ hz
    have hhi := hz₃ hz
    simp only [mem_ofPred_eq] at hn hlo hhi
    refine ⟨?_, ?_, ?_⟩
    · change vec3EuclideanNorm (z.1 - 0) < _
      rw [sub_zero]
      linarith only [hn, h₁]
    · linarith only [hlo, h₂]
    · linarith only [hhi, h₃]

/-- The box `B(0, r) × (a, b)` with `r < 1` and `-1 < a < b < 0` is a local box of the unit
cylinder. -/
theorem localBox_ball_Ioo {r a b : ℝ} (hr : 0 < r) (hr1 : r < 1) (ha : -1 < a) (hb : b < 0) :
    localBox (vec3Ball 0 1) (Ioo (-1) 0) (vec3Ball 0 r) (Ioo a b) := by
  refine ⟨?_, isCompact_closure_vec3Ball hr, ?_, ordConnected_Ioo, ?_, ?_⟩
  · have : IsOpen {y : Vec3 | vec3EuclideanNorm (y - 0) < r} := by
      have hc : Continuous (fun y : Vec3 => vec3EuclideanNorm (y - 0)) := by
        unfold vec3EuclideanNorm; fun_prop
      exact isOpen_lt hc continuous_const
    exact this
  · rw [closure_vec3Ball hr]
    intro y hy
    simp only [mem_ofPred_eq] at hy
    change vec3EuclideanNorm (y - 0) < 1
    linarith only [hy, hr1]
  · exact (isCompact_Icc).of_isClosed_subset isClosed_closure (closure_minimal
    Ioo_subset_Icc_self isClosed_Icc)
  · refine ((closure_minimal Ioo_subset_Icc_self isClosed_Icc)).trans ?_
    intro t ht
    exact ⟨by linarith only [ht.1, ha], by linarith only [ht.2, hb]⟩

/-- A spatial partial vanishes where the function vanishes on a neighbourhood. -/
theorem spatialPartial_eq_zero_of_eventually_eq_zero {F : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hF : ∀ᶠ w in nhds z, F w = 0) (j : Fin 3) : spatialPartial F j z = 0 := by
  unfold spatialPartial
  have hcont : Continuous (fun x : Vec3 => ((x, z.2) : Vec3 × ℝ)) := by fun_prop
  have h1 : (fun x : Vec3 => F (x, z.2)) =ᶠ[nhds z.1] fun _ => (0 : ℝ) := by
    have := hcont.continuousAt (x := z.1) |>.tendsto
    exact this.eventually (by simpa using hF)
  rw [h1.fderiv_eq]
  simp

/-- The spatial partial of a smooth function is its joint derivative in the direction `(eⱼ, 0)`,
hence smooth. -/
theorem contDiff_spatialPartial_of_contDiff {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial ψ j z) := by
  have heq : (fun z : Vec3 × ℝ => spatialPartial ψ j z) =
      fun z => fderiv ℝ ψ z ((basisVec j : Vec3), (0 : ℝ)) := by
    funext z
    unfold spatialPartial
    have hd : HasFDerivAt ψ (fderiv ℝ ψ z) z :=
      ((hψ.differentiable (by simp)) z).hasFDerivAt
    have hcomp : HasFDerivAt (fun x : Vec3 => ψ (x, z.2))
        ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ)) z.1 :=
      hd.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)
    rw [hcomp.fderiv]
    rfl
  rw [heq]
  exact (hψ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

/-- For a suitable weak solution on the unit cylinder, the weak gradient pairs with a test
function supported in the cylinder as the distributional gradient. -/
theorem integrable_and_integral_weakGradient_mul_spatialPartial {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ unitCylinder) (k j : Fin 3) :
    Integrable (fun z : Vec3 × ℝ => Du z k j * spatialPartial ψ j z) ∧
    ∫ z : Vec3 × ℝ, Du z k j * spatialPartial ψ j z =
      -∫ z : Vec3 × ℝ, u z k * spatialSecondPartial ψ j j z := by
  obtain ⟨r, a, b, hr, hr1, ha, hab, hb, hK⟩ :=
    exists_localBox_of_isCompact_subset_unitCylinder hψc hsupp
  have hLB := localBox_ball_Ioo hr hr1 ha hb
  have hbox := hsol.2.2.2.2.2.1 (vec3Ball 0 r) (Ioo a b) hLB
  obtain ⟨hum, hDum, -, -, -, hL2, -, -, hweak⟩ := hbox
  set Ω' : Set Vec3 := vec3Ball 0 r with hΩ'
  set J : Set ℝ := Ioo a b with hJ
  have hΩ'm : MeasurableSet Ω' := by
    have : IsOpen {y : Vec3 | vec3EuclideanNorm (y - 0) < r} := by
      have hc : Continuous (fun y : Vec3 => vec3EuclideanNorm (y - 0)) := by
        unfold vec3EuclideanNorm; fun_prop
      exact isOpen_lt hc continuous_const
    exact this.measurableSet
  -- the two integrands on `Vec3 × ℝ`
  set F : Vec3 × ℝ → ℝ := fun z => Du z k j * spatialPartial ψ j z with hF
  set G : Vec3 × ℝ → ℝ := fun z => u z k * spatialSecondPartial ψ j j z with hG
  have hsp : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial ψ j z) :=
    contDiff_spatialPartial_of_contDiff hψ j
  have hspc : HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial ψ j z) :=
    HasCompactSupport.intro hψc (fun z hz => spatialPartial_eq_zero_of_notMem_tsupport hz j)
  have hsp2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialSecondPartial ψ j j z) :=
    contDiff_spatialPartial_of_contDiff hsp j
  have hsp2c : HasCompactSupport (fun z : Vec3 × ℝ => spatialSecondPartial ψ j j z) :=
    HasCompactSupport.intro hψc (fun z hz => spatialSecondPartial_eq_zero_of_notMem_tsupport hz j j)
  -- the product measure restricted to the box
  set μB : Measure (Vec3 × ℝ) := (volume.restrict Ω').prod (volume.restrict J) with hμB
  have hμB' : μB = (volume : Measure (Vec3 × ℝ)).restrict (Ω' ×ˢ J) := by
    rw [hμB, Measure.prod_restrict]; rfl
  -- square integrability on the box
  have hL2' : (∫⁻ z in Ω' ×ˢ J, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := hL2
  have hDum' : AEStronglyMeasurable (fun z : Vec3 × ℝ => Du z) μB := by rw [hμB']; exact hDum
  have hum' : AEStronglyMeasurable (fun z : Vec3 × ℝ => u z) μB := by rw [hμB']; exact hum
  have hDu2 : MemLp (fun z : Vec3 × ℝ => Du z) 2 μB := by
    rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hDum',
      hμB']
    refine lt_of_le_of_lt (lintegral_mono (fun z => ?_)) hL2'
    simp only [ENNReal.toReal_ofNat]
    exact le_add_self
  have hu2 : MemLp (fun z : Vec3 × ℝ => u z) 2 μB := by
    rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hum',
      hμB']
    refine lt_of_le_of_lt (lintegral_mono (fun z => ?_)) hL2'
    simp only [ENNReal.toReal_ofNat]
    exact le_self_add
  have hDukj : MemLp (fun z : Vec3 × ℝ => Du z k j) 2 μB := by
    refine hDu2.of_le ?_ (Filter.Eventually.of_forall (fun z => ?_))
    · exact (continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply k).comp_aestronglyMeasurable hDum')
    · exact (norm_le_pi_norm (Du z k) j).trans (norm_le_pi_norm (Du z) k)
  have huk : MemLp (fun z : Vec3 × ℝ => u z k) 2 μB := by
    refine hu2.of_le ?_ (Filter.Eventually.of_forall (fun z => ?_))
    · exact (continuous_apply k).comp_aestronglyMeasurable hum'
    · exact norm_le_pi_norm (u z) k
  have hFint : Integrable F μB :=
    hDukj.integrable_mul (hsp.continuous.memLp_of_hasCompactSupport (p := 2) hspc)
  have hGint : Integrable G μB :=
    huk.integrable_mul (hsp2.continuous.memLp_of_hasCompactSupport (p := 2) hsp2c)
  -- whole-space integrals are box integrals
  have hout : ∀ z : Vec3 × ℝ, z ∉ Ω' ×ˢ J → z ∉ tsupport ψ := fun z hz h => hz (hK h)
  have hFwhole : ∫ z : Vec3 × ℝ, F z = ∫ z, F z ∂μB := by
    rw [hμB', setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro z hz
    simp only [hF, spatialPartial_eq_zero_of_notMem_tsupport (hout z hz) j, mul_zero]
  have hGwhole : ∫ z : Vec3 × ℝ, G z = ∫ z, G z ∂μB := by
    rw [hμB', setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro z hz
    simp only [hG, spatialSecondPartial_eq_zero_of_notMem_tsupport (hout z hz) j j, mul_zero]
  refine ⟨?_, ?_⟩
  · rw [hμB'] at hFint
    refine (integrableOn_iff_integrable_of_support_subset (fun z hz => ?_)).mp hFint
    by_contra hzB
    exact hz (by simp only [hF, spatialPartial_eq_zero_of_notMem_tsupport (hout z hzB) j,
      mul_zero])
  change ∫ z : Vec3 × ℝ, F z = -∫ z : Vec3 × ℝ, G z
  rw [hFwhole, hGwhole, hμB, integral_prod_symm F hFint, integral_prod_symm G hGint,
    ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hweak k] with s hs
  -- the slice test function
  set φ : Vec3 → ℝ := fun x => spatialPartial ψ j (x, s) with hφ
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := hsp.comp (contDiff_id.prodMk contDiff_const)
  set Ks : Set Vec3 := {x | (x, s) ∈ tsupport ψ} with hKs
  have hKsc : IsClosed Ks := (isClosed_tsupport ψ).preimage (by fun_prop)
  have hsuppφ : tsupport φ ⊆ Ks := by
    refine closure_minimal (fun x hx => ?_) hKsc
    by_contra hxK
    exact hx (spatialPartial_eq_zero_of_notMem_tsupport hxK j)
  have hKsΩ : Ks ⊆ Ω' := fun x hx => (hK hx).1
  have hφc : HasCompactSupport φ :=
    (isCompact_closure_vec3Ball hr).of_isClosed_subset (isClosed_tsupport φ)
      ((hsuppφ.trans hKsΩ).trans subset_closure)
  have h := hs j φ hφs hφc (hsuppφ.trans hKsΩ)
  change ∫ x in Ω', Du (x, s) k j * φ x =
    -∫ x in Ω', (fun x => u (x, s) k) x * fderiv ℝ φ x (basisVec j)
  rw [h, neg_neg]

/-- For a suitable weak solution on the unit cylinder, the weak gradient pairs with a test
function supported in the cylinder as the distributional gradient. -/
theorem integral_weakGradient_mul_spatialPartial_eq {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ unitCylinder) (k j : Fin 3) :
    ∫ z : Vec3 × ℝ, Du z k j * spatialPartial ψ j z =
      -∫ z : Vec3 × ℝ, u z k * spatialSecondPartial ψ j j z :=
  (integrable_and_integral_weakGradient_mul_spatialPartial hsol hψ hψc hsupp k j).2

end CIV
