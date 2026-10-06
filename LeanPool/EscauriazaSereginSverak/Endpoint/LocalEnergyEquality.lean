/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergyMollifiedEnergy
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergySuitability
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergySmooth
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Constructor
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace ESS

local instance localEnergyEqualityHolderTripleFourFourTwo :
    ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  have hreal : Real.HolderTriple 4 4 2 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyEqualityHolderTripleTwoFourFourThree :
    ENNReal.HolderTriple 2 4 (ENNReal.ofReal (4 / 3 : ℝ)) := by
  have hreal : Real.HolderTriple 2 4 (4 / 3) := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyEqualityHolderTripleThreeTwoFourTwelveEleven :
    ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ)) 4 (ENNReal.ofReal (12 / 11 : ℝ)) := by
  have hreal : Real.HolderTriple (3 / 2) 4 (12 / 11) := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyEqualityHolderTripleTwoTwoOne :
    ENNReal.HolderTriple 2 2 1 := by
  have hreal : Real.HolderTriple 2 2 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

/-- The ordinary product-space carrier for the unit backward cylinder. -/
@[expose] def localEnergyUnitProductCylinder : Set (Vec3 × ℝ) :=
  vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0

/-- The componentwise zero extension of the velocity from the unit cylinder. -/
@[expose] def localEnergyVelocityZeroExtension
    (u : ParabolicPoint → Vec3) (i : Fin 3) : Vec3 × ℝ → ℝ :=
  localEnergyUnitProductCylinder.indicator (fun z => u z i)

/-- The componentwise zero extension of the quadratic velocity tensor. -/
@[expose] def localEnergyTensorZeroExtension
    (u : ParabolicPoint → Vec3) (i j : Fin 3) : Vec3 × ℝ → ℝ :=
  localEnergyUnitProductCylinder.indicator (fun z => u z i * u z j)

/-- The componentwise zero extension of the weak gradient. -/
@[expose] def localEnergyGradientZeroExtension
    (Du : ParabolicPoint → Fin 3 → Vec3) (i j : Fin 3) : Vec3 × ℝ → ℝ :=
  localEnergyUnitProductCylinder.indicator (fun z => Du z i j)

/-- The zero extension of the pressure from the unit cylinder. -/
@[expose] def localEnergyPressureZeroExtension
    (p : ParabolicPoint → ℝ) : Vec3 × ℝ → ℝ :=
  localEnergyUnitProductCylinder.indicator p

/-- The smooth space-time mollification of a velocity component zero extension. -/
@[expose] def localEnergyMollifiedVelocity
    (u : ParabolicPoint → Vec3) (δ : ℝ) (hδ : 0 < δ) : Vec3 × ℝ → Vec3 :=
  fun z i => spaceTimeMollify (localEnergyVelocityZeroExtension u i) δ hδ z

/-- The smooth space-time mollification of a quadratic velocity tensor component. -/
@[expose] def localEnergyMollifiedTensor
    (u : ParabolicPoint → Vec3) (δ : ℝ) (hδ : 0 < δ) :
    Vec3 × ℝ → Fin 3 → Fin 3 → ℝ :=
  fun z i j => spaceTimeMollify (localEnergyTensorZeroExtension u i j) δ hδ z

/-- The smooth space-time mollification of a weak-gradient component. -/
@[expose] def localEnergyMollifiedGradient
    (Du : ParabolicPoint → Fin 3 → Vec3) (δ : ℝ) (hδ : 0 < δ) :
    Vec3 × ℝ → Fin 3 → Fin 3 → ℝ :=
  fun z i j => spaceTimeMollify (localEnergyGradientZeroExtension Du i j) δ hδ z

/-- The smooth space-time mollification of the pressure zero extension. -/
@[expose] def localEnergyMollifiedPressure
    (p : ParabolicPoint → ℝ) (δ : ℝ) (hδ : 0 < δ) : Vec3 × ℝ → ℝ :=
  spaceTimeMollify (localEnergyPressureZeroExtension p) δ hδ

/-- Finite sums preserve convergence in an `Lᵖ` seminorm when `p ≥ 1`. -/
theorem localEnergy_tendsto_eLpNorm_finset_sum_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) {ι : Type*} (s : Finset ι)
    (fn : ℕ → ι → α → ℝ) (f : ι → α → ℝ)
    (hconv : ∀ i ∈ s, Tendsto
      (fun n => eLpNorm (fun x => fn n i x - f i x) p μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm
      (fun x => (∑ i ∈ s, fn n i x) - ∑ i ∈ s, f i x) p μ) atTop (nhds 0) := by
  have hsumBound (d : ι → α → ℝ) (t : Finset ι) :
      eLpNorm (fun x => ∑ i ∈ t, d i x) p μ ≤
        ∑ i ∈ t, eLpNorm (d i) p μ := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t hat ih =>
        have heqInsert : (fun x => ∑ i ∈ insert a t, d i x) =
            fun x => d a x + ∑ i ∈ t, d i x := by
          funext x
          simp [Finset.sum_insert, hat]
        rw [heqInsert]
        calc
          _ ≤ eLpNorm (d a) p μ +
              eLpNorm (fun x => ∑ i ∈ t, d i x) p μ := eLpNorm_add_le hp
          _ ≤ eLpNorm (d a) p μ + ∑ i ∈ t, eLpNorm (d i) p μ :=
                add_le_add le_rfl ih
          _ = ∑ i ∈ insert a t, eLpNorm (d i) p μ := by
                simp [Finset.sum_insert, hat]
  have hbound (n : ℕ) : eLpNorm
      (fun x => (∑ i ∈ s, fn n i x) - ∑ i ∈ s, f i x) p μ ≤
        ∑ i ∈ s, eLpNorm (fun x => fn n i x - f i x) p μ := by
    have heq : (fun x => (∑ i ∈ s, fn n i x) - ∑ i ∈ s, f i x) =
        fun x => ∑ i ∈ s, (fn n i x - f i x) := by
      funext x
      rw [← Finset.sum_sub_distrib]
    rw [heq]
    exact hsumBound (fun i x => fn n i x - f i x) s
  have hsum : Tendsto (fun n => ∑ i ∈ s,
      eLpNorm (fun x => fn n i x - f i x) p μ) atTop (nhds 0) := by
    simpa using tendsto_finsetSum s (fun i hi => hconv i hi)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · filter_upwards with n
    exact bot_le
  · filter_upwards with n
    exact hbound n

private theorem localEnergy_smoothCompact_memLp
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (p : ℝ≥0∞) :
    MemLp f p (volume : Measure (Vec3 × ℝ)) :=
  hf.continuous.memLp_of_hasCompactSupport hfc

/-- Space-time mollification preserves finite-exponent MemLp membership. -/
theorem localEnergy_mollify_memLp
    {g : Vec3 × ℝ → ℝ} {p : ℝ≥0∞} {δr : ℝ}
    (hp : 1 ≤ p) (hpTop : p ≠ ⊤) (hδ : 0 < δr)
    (hg : MemLp g p (volume : Measure (Vec3 × ℝ))) :
    MemLp (spaceTimeMollify g δr hδ) p (volume : Measure (Vec3 × ℝ)) := by
  rw [memLp_iff]
  exact lt_of_le_of_lt
    (localEnergy_spaceTimeMollify_eLpNorm_le hp hpTop hδ hg) hg

/-- Smooth compactly supported energy-test coefficients have the exponents needed for the
space-time Hölder pairings in the energy identity. -/
theorem localEnergy_testCoefficients
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    MemLp (fun z : Vec3 × ℝ => timePartial ψ z +
      ∑ i : Fin 3, spatialSecondPartial ψ i i z) 2 (volume : Measure (Vec3 × ℝ)) ∧
    (∀ i : Fin 3, MemLp (fun z : Vec3 × ℝ => spatialPartial ψ i z)
      4 (volume : Measure (Vec3 × ℝ))) ∧
    (∀ i : Fin 3, MemLp (fun z : Vec3 × ℝ => spatialPartial ψ i z)
      12 (volume : Measure (Vec3 × ℝ))) ∧
    MemLp ψ ⊤ (volume : Measure (Vec3 × ℝ)) := by
  let lap : Vec3 × ℝ → ℝ := fun z : Vec3 × ℝ =>
    ∑ i : Fin 3, spatialSecondPartial ψ i i z
  have htimeC : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial ψ z) :=
    CKN.contDiff_timePartial hψ
  have hsecC (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialSecondPartial ψ i i z) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial
        (fun w : Vec3 × ℝ => spatialPartial ψ i w) i z)
    exact CKN.spatialPartial_contDiff (CKN.spatialPartial_contDiff hψ i) i
  have hlapC : ContDiff ℝ (⊤ : ℕ∞) lap := by
    dsimp [lap]
    exact ContDiff.sum (fun i hi => hsecC i)
  have htimeCpt : HasCompactSupport (fun z : Vec3 × ℝ => timePartial ψ z) :=
    CKN.hasCompactSupport_timePartial hψc
  have hsecCpt (i : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ => spatialSecondPartial ψ i i z) :=
    CKN.hasCompactSupport_spatialSecondPartial hψc i i
  have hlapCpt : HasCompactSupport lap := by
    apply HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    intro z hz
    by_contra hnot
    have hzero : ∀ i : Fin 3, spatialSecondPartial ψ i i z = 0 := by
      intro i
      exact CKN.spatialSecondPartial_eq_zero_off_tsupport hnot i i
    simp [lap, hzero] at hz
  have hAC : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial ψ z +
        ∑ i : Fin 3, spatialSecondPartial ψ i i z) := by
    exact htimeC.add hlapC
  have hApt : HasCompactSupport
      (fun z : Vec3 × ℝ => timePartial ψ z +
        ∑ i : Fin 3, spatialSecondPartial ψ i i z) :=
    htimeCpt.add hlapCpt
  have hBC (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial ψ i z) := CKN.spatialPartial_contDiff hψ i
  have hBCpt (i : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ => spatialPartial ψ i z) :=
    CKN.hasCompactSupport_spatialPartial hψc i
  refine ⟨localEnergy_smoothCompact_memLp hAC hApt 2, ?_, ?_, ?_⟩
  · intro i
    exact localEnergy_smoothCompact_memLp (hBC i) (hBCpt i) 4
  · intro i
    exact localEnergy_smoothCompact_memLp (hBC i) (hBCpt i) 12
  · exact localEnergy_smoothCompact_memLp hψ hψc ⊤

private theorem localEnergy_tendsto_eLpNorm_mul3_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q r s t : ℝ≥0∞} [hpqr : ENNReal.HolderTriple p q r]
    [hrst : ENNReal.HolderTriple r s t]
    (hr : 1 ≤ r) (ht : 1 ≤ t) {f g h : α → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g q μ) (hh : MemLp h s μ)
    {fn gn hn : ℕ → α → ℝ}
    (hfn : ∀ n, MemLp (fn n) p μ) (hgn : ∀ n, MemLp (gn n) q μ)
    (hhn : ∀ n, MemLp (hn n) s μ)
    (hfnLim : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) p μ)
      atTop (nhds 0))
    (hgnLim : Tendsto (fun n => eLpNorm (fun x => gn n x - g x) q μ)
      atTop (nhds 0))
    (hhnLim : Tendsto (fun n => eLpNorm (fun x => hn n x - h x) s μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm
      (fun x => fn n x * gn n x * hn n x - f x * g x * h x) t μ)
      atTop (nhds 0) := by
  have hfg : MemLp (fun x => f x * g x) r μ := hf.mul hg
  have hfgN (n : ℕ) : MemLp (fun x => fn n x * gn n x) r μ := (hfn n).mul (hgn n)
  have hfgLim := localEnergy_tendsto_eLpNorm_mul_sub
    (p := p) (q := q) (r := r) hr hf hg hfn hgn hfnLim hgnLim
  have hfinal := localEnergy_tendsto_eLpNorm_mul_sub
    (p := r) (q := s) (r := t) ht hfg hh hfgN hhn hfgLim hhnLim
  exact hfinal

/-- Sums of two convergent sequences converge in an `Lᵖ` seminorm when `p ≥ 1`. -/
theorem localEnergy_tendsto_eLpNorm_add_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) {f g : α → ℝ} {fn gn : ℕ → α → ℝ}
    (hfn : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) p μ)
      atTop (nhds 0))
    (hgn : Tendsto (fun n => eLpNorm (fun x => gn n x - g x) p μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm
      (fun x => fn n x + gn n x - (f x + g x)) p μ) atTop (nhds 0) := by
  have hsum : Tendsto (fun n =>
      eLpNorm (fun x => fn n x - f x) p μ +
        eLpNorm (fun x => gn n x - g x) p μ) atTop (nhds 0) := by
    simpa using hfn.add hgn
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · filter_upwards with n
    exact bot_le
  · filter_upwards with n
    have hpoint : (fun x => fn n x + gn n x - (f x + g x)) =
        fun x => (fn n x - f x) + (gn n x - g x) := by
      funext x
      ring
    rw [hpoint]
    exact eLpNorm_add_le hp

private theorem localEnergy_tendsto_eLpNorm_diff_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) {f : α → ℝ} {fn gn : ℕ → α → ℝ}
    (hfn : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) p μ)
      atTop (nhds 0))
    (hgn : Tendsto (fun n => eLpNorm (fun x => gn n x - f x) p μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun x => fn n x - gn n x) p μ)
      atTop (nhds 0) := by
  have hbound : ∀ n, eLpNorm (fun x => fn n x - gn n x) p μ ≤
      eLpNorm (fun x => fn n x - f x) p μ + eLpNorm (fun x => gn n x - f x) p μ := by
    intro n
    have heq : (fun x => fn n x - gn n x) =
        fun x => (fn n x - f x) - (gn n x - f x) := by
      funext x
      ring
    rw [heq]
    exact eLpNorm_sub_le hp
  have hsum : Tendsto (fun n =>
      eLpNorm (fun x => fn n x - f x) p μ +
        eLpNorm (fun x => gn n x - f x) p μ) atTop (nhds 0) := by
    simpa using hfn.add hgn
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · filter_upwards with n
    exact bot_le
  · filter_upwards with n
    exact hbound n

/-- The unit-cylinder zero extensions have the Lebesgue integrability needed for mollification. -/
theorem localEnergy_zeroExtensionLp
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i)) :
    (∀ i : Fin 3, MemLp
      ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
        (fun z : Vec3 × ℝ => u z i)) 4 (volume : Measure (Vec3 × ℝ))) ∧
    (∀ i j : Fin 3, MemLp
      ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
        (fun z : Vec3 × ℝ => u z i * u z j)) 2 (volume : Measure (Vec3 × ℝ))) ∧
    (∀ i j : Fin 3, MemLp
      ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
        (fun z : Vec3 × ℝ => Du z i j)) 2 (volume : Measure (Vec3 × ℝ))) ∧
    MemLp ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator p)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
  let U : Set (Vec3 × ℝ) := vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo
  have hu4para := velocity_memLp_four_unit_of_essLocalData hu hDu henergy hL3 hgrad
  have hu4prod : MemLp (fun z : Vec3 × ℝ => u z) 4
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    have h := localEnergy_memLp_parabolic_to_product hu4para
    simpa [U] using h
  have hDu2para := (energyL2_components_memLp hu hDu henergy).2
  have hDu2prod : MemLp (fun z : Vec3 × ℝ => Du z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    have h := localEnergy_memLp_parabolic_to_product hDu2para
    simpa [U] using h
  have hpProd : MemLp (fun z : Vec3 × ℝ => p z) (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    have h := localEnergy_memLp_parabolic_to_product hpLp
    simpa [U] using h
  have hu4i (i : Fin 3) : MemLp (fun z : Vec3 × ℝ => u z i) 4
      ((volume : Measure (Vec3 × ℝ)).restrict U) := (memLp_pi_iff.mp hu4prod) i
  have hDu2ij (i j : Fin 3) : MemLp (fun z : Vec3 × ℝ => Du z i j) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U) :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp hDu2prod) i)) j
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa [U] using
      ((memLp_indicator_iff_restrict hUmeas).2 (hu4i i))
  · intro i j
    have hF : MemLp (fun z : Vec3 × ℝ => u z i * u z j) 2
        ((volume : Measure (Vec3 × ℝ)).restrict U) :=
      MeasureTheory.MemLp.mul (p := 4) (q := 4) (r := 2) (hu4i i) (hu4i j)
    simpa [U] using ((memLp_indicator_iff_restrict hUmeas).2 hF)
  · intro i j
    simpa [U] using ((memLp_indicator_iff_restrict hUmeas).2 (hDu2ij i j))
  · simpa [U] using ((memLp_indicator_iff_restrict hUmeas).2 hpProd)

/-- A compactly supported test admits positive mollifier scales whose convolution neighborhoods
stay within the unit cylinder. -/
theorem localEnergy_exists_scales_for_test
    {ψ : Vec3 × ℝ → ℝ}
    (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℕ → ℝ,
      Tendsto δ atTop (nhds 0) ∧ (∀ n, 0 < δ n) ∧
      ∀ n z, z ∈ tsupport ψ →
        Metric.closedBall z (3 * δ n) ⊆ vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0 := by
  let U : Set (Vec3 × ℝ) := vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0
  have hUopen : IsOpen U := by
    dsimp [U]
    exact (isOpen_vec3Ball (0 : Vec3) 1).prod isOpen_Ioo
  obtain ⟨ε, hε, hbuffer⟩ := hψc.isCompact.exists_cthickening_subset_open hUopen (by
    simpa [U] using hψU)
  let δ : ℕ → ℝ := fun n => (ε / 3) * ((n : ℝ) + 1)⁻¹
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hδ : Tendsto δ atTop (nhds 0) := by
    simpa [δ] using (tendsto_const_nhds.mul hinv :
      Tendsto (fun n : ℕ => (ε / 3) * ((n : ℝ) + 1)⁻¹) atTop (nhds ((ε / 3) * 0)))
  refine ⟨ε, hε, δ, hδ, ?_, ?_⟩
  · intro n
    dsimp [δ]
    positivity
  · intro n z hz y hy
    have hythick : y ∈ Metric.cthickening (3 * δ n) (tsupport ψ) :=
      Metric.closedBall_subset_cthickening hz (3 * δ n) hy
    have hn : 3 * δ n ≤ ε := by
      dsimp [δ]
      have hone : 1 ≤ (n : ℝ) + 1 := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith only [hn0]
      have hrecip : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by linarith only [hone])]
        exact hone
      calc
        3 * ((ε / 3) * ((n : ℝ) + 1)⁻¹) = ε * ((n : ℝ) + 1)⁻¹ := by ring
        _ ≤ ε := mul_le_of_le_one_right hε.le hrecip
    have hmono : Metric.cthickening (3 * δ n) (tsupport ψ) ⊆
        Metric.cthickening ε (tsupport ψ) := Metric.cthickening_mono hn _
    exact hbuffer (hmono hythick)

/-- The scalar zero extensions converge to their mollifications in the exponents used by the
local energy identity. -/
theorem localEnergy_mollifiedInputs_tendsto
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (nhds 0)) (hδpos : ∀ n, 0 < δ n) :
    (∀ i : Fin 3, Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => u q i)) (δ n) (hδpos n) z -
        (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => u q i) z) 4 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0)) ∧
    (∀ i j : Fin 3, Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => u q i * u q j)) (δ n) (hδpos n) z -
        (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => u q i * u q j) z) 2 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0)) ∧
    (∀ i j : Fin 3, Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => Du q i j)) (δ n) (hδpos n) z -
        (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => Du q i j) z) 2 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0)) ∧
    Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator p)
          (δ n) (hδpos n) z - (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator p z)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
  have hExt := localEnergy_zeroExtensionLp hu hDu henergy hpLp hL3 hgrad
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact tendsto_eLpNorm_sub_zero_spaceTimeMollify_lp
      (by norm_num : (1 : ℝ≥0∞) ≤ 4) (by norm_num) (hExt.1 i) hδ hδpos
  · intro i j
    exact tendsto_eLpNorm_sub_zero_spaceTimeMollify_lp
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num)
      (hExt.2.1 i j) hδ hδpos
  · intro i j
    exact tendsto_eLpNorm_sub_zero_spaceTimeMollify_lp
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num)
      (hExt.2.2.1 i j) hδ hδpos
  · exact tendsto_eLpNorm_sub_zero_spaceTimeMollify_lp
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) (by norm_num)
      hExt.2.2.2 hδ hδpos

/-- Products of the mollified velocity, stress, gradient, and pressure converge in the
Lebesgue exponents used by the local energy identity. -/
theorem localEnergy_mollifiedProducts_tendsto
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (nhds 0)) (hδpos : ∀ n, 0 < δ n) :
    (∀ i : Fin 3, Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i -
        localEnergyVelocityZeroExtension u i z * localEnergyVelocityZeroExtension u i z)
      2 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0)) ∧
    (∀ i j : Fin 3, Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z j -
        localEnergyVelocityZeroExtension u i z *
          localEnergyVelocityZeroExtension u i z * localEnergyVelocityZeroExtension u j z)
      (ENNReal.ofReal (4 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ))) atTop (nhds 0)) ∧
    (∀ i : Fin 3, Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedPressure p (δ n) (hδpos n) z *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i -
        localEnergyPressureZeroExtension p z * localEnergyVelocityZeroExtension u i z)
      (ENNReal.ofReal (12 / 11 : ℝ)) (volume : Measure (Vec3 × ℝ))) atTop (nhds 0)) ∧
    (∀ i j : Fin 3, Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z j)
      2 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0)) ∧
    (∀ i j : Fin 3, Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j *
            localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j -
          localEnergyGradientZeroExtension Du i j z *
            localEnergyGradientZeroExtension Du i j z)
      1 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0)) := by
  have hExt := localEnergy_zeroExtensionLp hu hDu henergy hpLp hL3 hgrad
  have hInputs := localEnergy_mollifiedInputs_tendsto hu hDu henergy hpLp hL3 hgrad hδ hδpos
  have huN (n : ℕ) (i : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => localEnergyMollifiedVelocity u (δ n) (hδpos n) z i) 4
      (volume : Measure (Vec3 × ℝ)) := by
    exact localEnergy_mollify_memLp (by norm_num) (by norm_num) (hδpos n) (hExt.1 i)
  have hFN (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => localEnergyMollifiedTensor u (δ n) (hδpos n) z i j) 2
      (volume : Measure (Vec3 × ℝ)) := by
    exact localEnergy_mollify_memLp (by norm_num) (by norm_num) (hδpos n) (hExt.2.1 i j)
  have hGN (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j) 2
      (volume : Measure (Vec3 × ℝ)) := by
    exact localEnergy_mollify_memLp (by norm_num) (by norm_num) (hδpos n) (hExt.2.2.1 i j)
  have hpN (n : ℕ) : MemLp
      (localEnergyMollifiedPressure p (δ n) (hδpos n))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    exact localEnergy_mollify_memLp
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) (by norm_num)
      (hδpos n) hExt.2.2.2
  have huLim (i : Fin 3) : Tendsto
      (fun n => eLpNorm (fun z : Vec3 × ℝ =>
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i -
          localEnergyVelocityZeroExtension u i z) 4 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    simpa [localEnergyMollifiedVelocity, localEnergyVelocityZeroExtension,
      localEnergyUnitProductCylinder] using hInputs.1 i
  have hFLim (i j : Fin 3) : Tendsto
      (fun n => eLpNorm (fun z : Vec3 × ℝ =>
        localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
          localEnergyTensorZeroExtension u i j z) 2 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    simpa [localEnergyMollifiedTensor, localEnergyTensorZeroExtension,
      localEnergyUnitProductCylinder] using hInputs.2.1 i j
  have hGLim (i j : Fin 3) : Tendsto
      (fun n => eLpNorm (fun z : Vec3 × ℝ =>
        localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j -
          localEnergyGradientZeroExtension Du i j z) 2 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    simpa [localEnergyMollifiedGradient, localEnergyGradientZeroExtension,
      localEnergyUnitProductCylinder] using hInputs.2.2.1 i j
  have hpLim : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => localEnergyMollifiedPressure p (δ n) (hδpos n) z -
        localEnergyPressureZeroExtension p z)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    simpa [localEnergyMollifiedPressure, localEnergyPressureZeroExtension,
      localEnergyUnitProductCylinder] using hInputs.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact localEnergy_tendsto_eLpNorm_mul_sub
      (p := (4 : ℝ≥0∞)) (q := 4) (r := 2) (by norm_num)
      (hExt.1 i) (hExt.1 i) (fun n => huN n i) (fun n => huN n i)
      (huLim i) (huLim i)
  · intro i j
    exact localEnergy_tendsto_eLpNorm_mul3_sub
      (p := 4) (q := 4) (r := 2) (s := 4)
      (hr := by norm_num) (ht := by norm_num)
      (hExt.1 i) (hExt.1 i) (hExt.1 j)
      (fun n => huN n i) (fun n => huN n i) (fun n => huN n j)
      (huLim i) (huLim i) (huLim j)
  · intro i
    exact localEnergy_tendsto_eLpNorm_mul_sub
      (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := 4)
      (r := ENNReal.ofReal (12 / 11 : ℝ))
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (12 / 11 : ℝ))
      hExt.2.2.2 (hExt.1 i) hpN (fun n => huN n i)
      hpLim (huLim i)
  · intro i j
    have hFid : localEnergyTensorZeroExtension u i j =
        fun z : Vec3 × ℝ => localEnergyVelocityZeroExtension u i z *
          localEnergyVelocityZeroExtension u j z := by
      funext z
      by_cases hz : z ∈ localEnergyUnitProductCylinder
      · change z ∈ vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0 at hz
        rw [localEnergyTensorZeroExtension, localEnergyVelocityZeroExtension,
          localEnergyVelocityZeroExtension, localEnergyUnitProductCylinder]
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
          Set.indicator_of_mem hz]
      · change z ∉ vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0 at hz
        rw [localEnergyTensorZeroExtension, localEnergyVelocityZeroExtension,
          localEnergyVelocityZeroExtension, localEnergyUnitProductCylinder]
        rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
          Set.indicator_of_notMem hz]
        ring
    have hProdLim : Tendsto (fun n => eLpNorm
        (fun z : Vec3 × ℝ =>
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z j -
          localEnergyTensorZeroExtension u i j z) 2 (volume : Measure (Vec3 × ℝ)))
        atTop (nhds 0) := by
      have h := localEnergy_tendsto_eLpNorm_mul_sub
        (p := 4) (q := 4) (r := 2) (by norm_num)
        (hExt.1 i) (hExt.1 j) (fun n => huN n i) (fun n => huN n j)
        (huLim i) (huLim j)
      exact h.congr' (Filter.Eventually.of_forall fun n => by
        apply eLpNorm_congr_ae
        filter_upwards [] with z
        rw [hFid]
        rfl)
    have hProdLim' : Tendsto (fun n => eLpNorm
        (fun z : Vec3 × ℝ =>
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z j -
          localEnergyTensorZeroExtension u i j z) 2 (volume : Measure (Vec3 × ℝ)))
        atTop (nhds 0) := hProdLim
    exact localEnergy_tendsto_eLpNorm_diff_sub
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hFLim i j) hProdLim'
  · intro i j
    exact localEnergy_tendsto_eLpNorm_mul_sub
      (p := 2) (q := 2) (r := 1) (by norm_num)
      (hExt.2.2.1 i j) (hExt.2.2.1 i j)
      (fun n => hGN n i j) (fun n => hGN n i j)
      (hGLim i j) (hGLim i j)

end ESS
