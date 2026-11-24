/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PotentialL1
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicPullback

/-!
# Subgeodesics on the normalized strip

A subgeodesic is encoded exactly through its complexification on
`X × {τ : ℂ | 0 < re τ < 1}`.  In a holomorphic chart on `X`, adding a smooth
local potential of `θ` produces an actual plurisubharmonic function on the
product chart.  Endpoint convergence is the chart-local `L¹` convergence from
`PotentialL1`, rather than pointwise convergence or an abstract placeholder.

The pointwise convexity of slices, existence of the Perron geodesic, and its
energy properties are consequences of this definition.  They are deliberately
not stored as fields of the predicate below.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The normalized complex strip used to complexify a path of potentials. -/
def complexTimeStrip : Set ℂ :=
  {τ | τ.re ∈ Ioo (0 : ℝ) 1}

@[simp] theorem mem_complexTimeStrip {τ : ℂ} :
    τ ∈ complexTimeStrip ↔ 0 < τ.re ∧ τ.re < 1 := Iff.rfl

theorem isOpen_complexTimeStrip : IsOpen complexTimeStrip := by
  exact isOpen_Ioo.preimage Complex.continuous_re

/-- The product of a spatial chart domain with the normalized complex strip. -/
def geodesicChartDomain (W : Set (ComplexModel n)) :
    Set (ComplexModel n × ℂ) :=
  W ×ˢ complexTimeStrip

theorem isOpen_geodesicChartDomain {W : Set (ComplexModel n)} (hW : IsOpen W) :
    IsOpen (geodesicChartDomain W) :=
  hW.prod isOpen_complexTimeStrip

@[simp] theorem mem_geodesicChartDomain {W : Set (ComplexModel n)}
    {p : ComplexModel n × ℂ} :
    p ∈ geodesicChartDomain W ↔ p.1 ∈ W ∧ 0 < p.2.re ∧ p.2.re < 1 := by
  rfl

/-- Affine reparametrization of the normalized real interval onto `[a,b]`. -/
def affineTimeReparam (a b t : ℝ) : ℝ :=
  a + (b - a) * t

@[simp] theorem affineTimeReparam_zero (a b : ℝ) :
    affineTimeReparam a b 0 = a := by
  simp [affineTimeReparam]

@[simp] theorem affineTimeReparam_one (a b : ℝ) :
    affineTimeReparam a b 1 = b := by
  simp [affineTimeReparam]

theorem affineTimeReparam_mem_Ioo {a b t : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    affineTimeReparam a b t ∈ Ioo (0 : ℝ) 1 := by
  constructor <;> unfold affineTimeReparam
  · have hmul : 0 < (b - a) * t := mul_pos (sub_pos.mpr hab) ht.1
    linarith
  · have hmul : (b - a) * t < b - a :=
      mul_lt_of_lt_one_right (sub_pos.mpr hab) ht.2
    linarith

theorem tendsto_affineTimeReparam_nhdsGT_zero {a b : ℝ} (hab : a < b) :
    Tendsto (affineTimeReparam a b) (𝓝[>] (0 : ℝ)) (𝓝[>] a) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hmul : Tendsto (fun t : ℝ => (b - a) * t) (𝓝[>] (0 : ℝ))
        (𝓝 ((b - a) * 0)) := tendsto_const_nhds.mul ht
    have hconst : Tendsto (fun _ : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 a) :=
      tendsto_const_nhds
    change Tendsto (fun t : ℝ => a + (b - a) * t) (𝓝[>] (0 : ℝ)) (𝓝 a)
    simpa using hconst.add hmul
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change a < affineTimeReparam a b t
    unfold affineTimeReparam
    exact lt_add_of_pos_right a (mul_pos (sub_pos.mpr hab) ht)

theorem tendsto_affineTimeReparam_nhdsLT_one {a b : ℝ} (hab : a < b) :
    Tendsto (affineTimeReparam a b) (𝓝[<] (1 : ℝ)) (𝓝[<] b) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have ht : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hmul : Tendsto (fun t : ℝ => (b - a) * t) (𝓝[<] (1 : ℝ))
        (𝓝 ((b - a) * 1)) := tendsto_const_nhds.mul ht
    have hconst : Tendsto (fun _ : ℝ => a) (𝓝[<] (1 : ℝ)) (𝓝 a) :=
      tendsto_const_nhds
    change Tendsto (fun t : ℝ => a + (b - a) * t) (𝓝[<] (1 : ℝ)) (𝓝 b)
    simpa using hconst.add hmul
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change affineTimeReparam a b t < b
    unfold affineTimeReparam
    have hmul : (b - a) * t < (b - a) * 1 :=
      mul_lt_mul_of_pos_left ht (sub_pos.mpr hab)
    linarith

/-- Time reversal sends the right filter at zero to the left filter at one. -/
theorem tendsto_one_sub_nhdsGT_zero :
    Tendsto (fun t : ℝ => 1 - t) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
      tendsto_const_nhds
    simpa using hc.sub ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 1 - t < 1
    exact sub_lt_self 1 ht

/-- Time reversal sends the left filter at one to the right filter at zero. -/
theorem tendsto_one_sub_nhdsLT_one :
    Tendsto (fun t : ℝ => 1 - t) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have ht : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_const_nhds
    simpa using hc.sub ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < 1 - t
    exact sub_pos.mpr ht

/-- The complex-linear part of affine time reparametrization on a product
chart.  It fixes the spatial coordinate and multiplies complex time by the
real interval length `b-a`. -/
def complexTimeReparamLinear (a b : ℝ) :
    ComplexModel n × ℂ →L[ℂ] ComplexModel n × ℂ :=
  (ContinuousLinearMap.fst ℂ (ComplexModel n) ℂ).prod
    (((b - a : ℝ) : ℂ) •
      ContinuousLinearMap.snd ℂ (ComplexModel n) ℂ)

/-- The translation part of affine time reparametrization. -/
def complexTimeReparamTranslation (a : ℝ) : ComplexModel n × ℂ :=
  (0, (a : ℂ))

@[simp] theorem complexTimeReparam_affine_apply (a b : ℝ)
    (p : ComplexModel n × ℂ) :
    complexTimeReparamTranslation (n := n) a +
        complexTimeReparamLinear (n := n) a b p =
      (p.1, (a : ℂ) + ((b - a : ℝ) : ℂ) * p.2) := by
  simp [complexTimeReparamTranslation, complexTimeReparamLinear]

theorem complexTimeReparam_mapsTo_geodesicChartDomain
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (W : Set (ComplexModel n)) :
    MapsTo
      (fun p => complexTimeReparamTranslation (n := n) a +
        complexTimeReparamLinear (n := n) a b p)
      (geodesicChartDomain W) (geodesicChartDomain W) := by
  rintro p ⟨hpW, hp⟩
  change complexTimeReparamTranslation (n := n) a +
      complexTimeReparamLinear (n := n) a b p ∈ geodesicChartDomain W
  rw [complexTimeReparam_affine_apply]
  refine ⟨hpW, ?_⟩
  simpa [Complex.add_re, Complex.mul_re, affineTimeReparam] using
    affineTimeReparam_mem_Ioo ha hb hab hp

/-- Reparametrize a curve from the normalized interval to the subinterval
`[a,b]`. -/
def affineReparametrizedCurve (curve : ℝ → M → EReal) (a b : ℝ) :
    ℝ → M → EReal :=
  fun t => curve (affineTimeReparam a b t)

/-- Reverse the real-time parameter on the normalized interval. -/
def timeReversedCurve (curve : ℝ → M → EReal) : ℝ → M → EReal :=
  fun t => curve (1 - t)

/-- The extended-real chord joining two potential values.  Interior-time
coefficients are strictly positive, so the usual convention sends a pole at
either endpoint to a pole on the chord. -/
def eRealChord (a b : EReal) (t : ℝ) : EReal :=
  ((1 - t : ℝ) : EReal) * a + ((t : ℝ) : EReal) * b

omit [TopologicalSpace M] in
@[simp] theorem affineReparametrizedCurve_apply
    (curve : ℝ → M → EReal) (a b t : ℝ) (x : M) :
    affineReparametrizedCurve curve a b t x =
      curve (affineTimeReparam a b t) x := rfl

omit [TopologicalSpace M] in
@[simp] theorem timeReversedCurve_apply
    (curve : ℝ → M → EReal) (t : ℝ) (x : M) :
    timeReversedCurve curve t x = curve (1 - t) x := rfl

omit [TopologicalSpace M] in
@[simp] theorem timeReversedCurve_timeReversed (curve : ℝ → M → EReal) :
    timeReversedCurve (timeReversedCurve curve) = curve := by
  funext t x
  simp [timeReversedCurve]

/-- In a chart and after choosing a local potential `ρ` of `θ`, this is the
local representative of the complexified path plus the pullback of `ρ` from
the spatial factor. -/
def subgeodesicChartFunction (curve : ℝ → M → EReal)
    (e : ComplexChart n M) (ρ : ComplexModel n → ℝ) :
    ComplexModel n × ℂ → EReal :=
  fun p => chartFunction (curve p.2.re) e p.1 + (ρ p.1 : EReal)

omit [IsComplexManifold n M] in
@[simp] theorem subgeodesicChartFunction_apply
    (curve : ℝ → M → EReal) (e : ComplexChart n M)
    (ρ : ComplexModel n → ℝ) (z : ComplexModel n) (τ : ℂ) :
    subgeodesicChartFunction curve e ρ (z, τ) =
      chartFunction (curve τ.re) e z + (ρ z : EReal) := rfl

/-- Interior subgeodesic condition on `(0,1)`.  Every real slice is an actual
`θ`-PSH potential, and the complexification is locally `p₁*θ`-PSH because it
becomes genuinely PSH after adding a local potential pulled back from `X`. -/
def IsSubgeodesicInterior (θ : SmoothRealForm n M 2)
    (curve : ℝ → M → EReal) : Prop :=
  (∀ t ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ (curve t)) ∧
    ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ),
        z ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧
          PlurisubharmonicOn (subgeodesicChartFunction curve e ρ)
            (geodesicChartDomain W)

theorem IsSubgeodesicInterior.thetaPshPotential
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (h : IsSubgeodesicInterior θ curve) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    IsThetaPshPotential θ (curve t) :=
  h.1 t ht

theorem IsSubgeodesicInterior.complexified_psh
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (h : IsSubgeodesicInterior θ curve) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ),
      z ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧
        PlurisubharmonicOn (subgeodesicChartFunction curve e ρ)
          (geodesicChartDomain W) :=
  h.2 e z hz

/-- Restrict an interior subgeodesic to a nondegenerate closed subinterval and
affinely reparametrize it back to `(0,1)`.  This is the strip-PSH part of
restriction; identifying the new endpoint `L¹` limits requires the separate
interior-continuity theorem. -/
theorem IsSubgeodesicInterior.affineReparametrized
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (h : IsSubgeodesicInterior theta curve)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    IsSubgeodesicInterior theta (affineReparametrizedCurve curve a b) := by
  constructor
  · intro t ht
    exact h.thetaPshPotential (affineTimeReparam_mem_Ioo ha hb hab ht)
  · intro e z hz
    rcases h.complexified_psh e hz with ⟨W, rho, hzW, hrho, hpsh⟩
    refine ⟨W, rho, hzW, hrho, ?_⟩
    have hpull := hpsh.comp_affine
      (complexTimeReparamLinear (n := n) a b)
      (complexTimeReparamTranslation (n := n) a)
    have hmono : geodesicChartDomain W ⊆
        (fun p => complexTimeReparamTranslation (n := n) a +
          complexTimeReparamLinear (n := n) a b p) ⁻¹'
            geodesicChartDomain W :=
      complexTimeReparam_mapsTo_geodesicChartDomain ha hb hab W
    have hrestricted := hpull.mono hmono
    change PlurisubharmonicOn
      (fun p => chartFunction (curve (a + (b - a) * p.2.re)) e p.1 +
        (rho p.1 : EReal)) (geodesicChartDomain W)
    simpa [complexTimeReparamTranslation, complexTimeReparamLinear,
      Complex.add_re, Complex.mul_re] using hrestricted

/-- Reversing the normalized time coordinate preserves the strip-PSH
condition and exchanges its two ends. -/
theorem IsSubgeodesicInterior.timeReversed
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (h : IsSubgeodesicInterior theta curve) :
    IsSubgeodesicInterior theta (timeReversedCurve curve) := by
  constructor
  · intro t ht
    exact h.thetaPshPotential ⟨sub_pos.mpr ht.2, sub_lt_self 1 ht.1⟩
  · intro e z hz
    rcases h.complexified_psh e hz with ⟨W, rho, hzW, hrho, hpsh⟩
    refine ⟨W, rho, hzW, hrho, ?_⟩
    have hpull := hpsh.comp_affine
      (complexTimeReparamLinear (n := n) 1 0)
      (complexTimeReparamTranslation (n := n) 1)
    have hmono : geodesicChartDomain W ⊆
        (fun p => complexTimeReparamTranslation (n := n) 1 +
          complexTimeReparamLinear (n := n) 1 0 p) ⁻¹'
            geodesicChartDomain W := by
      rintro p ⟨hpW, hp0, hp1⟩
      change complexTimeReparamTranslation (n := n) 1 +
          complexTimeReparamLinear (n := n) 1 0 p ∈ geodesicChartDomain W
      rw [complexTimeReparam_affine_apply]
      refine ⟨hpW, ?_, ?_⟩ <;>
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero] <;> linarith
    have hrestricted := hpull.mono hmono
    change PlurisubharmonicOn
      (fun p => chartFunction (curve (1 - p.2.re)) e p.1 +
        (rho p.1 : EReal)) (geodesicChartDomain W)
    simpa [complexTimeReparamTranslation, complexTimeReparamLinear,
      Complex.add_re, Complex.mul_re, timeReversedCurve, sub_eq_add_neg] using hrestricted

/-- A subgeodesic from `u₀` to `u₁` on the normalized interval.  The endpoints
are themselves `θ`-PSH potentials and the interior path converges to them in
the genuine chart-local `L¹` topology from the right and left, respectively. -/
def IsSubgeodesicFrom (θ : SmoothRealForm n M 2)
    (curve : ℝ → M → EReal) (u₀ u₁ : M → EReal) : Prop :=
  IsThetaPshPotential θ u₀ ∧
    IsThetaPshPotential θ u₁ ∧
      IsSubgeodesicInterior θ curve ∧
        ManifoldL1LocallyTendsto (n := n) curve (𝓝[>] (0 : ℝ)) u₀ ∧
          ManifoldL1LocallyTendsto (n := n) curve (𝓝[<] (1 : ℝ)) u₁

/-- A genuine theta-PSH potential gives a constant strip subgeodesic.  The
strip-PSH assertion is the pullback of each spatial local representative by
the complex-linear projection onto the chart coordinate. -/
theorem isSubgeodesicInterior_const {theta : SmoothRealForm n M 2}
    {u : M → EReal} (hu : IsThetaPshPotential theta u) :
    IsSubgeodesicInterior theta (fun _ : ℝ => u) := by
  constructor
  · intro _ _
    exact hu
  · intro e z hz
    rcases hu.1 e z hz with ⟨W, rho, hzW, hrho, hpsh⟩
    refine ⟨W, rho, hzW, hrho, ?_⟩
    let spatialProjection :
        ComplexModel n × ℂ →L[ℂ] ComplexModel n :=
      ContinuousLinearMap.fst ℂ (ComplexModel n) ℂ
    have hpull := hpsh.comp_continuousLinearMap spatialProjection
    have hmono : geodesicChartDomain W ⊆ spatialProjection ⁻¹' W := by
      intro p hp
      exact hp.1
    have hrestricted := hpull.mono hmono
    change PlurisubharmonicOn
      (fun p => chartFunction u e p.1 + (rho p.1 : EReal))
      (geodesicChartDomain W)
    simpa [spatialProjection] using hrestricted

/-- The constant curve at a theta-PSH potential has the prescribed endpoint
limits in the actual chart-local `L¹` topology. -/
theorem isSubgeodesicFrom_const {theta : SmoothRealForm n M 2}
    {u : M → EReal} (hu : IsThetaPshPotential theta u) :
    IsSubgeodesicFrom theta (fun _ : ℝ => u) u u := by
  have hneTop : ∀ x, u x ≠ ⊤ := hu.1.quasiPlurisubharmonic.ne_top
  exact ⟨hu, hu, isSubgeodesicInterior_const hu,
    manifoldL1LocallyTendsto_const u hneTop (𝓝[>] (0 : ℝ)),
    manifoldL1LocallyTendsto_const u hneTop (𝓝[<] (1 : ℝ))⟩

/-- The full restriction theorem once the two interior `L¹` limits are
available.  The analytic continuity input is explicit: the proof below only
transports it through the affine time map and supplies the strip-PSH part from
`IsSubgeodesicInterior.affineReparametrized`. -/
theorem IsSubgeodesicInterior.affineReparametrized_isSubgeodesicFrom
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (h : IsSubgeodesicInterior theta curve)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a < b)
    (hleft : ManifoldL1LocallyTendsto (n := n) curve (𝓝[>] a) (curve a))
    (hright : ManifoldL1LocallyTendsto (n := n) curve (𝓝[<] b) (curve b)) :
    IsSubgeodesicFrom theta (affineReparametrizedCurve curve a b)
      (curve a) (curve b) := by
  refine ⟨h.thetaPshPotential ha, h.thetaPshPotential hb,
    h.affineReparametrized ha.1.le hb.2.le hab, ?_, ?_⟩
  · change ManifoldL1LocallyTendsto (n := n)
      (fun t => curve (affineTimeReparam a b t)) (𝓝[>] (0 : ℝ)) (curve a)
    exact hleft.comp (tendsto_affineTimeReparam_nhdsGT_zero hab)
  · change ManifoldL1LocallyTendsto (n := n)
      (fun t => curve (affineTimeReparam a b t)) (𝓝[<] (1 : ℝ)) (curve b)
    exact hright.comp (tendsto_affineTimeReparam_nhdsLT_one hab)

namespace IsSubgeodesicFrom

variable {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
  {u₀ u₁ : M → EReal}

theorem left_endpoint (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    IsThetaPshPotential θ u₀ :=
  h.1

theorem right_endpoint (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    IsThetaPshPotential θ u₁ :=
  h.2.1

theorem interior (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    IsSubgeodesicInterior θ curve :=
  h.2.2.1

theorem tendsto_left (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    ManifoldL1LocallyTendsto (n := n) curve (𝓝[>] (0 : ℝ)) u₀ :=
  h.2.2.2.1

theorem tendsto_right (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    ManifoldL1LocallyTendsto (n := n) curve (𝓝[<] (1 : ℝ)) u₁ :=
  h.2.2.2.2

/-- Time reversal exchanges the two prescribed endpoint potentials and their
one-sided chart-local `L¹` limits. -/
theorem timeReversed (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    IsSubgeodesicFrom θ (timeReversedCurve curve) u₁ u₀ := by
  refine ⟨h.right_endpoint, h.left_endpoint, h.interior.timeReversed, ?_, ?_⟩
  · change ManifoldL1LocallyTendsto (n := n)
      (fun t : ℝ => curve (1 - t)) (𝓝[>] (0 : ℝ)) u₁
    exact h.tendsto_right.comp tendsto_one_sub_nhdsGT_zero
  · change ManifoldL1LocallyTendsto (n := n)
      (fun t : ℝ => curve (1 - t)) (𝓝[<] (1 : ℝ)) u₀
    exact h.tendsto_left.comp tendsto_one_sub_nhdsLT_one

end IsSubgeodesicFrom

end

end SGPT.Foundations.Analysis.FirstPass
