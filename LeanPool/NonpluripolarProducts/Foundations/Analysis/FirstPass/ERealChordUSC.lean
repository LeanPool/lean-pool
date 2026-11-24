/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.Subgeodesics

/-!
# Upper semicontinuity of extended-real chords

Multiplication by a finite nonnegative real preserves upper semicontinuity of
`EReal`-valued functions.  Addition has to exclude the genuine indeterminacy
`⊤ + ⊥`; the hypotheses below that both summands avoid `⊤` are tailored to
quasi-plurisubharmonic functions.  These facts give both ambient and chartwise
upper-semicontinuity interfaces for `eRealChord`.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]

/-- A quasi-PSH germ is upper semicontinuous at its base point. -/
theorem QuasiPlurisubharmonicAt.upperSemicontinuousAt
    {u : E → EReal} {x : E} (hu : QuasiPlurisubharmonicAt u x) :
    UpperSemicontinuousAt u x := by
  obtain ⟨p, h, hp, hh, heq⟩ := hu
  have hhcont : ContinuousAt h x := hh.self_of_nhds.continuousAt
  have hcoe : ContinuousAt (fun y => (h y : EReal)) x :=
    continuous_coe_real_ereal.continuousAt.comp hhcont
  have hsum : UpperSemicontinuousAt (fun y => p y + (h y : EReal)) x :=
    hp.upperSemicontinuousAt.add' hcoe.upperSemicontinuousAt
      (EReal.continuousAt_add (Or.inl hp.ne_top) (Or.inr (EReal.coe_ne_top _)))
  rw [← upperSemicontinuousWithinAt_univ_iff]
  exact (hsum.upperSemicontinuousWithinAt univ).congr_of_eventuallyEq (mem_univ x)
    (heq.symm.filter_mono nhdsWithin_le_nhds)

/-- Quasi-PSH functions are upper semicontinuous on their domain. -/
theorem QuasiPlurisubharmonicOn.upperSemicontinuousOn
    {u : E → EReal} {U : Set E} (hu : QuasiPlurisubharmonicOn u U) :
    UpperSemicontinuousOn u U :=
  fun x hx => (hu x hx).upperSemicontinuousAt.upperSemicontinuousWithinAt U

namespace FirstPass

variable {X : Type*} [TopologicalSpace X]

/-- Multiplication on `EReal` by a fixed nonzero finite real is continuous. -/
theorem continuous_eReal_const_mul {c : ℝ} (hc : c ≠ 0) :
    Continuous (fun z : EReal => (c : EReal) * z) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact (EReal.continuousAt_mul
      (p := ((c : EReal), z))
      (Or.inl (by simpa using hc))
      (Or.inl (by simpa using hc))
      (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).comp
    (continuousAt_const.prodMk continuousAt_id)

/-- Multiplication on `EReal` by a finite nonnegative real is monotone. -/
theorem monotone_eReal_const_mul {c : ℝ} (hc : 0 ≤ c) :
    Monotone (fun z : EReal => (c : EReal) * z) :=
  fun _ _ h => mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr hc)

/-- A finite nonnegative real multiple of an upper semicontinuous
`EReal`-valued function is upper semicontinuous.  The limsup identity used here
also handles the zero coefficient, where multiplication is not continuous at
`(0, ±∞)`. -/
theorem upperSemicontinuous_eReal_const_mul
    {f : X → EReal} (hf : UpperSemicontinuous f) {c : ℝ} (hc : 0 ≤ c) :
    UpperSemicontinuous (fun x => (c : EReal) * f x) := by
  rw [upperSemicontinuous_iff_limsup_le]
  intro x
  rw [EReal.limsup_const_mul_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c)]
  exact mul_le_mul_of_nonneg_left (hf.limsup_le x) (EReal.coe_nonneg.mpr hc)

/-- The corresponding relative upper-semicontinuity statement on a set. -/
theorem upperSemicontinuousOn_eReal_const_mul
    {f : X → EReal} {U : Set X} (hf : UpperSemicontinuousOn f U)
    {c : ℝ} (hc : 0 ≤ c) :
    UpperSemicontinuousOn (fun x => (c : EReal) * f x) U := by
  rw [upperSemicontinuousOn_iff_limsup_le]
  intro x hx
  let _ : NeBot (𝓝[U] x) := nhdsWithin_neBot_of_mem hx
  rw [EReal.limsup_const_mul_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c)]
  exact mul_le_mul_of_nonneg_left (hf.limsup_le x hx) (EReal.coe_nonneg.mpr hc)

/-- A finite nonnegative real multiple cannot create `⊤` from a value which
was not `⊤`. -/
theorem eReal_const_mul_ne_top {c : ℝ} (hc : 0 ≤ c) {z : EReal} (hz : z ≠ ⊤) :
    (c : EReal) * z ≠ ⊤ := by
  rw [EReal.mul_ne_top]
  exact ⟨Or.inl (EReal.coe_ne_bot c),
    Or.inl (EReal.coe_nonneg.mpr hc),
    Or.inl (EReal.coe_ne_top c), Or.inr hz⟩

/-- The sum of two upper semicontinuous `EReal`-valued functions which avoid
`⊤` is upper semicontinuous. -/
theorem upperSemicontinuous_eReal_add
    {f g : X → EReal} (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
    (hftop : ∀ x, f x ≠ ⊤) (hgtop : ∀ x, g x ≠ ⊤) :
    UpperSemicontinuous (fun x => f x + g x) :=
  hf.add' hg fun x =>
    EReal.continuousAt_add (Or.inl (hftop x)) (Or.inr (hgtop x))

/-- The corresponding relative addition statement on a set. -/
theorem upperSemicontinuousOn_eReal_add
    {f g : X → EReal} {U : Set X}
    (hf : UpperSemicontinuousOn f U) (hg : UpperSemicontinuousOn g U)
    (hftop : ∀ x ∈ U, f x ≠ ⊤) (hgtop : ∀ x ∈ U, g x ≠ ⊤) :
    UpperSemicontinuousOn (fun x => f x + g x) U :=
  hf.add' hg fun x hx =>
    EReal.continuousAt_add (Or.inl (hftop x hx)) (Or.inr (hgtop x hx))

/-- A two-term finite nonnegative real linear combination preserves upper
semicontinuity for functions which avoid `⊤`. -/
theorem upperSemicontinuous_eReal_nonnegativeCombination
    {f g : X → EReal} (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
    (hftop : ∀ x, f x ≠ ⊤) (hgtop : ∀ x, g x ≠ ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    UpperSemicontinuous (fun x => (a : EReal) * f x + (b : EReal) * g x) :=
  upperSemicontinuous_eReal_add
    (upperSemicontinuous_eReal_const_mul hf ha)
    (upperSemicontinuous_eReal_const_mul hg hb)
    (fun x => eReal_const_mul_ne_top ha (hftop x))
    (fun x => eReal_const_mul_ne_top hb (hgtop x))

/-- The corresponding two-term relative statement on a set. -/
theorem upperSemicontinuousOn_eReal_nonnegativeCombination
    {f g : X → EReal} {U : Set X}
    (hf : UpperSemicontinuousOn f U) (hg : UpperSemicontinuousOn g U)
    (hftop : ∀ x ∈ U, f x ≠ ⊤) (hgtop : ∀ x ∈ U, g x ≠ ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    UpperSemicontinuousOn
      (fun x => (a : EReal) * f x + (b : EReal) * g x) U :=
  upperSemicontinuousOn_eReal_add
    (upperSemicontinuousOn_eReal_const_mul hf ha)
    (upperSemicontinuousOn_eReal_const_mul hg hb)
    (fun x hx => eReal_const_mul_ne_top ha (hftop x hx))
    (fun x hx => eReal_const_mul_ne_top hb (hgtop x hx))

/-- The pointwise extended-real chord of two upper semicontinuous functions
which avoid `⊤` is upper semicontinuous at every time in `[0,1]`. -/
theorem upperSemicontinuous_eRealChord
    {f g : X → EReal} (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
    (hftop : ∀ x, f x ≠ ⊤) (hgtop : ∀ x, g x ≠ ⊤)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    UpperSemicontinuous (fun x => eRealChord (f x) (g x) t) := by
  simpa only [eRealChord] using
    upperSemicontinuous_eReal_nonnegativeCombination hf hg hftop hgtop
      (sub_nonneg.mpr ht1) ht0

/-- The relative chart-domain version of upper semicontinuity of a chord. -/
theorem upperSemicontinuousOn_eRealChord
    {f g : X → EReal} {U : Set X}
    (hf : UpperSemicontinuousOn f U) (hg : UpperSemicontinuousOn g U)
    (hftop : ∀ x ∈ U, f x ≠ ⊤) (hgtop : ∀ x ∈ U, g x ≠ ⊤)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    UpperSemicontinuousOn (fun x => eRealChord (f x) (g x) t) U := by
  simpa only [eRealChord] using
    upperSemicontinuousOn_eReal_nonnegativeCombination hf hg hftop hgtop
      (sub_nonneg.mpr ht1) ht0

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A manifold quasi-PSH function is upper semicontinuous in the manifold
topology. -/
theorem ManifoldQuasiPlurisubharmonic.upperSemicontinuous
    {u : M → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u) :
    UpperSemicontinuous u := by
  intro x
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  have hchart : UpperSemicontinuousAt (chartFunction u e) (e.val x) :=
    (hu e (e.val x) hz).upperSemicontinuousAt
  have hcomp : UpperSemicontinuousAt ((chartFunction u e) ∘ e.val) x :=
    hchart.comp (e.val.continuousAt hx)
  have heq : ((chartFunction u e) ∘ e.val) =ᶠ[𝓝 x] u := by
    filter_upwards [e.val.open_source.mem_nhds hx] with y hy
    simp only [Function.comp_apply, chartFunction, e.val.left_inv hy]
  intro c hc
  have hc' : ((chartFunction u e) ∘ e.val) x < c := by
    rw [heq.eq_of_nhds]
    exact hc
  filter_upwards [hcomp c hc', heq] with y hy hyeq
  rw [← hyeq]
  exact hy

omit [IsComplexManifold n M] in
/-- Two manifold quasi-PSH endpoints give an upper semicontinuous chord. -/
theorem ManifoldQuasiPlurisubharmonic.upperSemicontinuous_eRealChord
    {u₀ u₁ : M → EReal}
    (hu₀ : ManifoldQuasiPlurisubharmonic (n := n) u₀)
    (hu₁ : ManifoldQuasiPlurisubharmonic (n := n) u₁)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    UpperSemicontinuous (fun x => eRealChord (u₀ x) (u₁ x) t) :=
  SGPT.Foundations.Analysis.FirstPass.upperSemicontinuous_eRealChord
    hu₀.upperSemicontinuous hu₁.upperSemicontinuous hu₀.ne_top hu₁.ne_top ht0 ht1

omit [IsComplexManifold n M] in
/-- Chartwise version of the chord USC statement for manifold quasi-PSH
endpoints.  This is the form used with chartwise almost-everywhere comparison. -/
theorem ManifoldQuasiPlurisubharmonic.upperSemicontinuousOn_chart_eRealChord
    {u₀ u₁ : M → EReal}
    (hu₀ : ManifoldQuasiPlurisubharmonic (n := n) u₀)
    (hu₁ : ManifoldQuasiPlurisubharmonic (n := n) u₁)
    (e : ComplexChart n M) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    UpperSemicontinuousOn
      (fun z => eRealChord (chartFunction u₀ e z) (chartFunction u₁ e z) t)
      e.val.target :=
  upperSemicontinuousOn_eRealChord
    (hu₀ e).upperSemicontinuousOn (hu₁ e).upperSemicontinuousOn
    (fun z hz => (hu₀ e z hz).ne_top) (fun z hz => (hu₁ e z hz).ne_top)
    ht0 ht1

/-- Two raw theta-PSH endpoints give an upper semicontinuous chord. -/
theorem ThetaPlurisubharmonic.upperSemicontinuous_eRealChord
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hu₀ : ThetaPlurisubharmonic θ u₀) (hu₁ : ThetaPlurisubharmonic θ u₁)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    UpperSemicontinuous (fun x => eRealChord (u₀ x) (u₁ x) t) :=
  hu₀.quasiPlurisubharmonic.upperSemicontinuous_eRealChord
    hu₁.quasiPlurisubharmonic ht0 ht1

/-- Chartwise chord USC for raw theta-PSH endpoints. -/
theorem ThetaPlurisubharmonic.upperSemicontinuousOn_chart_eRealChord
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hu₀ : ThetaPlurisubharmonic θ u₀) (hu₁ : ThetaPlurisubharmonic θ u₁)
    (e : ComplexChart n M) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    UpperSemicontinuousOn
      (fun z => eRealChord (chartFunction u₀ e z) (chartFunction u₁ e z) t)
      e.val.target :=
  hu₀.quasiPlurisubharmonic.upperSemicontinuousOn_chart_eRealChord
    hu₁.quasiPlurisubharmonic e ht0 ht1

/-- The potential predicate inherits the ambient chord USC interface. -/
theorem IsThetaPshPotential.upperSemicontinuous_eRealChord
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    UpperSemicontinuous (fun x => eRealChord (u₀ x) (u₁ x) t) :=
  hu₀.1.upperSemicontinuous_eRealChord hu₁.1 ht0 ht1

/-- The potential predicate inherits the chartwise chord USC interface. -/
theorem IsThetaPshPotential.upperSemicontinuousOn_chart_eRealChord
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (e : ComplexChart n M) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    UpperSemicontinuousOn
      (fun z => eRealChord (chartFunction u₀ e z) (chartFunction u₁ e z) t)
      e.val.target :=
  hu₀.1.upperSemicontinuousOn_chart_eRealChord hu₁.1 e ht0 ht1

namespace IsSubgeodesicFrom

variable {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
  {u₀ u₁ : M → EReal}

/-- The endpoint chord attached to a subgeodesic is upper semicontinuous. -/
theorem upperSemicontinuous_eRealChord
    (h : IsSubgeodesicFrom θ curve u₀ u₁)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    UpperSemicontinuous (fun x => eRealChord (u₀ x) (u₁ x) t) :=
  h.left_endpoint.upperSemicontinuous_eRealChord h.right_endpoint ht0 ht1

/-- Chartwise USC of the endpoint chord attached to a subgeodesic. -/
theorem upperSemicontinuousOn_chart_eRealChord
    (h : IsSubgeodesicFrom θ curve u₀ u₁) (e : ComplexChart n M)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    UpperSemicontinuousOn
      (fun z => eRealChord (chartFunction u₀ e z) (chartFunction u₁ e z) t)
      e.val.target :=
  h.left_endpoint.upperSemicontinuousOn_chart_eRealChord h.right_endpoint e ht0 ht1

end IsSubgeodesicFrom

end FirstPass

end

end SGPT.Foundations.Analysis
