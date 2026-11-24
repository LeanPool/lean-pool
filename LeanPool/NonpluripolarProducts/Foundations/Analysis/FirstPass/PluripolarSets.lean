/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshRegularDistribution

/-!
# Local pluripolar sets and Haar nullity

Witnesses are actual nontrivial extended-real PSH functions on connected open
neighborhoods. Nullity is a theorem, not a field of the definition. Local null
sets are assembled with the existing countable-open-cover argument; no
uncountable union of null sets and no measurability of the pluripolar set is
assumed. No global PSH witness or Josefson theorem is asserted here.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An actual nontrivial PSH pole-set witness around one point. -/
def LocallyPluripolarAt (s : Set E) (x : E) : Prop :=
  ∃ (V : Set E) (u : E → EReal), IsOpen V ∧ x ∈ V ∧ IsPreconnected V ∧
    PlurisubharmonicOn u V ∧ (∃ a ∈ V, u a ≠ ⊥) ∧
      ∀ y ∈ V, y ∈ s → u y = ⊥

/-- Local pluripolar witnesses at every center in `U`. For the usual domain
notion, `U` is open; the definition itself also makes sense for arbitrary sets. -/
def LocallyPluripolarOn (s U : Set E) : Prop :=
  ∀ x ∈ U, LocallyPluripolarAt s x

theorem LocallyPluripolarAt.mono {s t : Set E} {x : E}
    (hs : LocallyPluripolarAt s x) (hts : t ⊆ s) : LocallyPluripolarAt t x := by
  obtain ⟨V, u, hVo, hxV, hVc, hu, hne, hp⟩ := hs
  exact ⟨V, u, hVo, hxV, hVc, hu, hne, fun y hy hyt => hp y hy (hts hyt)⟩

theorem LocallyPluripolarOn.mono_set {s t U : Set E}
    (hs : LocallyPluripolarOn s U) (hts : t ⊆ s) : LocallyPluripolarOn t U :=
  fun x hx => (hs x hx).mono hts

theorem LocallyPluripolarOn.mono_domain {s U V : Set E}
    (hs : LocallyPluripolarOn s U) (hVU : V ⊆ U) : LocallyPluripolarOn s V :=
  fun x hx => hs x (hVU hx)

/-- The pole set of a nontrivial PSH function has the function itself as a
local witness on its connected open domain. -/
theorem PlurisubharmonicOn.locallyPluripolarOn_poles
    {u : E → EReal} {U : Set E} (hu : PlurisubharmonicOn u U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hne : ∃ a ∈ U, u a ≠ ⊥) :
    LocallyPluripolarOn {y | u y = ⊥} U :=
  fun _ hx => ⟨U, u, hUo, hx, hUc, hu, hne, fun _ _ hy => hy⟩

section Measures

variable [MeasurableSpace E]

/-- A measure-theoretic property phrased with actual local PSH pole sets.
This does not construct a non-pluripolar product. -/
def DoesNotChargePluripolarOn (μ : Measure E) (U : Set E) : Prop :=
  ∀ s : Set E, LocallyPluripolarOn s U → μ (s ∩ U) = 0

variable [BorelSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E]

/-- A single PSH witness yields an open neighborhood on which almost every
point lies outside the witnessed set. -/
theorem LocallyPluripolarAt.exists_open_ae_notMem {s : Set E} {x : E}
    (hs : LocallyPluripolarAt s x) (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ∀ᵐ y ∂μ.restrict V, y ∉ s := by
  obtain ⟨V, u, hVo, hxV, hVc, hu, hne, hp⟩ := hs
  refine ⟨V, hVo, hxV, ?_⟩
  filter_upwards [hu.ae_finite μ hVc hne, ae_restrict_mem hVo.measurableSet]
    with y hyfin hyV
  exact fun hys => hyfin.2 (hp y hyV hys)

/-- Countably many witnessing neighborhoods suffice; no measurability of `s`
or of the set of centers `U` is needed for this restricted AE assertion. -/
theorem LocallyPluripolarOn.ae_notMem {s U : Set E}
    (hs : LocallyPluripolarOn s U) (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ.restrict U, x ∉ s := by
  apply ae_restrict_of_open_neighborhood_ae
  exact fun x hx => (hs x hx).exists_open_ae_notMem μ

/-- Local pluripolar sets have Haar outer measure zero on an open domain.
The set `s` need not be measurable. -/
theorem LocallyPluripolarOn.measure_inter_eq_zero {s U : Set E}
    (hs : LocallyPluripolarOn s U) (hU : IsOpen U)
    (μ : Measure E) [μ.IsAddHaarMeasure] : μ (s ∩ U) = 0 := by
  have h : ∀ᵐ x ∂μ, x ∈ U → x ∉ s :=
    (ae_restrict_iff' hU.measurableSet).mp (hs.ae_notMem μ)
  have h' : ∀ᵐ x ∂μ, x ∉ s ∩ U :=
    h.mono (fun _ hx hxs => hx hxs.2 hxs.1)
  simpa only [not_not, Set.ofPred_mem_eq] using (ae_iff.mp h')

/-- Haar measures do not charge local pluripolar sets. -/
theorem haar_doesNotChargePluripolarOn (μ : Measure E) [μ.IsAddHaarMeasure]
    {U : Set E} (hU : IsOpen U) : DoesNotChargePluripolarOn μ U :=
  fun _ hs => hs.measure_inter_eq_zero hU μ

end Measures

end SGPT.Foundations.Analysis
