/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Borel
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Measure


/-!
# BorellRepresentation: Basic

Convexity of the positive-density set, concavity of its logarithm and continuity on the interior
support.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Topology Filter

namespace FunctionalInequalities

section Representative

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]

namespace KLS

/-- A Borell density representative of the measure `ν` relative to the reference measure `m`:
a Borel, nonnegative, real-valued, upper semicontinuous, log-concave function whose
`m`-density is `ν`. Log-concavity is the pointwise inequality with real powers, so zeros of `ρ`
are allowed and the set `{ρ > 0}` is convex. This is a definition of the representative;
it does not by itself assert existence, positivity or bounds. -/
structure IsBorellDensity (ν m : Measure V) (ρ : V → ℝ) : Prop where
  measurable : Measurable ρ
  nonneg : ∀ x, 0 ≤ ρ x
  upperSemicontinuous : UpperSemicontinuous ρ
  logConcave : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
    ρ x ^ t * ρ y ^ (1 - t) ≤ ρ (t • x + (1 - t) • y)
  withDensity_eq : m.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) = ν

end KLS

namespace KLS.IsBorellDensity

section DensitySupport

omit [BorelSpace V]
/-- The positivity set of a Borell density representative is convex. -/
theorem convex_pos {ν m : Measure V} {ρ : V → ℝ} (h : IsBorellDensity ν m ρ) :
    Convex ℝ {y | 0 < ρ y} := by
  intro a ha b hb s u hs hu hsu
  have ha' : 0 < ρ a := ha
  have hb' : 0 < ρ b := hb
  rcases hs.eq_or_lt with rfl | hs'
  · have hu1 : u = 1 := by linarith
    subst hu1
    simpa using hb'
  rcases hu.eq_or_lt with rfl | hu'
  · have hs1 : s = 1 := by linarith
    subst hs1
    simpa using ha'
  have hu_eq : u = 1 - s := by linarith
  have hs1 : s < 1 := by linarith
  have key := h.logConcave a b s hs' hs1
  rw [← hu_eq] at key
  change 0 < ρ (s • a + u • b)
  exact lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos ha' s) (Real.rpow_pos_of_pos hb' u)) key

/-- The logarithm of a Borell density representative is concave on the positivity set. -/
theorem concaveOn_log {ν m : Measure V} {ρ : V → ℝ} (h : IsBorellDensity ν m ρ) :
    ConcaveOn ℝ {y | 0 < ρ y} fun y ↦ Real.log (ρ y) := by
  refine ⟨h.convex_pos, ?_⟩
  intro a ha b hb s u hs hu hsu
  have ha' : 0 < ρ a := ha
  have hb' : 0 < ρ b := hb
  rcases hs.eq_or_lt with rfl | hs'
  · have hu1 : u = 1 := by linarith
    subst hu1
    simp
  rcases hu.eq_or_lt with rfl | hu'
  · have hs1 : s = 1 := by linarith
    subst hs1
    simp
  have hu_eq : u = 1 - s := by linarith
  have hs1 : s < 1 := by linarith
  have key := h.logConcave a b s hs' hs1
  rw [← hu_eq] at key
  simp only [smul_eq_mul]
  calc s * Real.log (ρ a) + u * Real.log (ρ b)
      = Real.log (ρ a ^ s * ρ b ^ u) := by
        rw [Real.log_mul (Real.rpow_pos_of_pos ha' s).ne' (Real.rpow_pos_of_pos hb' u).ne',
          Real.log_rpow ha', Real.log_rpow hb']
    _ ≤ Real.log (ρ (s • a + u • b)) :=
        Real.log_le_log (mul_pos (Real.rpow_pos_of_pos ha' s) (Real.rpow_pos_of_pos hb' u)) key

/-- The measure of the complement of the positivity set vanishes. -/
theorem measure_compl_pos {ν m : Measure V} {ρ : V → ℝ}
    (h : IsBorellDensity ν m ρ) : ν {y | 0 < ρ y}ᶜ = 0 := by
  have hmeas : MeasurableSet {y | 0 < ρ y} := measurableSet_lt measurable_const h.measurable
  rw [← h.withDensity_eq, withDensity_apply _ hmeas.compl]
  rw [setLIntegral_congr_fun hmeas.compl (g := fun _ ↦ 0)]
  · simp
  · intro x hx
    have : ¬ 0 < ρ x := hx
    exact ENNReal.ofReal_eq_zero.mpr (not_lt.mp this)

end DensitySupport

end KLS.IsBorellDensity

variable [FiniteDimensional ℝ V]

namespace KLS.IsBorellDensity

/-- The interior of the support of a probability law with a Borell density representative lies
inside the interior of the positivity set of that representative. -/
theorem interior_support_subset {ν : ProbabilityMeasure V} {m : Measure V}
    [m.IsAddHaarMeasure] {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) :
    interior (ν : Measure V).support ⊆ interior {y | 0 < ρ y} := by
  set S : Set V := {y | 0 < ρ y} with hS
  have hSconv : Convex ℝ S := h.convex_pos
  have hmeas : MeasurableSet S := measurableSet_lt measurable_const h.measurable
  have hνSc : (ν : Measure V) Sᶜ = 0 := h.measure_compl_pos
  have hint : (interior S).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hspan : affineSpan ℝ S ≠ ⊤ := by
      intro htop
      have := hSconv.interior_nonempty_iff_affineSpan_eq_top.mpr htop
      rw [hemp] at this
      exact Set.not_nonempty_empty this
    have hmS : m (affineSpan ℝ S : Set V) = 0 := Measure.addHaar_affineSubspace m _ hspan
    have hνS : (ν : Measure V) S = 0 := by
      rw [← h.withDensity_eq, withDensity_apply _ hmeas]
      exact setLIntegral_measure_zero _ _ (measure_mono_null (subset_affineSpan ℝ S) hmS)
    have huniv : (ν : Measure V) Set.univ = 0 := by
      rw [← Set.union_compl_self S]
      exact measure_union_null hνS hνSc
    simp at huniv
  have hsupp : (ν : Measure V).support ⊆ closure S := by
    intro y hy
    by_contra hyc
    have hopen : IsOpen (closure S)ᶜ := isClosed_closure.isOpen_compl
    have hnull : (ν : Measure V) (closure S)ᶜ = 0 :=
      measure_mono_null (Set.compl_subset_compl.mpr subset_closure) hνSc
    exact (Measure.notMem_support_iff_exists.mpr ⟨(closure S)ᶜ, hopen.mem_nhds hyc, hnull⟩) hy
  rw [← hSconv.interior_closure_eq_interior_of_nonempty_interior hint]
  exact interior_mono hsupp

/-- A Borell density representative of a probability law is positive at every interior point of
the topological support. -/
theorem pos_of_mem_interior_support {ν : ProbabilityMeasure V} {m : Measure V}
    [m.IsAddHaarMeasure] {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) {x : V}
    (hx : x ∈ interior (ν : Measure V).support) : 0 < ρ x := by
  have hxS : x ∈ {y | 0 < ρ y} := interior_subset (h.interior_support_subset hx)
  exact hxS

omit [BorelSpace V] in
/-- A Borell density representative is continuous on the interior of its positivity set: the
logarithm is a finite concave function there, hence continuous, and `ρ = exp ∘ log ρ`. -/
theorem continuousOn_interior_pos {ν m : Measure V} {ρ : V → ℝ}
    (h : IsBorellDensity ν m ρ) : ContinuousOn ρ (interior {y | 0 < ρ y}) := by
  have hlog := h.concaveOn_log.continuousOn_interior
  refine (Real.continuous_exp.comp_continuousOn hlog).congr ?_
  intro y hy
  have hyS : y ∈ {y | 0 < ρ y} := interior_subset hy
  have hy' : 0 < ρ y := hyS
  simp [Function.comp, Real.exp_log hy']

/-- A finite-dimensional Borell density is continuous Haar-almost everywhere.
It is continuous inside its convex positivity set, zero locally outside the
closure, and the frontier of that set has Haar measure zero. -/
theorem ae_continuous {ν m : Measure V} [m.IsAddHaarMeasure]
    {ρ : V → ℝ} (h : IsBorellDensity ν m ρ) :
    ∀ᵐ x ∂m, ContinuousAt ρ x := by
  let S : Set V := {x | 0 < ρ x}
  have hfront : m (frontier S) = 0 := h.convex_pos.addHaar_frontier m
  have hgood : ∀ᵐ x ∂m, x ∉ frontier S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hfront
  filter_upwards [hgood] with x hx
  have hx' : x ∈ interior S ∪ interior Sᶜ := by
    exact (compl_frontier_eq_union_interior (s := S)) ▸ hx
  rcases hx' with hxS | hxSc
  · exact h.continuousOn_interior_pos.continuousAt (isOpen_interior.mem_nhds hxS)
  · have hnear : ρ =ᶠ[𝓝 x] (fun _ : V => (0 : ℝ)) := by
      filter_upwards [isOpen_interior.mem_nhds hxSc] with y hy
      have hnot : ¬ 0 < ρ y := interior_subset hy
      exact le_antisymm (le_of_not_gt hnot) (h.nonneg y)
    exact continuousAt_const.congr_of_eventuallyEq hnear

/-- A Borell density representative of a probability law is continuous on the interior of the
support. This is the continuity used by the downstream covariance-core and relative-perimeter
arguments; it is not continuity on all of `V`, where `ρ` is only upper semicontinuous. -/
theorem continuousOn_interior_support {ν : ProbabilityMeasure V} {m : Measure V}
    [m.IsAddHaarMeasure] {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) :
    ContinuousOn ρ (interior (ν : Measure V).support) :=
  h.continuousOn_interior_pos.mono h.interior_support_subset

/-- On every compact subset of the interior of the support, a Borell density representative is
bounded above and bounded below by a positive constant. Upper semicontinuity gives the upper
bound; continuity of the concave logarithm on the open interior gives the lower bound. This is
the pointwise form of `ρ, ρ⁻¹ ∈ L^∞_loc(Ω)`. -/
theorem exists_bounds_of_isCompact {ν : ProbabilityMeasure V} {m : Measure V}
    [m.IsAddHaarMeasure] {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) {K : Set V}
    (hK : IsCompact K) (hKΩ : K ⊆ interior (ν : Measure V).support) :
    ∃ a b : ℝ, 0 < a ∧ ∀ x ∈ K, a ≤ ρ x ∧ ρ x ≤ b := by
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · exact ⟨1, 0, one_pos, by simp [hK0]⟩
  obtain ⟨b, hb⟩ := (h.upperSemicontinuous.upperSemicontinuousOn K).bddAbove_of_isCompact hK
  obtain ⟨x₀, hx₀K, hmin⟩ :=
    hK.exists_isMinOn hKne (h.continuousOn_interior_support.mono hKΩ)
  refine ⟨ρ x₀, b, h.pos_of_mem_interior_support (hKΩ hx₀K), fun x hx ↦ ⟨?_, hb ⟨x, hx, rfl⟩⟩⟩
  exact (isMinOn_iff.mp hmin) x hx

end KLS.IsBorellDensity

end Representative


end FunctionalInequalities
