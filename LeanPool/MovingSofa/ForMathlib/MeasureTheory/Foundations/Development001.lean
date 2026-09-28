/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.Order.Hom.Set
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Moving sofa: related mathematical developments

* `ForMathlib.MeasureTheory.EuclideanSpace`.
* `ForMathlib.MeasureTheory.FiniteMeasure.Portmanteau`.
* `ForMathlib.MeasureTheory.FiniteMeasure.Restriction`.
* `ForMathlib.MeasureTheory.Angle`.
* `ForMathlib.MeasureTheory.Hausdorff.Arclength`.
* `ForMathlib.MeasureTheory.Hausdorff.Graph`.
* `ForMathlib.MeasureTheory.Hausdorff.PlanarGraph`.
* `ForMathlib.MeasureTheory.Integral.AtomicBounds`.
* `ForMathlib.MeasureTheory.Integral.IntervalExhaustion`.
* `ForMathlib.MeasureTheory.Integral.MovingIntervals`.
* `ForMathlib.MeasureTheory.Integral.Translation`.
* `ForMathlib.MeasureTheory.Measure.Atoms`.
* `ForMathlib.MeasureTheory.Measure.HaarNullSets`.
* `ForMathlib.MeasureTheory.Measure.Map`.
* `ForMathlib.MeasureTheory.Measure.WithDensity`.
* `ForMathlib.MeasureTheory.RegionBetween`.
* `ForMathlib.MeasureTheory.Measure.PlanarTrapezoid`.
* `ForMathlib.MeasureTheory.Measure.PlanarTriangle`.
* `ForMathlib.MeasureTheory.StieltjesDensity`.
* `ForMathlib.MeasureTheory.VectorMeasure.Interval`.
* `ForMathlib.MeasureTheory.VectorMeasure.WithDensity`.
* `ForMathlib.MeasureTheory.Volume`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Euclidean Space
-/

@[expose] public section

open MeasureTheory

namespace EuclideanSpace

theorem volume_preserving_finTwoCoordinates :
    MeasurePreserving (fun p : EuclideanSpace ℝ (Fin 2) ↦ (p 0, p 1)) volume volume := by
  exact (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

/-- The volume of a closed coordinate box of the Euclidean plane. -/
theorem volume_setOf_apply_mem_Icc (l r b t : ℝ) :
    volume {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc l r ∧ p 1 ∈ Set.Icc b t} =
      ENNReal.ofReal (r - l) * ENNReal.ofReal (t - b) := by
  have h := volume_preserving_finTwoCoordinates.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet :
      NullMeasurableSet (Set.Icc l r ×ˢ Set.Icc b t) (volume : Measure (ℝ × ℝ)))
  calc
    volume {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc l r ∧ p 1 ∈ Set.Icc b t} =
        volume (Set.Icc l r ×ˢ Set.Icc b t) := by
      convert h using 1
      congr 1
    _ = _ := by rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]

/-- The coordinates of a point of the Euclidean plane, listed second coordinate first. -/
def finTwoCoordinatesSwap (p : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  (p 1, p 0)

/-- Reading the plane coordinates in the reversed order is measure preserving. -/
theorem volume_preserving_finTwoCoordinatesSwap :
    MeasurePreserving finTwoCoordinatesSwap volume
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hswap : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap
  convert hswap.comp volume_preserving_finTwoCoordinates using 1
  funext p
  rfl

end EuclideanSpace

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Portmanteau for finite measures: the open-set inequality

Mathlib proves the open-set portmanteau inequality
`MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto` for probability measures and
only the closed-set inequality `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto`
for finite measures. This file supplies the missing open-set inequality for finite measures, by
combining the closed-set inequality on the complement with the convergence of the total masses.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace MeasureTheory.FiniteMeasure

/-- Portmanteau for finite measures: weak convergence bounds the mass of an open set by the
lower limit of the approximating masses. -/
theorem le_liminf_measure_open_of_tendsto
    {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ : FiniteMeasure Ω} {μs : ι → FiniteMeasure Ω}
    (hlim : Tendsto μs L (𝓝 μ)) {G : Set Ω} (hG : IsOpen G) :
    (μ : Measure Ω) G ≤ L.liminf (fun i ↦ (μs i : Measure Ω) G) := by
  have hclosed := MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim
    hG.isClosed_compl
  rw [le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)]
  intro y hy
  have hμGtop : (μ : Measure Ω) G ≠ ⊤ := measure_ne_top _ _
  have hyTop : y ≠ ⊤ := ne_top_of_lt (hy.trans_le (le_top))
  have hyR : y.toReal < ((μ : Measure Ω) G).toReal :=
    (ENNReal.toReal_lt_toReal hyTop hμGtop).mpr hy
  let d : ℝ := (((μ : Measure Ω) G).toReal - y.toReal) / 3
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hmass : Tendsto (fun i ↦ ((μs i).mass : ℝ)) L (𝓝 (μ.mass : ℝ)) :=
    (NNReal.continuous_coe.tendsto μ.mass).comp
      (MeasureTheory.FiniteMeasure.continuous_mass.tendsto μ |>.comp hlim)
  have hevmass : ∀ᶠ i in L, (μ.mass : ℝ) - d < ((μs i).mass : ℝ) :=
    hmass.eventually_const_lt (sub_lt_self _ hd)
  let q : ENNReal := ENNReal.ofReal (((μ : Measure Ω) Gᶜ).toReal + d)
  have hqd : 0 ≤ ((μ : Measure Ω) Gᶜ).toReal + d := by
    have hcR : 0 ≤ ((μ : Measure Ω) Gᶜ).toReal := ENNReal.toReal_nonneg
    linarith
  have hcompq : (μ : Measure Ω) Gᶜ < q := by
    rw [← ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal hqd]
    linarith
  have hlsq : L.limsup (fun i ↦ (μs i : Measure Ω) Gᶜ) < q :=
    hclosed.trans_lt hcompq
  have hevcomp : ∀ᶠ i in L, (μs i : Measure Ω) Gᶜ < q :=
    eventually_lt_of_limsup_lt hlsq
  filter_upwards [hevmass, hevcomp] with i him hic
  have hmassEq : ((μs i : Measure Ω) univ).toReal = ((μs i).mass : ℝ) := by
    simp [← MeasureTheory.FiniteMeasure.ennreal_mass]
  have hcompR : ((μs i : Measure Ω) Gᶜ).toReal <
      ((μ : Measure Ω) Gᶜ).toReal + d := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).mpr hic
    simpa [q, ENNReal.toReal_ofReal hqd] using h
  have hsplit : ((μs i : Measure Ω) G).toReal =
      ((μs i).mass : ℝ) - ((μs i : Measure Ω) Gᶜ).toReal := by
    rw [show (μs i : Measure Ω) G = (μs i : Measure Ω) univ -
      (μs i : Measure Ω) Gᶜ by
        rw [measure_compl hG.measurableSet (measure_ne_top _ _),
          ENNReal.sub_sub_cancel (measure_ne_top _ _)
            (measure_mono (subset_univ G))]]
    rw [ENNReal.toReal_sub_of_le (measure_mono (subset_univ _))
      (measure_ne_top _ _), hmassEq]
  have hμsplit : ((μ : Measure Ω) G).toReal =
      (μ.mass : ℝ) - ((μ : Measure Ω) Gᶜ).toReal := by
    rw [show (μ : Measure Ω) G = (μ : Measure Ω) univ -
      (μ : Measure Ω) Gᶜ by
        rw [measure_compl hG.measurableSet (measure_ne_top _ _),
          ENNReal.sub_sub_cancel (measure_ne_top _ _)
            (measure_mono (subset_univ G))]]
    rw [ENNReal.toReal_sub_of_le (measure_mono (subset_univ _))
      (measure_ne_top _ _)]
    simp [← MeasureTheory.FiniteMeasure.ennreal_mass]
  apply (ENNReal.toReal_lt_toReal hyTop (measure_ne_top _ _)).mp
  rw [hsplit]
  dsimp [d] at him hcompR hd
  linarith [hyR, hμsplit]

end MeasureTheory.FiniteMeasure

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Finite Measure / Restriction
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace MeasureTheory.FiniteMeasure

/-- Weak convergence of finite measures and their restrictions implies weak
convergence of the complementary restrictions. -/
theorem tendsto_restrict_compl_of_tendsto_restrict
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hs : MeasurableSet s) (hμ : Tendsto μs F (𝓝 μ))
    (hsμ : Tendsto (fun n ↦ (μs n).restrict s) F (𝓝 (μ.restrict s))) :
    Tendsto (fun n ↦ (μs n).restrict sᶜ) F (𝓝 (μ.restrict sᶜ)) := by
  apply tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hi (ν : FiniteMeasure X) :
      (∫ x, f x ∂(ν.restrict sᶜ : Measure X)) =
        (∫ x, f x ∂(ν : Measure X)) - (∫ x, f x ∂(ν.restrict s : Measure X)) := by
    have h := integral_add_compl hs (f.integrable (μ := (ν : Measure X)))
    change (∫ x in sᶜ, f x ∂(ν : Measure X)) =
      (∫ x, f x ∂(ν : Measure X)) - (∫ x in s, f x ∂(ν : Measure X))
    linarith
  simpa only [hi] using
    ((tendsto_iff_forall_integral_tendsto.mp hμ) f).sub
      ((tendsto_iff_forall_integral_tendsto.mp hsμ) f)

end MeasureTheory.FiniteMeasure

namespace MeasureTheory.FiniteMeasure

/-- A continuity set has convergent masses under weak convergence of finite measures. -/
theorem tendsto_apply_of_null_frontier
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [Nonempty X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hμ : Tendsto μs F (𝓝 μ)) (hs : μ (frontier s) = 0) :
    Tendsto (fun n ↦ μs n s) F (𝓝 (μ s)) := by
  by_cases hzero : μ = 0
  · subst μ
    have hm := hμ.mass
    simp only [zero_mass] at hm
    have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0)) F (𝓝 0)) hm
      (fun _ ↦ zero_le) (fun n ↦ (μs n).apply_le_mass s)
    simpa using hlim
  · have hn := μ.tendsto_normalize_of_tendsto hμ hzero
    have hs' : μ.normalize (frontier s) = 0 := by
      rw [μ.normalize_eq_of_nonzero hzero, hs, mul_zero]
    have hset := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hs'
    simpa only [← self_eq_mass_mul_normalize] using hμ.mass.mul hset

end MeasureTheory.FiniteMeasure

namespace MeasureTheory.Measure

/-- Equal atoms on a finite set give equal restrictions to that set. -/
theorem restrict_finset_eq_of_singleton_eq
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ ν : Measure X} (s : Finset X) (h : ∀ x ∈ s, μ {x} = ν {x}) :
    μ.restrict (s : Set X) = ν.restrict (s : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hd : Disjoint ({a} : Set X) (s : Set X) := by simpa using ha
    have heq := ih (fun x hx ↦ h x (Finset.mem_insert_of_mem hx))
    rw [Finset.coe_insert, ← Set.singleton_union]
    rw [restrict_union hd s.measurableSet, restrict_union hd s.measurableSet]
    rw [restrict_singleton, restrict_singleton, h a (Finset.mem_insert_self _ _), heq]

end MeasureTheory.Measure

namespace MeasureTheory.FiniteMeasure

/-- Removing finitely many fixed atoms preserves weak convergence. -/
theorem tendsto_restrict_compl_finset_of_singleton_eq
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableSingletonClass X] {F : Filter ι}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} (s : Finset X)
    (hμ : Tendsto μs F (𝓝 μ))
    (h : ∀ n x, x ∈ s → (μs n : Measure X) {x} = (μ : Measure X) {x}) :
    Tendsto (fun n ↦ (μs n).restrict (s : Set X)ᶜ) F
      (𝓝 (μ.restrict (s : Set X)ᶜ)) := by
  apply tendsto_restrict_compl_of_tendsto_restrict s.measurableSet hμ
  have heq (n : ι) : (μs n).restrict (s : Set X) = μ.restrict (s : Set X) :=
    Subtype.ext (Measure.restrict_finset_eq_of_singleton_eq s (h n))
  simpa only [heq] using
    (tendsto_const_nhds : Tendsto (fun _ : ι ↦ μ.restrict (s : Set X)) F
      (𝓝 (μ.restrict (s : Set X))))

/-- A finite measure weighted by a bounded continuous nonnegative function. -/
private def withDensityNN {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : FiniteMeasure X) (g : X →ᵇ ℝ≥0) : FiniteMeasure X :=
  ⟨(μ : Measure X).withDensity (fun x ↦ g x),
    isFiniteMeasure_withDensity (g.lintegral_lt_top_of_nnreal μ).ne⟩

/-- Weighting by a fixed bounded continuous nonnegative function preserves weak convergence. -/
private theorem tendsto_withDensityNN
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μs F (𝓝 μ)) (g : X →ᵇ ℝ≥0) :
    Tendsto (fun n ↦ withDensityNN (μs n) g) F (𝓝 (withDensityNN μ g)) := by
  apply tendsto_iff_forall_lintegral_tendsto.mpr
  intro f
  have hprod := (tendsto_iff_forall_lintegral_tendsto.mp hμ) (g * f)
  have h_lintegral (ν : FiniteMeasure X) :
      (∫⁻ x, (f x : ℝ≥0∞) ∂(withDensityNN ν g : Measure X)) =
        ∫⁻ x, ((g * f) x : ℝ≥0∞) ∂(ν : Measure X) := by
    rw [withDensityNN, toMeasure_mk, lintegral_withDensity_eq_lintegral_mul]
    · simp
    · exact (ENNReal.continuous_coe.comp g.continuous).measurable
    · exact (ENNReal.continuous_coe.comp f.continuous).measurable
  simpa only [h_lintegral] using hprod

/-- Weak convergence is preserved by restriction to a measurable continuity set. -/
theorem tendsto_restrict_of_null_frontier
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [Nonempty X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hs : MeasurableSet s) (hμ : Tendsto μs F (𝓝 μ))
    (hfrontier : μ (frontier s) = 0) :
    Tendsto (fun n ↦ (μs n).restrict s) F (𝓝 (μ.restrict s)) := by
  apply tendsto_iff_forall_lintegral_tendsto.mpr
  intro g
  have hweighted := tendsto_withDensityNN hμ g
  have hfrontier' : (withDensityNN μ g) (frontier s) = 0 := by
    apply ENNReal.coe_eq_zero.mp
    rw [ennreal_coeFn_eq_coeFn_toMeasure]
    apply withDensity_absolutelyContinuous (μ : Measure X) (fun x ↦ g x)
    simpa only [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_zero] using
      congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hfrontier
  have hmass := tendsto_apply_of_null_frontier hweighted hfrontier'
  have hmass_ennreal := (ENNReal.continuous_coe.tendsto _).comp hmass
  change Tendsto (fun n ↦ (withDensityNN (μs n) g s : ℝ≥0∞)) F
    (𝓝 (withDensityNN μ g s : ℝ≥0∞)) at hmass_ennreal
  have h_lintegral (ν : FiniteMeasure X) :
      (withDensityNN ν g s : ℝ≥0∞) =
        ∫⁻ x in s, (g x : ℝ≥0∞) ∂(ν : Measure X) := by
    rw [ennreal_coeFn_eq_coeFn_toMeasure, withDensityNN, toMeasure_mk, withDensity_apply _ hs]
  simpa only [h_lintegral, restrict_measure_eq] using hmass_ennreal

/-- Fixed atoms on a finite set containing the frontier allow weak restriction convergence. -/
theorem tendsto_restrict_of_frontier_subset_finset
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [Nonempty X] [MeasurableSingletonClass X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hs : MeasurableSet s) (t : Finset X) (hfrontier : frontier s ⊆ (t : Set X))
    (hμ : Tendsto μs F (𝓝 μ))
    (hatoms : ∀ n x, x ∈ t → (μs n : Measure X) {x} = (μ : Measure X) {x}) :
    Tendsto (fun n ↦ (μs n).restrict s) F (𝓝 (μ.restrict s)) := by
  have hremoved := tendsto_restrict_compl_finset_of_singleton_eq t hμ hatoms
  have hzero : (μ.restrict (t : Set X)ᶜ) (frontier s) = 0 := by
    apply (null_iff_toMeasure_null _ _).mpr
    rw [restrict_measure_eq, Measure.restrict_apply measurableSet_frontier]
    have he : frontier s ∩ (t : Set X)ᶜ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.2 (hfrontier hx.1)
    rw [he, measure_empty]
  have hrestricted := tendsto_restrict_of_null_frontier hs hremoved hzero
  have hfixed (n : ι) : ((μs n).restrict (t : Set X)).restrict s =
      (μ.restrict (t : Set X)).restrict s := by
    congr 1
    exact Subtype.ext (Measure.restrict_finset_eq_of_singleton_eq t (hatoms n))
  have hsplit (ν : FiniteMeasure X) : ν.restrict s =
      (ν.restrict (t : Set X)ᶜ).restrict s + (ν.restrict (t : Set X)).restrict s := by
    apply Subtype.ext
    change (ν : Measure X).restrict s =
      ((ν : Measure X).restrict (t : Set X)ᶜ).restrict s +
        ((ν : Measure X).restrict (t : Set X)).restrict s
    rw [← Measure.restrict_add]
    congr 1
    rw [add_comm, Measure.restrict_add_restrict_compl t.measurableSet]
  have hconst : Tendsto (fun n ↦ ((μs n).restrict (t : Set X)).restrict s) F
      (𝓝 ((μ.restrict (t : Set X)).restrict s)) := by
    simpa only [hfixed] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (μ.restrict (t : Set X)).restrict s) F _)
  simpa only [← hsplit] using hrestricted.add hconst

end MeasureTheory.FiniteMeasure

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Angle
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace Real.Angle

/-- A half-open interval of at most one turn has distinct angular representatives. -/
theorem injOn_coe_Ioc {a b : ℝ} (h : b ≤ a + 2 * Real.pi) :
    Set.InjOn (fun t : ℝ ↦ (t : Angle)) (Ioc a b) := by
  let : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  intro x hx y hy hxy
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc
    ⟨hx.1, hx.2.trans h⟩ ⟨hy.1, hy.2.trans h⟩).mp hxy

/-- Every fibre of the angular projection is countable, being a full residue class. -/
theorem countable_preimage_coe_singleton (x : Angle) :
    ((fun s : ℝ ↦ (s : Angle)) ⁻¹' {x}).Countable := by
  refine Set.Countable.mono ?_
    (Set.countable_range fun k : ℤ ↦ x.toReal + 2 * Real.pi * (k : ℝ))
  intro y hy
  have hy' : ((y : ℝ) : Angle) = ((x.toReal : ℝ) : Angle) := by
    rw [mem_preimage, mem_singleton_iff] at hy
    rw [hy, coe_toReal]
  obtain ⟨k, hk⟩ := angle_eq_iff_two_pi_dvd_sub.mp hy'
  exact ⟨k, by linarith [hk]⟩

/-- The quotient map sends an open real interval to an open angular arc. -/
theorem isOpen_image_Ioo (a b : ℝ) :
    IsOpen ((fun t : ℝ ↦ (t : Angle)) '' Ioo a b) := by
  exact QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

/-- The frontier of an angular arc is contained in its two endpoint angles. -/
theorem frontier_image_Ioo_subset (a b : ℝ) :
    frontier ((fun t : ℝ ↦ (t : Angle)) '' Ioo a b) ⊆
      {(a : Angle), (b : Angle)} := by
  intro x hx
  have hc : IsClosed ((fun t : ℝ ↦ (t : Angle)) '' Icc a b) :=
    (isCompact_Icc.image continuous_coe).isClosed
  have hx' : x ∈ (fun t : ℝ ↦ (t : Angle)) '' Icc a b :=
    closure_minimal (image_mono Ioo_subset_Icc_self) hc hx.1
  obtain ⟨t, ht, rfl⟩ := hx'
  have hout : (t : Angle) ∉ (fun t : ℝ ↦ (t : Angle)) '' Ioo a b := by
    simpa only [(isOpen_image_Ioo a b).interior_eq] using hx.2
  have hends : t = a ∨ t = b := by
    by_contra h
    push Not at h
    exact hout ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm h.1),
      lt_of_le_of_ne ht.2 h.2⟩, rfl⟩
  rcases hends with rfl | rfl <;> simp

/-- A nonempty half-open arc consists of its open arc and its terminal angle. -/
theorem image_Ioc_eq_image_Ioo_union {a b : ℝ} (hab : a < b) :
    (fun t : ℝ ↦ (t : Angle)) '' Ioc a b =
      (fun t : ℝ ↦ (t : Angle)) '' Ioo a b ∪ {(b : Angle)} := by
  rw [← Ioo_union_right hab, image_union, image_singleton]

/-- The frontier of a nonempty half-open angular arc lies in its two endpoint angles. -/
theorem frontier_image_Ioc_subset {a b : ℝ} (hab : a < b) :
    frontier ((fun t : ℝ ↦ (t : Angle)) '' Ioc a b) ⊆
      {(a : Angle), (b : Angle)} := by
  rw [image_Ioc_eq_image_Ioo_union hab]
  refine (frontier_union_subset _ _).trans ?_
  refine union_subset ?_ ?_
  · exact inter_subset_left.trans (frontier_image_Ioo_subset a b)
  · refine inter_subset_right.trans (frontier_subset_closure.trans ?_)
    simp

/-- Half-open real intervals have measurable angular images. -/
theorem measurableSet_image_Ioc [MeasurableSpace Angle] [BorelSpace Angle] (a b : ℝ) :
    MeasurableSet ((fun t : ℝ ↦ (t : Angle)) '' Ioc a b) := by
  by_cases hab : a < b
  · rw [image_Ioc_eq_image_Ioo_union hab]
    exact (isOpen_image_Ioo a b).measurableSet.union (measurableSet_singleton _)
  · simp [Ioc_eq_empty_of_le (le_of_not_gt hab)]

/-- A Borel subset of a real interval of at most one turn has a Borel angular image. -/
theorem measurableSet_image_of_subset_Ioc [MeasurableSpace Angle] [BorelSpace Angle]
    {a b : ℝ} (hab : b ≤ a + 2 * Real.pi) {E : Set ℝ} (hE : MeasurableSet E)
    (hEab : E ⊆ Ioc a b) :
    MeasurableSet ((fun t : ℝ ↦ (t : Angle)) '' E) :=
  hE.image_of_continuousOn_injOn continuous_coe.continuousOn ((injOn_coe_Ioc hab).mono hEab)

/-- The preimage of an open angular arc under the half-turn shift is the shifted arc. -/
theorem preimage_sub_pi_image_Ioo (a b : ℝ) :
    (fun t : Angle ↦ t - ((Real.pi : ℝ) : Angle)) ⁻¹'
        ((fun s : ℝ ↦ (s : Angle)) '' Ioo a b) =
      (fun s : ℝ ↦ (s : Angle)) '' Ioo (a + Real.pi) (b + Real.pi) := by
  ext x
  simp only [mem_preimage, mem_image, mem_Ioo]
  constructor
  · rintro ⟨s, hs, hsx⟩
    refine ⟨s + Real.pi, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    rw [coe_add, hsx]
    abel
  · rintro ⟨r, hr, hrx⟩
    refine ⟨r - Real.pi, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
    rw [coe_sub, hrx]

/-- The terminal atom is disjoint from the open arc, even for a full turn. -/
theorem disjoint_image_Ioo_singleton {a b : ℝ} (h : b ≤ a + 2 * Real.pi) :
    Disjoint ((fun t : ℝ ↦ (t : Angle)) '' Ioo a b) {(b : Angle)} := by
  rw [Set.disjoint_singleton_right]
  rintro ⟨t, ht, heq⟩
  have htb := injOn_coe_Ioc h ⟨ht.1, ht.2.le⟩ ⟨ht.1.trans ht.2, le_rfl⟩ heq
  exact ht.2.ne htb

/-- Passing from an open arc to a half-open arc restores exactly its terminal atom. -/
theorem integral_image_Ioc [MeasurableSpace Angle] [BorelSpace Angle]
    (μ : MeasureTheory.FiniteMeasure Angle) (f : Angle →ᵇ ℝ)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    (∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioc a b, f x ∂(μ : MeasureTheory.Measure Angle)) =
      (∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioo a b, f x ∂(μ : MeasureTheory.Measure Angle)) +
        (μ : MeasureTheory.Measure Angle).real {(b : Angle)} * f (b : Angle) := by
  rw [image_Ioc_eq_image_Ioo_union hab, MeasureTheory.setIntegral_union
    (disjoint_image_Ioo_singleton hturn) (measurableSet_singleton _)
    (f.integrable (μ := (μ : Measure Angle))).integrableOn
    (f.integrable (μ := (μ : Measure Angle))).integrableOn]
  rw [MeasureTheory.integral_singleton]
  rfl

/-- Weak convergence with fixed endpoint atoms preserves integrals on half-open angular arcs. -/
theorem tendsto_integral_image_Ioc_of_fixed_endpoint_atoms
    [MeasurableSpace Angle] [BorelSpace Angle]
    {ι : Type*} {F : Filter ι} {μs : ι → FiniteMeasure Angle} {μ : FiniteMeasure Angle}
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (hμ : Tendsto μs F (𝓝 μ))
    (ha : ∀ n, (μs n : Measure Angle) {(a : Angle)} = (μ : Measure Angle) {(a : Angle)})
    (hb : ∀ n, (μs n : Measure Angle) {(b : Angle)} = (μ : Measure Angle) {(b : Angle)})
    (f : Angle →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioc a b,
      f x ∂(μs n : Measure Angle)) F
      (𝓝 (∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioc a b, f x ∂(μ : Measure Angle))) := by
  classical
  have hatoms : ∀ n x, x ∈ ({(a : Angle), (b : Angle)} : Finset Angle) →
      (μs n : Measure Angle) {x} = (μ : Measure Angle) {x} := by
    intro n x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha n
    · exact hb n
  have hres := FiniteMeasure.tendsto_restrict_of_frontier_subset_finset
    (isOpen_image_Ioo a b).measurableSet ({(a : Angle), (b : Angle)} : Finset Angle)
    (by simpa using frontier_image_Ioo_subset a b) hμ hatoms
  have hint := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hres f
  have hatom (n : ι) : (μs n : Measure Angle).real {(b : Angle)} =
      (μ : Measure Angle).real {(b : Angle)} := by
    exact congrArg ENNReal.toReal (hb n)
  simpa only [integral_image_Ioc _ _ hab hturn, hatom,
    FiniteMeasure.restrict_measure_eq] using
      hint.add (tendsto_const_nhds (x := (μ : Measure Angle).real {(b : Angle)} * f (b : Angle)))

/-! ### Integration over the circle of directions -/

/-- A continuous function of a direction is integrable for every finite angular measure, the
circle of directions being compact. -/
theorem integrable_of_continuous [MeasurableSpace Angle] [BorelSpace Angle] {E : Type*}
    [NormedAddCommGroup E] {μ : Measure Angle} [IsFiniteMeasure μ] {f : Angle → E}
    (hf : Continuous f) : Integrable f μ := by
  have : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  have : CompactSpace Angle := inferInstanceAs (CompactSpace (AddCircle (2 * Real.pi)))
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-! ### Angular measures reading a real density -/

/-- On a real window of at most one turn, the pushforward of a weighted measure along the
angular projection gives the angular image of a measurable subset the integral of the weight
over that subset. -/
theorem map_coe_withDensity_image_eq_setLIntegral [MeasurableSpace Angle] [BorelSpace Angle]
    {ν : Measure ℝ} {w : ℝ → ENNReal} {S T : Set ℝ} {a b : ℝ}
    (hturn : b ≤ a + 2 * Real.pi) (hS : S ⊆ Ioc a b) (hT : MeasurableSet T) (hTS : T ⊆ S) :
    Measure.map (fun t : ℝ ↦ (t : Angle)) ((ν.restrict S).withDensity w)
        ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, w t ∂ν := by
  have hmeas : Measurable fun t : ℝ ↦ (t : Angle) := continuous_coe.measurable
  have himage : MeasurableSet ((fun t : ℝ ↦ (t : Angle)) '' T) :=
    measurableSet_image_of_subset_Ioc hturn hT (hTS.trans hS)
  have hpre : MeasurableSet ((fun t : ℝ ↦ (t : Angle)) ⁻¹'
      ((fun t : ℝ ↦ (t : Angle)) '' T)) := himage.preimage hmeas
  have hback : (fun t : ℝ ↦ (t : Angle)) ⁻¹' ((fun t : ℝ ↦ (t : Angle)) '' T) ∩ S = T := by
    refine Subset.antisymm ?_ fun x hx ↦ ⟨mem_image_of_mem _ hx, hTS hx⟩
    rintro x ⟨⟨y, hy, hxy⟩, hxS⟩
    exact injOn_coe_Ioc hturn (hS (hTS hy)) (hS hxS) hxy ▸ hy
  rw [Measure.map_apply hmeas himage, withDensity_apply _ hpre, Measure.restrict_restrict hpre,
    hback]

/-- Two angular measures that agree on the angular image of every measurable subset of a real
window agree after restriction to that window's angular image. -/
theorem measure_restrict_image_congr [MeasurableSpace Angle] [BorelSpace Angle]
    {μ ν : Measure Angle} {J : Set ℝ} (hJ : MeasurableSet J)
    (h : ∀ T, MeasurableSet T → T ⊆ J →
      μ ((fun t : ℝ ↦ (t : Angle)) '' T) = ν ((fun t : ℝ ↦ (t : Angle)) '' T)) :
    μ.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) =
      ν.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) := by
  have hmeas : Measurable fun t : ℝ ↦ (t : Angle) := continuous_coe.measurable
  ext A hA
  have hpre : MeasurableSet ((fun t : ℝ ↦ (t : Angle)) ⁻¹' A) := hA.preimage hmeas
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA, inter_comm,
    ← image_inter_preimage, h _ (hJ.inter hpre) inter_subset_left]

/-- Two angular measures reading extended-real weights on a real window agree after restriction
to its angular image as soon as the weights agree almost everywhere on the window. -/
theorem measure_restrict_image_congr_of_ae_eq [MeasurableSpace Angle] [BorelSpace Angle]
    {μ ν : Measure Angle} {ρ : Measure ℝ} {w w' : ℝ → ENNReal} {J : Set ℝ}
    (hJ : MeasurableSet J)
    (hμ : ∀ T, MeasurableSet T → T ⊆ J →
      μ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, w t ∂ρ)
    (hν : ∀ T, MeasurableSet T → T ⊆ J →
      ν ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, w' t ∂ρ)
    (hw : ∀ᵐ t ∂ρ.restrict J, w t = w' t) :
    μ.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) =
      ν.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) := by
  refine measure_restrict_image_congr hJ fun T hT hTJ ↦ ?_
  rw [hμ T hT hTJ, hν T hT hTJ]
  exact lintegral_congr_ae (ae_restrict_of_ae_restrict_of_subset hTJ hw)

/-- An angular measure reading a real density on a window agrees, after restriction to the
window's angular image, with a sum of two angular measures whose densities add up to it almost
everywhere. -/
theorem measure_restrict_image_congr_add [MeasurableSpace Angle] [BorelSpace Angle]
    {μ ν₁ ν₂ : Measure Angle} {ρ : Measure ℝ} {f g h : ℝ → ℝ} {J : Set ℝ}
    (hJ : MeasurableSet J)
    (hμ : ∀ T, MeasurableSet T → T ⊆ J →
      μ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, ENNReal.ofReal (h t) ∂ρ)
    (hν₁ : ∀ T, MeasurableSet T → T ⊆ J →
      ν₁ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, ENNReal.ofReal (f t) ∂ρ)
    (hν₂ : ∀ T, MeasurableSet T → T ⊆ J →
      ν₂ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, ENNReal.ofReal (g t) ∂ρ)
    (hf : AEMeasurable f (ρ.restrict J)) (hf0 : ∀ᵐ t ∂ρ.restrict J, 0 ≤ f t)
    (hg0 : ∀ᵐ t ∂ρ.restrict J, 0 ≤ g t) (hfg : ∀ᵐ t ∂ρ.restrict J, h t = f t + g t) :
    μ.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) =
      (ν₁ + ν₂).restrict ((fun t : ℝ ↦ (t : Angle)) '' J) := by
  refine measure_restrict_image_congr hJ fun T hT hTJ ↦ ?_
  have hsplit : ∀ᵐ t ∂ρ.restrict T,
      ENNReal.ofReal (h t) = ENNReal.ofReal (f t) + ENNReal.ofReal (g t) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hTJ hf0,
      ae_restrict_of_ae_restrict_of_subset hTJ hg0,
      ae_restrict_of_ae_restrict_of_subset hTJ hfg] with t h1 h2 h3
    rw [h3, ENNReal.ofReal_add h1 h2]
  have hfT : AEMeasurable (fun t ↦ ENNReal.ofReal (f t)) (ρ.restrict T) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (hf.mono_measure (Measure.restrict_mono hTJ le_rfl))
  rw [hμ T hT hTJ, Measure.add_apply, hν₁ T hT hTJ, hν₂ T hT hTJ, lintegral_congr_ae hsplit,
    lintegral_add_left' hfT]

end Real.Angle

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Hausdorff / Arclength
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

open MeasureTheory

namespace MeasureTheory

private theorem dist_le_hausdorffMeasure_image_Icc_of_continuousOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b) (hγ : ContinuousOn γ (Set.Icc a
      b)) :
    ENNReal.ofReal (dist (γ a) (γ b)) ≤
      Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) := by
  by_cases heq : γ a = γ b
  · simp [heq]
  let n : (EuclideanSpace ℝ (Fin 2)) := ‖γ b - γ a‖⁻¹ • (γ b - γ a)
  let f : (EuclideanSpace ℝ (Fin 2)) → ℝ := fun p ↦ inner ℝ (p - γ a) n
  have hnorm : ‖n‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm heq)))]
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    change |inner ℝ (p - γ a) n - inner ℝ (q - γ a) n| ≤ dist p q
    rw [← inner_sub_left]
    have h := abs_real_inner_le_norm ((p - γ a) - (q - γ a)) n
    rw [hnorm, mul_one, show (p - γ a) - (q - γ a) = p - q by module,
      ← dist_eq_norm] at h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hfa : f (γ a) = 0 := by simp [f]
  have hfb : f (γ b) = dist (γ a) (γ b) := by
    dsimp only [f, n]
    rw [inner_smul_right, real_inner_self_eq_norm_sq, dist_eq_norm, inv_mul_eq_div,
      norm_sub_rev]
    field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm heq))]
  have hinterval : Set.Icc 0 (dist (γ a) (γ b)) ⊆ f '' (γ '' Set.Icc a b) := by
    rw [← hfa, ← hfb]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hab (hf.continuous.comp_continuousOn hγ) hy
    exact ⟨γ x, ⟨x, hx, rfl⟩, hxy⟩
  calc
    ENNReal.ofReal (dist (γ a) (γ b)) =
        Measure.hausdorffMeasure 1 (Set.Icc 0 (dist (γ a) (γ b))) := by
      rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
      simp
    _ ≤ Measure.hausdorffMeasure 1 (f '' (γ '' Set.Icc a b)) := measure_mono hinterval
    _ ≤ ((1 : NNReal) : ENNReal) ^ (1 : ℝ) *
        Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) :=
      hf.hausdorffMeasure_image_le (by norm_num) _
    _ = Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) := by simp

private theorem hausdorffMeasure_image_Icc_add_of_injectiveOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
      Measure.hausdorffMeasure 1 (γ '' Set.Icc a c) +
        Measure.hausdorffMeasure 1 (γ '' Set.Icc c b) := by
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := Measure.hausdorffMeasure 1
  have hleft : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hcb
  have hright : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc_left hac
  have hinter : γ '' Set.Icc a c ∩ γ '' Set.Icc c b ⊆ {γ c} := by
    rintro p ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have hxeq : x = y := hinj (hleft hx) (hright hy) hxy.symm
    have : x = c := le_antisymm hx.2 (hxeq ▸ hy.1)
    simp [this]
  have hnull : μ (γ '' Set.Icc a c ∩ γ '' Set.Icc c b) = 0 := by
    let _ := Measure.nullSingletonClass_hausdorff (EuclideanSpace ℝ (Fin 2))
      (by norm_num : (0 : ℝ) < 1)
    exact measure_mono_null hinter (measure_singleton (γ c))
  have hmeas : MeasurableSet (γ '' Set.Icc c b) :=
    (isCompact_Icc.image_of_continuousOn (hγ.mono hright)).measurableSet
  have hunion : γ '' Set.Icc a b = γ '' Set.Icc a c ∪ γ '' Set.Icc c b := by
    rw [← Set.image_union, Set.Icc_union_Icc_eq_Icc hac hcb]
  rw [hunion]
  exact measure_union₀ hmeas.nullMeasurableSet hnull

private theorem hausdorff_partition_sum_le (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) (u : ℕ → ℝ) (n : ℕ)
    (hu : Monotone u) (hγ : ContinuousOn γ (Set.Icc (u 0) (u n)))
    (hinj : Set.InjOn γ (Set.Icc (u 0) (u n))) :
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
      Measure.hausdorffMeasure 1 (γ '' Set.Icc (u 0) (u n)) := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      let v : ℕ → ℝ := fun i ↦ u (i + 1)
      have huv : u 0 ≤ u 1 := hu (Nat.zero_le 1)
      have hvn : u 1 ≤ u (n + 1) := hu (Nat.succ_le_succ (Nat.zero_le n))
      have hwhole : u 0 ≤ u (n + 1) := huv.trans hvn
      have hleft : Set.Icc (u 0) (u 1) ⊆ Set.Icc (u 0) (u (n + 1)) :=
        Set.Icc_subset_Icc_right hvn
      have hright : Set.Icc (u 1) (u (n + 1)) ⊆ Set.Icc (u 0) (u (n + 1)) :=
        Set.Icc_subset_Icc_left huv
      rw [Finset.sum_range_succ']
      have htail : (∑ i ∈ Finset.range n,
          edist (γ (u (i + 1 + 1))) (γ (u (i + 1)))) ≤
          Measure.hausdorffMeasure 1 (γ '' Set.Icc (u 1) (u (n + 1))) := by
        simpa [v, Nat.add_assoc] using ih v (fun _ _ hij ↦ hu (Nat.add_le_add_right hij 1))
          (hγ.mono hright) (hinj.mono hright)
      have hfirst := dist_le_hausdorffMeasure_image_Icc_of_continuousOn γ huv
        (hγ.mono hleft)
      rw [edist_dist]
      rw [hausdorffMeasure_image_Icc_add_of_injectiveOn γ huv hvn hγ hinj]
      simpa [add_comm, dist_comm] using add_le_add htail hfirst

private theorem eVariationOn_le_hausdorffMeasure_image_Icc_of_injectiveOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hγ : ContinuousOn γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤
      Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) := by
  rw [eVariationOn]
  refine iSup_le fun p ↦ ?_
  rcases p with ⟨n, u, hu, hus⟩
  have hu0 := hus 0
  have hun := hus n
  have hsub : Set.Icc (u 0) (u n) ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc hu0.1 hun.2
  calc
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
        Measure.hausdorffMeasure 1 (γ '' Set.Icc (u 0) (u n)) :=
      hausdorff_partition_sum_le γ u n hu (hγ.mono hsub) (hinj.mono hsub)
    _ ≤ Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) :=
      measure_mono (Set.image_mono hsub)

private theorem hausdorffMeasure_image_Icc_le_eVariationOn_of_injectiveOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b)
    (hinj : Set.InjOn γ (Set.Icc a b))
    (hBV : BoundedVariationOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) ≤
      eVariationOn γ (Set.Icc a b) := by
  let ℓ : ℝ → ℝ := variationOnFromTo γ (Set.Icc a b) a
  have hℓstrict : StrictMonoOn ℓ (Set.Icc a b) := by
    intro x hx y hy hxy
    have hnonneg : 0 ≤ variationOnFromTo γ (Set.Icc a b) x y :=
      variationOnFromTo.nonneg_of_le γ _ hxy.le
    have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) hx hy
    have hle : ℓ x ≤ ℓ y := by dsimp only [ℓ]; linarith
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hzero : variationOnFromTo γ (Set.Icc a b) x y = 0 := by
      dsimp only [ℓ] at heq
      linarith
    have hed := variationOnFromTo.edist_zero_of_eq_zero hBV.locallyBoundedVariationOn
      hx hy hzero
    have hxy' : γ x = γ y := edist_eq_zero.mp hed
    exact hxy.ne (hinj hx hy hxy')
  let iso := hℓstrict.orderIso ℓ (Set.Icc a b)
  let Γ : (ℓ '' Set.Icc a b) → (EuclideanSpace ℝ (Fin 2)) := fun z ↦ γ (iso.symm z)
  have hΓle : ∀ z w : (ℓ '' Set.Icc a b), z ≤ w →
      dist (Γ z) (Γ w) ≤ dist z w := by
    intro z w hzw
    have hxy : (iso.symm z : ℝ) ≤ iso.symm w := iso.symm.monotone hzw
    have hvar : dist (γ (iso.symm z)) (γ (iso.symm w)) ≤
        variationOnFromTo γ (Set.Icc a b) (iso.symm z) (iso.symm w) := by
      rw [variationOnFromTo.eq_of_le _ _ hxy, dist_edist]
      apply ENNReal.toReal_mono
        (hBV.locallyBoundedVariationOn _ _ (iso.symm z).property (iso.symm w).property)
      exact eVariationOn.edist_le γ
        ⟨(iso.symm z).property, le_rfl, hxy⟩
        ⟨(iso.symm w).property, hxy, le_rfl⟩
    have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) (iso.symm z).property (iso.symm w).property
    change dist (γ (iso.symm z)) (γ (iso.symm w)) ≤ dist (z : ℝ) (w : ℝ)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (show (z : ℝ) ≤ (w : ℝ) from hzw))]
    have hz : ℓ (iso.symm z) = z := congrArg Subtype.val (iso.apply_symm_apply z)
    have hw : ℓ (iso.symm w) = w := congrArg Subtype.val (iso.apply_symm_apply w)
    dsimp only [ℓ] at hz hw
    linarith
  have hΓ : LipschitzWith 1 Γ := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [NNReal.coe_one, one_mul]
    rcases le_total z w with hzw | hwz
    · exact hΓle z w hzw
    · simpa only [dist_comm] using hΓle w z hwz
  have himage : Γ '' Set.univ = γ '' Set.Icc a b := by
    ext p
    constructor
    · rintro ⟨z, _, rfl⟩
      exact ⟨iso.symm z, (iso.symm z).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨iso ⟨x, hx⟩, Set.mem_univ _, ?_⟩
      simp [Γ]
  have hval : (Subtype.val : (ℓ '' Set.Icc a b) → ℝ) '' Set.univ =
      ℓ '' Set.Icc a b := by
    ext x
    constructor
    · rintro ⟨z, _, rfl⟩; exact z.property
    · intro hx; exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  have hdom : Measure.hausdorffMeasure 1 (Set.univ : Set (ℓ '' Set.Icc a b)) =
      Measure.hausdorffMeasure 1 (ℓ '' Set.Icc a b) := by
    conv_rhs => rw [← hval]
    have hi : Isometry (Subtype.val : (ℓ '' Set.Icc a b) → ℝ) := fun _ _ ↦ rfl
    exact (hi.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1)) _).symm
  have hsub : ℓ '' Set.Icc a b ⊆
      Set.Icc 0 (eVariationOn γ (Set.Icc a b)).toReal := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨variationOnFromTo.nonneg_of_le γ _ hx.1,
      (le_abs_self _).trans (variationOnFromTo.abs_le_eVariationOn hBV)⟩
  calc
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
        Measure.hausdorffMeasure 1 (Γ '' Set.univ) := congrArg _ himage.symm
    _ ≤ Measure.hausdorffMeasure 1 (Set.univ : Set (ℓ '' Set.Icc a b)) := by
      simpa using hΓ.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) Set.univ
    _ = Measure.hausdorffMeasure 1 (ℓ '' Set.Icc a b) := hdom
    _ ≤ Measure.hausdorffMeasure 1
        (Set.Icc 0 (eVariationOn γ (Set.Icc a b)).toReal) := measure_mono hsub
    _ = eVariationOn γ (Set.Icc a b) := by
      rw [hausdorffMeasure_real, Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal hBV]

/-- Hausdorff length of a continuous injective arc is its total variation. -/
theorem hausdorffMeasure_image_Icc_eq_eVariationOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b))
    (hBV : BoundedVariationOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
      eVariationOn γ (Set.Icc a b) :=
  le_antisymm (hausdorffMeasure_image_Icc_le_eVariationOn_of_injectiveOn γ hab hinj hBV)
    (eVariationOn_le_hausdorffMeasure_image_Icc_of_injectiveOn γ hγ hinj)

private theorem eVariationOn_Icc_le_of_lipschitzOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ}
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤ C * ENNReal.ofReal (b - a) := by
  simpa using hγ.comp_eVariationOn_le (g := id) (s := Set.Icc a b) (fun _ hx ↦ hx)

/-- Accumulated variation preserves a curve's Lipschitz bound. -/
private theorem lipschitzOnWith_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    LipschitzOnWith C (variationOnFromTo γ (Set.Icc a b) a) (Set.Icc a b) := by
  let ℓ := variationOnFromTo γ (Set.Icc a b) a
  have hBV : BoundedVariationOn γ (Set.Icc a b) :=
    ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)
  have hbound : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      dist (ℓ x) (ℓ y) ≤ C * dist x y := by
    intro x hx y hy hxy
    have hsub : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 hy.2
    have hvar := eVariationOn_Icc_le_of_lipschitzOn (hγ.mono hsub)
    have hreal := ENNReal.toReal_mono (by finiteness) hvar
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)] at hreal
    have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) hx hy
    have hm := variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) hx hy hxy
    rw [variationOnFromTo.eq_of_le _ _ hxy, Set.inter_eq_right.mpr hsub] at hadd
    change dist (variationOnFromTo γ (Set.Icc a b) a x)
      (variationOnFromTo γ (Set.Icc a b) a y) ≤ _
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hm), Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact hbound x hx y hy hxy
  · simpa only [dist_comm] using hbound y hy x hx hyx

/-- Total variation of a Lipschitz curve is the integral of its accumulated variation derivative. -/
private theorem integral_deriv_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    (∫ x in a..b, deriv (variationOnFromTo γ (Set.Icc a b) a) x) =
      (eVariationOn γ (Set.Icc a b)).toReal := by
  have hL := lipschitzOnWith_variationOnFromTo hab hγ
  have hAC := (show LipschitzOnWith C (variationOnFromTo γ (Set.Icc a b) a)
    (Set.uIcc a b) by simpa only [Set.uIcc_of_le hab] using hL).absolutelyContinuousOnInterval
  rw [hAC.integral_deriv_eq_sub, variationOnFromTo.self,
    variationOnFromTo.eq_of_le _ _ hab, Set.inter_self, sub_zero]

private theorem norm_deriv_le_abs_deriv_of_eventually_dist_le
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {ℓ : ℝ → ℝ} {x : ℝ}
    (hγ : DifferentiableAt ℝ γ x) (hℓ : DifferentiableAt ℝ ℓ x)
    (hbound : ∀ᶠ y in nhds x, dist (γ y) (γ x) ≤ dist (ℓ y) (ℓ x)) :
    ‖deriv γ x‖ ≤ |deriv ℓ x| := by
  have hγlim := hγ.hasDerivAt.tendsto_slope.norm
  have hℓlim := hℓ.hasDerivAt.tendsto_slope.norm
  change Filter.Tendsto _ _ (nhds |deriv ℓ x|) at hℓlim
  apply le_of_tendsto_of_tendsto hγlim hℓlim
  filter_upwards [hbound.filter_mono nhdsWithin_le_nhds] with y hy
  simp only [slope, norm_smul]
  rw [dist_eq_norm, dist_eq_norm] at hy
  exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)

private theorem dist_le_dist_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {a b x y : ℝ} (hab : a ≤ b)
    (hBV : BoundedVariationOn γ (Set.Icc a b))
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    dist (γ x) (γ y) ≤
      dist (variationOnFromTo γ (Set.Icc a b) a x)
        (variationOnFromTo γ (Set.Icc a b) a y) := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [dist_comm] using this hy hx (le_of_not_ge hxy)
  have hvar : dist (γ x) (γ y) ≤ variationOnFromTo γ (Set.Icc a b) x y := by
    rw [variationOnFromTo.eq_of_le _ _ hxy, dist_edist]
    apply ENNReal.toReal_mono (hBV.locallyBoundedVariationOn _ _ hx hy)
    exact eVariationOn.edist_le γ ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
  have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
    (Set.left_mem_Icc.mpr hab) hx hy
  have hm := variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn
    (Set.left_mem_Icc.mpr hab) hx hy hxy
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hm)]
  linarith

/-- The derivative norm of a curve is bounded by the derivative of accumulated variation. -/
private theorem norm_deriv_le_deriv_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {a b x : ℝ}
    (hBV : BoundedVariationOn γ (Set.Icc a b)) (hx : x ∈ Set.Ioo a b)
    (hγ : DifferentiableAt ℝ γ x)
    (hℓ : DifferentiableAt ℝ (variationOnFromTo γ (Set.Icc a b) a) x) :
    ‖deriv γ x‖ ≤ deriv (variationOnFromTo γ (Set.Icc a b) a) x := by
  have hab := hx.1.le.trans hx.2.le
  have hnhds := Icc_mem_nhds hx.1 hx.2
  have hbound : ∀ᶠ y in nhds x, dist (γ y) (γ x) ≤
      dist (variationOnFromTo γ (Set.Icc a b) a y)
        (variationOnFromTo γ (Set.Icc a b) a x) := by
    filter_upwards [hnhds] with y hy
    exact dist_le_dist_variationOnFromTo hab hBV hy ⟨hx.1.le, hx.2.le⟩
  have h := norm_deriv_le_abs_deriv_of_eventually_dist_le hγ hℓ hbound
  have hm := variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn
    (Set.left_mem_Icc.mpr hab)
  have hnonneg := hm.derivWithin_nonneg (x := x)
  rw [derivWithin_of_mem_nhds hnhds] at hnonneg
  rwa [abs_of_nonneg hnonneg] at h

/-- The derivative of a planar Lipschitz curve is integrable on its interval. -/
theorem integrableOn_deriv_of_lipschitzOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ}
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    IntegrableOn (deriv γ) (Set.Icc a b) := by
  rw [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
  apply (integrable_const (C : ℝ)).mono' (aestronglyMeasurable_deriv γ _)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hx.1 hx.2) hγ

/-- The integral of speed is bounded by the total variation of a Lipschitz curve. -/
private theorem integral_norm_deriv_le_eVariationOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    (∫ x in a..b, ‖deriv γ x‖) ≤ (eVariationOn γ (Set.Icc a b)).toReal := by
  let ℓ := variationOnFromTo γ (Set.Icc a b) a
  have hL := lipschitzOnWith_variationOnFromTo hab hγ
  have hAC := (show LipschitzOnWith C ℓ (Set.uIcc a b) by
    simpa only [Set.uIcc_of_le hab] using hL).absolutelyContinuousOnInterval
  have hBV : BoundedVariationOn γ (Set.Icc a b) :=
    ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)
  rw [← integral_deriv_variationOnFromTo hab hγ]
  apply intervalIntegral.integral_mono_ae_restrict hab
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_of_lipschitzOn hγ).norm) hAC.intervalIntegrable_deriv
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hγ.ae_differentiableWithinAt_of_mem,
    hL.ae_differentiableWithinAt_of_mem,
    show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff, measure_singleton],
    show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff, measure_singleton]] with x hxγ hxL hxa hxb hx
  have hx' : x ∈ Set.Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have hxcc : x ∈ Set.Icc a b := ⟨hx'.1.le, hx'.2.le⟩
  exact norm_deriv_le_deriv_variationOnFromTo hBV hx'
    ((hxγ hxcc).differentiableAt (Icc_mem_nhds hx'.1 hx'.2))
    ((hxL hxcc).differentiableAt (Icc_mem_nhds hx'.1 hx'.2))

/-- Fundamental theorem of calculus for a planar Lipschitz curve. -/
private theorem integral_deriv_eq_sub_of_lipschitzOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    (∫ x in a..b, deriv γ x) = γ b - γ a := by
  have hint : IntervalIntegrable (deriv γ) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_of_lipschitzOn hγ)
  ext i
  let L : (EuclideanSpace ℝ (Fin 2)) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) i
  have hcoord := L.lipschitzWith.comp_lipschitzOnWith hγ
  have hAC := (show LipschitzOnWith _ (fun x ↦ L (γ x)) (Set.uIcc a b) by
    simpa only [Set.uIcc_of_le hab, LipschitzOnWith, Function.comp_apply] using
      hcoord).absolutelyContinuousOnInterval
  change L (∫ x in a..b, deriv γ x) = L (γ b - γ a)
  rw [← L.intervalIntegral_comp_comm hint, map_sub, ← hAC.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hγ.ae_differentiableWithinAt_of_mem,
    show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff, measure_singleton]] with x hx hxb hxI
  have hx' : x ∈ Set.Ioo a b := by
    rw [Set.uIoc_of_le hab] at hxI
    exact ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩
  have hd := (hx ⟨hx'.1.le, hx'.2.le⟩).differentiableAt (Icc_mem_nhds hx'.1 hx'.2)
  exact ((L.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt).deriv).symm

private theorem edist_le_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    edist (γ b) (γ a) ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  rw [edist_dist, dist_eq_norm, ← integral_deriv_eq_sub_of_lipschitzOn hab hγ]
  exact ENNReal.ofReal_le_ofReal (intervalIntegral.norm_integral_le_integral_norm hab)

/-- Total variation is bounded by the integral of speed for a Lipschitz curve. -/
private theorem eVariationOn_le_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  have hint : IntervalIntegrable (fun x ↦ ‖deriv γ x‖) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_of_lipschitzOn hγ).norm
  rw [eVariationOn]
  refine iSup_le fun p ↦ ?_
  rcases p with ⟨n, u, hu, hus⟩
  have hsub (i : ℕ) : Set.Icc (u i) (u (i + 1)) ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc (hus i).1 (hus (i + 1)).2
  have hints (i : ℕ) : IntervalIntegrable (fun x ↦ ‖deriv γ x‖) volume (u i) (u (i + 1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hu (Nat.le_succ i))).mpr
      (IntegrableOn.mono_set (integrableOn_deriv_of_lipschitzOn hγ).norm (hsub i))
  calc
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
        ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ x in u i..u (i + 1), ‖deriv γ x‖) :=
      Finset.sum_le_sum fun i _ ↦
        edist_le_ofReal_integral_norm_deriv (hu (Nat.le_succ i)) (hγ.mono (hsub i))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ x in u i..u (i + 1), ‖deriv γ x‖) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg fun i _ ↦
        intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) (fun _ _ ↦ norm_nonneg _)
    _ = ENNReal.ofReal (∫ x in u 0..u n, ‖deriv γ x‖) := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun i _ ↦ hints i)]
    _ ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
      apply ENNReal.ofReal_le_ofReal
      exact intervalIntegral.integral_mono_interval (hus 0).1 (hu (Nat.zero_le n)) (hus n).2
        (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) hint

/-- Total variation of a planar Lipschitz curve is the integral of its speed. -/
theorem eVariationOn_eq_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) = ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  apply le_antisymm (eVariationOn_le_ofReal_integral_norm_deriv hab hγ)
  have hBV : eVariationOn γ (Set.Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)
  rw [ENNReal.ofReal_le_iff_le_toReal hBV]
  exact integral_norm_deriv_le_eVariationOn hab hγ

/-- Hausdorff length of a planar injective Lipschitz curve is the integral of its speed. -/
theorem hausdorffMeasure_image_Icc_eq_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) (hinj : Set.InjOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
      ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  rw [hausdorffMeasure_image_Icc_eq_eVariationOn γ hab hγ.continuousOn hinj
    (ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)),
    eVariationOn_eq_ofReal_integral_norm_deriv hab hγ]

/-- The image of a continuous injective planar arc of bounded variation is Lebesgue null. -/
theorem volume_image_Icc_eq_zero_of_boundedVariationOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b)) (hinj : Set.InjOn γ (Set.Icc a b))
    (hBV : BoundedVariationOn γ (Set.Icc a b)) :
    volume (γ '' Set.Icc a b) = 0 := by
  have hlength : Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) ≠ ⊤ := by
    rw [hausdorffMeasure_image_Icc_eq_eVariationOn γ hab hγ hinj hBV]
    exact hBV
  have harea : Measure.hausdorffMeasure 2 (γ '' Set.Icc a b) = 0 :=
    (Measure.hausdorffMeasure_zero_or_top (by norm_num : (1 : ℝ) < 2) _).resolve_right hlength
  have habs := MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure
    (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (Measure.hausdorffMeasure (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))))
  apply habs
  simpa [finrank_euclideanSpace_fin] using harea

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Hausdorff / Graph
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace MeasureTheory

private theorem map_firstCoordinate_restrict_curve_Icc
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) (a b c d : ℝ)
    (hcoord : ∀ x ∈ Set.Icc a b, γ x 0 = x) :
    Measure.map (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0)
      ((Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) (Set.Icc c d) =
      Measure.hausdorffMeasure 1 (γ '' Set.Icc (max a c) (min b d)) := by
  have hm : Measurable (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.measurable
  rw [Measure.map_apply hm measurableSet_Icc,
    Measure.restrict_apply (hm measurableSet_Icc)]
  congr 1
  ext p
  constructor
  · rintro ⟨hp, x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    change γ x 0 ∈ Set.Icc c d at hp
    rw [hcoord x hx] at hp
    exact ⟨max_le hx.1 hp.1, le_min hx.2 hp.2⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, x, ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩, rfl⟩
    change γ x 0 ∈ Set.Icc c d
    rw [hcoord x ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩]
    exact ⟨(le_max_right _ _).trans hx.1, hx.2.trans (min_le_right _ _)⟩

/-- Projected Hausdorff measure on a Lipschitz graph has speed as its density. -/
theorem map_firstCoordinate_restrict_curve_eq_withDensity
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) (hcoord : ∀ x ∈ Set.Icc a b, γ x 0 = x) :
    Measure.map (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0)
      ((Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) =
      (volume.restrict (Set.Icc a b)).withDensity (fun x ↦ ENNReal.ofReal ‖deriv γ x‖) := by
  have hinj : Set.InjOn γ (Set.Icc a b) := by
    intro x hx y hy hxy
    simpa only [hcoord x hx, hcoord y hy] using congrArg (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p
      0) hxy
  have hfinite : Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) ≠ ⊤ := by
    rw [hausdorffMeasure_image_Icc_eq_ofReal_integral_norm_deriv hab hγ hinj]
    exact ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure ((Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) :=
    (isFiniteMeasure_restrict).mpr hfinite
  apply Measure.ext_of_Icc
  intro c d _
  rw [map_firstCoordinate_restrict_curve_Icc γ a b c d hcoord,
    withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc]
  have hinter : Set.Icc c d ∩ Set.Icc a b = Set.Icc (max a c) (min b d) := by
    rw [Set.Icc_inter_Icc]
    simp only [max_comm, min_comm]
  rw [hinter]
  by_cases hcd : max a c ≤ min b d
  · have hsub : Set.Icc (max a c) (min b d) ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    rw [hausdorffMeasure_image_Icc_eq_ofReal_integral_norm_deriv hcd
      (hγ.mono hsub) (hinj.mono hsub)]
    rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal
      (IntegrableOn.mono_set (integrableOn_deriv_of_lipschitzOn hγ).norm hsub)
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
  · rw [Set.Icc_eq_empty_of_lt (lt_of_not_ge hcd)]
    simp

/-- Weighted arclength formula for a planar Lipschitz graph on a compact interval. -/
theorem integral_restrict_curve_eq_integral_norm_deriv_mul
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) (hcoord : ∀ x ∈ Set.Icc a b, γ x 0 = x)
    {φ : (EuclideanSpace ℝ (Fin 2)) → ℝ} (hφ : Measurable φ) :
    (∫ p, φ p ∂(Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) =
      ∫ x in a..b, ‖deriv γ x‖ * φ (γ x) := by
  let γc : ℝ → (EuclideanSpace ℝ (Fin 2)) := fun x ↦ γ (max a (min x b))
  have hc : Continuous γc := hγ.continuousOn.comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
    (fun x ↦ ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩)
  have hceq (x : ℝ) (hx : x ∈ Set.Icc a b) : γc x = γ x := by
    simp only [γc, min_eq_left hx.2, max_eq_right hx.1]
  have hm : Measurable (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.measurable
  have hset : MeasurableSet (γ '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hγ.continuousOn).measurableSet
  have heq : (fun p ↦ φ (γc (p 0))) =ᵐ[
      (Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)] φ := by
    filter_upwards [ae_restrict_mem hset] with p hp
    obtain ⟨x, hx, rfl⟩ := hp
    rw [hcoord x hx, hceq x hx]
  rw [← integral_congr_ae heq,
    ← integral_map (μ := (Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b))
      (f := fun x : ℝ ↦ φ (γc x)) hm.aemeasurable
      (hφ.comp hc.measurable).aestronglyMeasurable,
    map_firstCoordinate_restrict_curve_eq_withDensity hab hγ hcoord,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_deriv γ |>.norm |>.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [hceq x hx]

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Hausdorff / Planar Graph
-/

@[expose] public section

noncomputable section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

private theorem lipschitzOnWith_planarGraph {g : ℝ → ℝ} {s : Set ℝ} {C : NNReal}
    (hg : LipschitzOnWith C g s) :
    LipschitzOnWith (C + 1) (fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) s := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hgxy := hg.dist_le_mul x hx y hy
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp only [PiLp.sub_apply, Fin.sum_univ_two, Real.norm_eq_abs, pow_two]
  have hxy : dist x y = |x - y| := Real.dist_eq x y
  have hgy : |g x - g y| ≤ (C : ℝ) * |x - y| := by
    simpa [Real.dist_eq] using hgxy
  have hnonneg : 0 ≤ ((C : ℝ) + 1) * |x - y| := mul_nonneg (by positivity) (abs_nonneg _)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, NNReal.coe_add, NNReal.coe_one,
    Real.dist_eq]
  rw [Real.sqrt_le_iff]
  constructor
  · exact hnonneg
  · have hsq := mul_self_le_mul_self (abs_nonneg (g x - g y)) hgy
    nlinarith [sq_nonneg ((C : ℝ) * |x - y|), NNReal.coe_nonneg C]

private theorem hausdorffMeasure_planarGraph_eq_zero {g : ℝ → ℝ} {s t : Set ℝ}
    {C : NNReal} (hg : LipschitzOnWith C g s) (hts : t ⊆ s) (ht : volume t = 0) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' t) = 0 := by
  have hgraph := (lipschitzOnWith_planarGraph hg).mono hts
  apply le_zero_iff.mp
  calc
    Measure.hausdorffMeasure 1
        ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' t) ≤
        ((C + 1 : NNReal) : ENNReal) ^ (1 : ℝ) * Measure.hausdorffMeasure 1 t :=
      hgraph.hausdorffMeasure_image_le (by positivity)
    _ = 0 := by rw [MeasureTheory.hausdorffMeasure_real, ht, mul_zero]

private theorem hausdorffMeasure_planarGraph_nondifferentiableOn_Icc_eq_zero
    {g : ℝ → ℝ} {a b : ℝ} {C : NNReal}
    (hg : LipschitzOnWith C g (Set.Icc a b)) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) ''
        {x | x ∈ Set.Icc a b ∧ ¬ DifferentiableAt ℝ g x}) = 0 := by
  apply hausdorffMeasure_planarGraph_eq_zero hg (by
    intro x hx
    exact hx.1)
  rcases le_total a b with hab | hba
  · rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
    have hg' : LipschitzOnWith C g (Set.uIcc a b) := by
      rwa [Set.uIcc_of_le hab]
    have hBV := hg'.absolutelyContinuousOnInterval.boundedVariationOn
    have hdiff := hBV.ae_differentiableAt_of_mem_uIcc
    rw [Set.uIcc_of_le hab] at hdiff
    filter_upwards [hdiff] with x hx hbad
    exact hbad.2 (hx hbad.1)
  · rcases hba.eq_or_lt with rfl | hba
    · apply measure_mono_null (by aesop) (MeasureTheory.measure_singleton b)
    · rw [Set.Icc_eq_empty (not_le_of_gt hba)]
      simp

private theorem hausdorffMeasure_planarGraph_nondifferentiableOn_Ioo_eq_zero
    {g : ℝ → ℝ} {a b : ℝ} (hg : LocallyLipschitzOn (Set.Ioo a b) g) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) ''
        {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) = 0 := by
  let s : ℕ → Set ℝ := fun n ↦
    Set.Icc (a + 1 / (n + 1 : ℝ)) (b - 1 / (n + 1 : ℝ))
  let bad : ℕ → Set ℝ := fun n ↦ {x | x ∈ s n ∧ ¬ DifferentiableAt ℝ g x}
  have hs (n : ℕ) : s n ⊆ Set.Ioo a b := by
    intro x hx
    dsimp only [s] at hx
    have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
    exact ⟨lt_of_lt_of_le (lt_add_of_pos_right a hpos) hx.1,
      lt_of_le_of_lt hx.2 (sub_lt_self b hpos)⟩
  have hzero (n : ℕ) : Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' bad n) = 0 := by
    obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      isCompact_Icc (hg.mono (hs n))
    exact hausdorffMeasure_planarGraph_nondifferentiableOn_Icc_eq_zero hC
  apply measure_mono_null
    (t := ⋃ n, (fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' bad n) ?_
    (MeasureTheory.measure_iUnion_null hzero)
  rintro p ⟨x, hx, rfl⟩
  have hδ : 0 < min (x - a) (b - x) := lt_min (sub_pos.mpr hx.1.1) (sub_pos.mpr hx.1.2)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  rw [Set.mem_iUnion]
  refine ⟨n, x, ?_, rfl⟩
  refine ⟨?_, hx.2⟩
  dsimp only [s]
  constructor <;> linarith [lt_of_lt_of_le hn (min_le_left _ _),
    lt_of_lt_of_le hn (min_le_right _ _)]

/-- The graph image of the nondifferentiability set of a locally Lipschitz real
function has zero one-dimensional Hausdorff measure, in isometric coordinates. -/
theorem hausdorffMeasure_coordinateGraph_nondifferentiable_eq_zero
    {g : ℝ → ℝ} {a b : ℝ} (hg : LocallyLipschitzOn (Set.Ioo a b) g)
    (o : EuclideanSpace ℝ (Fin 2))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ o + e.symm !₂[x, g x]) ''
        {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) = 0 := by
  let graph : ℝ → EuclideanSpace ℝ (Fin 2) := fun x ↦ !₂[x, g x]
  let transform : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun p ↦ o + e.symm p
  have htransform : LipschitzWith 1 transform := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simp only [transform, NNReal.coe_one, one_mul, dist_add_left]
    rw [e.symm.dist_map]
  have hzero := hausdorffMeasure_planarGraph_nondifferentiableOn_Ioo_eq_zero hg
  apply le_zero_iff.mp
  rw [show (fun x ↦ o + e.symm !₂[x, g x]) ''
      {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x} =
      transform '' (graph '' {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) by
    simp only [transform, graph, Set.image_image]]
  calc
    Measure.hausdorffMeasure 1
        (transform '' (graph '' {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x})) ≤
      ((1 : NNReal) : ENNReal) ^ (1 : ℝ) * Measure.hausdorffMeasure 1
        (graph '' {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) :=
      htransform.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [hzero, mul_zero]

private theorem norm_coordinateGraph_deriv (g : ℝ → ℝ) (x : ℝ) :
    ‖(!₂[1, deriv g x] : EuclideanSpace ℝ (Fin 2))‖ = Real.sqrt (1 + (deriv g x) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two, Real.norm_eq_abs, pow_two]

private theorem hasDerivAt_coordinateGraph {g : ℝ → ℝ} {x : ℝ}
    (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun y ↦ !₂[y, g y] : ℝ → EuclideanSpace ℝ (Fin 2))
      !₂[1, deriv g x] x := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap
  have hpi : HasDerivAt (fun y i ↦ !₂[y, g y].ofLp i)
      (fun i ↦ !₂[1, deriv g x].ofLp i) x := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hasDerivAt_id x
    · exact hg.hasDerivAt
  have hcomp := L.hasFDerivAt.comp x hpi
  have hfun : (L ∘ fun y i ↦ !₂[y, g y].ofLp i) =
      (fun y ↦ !₂[y, g y] : ℝ → EuclideanSpace ℝ (Fin 2)) := rfl
  have hder : L.comp (ContinuousLinearMap.toSpanSingleton ℝ
      (fun i ↦ !₂[1, deriv g x].ofLp i)) =
      ContinuousLinearMap.toSpanSingleton ℝ
        (!₂[1, deriv g x] : EuclideanSpace ℝ (Fin 2)) := by
    apply ContinuousLinearMap.ext
    intro r
    rw [WithLp.ext_iff]
    funext i
    fin_cases i <;> simp [L, ContinuousLinearMap.comp_apply]
  rw [hfun, hder] at hcomp
  exact hcomp

private theorem integral_restrict_planarGraph_eq_integral_sqrt_mul
    {g : ℝ → ℝ} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hg : LipschitzOnWith C g (Set.Icc a b))
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : Measurable φ) :
    (∫ p, φ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' Set.Icc a b)) =
      ∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2) * φ !₂[x, g x] := by
  let γ : ℝ → EuclideanSpace ℝ (Fin 2) := fun x ↦ !₂[x, g x]
  rw [MeasureTheory.integral_restrict_curve_eq_integral_norm_deriv_mul hab
    (lipschitzOnWith_planarGraph hg) (fun _ _ ↦ rfl) hφ]
  apply intervalIntegral.integral_congr_ae
  have hg' : LipschitzOnWith C g (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact hg
  have hdiff := hg'.absolutelyContinuousOnInterval.boundedVariationOn
    |>.ae_differentiableAt_of_mem_uIcc
  filter_upwards [hdiff] with x hx hxi
  have hderiv := (hasDerivAt_coordinateGraph (hx ⟨le_of_lt hxi.1, hxi.2⟩)).deriv
  rw [hderiv, norm_coordinateGraph_deriv]

/-- Weighted Hausdorff integration over an isometric planar graph equals the
parameter integral weighted by its almost-everywhere speed. -/
theorem integral_restrict_coordinateGraph_eq_integral_sqrt_mul
    {g : ℝ → ℝ} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hg : LipschitzOnWith C g (Set.Icc a b)) (o : EuclideanSpace ℝ (Fin 2))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : Measurable φ) :
    (∫ p, φ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ o + e.symm !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' Set.Icc a b)) =
      ∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2) * φ (o + e.symm !₂[x, g x]) := by
  let F : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2) :=
    e.symm.toIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst (V := EuclideanSpace ℝ (Fin 2))
        (P := EuclideanSpace ℝ (Fin 2)) ℝ o).toIsometryEquiv
  let γ : ℝ → EuclideanSpace ℝ (Fin 2) := fun x ↦ !₂[x, g x]
  have hF : ∀ p, F p = o + e.symm p := by
    intro p
    simp [F, add_comm]
  rw [show (fun x ↦ o + e.symm !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' Set.Icc a b =
      F '' (γ '' Set.Icc a b) by
    rw [Set.image_image]
    congr 1
    funext x
    exact (hF _).symm]
  rw [(F.measurePreserving_hausdorffMeasure 1).setIntegral_image_emb
    F.toHomeomorph.measurableEmbedding φ (γ '' Set.Icc a b)]
  have hbase := integral_restrict_planarGraph_eq_integral_sqrt_mul hab hg
    (hφ.comp F.continuous.measurable)
  simpa only [γ, Function.comp_apply, hF] using hbase

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Integral / Atomic Bounds
-/

@[expose] public section

noncomputable section

namespace MeasureTheory

/-- A finite sum of atomic contributions is bounded by the integral of a nonnegative function. -/
theorem sum_measureReal_mul_le_setIntegral {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : MeasureTheory.Measure α) (D : Finset α)
    {E : Set α} {f : α → ℝ} (hE : MeasurableSet E)
    (hDE : (D : Set α) ⊆ E) (hf : MeasureTheory.IntegrableOn f E μ)
    (hnonneg : ∀ x ∈ E, 0 ≤ f x) :
    ∑ x ∈ D, (μ {x}).toReal * f x ≤ ∫ x in E, f x ∂μ := by
  have hfinite := MeasureTheory.setIntegral_finset D (hf.mono_set hDE)
  simp only [smul_eq_mul, MeasureTheory.measureReal_def] at hfinite
  rw [← hfinite]
  apply MeasureTheory.setIntegral_mono_set hf
  · exact (MeasureTheory.ae_restrict_iff' hE).mpr (Filter.Eventually.of_forall hnonneg)
  · exact Filter.Eventually.of_forall hDE

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Integral / Interval Exhaustion
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace MeasureTheory

/-- Every interior point eventually belongs to the standard inner exhaustion of an interval. -/
theorem eventually_mem_innerIcc_of_mem_Ioo {a b x : ℝ}
    (hx : x ∈ Set.Ioo a b) :
    ∀ᶠ n : ℕ in atTop,
      x ∈ Set.Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1)) := by
  have hleft := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (Iio_mem_nhds (sub_pos.mpr hx.1))
  have hright := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (Iio_mem_nhds (sub_pos.mpr hx.2))
  exact (hleft.and hright).mono fun n hn ↦ by
    constructor <;> linarith [hn.1, hn.2]

/-- Each interval in the standard inner exhaustion lies in the open interval. -/
theorem innerIcc_subset_Ioo (a b : ℝ) (n : ℕ) :
    Set.Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1)) ⊆
      Set.Ioo a b := by
  intro x hx
  have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
  constructor <;> linarith [hx.1, hx.2]

/-- Integrals over compact intervals exhausting the interior converge to the
integral over the full compact interval. -/
theorem tendsto_integral_innerIcc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hf : Integrable f (volume.restrict (Set.Icc a b))) :
    Tendsto (fun n : ℕ ↦ ∫ x in Set.Icc (a + 1 / ((n : ℝ) + 1))
        (b - 1 / ((n : ℝ) + 1)), f x)
      atTop (nhds (∫ x in Set.Icc a b, f x)) := by
  let t := Set.Icc a b
  let s : ℕ → Set ℝ := fun n ↦
    Set.Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1))
  have hs (n : ℕ) : MeasurableSet (s n) := measurableSet_Icc
  have hft : Integrable (t.indicator f) volume :=
    IntegrableOn.integrable_indicator hf measurableSet_Icc
  have hmeas (n : ℕ) : AEStronglyMeasurable ((s n).indicator f) volume := by
    apply (hft.1.indicator (hs n)).congr
    filter_upwards [] with x
    by_cases hx : x ∈ s n
    · have hxi := innerIcc_subset_Ioo a b n hx
      have hxt : x ∈ t := ⟨hxi.1.le, hxi.2.le⟩
      simp [Set.indicator, hx, hxt]
    · simp [Set.indicator, hx]
  have hbound (n : ℕ) : ∀ᵐ x ∂volume,
      ‖(s n).indicator f x‖ ≤ ‖t.indicator f x‖ :=
    Filter.Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ s n
      · have hxi := innerIcc_subset_Ioo a b n hx
        have hxt : x ∈ t := ⟨hxi.1.le, hxi.2.le⟩
        simp [Set.indicator, hx, hxt]
      · simp only [Set.indicator, hx, ↓reduceIte, norm_zero]
        exact norm_nonneg _
  have hIooVolume : Set.Ioo a b =ᵐ[volume] Set.Icc a b := Ioo_ae_eq_Icc
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n ↦ (s n).indicator f x)
      atTop (nhds (t.indicator f x)) := by
    filter_upwards [hIooVolume] with x hxeq
    by_cases hx : x ∈ Set.Ioo a b
    · have hev := eventually_mem_innerIcc_of_mem_Ioo hx
      apply tendsto_const_nhds.congr'
      exact hev.mono fun n hn ↦
        (Set.indicator_of_mem (hxeq.mp hx) f).trans
          (Set.indicator_of_mem hn f).symm
    · have hxt : x ∉ t := fun h ↦ hx (hxeq.mpr h)
      apply tendsto_const_nhds.congr'
      filter_upwards [] with n
      have hxn : x ∉ s n := fun h ↦ by
        have hxi := innerIcc_subset_Ioo a b n h
        exact hxt ⟨hxi.1.le, hxi.2.le⟩
      simp only [Set.indicator, hxn, hxt, ↓reduceIte]
  have ht := tendsto_integral_of_dominated_convergence (μ := volume)
    (fun x ↦ ‖t.indicator f x‖) hmeas hft.norm hbound hlim
  simpa only [s, t, integral_indicator, hs, measurableSet_Icc] using ht

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Integral / Moving Intervals
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace MeasureTheory

/-- Moving interval cutoffs preserve almost-everywhere convergence on the limiting interior. -/
theorem ae_tendsto_indicator_Icc_of_tendsto_endpoints
    {E : Type*} [NormedAddCommGroup E] {a b : ℕ → ℝ} {c d : ℝ}
    {f : ℕ → ℝ → E} {g : ℝ → E}
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 d))
    (hf : ∀ᵐ x ∂volume, x ∈ Ioo c d → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂volume, Tendsto (fun n ↦ (Icc (a n) (b n)).indicator (f n) x)
      atTop (𝓝 ((Icc c d).indicator g x)) := by
  have hne (y : ℝ) : ∀ᵐ x ∂volume, x ≠ y := by
    simpa using (measure_eq_zero_iff_ae_notMem.mp (measure_singleton y :
      volume ({y} : Set ℝ) = 0))
  filter_upwards [hf, hne c, hne d] with x hx hxc hxd
  by_cases hmem : x ∈ Icc c d
  · have hxi : x ∈ Ioo c d :=
      ⟨lt_of_le_of_ne hmem.1 (Ne.symm hxc), lt_of_le_of_ne hmem.2 hxd⟩
    rw [indicator_of_mem hmem]
    apply (hx hxi).congr'
    filter_upwards [ha.eventually (gt_mem_nhds hxi.1),
      hb.eventually (lt_mem_nhds hxi.2)] with n hn hn'
    exact (indicator_of_mem (show x ∈ Icc (a n) (b n) from ⟨hn.le, hn'.le⟩) _).symm
  · rw [indicator_of_notMem hmem]
    apply tendsto_const_nhds.congr'
    have hout : x < c ∨ d < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hmem
    rcases hout with hleft | hright
    · filter_upwards [ha.eventually (lt_mem_nhds hleft)] with n hn
      exact (indicator_of_notMem (show x ∉ Icc (a n) (b n) from
        fun h ↦ (not_le.mpr hn) h.1) _).symm
    · filter_upwards [hb.eventually (gt_mem_nhds hright)] with n hn
      exact (indicator_of_notMem (show x ∉ Icc (a n) (b n) from
        fun h ↦ (not_le.mpr hn) h.2) _).symm

/-- Dominated convergence on intervals whose endpoints converge, using convergence
only in the interior of the limiting interval. -/
theorem tendsto_integral_Icc_of_tendsto_endpoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℕ → ℝ} {c d : ℝ} {f : ℕ → ℝ → E} {g : ℝ → E} {bound : ℝ → ℝ}
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 d))
    (hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (f n) (volume.restrict (Icc (a n) (b n))))
    (hbound : Integrable bound) (hbound_nonneg : ∀ᵐ x ∂volume, 0 ≤ bound x)
    (hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂volume, x ∈ Icc (a n) (b n) → ‖f n x‖ ≤ bound x)
    (hf : ∀ᵐ x ∂volume, x ∈ Ioo c d → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ ∫ x in Icc (a n) (b n), f n x) atTop
      (𝓝 (∫ x in Icc c d, g x)) := by
  have hm : ∀ᶠ n in atTop,
      AEStronglyMeasurable ((Icc (a n) (b n)).indicator (f n)) volume := by
    filter_upwards [hmeas] with n hn
    exact (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr hn
  have hd : ∀ᶠ n in atTop, ∀ᵐ x ∂volume,
      ‖(Icc (a n) (b n)).indicator (f n) x‖ ≤ bound x := by
    filter_upwards [hdom] with n hn
    filter_upwards [hn, hbound_nonneg] with x hx hnonneg
    by_cases hmem : x ∈ Icc (a n) (b n)
    · simpa only [indicator_of_mem hmem] using hx hmem
    · simpa only [indicator_of_notMem hmem, norm_zero] using hnonneg
  have h := tendsto_integral_filter_of_dominated_convergence bound hm hd hbound
    (ae_tendsto_indicator_Icc_of_tendsto_endpoints ha hb hf)
  simpa only [integral_indicator measurableSet_Icc] using h

/-- A uniform bound on moving finite intervals suffices for dominated convergence. -/
theorem tendsto_integral_Icc_of_tendsto_endpoints_of_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℕ → ℝ} {c d M : ℝ} {f : ℕ → ℝ → E} {g : ℝ → E}
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 d))
    (hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (f n) (volume.restrict (Icc (a n) (b n))))
    (hM : 0 ≤ M)
    (hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂volume, x ∈ Icc (a n) (b n) → ‖f n x‖ ≤ M)
    (hf : ∀ᵐ x ∂volume, x ∈ Ioo c d → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ ∫ x in Icc (a n) (b n), f n x) atTop
      (𝓝 (∫ x in Icc c d, g x)) := by
  let s := Icc (c - 1) (d + 1)
  have hs : MeasurableSet s := measurableSet_Icc
  have hi : Integrable (s.indicator (fun _ : ℝ ↦ M)) volume := by
    apply IntegrableOn.integrable_indicator _ hs
    exact integrableOn_const isCompact_Icc.measure_lt_top.ne
  apply tendsto_integral_Icc_of_tendsto_endpoints ha hb hmeas hi
  · exact Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ s <;> simp [indicator, hx, hM]
  · filter_upwards [hdom, ha.eventually (lt_mem_nhds (show c - 1 < c by linarith)),
      hb.eventually (gt_mem_nhds (show d < d + 1 by linarith))] with n hn hna hnb
    filter_upwards [hn] with x hx
    intro hmem
    have hxs : x ∈ s := ⟨hna.le.trans hmem.1, hmem.2.trans hnb.le⟩
    simpa only [indicator_of_mem hxs] using hx hmem
  · exact hf

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Integral / Translation
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

/-- Translation of a measurable real set preserves integrals. -/
theorem integral_image_add_right_eq (c : ℝ) (E : Set ℝ) (hE : MeasurableSet E)
    (f : ℝ → ℝ) :
    (∫ y in (fun x : ℝ ↦ x + c) '' E, f y) = ∫ x in E, f (x + c) := by
  let φ : ℝ → ℝ := fun x ↦ x + c
  have hφ : MeasurableEmbedding φ :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have hpres : MeasurePreserving φ volume volume :=
    ⟨hφ.measurable, map_add_right_eq_self volume c⟩
  have himage : MeasurableSet (φ '' E) := hφ.measurableSet_image' hE
  have hpre : φ ⁻¹' (φ '' E) = E := Set.preimage_image_eq E hφ.injective
  have hr := hpres.restrict_preimage himage
  rw [hpre] at hr
  exact (hr.integral_comp hφ f).symm

/-- Translating both endpoints of a closed real interval translates the integrand. -/
theorem integral_Icc_const_add_eq (c a b : ℝ) (f : ℝ → ℝ) :
    (∫ y in Icc (c + a) (c + b), f y) = ∫ x in Icc a b, f (x + c) := by
  rw [show c + a = a + c from add_comm c a, show c + b = b + c from add_comm c b,
    ← Set.image_add_const_Icc, integral_image_add_right_eq c _ measurableSet_Icc]

/-- Integrability on a translated measurable set is preserved by translation. -/
theorem integrableOn_comp_add_right_iff (c : ℝ) (E : Set ℝ) (hE : MeasurableSet E)
    (f : ℝ → ℝ) :
    IntegrableOn (fun x ↦ f (x + c)) E ↔
      IntegrableOn f ((fun x : ℝ ↦ x + c) '' E) := by
  let φ : ℝ → ℝ := fun x ↦ x + c
  have hφ : MeasurableEmbedding φ :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have hpres : MeasurePreserving φ volume volume :=
    ⟨hφ.measurable, map_add_right_eq_self volume c⟩
  have himage : MeasurableSet (φ '' E) := hφ.measurableSet_image' hE
  have hpre : φ ⁻¹' (φ '' E) = E := Set.preimage_image_eq E hφ.injective
  have hr := hpres.restrict_preimage himage
  rw [hpre] at hr
  exact hr.integrable_comp_emb hφ

/-- A lower Lebesgue integral of a right-translated function is the integral of the function
itself over the translated set. -/
theorem setLIntegral_comp_sub_right (w : ℝ → ℝ≥0∞) (c : ℝ) (A : Set ℝ) :
    ∫⁻ u in A, w (u - c) = ∫⁻ t in (fun t : ℝ ↦ t + c) ⁻¹' A, w t := by
  have hemb : MeasurableEmbedding fun t : ℝ ↦ t + c :=
    (MeasurableEquiv.addRight c).measurableEmbedding
  simpa using ((measurePreserving_add_right (volume : Measure ℝ) c).setLIntegral_comp_preimage_emb
    hemb (fun u ↦ w (u - c)) A).symm

/-- Pushing a weighted restriction of Lebesgue measure forward along `t ↦ t + c` translates both
the set and the weight. -/
theorem map_add_right_restrict_withDensity (c : ℝ) (S : Set ℝ) (w : ℝ → ℝ≥0∞) :
    Measure.map (fun t : ℝ ↦ t + c) ((volume.restrict S).withDensity w) =
      (volume.restrict ((fun t : ℝ ↦ t + c) '' S)).withDensity (fun u ↦ w (u - c)) := by
  have hemb : MeasurableEmbedding fun t : ℝ ↦ t + c :=
    (MeasurableEquiv.addRight c).measurableEmbedding
  ext A hA
  have hpre : MeasurableSet ((fun t : ℝ ↦ t + c) ⁻¹' A) := hA.preimage hemb.measurable
  rw [Measure.map_apply hemb.measurable hA, withDensity_apply _ hpre,
    Measure.restrict_restrict hpre, withDensity_apply _ hA, Measure.restrict_restrict hA,
    setLIntegral_comp_sub_right, Set.preimage_inter, hemb.injective.preimage_image]

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Measure / Atoms
-/

@[expose] public section

noncomputable section

open Set

namespace MeasureTheory

/-- A membership that fails only on a countable set holds almost everywhere on the restriction
of a measure with null singletons. -/
theorem ae_restrict_mem_of_countable_diff {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [NullSingletonClass μ] {S A N : Set α} (hS : MeasurableSet S) (hN : N.Countable)
    (hsub : S \ A ⊆ N) : ∀ᵐ x ∂μ.restrict S, x ∈ A := by
  rw [ae_iff, Measure.restrict_apply' hS]
  exact measure_mono_null (fun x hx ↦ hsub ⟨hx.2, hx.1⟩) (hN.measure_zero μ)

/-- Along an injective parametrization, a finite-measure atom occurs only almost nowhere. -/
theorem ae_measure_singleton_comp_eq_zero_of_injOn
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [SFinite μ] {s : Set ℝ} (hs : MeasurableSet s)
    {f : ℝ → X} (hf : Set.InjOn f s) :
    ∀ᵐ t ∂volume.restrict s, μ {f t} = 0 := by
  let A : Set X := {x | 0 < μ {x}}
  have hA : A.Countable := μ.countable_meas_level_set_pos measurable_id
  let B : Set ℝ := {t | t ∈ s ∧ f t ∈ A}
  have hmaps : MapsTo f B A := fun _ h ↦ h.2
  have hB : B.Countable := hmaps.countable_of_injOn (hf.mono fun _ h ↦ h.1) hA
  filter_upwards [ae_restrict_mem hs, hB.ae_notMem (volume.restrict s)] with t hts htB
  by_contra hne
  exact htB ⟨hts, pos_iff_ne_zero.mpr hne⟩

/-- A measure carried by a finite set is the sum of its atomic contributions. -/
theorem measure_eq_sum_singleton_inter_of_compl_eq_zero
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (S : Finset α) (hS : μ (S : Set α)ᶜ = 0)
    (E : Set α) (hE : MeasurableSet E) :
    μ E = ∑ x ∈ S, μ ({x} ∩ E) := by
  classical
  have hae : ∀ᵐ x ∂μ, x ∈ (S : Set α) := by
    rw [ae_iff]
    exact hS
  have hrestrict : μ.restrict (S : Set α) = μ :=
    Measure.restrict_eq_self_of_ae_mem hae
  have hinter : μ E = μ (E ∩ (S : Set α)) := by
    calc
      μ E = (μ.restrict (S : Set α)) E := by rw [hrestrict]
      _ = μ (E ∩ (S : Set α)) := Measure.restrict_apply hE
  rw [hinter]
  have heq : E ∩ (S : Set α) = ⋃ x ∈ S, ({x} ∩ E : Set α) := by
    ext x
    simp [and_comm]
  rw [heq, measure_biUnion_finset]
  · intro i _ j _ hij
    simp only [Set.disjoint_left]
    intro x hxi hxj
    exact hij (hxi.1.symm.trans hxj.1)
  · intro b _
    exact (measurableSet_singleton b).inter hE

/-- A measure carried by the image of a finite index set is bounded by the sum of atomic bounds
over any index subset containing every index whose atom meets the measured set. -/
theorem measure_le_sum_of_measure_compl_image_eq_zero
    {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (S S' : Finset ι) (f : ι → α) (b : ι → ENNReal)
    (hf : Set.InjOn f (S : Set ι)) (hS : μ (f '' (S : Set ι))ᶜ = 0)
    (hb : ∀ i ∈ S, μ {f i} ≤ b i) (E : Set α) (hE : MeasurableSet E)
    (hactive : ∀ i ∈ S, f i ∈ E → i ∈ S') :
    μ E ≤ ∑ i ∈ S', b i := by
  classical
  have himage : ((S.image f : Finset α) : Set α) = f '' (S : Set ι) := by
    ext x
    simp
  rw [measure_eq_sum_singleton_inter_of_compl_eq_zero μ (S.image f)
    (by rw [himage]; exact hS) E hE]
  calc
    ∑ x ∈ S.image f, μ ({x} ∩ E) = ∑ i ∈ S, μ ({f i} ∩ E) :=
      Finset.sum_image fun i hi j hj h ↦ hf (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hj) h
    _ ≤ ∑ i ∈ S, (if f i ∈ E then b i else 0) := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      by_cases hfi : f i ∈ E
      · have hinter : ({f i} : Set α) ∩ E = {f i} := by
          ext y
          simp [hfi]
        simp only [hinter, hfi, ite_true]
        exact hb i hi
      · have hinter : ({f i} : Set α) ∩ E = ∅ := by
          ext y
          simp [hfi]
        simp [hinter, hfi]
    _ = ∑ i ∈ S.filter (fun i ↦ f i ∈ E), b i := (Finset.sum_filter _ _).symm
    _ ≤ ∑ i ∈ S', b i := by
      refine Finset.sum_le_sum_of_subset fun i hi ↦ ?_
      obtain ⟨hiS, hiE⟩ := Finset.mem_filter.1 hi
      exact hactive i hiS hiE

/-! ### Almost every point of a half-open interval is interior -/

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in the
corresponding open interval. -/
theorem ae_restrict_Ico_mem_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ico a b), t ∈ Ioo a b :=
  ae_restrict_mem_of_countable_diff measurableSet_Ico (countable_singleton a)
    fun _ ⟨hx, hx'⟩ ↦ mem_singleton_iff.2 (le_antisymm (not_lt.1 fun h ↦ hx' ⟨h, hx.2⟩) hx.1)

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in the
corresponding open interval. -/
theorem ae_restrict_Ioc_mem_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ioc a b), t ∈ Ioo a b :=
  ae_restrict_mem_of_countable_diff measurableSet_Ioc (countable_singleton b)
    fun _ ⟨hx, hx'⟩ ↦ mem_singleton_iff.2 (le_antisymm hx.2 (not_lt.1 fun h ↦ hx' ⟨hx.1, h⟩))

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in one
of the two open intervals cut out by an arbitrary intermediate point. -/
theorem ae_restrict_Ico_mem_Ioo_union_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b c : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ico a c), t ∈ Ioo a b ∪ Ioo b c := by
  refine ae_restrict_mem_of_countable_diff measurableSet_Ico
    ((countable_singleton b).insert a) ?_
  rintro x ⟨hx, hx'⟩
  rcases lt_trichotomy x b with h | h | h
  · exact Or.inl (le_antisymm (not_lt.1 fun hlt ↦ hx' (Or.inl ⟨hlt, h⟩)) hx.1)
  · exact Or.inr (mem_singleton_iff.2 h)
  · exact absurd (Or.inr ⟨h, hx.2⟩) hx'

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in one
of the two open intervals cut out by an arbitrary intermediate point. -/
theorem ae_restrict_Ioc_mem_Ioo_union_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b c : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ioc a c), t ∈ Ioo a b ∪ Ioo b c := by
  refine ae_restrict_mem_of_countable_diff measurableSet_Ioc
    ((countable_singleton c).insert b) ?_
  rintro x ⟨hx, hx'⟩
  rcases lt_trichotomy x b with h | h | h
  · exact absurd (Or.inl ⟨hx.1, h⟩) hx'
  · exact Or.inl h
  · exact Or.inr (mem_singleton_iff.2
      (le_antisymm hx.2 (not_lt.1 fun hlt ↦ hx' (Or.inr ⟨h, hlt⟩))))

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Haar-null lines and inner-product level sets

Lines and hyperplanes of a finite-dimensional real normed space carry no additive Haar mass.
This file records the two convenient forms used when a planar region is exhausted by triangles
up to the rays through finitely many vertices.
-/

@[expose] public section

open MeasureTheory
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A line through the origin is a proper subspace once the ambient dimension exceeds one. -/
theorem Submodule.span_singleton_ne_top (h : 1 < Module.finrank ℝ E) (v : E) :
    (ℝ ∙ v) ≠ ⊤ := by
  rcases eq_or_ne v 0 with rfl | hv
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
    rw [Submodule.span_zero_singleton]
    exact bot_ne_top
  · intro htop
    have hfin : Module.finrank ℝ E = 1 := (finrank_eq_one_iff_of_nonzero v hv).2 htop
    omega

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Any line in a space of dimension at least two is null for an additive Haar measure. -/
theorem MeasureTheory.Measure.addHaar_vadd_span_singleton (μ : Measure E)
    [μ.IsAddHaarMeasure] (h : 1 < Module.finrank ℝ E) (o v : E) :
    μ (o +ᵥ (ℝ ∙ v : Set E)) = 0 := by
  rw [measure_vadd]
  exact μ.addHaar_submodule _ (Submodule.span_singleton_ne_top h v)

/-- A countable union of lines through a common point is null. -/
theorem MeasureTheory.Measure.addHaar_iUnion_vadd_span_singleton {ι : Type*} [Countable ι]
    (μ : Measure E) [μ.IsAddHaarMeasure] (h : 1 < Module.finrank ℝ E) (o : E) (v : ι → E) :
    μ (⋃ i, o +ᵥ (ℝ ∙ v i : Set E)) = 0 :=
  measure_iUnion_null fun i ↦ μ.addHaar_vadd_span_singleton h o (v i)

/-- A level set of a nonzero inner-product functional is null for an additive Haar measure. -/
theorem MeasureTheory.Measure.addHaar_setOf_real_inner_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (μ : Measure F) [μ.IsAddHaarMeasure] {u : F} (hu : u ≠ 0) (c : ℝ) :
    μ {p : F | inner ℝ p u = c} = 0 := by
  have hu2 : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
  set f : F →ᵃ[ℝ] ℝ := (innerSL ℝ u).toLinearMap.toAffineMap with hf
  set A := (AffineSubspace.mk' c (⊥ : Submodule ℝ ℝ)).comap f with hA
  have hAset : (A : Set F) = {p : F | inner ℝ p u = c} := by
    ext p
    simp [hA, hf, AffineSubspace.mem_mk', real_inner_comm, sub_eq_zero]
  rw [← hAset]
  refine μ.addHaar_affineSubspace _ fun htop ↦ ?_
  have hp : ((c + ‖u‖ ^ 2) / ‖u‖ ^ 2) • u ∈ A := by rw [htop]; trivial
  rw [← SetLike.mem_coe, hAset, Set.mem_ofPred_eq] at hp
  have : inner ℝ (((c + ‖u‖ ^ 2) / ‖u‖ ^ 2) • u) u = c + ‖u‖ ^ 2 := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  rw [this] at hp
  linarith

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Measure / Map
-/

@[expose] public section

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}

/-- If `g` is almost everywhere a left inverse of `f`, then pushing a measure forward along `f`
and then along `g` recovers it. This is the almost-everywhere form of
`MeasurableEquiv.map_symm_map`. -/
theorem map_map_of_ae_leftInverse {f : α → β} (hf : Measurable f) {g : β → α}
    (hg : Measurable g) (h : ∀ᵐ a ∂μ, g (f a) = a) :
    (μ.map f).map g = μ := by
  rw [map_map hg hf, show μ.map (g ∘ f) = μ.map id from map_congr h, map_id]

end MeasureTheory.Measure

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Measure / With Density
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- An injective image of a weighted restriction preserves null singleton masses. -/
theorem map_restrict_withDensity_singleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [NullSingletonClass μ] (f : α → β) (hf : Measurable f)
    (s : Set α) (hinj : Set.InjOn f s) (w : α → ℝ≥0∞) {x : α} (hx : x ∈ s) :
    Measure.map f ((μ.restrict s).withDensity w) {f x} = 0 := by
  rw [Measure.map_apply hf (measurableSet_singleton _)]
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply (hf (measurableSet_singleton _))]
  have heq : f ⁻¹' {f x} ∩ s = {x} := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun h ↦ hinj h.2 hx h.1, fun h ↦ by subst y; exact ⟨rfl, hx⟩⟩
  rw [heq, measure_singleton]

/-- Pushing a weighted measure forward along a measurable map is linear in the weight: if `w` is
the pointwise combination `a * w₁ + b * w₂`, then the pushforward of `μ.withDensity w` is the
same combination of the pushforwards of `μ.withDensity w₁` and `μ.withDensity w₂`. -/
theorem map_withDensity_eq_smul_add_smul {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) (a b : ℝ≥0∞) {w w₁ w₂ : α → ℝ≥0∞}
    (h₁ : Measurable w₁) (h₂ : Measurable w₂) (hw : ∀ x, w x = a * w₁ x + b * w₂ x) :
    Measure.map φ (μ.withDensity w) =
      a • Measure.map φ (μ.withDensity w₁) + b • Measure.map φ (μ.withDensity w₂) := by
  have hwfun : w = a • w₁ + b • w₂ := funext hw
  rw [hwfun, withDensity_add_left (h₁.const_smul a), withDensity_smul _ h₁,
    withDensity_smul _ h₂, Measure.map_add _ _ hφ, Measure.map_smul _ hφ.aemeasurable,
    Measure.map_smul _ hφ.aemeasurable]

end MeasureTheory.Measure

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Region Between
-/

@[expose] public section

open EuclideanSpace MeasureTheory Set

theorem volume_setOf_mem_Icc_eq_volume_regionBetween {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    volume {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
      volume (regionBetween f g s) := by
  change (volume.prod volume) _ = (volume.prod volume) _
  rw [Measure.prod_apply (measurableSet_region_between_cc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, Set.preimage_ofPred_eq, hx, true_and]
    change volume (Icc (f x) (g x)) = volume (Ioo (f x) (g x))
    rw [Real.volume_Icc, Real.volume_Ioo]
  · simp [regionBetween, hx]

theorem volume_regionBetween_triangle {b h : ℝ} (hb : 0 < b) (hh : 0 ≤ h) :
    volume (regionBetween (fun _ : ℝ ↦ 0) (fun x ↦ h - h / b * x) (Ioc 0 b)) =
      ENNReal.ofReal (b * h / 2) := by
  have hc : Continuous (fun x : ℝ ↦ h - h / b * x) := by fun_prop
  have hi := hc.intervalIntegrable (μ := volume) 0 b
  have hz := (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ))).intervalIntegrable
    (μ := volume) 0 b
  change (volume.prod volume) _ = _
  rw [volume_regionBetween_eq_integral
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hz)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hi) measurableSet_Ioc]
  · congr 1
    simp only [Pi.sub_apply, sub_zero]
    rw [← intervalIntegral.integral_of_le hb.le]
    have hm : IntervalIntegrable (fun x : ℝ ↦ h / b * x) volume 0 b :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 b
    have hh' : IntervalIntegrable (fun _ : ℝ ↦ h) volume 0 b :=
      continuous_const.intervalIntegrable 0 b
    rw [intervalIntegral.integral_sub hh' hm,
      intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id]
    simp only [sub_zero, smul_eq_mul]
    field_simp
    ring
  · intro x hx
    have := mul_le_mul_of_nonneg_left hx.2 (div_nonneg hh hb.le)
    have heq : h / b * b = h := div_mul_cancel₀ h hb.ne'
    linarith

theorem volume_setOf_mem_Ioc_eq_volume_regionBetween
    {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    volume {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioc (f p.1) (g p.1)} =
      volume (regionBetween f g s) := by
  change (volume.prod volume) _ = (volume.prod volume) _
  rw [Measure.prod_apply (measurableSet_region_between_oc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, Set.preimage_ofPred_eq, hx, true_and]
    change volume (Ioc (f x) (g x)) = volume (Ioo (f x) (g x))
    rw [Real.volume_Ioc, Real.volume_Ioo]
  · simp [regionBetween, hx]

/-- The planar volume of the horizontal band between the graphs of `f` and `g` over `s`,
where the first coordinate is the one squeezed between the two graphs. -/
theorem volume_horizontalIcc {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s)
    (hfi : IntegrableOn f s) (hgi : IntegrableOn g s)
    (hfg : ∀ x ∈ s, f x ≤ g x) :
    volume {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Icc (f (p 1)) (g (p 1))} =
      ENNReal.ofReal (∫ x in s, (g - f) x) := by
  let T : Set (ℝ × ℝ) :=
    {p | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)}
  have hT : MeasurableSet T := measurableSet_region_between_cc hf hg hs
  rw [show {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Icc (f (p 1)) (g (p 1))} =
      finTwoCoordinatesSwap ⁻¹' T by rfl,
    volume_preserving_finTwoCoordinatesSwap.measure_preimage hT.nullMeasurableSet]
  change volume T = _
  rw [volume_setOf_mem_Icc_eq_volume_regionBetween hf hg hs]
  change (volume.prod volume) (regionBetween f g s) = _
  rw [volume_regionBetween_eq_integral hfi hgi hs hfg]

/-- The half-open variant of `volume_horizontalIcc`. -/
theorem volume_horizontalIoc {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s)
    (hfi : IntegrableOn f s) (hgi : IntegrableOn g s)
    (hfg : ∀ x ∈ s, f x ≤ g x) :
    volume {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Ioc (f (p 1)) (g (p 1))} =
      ENNReal.ofReal (∫ x in s, (g - f) x) := by
  let T : Set (ℝ × ℝ) :=
    {p | p.1 ∈ s ∧ p.2 ∈ Ioc (f p.1) (g p.1)}
  have hT : MeasurableSet T := measurableSet_region_between_oc hf hg hs
  rw [show {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Ioc (f (p 1)) (g (p 1))} =
      finTwoCoordinatesSwap ⁻¹' T by rfl,
    volume_preserving_finTwoCoordinatesSwap.measure_preimage hT.nullMeasurableSet]
  change volume T = _
  rw [volume_setOf_mem_Ioc_eq_volume_regionBetween hf hg hs]
  change (volume.prod volume) (regionBetween f g s) = _
  rw [volume_regionBetween_eq_integral hfi hgi hs hfg]

/-- A planar set whose second coordinate lies in `[0, 1]` and whose first coordinate is
squeezed between a continuous graph and its horizontal translate by `c` has volume at
most `c`. Only the upper bound is asserted, so no measurability of the set is needed. -/
theorem volume_le_of_subset_horizontalBand {X : Set (EuclideanSpace ℝ (Fin 2))}
    {f : ℝ → ℝ} {c : ℝ} (hf : Continuous f) (hc : 0 ≤ c)
    (hX : ∀ p ∈ X, (0 ≤ p 1 ∧ p 1 ≤ 1) ∧ f (p 1) ≤ p 0 ∧ p 0 ≤ f (p 1) + c) :
    volume X ≤ ENNReal.ofReal c := by
  have hg : Continuous (fun y ↦ f y + c) := hf.add continuous_const
  have hfi : IntegrableOn f (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      (hf.intervalIntegrable 0 1)
  have hgi : IntegrableOn (fun y ↦ f y + c) (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      (hg.intervalIntegrable 0 1)
  have key := volume_horizontalIcc (f := f) (g := fun y ↦ f y + c)
    (s := Icc (0 : ℝ) 1) hf.measurable hg.measurable measurableSet_Icc hfi hgi
    (fun x _ ↦ by simp [hc])
  have hint : ∫ x in Icc (0 : ℝ) 1, ((fun y ↦ f y + c) - f) x = c := by
    have hdiff : ((fun y ↦ f y + c) - f) = fun _ ↦ c := by funext y; simp
    rw [hdiff, setIntegral_const]
    simp
  rw [hint] at key
  refine le_trans (measure_mono ?_) key.le
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hX p hp
  exact ⟨h1, h2, h3⟩

/-- The horizontal unit strip meets the band `c ≤ a * x + b * y ≤ c + 1` in a
parallelogram of area `1 / |a|`. Only the upper bound is asserted. -/
theorem volume_horizontalBand_inter_le (a b c : ℝ) (ha : a ≠ 0) :
    volume {p : EuclideanSpace ℝ (Fin 2) | (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
        (c ≤ a * p 0 + b * p 1 ∧ a * p 0 + b * p 1 ≤ c + 1)} ≤
      ENNReal.ofReal (1 / |a|) := by
  have habs : 0 < |a| := abs_pos.mpr ha
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · refine volume_le_of_subset_horizontalBand (f := fun y ↦ (c + 1 - b * y) / a)
      (c := 1 / |a|) (by fun_prop) (by positivity) ?_
    rintro p ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [div_le_iff_of_neg hneg]
      linarith
    · have hrw : (c + 1 - b * p 1) / a + 1 / |a| = (c - b * p 1) / a := by
        rw [abs_of_neg hneg]
        field_simp
        ring
      rw [hrw, le_div_iff_of_neg hneg]
      linarith
  · refine volume_le_of_subset_horizontalBand (f := fun y ↦ (c - b * y) / a)
      (c := 1 / |a|) (by fun_prop) (by positivity) ?_
    rintro p ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [div_le_iff₀ hpos]
      linarith
    · have hrw : (c - b * p 1) / a + 1 / |a| = (c + 1 - b * p 1) / a := by
        rw [abs_of_pos hpos]
        field_simp
        ring
      rw [hrw, le_div_iff₀ hpos]
      linarith

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Planar trapezoids with horizontal parallel sides
-/

@[expose] public section

namespace EuclideanSpace

/-- A convex planar set containing the four vertices of a trapezoid whose parallel sides are
the horizontal segments at heights `0` and `1` contains the whole trapezoid. -/
theorem horizontalTrapezoid_subset_of_convex {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : Convex ℝ S) {l₀ r₀ l₁ r₁ : ℝ}
    (h₀l : (!₂[l₀, 0] : EuclideanSpace ℝ (Fin 2)) ∈ S)
    (h₀r : (!₂[r₀, 0] : EuclideanSpace ℝ (Fin 2)) ∈ S)
    (h₁l : (!₂[l₁, 1] : EuclideanSpace ℝ (Fin 2)) ∈ S)
    (h₁r : (!₂[r₁, 1] : EuclideanSpace ℝ (Fin 2)) ∈ S) :
    {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc ((1 - q 1) * l₀ + q 1 * l₁) ((1 - q 1) * r₀ + q 1 * r₁)} ⊆ S := by
  rintro q ⟨⟨hy0, hy1⟩, hql, hqr⟩
  have hleft : ((1 - q 1) • (!₂[l₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[l₁, 1]) ∈ S :=
    hS h₀l h₁l (by linarith) hy0 (by ring)
  have hright : ((1 - q 1) • (!₂[r₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[r₁, 1]) ∈ S :=
    hS h₀r h₁r (by linarith) hy0 (by ring)
  obtain ⟨s, hs0, hs1, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      q 0 = (1 - s) * ((1 - q 1) * l₀ + q 1 * l₁) + s * ((1 - q 1) * r₀ + q 1 * r₁) := by
    rcases (hql.trans hqr).eq_or_lt with hLR | hLR
    · exact ⟨0, le_rfl, zero_le_one, by rw [sub_zero, one_mul, zero_mul, add_zero]; linarith⟩
    · have hne : (1 - q 1) * r₀ + q 1 * r₁ - ((1 - q 1) * l₀ + q 1 * l₁) ≠ 0 := by linarith
      refine ⟨(q 0 - ((1 - q 1) * l₀ + q 1 * l₁)) /
          ((1 - q 1) * r₀ + q 1 * r₁ - ((1 - q 1) * l₀ + q 1 * l₁)),
        div_nonneg (by linarith) (by linarith), by rw [div_le_one (by linarith)]; linarith, ?_⟩
      field_simp
      ring
  have hcoord : ∀ z w : EuclideanSpace ℝ (Fin 2), z 0 = w 0 → z 1 = w 1 → z = w := by
    intro z w h0 h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have heq : q = (1 - s) • ((1 - q 1) • (!₂[l₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[l₁, 1]) +
      s • ((1 - q 1) • (!₂[r₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[r₁, 1]) := by
    refine hcoord _ _ ?_ ?_
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
      linear_combination hs
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring
  rw [heq]
  exact hS hleft hright (by linarith) hs0 (by ring)

/-- The planar area of the trapezoid cut from the horizontal band `y₀ ≤ y ≤ y₁` by the two lines
`x = a + b * y` and `x = c + d * y`: the height of the band times the mean of the lengths of its
two horizontal sides. -/
theorem volume_horizontalTrapezoid_band {y₀ y₁ a b c d : ℝ} (hy : y₀ ≤ y₁)
    (h₀ : a + b * y₀ ≤ c + d * y₀) (h₁ : a + b * y₁ ≤ c + d * y₁) :
    MeasureTheory.volume {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc y₀ y₁ ∧
        q 0 ∈ Set.Icc (a + b * q 1) (c + d * q 1)} =
      ENNReal.ofReal ((y₁ - y₀) *
        ((c + d * y₀ - (a + b * y₀)) + (c + d * y₁ - (a + b * y₁))) / 2) := by
  have hfc : Continuous fun y : ℝ ↦ a + b * y := by fun_prop
  have hgc : Continuous fun y : ℝ ↦ c + d * y := by fun_prop
  rw [volume_horizontalIcc (f := fun y : ℝ ↦ a + b * y) (g := fun y : ℝ ↦ c + d * y)
    (s := Set.Icc y₀ y₁) hfc.measurable hgc.measurable measurableSet_Icc
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hy).mp (hfc.intervalIntegrable y₀ y₁))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hy).mp (hgc.intervalIntegrable y₀ y₁))
    (fun y hy' ↦ by
      rcases hy.eq_or_lt with rfl | hylt
      · have : y = y₀ := le_antisymm hy'.2 hy'.1
        rw [this]
        exact h₀
      · have hcoef : (y₁ - y) * (c + d * y₀ - (a + b * y₀)) +
            (y - y₀) * (c + d * y₁ - (a + b * y₁)) =
            (y₁ - y₀) * (c + d * y - (a + b * y)) := by ring
        nlinarith [mul_nonneg (by linarith [hy'.2] : (0 : ℝ) ≤ y₁ - y) (by linarith : (0 : ℝ) ≤
            c + d * y₀ - (a + b * y₀)),
          mul_nonneg (by linarith [hy'.1] : (0 : ℝ) ≤ y - y₀) (by linarith : (0 : ℝ) ≤
            c + d * y₁ - (a + b * y₁))])]
  congr 1
  have hrw : ((fun y : ℝ ↦ c + d * y) - fun y : ℝ ↦ a + b * y) =
      fun y : ℝ ↦ (c - a) + (d - b) * y := by
    funext y
    simp only [Pi.sub_apply]
    ring
  have hii : IntervalIntegrable (fun x : ℝ ↦ (d - b) * x) MeasureTheory.volume y₀ y₁ :=
    (by fun_prop : Continuous fun x : ℝ ↦ (d - b) * x).intervalIntegrable y₀ y₁
  rw [hrw, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hy,
    intervalIntegral.integral_add intervalIntegrable_const hii,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

/-- The planar area of a trapezoid whose parallel sides are the horizontal segments
`[l₀, r₀] × {0}` and `[l₁, r₁] × {1}` is the mean of their lengths. -/
theorem volume_horizontalTrapezoid {l₀ r₀ l₁ r₁ : ℝ} (h₀ : l₀ ≤ r₀) (h₁ : l₁ ≤ r₁) :
    MeasureTheory.volume {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc ((1 - q 1) * l₀ + q 1 * l₁) ((1 - q 1) * r₀ + q 1 * r₁)} =
      ENNReal.ofReal ((r₀ - l₀ + (r₁ - l₁)) / 2) := by
  have hset : {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc ((1 - q 1) * l₀ + q 1 * l₁) ((1 - q 1) * r₀ + q 1 * r₁)} =
      {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc (l₀ + (l₁ - l₀) * q 1) (r₀ + (r₁ - r₀) * q 1)} := by
    refine Set.ext fun q ↦ ?_
    simp only [Set.mem_ofPred_eq,
      show (1 - q 1) * l₀ + q 1 * l₁ = l₀ + (l₁ - l₀) * q 1 from by ring,
      show (1 - q 1) * r₀ + q 1 * r₁ = r₀ + (r₁ - r₀) * q 1 from by ring]
  rw [hset, volume_horizontalTrapezoid_band zero_le_one (by simpa using h₀) (by simpa using h₁)]
  congr 1
  ring

end EuclideanSpace

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The area of a planar triangle

The convex hull of three points of the Euclidean plane has area one half of the absolute
determinant of the two edge vectors emanating from the first point. The proof transports the
standard right triangle, whose area is computed by integration, along the linear map sending
the coordinate basis to the two edge vectors.
-/

@[expose] public section

open MeasureTheory Set
open scoped Pointwise

namespace EuclideanSpace

private def standardTriangleProd : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioc 0 1 ∧ p.2 ∈ Icc 0 (1 - p.1)}

private theorem measurableSet_standardTriangleProd : MeasurableSet standardTriangleProd := by
  have h : MeasurableSet {p : ℝ × ℝ | (0 < p.1 ∧ p.1 ≤ 1) ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 - p.1} :=
    ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const)).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_const.sub measurable_fst)))
  simpa only [standardTriangleProd, Set.mem_Ioc, Set.mem_Icc] using h

private theorem volume_standardTriangleProd :
    volume standardTriangleProd = ENNReal.ofReal (1 / 2) := by
  rw [show standardTriangleProd =
      {p : ℝ × ℝ | p.1 ∈ Ioc 0 1 ∧ p.2 ∈ Icc (0 : ℝ) (1 - p.1)} from rfl,
    volume_setOf_mem_Icc_eq_volume_regionBetween
      (f := fun _ : ℝ ↦ 0) (g := fun x ↦ 1 - x) (s := Ioc 0 1)
      measurable_const (measurable_const.sub measurable_id) measurableSet_Ioc]
  simpa using
    (volume_regionBetween_triangle (b := 1) (h := 1)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1))

private def standardTriangle : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ∈ Ioc 0 1 ∧ p 1 ∈ Icc 0 (1 - p 0)}

private theorem volume_standardTriangle : volume standardTriangle = ENNReal.ofReal (1 / 2) := by
  have hpre := volume_preserving_finTwoCoordinates.measure_preimage
    measurableSet_standardTriangleProd.nullMeasurableSet
  rw [show (fun p : EuclideanSpace ℝ (Fin 2) ↦ (p 0, p 1)) ⁻¹' standardTriangleProd =
      standardTriangle from rfl, volume_standardTriangleProd] at hpre
  exact hpre

private def closedStandardTriangle : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 - p 0}

private theorem volume_closedStandardTriangle :
    volume closedStandardTriangle = ENNReal.ofReal (1 / 2) := by
  rw [← volume_standardTriangle]
  refine (measure_eq_measure_of_null_sdiff (μ := volume) ?_ ?_).symm
  · exact fun p hp ↦ ⟨hp.1.1.le, hp.2⟩
  · refine measure_mono_null
      (t := {p : EuclideanSpace ℝ (Fin 2) | inner ℝ p (EuclideanSpace.single 0 (1 : ℝ)) = 0})
      (fun p hp ↦ ?_) ?_
    · have hp0 : p 0 = 0 := by
        refine le_antisymm (le_of_not_gt fun hpos ↦ hp.2 ⟨⟨hpos, ?_⟩, hp.1.2⟩) hp.1.1
        linarith [hp.1.2.1, hp.1.2.2]
      simpa [EuclideanSpace.inner_single_right] using hp0
    · refine volume.addHaar_setOf_real_inner_eq (fun h ↦ ?_) 0
      have hone : (1 : ℝ) = 0 := by
        simpa [PiLp.single_apply] using congrArg (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0) h
      exact one_ne_zero hone

private def standardTriangleVertices : Set (EuclideanSpace ℝ (Fin 2)) :=
  {0, EuclideanSpace.single 0 (1 : ℝ), EuclideanSpace.single 1 (1 : ℝ)}

private theorem convex_closedStandardTriangle : Convex ℝ closedStandardTriangle := by
  intro p hp q hq a b ha hb hab
  simp only [closedStandardTriangle, Set.mem_ofPred_eq] at hp hq ⊢
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    nlinarith [hp.1, hq.1, hp.2.1, hq.2.1, hp.2.2, hq.2.2]

private theorem convexHull_standardTriangleVertices :
    convexHull ℝ standardTriangleVertices = closedStandardTriangle := by
  refine Set.Subset.antisymm (convexHull_min (fun p hp ↦ ?_) convex_closedStandardTriangle)
    (fun p hp ↦ ?_)
  · simp only [standardTriangleVertices, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;>
      norm_num [closedStandardTriangle, PiLp.single_apply]
  · simp only [closedStandardTriangle, Set.mem_ofPred_eq] at hp
    refine mem_convexHull_of_exists_fintype ![1 - p 0 - p 1, p 0, p 1]
      ![0, EuclideanSpace.single 0 (1 : ℝ), EuclideanSpace.single 1 (1 : ℝ)] ?_ ?_ ?_ ?_
    · intro i
      fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_succ]
    · intro i
      fin_cases i <;> simp [standardTriangleVertices]
    · ext i
      fin_cases i <;> simp [Fin.sum_univ_succ]

private def triangleMap (u v : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := p 0 • u + p 1 • v
  map_add' p q := by
    ext i
    simp [add_smul, add_assoc, add_left_comm]
  map_smul' c p := by
    ext i
    simp [mul_smul]

private theorem det_triangleMap (u v : EuclideanSpace ℝ (Fin 2)) :
    LinearMap.det (triangleMap u v) = u 0 * v 1 - v 0 * u 1 := by
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 2)), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, PiLp.basisFun_repr, triangleMap,
    PiLp.basisFun_apply, Fin.isValue]
  norm_num

private theorem convexHull_triple_eq_image (u v : EuclideanSpace ℝ (Fin 2)) :
    convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2))) =
      triangleMap u v '' closedStandardTriangle := by
  have himage : triangleMap u v '' standardTriangleVertices =
      ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [standardTriangleVertices, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl <;> simp [triangleMap]
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp [standardTriangleVertices], by simp [triangleMap]⟩
      · exact ⟨EuclideanSpace.single 0 (1 : ℝ), by simp [standardTriangleVertices],
          by simp [triangleMap]⟩
      · exact ⟨EuclideanSpace.single 1 (1 : ℝ), by simp [standardTriangleVertices],
          by simp [triangleMap]⟩
  rw [← himage, ← LinearMap.image_convexHull, convexHull_standardTriangleVertices]

/-- The triangle spanned by the origin and two vectors of the Euclidean plane has area one
half of the absolute determinant of their coordinates. -/
theorem volume_convexHull_zero_pair (u v : EuclideanSpace ℝ (Fin 2)) :
    volume (convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))) =
      ENNReal.ofReal (|u 0 * v 1 - v 0 * u 1| / 2) := by
  rw [convexHull_triple_eq_image, Measure.addHaar_image_linearMap, det_triangleMap,
    volume_closedStandardTriangle, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

/-- The area of a planar triangle is one half of the absolute coordinate determinant of its
two edge vectors. -/
theorem volume_convexHull_triple (a b c : EuclideanSpace ℝ (Fin 2)) :
    volume (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) =
      ENNReal.ofReal (|(b - a) 0 * (c - a) 1 - (c - a) 0 * (b - a) 1| / 2) := by
  have hvertices : ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) =
      a +ᵥ ({0, b - a, c - a} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_vadd_set]
    constructor
    · intro hp
      rcases hp with hp | hp | hp
      · exact ⟨0, by simp, by simp [hp]⟩
      · refine ⟨b - a, by simp, ?_⟩
        rw [hp]
        change a + (b - a) = b
        abel
      · refine ⟨c - a, by simp, ?_⟩
        rw [hp]
        change a + (c - a) = c
        abel
    · rintro ⟨q, hq, hp⟩
      rcases hq with hq | hq | hq
      · subst hq
        simp only [vadd_eq_add, add_zero] at hp
        exact hp ▸ Or.inl rfl
      · refine Or.inr (Or.inl ?_)
        rw [← hp, hq]
        change a + (b - a) = b
        abel
      · refine Or.inr (Or.inr ?_)
        rw [← hp, hq]
        change a + (c - a) = c
        abel
  rw [hvertices, convexHull_vadd, measure_vadd, volume_convexHull_zero_pair]

end EuclideanSpace

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Stieltjes Density
-/

@[expose] public section

open MeasureTheory Set

/-- Equality of interval increments identifies a continuous BV function's vector measure. -/
theorem BoundedVariationOn.vectorMeasure_eq_withDensity_of_integral_Icc
    {α E : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    [CompactIccSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f r : α → E} {μ : Measure α} (hf : BoundedVariationOn f univ)
    (hcont : Continuous f) (hr : Integrable r μ)
    (hinc : ∀ a b, a ≤ b → f b - f a = ∫ x in Icc a b, r x ∂μ) :
    hf.vectorMeasure = μ.withDensityᵥ r := by
  apply VectorMeasure.ext_of_Icc
  intro a b hab
  rw [hf.vectorMeasure_Icc hab, (hcont.continuousAt (x := b)).continuousWithinAt.rightLim_eq,
    (hcont.continuousAt (x := a)).continuousWithinAt.leftLim_eq,
    withDensityᵥ_apply hr measurableSet_Icc]
  exact hinc a b hab

/-- Integrating on a subtype and a measurable preimage agrees with restricting both sets. -/
theorem MeasureTheory.integral_subtype_preimage {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (f : α → E) :
    (∫ x in {x : s | (x : α) ∈ t}, f (x : α) ∂μ.comap Subtype.val) =
      ∫ x in t, f x ∂μ.restrict s := by
  have hpre : MeasurableSet {x : s | (x : α) ∈ t} := ht.preimage measurable_subtype_coe
  rw [← integral_indicator (μ := μ.comap (Subtype.val : s → α))
    (f := fun x : s ↦ f (x : α)) hpre]
  change (∫ x : s, (t.indicator f) (x : α) ∂μ.comap Subtype.val) = _
  rw [integral_subtype_comap hs, integral_indicator ht]

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Vector Measure / Interval
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace MeasureTheory.VectorMeasure

/-- Agreement on half-open intervals and the whole space determines a vector measure. -/
theorem ext_of_Ioc {α E : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E] (μ ν : VectorMeasure α E)
    (h : ∀ a b, a < b → μ (Ioc a b) = ν (Ioc a b))
    (huniv : μ univ = ν univ) : μ = ν := by
  apply ext_of_generateFrom {s | ∃ a b, a < b ∧ Ioc a b = s} _
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc α))
    (isPiSystem_Ioc id id) huniv
  rintro s ⟨a, b, hab, rfl⟩
  exact h a b hab

end MeasureTheory.VectorMeasure

/-- Pulling an integrable density back along a measurable embedding gives its image integrals. -/
theorem MeasurableEmbedding.exists_vectorMeasure_image_integral
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure β) (g : β → E)
    (hg : Integrable g μ) :
    ∃ ν : VectorMeasure α E, ∀ s, MeasurableSet s → ν s = ∫ x in f '' s, g x ∂μ := by
  have hi : Integrable (fun x ↦ g (f x)) (μ.comap f) := by
    apply hf.integrable_map_iff.mp
    rw [hf.map_comap]
    exact hg.integrableOn
  refine ⟨(μ.comap f).withDensityᵥ (fun x ↦ g (f x)), ?_⟩
  intro s hs
  rw [withDensityᵥ_apply hi hs]
  have h := hf.setIntegral_map (μ := μ.comap f) g (f '' s)
  rw [hf.map_comap, hf.injective.preimage_image,
    Measure.restrict_restrict_of_subset (image_subset_range _ _)] at h
  exact h.symm

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Vector Measure / With Density
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MeasureTheory

/-- Integrating a bounded function against a real signed density multiplies the ordinary
integrand by that density. -/
theorem VectorMeasure.setIntegral_withDensity_mul_of_bounded
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {r q : X → ℝ}
    (hr : Integrable r μ) (hq : AEStronglyMeasurable q μ) (C : ℝ)
    (hq_bound : ∀ x, ‖q x‖ ≤ C) (E : Set X) (hE : MeasurableSet E) :
    (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μ.withDensityᵥ r]) =
      ∫ x in E, q x * r x ∂μ := by
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hr]
  let μp := μ.withDensity fun x ↦ ENNReal.ofReal (r x)
  let μn := μ.withDensity fun x ↦ ENNReal.ofReal (-r x)
  let _ : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hr.2
  let _ : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hr.neg.2
  have hqp : (μp.toSignedMeasure : SignedMeasure X).Integrable q := by
    rw [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound (hq.mono_ac (withDensity_absolutelyContinuous _ _)) C
      (ae_of_all _ hq_bound)
  have hqn : (μn.toSignedMeasure : SignedMeasure X).Integrable q := by
    rw [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound (hq.mono_ac (withDensity_absolutelyContinuous _ _)) C
      (ae_of_all _ hq_bound)
  have hmul : ContinuousLinearMap.mul ℝ ℝ =
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    ext; simp
  change ∫ᵛ x, q x ∂[ContinuousLinearMap.mul ℝ ℝ;
      ((μp.toSignedMeasure : SignedMeasure X) - μn.toSignedMeasure).restrict E] = _
  rw [VectorMeasure.restrict_sub,
    VectorMeasure.integral_sub_vectorMeasure hqp.restrict hqn.restrict]
  have hp : (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μp.toSignedMeasure]) =
      ∫ x in E, q x ∂μp := by
    rw [hmul]
    exact VectorMeasure.setIntegral_toSignedMeasure hE
  have hn : (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μn.toSignedMeasure]) =
      ∫ x in E, q x ∂μn := by
    rw [hmul]
    exact VectorMeasure.setIntegral_toSignedMeasure hE
  have hdp : ∫ x in E, q x ∂μp =
      ∫ x in E, (ENNReal.ofReal (r x)).toReal • q x ∂μ := by
    apply setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    · exact hr.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
    · filter_upwards with x
      simp
    · exact hE
  have hdn : ∫ x in E, q x ∂μn =
      ∫ x in E, (ENNReal.ofReal (-r x)).toReal • q x ∂μ := by
    apply setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    · exact hr.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
    · filter_upwards with x
      simp
    · exact hE
  rw [hp, hn, hdp, hdn]
  have hip : Integrable (fun x ↦ (ENNReal.ofReal (r x)).toReal • q x) μ := by
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul, mul_comm] using
      hr.pos_part.bdd_mul hq (ae_of_all _ hq_bound)
  have hin : Integrable (fun x ↦ (ENNReal.ofReal (-r x)).toReal • q x) μ := by
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul, mul_comm] using
      hr.neg_part.bdd_mul hq (ae_of_all _ hq_bound)
  rw [← MeasureTheory.integral_sub hip.integrableOn hin.integrableOn]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rcases le_total 0 (r x) with hx | hx
  · rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    simp only [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    simp only [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    ring

/-- Integrating a continuous real function on a compact space against a signed density
multiplies the ordinary integrand by that density. -/
theorem VectorMeasure.setIntegral_withDensity_mul
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [CompactSpace X]
    {μ : Measure X} {r q : X → ℝ}
    (hr : Integrable r μ) (hq : Continuous q) (E : Set X) (hE : MeasurableSet E) :
    (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μ.withDensityᵥ r]) =
      ∫ x in E, q x * r x ∂μ := by
  let q' : BoundedContinuousFunction X ℝ :=
    ContinuousMap.equivBoundedOfCompact X ℝ ⟨q, hq⟩
  exact VectorMeasure.setIntegral_withDensity_mul_of_bounded hr hq.aestronglyMeasurable ‖q'‖
    (fun x ↦ BoundedContinuousFunction.norm_coe_le_norm q' x) E hE

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Volume
-/

@[expose] public section

open scoped Pointwise

namespace MeasureTheory

/-- The square root of planar volume scales linearly under nonnegative dilations. -/
theorem volume_smul_rpow_half (S : Set (EuclideanSpace ℝ (Fin 2))) (a : ℝ) (ha : 0 ≤ a) :
    volume (a • S) ^ (2 : ℝ)⁻¹ = ENNReal.ofReal a * volume S ^ (2 : ℝ)⁻¹ := by
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg (μ := volume) ha]
  simp only [finrank_euclideanSpace_fin]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  rw [ENNReal.ofReal_pow ha]
  simpa using ENNReal.pow_rpow_inv_natCast (by norm_num : (2 : ℕ) ≠ 0) (ENNReal.ofReal a)

end MeasureTheory

end

end
