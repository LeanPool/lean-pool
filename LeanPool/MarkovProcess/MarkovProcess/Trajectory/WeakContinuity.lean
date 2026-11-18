/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.CylinderAlgebra
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.PathTightness
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.StartingPointContinuity
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure


/-!
# Weak continuity of the path law in the starting point

`Trajectory/StartingPointContinuity.lean` proves that cylinder expectations of the
continuous-path process depend continuously on the starting point.  This file upgrades that to
*every* bounded continuous functional of the path, which is weak continuity of the path law
itself.

The route needs no compactness theorem for measures.  Fix a starting point `x0` and a compact
neighbourhood `K0` of it.  Tightness (`Trajectory/PathTightness.lean`) produces one compact set of
paths carrying all but `eta` of the mass from every starting point of `K0`.  On that compact set
Stone--Weierstrass replaces the given functional by a bounded cylinder functional, with a norm
bound that makes the discarded mass cheap (`Trajectory/CylinderAlgebra.lean`), and the cylinder
functional is already known to have continuous expectations.  Three epsilons and a triangle
inequality finish the argument.

Main results:

* `IsFellerKernelSemigroup.continuous_integral_boundedCylinder`, continuity for cylinder
  functionals;
* `IsFellerKernelSemigroup.continuous_integral_continuousProcess`, continuity for every bounded
  continuous functional of the path;
* `IsConservative.pathLaw` and `IsFellerKernelSemigroup.continuous_pathLaw`, the same statement
  read as continuity into the space of probability measures on path space with its topology of
  convergence in distribution.

Nothing here asserts relative compactness of a family of laws, and no convergence of a sequence
of semigroups is treated.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace MarkovProcess

section TruncationError

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Two bounded continuous functionals that agree to within `eps` on a measurable set have
integrals that agree to within `eps` plus the mass off that set times the sum of the norms. -/
theorem abs_integral_sub_le_of_approx_on (mu : Measure X) [IsProbabilityMeasure mu]
    (F G : X →ᵇ ℝ) {K : Set X} (hK : MeasurableSet K) {eps : ℝ} (heps : 0 ≤ eps)
    (happrox : ∀ x ∈ K, |G x - F x| ≤ eps) :
    |(∫ x, F x ∂mu) - ∫ x, G x ∂mu| ≤ eps + (‖F‖ + ‖G‖) * mu.real Kᶜ := by
  have hF : Integrable (fun x ↦ F x) mu := F.integrable mu
  have hG : Integrable (fun x ↦ G x) mu := G.integrable mu
  have hKc : MeasurableSet Kᶜ := hK.compl
  have hind : Integrable (Set.indicator Kᶜ (1 : X → ℝ)) mu :=
    (integrable_const (1 : ℝ)).indicator hKc
  have hbound : ∀ x, ‖F x - G x‖ ≤
      eps + (‖F‖ + ‖G‖) * Set.indicator Kᶜ (1 : X → ℝ) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_notMem (by simpa using hx), mul_zero, add_zero, Real.norm_eq_abs,
        abs_sub_comm]
      exact happrox x hx
    · rw [Set.indicator_of_mem (by simpa using hx), Pi.one_apply, mul_one]
      have h1 : ‖F x - G x‖ ≤ ‖F x‖ + ‖G x‖ := norm_sub_le _ _
      have h2 : ‖F x‖ ≤ ‖F‖ := F.norm_coe_le_norm x
      have h3 : ‖G x‖ ≤ ‖G‖ := G.norm_coe_le_norm x
      linarith
  have hmaj : Integrable
      (fun x ↦ eps + (‖F‖ + ‖G‖) * Set.indicator Kᶜ (1 : X → ℝ) x) mu :=
    (integrable_const eps).add (hind.const_mul _)
  rw [← integral_sub hF hG, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hmaj (Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_add (integrable_const eps) (hind.const_mul _), integral_const, integral_const_mul,
    integral_indicator_one hKc, probReal_univ, smul_eq_mul, one_mul]

/-- Tightness and compact approximation reduce convergence of bounded continuous integrals
 to convergence on a family of test functions. The tightness bound is needed only eventually. -/
theorem tendsto_integral_of_tight_approximation [T2Space X]
    {ι : Type*} {l : Filter ι} (mu : ι → Measure X) (nu : Measure X)
    [∀ i, IsProbabilityMeasure (mu i)] [IsProbabilityMeasure nu]
    (tests : Set (X →ᵇ ℝ)) (F : X →ᵇ ℝ)
    (htight : ∀ eta : ℝ, 0 < eta → ∃ K : Set X, IsCompact K ∧
      (∀ᶠ i in l, mu i Kᶜ ≤ ENNReal.ofReal eta) ∧ nu Kᶜ ≤ ENNReal.ofReal eta)
    (happrox : ∀ K : Set X, IsCompact K → ∀ eps : ℝ, 0 < eps →
      ∃ G ∈ tests, ‖G‖ ≤ ‖F‖ + eps ∧ ∀ x ∈ K, |G x - F x| ≤ eps)
    (htests : ∀ G ∈ tests, Tendsto (fun i ↦ ∫ x, G x ∂mu i) l (nhds (∫ x, G x ∂nu))) :
    Tendsto (fun i ↦ ∫ x, F x ∂mu i) l (nhds (∫ x, F x ∂nu)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  let error := eps / 5
  have herror : 0 < error := by dsimp [error]; positivity
  let bound := ‖F‖ + (‖F‖ + error)
  have hbound : 0 < bound := by
    dsimp [bound]
    exact add_pos_of_nonneg_of_pos (norm_nonneg F)
      (add_pos_of_nonneg_of_pos (norm_nonneg F) herror)
  let eta := error / bound
  have heta : 0 < eta := div_pos herror hbound
  obtain ⟨K, hK, hmass, hnu⟩ := htight eta heta
  obtain ⟨G, hG, hGnorm, hGapprox⟩ := happrox K hK error herror
  have hnorm : ‖F‖ + ‖G‖ ≤ bound := add_le_add_right hGnorm _
  have hestimate : ∀ rho : Measure X, ∀ _ : IsProbabilityMeasure rho,
      rho Kᶜ ≤ ENNReal.ofReal eta →
      |(∫ x, F x ∂rho) - ∫ x, G x ∂rho| ≤ 2 * error := by
    intro rho _ hrho
    have hreal : rho.real Kᶜ ≤ eta :=
      ENNReal.toReal_le_of_le_ofReal heta.le hrho
    have hproduct : (‖F‖ + ‖G‖) * rho.real Kᶜ ≤ error := by
      refine (mul_le_mul hnorm hreal measureReal_nonneg hbound.le).trans_eq ?_
      exact mul_div_cancel₀ error hbound.ne'
    have h := abs_integral_sub_le_of_approx_on rho F G hK.isClosed.measurableSet
      herror.le hGapprox
    exact h.trans ((add_le_add_right hproduct error).trans_eq (two_mul error).symm)
  have hnear := Metric.tendsto_nhds.mp (htests G hG) error herror
  filter_upwards [hmass, hnear] with i hi hclose
  rw [Real.dist_eq] at hclose ⊢
  have hleft := hestimate (mu i) inferInstance hi
  have hright := hestimate nu inferInstance hnu
  have htriangle := abs_sub_le (∫ x, F x ∂mu i) (∫ x, G x ∂mu i) (∫ x, F x ∂nu)
  have htriangle' := abs_sub_le (∫ x, G x ∂mu i) (∫ x, G x ∂nu) (∫ x, F x ∂nu)
  rw [abs_sub_comm] at hright
  dsimp [error] at hleft hright hclose
  linarith only [hleft, hright, hclose, htriangle, htriangle']

end TruncationError

namespace SubMarkovKernelSemigroup

section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [ProperSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- Expectations of a bounded cylinder functional depend continuously on the starting point. -/
theorem IsFellerKernelSemigroup.continuous_integral_boundedCylinder
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {G : ContinuousPath alpha → ℝ} (hG : ContinuousPath.IsBoundedCylinder G) :
    Continuous fun x ↦ ∫ omega, G omega ∂(continuousProcess P hP x) := by
  obtain ⟨I, g, hg⟩ := hG
  simp only [hg]
  exact hFeller.continuous_integral_finsetEvaluation_continuousProcess P hP hK I g

/-- **Weak continuity of the path law in the starting point.**  For a conservative Feller
semigroup on a proper metric state space satisfying the intrinsic Kolmogorov moment criterion, the
expectation of *every* bounded continuous functional of the path is a continuous function of the
starting point.

This extends the cylinder-expectation continuity of
`continuous_integral_finsetEvaluation_continuousProcess` to all of path space.  The proof is the
direct one: tightness over a compact neighbourhood of the reference point produces a compact set
of paths carrying all but a prescribed mass, Stone--Weierstrass replaces the functional by a
bounded cylinder functional on that compact set, and the cylinder case is already known.  No
compactness theorem for measures is used. -/
theorem IsFellerKernelSemigroup.continuous_integral_continuousProcess
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) (F : ContinuousPath alpha →ᵇ ℝ) :
    Continuous fun x ↦ ∫ omega, F omega ∂(continuousProcess P hP x) := by
  have hKreg := KolmogorovRegular.of_hasKolmogorovMoments P hP hmom
  refine continuous_iff_continuousAt.mpr fun x0 ↦ ?_
  refine tendsto_integral_of_tight_approximation (fun x ↦ continuousProcess P hP x)
    (continuousProcess P hP x0) {G | ContinuousPath.IsBoundedCylinder G} F ?_ ?_ ?_
  · intro eta heta
    obtain ⟨K0, hK0, hneighbourhood⟩ := exists_compact_mem_nhds x0
    obtain ⟨K, hK, hmass⟩ :=
      IsConservative.exists_isCompact_measure_compl_le P hP hmom hK0
        (eps := ENNReal.ofReal eta) (ENNReal.ofReal_pos.mpr heta)
    exact ⟨K, hK, Filter.Eventually.mono hneighbourhood fun x hx ↦ hmass x hx,
      hmass x0 (mem_of_mem_nhds hneighbourhood)⟩
  · intro K hK eps heps
    exact ContinuousPath.exists_boundedCylinder_approx F hK heps
  · intro G hG
    exact (IsFellerKernelSemigroup.continuous_integral_boundedCylinder
      P hP hFeller hKreg hG).continuousAt

/-- The law of the continuous-path process, read as a probability measure on path space. -/
def IsConservative.pathLaw (x : alpha) : ProbabilityMeasure (ContinuousPath alpha) :=
  ⟨continuousProcess P hP x, inferInstance⟩

omit [ProperSpace alpha] in
@[simp]
theorem IsConservative.pathLaw_toMeasure (x : alpha) :
    ((IsConservative.pathLaw P hP x : ProbabilityMeasure (ContinuousPath alpha)) :
        Measure (ContinuousPath alpha)) = continuousProcess P hP x :=
  rfl

/-- **The path law is weakly continuous in the starting point.**  Read on the space of
probability measures on path space with its topology of convergence in distribution, the map
`x ↦ pathLaw P hP x` is continuous. -/
theorem IsFellerKernelSemigroup.continuous_pathLaw
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) :
    Continuous (IsConservative.pathLaw P hP) := by
  refine ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr fun F ↦ ?_
  exact IsFellerKernelSemigroup.continuous_integral_continuousProcess P hP hFeller hmom F

end

end SubMarkovKernelSemigroup

end MarkovProcess

end PortComputability
