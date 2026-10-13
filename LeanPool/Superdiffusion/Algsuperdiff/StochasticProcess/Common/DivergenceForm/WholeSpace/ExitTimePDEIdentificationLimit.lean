/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationEverywhere
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDEIdentificationL2

/-!
# ExitTimePDEIdentificationLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The exit-time function of an exhaustion cube is the torsion function

The limit of the Dirichlet resolvents of the constant datum as the shift
decreases to zero is identified here, at every point of the cube and not only
almost everywhere, with a representative of the torsion function that is
continuous there.

The representative is produced from the torsion function itself.  The torsion
function is bounded, so truncating it at its bound and adding the constant
datum gives a bounded measurable datum whose Dirichlet resolvent at shift one
is, as an `L²` class, the torsion function again; the analytic layer supplies
a representative of that resolvent which is continuous on the cube
(`cubeTorsionRepresentative`).

With both families continuous on the cube, the almost-everywhere sandwich of
the previous file holds at every point of the cube: the Dirichlet resolvent of
the constant datum at the shift `lam` lies between the continuous
representative minus `lam` times the square of the uniform bound and that
representative itself.  Letting the shift decrease to zero along `1 / (n + 1)`
squeezes the supremum, so the limit is exactly the value of the representative.

Two consequences are recorded.  The limit is bounded on the whole
compactification by the uniform bound of the torsion function, hence finite;
and almost everywhere on the cube it is the extended-real image of the chosen
torsion function.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The shift one. -/
def unitShift : PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩

@[simp] theorem unitShift_coe : ((unitShift : PositiveShift) : ℝ) = 1 := rfl

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- The torsion function truncated at its uniform bound and restricted to the
cube. -/
def cubeTorsionTrunc (v : ℕ) : Vec d → ℝ :=
  (wholeSpaceCube d v).indicator fun y =>
    max (-(A.cubeTorsionBound v))
      (min (A.cubeTorsionBound v)
        ((A.cubeTorsionFunction v).toH1Function.toFun y))

theorem measurable_cubeTorsionTrunc (v : ℕ) : Measurable (A.cubeTorsionTrunc v) :=
  (measurable_const.max (measurable_const.min (A.measurable_cubeTorsionFunction v))).indicator
    (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen.measurableSet

theorem abs_cubeTorsionTrunc_le (v : ℕ) (y : Vec d) :
    |A.cubeTorsionTrunc v y| ≤ A.cubeTorsionBound v := by
  have hM : 0 ≤ A.cubeTorsionBound v := A.cubeTorsionBound_nonneg v
  rw [cubeTorsionTrunc]
  by_cases hy : y ∈ wholeSpaceCube d v
  · rw [Set.indicator_of_mem hy]
    refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith only [hM]) (min_le_left _ _)⟩
  · rw [Set.indicator_of_notMem hy, abs_zero]
    exact hM

theorem cubeTorsionTrunc_ae (v : ℕ) :
    ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d v),
      A.cubeTorsionTrunc v y = (A.cubeTorsionFunction v).toH1Function.toFun y := by
  filter_upwards [A.abs_cubeTorsionFunction_le v,
    ae_restrict_mem
      (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen.measurableSet]
    with y habs hmem
  rw [cubeTorsionTrunc, Set.indicator_of_mem hmem,
    min_eq_right (abs_le.mp habs).2, max_eq_right (abs_le.mp habs).1]

/-- The datum of the torsion function read as a shifted problem at shift one. -/
def cubeTorsionDatum (v : ℕ) : Vec d → ℝ :=
  fun y => cubeOneDatum d v y + A.cubeTorsionTrunc v y

@[simp] theorem cubeTorsionDatum_apply (v : ℕ) (y : Vec d) :
    A.cubeTorsionDatum v y = cubeOneDatum d v y + A.cubeTorsionTrunc v y := rfl

theorem measurable_cubeTorsionDatum (v : ℕ) : Measurable (A.cubeTorsionDatum v) :=
  (measurable_cubeOneDatum d v).add (A.measurable_cubeTorsionTrunc v)

theorem abs_cubeTorsionDatum_le (v : ℕ) (y : Vec d) :
    |A.cubeTorsionDatum v y| ≤ 1 + A.cubeTorsionBound v :=
  (abs_add_le _ _).trans (add_le_add (abs_cubeOneDatum_le d v y)
    (A.abs_cubeTorsionTrunc_le v y))

/-- The continuous representative on the cube of the torsion function: the
Dirichlet resolvent at shift one of the datum the torsion function solves for
at that shift. -/
def cubeTorsionRepresentative (v : ℕ) : Vec d → ℝ :=
  A.analyticCubeResolvent unitShift (A.cubeTorsionDatum v)
    (A.measurable_cubeTorsionDatum v) (A.abs_cubeTorsionDatum_le v) v

theorem continuousOn_cubeTorsionRepresentative (v : ℕ) :
    ContinuousOn (A.cubeTorsionRepresentative v) (wholeSpaceCube d v) :=
  A.continuousOn_analyticCubeResolvent unitShift _ _ v

theorem cubeTorsionRepresentative_of_notMem (v : ℕ) {x : Vec d}
    (hx : x ∉ wholeSpaceCube d v) : A.cubeTorsionRepresentative v x = 0 := by
  rw [cubeTorsionRepresentative, analyticCubeResolvent, dite_eq_right hx]

/-- The continuous representative agrees almost everywhere on the cube with the
`L²` class of the torsion function. -/
theorem cubeTorsionRepresentative_ae (v : ℕ) :
    A.cubeTorsionRepresentative v =ᵐ[volumeMeasureOn (wholeSpaceCube d v)]
      fun x => A.cubeTorsionL2 v x := by
  have hU : IsOpenBoundedConvexDomain (wholeSpaceCube d v) :=
    isOpenBoundedConvexDomain_wholeSpaceCube d v
  have hdatum : boundedMeasurableToScalarL2 hU
      ((A.measurable_cubeTorsionDatum v).comp measurable_subtype_coe)
      (fun y => A.abs_cubeTorsionDatum_le v y) =
      cubeOneL2 d v + (unitShift : ℝ) • A.cubeTorsionL2 v := by
    apply MeasureTheory.Lp.ext
    filter_upwards [boundedMeasurableToScalarL2_coeFn hU
        ((A.measurable_cubeTorsionDatum v).comp measurable_subtype_coe)
        (fun y => A.abs_cubeTorsionDatum_le v y),
      MeasureTheory.Lp.coeFn_add (cubeOneL2 d v)
        ((unitShift : ℝ) • A.cubeTorsionL2 v),
      MeasureTheory.Lp.coeFn_smul (unitShift : ℝ) (A.cubeTorsionL2 v),
      cubeOneL2_ae d v, A.cubeTorsionL2_ae v, A.cubeTorsionTrunc_ae v,
      ae_restrict_mem hU.isOpen.measurableSet] with x hx hadd hsmul hone htors
      htrunc hmem
    rw [hx, domainExtension_of_mem hmem, hadd, Pi.add_apply, hsmul,
      Pi.smul_apply, smul_eq_mul, hone, htors, unitShift_coe, one_mul]
    show A.cubeTorsionDatum v x = _
    rw [cubeTorsionDatum_apply, cubeOneDatum_of_mem hmem, htrunc]
  have h1 := A.analyticCubeResolvent_ae unitShift
    (A.measurable_cubeTorsionDatum v) (A.abs_cubeTorsionDatum_le v) v
  rw [hdatum, ← A.cubeTorsionL2_eq_alphaShiftedResolvent v unitShift] at h1
  exact h1

theorem analyticCubeResolvent_cubeOneDatum_ae (v : ℕ) (lam : PositiveShift) :
    A.analyticCubeResolvent lam (cubeOneDatum d v) (measurable_cubeOneDatum d v)
        (abs_cubeOneDatum_le d v) v =ᵐ[volumeMeasureOn (wholeSpaceCube d v)]
      fun x => alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
        (cubeOneL2 d v) x :=
  A.analyticCubeResolvent_ae lam (measurable_cubeOneDatum d v)
    (abs_cubeOneDatum_le d v) v

theorem analyticCubeResolvent_of_notMem (lam : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) {x : Vec d}
    (hx : x ∉ wholeSpaceCube d m) : A.analyticCubeResolvent lam f hf hfD m x = 0 := by
  rw [analyticCubeResolvent, dite_eq_right hx]

/-- **The Dirichlet resolvent of the constant datum is below the continuous
representative of the torsion function at every point of the cube.** -/
theorem analyticCubeResolvent_cubeOneDatum_le_cubeTorsionRepresentative (v : ℕ)
    (lam : PositiveShift) {x : Vec d} (hx : x ∈ wholeSpaceCube d v) :
    A.analyticCubeResolvent lam (cubeOneDatum d v) (measurable_cubeOneDatum d v)
        (abs_cubeOneDatum_le d v) v x ≤ A.cubeTorsionRepresentative v x := by
  refine le_of_ae_le_of_continuousOn
    (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
    (A.continuousOn_analyticCubeResolvent lam _ _ v)
    (A.continuousOn_cubeTorsionRepresentative v) ?_ x hx
  filter_upwards [A.analyticCubeResolvent_cubeOneDatum_ae v lam,
    A.cubeTorsionRepresentative_ae v,
    A.alphaShiftedResolvent_cubeOneL2_le_cubeTorsionL2 v lam] with y h1 h2 h3
  rw [h1, h2]
  exact h3

/-- **The continuous representative of the torsion function exceeds the
Dirichlet resolvent of the constant datum by at most the shift times the
square of the uniform bound.** -/
theorem cubeTorsionRepresentative_sub_analyticCubeResolvent_cubeOneDatum_le (v : ℕ)
    (lam : PositiveShift) {x : Vec d} (hx : x ∈ wholeSpaceCube d v) :
    A.cubeTorsionRepresentative v x -
        A.analyticCubeResolvent lam (cubeOneDatum d v) (measurable_cubeOneDatum d v)
          (abs_cubeOneDatum_le d v) v x ≤
      (lam : ℝ) * (A.cubeTorsionBound v * A.cubeTorsionBound v) := by
  refine le_of_ae_le_of_continuousOn
    (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
    ((A.continuousOn_cubeTorsionRepresentative v).sub
      (A.continuousOn_analyticCubeResolvent lam _ _ v))
    continuousOn_const ?_ x hx
  filter_upwards [A.analyticCubeResolvent_cubeOneDatum_ae v lam,
    A.cubeTorsionRepresentative_ae v,
    A.cubeTorsionL2_sub_alphaShiftedResolvent_cubeOneL2_le v lam] with y h1 h2 h3
  simp only [Pi.sub_apply, h1, h2]
  exact h3

theorem cubeTorsionRepresentative_le (v : ℕ) (x : Vec d) :
    A.cubeTorsionRepresentative v x ≤ A.cubeTorsionBound v := by
  by_cases hx : x ∈ wholeSpaceCube d v
  · refine le_of_ae_le_of_continuousOn
      (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
      (A.continuousOn_cubeTorsionRepresentative v) continuousOn_const ?_ x hx
    filter_upwards [A.cubeTorsionRepresentative_ae v, A.cubeTorsionL2_le v]
      with y h1 h2
    rw [h1]
    exact h2
  · rw [A.cubeTorsionRepresentative_of_notMem v hx]
    exact A.cubeTorsionBound_nonneg v

end WholeSpaceAnalyticData

/-- A sequence squeezed between a value and that value minus a null sequence
has that value as the supremum of its nonnegative extended-real images. -/
theorem iSup_ofReal_eq_of_squeeze {g : ℕ → ℝ} {c e : ℝ}
    (hle : ∀ n, g n ≤ c) (hge : ∀ n : ℕ, c - g n ≤ ((n : ℝ) + 1)⁻¹ * e) :
    ⨆ n, ENNReal.ofReal (g n) = ENNReal.ofReal c := by
  have hzero : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * e) atTop (nhds 0) := by
    have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) := by
      simpa only [one_div] using
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hconst : Tendsto (fun _ : ℕ => e) atTop (nhds e) := tendsto_const_nhds
    simpa using h.mul hconst
  have hlower : Tendsto (fun n : ℕ => c - ((n : ℝ) + 1)⁻¹ * e) atTop (nhds c) := by
    have hconst : Tendsto (fun _ : ℕ => c) atTop (nhds c) := tendsto_const_nhds
    simpa using hconst.sub hzero
  have htend : Tendsto g atTop (nhds c) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => by linarith only [hge n]) hle
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (hle n)) ?_
  exact le_of_tendsto (ENNReal.tendsto_ofReal htend)
    (Filter.Eventually.of_forall fun n =>
      le_iSup (fun n => ENNReal.ofReal (g n)) n)

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- **The limit of the Dirichlet resolvents of the constant datum is the
continuous representative of the torsion function at every point.** -/
theorem cubeExitFunction_coe_eq (v : ℕ) (x : Vec d) :
    A.cubeExitFunction v (x : OnePoint (Vec d)) =
      ENNReal.ofReal (A.cubeTorsionRepresentative v x) := by
  rw [A.cubeExitFunction_coe v x]
  by_cases hx : x ∈ wholeSpaceCube d v
  · exact iSup_ofReal_eq_of_squeeze
      (e := A.cubeTorsionBound v * A.cubeTorsionBound v)
      (fun n => A.analyticCubeResolvent_cubeOneDatum_le_cubeTorsionRepresentative
        v _ hx)
      (fun n => A.cubeTorsionRepresentative_sub_analyticCubeResolvent_cubeOneDatum_le
        v _ hx)
  · rw [A.cubeTorsionRepresentative_of_notMem v hx, ENNReal.ofReal_zero]
    refine iSup_eq_bot.mpr fun n => ?_
    rw [A.analyticCubeResolvent_of_notMem _ _ _ v hx, ENNReal.ofReal_zero]
    rfl

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
