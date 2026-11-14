/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxGeneralDomainCube
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValue

/-!
# ExitMeanValueCubeSetAt

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Dirichlet resolvent of a bounded part domain, read on a translated triadic cube

The exit decomposition of a resolvent datum needs the Dirichlet resolvent of the domain the
process is killed on.  On the centred exhaustion cubes that object is
`analyticCubeResolvent`, whose index is the exhaustion step; the localized Dirichlet problems
of the field are posed instead on `cubeSetAt y n`, the open cube of side `3 ^ n` centred at `y`,
which is not an exhaustion cube.

This file supplies the Dirichlet resolvent of an arbitrary bounded part domain and specializes it
to a translated triadic cube.

* `partC0Resolvent` is the continuous representative of the Dirichlet resolvent of a bounded
  measurable datum on a bounded convex open set, extended by zero.  It is the domain-generic
  form of `analyticCubeResolvent`: the underlying analytic object,
  `continuousCoeffBoundedResolvent`, already takes an arbitrary such set, and the ellipticity
  certificate is the one `partEllipticity` supplies for it.
* `eq_partC0Resolvent_of_isRepresentative` names it: a continuous function agreeing almost
  everywhere on the domain with the shifted part solution is that resolvent there.
* `cubeSetAtC0Resolvent` is that resolvent on `cubeSetAt y n`, with `cubeSetAtC0BarrierData`
  packaging the barrier data of the cube problem.  The triadic cube is an axis cube, so the
  caller obligation of the whole-space barrier data is discharged there.

Everything here is analytic: no process, and no hypothesis about one, appears.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Section5.Support
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ## The datum of a translated triadic cube -/

/-- The restriction to a translated triadic cube of a continuous datum vanishing at infinity,
extended by zero. -/
def cubeSetAtC0Datum (y : Vec d) (n : ℤ) (g : C₀(Vec d, ℝ)) : Vec d → ℝ :=
  (cubeSetAt y n).indicator fun z => g z

theorem measurable_cubeSetAtC0Datum (y : Vec d) (n : ℤ) (g : C₀(Vec d, ℝ)) :
    Measurable (cubeSetAtC0Datum y n g) :=
  g.continuous.measurable.indicator (measurableSet_cubeSetAt y n)

theorem abs_cubeSetAtC0Datum_le (y : Vec d) (n : ℤ) (g : C₀(Vec d, ℝ)) (z : Vec d) :
    |cubeSetAtC0Datum y n g z| ≤ ‖g‖ := by
  rw [cubeSetAtC0Datum]
  by_cases hz : z ∈ cubeSetAt y n
  · rw [Set.indicator_of_mem hz, ← Real.norm_eq_abs,
      ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF z
  · rw [Set.indicator_of_notMem hz, abs_zero]
    exact norm_nonneg g

theorem cubeSetAtC0Datum_nonneg (y : Vec d) (n : ℤ) {g : C₀(Vec d, ℝ)}
    (hg0 : ∀ z, 0 ≤ g z) (z : Vec d) : 0 ≤ cubeSetAtC0Datum y n g z :=
  Set.indicator_nonneg (fun w _ => hg0 w) z

theorem cubeSetAtC0Datum_of_mem {y : Vec d} {n : ℤ} (g : C₀(Vec d, ℝ)) {z : Vec d}
    (hz : z ∈ cubeSetAt y n) : cubeSetAtC0Datum y n g z = g z :=
  Set.indicator_of_mem hz _

theorem cubeSetAtC0Datum_ae_indicator (y : Vec d) (n : ℤ) (g : C₀(Vec d, ℝ)) :
    cubeSetAtC0Datum y n g =ᵐ[volume]
      (cubeSetAt y n).indicator (cubeSetAtC0Datum y n g) := by
  refine Filter.Eventually.of_forall fun z => ?_
  rw [cubeSetAtC0Datum, Set.indicator_indicator, Set.inter_self]

variable [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The Dirichlet resolvent of a bounded part domain -/

/-- **The Dirichlet resolvent of a bounded part domain.**  The continuous representative
supplied by freezing the skew part, extended by zero off the domain.  This is
`analyticCubeResolvent` with the exhaustion index replaced by the domain itself. -/
def partC0Resolvent {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) : Vec d → ℝ :=
  V.indicator (continuousCoeffBoundedResolvent A.a hV A.hnu A.hnu
    (partEllipticity A hV) A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
    (hf.comp measurable_subtype_coe) (fun z => hfD z))

theorem partC0Resolvent_of_mem {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) {x : Vec d} (hx : x ∈ V) :
    A.partC0Resolvent hV mu f hf hfD x =
      continuousCoeffBoundedResolvent A.a hV A.hnu A.hnu (partEllipticity A hV) A.hsymm
        (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
        (hf.comp measurable_subtype_coe) (fun z => hfD z) x :=
  Set.indicator_of_mem hx _

theorem partC0Resolvent_of_notMem {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) {x : Vec d} (hx : x ∉ V) :
    A.partC0Resolvent hV mu f hf hfD x = 0 :=
  Set.indicator_of_notMem hx _

theorem continuousOn_partC0Resolvent {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) :
    ContinuousOn (A.partC0Resolvent hV mu f hf hfD) V := by
  refine ContinuousOn.congr (continuousOn_continuousCoeffBoundedResolvent A.a hV A.hnu
    A.hnu (partEllipticity A hV) A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd
    mu (hf.comp measurable_subtype_coe) (fun z => hfD z)) fun x hx => ?_
  exact A.partC0Resolvent_of_mem hV mu f hf hfD hx

theorem partC0Resolvent_ae {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) :
    A.partC0Resolvent hV mu f hf hfD =ᵐ[volumeMeasureOn V]
      alphaShiftedResolvent A.a mu.property A.hnu (partEllipticity A hV)
        (partDatumL2 hV hf hfD) := by
  filter_upwards [continuousCoeffBoundedResolvent_ae A.a hV A.hnu A.hnu
      (partEllipticity A hV) A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
      (hf.comp measurable_subtype_coe) (fun z => hfD z),
    self_mem_ae_restrict hV.isOpen.measurableSet] with x hx hxV
  rw [A.partC0Resolvent_of_mem hV mu f hf hfD hxV, hx]
  rfl

/-- **The Dirichlet resolvent of a part domain is nonnegative on a nonnegative datum.** -/
theorem partC0Resolvent_nonneg {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    0 ≤ A.partC0Resolvent hV mu f hf hfD x := by
  by_cases hx : x ∈ V
  · refine le_of_ae_le_of_continuousOn hV.isOpen continuousOn_const
      (A.continuousOn_partC0Resolvent hV mu f hf hfD) ?_ x hx
    filter_upwards [A.partC0Resolvent_ae hV mu f hf hfD,
      alphaShiftedResolvent_nonneg_ae A.a hV mu.property A.hnu (partEllipticity A hV)
        (partDatumL2 hV hf hfD)
        (ae_nonneg_boundedMeasurableToScalarL2 hV hf hf0 hfD)] with z h1 h2
    rw [h1]
    exact h2
  · rw [A.partC0Resolvent_of_notMem hV mu f hf hfD hx]

/-- **The Dirichlet resolvent of a part domain is named by continuity and its almost-everywhere
value.**  A continuous function agreeing almost everywhere on the domain with the shifted part
solution equals the resolvent at every point of the domain. -/
theorem eq_partC0Resolvent_of_isRepresentative {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (lam : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) {u : Vec d → ℝ}
    (hucont : Continuous u)
    (hurep : u =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
      (alphaShiftedSolution A.a lam.property A.hnu (partEllipticity A hV)
        (partDatumL2 hV hf hfD)))
    {x : Vec d} (hx : x ∈ V) :
    u x = A.partC0Resolvent hV lam f hf hfD x := by
  rw [A.partC0Resolvent_of_mem hV lam f hf hfD hx]
  exact continuousCoeffBoundedResolvent_eq_of_continuousOn_of_ae_eq A.a hV A.hnu A.hnu
    (partEllipticity A hV) A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd lam
    (hf.comp measurable_subtype_coe) (fun z => hfD z) hucont.continuousOn hurep hx

/-! ## The Dirichlet resolvent of a translated triadic cube -/

/-- **The barrier data of the cube problem for a nonnegative continuous datum on a translated
triadic cube.** -/
def cubeSetAtC0BarrierData (y : Vec d) (n : ℤ) (lam : PositiveShift) (g : C₀(Vec d, ℝ))
    (hg0 : ∀ z, 0 ≤ g z) : WholeSpaceBarrierData A :=
  eqAxisCubeBarrierData A (isOpenBoundedConvexDomain_cubeSetAt y n)
    (fun i => y i - (3 : ℝ) ^ n / 2) (zpow_pos (by norm_num) n)
    (cubeSetAt_eq_axisCube y n) lam (measurable_cubeSetAtC0Datum y n g)
    (cubeSetAtC0Datum_nonneg y n hg0) (abs_cubeSetAtC0Datum_le y n g)
    (cubeSetAtC0Datum_ae_indicator y n g)

@[simp] theorem cubeSetAtC0BarrierData_V (y : Vec d) (n : ℤ) (lam : PositiveShift)
    (g : C₀(Vec d, ℝ)) (hg0 : ∀ z, 0 ≤ g z) :
    (A.cubeSetAtC0BarrierData y n lam g hg0).V = cubeSetAt y n := rfl

@[simp] theorem cubeSetAtC0BarrierData_f (y : Vec d) (n : ℤ) (lam : PositiveShift)
    (g : C₀(Vec d, ℝ)) (hg0 : ∀ z, 0 ≤ g z) :
    (A.cubeSetAtC0BarrierData y n lam g hg0).f = cubeSetAtC0Datum y n g := rfl

@[simp] theorem cubeSetAtC0BarrierData_lam (y : Vec d) (n : ℤ) (lam : PositiveShift)
    (g : C₀(Vec d, ℝ)) (hg0 : ∀ z, 0 ≤ g z) :
    (A.cubeSetAtC0BarrierData y n lam g hg0).lam = lam := rfl

/-- **The Dirichlet resolvent of a continuous datum on a translated triadic cube**, as a
function of the shift; the value at a non-positive shift is zero. -/
def cubeSetAtC0Resolvent (y : Vec d) (n : ℤ) (g : C₀(Vec d, ℝ)) (lam : ℝ) :
    Vec d → ℝ :=
  if h : 0 < lam then
    A.partC0Resolvent (isOpenBoundedConvexDomain_cubeSetAt y n) ⟨lam, h⟩
      (cubeSetAtC0Datum y n g) (measurable_cubeSetAtC0Datum y n g)
      (abs_cubeSetAtC0Datum_le y n g)
  else 0

theorem cubeSetAtC0Resolvent_of_pos (y : Vec d) (n : ℤ) (g : C₀(Vec d, ℝ)) {lam : ℝ}
    (hlam : 0 < lam) (x : Vec d) :
    A.cubeSetAtC0Resolvent y n g lam x =
      A.partC0Resolvent (isOpenBoundedConvexDomain_cubeSetAt y n) ⟨lam, hlam⟩
        (cubeSetAtC0Datum y n g) (measurable_cubeSetAtC0Datum y n g)
        (abs_cubeSetAtC0Datum_le y n g) x := by
  rw [cubeSetAtC0Resolvent, dite_eq_left hlam]

theorem cubeSetAtC0Resolvent_nonneg (y : Vec d) (n : ℤ) {g : C₀(Vec d, ℝ)}
    (hg0 : ∀ z, 0 ≤ g z) (lam : ℝ) (x : Vec d) :
    0 ≤ A.cubeSetAtC0Resolvent y n g lam x := by
  rw [cubeSetAtC0Resolvent]
  split_ifs with h
  · exact A.partC0Resolvent_nonneg _ _ _ _ (cubeSetAtC0Datum_nonneg y n hg0) _ x
  · exact le_rfl

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
