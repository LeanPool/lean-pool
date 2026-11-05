/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.BoundedMeasurableAlgebra
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Comparison
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PartDomainSubsolution
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ContinuousCoeffBoundedResolvent
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Cubes
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.EllipticityWitness
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.ContinuousCoeffResolvent

/-!
# Minimal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The analytic minimal resolvent on the cubic exhaustion

This file transports the bounded-domain analytic Dirichlet resolvents to
`Vec d` by zero extension and takes their pointwise supremum.  All coefficient
hypotheses are imposed on the whole space and restricted to the individual
cubes in the definitions below.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open MarkovProcess.Semigroup
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The coefficient and regularity data used by the whole-space cubic
exhaustion.  The field has the form `a = nu I + k`, where `nu > 0` and `k` is
continuous and skew with arbitrary size; no whole-space small-contrast
hypothesis is included. -/
structure WholeSpaceAnalyticData (d : ℕ) [NeZero d] where
  /-- The measurable whole-space coefficient field with fixed symmetric part. -/
  a : CoeffField d
  /-- The positive molecular diffusivity determining the symmetric coefficient part. -/
  nu : ℝ
  hnu : 0 < nu
  hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d)
  hskewContinuous : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) Set.univ
  hd : 2 ≤ d
  hameas : Measurable a

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- Continuity of the arbitrary-size skew part restricted to an exhaustion
cube. -/
theorem skewContinuousOnCube (m : ℕ) :
    ContinuousOn (fun y ↦ A.a y - A.nu • (1 : Mat d))
      (wholeSpaceCube d m) :=
  A.hskewContinuous.mono (Set.subset_univ _)

/-- Continuity of the skew part on the closed box underlying an exhaustion
cube.  Boundary regularity uses this carrier rather than the open cube. -/
theorem skewContinuousOnCubeClosure (m : ℕ) :
    ContinuousOn (fun y ↦ A.a y - A.nu • (1 : Mat d))
      {x | Algsuperdiff.StochasticProcess.Common.Regularity.MemAxisCubeClosure
        (fun _ ↦ -((3 : ℝ) ^ m))
        (2 * (3 : ℝ) ^ m) x} :=
  A.hskewContinuous.mono (Set.subset_univ _)

/-- The compactness-supplied upper ellipticity constant on the `m`th cube. -/
def cubeEllipticityUpper (m : ℕ) : ℝ :=
  Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.axisCubeEllipticUpper
    (fun _ ↦ -((3 : ℝ) ^ m)) (2 * (3 : ℝ) ^ m) A.hnu A.hsymm
    (A.skewContinuousOnCubeClosure m)

/-- The `m`th cube is elliptic with lower constant `nu`; continuity on its
compact closure supplies the upper constant. -/
theorem cubeEllipticity (m : ℕ) :
    IsEllipticFieldOn A.nu (A.cubeEllipticityUpper m)
      (wholeSpaceCube d m) A.a :=
  Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.isEllipticFieldOn_axisCubeEllipticUpper
    (fun _ ↦ -((3 : ℝ) ^ m)) (2 * (3 : ℝ) ^ m) A.hnu A.hsymm
    (A.skewContinuousOnCubeClosure m)

/-- The analytic Dirichlet resolvent on the `m`th cube, extended by zero to
the whole space. -/
def analyticCubeResolvent (mu : PositiveShift) (f : Vec d → ℝ)
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (m : ℕ) (x : Vec d) : ℝ := by
  classical
  exact if hx : x ∈ wholeSpaceCube d m then
      continuousCoeffBoundedResolvent A.a
        (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y => hfD y) x
    else 0

/-- The nonnegative extended-real form of a local analytic resolvent. -/
def analyticCubeResolventENN (mu : PositiveShift) (f : Vec d → ℝ)
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (m : ℕ) (x : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (A.analyticCubeResolvent mu f hf hfD m x)

/-- The analytic minimal resolvent of a nonnegative bounded measurable
observable is the pointwise supremum of its zero-extended cube resolvents. -/
def analyticMinimalResolvent (mu : PositiveShift) (f : Vec d → ℝ)
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (x : Vec d) : ℝ≥0∞ :=
  ⨆ m, A.analyticCubeResolventENN mu f hf hfD m x

/-- The nonnegative part of a real observable. -/
def analyticPositivePart (f : Vec d → ℝ) (x : Vec d) : ℝ := max (f x) 0

omit [NeZero d] in
theorem measurable_analyticPositivePart {f : Vec d → ℝ} (hf : Measurable f) :
    Measurable (analyticPositivePart f) :=
  hf.max measurable_const

omit [NeZero d] in
theorem abs_analyticPositivePart_le {f : Vec d → ℝ} {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    |analyticPositivePart f x| ≤ D := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hpart : 0 ≤ analyticPositivePart f x := le_max_right _ _
  rw [abs_of_nonneg hpart, analyticPositivePart]
  exact max_le ((le_abs_self (f x)).trans (hfD x)) hD

/-- The real form of the analytic minimal resolvent, defined by positive and
negative parts. -/
def analyticMinimalResolventReal (mu : PositiveShift) (f : Vec d → ℝ)
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (x : Vec d) : ℝ :=
  (A.analyticMinimalResolvent mu (analyticPositivePart f)
      (measurable_analyticPositivePart hf)
      (abs_analyticPositivePart_le hfD) x).toReal -
    (A.analyticMinimalResolvent mu (analyticPositivePart fun y => -f y)
      (measurable_analyticPositivePart hf.neg)
      (abs_analyticPositivePart_le (D := D) (fun y => by simpa using hfD y)) x).toReal

omit [NeZero d] in
private theorem restrictedDatum_nonneg_ae {f : Vec d → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d m),
      0 ≤ boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (hf.comp measurable_subtype_coe) (fun y => hfD y) x := by
  filter_upwards [boundedMeasurableToScalarL2_coeFn
      (isOpenBoundedConvexDomain_wholeSpaceCube d m)
      (hf.comp measurable_subtype_coe) (fun y => hfD y),
    ae_restrict_mem
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen.measurableSet] with x hx hxmem
  rw [hx, domainExtension_of_mem hxmem]
  exact hf0 x

omit [NeZero d] in
theorem restrict_boundedMeasurableToScalarL2_succ
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    restrictScalarL2ToPart (V := wholeSpaceCube d m)
        (isOpenBoundedConvexDomain_wholeSpaceCube d (m + 1)).isOpen.measurableSet
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d (m + 1))
          (hf.comp measurable_subtype_coe) (fun y => hfD y)) =
      boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (hf.comp measurable_subtype_coe) (fun y => hfD y) := by
  let hV := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d (m + 1)
  let fU : ScalarL2 (wholeSpaceCube d (m + 1)) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
      (fun y => hfD y)
  let fV : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe)
      (fun y => hfD y)
  change restrictScalarL2ToPart hU.isOpen.measurableSet fU = fV
  refine (Lp.ext_iff).2 ?_
  have hrestrict := restrictScalarL2ToPart_coeFn hV.isOpen.measurableSet
    hU.isOpen.measurableSet (wholeSpaceCube_subset_succ d m) fU
  have hlarge := boundedMeasurableToScalarL2_coeFn hU
    (hf.comp measurable_subtype_coe) (fun y => hfD y)
  have hlargeV := ae_restrict_of_ae_restrict_of_subset
    (wholeSpaceCube_subset_succ d m) hlarge
  have hsmall := boundedMeasurableToScalarL2_coeFn hV
    (hf.comp measurable_subtype_coe) (fun y => hfD y)
  have hmem : ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d m),
      x ∈ wholeSpaceCube d m := self_mem_ae_restrict hV.isOpen.measurableSet
  filter_upwards [hrestrict, hlargeV, hsmall, hmem]
      with x hrestrict hlarge hsmall hx
  rw [hrestrict, hlarge, hsmall]
  have hxU := wholeSpaceCube_subset_succ d m hx
  rw [domainExtension_of_mem (U := wholeSpaceCube d (m + 1)) hxU,
    domainExtension_of_mem (U := wholeSpaceCube d m) hx]
  rfl

/-- A local analytic cube resolvent is pointwise nonnegative on nonnegative
data. -/
theorem analyticCubeResolvent_nonneg (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    0 ≤ A.analyticCubeResolvent mu f hf hfD m x := by
  rw [analyticCubeResolvent]
  split_ifs with hx
  · refine le_of_ae_le_of_continuousOn
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen continuousOn_const
      (continuousOn_continuousCoeffBoundedResolvent A.a
        (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y => hfD y)) ?_ x hx
    filter_upwards [continuousCoeffBoundedResolvent_ae A.a
        (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y => hfD y),
      alphaShiftedResolvent_nonneg_ae A.a
        (isOpenBoundedConvexDomain_wholeSpaceCube d m) mu.property
        A.hnu
        (A.cubeEllipticity m)
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d m)
          (hf.comp measurable_subtype_coe) (fun y => hfD y))
        (restrictedDatum_nonneg_ae hf hf0 hfD m)] with y hy hnonneg
    rw [hy]
    exact hnonneg
  · exact le_rfl

/-- The zero-extended analytic Dirichlet resolvents increase with the cubic
exhaustion on nonnegative data. -/
theorem analyticCubeResolvent_le_succ (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    A.analyticCubeResolvent mu f hf hfD m x ≤
      A.analyticCubeResolvent mu f hf hfD (m + 1) x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · have hx' : x ∈ wholeSpaceCube d (m + 1) :=
      wholeSpaceCube_subset_succ d m hx
    rw [analyticCubeResolvent, dite_eq_left hx, analyticCubeResolvent, dite_eq_left hx']
    let hV := isOpenBoundedConvexDomain_wholeSpaceCube d m
    let hU := isOpenBoundedConvexDomain_wholeSpaceCube d (m + 1)
    let fU : ScalarL2 (wholeSpaceCube d (m + 1)) :=
      boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
        (fun y => hfD y)
    have hfU : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d (m + 1)), 0 ≤ fU y :=
      restrictedDatum_nonneg_ae hf hf0 hfD (m + 1)
    have hrem := partDomainRemainder_nonneg_ae A.a hV hU
      (wholeSpaceCube_subset_succ d m) mu.property A.hnu
      (A.cubeEllipticity (m + 1)) fU hfU
    have hrestrict := restrict_boundedMeasurableToScalarL2_succ hf hfD m
    have hrestrict' : restrictScalarL2ToPart hU.isOpen.measurableSet fU =
        boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe)
          (fun y => hfD y) := by
      simpa only [fU, hU, hV] using hrestrict
    rw [hrestrict'] at hrem
    have hsolutionWitness :
        alphaShiftedSolution A.a mu.property A.hnu (A.cubeEllipticity m)
            (boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe)
              (fun y => hfD y)) =
          alphaShiftedSolution A.a mu.property A.hnu
            ((A.cubeEllipticity (m + 1)).mono hV.isOpen.measurableSet
              (wholeSpaceCube_subset_succ d m))
            (boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe)
              (fun y => hfD y)) :=
      alphaShiftedSolution_eq_of_ellipticityWitness A.a mu.property A.hnu A.hnu
        (A.cubeEllipticity m)
        ((A.cubeEllipticity (m + 1)).mono hV.isOpen.measurableSet
          (wholeSpaceCube_subset_succ d m)) _
    rw [← hsolutionWitness] at hrem
    have hremV := ae_restrict_of_ae_restrict_of_subset
      (wholeSpaceCube_subset_succ d m) hrem
    have hext := ae_restrict_of_ae_restrict_of_subset
      (wholeSpaceCube_subset_succ d m)
      (ZeroTraceSobolev.extendByZeroToPartSuperset_toL2 hV hU.isOpen
        (wholeSpaceCube_subset_succ d m)
        (alphaShiftedSolution A.a mu.property A.hnu
          (A.cubeEllipticity m)
          (boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe)
            (fun y => hfD y))))
    have hbig := ae_restrict_of_ae_restrict_of_subset
      (wholeSpaceCube_subset_succ d m)
      (continuousCoeffBoundedResolvent_ae A.a hU A.hnu A.hnu
        (A.cubeEllipticity (m + 1)) A.hsymm
        (A.skewContinuousOnCube (m + 1)) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y => hfD y))
    have hsmall := continuousCoeffBoundedResolvent_ae A.a hV A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd mu
      (hf.comp measurable_subtype_coe) (fun y => hfD y)
    have hsubU := Lp.coeFn_sub
      (ZeroTraceSobolev.toL2
        (alphaShiftedSolution A.a mu.property A.hnu
          (A.cubeEllipticity (m + 1)) fU))
      (ZeroTraceSobolev.toL2
        (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen
          (wholeSpaceCube_subset_succ d m)
          (alphaShiftedSolution A.a mu.property A.hnu
            (A.cubeEllipticity m)
            (boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe)
              (fun y => hfD y)))))
    have hsub := ae_restrict_of_ae_restrict_of_subset
      (wholeSpaceCube_subset_succ d m) hsubU
    refine le_of_ae_le_of_continuousOn hV.isOpen
      (continuousOn_continuousCoeffBoundedResolvent A.a hV A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y => hfD y))
      ((continuousOn_continuousCoeffBoundedResolvent A.a hU A.hnu
        A.hnu (A.cubeEllipticity (m + 1)) A.hsymm
        (A.skewContinuousOnCube (m + 1)) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y => hfD y)).mono
          (wholeSpaceCube_subset_succ d m)) ?_ x hx
    filter_upwards [hremV, hext, hbig, hsmall, hsub,
      ae_restrict_mem hV.isOpen.measurableSet]
        with y hnonneg hexty hbigy hsmally hsub hyV
    rw [map_sub, hsub, Pi.sub_apply, hexty, Set.indicator_of_mem hyV] at hnonneg
    rw [hbigy, hsmally]
    exact sub_nonneg.mp hnonneg
  · rw [analyticCubeResolvent, dite_eq_right hx]
    exact A.analyticCubeResolvent_nonneg mu hf hf0 hfD (m + 1) x

/-- At each point, the local analytic resolvents form a monotone sequence. -/
theorem monotone_analyticCubeResolvent (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    Monotone fun m => A.analyticCubeResolvent mu f hf hfD m x :=
  monotone_nat_of_le_succ fun m =>
    A.analyticCubeResolvent_le_succ mu hf hf0 hfD m x

/-- A zero-extended cube resolvent is measurable on the ambient space. -/
theorem measurable_analyticCubeResolvent (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    Measurable (A.analyticCubeResolvent mu f hf hfD m) := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let v : wholeSpaceCube d m → ℝ := fun y =>
    continuousCoeffBoundedResolvent A.a hU A.hnu A.hnu
      (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd mu
      (hf.comp measurable_subtype_coe)
      (fun z => hfD z) y
  have hv : Measurable v :=
    ((continuousOn_continuousCoeffBoundedResolvent A.a hU A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd mu
      (hf.comp measurable_subtype_coe) (fun z => hfD z)).domRestrict).measurable
  have heq : A.analyticCubeResolvent mu f hf hfD m = domainExtension v := by
    funext x
    by_cases hx : x ∈ wholeSpaceCube d m
    · rw [analyticCubeResolvent, dite_eq_left hx, domainExtension_of_mem hx]
    · rw [analyticCubeResolvent, dite_eq_right hx]
      have hnot : ¬ ∃ y : wholeSpaceCube d m, (y : Vec d) = x := by
        rintro ⟨y, rfl⟩
        exact hx y.2
      exact (Function.extend_apply' v (0 : Vec d → ℝ) x hnot).symm
  rw [heq]
  exact measurable_domainExtension hU.isOpen.measurableSet hv

/-- On its defining cube, the zero-extended analytic resolvent is continuous. -/
theorem continuousOn_analyticCubeResolvent (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    ContinuousOn (A.analyticCubeResolvent mu f hf hfD m)
      (wholeSpaceCube d m) := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  refine (continuousOn_continuousCoeffBoundedResolvent A.a hU A.hnu
    A.hnu (A.cubeEllipticity m) A.hsymm
    (A.skewContinuousOnCube m) A.hd mu
    (hf.comp measurable_subtype_coe) (fun y => hfD y)).congr ?_
  intro x hx
  rw [analyticCubeResolvent, dite_eq_left hx]

/-- On its defining cube, the analytic representative agrees almost
everywhere with the `L²` resolvent class. -/
theorem analyticCubeResolvent_ae (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    A.analyticCubeResolvent mu f hf hfD m =ᵐ[
        volumeMeasureOn (wholeSpaceCube d m)]
      alphaShiftedResolvent A.a mu.property A.hnu
        (A.cubeEllipticity m)
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d m)
          (hf.comp measurable_subtype_coe) (fun y => hfD y)) := by
  filter_upwards [continuousCoeffBoundedResolvent_ae A.a
      (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd mu
      (hf.comp measurable_subtype_coe) (fun y => hfD y),
    ae_restrict_mem
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen.measurableSet]
      with x hrep hx
  rw [analyticCubeResolvent, dite_eq_left hx, hrep]

/-- The analytic minimal resolvent is measurable as a pointwise supremum. -/
theorem measurable_analyticMinimalResolvent (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) :
    Measurable (A.analyticMinimalResolvent mu f hf hfD) := by
  exact Measurable.iSup fun m => ENNReal.measurable_ofReal.comp
    (A.measurable_analyticCubeResolvent mu hf hfD m)

/-- A local analytic cube resolvent preserves pointwise order between bounded
measurable data. -/
theorem analyticCubeResolvent_mono (mu : PositiveShift)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E)
    (hfg : ∀ x, f x ≤ g x) (m : ℕ) (x : Vec d) :
    A.analyticCubeResolvent mu f hf hfD m x ≤
      A.analyticCubeResolvent mu g hg hgE m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · rw [analyticCubeResolvent, dite_eq_left hx, analyticCubeResolvent, dite_eq_left hx]
    let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
    let F : ScalarL2 (wholeSpaceCube d m) :=
      boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
        (fun y => hfD y)
    let G : ScalarL2 (wholeSpaceCube d m) :=
      boundedMeasurableToScalarL2 hU (hg.comp measurable_subtype_coe)
        (fun y => hgE y)
    have hFG : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m), F y ≤ G y := by
      filter_upwards [boundedMeasurableToScalarL2_coeFn hU
          (hf.comp measurable_subtype_coe) (fun y => hfD y),
        boundedMeasurableToScalarL2_coeFn hU
          (hg.comp measurable_subtype_coe) (fun y => hgE y),
        ae_restrict_mem hU.isOpen.measurableSet] with y hF hG hy
      rw [hF, hG, domainExtension_of_mem hy, domainExtension_of_mem hy]
      exact hfg y
    refine le_of_ae_le_of_continuousOn hU.isOpen
      (continuousOn_continuousCoeffBoundedResolvent A.a hU A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y => hfD y))
      (continuousOn_continuousCoeffBoundedResolvent A.a hU A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd mu
        (hg.comp measurable_subtype_coe) (fun y => hgE y)) ?_ x hx
    filter_upwards [continuousCoeffBoundedResolvent_ae A.a hU A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y => hfD y),
      continuousCoeffBoundedResolvent_ae A.a hU A.hnu A.hnu
        (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd mu
        (hg.comp measurable_subtype_coe) (fun y => hgE y),
      alphaShiftedResolvent_mono_ae A.a hU mu.property A.hnu
        (A.cubeEllipticity m) F G hFG] with y hrepF hrepG hle
    rw [hrepF, hrepG]
    exact hle
  · rw [analyticCubeResolvent, dite_eq_right hx, analyticCubeResolvent, dite_eq_right hx]

private theorem alphaShiftedResolvent_resolvent_identity_apply
    {U : Set (Vec d)} {Lam : ℝ} (mu nu : PositiveShift) (hUell :
      IsEllipticFieldOn A.nu Lam U A.a)
    (F : ScalarL2 U) :
    alphaShiftedResolvent A.a mu.property A.hnu hUell F =
      alphaShiftedResolvent A.a nu.property A.hnu hUell F +
        ((nu : ℝ) - (mu : ℝ)) •
          alphaShiftedResolvent A.a nu.property A.hnu hUell
            (alphaShiftedResolvent A.a mu.property A.hnu hUell F) := by
  have hid := alphaShiftedResolvent_resolvent_identity A.a nu.property mu.property
    A.hnu hUell
  have happ := congrArg (fun T : ScalarL2 U →L[ℝ] ScalarL2 U => T F) hid
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply] at happ
  have hstep :
      alphaShiftedResolvent A.a nu.property A.hnu hUell F -
          alphaShiftedResolvent A.a mu.property A.hnu hUell F =
        ((mu : ℝ) - (nu : ℝ)) •
          alphaShiftedResolvent A.a nu.property A.hnu hUell
            (alphaShiftedResolvent A.a mu.property A.hnu hUell F) := happ
  have hsmul : ((mu : ℝ) - (nu : ℝ)) •
        alphaShiftedResolvent A.a nu.property A.hnu hUell
          (alphaShiftedResolvent A.a mu.property A.hnu hUell F) =
      -(((nu : ℝ) - (mu : ℝ)) •
        alphaShiftedResolvent A.a nu.property A.hnu hUell
          (alphaShiftedResolvent A.a mu.property A.hnu hUell F)) := by
    rw [← neg_smul]
    congr 1
    ring
  rw [hsmul] at hstep
  linear_combination (norm := module) -hstep

/-- The local analytic cube resolvent is additive on nonnegative bounded
measurable data. -/
theorem analyticCubeResolvent_add (mu : PositiveShift)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E)
    (hfg : ∀ x, |f x + g x| ≤ D + E) (m : ℕ) (x : Vec d) :
    A.analyticCubeResolvent mu (fun y => f y + g y) (hf.add hg) hfg m x =
      A.analyticCubeResolvent mu f hf hfD m x +
        A.analyticCubeResolvent mu g hg hgE m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · rw [analyticCubeResolvent, dite_eq_left hx, analyticCubeResolvent, dite_eq_left hx,
      analyticCubeResolvent, dite_eq_left hx]
    exact (continuousCoeffBoundedResolvent_add A.a
      (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd mu
      (hf.comp measurable_subtype_coe) (hg.comp measurable_subtype_coe)
      (fun y => hfD y) (fun y => hgE y) (fun y => hfg y) hx).symm
  · rw [analyticCubeResolvent, dite_eq_right hx, analyticCubeResolvent, dite_eq_right hx,
      analyticCubeResolvent, dite_eq_right hx, add_zero]

/-- The extended-real local resolvent is additive on nonnegative data. -/
theorem analyticCubeResolventENN_add (mu : PositiveShift)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) {D E : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E)
    (hfg : ∀ x, |f x + g x| ≤ D + E) (m : ℕ) (x : Vec d) :
    A.analyticCubeResolventENN mu (fun y => f y + g y) (hf.add hg) hfg m x =
      A.analyticCubeResolventENN mu f hf hfD m x +
        A.analyticCubeResolventENN mu g hg hgE m x := by
  simp only [analyticCubeResolventENN]
  rw [A.analyticCubeResolvent_add mu hf hg hfD hgE hfg m x,
    ENNReal.ofReal_add
      (A.analyticCubeResolvent_nonneg mu hf hf0 hfD m x)
      (A.analyticCubeResolvent_nonneg mu hg hg0 hgE m x)]

/-- The analytic minimal resolvent is additive on nonnegative bounded
measurable observables. -/
theorem analyticMinimalResolvent_add (mu : PositiveShift)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) {D E : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E)
    (hfg : ∀ x, |f x + g x| ≤ D + E) (x : Vec d) :
    A.analyticMinimalResolvent mu (fun y => f y + g y) (hf.add hg) hfg x =
      A.analyticMinimalResolvent mu f hf hfD x +
        A.analyticMinimalResolvent mu g hg hgE x := by
  unfold analyticMinimalResolvent
  have hmonoF : Monotone fun m => A.analyticCubeResolventENN mu f hf hfD m x :=
    fun m n hmn => ENNReal.ofReal_le_ofReal
      (A.monotone_analyticCubeResolvent mu hf hf0 hfD x hmn)
  have hmonoG : Monotone fun m => A.analyticCubeResolventENN mu g hg hgE m x :=
    fun m n hmn => ENNReal.ofReal_le_ofReal
      (A.monotone_analyticCubeResolvent mu hg hg0 hgE x hmn)
  rw [ENNReal.iSup_add_iSup_of_monotone hmonoF hmonoG]
  exact iSup_congr fun m =>
    A.analyticCubeResolventENN_add mu hf hg hf0 hg0 hfD hgE hfg m x

/-- The local analytic cube resolvent obeys the uniform resolvent bound. -/
theorem abs_analyticCubeResolvent_le (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D)
    (m : ℕ) (x : Vec d) :
    |A.analyticCubeResolvent mu f hf hfD m x| ≤ D / (mu : ℝ) := by
  rw [analyticCubeResolvent]
  split_ifs with hx
  · simpa only [abs_of_nonneg hD] using
      (abs_continuousCoeffBoundedResolvent_le A.a
        (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y => hfD y) x hx)
  · rw [abs_zero]
    exact div_nonneg hD mu.property.le

/-- The analytic minimal resolvent of nonnegative data satisfies the sharp
uniform bound inherited from the bounded domains. -/
theorem analyticMinimalResolvent_le (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    A.analyticMinimalResolvent mu f hf hfD x ≤
      ENNReal.ofReal (D / (mu : ℝ)) := by
  rw [analyticMinimalResolvent]
  refine iSup_le fun m => ?_
  rw [analyticCubeResolventENN]
  apply ENNReal.ofReal_le_ofReal
  have habs := A.abs_analyticCubeResolvent_le mu hf hD hfD m x
  have hnonneg := A.analyticCubeResolvent_nonneg mu hf hf0 hfD m x
  rwa [abs_of_nonneg hnonneg] at habs

/-- The bounded analytic minimal resolvent never takes the value infinity. -/
theorem analyticMinimalResolvent_ne_top (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    A.analyticMinimalResolvent mu f hf hfD x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (A.analyticMinimalResolvent_le mu hf hf0 hD hfD x)

/-- The zero-extended analytic resolvent on one cube satisfies the resolvent
identity pointwise on the ambient space. -/
theorem analyticCubeResolvent_resolvent_identity (mu nu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    A.analyticCubeResolvent mu f hf hfD m x =
      A.analyticCubeResolvent nu f hf hfD m x +
        ((nu : ℝ) - (mu : ℝ)) *
          A.analyticCubeResolvent nu
            (A.analyticCubeResolvent mu f hf hfD m)
            (A.measurable_analyticCubeResolvent mu hf hfD m)
            (D := D / (mu : ℝ))
            (A.abs_analyticCubeResolvent_le mu hf hD hfD m) m x := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
      (fun y => hfD y)
  let rmu : Vec d → ℝ := continuousCoeffBoundedResolvent A.a hU A.hnu
    A.hnu (A.cubeEllipticity m) A.hsymm
    (A.skewContinuousOnCube m) A.hd mu
    (hf.comp measurable_subtype_coe) (fun y => hfD y)
  let rnu : Vec d → ℝ := continuousCoeffBoundedResolvent A.a hU A.hnu
    A.hnu (A.cubeEllipticity m) A.hsymm
    (A.skewContinuousOnCube m) A.hd nu
    (hf.comp measurable_subtype_coe) (fun y => hfD y)
  let g : Vec d → ℝ := A.analyticCubeResolvent mu f hf hfD m
  let hg : Measurable g := A.measurable_analyticCubeResolvent mu hf hfD m
  let hgD : ∀ y, |g y| ≤ D / (mu : ℝ) :=
    A.abs_analyticCubeResolvent_le mu hf hD hfD m
  let router : Vec d → ℝ := continuousCoeffBoundedResolvent A.a hU A.hnu
    A.hnu (A.cubeEllipticity m) A.hsymm
    (A.skewContinuousOnCube m) A.hd nu
    (hg.comp measurable_subtype_coe) (fun y => hgD y)
  by_cases hx : x ∈ wholeSpaceCube d m
  · rw [analyticCubeResolvent, dite_eq_left hx, analyticCubeResolvent, dite_eq_left hx,
      analyticCubeResolvent, dite_eq_left hx]
    change rmu x = rnu x + ((nu : ℝ) - (mu : ℝ)) * router x
    have hclass : boundedMeasurableToScalarL2 hU
          (hg.comp measurable_subtype_coe) (fun y => hgD y) =
        alphaShiftedResolvent A.a mu.property A.hnu
          (A.cubeEllipticity m) F := by
      refine (Lp.ext_iff).2 ?_
      filter_upwards [boundedMeasurableToScalarL2_coeFn hU
          (hg.comp measurable_subtype_coe) (fun y => hgD y),
        continuousCoeffBoundedResolvent_ae A.a hU A.hnu
          A.hnu (A.cubeEllipticity m) A.hsymm
          (A.skewContinuousOnCube m) A.hd mu
          (hf.comp measurable_subtype_coe) (fun y => hfD y),
        ae_restrict_mem hU.isOpen.measurableSet] with y hdatum hrep hy
      rw [hdatum, domainExtension_of_mem hy]
      change g y = _
      dsimp only [g]
      rw [analyticCubeResolvent, dite_eq_left hy]
      simpa only [rmu, F] using hrep
    have hL2 := A.alphaShiftedResolvent_resolvent_identity_apply mu nu
      (A.cubeEllipticity m) F
    have heq := continuousCoeffBoundedResolvent_eq_of_continuousOn_of_ae_eq
      A.a hU A.hnu A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd mu
      (hf.comp measurable_subtype_coe) (fun y => hfD y)
      (v := fun y => rnu y + ((nu : ℝ) - (mu : ℝ)) * router y)
      ((continuousOn_continuousCoeffBoundedResolvent A.a hU A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd nu
        (hf.comp measurable_subtype_coe) (fun y => hfD y)).add
        (continuousOn_const.mul
          (continuousOn_continuousCoeffBoundedResolvent A.a hU A.hnu
            A.hnu (A.cubeEllipticity m) A.hsymm
            (A.skewContinuousOnCube m) A.hd nu
            (hg.comp measurable_subtype_coe) (fun y => hgD y)))) ?_
    · exact (heq hx).symm
    · rw [hL2]
      have hinner := continuousCoeffBoundedResolvent_ae A.a hU A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd nu
        (hg.comp measurable_subtype_coe) (fun y => hgD y)
      rw [hclass] at hinner
      filter_upwards [continuousCoeffBoundedResolvent_ae A.a hU A.hnu
          A.hnu (A.cubeEllipticity m) A.hsymm
          (A.skewContinuousOnCube m) A.hd nu
          (hf.comp measurable_subtype_coe) (fun y => hfD y), hinner,
        Lp.coeFn_add
          (alphaShiftedResolvent A.a nu.property A.hnu
            (A.cubeEllipticity m) F)
          (((nu : ℝ) - (mu : ℝ)) •
            alphaShiftedResolvent A.a nu.property A.hnu
              (A.cubeEllipticity m)
              (alphaShiftedResolvent A.a mu.property A.hnu
                (A.cubeEllipticity m) F)),
        Lp.coeFn_smul ((nu : ℝ) - (mu : ℝ))
          (alphaShiftedResolvent A.a nu.property A.hnu
            (A.cubeEllipticity m)
            (alphaShiftedResolvent A.a mu.property A.hnu
              (A.cubeEllipticity m) F))]
          with y hnu houter hadd hsmul
      rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, ← hnu,
        ← houter]
  · rw [analyticCubeResolvent, dite_eq_right hx, analyticCubeResolvent, dite_eq_right hx,
      analyticCubeResolvent, dite_eq_right hx, mul_zero, add_zero]

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
