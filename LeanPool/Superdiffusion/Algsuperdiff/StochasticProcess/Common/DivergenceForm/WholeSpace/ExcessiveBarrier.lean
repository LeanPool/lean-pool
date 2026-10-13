/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PartDomainSubsolution
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Minimal

/-!
# ExcessiveBarrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The barrier of the whole-space part-domain comparison

Let `V` be an open bounded convex domain, `f` a nonnegative bounded measurable
observable vanishing off `V`, and `u` the shifted Dirichlet solution on `V`.
The barrier of the whole-space comparison is the difference

`v = R^min f - u~`,

where `R^min` is the analytic minimal resolvent of the cubic exhaustion and
`u~` is the extension of `u` by zero to the whole space.

This file fixes the data of that barrier and proves the first analytic step:
on every exhaustion cube containing `V`, the zero extension of the part
solution is a weak subsolution of the shifted equation with the same forcing.

The continuous representative of the part solution vanishing on the geometric
boundary of `V` is a caller-supplied field of `WholeSpaceBarrierData`, not a
claim proved here.  On an axis cube it is discharged by the closed-cube
boundary representative of the regularity layer.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open MarkovProcess.Semigroup

noncomputable section

variable {d : ℕ}

/-- The canonical shifted solution does not depend on the ellipticity
certificate used to build it. -/
theorem alphaShiftedSolution_congr_ellipticity (a : CoeffField d)
    {U : Set (Vec d)} {alpha nu nu' Lam Lam' : ℝ} (halpha : 0 < alpha)
    (hnu : 0 < nu) (hnu' : 0 < nu')
    (hEll : IsEllipticFieldOn nu Lam U a)
    (hEll' : IsEllipticFieldOn nu' Lam' U a) (f : ScalarL2 U) :
    alphaShiftedSolution a halpha hnu hEll f =
      alphaShiftedSolution a halpha hnu' hEll' f :=
  (isAlphaShiftedWeakSolution_iff_eq a halpha hnu' hEll' f _).1
    (alphaShiftedSolution_isAlphaShiftedWeakSolution a halpha hnu hEll f)

/-- Restricting the `L²` class of a globally defined bounded measurable
observable to a smaller domain returns its `L²` class there. -/
theorem restrictScalarL2ToPart_boundedMeasurableToScalarL2
    {V U : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet
        (boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
          (fun y => hfD y)) =
      boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe)
        (fun y => hfD y) := by
  refine (Lp.ext_iff).2 ?_
  have hrestrict := restrictScalarL2ToPart_coeFn hV.isOpen.measurableSet
    hU.isOpen.measurableSet hVU
    (boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
      (fun y => hfD y))
  have hlarge := boundedMeasurableToScalarL2_coeFn hU
    (hf.comp measurable_subtype_coe) (fun y => hfD y)
  have hlargeV := ae_restrict_of_ae_restrict_of_subset hVU hlarge
  have hsmall := boundedMeasurableToScalarL2_coeFn hV
    (hf.comp measurable_subtype_coe) (fun y => hfD y)
  filter_upwards [hrestrict, hlargeV, hsmall,
    self_mem_ae_restrict hV.isOpen.measurableSet] with x h1 h2 h3 hx
  rw [h1, h2, h3, domainExtension_of_mem (hVU hx), domainExtension_of_mem hx]
  rfl

/-- A pointwise nonnegative bounded measurable observable has an almost
everywhere nonnegative `L²` class. -/
theorem ae_nonneg_boundedMeasurableToScalarL2 {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
        (fun y => hfD y) x := by
  filter_upwards [boundedMeasurableToScalarL2_coeFn hU
      (hf.comp measurable_subtype_coe) (fun y => hfD y),
    self_mem_ae_restrict hU.isOpen.measurableSet] with x hx hxU
  rw [hx, domainExtension_of_mem hxU]
  exact hf0 x

/-- The `L²` class on the part domain of a globally defined bounded
measurable observable. -/
def partDatumL2 {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    ScalarL2 V :=
  boundedMeasurableToScalarL2 hV (hf.comp measurable_subtype_coe)
    (fun y => hfD y)

/-- Every bounded set lies inside an exhaustion cube. -/
theorem exists_wholeSpaceCube_superset {V : Set (Vec d)}
    (hV : Bornology.IsBounded V) : ∃ m : ℕ, V ⊆ wholeSpaceCube d m := by
  obtain ⟨R, hR⟩ := hV.subset_closedBall (0 : Vec d)
  obtain ⟨m, hm⟩ := exists_nat_gt R
  have hpowNat : m < 3 ^ m := Nat.lt_pow_self (by norm_num)
  have hpow : (m : ℝ) < (3 : ℝ) ^ m := by exact_mod_cast hpowNat
  refine ⟨m, fun x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hx
  rw [mem_wholeSpaceCube_iff]
  intro i
  have hxi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hlt : |x i| < (3 : ℝ) ^ m :=
    calc |x i| ≤ ‖x‖ := hxi
      _ ≤ R := hxR
      _ < (m : ℝ) := hm
      _ < (3 : ℝ) ^ m := hpow
  exact abs_lt.mp hlt

/-- The index of an exhaustion cube containing a bounded part domain. -/
def partCubeIndex {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) : ℕ :=
  Classical.choose (exists_wholeSpaceCube_superset hV.isBoundedDomain.isBounded)

theorem subset_wholeSpaceCube_partCubeIndex {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) :
    V ⊆ wholeSpaceCube d (partCubeIndex hV) :=
  Classical.choose_spec
    (exists_wholeSpaceCube_superset hV.isBoundedDomain.isBounded)

variable [NeZero d]

/-- The ellipticity certificate of a bounded part domain, obtained by
restricting the certificate of an exhaustion cube containing it.  The shifted
solution does not depend on the certificate, so nothing is lost by fixing this
one. -/
theorem partEllipticity (A : WholeSpaceAnalyticData d) {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) :
    IsEllipticFieldOn A.nu (A.cubeEllipticityUpper (partCubeIndex hV)) V A.a :=
  (A.cubeEllipticity (partCubeIndex hV)).mono hV.isOpen.measurableSet
    (subset_wholeSpaceCube_partCubeIndex hV)

/-- **The data of the whole-space barrier.**  A part domain `V`, a
nonnegative bounded measurable observable supported in `V`, and a continuous
zero extension `utilde` of the shifted Dirichlet solution on `V`.  The last
three fields are the caller's obligation: they record that `utilde` is a
continuous representative of the part solution which vanishes off `V`. -/
structure WholeSpaceBarrierData (A : WholeSpaceAnalyticData d) where
  /-- The part domain. -/
  V : Set (Vec d)
  /-- The part domain is an open bounded convex domain. -/
  hV : IsOpenBoundedConvexDomain V
  /-- The shift. -/
  lam : PositiveShift
  /-- The observable. -/
  f : Vec d → ℝ
  /-- Measurability of the observable. -/
  hf : Measurable f
  /-- Nonnegativity of the observable. -/
  hf0 : ∀ x, 0 ≤ f x
  /-- A uniform bound for the observable. -/
  D : ℝ
  /-- The uniform bound. -/
  hfD : ∀ x, |f x| ≤ D
  /-- The observable vanishes almost everywhere off the part domain. -/
  hfV : f =ᵐ[volume] V.indicator f
  /-- The continuous zero extension of the part solution. -/
  utilde : Vec d → ℝ
  /-- Continuity of the zero extension. -/
  hutildeCont : Continuous utilde
  /-- The zero extension vanishes off the part domain. -/
  hutildeOff : ∀ x, x ∉ V → utilde x = 0
  /-- The zero extension represents the part solution. -/
  hutildeRep : utilde =ᵐ[volumeMeasureOn V]
    ZeroTraceSobolev.toL2
      (alphaShiftedSolution A.a lam.property A.hnu (partEllipticity A hV)
        (partDatumL2 hV hf hfD))

namespace WholeSpaceBarrierData

variable {A : WholeSpaceAnalyticData d} (P : WholeSpaceBarrierData A)

/-- The shifted Dirichlet solution on the part domain. -/
def partSolution : ZeroTraceSobolev P.V :=
  alphaShiftedSolution A.a P.lam.property A.hnu (partEllipticity A P.hV)
    (partDatumL2 P.hV P.hf P.hfD)

theorem utilde_ae_eq_partSolution :
    P.utilde =ᵐ[volumeMeasureOn P.V]
      ZeroTraceSobolev.toL2 P.partSolution :=
  P.hutildeRep

/-- On an exhaustion cube containing the part domain, the restriction of the
ambient datum solves the same part problem. -/
theorem partSolution_eq_of_cube (m : ℕ) (hVU : P.V ⊆ wholeSpaceCube d m) :
    alphaShiftedSolution A.a P.lam.property A.hnu
        ((A.cubeEllipticity m).mono P.hV.isOpen.measurableSet hVU)
        (restrictScalarL2ToPart (V := P.V)
          (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen.measurableSet
          (boundedMeasurableToScalarL2
            (isOpenBoundedConvexDomain_wholeSpaceCube d m)
            (P.hf.comp measurable_subtype_coe) (fun y => P.hfD y))) =
      P.partSolution := by
  rw [restrictScalarL2ToPart_boundedMeasurableToScalarL2 P.hV
    (isOpenBoundedConvexDomain_wholeSpaceCube d m) hVU P.hf P.hfD]
  exact alphaShiftedSolution_congr_ellipticity A.a P.lam.property A.hnu A.hnu
    _ _ _

/-- The zero extension of the part solution to an exhaustion cube. -/
def cubeZeroExtension (m : ℕ) (hVU : P.V ⊆ wholeSpaceCube d m) :
    ZeroTraceSobolev (wholeSpaceCube d m) :=
  ZeroTraceSobolev.extendByZeroToPartSuperset P.hV
    (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen hVU P.partSolution

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form
