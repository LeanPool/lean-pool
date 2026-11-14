/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ContinuousCoeffPotentialResolvent
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Minimal
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PotentialDomainMonotonicity

/-!
# PenalizedMinimal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Minimal whole-space resolvents with exterior penalization

For an open bounded convex cube `V`, the potential is `n` on `Vᶜ` and zero
on `V`.  The local potential resolvents increase along the cubic exhaustion,
so their pointwise supremum defines the whole-space penalized resolvent.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- The exterior penalization potential `n 1_(Vᶜ)`. -/
def wholeSpacePenalizationPotential (V : Set (Vec d)) (n : ℕ) : Vec d → ℝ :=
  Vᶜ.indicator fun _ ↦ (n : ℝ)

omit [NeZero d] in
theorem measurable_wholeSpacePenalizationPotential {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) :
    Measurable (wholeSpacePenalizationPotential V n) :=
  measurable_const.indicator hV.measurableSet.compl

omit [NeZero d] in
theorem wholeSpacePenalizationPotential_nonneg (V : Set (Vec d)) (n : ℕ)
    (x : Vec d) : 0 ≤ wholeSpacePenalizationPotential V n x := by
  classical
  rw [wholeSpacePenalizationPotential, Set.indicator_apply]
  split_ifs <;> positivity

omit [NeZero d] in
theorem wholeSpacePenalizationPotential_le (V : Set (Vec d)) (n : ℕ)
    (x : Vec d) : wholeSpacePenalizationPotential V n x ≤ n := by
  classical
  rw [wholeSpacePenalizationPotential, Set.indicator_apply]
  split_ifs <;> simp

omit [NeZero d] in
theorem wholeSpacePenalizationPotential_eq_zero {V : Set (Vec d)} (n : ℕ)
    {x : Vec d} (hx : x ∈ V) : wholeSpacePenalizationPotential V n x = 0 := by
  rw [wholeSpacePenalizationPotential, Set.indicator_of_notMem]
  exact fun hxcompl ↦ hxcompl hx

omit [NeZero d] in
/-- The exterior potential is bounded and nonnegative on every exhaustion
cube. -/
theorem wholeSpacePenalizationPotential_isBounded
    {V : Set (Vec d)} (hV : IsOpen V) (n m : ℕ) :
    IsBoundedNonnegativePotential (wholeSpaceCube d m)
      (wholeSpacePenalizationPotential V n) n :=
  ⟨measurable_wholeSpacePenalizationPotential hV n,
    Filter.Eventually.of_forall fun x ↦
      wholeSpacePenalizationPotential_nonneg V n x,
    Filter.Eventually.of_forall fun x ↦
      wholeSpacePenalizationPotential_le V n x⟩

/-- The local potential resolvent on an exhaustion cube, extended by zero. -/
def analyticPenalizedCubeResolvent {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) : ℝ := by
  classical
  exact if hx : x ∈ wholeSpaceCube d m then
    continuousCoeffPotentialBoundedResolvent A.a
      (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd
      (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m) mu
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y) x
  else 0

/-- The extended-real local penalized resolvent. -/
def analyticPenalizedCubeResolventENN {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x)

/-- The minimal whole-space exterior-penalized resolvent. -/
def analyticPenalizedResolvent {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (x : Vec d) : ℝ≥0∞ :=
  ⨆ m, A.analyticPenalizedCubeResolventENN hV n mu f hf hfD m x

omit [NeZero d] in
private theorem restrictedDatum_nonneg_ae_penalized {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d m),
      0 ≤ boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y) x := by
  filter_upwards [boundedMeasurableToScalarL2_coeFn
      (isOpenBoundedConvexDomain_wholeSpaceCube d m)
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y),
    ae_restrict_mem
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen.measurableSet]
      with x hx hxmem
  rw [hx, domainExtension_of_mem hxmem]
  exact hf0 x

/-- Local penalized cube resolvents are nonnegative on nonnegative data. -/
theorem analyticPenalizedCubeResolvent_nonneg {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    0 ≤ A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x := by
  rw [analyticPenalizedCubeResolvent]
  split_ifs with hx
  · refine le_of_ae_le_of_continuousOn
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen continuousOn_const
      (continuousOn_continuousCoeffPotentialBoundedResolvent A.a
        (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) mu
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)) ?_ x hx
    filter_upwards [continuousCoeffPotentialBoundedResolvent_ae A.a
        (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) mu
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y),
      potentialResolvent_nonneg_ae A.a
        (isOpenBoundedConvexDomain_wholeSpaceCube d m) mu.property
        A.hnu (A.cubeEllipticity m)
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m)
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d m)
          (hf.comp measurable_subtype_coe) (fun y ↦ hfD y))
        (restrictedDatum_nonneg_ae_penalized hf hf0 hfD m)] with y hrep hpos
    rwa [hrep]
  · exact le_rfl

/-- A local penalized cube resolvent preserves pointwise order of bounded
measurable data. -/
theorem analyticPenalizedCubeResolvent_mono {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E)
    (hfg : ∀ x, f x ≤ g x) (m : ℕ) (x : Vec d) :
    A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x ≤
      A.analyticPenalizedCubeResolvent hV n mu g hg hgE m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · rw [analyticPenalizedCubeResolvent, dite_eq_left hx,
      analyticPenalizedCubeResolvent, dite_eq_left hx]
    let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
    let F := boundedMeasurableToScalarL2 hU
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)
    let G := boundedMeasurableToScalarL2 hU
      (hg.comp measurable_subtype_coe) (fun y ↦ hgE y)
    have hFG : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m), F y ≤ G y := by
      filter_upwards [boundedMeasurableToScalarL2_coeFn hU
          (hf.comp measurable_subtype_coe) (fun y ↦ hfD y),
        boundedMeasurableToScalarL2_coeFn hU
          (hg.comp measurable_subtype_coe) (fun y ↦ hgE y),
        ae_restrict_mem hU.isOpen.measurableSet] with y hFy hGy hy
      rw [hFy, hGy, domainExtension_of_mem hy, domainExtension_of_mem hy]
      exact hfg y
    have hle := potentialResolvent_mono_ae A.a hU mu.property A.hnu
      (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m) F G hFG
    refine le_of_ae_le_of_continuousOn hU.isOpen
      (continuousOn_continuousCoeffPotentialBoundedResolvent A.a hU A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) mu
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y))
      (continuousOn_continuousCoeffPotentialBoundedResolvent A.a hU A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) mu
        (hg.comp measurable_subtype_coe) (fun y ↦ hgE y)) ?_ x hx
    filter_upwards [hle,
      continuousCoeffPotentialBoundedResolvent_ae A.a hU A.hnu A.hnu
        (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) mu
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y),
      continuousCoeffPotentialBoundedResolvent_ae A.a hU A.hnu A.hnu
        (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) mu
        (hg.comp measurable_subtype_coe) (fun y ↦ hgE y)] with y hle hrepF hrepG
    rwa [hrepF, hrepG]
  · rw [analyticPenalizedCubeResolvent, dite_eq_right hx,
      analyticPenalizedCubeResolvent, dite_eq_right hx]

/-- The local exterior-penalized resolvents increase with the exhaustion. -/
theorem analyticPenalizedCubeResolvent_le_succ {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x ≤
      A.analyticPenalizedCubeResolvent hV n mu f hf hfD (m + 1) x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · have hx' := wholeSpaceCube_subset_succ d m hx
    rw [analyticPenalizedCubeResolvent, dite_eq_left hx,
      analyticPenalizedCubeResolvent, dite_eq_left hx']
    let hSmall := isOpenBoundedConvexDomain_wholeSpaceCube d m
    let hLarge := isOpenBoundedConvexDomain_wholeSpaceCube d (m + 1)
    let F := boundedMeasurableToScalarL2 hLarge
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)
    have hmono := potentialPartDomainResolvent_le_ae_of_ellipticityWitness A.a
      hSmall hLarge (wholeSpaceCube_subset_succ d m) mu.property A.hnu A.hnu
      (Nat.cast_nonneg n) (A.cubeEllipticity m)
      (A.cubeEllipticity (m + 1))
      (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m)
      (wholeSpacePenalizationPotential_isBounded hV n (m + 1)) F
      (restrictedDatum_nonneg_ae_penalized hf hf0 hfD (m + 1))
    have hrestrict := restrict_boundedMeasurableToScalarL2_succ hf hfD m
    rw [hrestrict] at hmono
    refine le_of_ae_le_of_continuousOn hSmall.isOpen
      (continuousOn_continuousCoeffPotentialBoundedResolvent A.a hSmall A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) mu
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y))
      ((continuousOn_continuousCoeffPotentialBoundedResolvent A.a hLarge A.hnu
        A.hnu (A.cubeEllipticity (m + 1)) A.hsymm
        (A.skewContinuousOnCube (m + 1)) A.hd
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n (m + 1)) mu
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)).mono
          (wholeSpaceCube_subset_succ d m)) ?_ x hx
    filter_upwards [hmono,
      continuousCoeffPotentialBoundedResolvent_ae A.a hSmall A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) mu
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y),
      ae_restrict_of_ae_restrict_of_subset (wholeSpaceCube_subset_succ d m)
        (continuousCoeffPotentialBoundedResolvent_ae A.a hLarge A.hnu
          A.hnu (A.cubeEllipticity (m + 1)) A.hsymm
          (A.skewContinuousOnCube (m + 1)) A.hd
          (wholeSpacePenalizationPotential V n)
          (wholeSpacePenalizationPotential_isBounded hV n (m + 1)) mu
          (hf.comp measurable_subtype_coe) (fun y ↦ hfD y))]
        with y hle hsmall hlarge
    rwa [hsmall, hlarge]
  · rw [analyticPenalizedCubeResolvent, dite_eq_right hx]
    exact A.analyticPenalizedCubeResolvent_nonneg hV n mu hf hf0 hfD (m + 1) x

/-- At each point the local penalized resolvents form a monotone sequence. -/
theorem monotone_analyticPenalizedCubeResolvent {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    Monotone fun m ↦ A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x :=
  monotone_nat_of_le_succ fun m ↦
    A.analyticPenalizedCubeResolvent_le_succ hV n mu hf hf0 hfD m x

/-- Scalar multiplication commutes with one local exterior-penalized
resolvent. -/
theorem analyticPenalizedCubeResolvent_smul {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) (c : ℝ)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D)
    (hcf : ∀ x, |c * f x| ≤ |c| * D) (m : ℕ) (x : Vec d) :
    A.analyticPenalizedCubeResolvent hV n mu (fun y ↦ c * f y)
        (hf.const_smul c) hcf m x =
      c * A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · rw [analyticPenalizedCubeResolvent, dite_eq_left hx,
      analyticPenalizedCubeResolvent, dite_eq_left hx]
    exact (continuousCoeffPotentialBoundedResolvent_smul A.a
      (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd
      (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m) mu c
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y) (fun y ↦ hcf y) hx).symm
  · rw [analyticPenalizedCubeResolvent, dite_eq_right hx,
      analyticPenalizedCubeResolvent, dite_eq_right hx, mul_zero]

/-- A zero-extended local penalized resolvent is measurable. -/
theorem measurable_analyticPenalizedCubeResolvent {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    Measurable (A.analyticPenalizedCubeResolvent hV n mu f hf hfD m) := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let v : wholeSpaceCube d m → ℝ := fun y ↦
    continuousCoeffPotentialBoundedResolvent A.a hU A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd
      (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m) mu
      (hf.comp measurable_subtype_coe) (fun z ↦ hfD z) y
  have hv : Measurable v :=
    ((continuousOn_continuousCoeffPotentialBoundedResolvent A.a hU A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd
      (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m) mu
      (hf.comp measurable_subtype_coe) (fun z ↦ hfD z)).domRestrict).measurable
  have heq : A.analyticPenalizedCubeResolvent hV n mu f hf hfD m =
      domainExtension v := by
    funext x
    by_cases hx : x ∈ wholeSpaceCube d m
    · rw [analyticPenalizedCubeResolvent, dite_eq_left hx, domainExtension_of_mem hx]
    · rw [analyticPenalizedCubeResolvent, dite_eq_right hx]
      have hnot : ¬ ∃ y : wholeSpaceCube d m, (y : Vec d) = x := by
        rintro ⟨y, rfl⟩
        exact hx y.2
      exact (Function.extend_apply' v (0 : Vec d → ℝ) x hnot).symm
  rw [heq]
  exact measurable_domainExtension hU.isOpen.measurableSet hv

/-- A local penalized representative is continuous on its defining cube. -/
theorem continuousOn_analyticPenalizedCubeResolvent {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    ContinuousOn (A.analyticPenalizedCubeResolvent hV n mu f hf hfD m)
      (wholeSpaceCube d m) := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  refine (continuousOn_continuousCoeffPotentialBoundedResolvent A.a hU A.hnu
    A.hnu (A.cubeEllipticity m) A.hsymm
    (A.skewContinuousOnCube m) A.hd
    (wholeSpacePenalizationPotential V n)
    (wholeSpacePenalizationPotential_isBounded hV n m) mu
    (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)).congr ?_
  intro x hx
  rw [analyticPenalizedCubeResolvent, dite_eq_left hx]

/-- On its cube, the local representative agrees almost everywhere with the
potential resolvent class. -/
theorem analyticPenalizedCubeResolvent_ae {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    A.analyticPenalizedCubeResolvent hV n mu f hf hfD m =ᵐ[
        volumeMeasureOn (wholeSpaceCube d m)]
      potentialResolvent A.a mu.property A.hnu
        (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m)
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d m)
          (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)) := by
  filter_upwards [continuousCoeffPotentialBoundedResolvent_ae A.a
      (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd
      (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m) mu
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y),
    ae_restrict_mem
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen.measurableSet]
      with x hrep hx
  rw [analyticPenalizedCubeResolvent, dite_eq_left hx, hrep]

/-- The minimal penalized resolvent is measurable. -/
theorem measurable_analyticPenalizedResolvent {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    Measurable (A.analyticPenalizedResolvent hV n mu f hf hfD) := by
  exact Measurable.iSup fun m ↦ ENNReal.measurable_ofReal.comp
    (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)

/-- Local penalized resolvents obey the maximum-principle bound. -/
theorem abs_analyticPenalizedCubeResolvent_le {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    |A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x| ≤
      D / (mu : ℝ) := by
  rw [analyticPenalizedCubeResolvent]
  split_ifs with hx
  · simpa only [abs_of_nonneg hD] using
      (abs_continuousCoeffPotentialBoundedResolvent_le A.a
        (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
        A.hnu (A.cubeEllipticity m) A.hsymm
        (A.skewContinuousOnCube m) A.hd
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) mu
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y) x hx)
  · rw [abs_zero]
    exact div_nonneg hD mu.property.le

/-- The minimal penalized resolvent inherits the sharp uniform bound. -/
theorem analyticPenalizedResolvent_le {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    A.analyticPenalizedResolvent hV n mu f hf hfD x ≤
      ENNReal.ofReal (D / (mu : ℝ)) := by
  rw [analyticPenalizedResolvent]
  refine iSup_le fun m ↦ ?_
  rw [analyticPenalizedCubeResolventENN]
  apply ENNReal.ofReal_le_ofReal
  have habs := A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m x
  rwa [abs_of_nonneg
    (A.analyticPenalizedCubeResolvent_nonneg hV n mu hf hf0 hfD m x)] at habs

/-- The local penalized representatives converge to the real value of their
extended-real supremum. -/
theorem tendsto_analyticPenalizedCubeResolvent {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    Tendsto (fun m ↦ A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x)
      Filter.atTop
      (nhds (A.analyticPenalizedResolvent hV n mu f hf hfD x).toReal) := by
  have hmono := A.monotone_analyticPenalizedCubeResolvent hV n mu hf hf0 hfD x
  have hbdd : BddAbove (Set.range fun m ↦
      A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x) := by
    refine ⟨D / (mu : ℝ), ?_⟩
    rintro y ⟨m, rfl⟩
    exact (le_abs_self _).trans
      (A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m x)
  have hsup : (A.analyticPenalizedResolvent hV n mu f hf hfD x).toReal =
      ⨆ m, A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x := by
    rw [analyticPenalizedResolvent]
    change (⨆ m, ENNReal.ofReal
      (A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x)).toReal = _
    rw [ENNReal.toReal_iSup (fun _ ↦ ENNReal.ofReal_ne_top)]
    apply iSup_congr
    intro m
    rw [ENNReal.toReal_ofReal
      (A.analyticPenalizedCubeResolvent_nonneg hV n mu hf hf0 hfD m x)]
  rw [hsup]
  exact tendsto_atTop_ciSup hmono hbdd

/-- Nonnegative scalar multiplication commutes with the real value of the
minimal exterior-penalized resolvent. -/
theorem toReal_analyticPenalizedResolvent_smul {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {c : ℝ}
    (hc : 0 ≤ c) {f : Vec d → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    (A.analyticPenalizedResolvent hV n mu (fun y ↦ c * f y)
        (hf.const_smul c) (D := c * D) (fun y ↦ by
          rw [abs_mul, abs_of_nonneg hc]
          exact mul_le_mul_of_nonneg_left (hfD y) hc) x).toReal =
      c * (A.analyticPenalizedResolvent hV n mu f hf hfD x).toReal := by
  let hcf : ∀ y, |c * f y| ≤ c * D := fun y ↦ by
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hfD y) hc
  have htcf := A.tendsto_analyticPenalizedCubeResolvent hV n mu
    (hf.const_smul c) (fun y ↦ mul_nonneg hc (hf0 y))
    (mul_nonneg hc hD) hcf x
  have htf := (A.tendsto_analyticPenalizedCubeResolvent hV n mu hf hf0 hD
    hfD x).const_mul c
  apply tendsto_nhds_unique htcf
  apply htf.congr'
  filter_upwards with m
  exact A.analyticPenalizedCubeResolvent_smul hV n mu c hf hfD
    (fun y ↦ by simpa only [abs_of_nonneg hc] using hcf y) m x |>.symm

/-- A local penalized resolvent is additive. -/
theorem analyticPenalizedCubeResolvent_add {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E)
    (hfg : ∀ x, |f x + g x| ≤ D + E) (m : ℕ) (x : Vec d) :
    A.analyticPenalizedCubeResolvent hV n mu (fun y ↦ f y + g y)
        (hf.add hg) hfg m x =
      A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x +
        A.analyticPenalizedCubeResolvent hV n mu g hg hgE m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · rw [analyticPenalizedCubeResolvent, dite_eq_left hx,
      analyticPenalizedCubeResolvent, dite_eq_left hx,
      analyticPenalizedCubeResolvent, dite_eq_left hx]
    exact (continuousCoeffPotentialBoundedResolvent_add A.a
      (isOpenBoundedConvexDomain_wholeSpaceCube d m) A.hnu
      A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd
      (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m) mu
      (hf.comp measurable_subtype_coe) (hg.comp measurable_subtype_coe)
      (fun y ↦ hfD y) (fun y ↦ hgE y) (fun y ↦ hfg y) hx).symm
  · rw [analyticPenalizedCubeResolvent, dite_eq_right hx,
      analyticPenalizedCubeResolvent, dite_eq_right hx,
      analyticPenalizedCubeResolvent, dite_eq_right hx, add_zero]

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
