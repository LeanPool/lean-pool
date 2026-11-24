/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexAnalyticSubvarieties
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PositiveClasses
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.AnalyticSingularities

/-!
# Data underlying numerical restricted volume

This file records a first, deliberately data-level version of the definitions
used in the numerical restricted volume and null locus.  An admissible current
is represented by an actual closed real `(1,1)`-form and a global extended-real
potential.  The analytic intersection mass and the non-nef locus are supplied
as separate data: their intended geometric constructions and independence
properties have not yet been implemented here.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold

noncomputable section

open PositiveClasses

variable {M : Type*}

/-- The pole set of an extended-real potential. -/
def poleSet (u : M → EReal) : Set M := {x | u x = ⊥}

@[simp] theorem mem_poleSet {u : M → EReal} {x : M} :
    x ∈ poleSet u ↔ u x = ⊥ := Iff.rfl

variable {n : ℕ} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A global potential has smooth analytic singularities when this holds in
every actual complex chart, using a positive real logarithmic coefficient and
a smooth real remainder. -/
def HasManifoldSmoothAnalyticSingularities (u : M → EReal) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    HasSmoothAnalyticSingularitiesAt (chartFunction u e) z

/-- **The manifold form of the bounded-remainder convention.**  In every actual complex chart the
coordinate representative is `c log \sum_j |f_j|^2 + b` with `c > 0` real, the `f_j`
holomorphic, and `b` bounded near the point and `C^\infty` off the pole set.

This predicate is the chartwise bounded, off-pole smooth variant of
[Collins–Tosatti, §2](https://www.numdam.org/item/10.5802/afst.1708.pdf#page=8). The local expression in the paper
has a remainder smooth on the whole neighbourhood. The corresponding chartwise
smoothness predicate is `HasManifoldSmoothAnalyticSingularities`. -/
def HasManifoldAnalyticSingularitiesSmoothOffPole (u : M → EReal) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    HasAnalyticSingularitiesSmoothOffPoleAt (chartFunction u e) z

omit [IsComplexManifold n M] in
/-- A presentation with smooth remainder satisfies the off-pole smoothness criterion. -/
theorem HasManifoldSmoothAnalyticSingularities.smoothOffPole {u : M → EReal}
    (hu : HasManifoldSmoothAnalyticSingularities (n := n) u) :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u :=
  fun e z hz => (hu e z hz).smoothOffPole

/-- A strictly positive real error parameter. -/
abbrev PositiveError := { ε : ℝ // 0 < ε }

/-- A potential presentation of a current `T ∈ α`, admissible along `V`,
such that `T + εω` is positive.

The represented current is `θ + ddᶜ u`: `representative` is an actual closed
smooth real `(1,1)`-form representing `α`, while `potential_psh` says that
`θ + εω + ddᶜ u` is positive.  The last field rules out a potential that
is identically singular along `V`. -/
structure AdmissibleRestrictedCurrentPresentation
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) (epsilon : PositiveError) where
  /-- The smooth representative of the prescribed class. -/
  representative : ClosedRealOneOneForm n M
  represents : RealBottChern.ofRepresentative representative = alpha
  /-- The potential of the admissible current. -/
  potential : M → EReal
  potential_psh :
    IsThetaPshPotential
      (representative + (epsilon : ℝ) • omega.form).val potential
  smoothAnalyticSingularities :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) potential
  not_carrier_subset_poleSet : ¬ V.carrier ⊆ poleSet potential

/-- Placeholder input for the non-nef locus construction.

Only the class-indexed subsets are recorded.  This structure does not yet
assert that they are the Boucksom non-nef loci, nor any representative
independence, analyticity, or functoriality property. -/
structure NonNefLocusData (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] where
  /-- The exceptional subset associated with each class. -/
  locus : RealBottChern n M → Set M

/-- Placeholder input for the restricted absolutely-continuous top mass.

The value is attached to each actual admissible presentation.  Its intended
meaning as the integral over the regular locus of `V`, and the theorems needed
to compare presentations, are not yet implemented. -/
structure RestrictedACTopMassData (omega : KahlerBackground n M) where
  /-- The mass assigned to the top-degree product on the regular locus. -/
  topMass :
    ∀ {alpha : RealBottChern n M}
      {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError},
      AdmissibleRestrictedCurrentPresentation omega alpha V epsilon → ℝ≥0∞

/-- Supremum of the supplied candidate masses over all admissible
presentations at one positive error.  An empty family has supremum zero. -/
def restrictedMassEnvelope {omega : KahlerBackground n M}
    (massData : RestrictedACTopMassData omega) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) (epsilon : PositiveError) : ℝ≥0∞ :=
  ⨆ p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon,
    massData.topMass p

/-- A first-pass infimum formula for numerical restricted volume.

On a subvariety contained in the supplied non-nef locus it is zero.  Otherwise
it is the infimum, over all positive errors, of the presentation envelopes.
This is intentionally named `Inf`: no theorem here identifies this infimum
with the manuscript's right limit as `ε → 0⁺`.  The function is total on all
Bott--Chern classes; applications matching the manuscript must separately
assume pseudoeffectivity, and must not identify the current-theoretic notion
with the existing potential-based predicate without an equivalence theorem. -/
def numericalRestrictedVolumeInf {omega : KahlerBackground n M}
    (nonNef : NonNefLocusData n M) (massData : RestrictedACTopMassData omega)
    (alpha : RealBottChern n M) (V : ClosedIrreducibleAnalyticSubvariety n M) : ℝ≥0∞ := by
  classical
  exact if V.carrier ⊆ nonNef.locus alpha then 0
    else ⨅ epsilon : PositiveError, restrictedMassEnvelope massData alpha V epsilon

@[simp] theorem numericalRestrictedVolumeInf_eq_zero_of_subset_nonNef
    {omega : KahlerBackground n M} (nonNef : NonNefLocusData n M)
    (massData : RestrictedACTopMassData omega) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hV : V.carrier ⊆ nonNef.locus alpha) :
    numericalRestrictedVolumeInf nonNef massData alpha V = 0 := by
  simp [numericalRestrictedVolumeInf, hV]

theorem numericalRestrictedVolumeInf_eq_iInf_of_not_subset_nonNef
    {omega : KahlerBackground n M} (nonNef : NonNefLocusData n M)
    (massData : RestrictedACTopMassData omega) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hV : ¬ V.carrier ⊆ nonNef.locus alpha) :
    numericalRestrictedVolumeInf nonNef massData alpha V =
      ⨅ epsilon : PositiveError, restrictedMassEnvelope massData alpha V epsilon := by
  simp [numericalRestrictedVolumeInf, hV]

/-- Union of the positive-dimensional irreducible analytic subvarieties whose
first-pass numerical restricted volume is zero. -/
def nullLocusInf {omega : KahlerBackground n M}
    (nonNef : NonNefLocusData n M) (massData : RestrictedACTopMassData omega)
    (alpha : RealBottChern n M) : Set M :=
  ⋃ (V : ClosedIrreducibleAnalyticSubvariety n M) (_ : 0 < V.dim)
    (_ : numericalRestrictedVolumeInf nonNef massData alpha V = 0), V.carrier

@[simp] theorem mem_nullLocusInf {omega : KahlerBackground n M}
    {nonNef : NonNefLocusData n M} {massData : RestrictedACTopMassData omega}
    {alpha : RealBottChern n M} {x : M} :
    x ∈ nullLocusInf nonNef massData alpha ↔
      ∃ V : ClosedIrreducibleAnalyticSubvariety n M,
        0 < V.dim ∧
          numericalRestrictedVolumeInf nonNef massData alpha V = 0 ∧
          x ∈ V.carrier := by
  simp only [nullLocusInf, Set.mem_iUnion]
  constructor
  · rintro ⟨V, hdim, hzero, hx⟩
    exact ⟨V, hdim, hzero, hx⟩
  · rintro ⟨V, hdim, hzero, hx⟩
    exact ⟨V, hdim, hzero, hx⟩

theorem carrier_subset_nullLocusInf_of_volume_eq_zero
    {omega : KahlerBackground n M} {nonNef : NonNefLocusData n M}
    {massData : RestrictedACTopMassData omega} {alpha : RealBottChern n M}
    (V : ClosedIrreducibleAnalyticSubvariety n M) (hdim : 0 < V.dim)
    (hzero : numericalRestrictedVolumeInf nonNef massData alpha V = 0) :
    V.carrier ⊆ nullLocusInf nonNef massData alpha := by
  intro x hx
  exact mem_nullLocusInf.mpr ⟨V, hdim, hzero, hx⟩

theorem carrier_subset_nullLocusInf_of_subset_nonNef
    {omega : KahlerBackground n M} (nonNef : NonNefLocusData n M)
    (massData : RestrictedACTopMassData omega) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) (hdim : 0 < V.dim)
    (hV : V.carrier ⊆ nonNef.locus alpha) :
    V.carrier ⊆ nullLocusInf nonNef massData alpha :=
  carrier_subset_nullLocusInf_of_volume_eq_zero V hdim
    (numericalRestrictedVolumeInf_eq_zero_of_subset_nonNef
      nonNef massData alpha V hV)

end

end SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
