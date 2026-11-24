/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.NonKahlerLocus
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.CoordinateDensityGeometry

/-!
# Numerical restricted volume and the null locus

The right-limit construction is modeled on the SGPT manuscript's restricted volume
and [Collins–Tosatti, §2](https://www.numdam.org/item/10.5802/afst.1708.pdf#page=8). The Lean admissible family
uses chartwise logarithmic presentations with a bounded remainder smooth off the poles.
The paper uses local generators of a coherent ideal and a remainder smooth throughout
the neighbourhood. The Lean definition uses the weaker admissibility criterion specified in
`NumericalRestrictedVolumeScaffold`.

## The absolutely continuous restricted top mass

Let `T = θ + ddᶜ u` be admissible at error `ε`
(`AdmissibleRestrictedCurrentPresentation`). The potential `u` has the chartwise
bounded, off-pole smooth logarithmic presentations, `T + εω ≥ 0`, and the pole set
`P` of `u` does not contain `V`.
Off `P` the potential is smooth, so `(T + εω)|_{V_reg \ P}` is a smooth
semipositive `(1,1)`-form.  Since `P ∩ V_reg` is a proper analytic subset of
the connected manifold part of `V_reg`, it is Lebesgue-null, and the absolutely
continuous part of the coefficients of `(T + εω)|_{V_reg}` is this smooth form
almost everywhere.  Hence
`∫_{V_reg} ((T + εω)|_{V_reg})_ac^k = ∫_{V_reg \ P} ((T + εω)|_{V_reg \ P})^k`.

The right-hand side is defined here without choosing a partition of unity.
A `RegularPatch` is a biholomorphic flattening of `V` at a regular point of the
certified dimension `k = V.dim` (the data of `RegularAtDim`), and gives the
holomorphic parametrization `w ↦ Φ⁻¹(w, 0)` of `V` near that point.  The top
power of the pulled-back form has the coordinate density
`MongeAmpere.actualTopPowerDensity` (a genuine wedge power evaluated on the
positively oriented real frame).  The mass `acTopMass` is the supremum, over
finite families of measurable coordinate pieces with pairwise disjoint images in
`V_reg \ P`, of the sums of the Lebesgue integrals of these densities.  Because
the density is nonnegative and holomorphic coordinate changes preserve
orientation, this supremum is the integral of the top-degree form over
`V_reg \ P`.

## Restricted volume and null locus

`numericalRestrictedVolume omega alpha V` is `0` if `V ⊆ E_nn(α)` and otherwise
the limit as `ε ↓ 0` of the supremum of `acTopMass` over admissible
presentations at error `ε` (`limUnder` along `𝓝[>] 0`).  The limit exists
because the envelope is nondecreasing in `ε` (an `ε`-admissible current is
`ε'`-admissible for `ε' > ε`, and `(T + ε'ω)^k ≥ (T + εω)^k`); this monotonicity is
the explicit obligation `Pending.RestrictedVolumeMonotonicity.restrictedMassEnvelope_mono`,
from which `numericalRestrictedVolume_eq_numericalRestrictedVolumeInf` there
identifies the limit with the scaffold's infimum `numericalRestrictedVolumeInf`.  `nullLocus` is
    the union of the positive-dimensional closed
irreducible analytic subvarieties with zero restricted volume.

These are new definitions of this first pass and are recorded in the blueprint
(`ana:restricted-volume`).
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume

noncomputable section

open PositiveClasses NumericalRestrictedVolumeScaffold NonKahlerLocus

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The inclusion `ℂ^k → ℂ^n`, `w ↦ (w, 0)`, onto the first `k` coordinates. -/
def planeInclusion (k n : ℕ) : ComplexModel k → ComplexModel n :=
  fun w => WithLp.toLp 2 (fun i : Fin n => if h : i.1 < k then w ⟨i.1, h⟩ else 0)

/-- A biholomorphic flattening of `V` onto `ℂ^{dim V} × {0}` near a regular point,
in the preferred chart at that point.  The fields are the data of
`RegularAtDim V.carrier center V.dim`. -/
structure RegularPatch (V : ClosedIrreducibleAnalyticSubvariety n M) where
  /-- The point at which the analytic subset is flattened. -/
  center : M
  center_mem : center ∈ V.carrier
  /-- The local holomorphic equivalence exhibiting the coordinate plane. -/
  flattening : LocalHolomorphicEquivAt (n := n)
    ((complexChartAt (n := n) center).val center)
  source_subset : flattening.source ⊆ (complexChartAt (n := n) center).val.target
  center_to_zero : flattening.toFun ((complexChartAt (n := n) center).val center) = 0
  flattens : ∀ {y : M},
    y ∈ (complexChartAt (n := n) center).val.source →
    (complexChartAt (n := n) center).val y ∈ flattening.source →
      (y ∈ V.carrier ↔
        flattening.toFun ((complexChartAt (n := n) center).val y) ∈
          complexCoordinatePlane n V.dim)

namespace RegularPatch

variable {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- Parameters `w ∈ ℂ^{dim V}` with `(w, 0)` in the flattened coordinates. -/
def parameterDomain (P : RegularPatch V) : Set (ComplexModel V.dim) :=
  {w | planeInclusion V.dim n w ∈ P.flattening.target}

/-- The coordinate parametrization `w ↦ Φ⁻¹(w, 0)` in the chart at the center. -/
def coordinateParametrization (P : RegularPatch V) :
    ComplexModel V.dim → ComplexModel n :=
  fun w => P.flattening.invFun (planeInclusion V.dim n w)

/-- The parametrization of `V` near the center, as a map into the manifold. -/
def toManifold (P : RegularPatch V) : ComplexModel V.dim → M :=
  fun w => (complexChartAt (n := n) P.center).val.symm (P.coordinateParametrization w)

end RegularPatch

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

/-- The smooth representative `θ + εω` of the perturbed class. -/
def perturbedRepresentative
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon) :
    ClosedRealOneOneForm n M :=
  p.representative + (epsilon : ℝ) • omega.form

/-- The coordinate two-form of `T + εω = θ + εω + ddᶜ u` in the chart `e`.  It is
the genuine form at points where the potential is finite, hence smooth. -/
def coordinateCurrentForm
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (e : ComplexChart n M) (z : ComplexModel n) : MongeAmpere.CoordinateRealTwoForm n :=
  (perturbedRepresentative p).val.coeff e z +
    smoothDDC (fun y => (p.potential (e.val.symm y)).toReal) z

/-- The density, in patch parameters, of the top power of the restriction of
`T + εω` to `V`. -/
def patchDensity
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) (w : ComplexModel V.dim) : ℝ :=
  MongeAmpere.actualTopPowerDensity
    ((coordinateCurrentForm p (complexChartAt (n := n) P.center)
        (P.coordinateParametrization w)).compContinuousLinearMap
      (fderiv ℝ P.coordinateParametrization w))

/-- Finitely many measurable parameter pieces whose images are pairwise disjoint
subsets of `V_reg` avoiding the set `avoid`. -/
structure RegularPieceFamily (V : ClosedIrreducibleAnalyticSubvariety n M)
    (avoid : Set M) where
  /-- The number of chart patches in the partition. -/
  size : ℕ
  /-- The regular-coordinate patch supporting each partition piece. -/
  patch : Fin size → RegularPatch V
  /-- The measurable coordinate piece associated with each patch. -/
  piece : Fin size → Set (ComplexModel V.dim)
  measurableSet_piece : ∀ i, MeasurableSet (piece i)
  piece_subset : ∀ i, piece i ⊆ (patch i).parameterDomain
  image_subset_regularLocus :
    ∀ i, (patch i).toManifold '' piece i ⊆ regularLocus (n := n) V.carrier V.dim
  image_disjoint_avoid : ∀ i, Disjoint ((patch i).toManifold '' piece i) avoid
  pairwise_disjoint_image : Pairwise fun i j =>
    Disjoint ((patch i).toManifold '' piece i) ((patch j).toManifold '' piece j)

/-- The absolutely continuous restricted top mass
`∫_{V_reg} ((T + εω)|_{V_reg})_ac^{dim V}`, computed on `V_reg` minus the pole set. -/
def acTopMass
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon) : ℝ≥0∞ :=
  ⨆ F : RegularPieceFamily V (poleSet p.potential),
    ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity p (F.patch i) w)

/-- The actual restricted absolutely continuous top mass, packaged as the
scaffold's mass input. -/
def acTopMassData (omega : KahlerBackground n M) : RestrictedACTopMassData omega where
  topMass := fun p => acTopMass p

/-- The numerical restricted volume `⟨α^{dim V}⟩_{X|V}`: zero on subvarieties
contained in `E_nn(α)`, and otherwise the right limit at `0` of the admissible
mass envelopes. -/
def numericalRestrictedVolume (omega : KahlerBackground n M)
    (alpha : RealBottChern n M) (V : ClosedIrreducibleAnalyticSubvariety n M) :
    ℝ≥0∞ := by
  classical
  exact if V.carrier ⊆ nonNefLocus omega alpha then 0
    else limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ =>
      if h : 0 < ε then restrictedMassEnvelope (acTopMassData omega) alpha V ⟨ε, h⟩
      else 0

theorem numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hV : V.carrier ⊆ nonNefLocus omega alpha) :
    numericalRestrictedVolume omega alpha V = 0 := by
  simp [numericalRestrictedVolume, hV]

/-- The null locus: the union of positive-dimensional closed irreducible analytic
subvarieties with zero numerical restricted volume. -/
def nullLocus (omega : KahlerBackground n M) (alpha : RealBottChern n M) : Set M :=
  ⋃ (V : ClosedIrreducibleAnalyticSubvariety n M) (_ : 0 < V.dim)
    (_ : numericalRestrictedVolume omega alpha V = 0), V.carrier

@[simp] theorem mem_nullLocus {omega : KahlerBackground n M}
    {alpha : RealBottChern n M} {x : M} :
    x ∈ nullLocus omega alpha ↔
      ∃ V : ClosedIrreducibleAnalyticSubvariety n M,
        0 < V.dim ∧ numericalRestrictedVolume omega alpha V = 0 ∧ x ∈ V.carrier := by
  simp only [nullLocus, Set.mem_iUnion, exists_prop]

end

end SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
