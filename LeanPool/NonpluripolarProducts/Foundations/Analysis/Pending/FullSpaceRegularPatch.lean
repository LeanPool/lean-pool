/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorHolomorphic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AnalyticIrreducibleComponents

/-!
# Full-dimensional regular patches

For a subvariety whose carrier is the whole ambient manifold, its certified
dimension is the ambient dimension.  A `RegularPatch` is then a genuine local
biholomorphic coordinate change, rather than a lower-dimensional
parametrization.  This file makes that change of type explicit.

The conversion matters for the ambient-mass argument: the Jacobian
change-of-variables theorem for Bedford--Taylor measures is stated for maps
between equal-dimensional coordinate models, whereas a general
`RegularPatch V` has source `ComplexModel V.dim`.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.FullSpaceRegularPatch

open FirstPass FirstPass.NumericalRestrictedVolume
  FirstPass.AdmissibleCurrentFormPositivity
open BedfordTaylor

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The canonical full-dimensional presentation of a subvariety already known
to be the whole ambient manifold.  Its dimension field is definitionally
`n`, avoiding casts in local change-of-variables statements. -/
def fullSpaceSubvariety (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hcarrier : V.carrier = univ) (hdim : V.dim = n) :
    ClosedIrreducibleAnalyticSubvariety n M where
  carrier := univ
  isClosed_carrier := isClosed_univ
  irreducible_carrier := by simpa only [hcarrier] using V.irreducible_carrier
  dim := n
  dim_le := le_rfl
  regularLocus_nonempty := by simpa only [hcarrier, hdim] using V.regularLocus_nonempty

/-- The canonical full-dimensional presentation is propositionally the
original subvariety. -/
theorem fullSpaceSubvariety_eq (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hcarrier : V.carrier = univ) (hdim : V.dim = n) :
    V = fullSpaceSubvariety V hcarrier hdim := by
  apply ClosedIrreducibleAnalyticSubvariety.ext hcarrier hdim

/-- At full dimension, the coordinate-plane inclusion is the identity. -/
theorem planeInclusion_self (w : ComplexModel n) : planeInclusion n n w = w := by
  ext i
  simp [planeInclusion]

/-- The parameter domain of a full-dimensional regular patch, bundled as an
open coordinate set. -/
def fullParameterDomain {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim)) :
    Opens (ComplexModel n) :=
  ⟨P.parameterDomain, RegularPatchDerivative.isOpen_parameterDomain P⟩

/-- The source of the flattening, bundled as its open coordinate set. -/
def flatteningSource {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim)) :
    Opens (ComplexModel n) :=
  ⟨P.flattening.source, P.flattening.isOpen_source⟩

/-- In the full-space case, the regular-patch parameterization and its
flattening are mutually inverse holomorphic maps between their actual open
domains.  This is the geometric input needed to apply
`IsBTLimit.comp_biholomorphic` and the underlying Jacobian formula to a
closed regular parameter ball. -/
theorem coordinateParametrization_isBiholomorphic
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim)) :
    IsBiholomorphicPair (fullParameterDomain P) (flatteningSource P)
      P.coordinateParametrization P.flattening.toFun := by
  have hdomain : (fullParameterDomain P : Set (ComplexModel n)) = P.flattening.target := by
    ext w
    change planeInclusion n n w ∈ P.flattening.target ↔ w ∈ P.flattening.target
    rw [planeInclusion_self]
  have hparam : P.coordinateParametrization = P.flattening.invFun := by
    funext w
    simp only [RegularPatch.coordinateParametrization]
    apply congrArg P.flattening.invFun
    ext i
    simp [planeInclusion, fullSpaceSubvariety]
  refine ⟨?_,
    contDiffOn_of_differentiableOn_complex P.flattening.toFun_holomorphic
      P.flattening.isOpen_source, ?_, ?_, ?_, ?_⟩
  · rw [hparam, hdomain]
    exact contDiffOn_of_differentiableOn_complex P.flattening.invFun_holomorphic
      P.flattening.isOpen_target
  · intro w hw
    change P.flattening.invFun (planeInclusion n n w) ∈ P.flattening.source
    exact P.flattening.mapsTo_invFun hw
  · intro z hz
    change planeInclusion n n (P.flattening.toFun z) ∈ P.flattening.target
    rw [planeInclusion_self]
    exact P.flattening.mapsTo_toFun hz
  · intro w hw
    change P.flattening.toFun (P.flattening.invFun (planeInclusion n n w)) = w
    rw [planeInclusion_self]
    exact P.flattening.right_inv w (hdomain ▸ hw)
  · intro z hz
    change P.flattening.invFun (planeInclusion n n (P.flattening.toFun z)) = z
    rw [planeInclusion_self, P.flattening.left_inv z hz]

end SGPT.Foundations.Analysis.Pending.FullSpaceRegularPatch
