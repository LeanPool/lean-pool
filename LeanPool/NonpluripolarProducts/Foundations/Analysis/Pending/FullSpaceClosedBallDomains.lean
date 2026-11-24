/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.FullSpaceLocalCurrent

/-!
# Domains for the full-space closed-ball transport

A local potential is available on a chart open `U`, while a full-dimensional
regular patch is biholomorphic only on its flattening source.  This file records
their literal intersection and its parameter preimage.  These are the two
open sets used by the closed-ball change-of-variables argument.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending.FullSpaceClosedBallDomains

open FirstPass FirstPass.NumericalRestrictedVolume
  FirstPass.AdmissibleCurrentFormPositivity
open FullSpaceRegularPatch

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The honest coordinate domain on which both the chosen smooth potential and
flattening inverse are available. -/
def regularPotentialDomain
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) : Opens (ComplexModel n) :=
  U ⊓ flatteningSource P

/-- Parameters whose full-space regular parametrization lies in the chosen
local-potential coordinate domain. -/
def regularParameterDomain
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) : Opens (ComplexModel n) :=
  ⟨(fullParameterDomain P : Set (ComplexModel n)) ∩
      P.coordinateParametrization ⁻¹' (U : Set (ComplexModel n)),
    (coordinateParametrization_isBiholomorphic P).holo.continuousOn.isOpen_inter_preimage
      (fullParameterDomain P).isOpen U.isOpen⟩

/-- Membership in the parameter domain is exactly membership in the regular
parameter domain together with membership in the local potential domain. -/
theorem mem_regularParameterDomain_iff
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) (w : ComplexModel n) :
    w ∈ regularParameterDomain P U ↔
      w ∈ fullParameterDomain P ∧ P.coordinateParametrization w ∈ U := by
  constructor
  · intro hw
    exact hw
  · rintro ⟨hw, hwU⟩
    exact ⟨hw, hwU⟩

end SGPT.Foundations.Analysis.Pending.FullSpaceClosedBallDomains
