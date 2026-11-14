/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.BoxGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.BoundaryFreezingRadius

/-!
# ContinuousCoeffResolvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Ellipticity bounds for a continuous coefficient

A coefficient with scalar symmetric part `nu * I` and continuous skew part is
elliptic on every compact set, with an upper constant that compactness
supplies.  The closed axis cube and the closure of a bounded domain are
compact, so on those two carriers the ellipticity certificate is a consequence
of the continuity hypothesis and need not be assumed.

This file names the compact, cube, and bounded-domain ellipticity certificates
supplied by continuity.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity

noncomputable section

variable {d : ℕ}

/-! ## 1. Two compact carriers -/

/-- The coordinatewise closure of an axis cube is compact. -/
theorem isCompact_memAxisCubeClosure (z : Vec d) (L : ℝ) :
    IsCompact {x | MemAxisCubeClosure z L x} := by
  have hset : {x | MemAxisCubeClosure z L x} =
      Set.pi Set.univ fun i => Set.Icc (z i) (z i + L) := by
    ext x
    simp only [MemAxisCubeClosure, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      Set.mem_Icc, forall_const]
  rw [hset]
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-- The closure of a bounded domain is compact. -/
theorem isCompact_closure_of_isBoundedDomain {U : Set (Vec d)}
    (hU : IsBoundedDomain U) : IsCompact (closure U) := by
  obtain ⟨R, -, hRU⟩ := hU
  have hsub : U ⊆ Set.pi Set.univ fun _ : Fin d => Set.Icc (-R) R := by
    intro x hx i _
    exact abs_le.mp (hRU x hx i)
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin d => Set.Icc (-R) R) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hboxClosed : IsClosed (Set.pi Set.univ fun _ : Fin d => Set.Icc (-R) R) :=
    isClosed_set_pi fun _ _ => isClosed_Icc
  exact hbox.of_isClosed_subset isClosed_closure (closure_minimal hsub hboxClosed)

/-! ## 2. The ellipticity witness supplied by continuity -/

/-- The upper ellipticity constant of a coefficient with scalar symmetric part
and continuous skew part on a compact set. -/
def compactEllipticUpper {W K : Set (Vec d)} (hW : MeasurableSet W)
    (hK : IsCompact K) (hWK : W ⊆ K) {nu : ℝ} (hnu : 0 < nu)
    {a : CoeffField d} (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) K) : ℝ :=
  Classical.choose (exists_isEllipticFieldOn_of_symmPart_eq_of_isCompact
    hW hK hWK hnu hsymm hcont)

/-- The ellipticity certificate that the constant names. -/
theorem isEllipticFieldOn_compactEllipticUpper {W K : Set (Vec d)}
    (hW : MeasurableSet W) (hK : IsCompact K) (hWK : W ⊆ K) {nu : ℝ}
    (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) K) :
    IsEllipticFieldOn nu (compactEllipticUpper hW hK hWK hnu hsymm hcont) W a :=
  Classical.choose_spec (exists_isEllipticFieldOn_of_symmPart_eq_of_isCompact
    hW hK hWK hnu hsymm hcont)

/-- The upper ellipticity constant on an axis cube. -/
def axisCubeEllipticUpper (z : Vec d) (L : ℝ) {nu : ℝ} (hnu : 0 < nu)
    {a : CoeffField d} (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d))
      {x | MemAxisCubeClosure z L x}) : ℝ :=
  compactEllipticUpper (isOpen_axisCube z L).measurableSet
    (isCompact_memAxisCubeClosure z L) (axisCube_subset_closureSet z L)
    hnu hsymm hcont

/-- **An axis-cube ellipticity certificate from continuity alone.** -/
theorem isEllipticFieldOn_axisCubeEllipticUpper (z : Vec d) (L : ℝ) {nu : ℝ}
    (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d))
      {x | MemAxisCubeClosure z L x}) :
    IsEllipticFieldOn nu (axisCubeEllipticUpper z L hnu hsymm hcont)
      (axisCube z L) a :=
  isEllipticFieldOn_compactEllipticUpper (isOpen_axisCube z L).measurableSet
    (isCompact_memAxisCubeClosure z L) (axisCube_subset_closureSet z L)
    hnu hsymm hcont

/-- The upper ellipticity constant on a bounded domain. -/
def domainEllipticUpper {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {nu : ℝ} (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) (closure U)) : ℝ :=
  compactEllipticUpper hU.isOpen.measurableSet
    (isCompact_closure_of_isBoundedDomain hU.isBoundedDomain) subset_closure
    hnu hsymm hcont

/-- **A bounded-domain ellipticity certificate from continuity alone.** -/
theorem isEllipticFieldOn_domainEllipticUpper {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {nu : ℝ} (hnu : 0 < nu)
    {a : CoeffField d} (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) (closure U)) :
    IsEllipticFieldOn nu (domainEllipticUpper hU hnu hsymm hcont) U a :=
  isEllipticFieldOn_compactEllipticUpper hU.isOpen.measurableSet
    (isCompact_closure_of_isBoundedDomain hU.isBoundedDomain) subset_closure
    hnu hsymm hcont

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
