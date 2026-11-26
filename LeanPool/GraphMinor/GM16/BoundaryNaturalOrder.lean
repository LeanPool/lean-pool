/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM16.CircleListing
import LeanPool.GraphMinor.GM16.FiniteCircleCycle
import LeanPool.GraphMinor.GM16.CyclicOrderTransport
import LeanPool.GraphMinor.GM09.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Natural orders of finite boundary sets

Sort the finite boundary vertices by angles in a fixed circle
parametrization. Rotation of that listing gives the required cyclic
permutation. The construction proves its agreement with the circle,
including triples whose angles cross the cut of the parametrization.
This supplies the boundary orders of the rural neighborhood in
XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S]

/-- A nonempty finite set of points on a circle has a cyclic order
agreeing with any chosen parametrization of that circle. -/
theorem exists_cyclicPerm_agrees {F Y : Set S} (φ : Circle ≃ₜ F)
    (hY : Y.Finite) (hNe : Y.Nonempty) (hYF : Y ⊆ F) :
    ∃ Ω : CyclicPerm S, Ω.bar = Y ∧ AgreesWithOArcHomeo id Ω F φ :=
  exists_cyclicPerm_from_circle φ id hY hNe (Function.injective_id.injOn) (fun _ hx => hYF hx)

/-- The natural order of a nonempty finite set on an `O`-arc, in the
sense used for battlefield boundaries in XVI (8.1). -/
theorem exists_natural_order {F Y : Set S} (hF : IsOArc F)
    (hY : Y.Finite) (hNe : Y.Nonempty) (hYF : Y ⊆ F) :
    ∃ Ω : CyclicPerm S, Ω.bar = Y ∧ IsNaturalOrderFrom id Ω F := by
  obtain ⟨φ⟩ := hF
  obtain ⟨Ω, hbar, hAgree⟩ := exists_cyclicPerm_agrees φ hY hNe hYF
  exact ⟨Ω, hbar, ⟨φ⟩, φ, hAgree⟩

end GraphMinor.GM16
