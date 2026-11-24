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
    ∃ Ω : CyclicPerm S, Ω.bar = Y ∧ AgreesWithOArcHomeo id Ω F φ := by
  classical
  let : Fintype Y := hY.fintype
  have hCard : Fintype.card Y = Y.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  let e₀ : Fin Y.ncard ≃ Y := (finCongr hCard.symm).trans (Fintype.equivFin Y).symm
  let ν₀ : Fin Y.ncard → S := fun i => (e₀ i).val
  have hν₀ : Function.Injective ν₀ := Subtype.val_injective.comp e₀.injective
  obtain ⟨perm, τ, hPerm, hτ, hBounds, hEq⟩ := exists_increasing_circle_angles φ ν₀ hν₀
    (fun i => hYF (e₀ i).property)
  let e : Fin Y.ncard ≃ Y := (Equiv.ofBijective perm hPerm).trans e₀
  let Ω := cyclicPermOnSet hY e
  have hNeCard : 0 < Y.ncard := (Set.ncard_pos hY).mpr hNe
  have hEq' : ∀ i, (φ (Circle.exp (τ i))).val = (e i).val := hEq
  have hTurn : ∀ i, τ i < τ ⟨0, hNeCard⟩ + 2 * Real.pi := by
    intro i
    have hi := hBounds i
    have hzero := hBounds ⟨0, hNeCard⟩
    linarith
  have hAgreeFin := finCyclicPerm_agrees_of_angles φ hNeCard (fun i => (e i).val) τ hτ hTurn hEq'
  refine ⟨Ω, rfl, fun x hx => hYF hx, ?_⟩
  intro x y z hCW
  have hMem := CyclicPerm.isClockwise3_iff.mp hCW
  let i := e.symm ⟨x, hMem.2.2.2.1⟩
  let j := e.symm ⟨y, hMem.2.2.2.2.1⟩
  let k := e.symm ⟨z, hMem.2.2.2.2.2.1⟩
  have hi : (e i).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hMem.2.2.2.1⟩)
  have hj : (e j).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hMem.2.2.2.2.1⟩)
  have hk : (e k).val = z := congrArg Subtype.val (e.apply_symm_apply ⟨z, hMem.2.2.2.2.2.1⟩)
  have hCW' : (cyclicPermOnSet hY e).IsClockwise3 (e i).val (e j).val (e k).val := by
    rw [hi, hj, hk]
    exact hCW
  have hFin := (cyclicPermOnSet_clockwise3_iff hY e i j k).mp hCW'
  simpa only [hi, hj, hk, id_eq] using hAgreeFin.2 i j k hFin

/-- The natural order of a nonempty finite set on an `O`-arc, in the
sense used for battlefield boundaries in XVI (8.1). -/
theorem exists_natural_order {F Y : Set S} (hF : IsOArc F)
    (hY : Y.Finite) (hNe : Y.Nonempty) (hYF : Y ⊆ F) :
    ∃ Ω : CyclicPerm S, Ω.bar = Y ∧ IsNaturalOrderFrom id Ω F := by
  obtain ⟨φ⟩ := hF
  obtain ⟨Ω, hbar, hAgree⟩ := exists_cyclicPerm_agrees φ hY hNe hYF
  exact ⟨Ω, hbar, ⟨φ⟩, φ, hAgree⟩

end GraphMinor.GM16
