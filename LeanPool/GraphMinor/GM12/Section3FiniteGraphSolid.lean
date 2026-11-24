/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.SurfaceGraph
public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM12.Section3SolidConnections
import Mathlib.Topology.Algebra.Module.LocallyConvex
import LeanPool.GraphMinor.Surface.ArcErase
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# Finite graph carriers are solid

The Section 8 reduction of VII used in XII (3.1), page 245, applies
the planar criterion to its finite graph shapes. Parametrize each
edge by a closed interval and include the finitely many vertices.
The resulting map from a finite disjoint union is a compact quotient.
Local path-connectedness passes to the quotient, giving the paper's
local arc-connectedness. The finite graph carrier is also closed.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A finite graph carrier is solid, with local arc-connectedness
proved through its compact interval parametrizations. -/
theorem isSolid_gr_of_isGraph
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (h : Surface.IsGraph V E) : IsSolid (gr V E) := by
  classical
  let : Fintype V := h.fin.fintype
  let : Fintype E := h.fine.fintype
  let : LocallyPathConnectedSpace unitInterval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  have hpar : ∀ e : E, Nonempty (unitInterval ≃ₜ e.val) := by
    intro e
    obtain ⟨a, b, _, hL, _⟩ := h.edge e.val e.property
    obtain ⟨φ, _, _⟩ := hL
    exact ⟨φ⟩
  let φ : ∀ e : E, unitInterval ≃ₜ e.val := fun e => Classical.choice (hpar e)
  let M := (Σ _ : E, unitInterval) ⊕ V
  let f : M → gr V E := fun m => match m with
    | .inl ⟨e, t⟩ => ⟨(φ e t).val, Or.inr ⟨e.val, e.property, (φ e t).property⟩⟩
    | .inr v => ⟨v.val, Or.inl v.property⟩
  have hfcval : Continuous (fun m : M => (f m).val) := by
    apply continuous_sum_dom.mpr
    constructor
    · apply continuous_sigma
      intro e
      change Continuous (fun t : unitInterval => (φ e t).val)
      exact continuous_subtype_val.comp (φ e).continuous
    · change Continuous (fun v : V => v.val)
      exact continuous_subtype_val
  have hfc : Continuous f := hfcval.subtype_mk _
  have hfs : Function.Surjective f := by
    intro y
    rcases y.property with hyV | hyE
    · exact ⟨.inr ⟨y.val, hyV⟩, rfl⟩
    · obtain ⟨e, he, hye⟩ := hyE
      let z : E := ⟨e, he⟩
      refine ⟨.inl ⟨z, (φ z).symm ⟨y.val, hye⟩⟩, ?_⟩
      apply Subtype.ext
      change (φ z ((φ z).symm ⟨y.val, hye⟩)).val = y.val
      exact congrArg Subtype.val ((φ z).apply_symm_apply ⟨y.val, hye⟩)
  have hquot := hfc.isClosedMap.isQuotientMap hfc hfs
  let : LocallyPathConnectedSpace (gr V E) := hquot.locallyPathConnectedSpace
  exact ⟨isLocallyArcConnected_of_locallyPathConnectedSpace, h.isClosed_gr⟩

/-- A circle is solid. Its finite graph presentation comes from the
proved curve-addition construction, so its local arc-connectedness
uses the same compact quotient argument as other finite shapes. -/
theorem isSolid_oArc
    {S : Type*} [TopologicalSpace S] [T2Space S] {F : Set S} (hF : IsOArc F) : IsSolid F := by
  have h0 : gr (∅ : Set S) ∅ = ∅ := by simp [gr]
  have hfin : FinConn (F \ gr (∅ : Set S) ∅) := by
    rw [h0, sdiff_empty]
    exact finConn_of_isPreconnected hF.isPreconnected
  obtain ⟨V, E, _, hG, hcarrier, _⟩ := isGraph_empty.add_curve hF hfin
  rw [h0, empty_union] at hcarrier
  have hsolid := isSolid_gr_of_isGraph hG
  exact hcarrier ▸ hsolid

end GraphMinor.GM12
