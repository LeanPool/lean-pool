/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Carrying feasible discs by a homeomorphism

In XII (4.3), claim (7), page 251, the vertex discs of a
drawing of the target graph are carried to the selected ends by
a homeomorphism of the surface. Homeomorphisms preserve the
discs, their disjointness, and their exact intersections with the
prescribed disc family. This file gives the transport calculation.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The transport calculation in XII (4.3), claim (7), page 251.
A homeomorphism carries feasible connecting discs to feasible
connecting discs, with the corresponding prescribed contacts. -/
theorem IsTopologicallyFeasible.image
    {S U : Type*} [TopologicalSpace S] [TopologicalSpace U]
    {t p : ℕ} {Δ : Fin t → Set S} {Zs : Fin p → Set S}
    (hf : IsTopologicallyFeasible Δ Zs) (e : S ≃ₜ U) :
    IsTopologicallyFeasible (fun i => e '' Δ i) (fun v => e '' Zs v) := by
  obtain ⟨D, hD, hdisj, hcontact⟩ := hf
  refine ⟨fun v => e '' D v, ?_, ?_, ?_⟩
  · intro v
    exact ((hD v).image e.continuous.continuousOn e.symm.continuous.continuousOn
      (fun _ _ => e.symm_apply_apply _)).1
  · intro v w hvw
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have hyz : y = z := e.injective (hyx.trans hzx.symm)
    exact Set.disjoint_left.mp (hdisj v w hvw) hy (hyz.symm ▸ hz)
  · intro v
    rw [← image_iUnion, ← Set.image_inter e.injective, hcontact v]

/-- Specifying the images of the prescribed discs and contact
classes gives the target feasibility condition in XII (4.3). -/
theorem topologicallyFeasible_of_homeomorph
    {S U : Type*} [TopologicalSpace S] [TopologicalSpace U]
    {t p : ℕ} {Δ : Fin t → Set S} {Zs : Fin p → Set S}
    {Δ' : Fin t → Set U} {Zs' : Fin p → Set U}
    (hf : IsTopologicallyFeasible Δ Zs) (e : S ≃ₜ U)
    (hΔ : ∀ i, e '' Δ i = Δ' i) (hZ : ∀ v, e '' Zs v = Zs' v) :
    IsTopologicallyFeasible Δ' Zs' := by
  have he := hf.image e
  have hΔ' : (fun i => e '' Δ i) = Δ' := funext hΔ
  have hZ' : (fun v => e '' Zs v) = Zs' := funext hZ
  rwa [hΔ', hZ'] at he

end GraphMinor.GM12
