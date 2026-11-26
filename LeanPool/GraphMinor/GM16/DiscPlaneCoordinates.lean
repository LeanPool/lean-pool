/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM16.DiscChartExtension
import LeanPool.GraphMinor.GM16.DiscPlaneBoundary
import LeanPool.GraphMinor.GM11.Section7

/-!
# Plane coordinates on a surface disc

Compose the extended complex chart with the standard identification
of the complex plane and the Euclidean plane. The chart inverse
preserves every closed disc inside the chart, including its boundary.
These are the discs of the rural presentation in XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [CompactSpace S]

/-- A disc chart gives a continuous map to the Euclidean plane,
with a continuous inverse on the disc image. Every smaller closed disc
retains its boundary under this map. -/
theorem exists_plane_disc_coordinates {D : Set S} (hD : IsClosedDisc D) :
    ∃ (f : S → EuclideanPlane) (g : EuclideanPlane → S),
      Continuous f ∧ InjOn f D ∧ ContinuousOn g (f '' D) ∧ LeftInvOn g f D ∧
      ∀ E ⊆ D, IsClosedDisc E →
        IsClosedDisc (f '' E) ∧ subBd (f '' E) = f '' discBd E := by
  obtain ⟨h, k, hh, c, hi⟩ := exists_extended_disc_chart hD
  let e : ℂ ≃ₜ EuclideanPlane := complexPlane.toHomeomorph
  let f : S → EuclideanPlane := e ∘ h
  let g : EuclideanPlane → S := k ∘ e.symm
  have hf : Continuous f := e.continuous.comp hh
  have hinj : InjOn f D := fun x hx y hy heq => hi hx hy (e.injective heq)
  have hg : ContinuousOn g (f '' D) := by
    apply c.gc.comp e.symm.continuous.continuousOn
    rintro _ ⟨x, hx, rfl⟩
    simpa only [f, Function.comp_apply, Homeomorph.symm_apply_apply] using c.hm hx
  have hgf : LeftInvOn g f D := by
    intro x hx
    simpa only [f, g, Function.comp_apply, Homeomorph.symm_apply_apply] using c.gh hx
  refine ⟨f, g, hf, hinj, hg, hgf, ?_⟩
  intro E hED hE
  obtain ⟨hFE, hb⟩ := hE.image hf.continuousOn (hg.mono (image_mono hED))
    (fun _ hx => hgf (hED hx))
  exact ⟨hFE, by rw [GraphMinor.GM11.subBd_eq_frontier, plane_disc_frontier hFE, hb]⟩

end GraphMinor.GM16
