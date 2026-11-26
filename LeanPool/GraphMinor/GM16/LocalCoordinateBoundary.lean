/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs

/-!
# Local coordinate extrema prevent interior membership

An open coordinate projection sends a neighborhood to an open
set of the real line. It cannot have a greatest or least point.
Thus a local coordinate bound places its extreme points outside
the interior. Applied inside open horizontal strips, this checks
the straight outer wall sides in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology

/-- A local maximum of an open real coordinate cannot be an interior point. -/
theorem not_mem_interior_of_local_coordinate_max {X : Type*} [TopologicalSpace X]
    {A O : Set X} (hO : IsOpen O) {g : X → ℝ} (hg : IsOpenMap g)
    {p : X} {c : ℝ} (hpO : p ∈ O) (hpc : g p = c)
    (hBound : ∀ q ∈ A ∩ O, g q ≤ c) : p ∉ interior A := by
  intro hpInt
  have hOpen : IsOpen (g '' (interior A ∩ O)) := hg _ (isOpen_interior.inter hO)
  have hpImage : g p ∈ g '' (interior A ∩ O) := ⟨p,⟨hpInt,hpO⟩,rfl⟩
  have hSub : g '' (interior A ∩ O) ⊆ Iic c := by
    rintro y ⟨q,hq,rfl⟩
    exact hBound q ⟨interior_subset hq.1,hq.2⟩
  have hpRange : g p ∈ interior (Iic c) := interior_mono hSub (hOpen.interior_eq.symm ▸ hpImage)
  rw [interior_Iic,hpc] at hpRange
  exact (lt_irrefl c) hpRange

/-- The corresponding assertion for a local minimum. -/
theorem not_mem_interior_of_local_coordinate_min {X : Type*} [TopologicalSpace X]
    {A O : Set X} (hO : IsOpen O) {g : X → ℝ} (hg : IsOpenMap g)
    {p : X} {c : ℝ} (hpO : p ∈ O) (hpc : g p = c)
    (hBound : ∀ q ∈ A ∩ O, c ≤ g q) : p ∉ interior A := by
  intro hpInt
  have hOpen : IsOpen (g '' (interior A ∩ O)) := hg _ (isOpen_interior.inter hO)
  have hpImage : g p ∈ g '' (interior A ∩ O) := ⟨p,⟨hpInt,hpO⟩,rfl⟩
  have hSub : g '' (interior A ∩ O) ⊆ Ici c := by
    rintro y ⟨q,hq,rfl⟩
    exact hBound q ⟨interior_subset hq.1,hq.2⟩
  have hpRange : g p ∈ interior (Ici c) := interior_mono hSub (hOpen.interior_eq.symm ▸ hpImage)
  rw [interior_Ici,hpc] at hpRange
  exact (lt_irrefl c) hpRange

end GraphMinor.GM16
