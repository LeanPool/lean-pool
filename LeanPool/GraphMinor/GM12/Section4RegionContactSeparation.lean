/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs

/-!
# Separation of contact discs in distinct regions

For XII (4.5), page 253, two contact discs in distinct regions
can meet only in their marked boundary sets. Disjoint marked
sets therefore give disjoint discs. A second nonempty open
region also ensures that the first region is not dense.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Another nonempty open region prevents a region from being
dense. This is the properness condition used to close eye regions. -/
theorem closure_ne_univ_of_disjoint_open_nonempty
    {S : Type*} [TopologicalSpace S] {r s : Set S}
    (hs : IsOpen s) (hne : s.Nonempty) (hrs : Disjoint r s) :
    closure r ≠ univ := by
  intro heq
  obtain ⟨x, hx⟩ := hne
  exact disjoint_left.mp (hrs.closure_left hs) (heq.symm ▸ mem_univ x) hx

/-- Contact discs lying in closures of disjoint regions are
disjoint when their boundary contact sets are disjoint. -/
theorem contact_discs_disjoint_of_regions_disjoint
    {S : Type*} [TopologicalSpace S] {r s Z D E N M : Set S}
    (hr : IsOpen r) (hrs : Disjoint r s) (hbd : frontier r ⊆ Z)
    (hD : D ⊆ closure r) (hE : E ⊆ closure s)
    (hDN : D ∩ Z = N) (hEM : E ∩ Z = M) (hNM : Disjoint N M) :
    Disjoint D E := by
  apply disjoint_left.mpr
  intro x hxD hxE
  have hxr : x ∉ r := fun hx =>
    disjoint_left.mp (hrs.closure_right hr) hx (hE hxE)
  have hxf : x ∈ frontier r := by
    rw [frontier, hr.interior_eq]
    exact ⟨hD hxD, hxr⟩
  have hxZ := hbd hxf
  exact disjoint_left.mp hNM (hDN.subset ⟨hxD, hxZ⟩) (hEM.subset ⟨hxE, hxZ⟩)

end GraphMinor.GM12
