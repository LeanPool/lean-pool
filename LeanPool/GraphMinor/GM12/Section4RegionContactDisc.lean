/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section4RegionFrontier
import LeanPool.GraphMinor.GM12.Section4ContactDiscUniverses

/-!
# Contact discs inside eye regions

XII (4.5), page 253, applies the feasibility construction to
four boundary vertices of each eye region. Shrink its closure
while retaining those points and their boundary parameters.
The smaller disc meets the drawing only at the chosen points,
since the region itself misses the drawing.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A non-dense disc region supplies a contact disc retaining
a given circle parametrization at a finite nonempty set of
boundary marks. The set `Z` represents the drawing. -/
theorem exists_region_contact_disc {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {r Z N : Set S} (hr : IsOpenDisc r) (hC : IsOArc (frontier r))
    (hproper : closure r ≠ univ) (hZ : Disjoint r Z)
    (hNZ : N ⊆ Z) (hN : N ⊆ frontier r)
    (hfin : N.Finite) (hne : N.Nonempty)
    (φ : Circle ≃ₜ frontier r) :
    ∃ (Q : Set S) (q : Circle → S),
      IsClosedDisc Q ∧ Q ⊆ closure r ∧ Q ∩ Z = N ∧ N ⊆ discBd Q ∧
      Continuous q ∧ Function.Injective q ∧ range q = discBd Q ∧
      ∀ w, (φ w).val ∈ N → q w = (φ w).val := by
  obtain ⟨hD, hDb⟩ := closedDisc_closure_of_nondense_openDisc hS hr hC hproper
  let ψ : Circle ≃ₜ discBd (closure r) :=
    φ.trans (Homeomorph.setCongr hDb.symm)
  have hND : N ⊆ discBd (closure r) := hDb.symm ▸ hN
  obtain ⟨Q, q, hQ, hQD, hQN, hNb, hqc, hqi, hqr, hfix⟩ :=
    exists_contact_disc_preserving_param_univ hS hD ψ hND hfin hne
  have hQZ : Q ∩ Z = N := by
    apply Subset.antisymm
    · intro x hx
      have hxr : x ∉ r := fun h => disjoint_left.mp hZ h hx.2
      have hxb : x ∈ discBd (closure r) := by
        rw [hDb, frontier, hr.1.interior_eq]
        exact ⟨hQD hx.1, hxr⟩
      exact hQN ▸ ⟨hx.1, hxb⟩
    · intro x hx
      have hxb : x ∈ Q ∩ discBd (closure r) := hQN.symm ▸ hx
      exact ⟨hxb.1, hNZ hx⟩
  exact ⟨Q, q, hQ, hQD, hQZ, hNb, hqc, hqi, hqr, hfix⟩

end GraphMinor.GM12
