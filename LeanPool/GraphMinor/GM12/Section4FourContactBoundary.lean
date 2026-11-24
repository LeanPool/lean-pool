/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Section3Punctured
import LeanPool.GraphMinor.Surface.SurfaceGraph
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Prod

/-!
# The boundary set of four-contact discs

XII (4.5), page 253, uses the connection theorem with at most
four marks for each eye. Exact contact with the drawing and
boundary containment make each disc normal. Enumerating the
four marks bounds the total boundary set by four times the
number of discs.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Exact contacts lying on the disc boundary give the normality
condition required by XII (3.2). -/
theorem normal_disc_of_exact_boundary_contacts
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {D N : Set S}
    (hcontact : D ∩ Γ.U = N) (hNV : N ⊆ Γ.V) (hNb : N ⊆ discBd D) :
    Γ.U ∩ D = Γ.V ∩ discBd D ∧ Γ.V ∩ discBd D = N := by
  have hbd : Γ.V ∩ discBd D = N := by
    apply Subset.antisymm
    · intro x hx
      exact hcontact.subset ⟨discBd_subset D hx.2, Γ.V_subset_U hx.1⟩
    · exact fun x hx => ⟨hNV hx, hNb hx⟩
  exact ⟨(inter_comm _ _).trans (hcontact.trans hbd.symm), hbd⟩

/-- Four contacts per disc give the parameter `z = 4t` used in
XII (4.5), page 253. -/
theorem discBoundaryVertices_ncard_le_four
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {t : ℕ}
    (D : Fin t → Set S) (a b c d : Fin t → S)
    (hbd : ∀ i, Γ.V ∩ discBd (D i) = {a i, b i, c i, d i}) :
    (discBoundaryVertices Γ D).ncard ≤ 4 * t := by
  let marks : Fin t × Fin 4 → S := fun q => ![a q.1, b q.1, c q.1, d q.1] q.2
  have hsub : discBoundaryVertices Γ D ⊆ marks '' univ := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [hbd i] at hi
    rcases hi with rfl | rfl | rfl | hi
    · exact ⟨(i, 0), mem_univ _, rfl⟩
    · exact ⟨(i, 1), mem_univ _, rfl⟩
    · exact ⟨(i, 2), mem_univ _, rfl⟩
    · exact ⟨(i, 3), mem_univ _, (mem_singleton_iff.mp hi).symm⟩
  have hc := (ncard_le_ncard hsub (toFinite _)).trans (ncard_image_le (toFinite univ))
  simpa only [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fin, Nat.mul_comm t 4] using hc

end GraphMinor.GM12
