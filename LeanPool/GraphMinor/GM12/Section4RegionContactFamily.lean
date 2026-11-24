/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section4RegionContactDisc
import LeanPool.GraphMinor.GM12.Section4RegionContactSeparation

/-!
# Simultaneous contact discs in eye regions

The eye regions in XII (4.5), page 253, are distinct and have
pairwise disjoint marked sets. Choose a contact disc in each
region. A second region ensures that its closure is proper,
and the contact separation lemma makes all chosen discs
disjoint while retaining their original boundary parameters.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The simultaneous geometric preparation of the target discs
for XII (4.5), page 253. -/
theorem exists_region_contact_family
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {ι : Type*} [Nontrivial ι]
    (r N : ι → Set S) (Z : Set S)
    (hr : ∀ i, IsOpenDisc (r i))
    (hrr : Pairwise (fun i j => Disjoint (r i) (r j)))
    (hC : ∀ i, IsOArc (frontier (r i)))
    (hrZ : ∀ i, Disjoint (r i) Z)
    (hbdZ : ∀ i, frontier (r i) ⊆ Z)
    (hNZ : ∀ i, N i ⊆ Z) (hNb : ∀ i, N i ⊆ frontier (r i))
    (hfin : ∀ i, (N i).Finite) (hne : ∀ i, (N i).Nonempty)
    (hNN : Pairwise (fun i j => Disjoint (N i) (N j)))
    (φ : ∀ i, Circle ≃ₜ frontier (r i)) :
    ∃ (D : ι → Set S) (q : ι → Circle → S),
      (∀ i, IsClosedDisc (D i)) ∧
      Pairwise (fun i j => Disjoint (D i) (D j)) ∧
      (∀ i, D i ⊆ closure (r i) ∧ D i ∩ Z = N i ∧ N i ⊆ discBd (D i)) ∧
      (∀ i, Continuous (q i) ∧ Function.Injective (q i) ∧ range (q i) = discBd (D i)) ∧
      ∀ i w, (φ i w).val ∈ N i → q i w = (φ i w).val := by
  classical
  have hproper : ∀ i, closure (r i) ≠ univ := by
    intro i
    obtain ⟨j, hji⟩ := exists_ne i
    obtain ⟨f⟩ := (hr j).2
    have hrjne : (r j).Nonempty :=
      ⟨(f ⟨0, by simp [OpenUnitDisc]⟩).val,
        (f ⟨0, by simp [OpenUnitDisc]⟩).property⟩
    exact closure_ne_univ_of_disjoint_open_nonempty (hr j).1 hrjne (hrr hji.symm)
  have hex := fun i => exists_region_contact_disc hS (hr i) (hC i) (hproper i)
    (hrZ i) (hNZ i) (hNb i) (hfin i) (hne i) (φ i)
  choose D q hD hDr hDZ hND hqc hqi hqr hfix using hex
  refine ⟨D, q, hD, ?_, fun i => ⟨hDr i, hDZ i, hND i⟩,
    fun i => ⟨hqc i, hqi i, hqr i⟩, hfix⟩
  intro i j hij
  exact contact_discs_disjoint_of_regions_disjoint (hr i).1 (hrr hij) (hbdZ i)
    (hDr i) (hDr j) (hDZ i) (hDZ j) (hNN hij)

end GraphMinor.GM12
