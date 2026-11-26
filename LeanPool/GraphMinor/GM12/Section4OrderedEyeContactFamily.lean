/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.Surface.CircleMove
import LeanPool.GraphMinor.GM12.Section4EyeContactFamily
import LeanPool.GraphMinor.GM12.Section4EyeBoundaryParameters
import LeanPool.GraphMinor.GM11.Separate
import Mathlib.Order.Fin.Basic

/-!
# Ordered contact discs for the eye data

XII (4.5), pages 252--253, specifies the order of four vertices
on each eye circuit. Use that order to parametrize the region
boundary, then shrink the region closure while fixing the
four parameters. This gives disjoint target discs with exactly
the ordered marks required by claim (1).
-/

public section

namespace GraphMinor.GM12

open Set Surface GM14

/-- The ordered target-disc preparation in XII (4.5), page 253,
from the actual circuits and vertices of the eye regions. -/
theorem exists_ordered_eye_contact_family
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} (hcell : Γ.IsTwoCell)
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {δ : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T δ) (hE : Γ.E.Nonempty)
    {t : ℕ} (ht : 2 ≤ t) (r : Fin t → Set S) (C : Fin t → Drawing S)
    (a b c d : Fin t → S) (hr : ∀ i, r i ∈ Γ.R) (hri : Function.Injective r)
    (hfar : ∀ i j, i ≠ j → 3 ≤ δ (r i) (r j))
    (hC : ∀ i, (C i).IsCircuit) (hCG : ∀ i, (C i).IsSubdrawing Γ)
    (hCr : ∀ i, (C i).U = subBd (r i))
    (hmarks : ∀ i, a i ∈ (C i).V ∧ b i ∈ (C i).V ∧
      c i ∈ (C i).V ∧ d i ∈ (C i).V)
    (horder : ∀ i, OccurInCircuitOrder (C i) (a i) (b i) (c i) (d i)) :
    ∃ (D : Fin t → Set S) (q : Fin t → Circle → S) (β : Fin t → Fin 4 → ℝ),
      (∀ i, IsClosedDisc (D i)) ∧ Pairwise (fun i j => Disjoint (D i) (D j)) ∧
      (∀ i, D i ⊆ closure (r i) ∧ D i ∩ Γ.U = {a i, b i, c i, d i} ∧
        ({a i, b i, c i, d i} : Set S) ⊆ discBd (D i)) ∧
      (∀ i, Continuous (q i) ∧ Function.Injective (q i) ∧ range (q i) = discBd (D i)) ∧
      (∀ i, StrictMono (β i)) ∧ (∀ i j, β i j ∈ Ico 0 1) ∧
      ∀ i, q i (ee (β i 0)) = a i ∧ q i (ee (β i 1)) = b i ∧
        q i (ee (β i 2)) = c i ∧ q i (ee (β i 3)) = d i := by
  classical
  let : Nontrivial (Fin t) := Fin.nontrivial_iff_two_le.mpr ht
  have hCf : ∀ i, (C i).U = frontier (r i) := by
    intro i
    rw [hCr i, frontier_eq_closure_inter_closure, subBd, compl_eq_univ_sdiff]
  have hex := fun i => exists_eye_boundary_parameters (horder i)
  choose φ β hβ hβ01 ha hb hc hd using hex
  let ψ : ∀ i, Circle ≃ₜ frontier (r i) := fun i =>
    (φ i).trans (Homeomorph.setCongr (hCf i))
  let N : Fin t → Set S := fun i => {a i, b i, c i, d i}
  have hNV : ∀ i, N i ⊆ Γ.V := by
    intro i x hx
    rcases hx with rfl | rfl | rfl | hx
    · exact (hCG i).1 (hmarks i).1
    · exact (hCG i).1 (hmarks i).2.1
    · exact (hCG i).1 (hmarks i).2.2.1
    · exact (mem_singleton_iff.mp hx) ▸ (hCG i).1 (hmarks i).2.2.2
  have hNb : ∀ i, N i ⊆ frontier (r i) := by
    intro i x hx
    rw [← hCf i]
    rcases hx with rfl | rfl | rfl | hx
    · exact (C i).V_subset_U (hmarks i).1
    · exact (C i).V_subset_U (hmarks i).2.1
    · exact (C i).V_subset_U (hmarks i).2.2.1
    · exact (mem_singleton_iff.mp hx) ▸ (C i).V_subset_U (hmarks i).2.2.2
  obtain ⟨D, q, hD, hDD, hDN, hq, hfix⟩ := exists_eye_contact_family hS hcell hm hE r N
    hr hri hfar (fun i => hCf i ▸ GM11.IsCircuit.isOArc_U (hC i))
    hNV hNb (fun i => Set.toFinite (N i)) (fun i => ⟨a i, by simp [N]⟩) ψ
  refine ⟨D, q, β, hD, hDD, hDN, hq, hβ, hβ01, ?_⟩
  intro i
  have hψ : ∀ w, (ψ i w).val = (φ i w).val := fun _ => rfl
  have hfa : q i (ee (β i 0)) = a i := by
    rw [hfix i _ (by rw [hψ, ha i]; simp [N]), hψ, ha i]
  have hfb : q i (ee (β i 1)) = b i := by
    rw [hfix i _ (by rw [hψ, hb i]; simp [N]), hψ, hb i]
  have hfc : q i (ee (β i 2)) = c i := by
    rw [hfix i _ (by rw [hψ, hc i]; simp [N]), hψ, hc i]
  have hfd : q i (ee (β i 3)) = d i := by
    rw [hfix i _ (by rw [hψ, hd i]; simp [N]), hψ, hd i]
  exact ⟨hfa, hfb, hfc, hfd⟩

end GraphMinor.GM12
