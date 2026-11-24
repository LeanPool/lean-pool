/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Section4EndPartition
public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM12.Section4CrossingFeasibilityUniverses
import LeanPool.GraphMinor.GM12.Section4OrderedEyeContactFamily
import LeanPool.GraphMinor.GM12.Section4FourContactBoundary
import LeanPool.GraphMinor.GM12.Section4DiscConnections
import LeanPool.GraphMinor.GM12.Section4CrossingEndClasses
import LeanPool.GraphMinor.GM12.Section2NonemptyEdges

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# The endpoint connections for XII (4.5)

Choose the source subdivision and the threshold in (3.2),
with four marks per crossing. For the prescribed eye regions,
construct the ordered contact discs, apply claim (1), and then
apply (3.2) to its endpoint classes. All source geometry and
feasibility are proved before this application. The resulting
connected subdrawings contain the assigned ends of the two
external paths at each eye.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph GM14

universe u

/-- The endpoint-connection construction following claim (1) in
XII (4.5), page 253. Its only statement hypotheses are the cited
VII (7.5), (5.1), and (5.5). -/
theorem exists_eye_connections
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {p : ℕ} (hp : 4 ≤ p) :
    ∃ (W E : Type) (L : Graph W E) (κ : E × Bool → W) (t : ℕ)
      (σ : Fin t × Bool ≃ E) (N : ℕ),
      Finite W ∧ Finite E ∧ IsIsoMinor (GM16.completeGraph p) L ∧
      (∀ e, L.IsLink e (κ (e, false)) (κ (e, true))) ∧
      (∀ e, κ (e, false) ≠ κ (e, true)) ∧ 2 ≤ t ∧ 2 * Nat.card W + 3 ≤ N ∧
      (∀ w, ∃ i j, i ≠ j ∧ ∃ b c d e : Bool,
        κ (σ (i, b), c) = w ∧ κ (σ (j, d), e) = w) ∧
      ∀ (Γ : Drawing S) (θ : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (δ : Set S → Set S → ℕ) (r : Fin t → Set S) (C : Fin t → Drawing S)
        (a b c d : Fin t → S),
      Γ.IsTwoCell → HasTangleMetric Γ θ T δ → N ≤ θ →
      (∀ i, r i ∈ Γ.R) → Function.Injective r →
      (∀ i j, i ≠ j → N ≤ δ (r i) (r j)) →
      (∀ i, (C i).IsCircuit) → (∀ i, (C i).IsSubdrawing Γ) →
      (∀ i, (C i).U = subBd (r i)) →
      (∀ i, a i ∈ (C i).V ∧ b i ∈ (C i).V ∧ c i ∈ (C i).V ∧ d i ∈ (C i).V) →
      (∀ i, OccurInCircuitOrder (C i) (a i) (b i) (c i) (d i)) →
      (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ {a i, b i, c i, d i}) →
      ∃ (ends : E × Bool → S) (H : W → Drawing S),
        Function.Injective ends ∧ (∀ q, ends q ∈ Γ.V) ∧
        (∀ i b c, ends (σ (i, b), c) ∈ closure (r i)) ∧
        (∀ w, (H w).IsSubdrawing Γ) ∧ (∀ w, IsConnectedDrawing (H w)) ∧
        Pairwise (fun v w => Disjoint (H v).V (H w).V) ∧
        (∀ w, (H w).V ∩ range ends = edgeEndClass ends κ w) ∧
        (∀ i, ({ends (σ (i, false), false), ends (σ (i, false), true)} : Set S) = {a i, c i}) ∧
        (∀ i, ({ends (σ (i, true), false), ends (σ (i, true), true)} : Set S) = {b i, d i}) := by
  classical
  obtain ⟨W, E, L, κ, t, σ, hW, hE, hminor, hLV, hLE, hlink, hκne, ht, htwo, hsource⟩ :=
    theorem_4_5_claim_1_ordered_univ hS hp
  let : Finite W := hW
  let : Fintype W := Fintype.ofFinite W
  obtain ⟨η, hη, hconnect⟩ := exists_threshold_for_disc_connections hS t (4 * t)
  let N := max η (2 * Nat.card W + 3)
  have hNW : 2 * Nat.card W + 3 ≤ N := le_max_right _ _
  refine ⟨W, E, L, κ, t, σ, N, hW, hE, hminor, hlink, hκne, ht, hNW, htwo, ?_⟩
  intro Γ θ T δ r C a b c d hcell hm hθ hr hri hfar hC hCG hCr hmarks horder hfree
  have hN3 : 3 ≤ N := by omega
  have hEΓ : Γ.E.Nonempty := edges_nonempty_of_tangle_order_two hm.1.2.1 (by omega)
  obtain ⟨D, q, β, hD, hDD, hDN, hq, hβ, hβ01, hqmarks⟩ :=
    exists_ordered_eye_contact_family hS hcell hm hEΓ ht r C a b c d hr hri
      (fun i j hij => hN3.trans (hfar i j hij)) hC hCG hCr hmarks horder
  obtain ⟨ends, B, hinj, hB, hBB, hcontact, hp0, hp1⟩ := hsource D q β hD hDD hq hβ hβ01
  have hp0' : ∀ i, ({ends (σ (i, false), false), ends (σ (i, false), true)} : Set S) = {a i, c i}
    := by
    intro i
    rw [hp0 i, (hqmarks i).1, (hqmarks i).2.2.1]
  have hp1' : ∀ i, ({ends (σ (i, true), false), ends (σ (i, true), true)} : Set S) = {b i, d i}
    := by
    intro i
    rw [hp1 i, (hqmarks i).2.1, (hqmarks i).2.2.2]
  let M : Fin t → Set S := fun i => {a i, b i, c i, d i}
  have hMV : ∀ i, M i ⊆ Γ.V := by
    intro i x hx
    rcases hx with rfl | rfl | rfl | hx
    · exact (hCG i).1 (hmarks i).1
    · exact (hCG i).1 (hmarks i).2.1
    · exact (hCG i).1 (hmarks i).2.2.1
    · exact (mem_singleton_iff.mp hx) ▸ (hCG i).1 (hmarks i).2.2.2
  have hnorm := fun i => normal_disc_of_exact_boundary_contacts (hDN i).2.1 (hMV i) (hDN i).2.2
  have hbd : ∀ i, Γ.V ∩ discBd (D i) = M i := fun i => (hnorm i).2
  have hrange : range ends = ⋃ i, M i := by
    have hh := range_ends_eq_crossing_marks σ ends (fun i => ![a i, b i, c i, d i]) hp0' hp1'
    have hvec : ∀ i, range ![a i, b i, c i, d i] = M i := by
      intro i
      ext x
      simp [M, or_comm, or_left_comm]
    simpa only [hvec] using hh
  have hZ : discBoundaryVertices Γ D = range ends := by
    simp only [discBoundaryVertices, hbd, hrange]
  have hendM : ∀ i b c, ends (σ (i, b), c) ∈ M i := by
    intro i b' c'
    have hh : ends (σ (i, b'), c') ∈
        ({ends (σ (i, b'), false), ends (σ (i, b'), true)} : Set S) := by cases c' <;> simp
    cases b'
    · rw [hp0' i] at hh
      rcases hh with hh | hh
      · rw [hh]; simp [M]
      · rw [mem_singleton_iff.mp hh]; simp [M]
    · rw [hp1' i] at hh
      rcases hh with hh | hh
      · rw [hh]; simp [M]
      · rw [mem_singleton_iff.mp hh]; simp [M]
  have hends : ∀ z, ends z ∈ Γ.V := by
    rintro ⟨e, c'⟩
    obtain ⟨⟨i, b'⟩, rfl⟩ := σ.surjective e
    exact hMV i (hendM i b' c')
  have hinc : ∀ i b c, ends (σ (i, b), c) ∈ closure (r i) := by
    intro i b' c'
    have hmD := (hDN i).2.2 (hendM i b' c')
    exact (hDN i).1 (discBd_subset _ hmD)
  obtain ⟨H, hHs, hHc, hHH, hHZ⟩ := hconnect Γ θ T δ D r (edgeEndClass ends κ)
    (fun i => ⟨hD i, (hnorm i).1⟩) hDD
    (discBoundaryVertices_ncard_le_four D a b c d hbd)
    ((iUnion_edgeEndClass ends κ).trans hZ.symm)
    (fun v w hvw => disjoint_edgeEndClass ends κ hinj hvw)
    ⟨B, hB, hBB, hcontact⟩ ((le_max_left _ _).trans hθ) hm
    (fun i => ⟨hr i, (hDN i).1⟩)
    (fun i j hij => (le_max_left _ _).trans (hfar i j hij))
    (fun i => hbd i ▸ hfree i)
  refine ⟨ends, H, hinj, hends, hinc, hHs, hHc, hHH, ?_, hp0', hp1'⟩
  intro w
  simpa only [hZ] using hHZ w

end GraphMinor.GM12
