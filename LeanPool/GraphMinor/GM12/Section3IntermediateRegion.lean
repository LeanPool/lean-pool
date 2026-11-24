/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.Section5

/-!
# An intermediate region between two distant regions

For the two-disc sphere case of XII (3.2), page 247, follow the
regions from the first prescribed region to the second. XI (5.1)
supplies the step leaving the regions at distance less than the
chosen threshold. The two regions at this step share an edge and
therefore an end vertex. Their distance is at most two. The region
after this step has distance between the threshold and threshold
plus one, and the triangle inequality separates it from the other
prescribed region as well.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM14

/-- The intermediate region chosen in the two-disc case of XII
(3.2), page 247. -/
theorem exists_intermediate_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ η : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    (hη : 1 ≤ η) {r₁ r₂ : Set S} (hr₁ : r₁ ∈ Γ.R) (hr₂ : r₂ ∈ Γ.R)
    (hfar : 2 * η + 1 ≤ d r₁ r₂) :
    ∃ r ∈ Γ.R, η ≤ d r₁ r ∧ d r₁ r ≤ η + 1 ∧ η ≤ d r₂ r := by
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  have hrefl := h91.2.1
  have hsym := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have hvr := h91.2.2.2.2.2.1
  let O := Γ.span ∅ ∅
  have hOU : O.U = ∅ := by simp [O, Drawing.span_U, Drawing.spanU, Drawing.spanV]
  have hOR : univ ∈ O.R := by
    obtain ⟨x, _⟩ := region_nonempty hr₁
    apply (mem_R_iff O).mpr
    refine ⟨x, by simp [hOU], ?_⟩
    simp only [hOU, sdiff_empty]
    simp only [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
  let Z : Set (Set S) := {r | d r₁ r < η}
  have hr₁Z : r₁ ∈ Z := by
    change d r₁ r₁ < η
    rw [hrefl r₁ (Or.inr hr₁)]
    exact hη
  have hr₂Z : r₂ ∉ Z := by
    change ¬ d r₁ r₂ < η
    omega
  obtain ⟨e, he, _, a, b, haZ, hbZ, _, _, hea, heb⟩ :=
    GM11.theorem_5_1_proof hS (Γ.span_isSubdrawing ∅ ∅) hOR hr₁ hr₁Z hr₂ hr₂Z
      (subset_univ _) (subset_univ _)
  obtain ⟨v, hvV, hve⟩ : ∃ v ∈ Γ.V, v ∈ closure e := by
    rcases Γ.edge_cond e he with ⟨v, w, _, hcap, _⟩ | ⟨v, hcap, _⟩
    · have hv : v ∈ closure e ∩ Γ.V := hcap.symm.subset (by simp)
      exact ⟨v, hv.2, hv.1⟩
    · have hv : v ∈ closure e ∩ Γ.V := hcap.symm.subset (by simp)
      exact ⟨v, hv.2, hv.1⟩
  have hva : v ∈ closure a := (closure_minimal (edge_subset_closure_of_incident hS hea.1 hea.2.1
    hea.2.2)
    isClosed_closure) hve
  have hvb : v ∈ closure b := (closure_minimal (edge_subset_closure_of_incident hS heb.1 heb.2.1
    heb.2.2)
    isClosed_closure) hve
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hvV, rfl⟩)
  have hstep : d a b ≤ 2 := by
    have h := htri a (Or.inr hea.2.1) {v} hvA b (Or.inr heb.2.1)
    rw [hsym a (Or.inr hea.2.1) {v} hvA] at h
    exact h.trans (Nat.add_le_add (hvr ⟨e, he⟩ v hvV a hea.2.1 hva)
      (hvr ⟨e, he⟩ v hvV b heb.2.1 hvb))
  have hab := htri r₁ (Or.inr hr₁) a (Or.inr hea.2.1) b (Or.inr heb.2.1)
  have hbr : η ≤ d r₁ b := Nat.le_of_not_gt hbZ
  have har : d r₁ a < η := haZ
  have hupper : d r₁ b ≤ η + 1 := by omega
  have hback := htri r₁ (Or.inr hr₁) b (Or.inr heb.2.1) r₂ (Or.inr hr₂)
  rw [hsym b (Or.inr heb.2.1) r₂ (Or.inr hr₂)] at hback
  exact ⟨b, heb.2.1, hbr, hupper, by omega⟩

end GraphMinor.GM12
