/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46CentralLift
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.NetExists

/-!
# Walks from connected sets

The forest `H₆` of VII (4.6), page 227, is `H₅` with more vertices. To
compare their paths we use a plain fact: two vertices of a graph which lie
in a connected subset of its point set are joined by a walk. The vertices
joined to the first one, with the edges at them, form a closed set, as do
the other vertices with their edges. These two sets are disjoint and
cover the point set.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- Two vertices in a connected subset of `U(Γ)` are joined by a walk of `Γ`. -/
theorem exists_walk_of_preconnected (Γ : Drawing S) {A : Set S} (hA : IsPreconnected A)
    (hAU : A ⊆ Γ.U) {a b : S} (ha : a ∈ Γ.V) (haA : a ∈ A) (hb : b ∈ Γ.V) (hbA : b ∈ A) :
    Nonempty (GraphWalk Γ.toGraph a b) := by
  classical
  let Rv : Set S := {v | v ∈ Γ.V ∧ Nonempty (GraphWalk Γ.toGraph a v)}
  have hRa : a ∈ Rv := ⟨ha, ⟨.nil ha⟩⟩
  have hstep : ∀ e ∈ Γ.E, (closure e ∩ Rv).Nonempty → ∀ y ∈ closure e, y ∈ Γ.V → y ∈ Rv := by
    rintro e he ⟨r, hrc, hrV, ⟨W⟩⟩ y hy hyV
    by_cases hyr : y = r
    · exact hyr ▸ ⟨hrV, ⟨W⟩⟩
    have hcap : closure e ∩ Γ.V = {r, y} := by
      rcases Γ.edge_cond e he with ⟨u, v, -, hc, -⟩ | ⟨u, hc, -⟩
      · have h1 : r ∈ ({u, v} : Set S) := hc ▸ ⟨hrc, hrV⟩
        have h2 : y ∈ ({u, v} : Set S) := hc ▸ ⟨hy, hyV⟩
        rw [hc]
        rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
        · exact (hyr rfl).elim
        · rfl
        · exact pair_comm _ _
        · exact (hyr rfl).elim
      · have h1 : r ∈ ({u} : Set S) := hc ▸ ⟨hrc, hrV⟩
        have h2 : y ∈ ({u} : Set S) := hc ▸ ⟨hy, hyV⟩
        exact (hyr (h2.trans h1.symm)).elim
    have hl : Γ.toGraph.IsLink e r y := ⟨he, hrV, hyV, hcap⟩
    exact ⟨hyV, ⟨W.append (.cons hl (.nil hyV))⟩⟩
  let Et : Set (Set S) := {e ∈ Γ.E | (closure e ∩ Rv).Nonempty}
  let En : Set (Set S) := {e ∈ Γ.E | ¬(closure e ∩ Rv).Nonempty}
  let T₁ : Set S := Rv ∪ ⋃ e ∈ Et, closure e
  let T₂ : Set S := (Γ.V \ Rv) ∪ ⋃ e ∈ En, closure e
  have hRvfin : Rv.Finite := Γ.finite_V.subset fun _ hv => hv.1
  have hEtfin : Et.Finite := Γ.finite_edges.subset fun _ he => he.1
  have hEnfin : En.Finite := Γ.finite_edges.subset fun _ he => he.1
  have hT₁ : IsClosed T₁ :=
    hRvfin.isClosed.union (hEtfin.isClosed_biUnion fun _ _ => isClosed_closure)
  have hT₂ : IsClosed T₂ :=
    (Γ.finite_V.subset sdiff_subset).isClosed.union
      (hEnfin.isClosed_biUnion fun _ _ => isClosed_closure)
  have hcov : A ⊆ T₁ ∪ T₂ := by
    intro x hx
    rcases (mem_U_iff_edge Γ).mp (hAU hx) with h | ⟨e, he, hxe⟩
    · by_cases hR : x ∈ Rv
      · exact .inl (.inl hR)
      · exact .inr (.inl ⟨h, hR⟩)
    · by_cases ht : (closure e ∩ Rv).Nonempty
      · exact .inl (.inr (mem_biUnion (x := e) ⟨he, ht⟩ (subset_closure hxe)))
      · exact .inr (.inr (mem_biUnion (x := e) ⟨he, ht⟩ (subset_closure hxe)))
  have hdis : Disjoint T₁ T₂ := by
    have hvert : ∀ x ∈ Rv, ∀ e ∈ En, x ∉ closure e := fun x hx e he hxe => he.2 ⟨x, hxe, hx⟩
    rw [disjoint_left]
    rintro x (hx | hx) hx₂
    · rcases hx₂ with hx₂ | hx₂
      · exact hx₂.2 hx
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx₂
        exact hvert x hx e he hxe
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      rcases hx₂ with hx₂ | hx₂
      · exact hx₂.2 (hstep e he.1 he.2 x hxe hx₂.1)
      · obtain ⟨e', he', hxe'⟩ := mem_iUnion₂.mp hx₂
        by_cases hV : x ∈ Γ.V
        · exact hvert x (hstep e he.1 he.2 x hxe hV) e' he' hxe'
        · have h1 : x ∈ e := (Γ.closure_diff_V he.1) ▸ ⟨hxe, hV⟩
          have h2 : x ∈ e' := (Γ.closure_diff_V he'.1) ▸ ⟨hxe', hV⟩
          have heq : e = e' := arcComponentsIn_eq_of_mem he.1 he'.1 h1 h2
          exact he'.2 (heq ▸ he.2)
  by_contra hne
  have hbT₂ : b ∈ T₂ := .inl ⟨hb, fun h => hne h.2⟩
  have haT₁ : a ∈ T₁ := .inl hRa
  obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hA _ _ hT₁ hT₂ hcov ⟨a, haA, haT₁⟩
    ⟨b, hbA, hbT₂⟩
  exact disjoint_left.mp hdis hz₁ hz₂

end GraphMinor.GM07
