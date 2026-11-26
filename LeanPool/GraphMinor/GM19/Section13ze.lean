/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13zd

/-!
# Graph Minors XIX, Section 13: the paths in the disc

A realization of the division gives vertex-disjoint paths of the part of `sk(Γ)` in the disc, one
for each member of the division.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM06 Graph

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- A walk of a subgraph is a walk of the graph, with the same vertices. -/
theorem GraphWalk.exists_lift {α' β : Type*} {C G : Graph α' β} (hle : C ≤ G) {a b : α'}
  (K : GraphWalk C a b) : ∃ K' : GraphWalk G a b, K'.support = K.support := by
  induction K with
  | nil h => exact ⟨.nil (hle.1 h), rfl⟩
  | cons hl t ih =>
    obtain ⟨K', hK'⟩ := ih
    exact ⟨.cons (hle.2 hl) K', by simp [GraphWalk.support_cons, hK']⟩

namespace TangleDatum

variable {D : TangleDatum cap χ} {r u : Shat} {B : Bool → GraphWalk D.rad.G.toGraph r u} {Δ : Set
  Shat} {Sk : Drawing Shat} {G : Drawing Δ}

/-- One vertex set for each member of the division, mutually disjoint, and in each a path of `G`
between any two vertices of the member. -/
theorem IsBigonDisc.exists_paths (h : D.IsBigonDisc B Δ Sk G) :
    ∃ P : ℕ → Set Δ, (∀ j k, 2 * j + 1 ≤ (B false).length → 2 * k + 1 ≤ (B false).length → j ≠ k
      → Disjoint (P j) (P k)) ∧ ∀ j, 2 * j + 1 ≤ (B false).length →
      block B Δ j ⊆ P j ∧ ∀ a ∈ block B Δ j, ∀ b ∈ block B Δ j, ∃ K : GraphWalk G.toGraph a b,
        K.IsSimple ∧ ∀ x ∈ K.support, x ∈ P j := by
  classical
  obtain ⟨H, -, -, hH, -, C, hinj, hC, -⟩ := h.isFeasible
  have hmem : ∀ j, 2 * j + 1 ≤ (B false).length → block B Δ j ∈ blocks B Δ
    := fun j hj ↦ ⟨j, hj, rfl⟩
  have hdis : ∀ j k, 2 * j + 1 ≤ (B false).length → 2 * k + 1 ≤ (B false).length → j ≠ k
    → block B Δ j ≠ block B Δ k := fun j k hj hk hjk e ↦ by
    have hm := Surface.discBd_subset _ (h.vertex_mem (i := false) hj)
    have h₁ : (⟨_, hm⟩ : Δ) ∈ block B Δ k := by rw [← e]; exact ⟨false, rfl⟩
    obtain ⟨i, hi⟩ := h₁
    have := h.bigon.position_unique (i := i) (i' := false)
      (by rw [h.bigon.len i false]; exact hk) hj hi
    omega
  refine ⟨fun j ↦ V(C (block B Δ j)), fun j k hj hk hjk ↦ ?_, fun j hj ↦ ⟨(hC _ (hmem j hj)).2,
    fun a ha b hb ↦ ?_⟩⟩
  · exact (hC _ (hmem j hj)).1.disjoint_vertexSet_of_ne (hC _ (hmem k hk)).1 fun e ↦ hdis j k hj hk
      hjk (hinj (hmem j hj) (hmem k hk) e)
  · obtain ⟨hcomp, hsub⟩ := hC _ (hmem j hj)
    obtain ⟨K⟩ := hcomp.2.1.2 a (hsub ha) b (hsub hb)
    obtain ⟨K', hK'⟩ := GraphWalk.exists_lift (hcomp.1.trans hH) K
    obtain ⟨L, hs, hsup, -⟩ := GM11.GraphWalk.exists_isSimple K'
    exact ⟨L, hs, fun x hx ↦ K.mem_vertexSet_of_mem_support (hK' ▸ hsup x hx)⟩

end TangleDatum

end GraphMinor.GM19
