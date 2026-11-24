/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10c

import LeanPool.GraphMinor.GM20.Section9hProved

import LeanPool.GraphMinor.GM20.Section10l

import LeanPool.GraphMinor.GM20.Section8b

/-!
# Graph Minors XX: deductions from Section10c

The deductions apply the proved results after their geometric prerequisites.
-/

public section
namespace GraphMinor.GM20
open Set Topology GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM18 GraphMinor.GM10 Hypergraph
  GraphMinor.GM04
universe u v
variable {α : Type u} {β : Type v}

/-- Graph Minors XX, (10.4) (page 355): "Let* $\Omega$ *be a well-quasi-order and let* $p \ge 0$.
*Let* $P_i = (G_i, \mu_i, \Delta_i,
\phi_i)$ $(i = 1, 2, \dots)$ *be a countable sequence of free rootless* $\Omega$*-patchworks
such that for all* $i \ge 1$, $sk(G_i^-)$ *has no* $K_p$ *minor. Then there exist* $j > i
\ge 1$ *such that* $P_i$ *is simulated in* $P_j$." -/
theorem theorem_10_4_proof [Infinite β]
    {Ω : Type (max u v)} [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω) (p : ℕ)
    (P : ℕ → GM04.Patchwork Ω α β) (hfree : ∀ i, IsFree (P i)) (hroot : ∀ i, IsRootless (P i))
    (hmin : ∀ i, ¬ HasCliqueMinor (P i).G.toHypergraph p) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) := by
  obtain ⟨θ, 𝒮, hθ, hfin, h⟩ := GraphMinor.GM20.theorem_10_3_proof.{u, v} (completeHypergraph p)
    (isGraph_completeHypergraph p)
  have hroots : ∀ i, (P i).G.roots = [] := fun i ↦ by
    refine List.eq_nil_iff_forall_not_mem.mpr fun x hx ↦ ?_
    have h₁ : x ∈ (P i).G.rootSet := hx
    rw [show (P i).G.rootSet = ∅ from hroot i] at h₁
    exact h₁
  refine theorem_7_3_proof hΩ (wellBehaved_biUnion hfin fun X _ ↦ theorem_9_1_proof X) hθ P hfree
    hroot
    fun i θ' 𝒯 h𝒯 hθ' ↦ ?_
  have hfree' : IsFree ((P i).relabel fun _ ↦ ()) := fun e he ↦ hfree i e he
  obtain ⟨W, hWV, hWθ, ℒ, hfine, ⟨X, hX, hs⟩, hlink⟩ := h ((P i).relabel fun _ ↦ ()) hfree'
    (hroots i) θ' 𝒯 h𝒯 hθ' fun hc ↦ hmin i (hasCliqueMinor_of_controlsMinor hc)
  obtain ⟨Q, hQ, hul⟩ := theorem_10_2_proof (isFree_slash hfree' W) (by
    change marchSlash (P i).G.roots W = []
    rw [hroots i]
    rfl) hs
  exact ⟨W, ℒ, hWV, hWθ, hfine, hlink, Q, mem_biUnion hX hul, hQ⟩

end GraphMinor.GM20
