/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section2
import LeanPool.GraphMinor.GM18.Section6

/-!
# Graph Minors XX, Section 3

This file proves (3.1) of Graph Minors XX, which is (6.7) of Graph Minors XVIII for a sequence of
patchworks. The import of Graph Minors XVIII is private, since that file has many names in common
with
those of Graph Minors X that the rest of this directory opens.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- (6.7) of Graph Minors XVIII holds in the form of `GM18Theorem67Statement`. -/
theorem gm18Theorem67 : GM18Theorem67Statement.{u, v} := by
  intro Ω _ α β _ 𝒞 θ 𝒟 hΩ h𝒞 _ hθ h₁ h₂ Q hQ
  refine GM18.theorem_6_7_proof.{u, v, max u v, 0} hΩ h𝒞 hθ (fun P hP ↦ ⟨(h₁ P hP).1,
    (h₁ P hP).2, ?_⟩) Q hQ
  obtain ⟨Λ, inst, lam, hl, h⟩ := h₂ P hP
  refine ⟨Λ, inst, lam, hl, fun θ' 𝒯 hθ' h𝒯 ↦ ?_⟩
  obtain ⟨ℒ, hp, ⟨Q', hQ', hh⟩, hi⟩ := h θ' 𝒯 h𝒯 hθ'
  exact ⟨ℒ, Q', hp, hh, hQ', hi⟩

/-- Graph Minors XX, (3.1) (page 330), which is (6.7) of Graph Minors XVIII: "Let $\Omega$ be a
well-quasi-order, let $\mathcal{F}$ be a well-behaved set of rootless
partial $\Omega$-patchworks, and let $\theta \ge 1$ be an integer. Let $P_i = (G_i, \mu_i,
\Delta_i, \phi_i)$ ($i = 1, 2, \dots$) be a countable sequence of rootless robust
$\Omega$-patchworks. For each $i \ge 1$ let $\lambda_i$ be a tie-breaker in $G_i$; and
suppose that for every tangle $\mathcal{T}$ in $G_i$ of order $\ge \theta$ there is a rooted
location $\mathcal{L}$ in $G_i$ such that $\mathcal{L}$ $\theta$-isolates $\mathcal{T}$ and
$(P_i, \mathcal{L})$ has a heart in $\mathcal{F}$. Then there exist $j > i \ge 1$ such that
$P_i$ is simulated in $P_j$." -/
theorem theorem_3_1_proof [Infinite β] {Ω : Type (max u v)} [Preorder Ω]
    (hΩ : WellQuasiOrderedLE Ω) {𝓕 : Set (PartialPatchwork Ω α β)} (h𝓕 : GM18.WellBehaved 𝓕)
    (hroot : ∀ P ∈ 𝓕, IsRootless P) {θ : ℕ} (hθ : 1 ≤ θ) (P : ℕ → GM04.Patchwork Ω α β)
    (hP : ∀ i, IsRootless (P i) ∧ (P i).IsRobust) (Λ : ℕ → Type) [∀ i, LinearOrder (Λ i)]
    (lam : ∀ i, Hypergraph α β × Hypergraph α β → Λ i)
    (hlam : ∀ i, IsTieBreaker (P i).G.toHypergraph (lam i))
    (h : ∀ i (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (P i).G.toHypergraph θ' 𝒯 → θ ≤ θ' → ∃ ℒ : Set (RootedHypergraph α β),
        IsOmegaPlace (PartialPatchwork.ofPatchwork (P i)) ℒ ∧
        (∃ Q ∈ 𝓕, HasPlaceHeart (PartialPatchwork.ofPatchwork (P i)) ℒ Q) ∧
        GM18.Isolates (P i).G.toHypergraph (lam i) θ 𝒯
          (rootedLocationToLocation (P i).G ℒ)) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) := by
  refine gm18Theorem67 𝓕 θ (Set.range P) hΩ h𝓕 hroot hθ ?_ ?_ P fun i ↦ ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact hP i
  · rintro _ ⟨i, rfl⟩
    exact ⟨Λ i, inferInstance, lam i, hlam i, h i⟩

end GraphMinor.GM20
