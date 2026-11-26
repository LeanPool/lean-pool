/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section8c
public import LeanPool.GraphMinor.GM18.Section7

/-!
# Graph Minors XIX, (8.8)

A rooted location linked to a tangle isolates it, by (7.1) of Graph Minors XVIII.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S}

omit [T2Space S] in
theorem Arm.order_le_ord {L : RootedLocation Γ} {A : Arm Γ} (hA : A ∈ L.arms) : A.order ≤ L.ord :=
  le_csSup (L.finite_arms.image _).bddAbove (mem_image_of_mem _ hA)

/-- **Graph Minors XIX, (8.8).** "If $\mathscr{T}$ is a tangle in $\Gamma$, and $\mathscr{L}$ is a
rooted location with
$\mathscr{L}^- \subseteq \mathscr{T}$, and $ord(\mathscr{L}) < \theta \le ord(\mathscr{T})$,
and $\mathscr{L}$ is $\lambda$-linked to $\mathscr{T}$, then $\mathscr{L}$ $\theta$-isolates
$\mathscr{T}$."
The paper applies (7.1) of Graph Minors XVIII to `ℒ⁻`. We apply it to each `(A⁻, Aᶜ)` alone, since
two arms with the same `A⁻` and different `πBar(A)` do not form a location of Graph Minors X. -/
theorem theorem_8_8_proof {rad : RadialDrawing cap Γ} (tb : TieBreaker rad)
    (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected) {ord θ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯)
    {L : RootedLocation Γ} (hlink : L.IsLambdaLinked tb 𝒯) (hlt : L.ord < θ) (hle : θ ≤ ord) :
    L.Isolates tb θ ord 𝒯 where
  seps_subset := hlink.1
  ord_lt := hlt
  le_ord := hle
  distinction_le A hA ord' 𝒯' h𝒯' hθ' hswap C D hCD := by
    have hmem : A.sep ∈ 𝒯 := hlink.1 (mem_image_of_mem _ hA)
    have hloc : IsLocation Γ.toHypergraph {A.sep} :=
      ⟨fun p hp ↦ by
        rw [mem_singleton_iff.mp hp]
        exact A.isSeparation,
        fun p₁ h₁ p₂ h₂ hne ↦ absurd ((mem_singleton_iff.mp h₁).trans
          (mem_singleton_iff.mp h₂).symm) hne⟩
    have hord : GM18.locationOrder {A.sep} < θ := by
      have h₁ : GM18.locationOrder {A.sep} = A.order := by
        simp [GM18.locationOrder, Arm.order, Arm.sep]
      rw [h₁]
      exact (Arm.order_le_ord hA).trans_lt hlt
    have hiso := GM18.theorem_7_1_proof (tb.isTieBreaker hS h3) h𝒯 hle hloc
      (singleton_subset_iff.2 hmem) hord (fun C' D' hp ↦ by
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton_iff.mp hp)
        exact hlink.2 A hA)
    exact hiso.distinction_le (C := A.sep.1) (D := A.sep.2) (mem_singleton A.sep) h𝒯' hθ' hswap hCD

end GraphMinor.GM19
