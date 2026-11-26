/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.SpanRestriction

public import LeanPool.GraphMinor.GM16.Section5

import LeanPool.GraphMinor.GM11.CitedResults

/-!
# Graph Minors XVI, Section 6: Induction on Hairs

This file formalizes Section 6 ("Induction on hairs", pages 58–61) of
N. Robertson and P. D. Seymour, *Graph Minors. XVI. Excluding a non-planar graph*, J. Combin.
Theory Ser. B 89 (2003) 43–76:

- Restriction of a `SpanEmbedding H G` to a spanned subdrawing `H.span V' E'`
  (`SpanEmbedding.restrictSpan`)
  and to `clearedSubdrawing H Λ` (`SpanEmbedding.restrictCleared`).
- Statement of **Graph Minors XVI, (6.1)** (`GM16Theorem61Statement`, page 58).
- Statement and complete proof of **Graph Minors XVI, (6.2)** (`GM16Theorem62Statement`,
  `theorem_6_2`, page 59): clearing a `λ`-zone preserves a horn of cardinality `σ` and breadth
  `≥ θ - 4λ - 2` whenever a horn of cardinality `σ + 1` and breadth `≥ θ` is given.
- Statement of **Graph Minors XVI, (6.3)** (`GM16Theorem63Statement`, page 59).
- Complete proof of **Graph Minors XVI, (5.1)** (`theorem_5_1`, page 61) from `(6.1)` and `(6.3)`
  by induction on the number of hairs `0 ≤ i ≤ δ`.
The backward and tower inductions are proved in `InductionsProved.lean`.
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15

universe u v w

variable {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}

/-! ## Restriction of `SpanEmbedding` to Subdrawings -/

omit [T2Space S] in
/-- Every singleton vertex `{v}` with `v ∈ Γ.V` is an atom in `Γ.A`. -/
theorem singleton_mem_A_of_mem_V {Γ : Drawing S} {v : S} (hv : v ∈ Γ.V) :
    ({v} : Set S) ∈ Γ.A :=
  Or.inl (Or.inl ⟨v, hv, rfl⟩)

/-- A vertex `w ∈ H.V` with `w ∉ Λ` belongs to `(clearedSubdrawing H Λ).V`. -/
theorem mem_clearedSubdrawing_V {H : Drawing S} {Λ : Set S} {w : S}
    (hw : w ∈ H.V) (hnot : w ∉ Λ) :
    w ∈ (clearedSubdrawing H Λ).V :=
  Or.inl ⟨⟨hw, mem_univ w, hnot⟩, hw⟩

/-- Restriction of a `SpanEmbedding H G` to a spanned subdrawing `H.span V' E'`. -/
def restrictSpan {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (V' : Set S) (E' : Set (Set S)) :
    SpanEmbedding (H.span V' E') G :=
  GM14.restrictSpan η V' E'

/-- Restriction of a `SpanEmbedding H G` to `clearedSubdrawing H Λ = H.interSet (univ \ Λ)`. -/
def restrictCleared {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Λ : Set S) :
    SpanEmbedding (clearedSubdrawing H Λ) G :=
  GM14.restrictCleared η Λ

@[simp]
theorem restrictCleared_vMap {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Λ : Set S) :
    (restrictCleared η Λ).vMap = η.vMap := rfl

theorem restrictCleared_imageGraph_le {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Λ : Set S) :
    (restrictCleared η Λ).imageGraph ≤ η.imageGraph :=
  GM14.restrictCleared_imageGraph_le η Λ

/-! ## Statements of (6.1), (6.2), and (6.3), and Proof of (6.2) (pages 58–60) -/

/-- Statement of Graph Minors XVI, (6.1) (page 58):
"Let $\Sigma$ be a surface, and let $p, \tau, \chi, \delta \ge 0$ and $\phi, \psi \ge 1$. Then there
exist $\sigma, \kappa, \rho, \zeta \ge 0$ and $\theta \ge 1$ such that if $\mathscr{T}^*$ is a
tangle
in a graph $G$, and there is an animal with $\chi$ horns and $\delta$ hairs, of strength
$\ge (\theta, \sigma)$, then either
1. there is a $\Sigma'$-span of order $\ge \phi$, for some surface $\Sigma'$ obtained from $\Sigma$
   by adding a handle or a crosscap, or
2. there is an animal with $\chi$ horns and $\delta + 1$ hairs, of strength $\ge (\psi, \tau)$, or
3. there exists $Z \subseteq V(G)$ with $|Z| \le \zeta$, and a $\mathscr{T}^* \setminus Z$-central
   segregation of $G \setminus Z$ of type $(\rho, \kappa)$ with a proper arrangement in $\Sigma$, or
4. $\mathscr{T}^*$ controls a $K_p$-minor of $G$." -/
def GM16Theorem61Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ p τ χ δ φ ψ : ℕ, 1 ≤ φ → 1 ≤ ψ →
      ∃ σ κ ρ ζ θ : ℕ, 1 ≤ θ ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (hT : IsGraphTangle G θ_star T_star),
          HasAnimal S G T_star θ_star χ δ θ σ →
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
            (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
            (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
            IsClosedSurface S' ∧ ConnectedSpace S' ∧
            IsObtainedByAddingHandleOrCrosscap S S' ∧
            φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
          HasAnimal S G T_star θ_star χ (δ + 1) ψ τ ∨
          (∃ (Z : Set α) (S_seg : Set (Society α β))
            (α_disc : Society α β → Set S) (α_pt : α → S),
            Z ⊆ V(G) ∧ Z.ncard ≤ ζ ∧ Z.ncard < θ_star ∧
            IsCentralSegregation (deleteVertices G Z)
              (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
            IsSegregationOfType (deleteVertices G Z) ρ κ S_seg ∧
            IsProperArrangement S_seg α_disc α_pt) ∨
          ControlsMinor G (completeGraph p) T_star

/-- Statement of Graph Minors XVI, (6.2) (page 59):
"Let $\Sigma$ be a surface and let $\sigma \ge 0$ be an integer. Let $\mathcal{T}^*$ be a tangle in
a graph $G$, and let $H, \mathcal{T}$ be a $\Sigma$-span of order $\theta$. Let $\lambda \ge 2$ be
an integer with $\theta \ge 4\lambda + 3$, let $\Lambda \subseteq \Sigma$ be a $\lambda$-zone such
that $H \cap (\Sigma \setminus \Lambda)$ is rigid, and let $\mathcal{T}'$ be the tangle in
$H' = H \cap (\Sigma \setminus \Lambda)$ of order $\theta - 4\lambda - 2$ which is a
$(4\lambda + 2)$-compression of $\mathcal{T}$. Let $v \in V(G) \setminus V(H)$, such that there is a
horn at $v$ over $H, \mathcal{T}$ with cardinality $\sigma + 1$ and breadth $\ge \theta$. Then there
is a horn at $v$ over $H', \mathcal{T}'$ with cardinality $\sigma$ and breadth
$\ge \theta - 4\lambda - 2$." -/
def GM16Theorem62Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ lam σ : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β))
      (H : Drawing S) (η : SpanEmbedding H G)
      (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d d' : Set S → Set S → ℕ)
      (Λ : Set S) (v : α)
      (P : Fin (σ + 1) → Graph α β) (u : Fin (σ + 1) → S),
      IsSigmaSpan G H η θ_star θ T_star T →
      HasTangleMetric H θ T d →
      2 ≤ lam → 4 * lam + 3 ≤ θ →
      IsLambdaZone H d lam Λ →
      IsRigid (clearedSubdrawing H Λ) →
      IsClearedTangle H T d θ lam Λ T' d' →
      IsHorn G H η d v θ (σ + 1) P u →
      ∃ (P' : Fin σ → Graph α β) (u' : Fin σ → S),
        IsHorn G (clearedSubdrawing H Λ) (restrictCleared η Λ) d' v (θ - 4 * lam - 2) σ P' u'

/-- **Graph Minors XVI, (6.2)** (page 59):
Clearing a `λ`-zone `Λ` (where `2 ≤ λ` and `4λ + 3 ≤ θ`) contains at most one end `u_i` of a horn
`{P_1, …, P_{σ+1}}` of breadth `≥ θ`, leaving a horn of cardinality `σ` and breadth
`≥ θ - 4λ - 2` over `H' = H ∩ (Σ \ Λ)` and the cleared tangle `T'`. -/
theorem theorem_6_2_proof :
    GM16Theorem62Statement.{u, v, w} := by
  classical
  intro S _ _ hS hconn α β G θ_star θ lam σ T_star H η T T' d d' Λ v P u
    _hSpan hMet _hlam2 hθ_le hZone _hRigid hCleared hHorn
  rcases hHorn with ⟨hv, hu_V, hP_path, hP_inter, hP_disj, hu_dist⟩
  obtain ⟨z, hzA, hZoneAround⟩ := hZone
  obtain ⟨_, _, _, hsymm, htri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ T d hS hconn hMet
  -- Claim: at most one index k : Fin (σ + 1) has u k ∈ Λ.
  have hat_most_one : ∀ i j : Fin (σ + 1), u i ∈ Λ → u j ∈ Λ → i = j := by
    intro i j hui huj
    by_contra hij
    have hui_A : ({u i} : Set S) ∈ H.A := singleton_mem_A_of_mem_V (hu_V i)
    have huj_A : ({u j} : Set S) ∈ H.A := singleton_mem_A_of_mem_V (hu_V j)
    have hdi : d z {u i} ≤ lam :=
      hZoneAround.dist_le {u i} hui_A (singleton_subset_iff.mpr (subset_closure hui))
    have hdj : d z {u j} ≤ lam :=
      hZoneAround.dist_le {u j} huj_A (singleton_subset_iff.mpr (subset_closure huj))
    have hdi_symm : d {u i} z = d z {u i} := hsymm {u i} hui_A z hzA
    have htri_ij : d {u i} {u j} ≤ d {u i} z + d z {u j} := htri {u i} hui_A z hzA {u j} huj_A
    have hge : θ ≤ d {u i} {u j} := hu_dist i j hij
    omega
  -- Choose an injection emb : Fin σ → Fin (σ + 1) avoiding Λ.
  have hex_emb : ∃ emb : Fin σ → Fin (σ + 1), Injective emb ∧ ∀ i : Fin σ, u (emb i) ∉ Λ := by
    by_cases hex : ∃ k : Fin (σ + 1), u k ∈ Λ
    · obtain ⟨k₀, hk₀⟩ := hex
      refine ⟨k₀.succAbove, Fin.succAbove_right_injective, fun i hui => ?_⟩
      exact Fin.succAbove_ne k₀ i (hat_most_one (k₀.succAbove i) k₀ hui hk₀)
    · refine ⟨Fin.castSucc, Fin.castSucc_injective σ, fun i hui => hex ⟨Fin.castSucc i, hui⟩⟩
  obtain ⟨emb, hemb_inj, hu_not_mem⟩ := hex_emb
  refine ⟨fun i => P (emb i), fun i => u (emb i), ?_⟩
  have hsub_V : V((restrictCleared η Λ).imageGraph) ⊆ V(η.imageGraph) :=
    (restrictCleared_imageGraph_le η Λ).vertexSet_mono
  refine ⟨⟨hv.1, fun hv' => hv.2 (hsub_V hv')⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact mem_clearedSubdrawing_V (hu_V (emb i)) (hu_not_mem i)
  · intro i
    simpa [restrictCleared_vMap] using hP_path (emb i)
  · intro i
    apply Subset.antisymm
    · calc
        V(P (emb i)) ∩ V((restrictCleared η Λ).imageGraph)
          ⊆ V(P (emb i)) ∩ V(η.imageGraph) := inter_subset_inter_right _ hsub_V
        _ = {η.vMap (u (emb i))} := hP_inter (emb i)
    · rw [singleton_subset_iff]
      have hmem_Pi : η.vMap (u (emb i)) ∈ V(P (emb i)) := by
        have : η.vMap (u (emb i)) ∈ V(P (emb i)) ∩ V(η.imageGraph) := by
          rw [hP_inter (emb i)]
          exact mem_singleton _
        exact this.1
      have hmem_H' : η.vMap (u (emb i)) ∈ V((restrictCleared η Λ).imageGraph) :=
        (restrictCleared η Λ).bijOn_v.mapsTo
          (mem_clearedSubdrawing_V (hu_V (emb i)) (hu_not_mem i))
      exact ⟨hmem_Pi, hmem_H'⟩
  · intro i j hij
    exact hP_disj (emb i) (emb j) (fun h_eq => hij (hemb_inj h_eq))
  · intro i j hij
    have hemb_ne : emb i ≠ emb j := fun h_eq => hij (hemb_inj h_eq)
    have hui_A : ({u (emb i)} : Set S) ∈ H.A := singleton_mem_A_of_mem_V (hu_V (emb i))
    have huj_A : ({u (emb j)} : Set S) ∈ H.A := singleton_mem_A_of_mem_V (hu_V (emb j))
    have hui_A' : ({u (emb i)} : Set S) ∈ (clearedSubdrawing H Λ).A :=
      singleton_mem_A_of_mem_V (mem_clearedSubdrawing_V (hu_V (emb i)) (hu_not_mem i))
    have huj_A' : ({u (emb j)} : Set S) ∈ (clearedSubdrawing H Λ).A :=
      singleton_mem_A_of_mem_V (mem_clearedSubdrawing_V (hu_V (emb j)) (hu_not_mem j))
    have hbd := (hCleared.dist_bounds {u (emb i)} hui_A {u (emb j)} huj_A
      {u (emb i)} hui_A' {u (emb j)} huj_A' Subset.rfl Subset.rfl).1
    have hge := hu_dist (emb i) (emb j) hemb_ne
    dsimp only
    omega

/-- Statement of Graph Minors XVI, (6.3) (page 59):
"Let $\Sigma$ be a surface, and let $p, \tau, \chi \ge 0$ and $\psi \ge 1$ be integers. Then there
exists $\delta \ge 0$ and $\theta \ge 1$ such that if $\mathcal{T}^*$ is a tangle in a graph $G$,
and
there is an animal with $\chi$ horns and $\delta$ hairs of strength $\ge (\theta, \tau + 1)$, then
either
- there is a hairless animal with $\chi + 1$ horns of strength $\ge (\psi, \tau)$, or
- $\mathcal{T}^*$ controls a $K_p$-minor of $G$." -/
def GM16Theorem63Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ p τ χ ψ : ℕ, 1 ≤ ψ →
      ∃ δ θ : ℕ, 1 ≤ θ ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β)),
          IsGraphTangle G θ_star T_star →
          HasAnimal S G T_star θ_star χ δ θ (τ + 1) →
          HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ ∨
          ControlsMinor G (completeGraph p) T_star

/-! ## Proof of Graph Minors XVI, (5.1) from (6.1) and (6.3) (page 61) -/


end GraphMinor.GM16
