/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section3
public import LeanPool.GraphMinor.GM20.Section5j
public import LeanPool.GraphMinor.GM20.Section2
public import LeanPool.GraphMinor.GM04.Patchwork.Menger

/-!
# Graph Minors XX, Section 5, (5.7)

This is the main result of Section 5: (3.1) with the weaker hypothesis about isolation modulo a set
`W`. We apply (5.6) to each tangle, and then (3.1) with `θ²`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v} {Ω : Type*}

theorem feasibleGroupings_congr {Ω₁ Ω₂ : Type*} {P : Patchwork Ω₁ α β} {Q : Patchwork Ω₂ α β}
    (hb : SameBase P Q) {B : RootedHypergraph α β} (hB : B.toHypergraph ≤ P.G.toHypergraph) :
    feasibleGroupings (P.restrict B) = feasibleGroupings (Q.restrict B) := by
  refine Patch.ext_of rfl ?_
  ext K
  exact ⟨fun h ↦ feasible_transfer hb hB h,
    fun h ↦ feasible_transfer hb.symm (hb.hyper ▸ hB) h⟩

/-- The heart of the underlying patchwork gives a place heart with no labels. -/
theorem placeHeart_of_patchworkHeart {P : Patchwork Ω α β}
    {ℒ : Set (RootedHypergraph α β)} {e : RootedHypergraph α β → β}
    {Q : UnlabeledPatchwork α β} (hfine : IsFine P.G ℒ)
    (h : IsPatchworkHeart (P.relabel fun _ ↦ ()) ℒ e Q) :
    IsPlaceHeart (PartialPatchwork.ofPatchwork P) ℒ e (Q.relabel fun _ ↦ ⊥) := by
  have hb : SameBase (P.relabel fun _ ↦ ()) (PartialPatchwork.ofPatchwork P) :=
    ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have hemp : (rootedLocationCore P.G ℒ).edgeSet = ∅ :=
    core_edgeSet_eq_empty (P := P.relabel fun _ ↦ ()) hfine
  refine
  { isRootedLocation := h.isRootedLocation
    injOn_newEdge := h.injOn_newEdge
    newEdge_notMem_core := h.newEdge_notMem_core
    vertexSet_eq := h.vertexSet_eq
    edgeSet_eq := h.edgeSet_eq
    roots_eq := h.roots_eq
    ends_core := h.ends_core
    ends_newEdge := h.ends_newEdge
    dom_eq := h.dom_eq
    μ_core := h.μ_core
    μ_newEdge := h.μ_newEdge
    Δ_core := h.Δ_core
    Δ_newEdge := fun A hA ↦ ?_
    φ_core := fun f hf ↦ ?_
    φ_newEdge := fun _ _ ↦ rfl }
  · refine (h.Δ_newEdge hA).trans (feasibleGroupings_congr hb ?_)
    exact (h.isRootedLocation.isComplemented hA).le
  · change f ∈ (rootedLocationCore P.G ℒ).edgeSet at hf
    rw [hemp] at hf
    exact hf.elim

/-- Graph Minors XX, (5.7) (page 342): "Let $\Omega$ be a well-quasi-order, let $\mathcal{F}$ be a
well-behaved set of patchworks,
and let $\theta \ge 1$. Let $P_i = (G_i, \mu_i, \Delta_i, \phi_i)$ ($i = 1, 2, \dots$) be a
countable sequence of rootless robust $\Omega$-patchworks. For each $i \ge 1$ let
$\lambda_i$ be a tie-breaker in $G_i$; and suppose that for each tangle $\mathcal{T}$ in
$G_i$ of order $\ge \theta$, there exist $W \subseteq Z(G_i)$ with $|W| \le \theta$ and a
fine rooted location $\mathcal{L}$ in $G_i$, such that $\mathcal{L}$ $\theta$-isolates
$\mathcal{T}$ modulo $W$, and $\mathcal{F}$ contains a heart of $((G_i, \mu_i, \Delta_i),
\mathcal{L})$. Then there exist $j > i \ge 1$ such that $P_i$ is simulated in $P_j$." -/
theorem theorem_5_7_proof [Infinite β] {Ω : Type (max u v)}
    [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω) {𝓕 : Set (UnlabeledPatchwork α β)}
    (h𝓕 : WellBehaved 𝓕) {θ : ℕ} (hθ : 1 ≤ θ) (P : ℕ → GM04.Patchwork Ω α β)
    (hP : ∀ i, IsRootless (P i) ∧ (P i).IsRobust) (Λ : ℕ → Type) [∀ i, LinearOrder (Λ i)]
    (lam : ∀ i, Hypergraph α β × Hypergraph α β → Λ i)
    (hlam : ∀ i, IsTieBreaker (P i).G.toHypergraph (lam i))
    (h : ∀ i (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (P i).G.toHypergraph θ' 𝒯 → θ ≤ θ' → ∃ (W : Set (α ⊕ β))
        (ℒ : Set (RootedHypergraph α β)), W ⊆ zSet (P i).G.toHypergraph ∧ W.ncard ≤ θ ∧
        IsFine (P i).G ℒ ∧ IsolatesModulo (lam i) 𝒯 W θ (P i).G ℒ ∧
        ∃ Q ∈ 𝓕, HasPatchworkHeart ((P i).relabel fun _ ↦ ()) ℒ Q) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) := by
  classical
  obtain ⟨𝓕', h𝓕', H⟩ := theorem_5_6_proof.{u, v, 0} h𝓕 hθ
  let 𝓕'' : Set (PartialPatchwork Ω α β) :=
    {R | IsRootless R ∧ (∀ e ∈ R.G.edgeSet, R.φ e = ⊥) ∧ ∃ Q ∈ 𝓕', IsCompletionOf Q R}
  have hwb : GM18.WellBehaved 𝓕'' := by
    intro Ω' _ ι hΩ' Q hQ
    refine h𝓕' Ω' hΩ' Q fun i ↦ ?_
    obtain ⟨R, ⟨-, -, Q₀, hQ₀, hc⟩, hR⟩ := hQ i
    refine ⟨Q₀, hQ₀, hR.G_eq.trans hc.G_eq, hR.dom_eq.trans hc.dom_eq, fun e he ↦ ?_,
      fun e he ↦ ?_⟩
    · have he' : e ∈ R.dom := hc.dom_eq ▸ he
      exact (hR.μ_eq he').trans (hc.μ_eq he)
    · have he' : e ∈ R.G.edgeSet := by
        rw [hc.G_eq]
        exact he
      exact (hR.Δ_eq he').trans (hc.Δ_eq he)
  have hθθ : θ ≤ θ ^ 2 := Nat.le_self_pow two_ne_zero _
  refine theorem_3_1_proof hΩ hwb (fun R hR ↦ hR.1) (hθ.trans hθθ) P hP Λ lam hlam ?_
  intro i θ' 𝒯 h𝒯 hθ'
  obtain ⟨W, ℒ, hWG, hWθ, hfine, hiso, hheart⟩ := h i θ' 𝒯 h𝒯 (hθθ.trans hθ')
  obtain ⟨ℒ', hfine', hloc', hiso', Q, hQ, e, hQe⟩ := H ((P i).relabel fun _ ↦ ()) (Λ i)
    (lam i) 𝒯 θ'
    W ℒ (hlam i) h𝒯 hθ' hWG hWθ (hP i).1 (hP i).2.isRemovable hfine hiso hheart
  refine ⟨ℒ', ⟨fun e _ ↦ WithBot.coe_ne_bot, hloc'⟩, ⟨Q.relabel fun _ ↦ ⊥, ⟨?_, fun _ _ ↦ rfl, Q,
    hQ,
    isCompletionOf_relabel _ _⟩, e, placeHeart_of_patchworkHeart hfine' hQe⟩, hiso'⟩
  change {v | v ∈ Q.G.roots} = ∅
  rw [hQe.roots_eq]
  exact (hP i).1

end GraphMinor.GM20
