/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section5i

/-!
# Graph Minors XX, Section 5, (5.5) and (5.6)

(5.5) replaces the members of a suitable location on the small side of a member of `ℳ(𝒯, W, θ)` by
that small side, using the heart step of `Section5i`. The new location isolates `𝒯` outright. (5.6)
applies (5.3), (5.4) and (5.5) in turn.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v w

variable {α : Type u} {β : Type v}

theorem locationReplaced_mono {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)} (h : 𝓕₁ ⊆ 𝓕₂) {k k' w w' : ℕ}
    (hk : k ≤ k') (hw : w ≤ w') : locationReplaced 𝓕₁ k w ⊆ locationReplaced 𝓕₂ k' w' := by
  rintro P₂ ⟨F, hF, hn, P₁, hP₁, A, h₁, h₂, h₃, h₄, h₅⟩
  exact ⟨F, hF, hn.trans hw, P₁, h hP₁, A, h₁, h₂, h₃, h₄, fun f hf ↦
    ⟨(h₅ f hf).1, (h₅ f hf).2.trans hk⟩⟩

/-- `ℒ⁻` is a location, for a rooted location `ℒ`. -/
theorem isLocation_of_isRootedLocation {G : RootedHypergraph α β} {ℒ : Set (RootedHypergraph α β)}
    (h : IsRootedLocation G ℒ) : IsLocation G.toHypergraph (rootedLocationToLocation G ℒ) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact isSeparation_complement (h.isComplemented hA)
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
    have := h.le_complement hA hB fun h' ↦ hne (by rw [h'])
    rwa [complement_toHypergraph] at this

section

variable {Λ : Type*} [LinearOrder Λ] {lam : Hypergraph α β × Hypergraph α β → Λ}
  {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {W : Set (α ⊕ β)} {θ θ₀ : ℕ}
  {G : RootedHypergraph α β} {ℒ : Set (RootedHypergraph α β)}

/-- Subproof (2) of (5.5): `ℒ'` `θ²`-isolates `𝒯`. -/
theorem isolates_sideSet (hTB : IsTieBreaker G.toHypergraph lam)
    (h𝒯 : IsTangle G.toHypergraph θ₀ 𝒯) (hθ : 1 ≤ θ)
    (hS : IsSuitable lam 𝒯 W θ G ℒ)
    (hD : SideData G ℒ {p | InM lam G.toHypergraph 𝒯 W θ p.1 p.2}) :
    Isolates G.toHypergraph lam (θ ^ 2) 𝒯 (rootedLocationToLocation G
      (sideSet G ℒ {p | InM lam G.toHypergraph 𝒯 W θ p.1 p.2})) := by
  set ℳ : Set (Hypergraph α β × Hypergraph α β) := {p | InM lam G.toHypergraph 𝒯 W θ p.1 p.2}
    with hℳ
  have hθθ : θ ≤ θ ^ 2 := Nat.le_self_pow two_ne_zero _
  have hpos : 1 ≤ θ ^ 2 := hθ.trans hθθ
  have hcompl : ∀ {p}, p ∈ ℳ → complementHypergraph G (sepRooted p.1 p.2) = p.2 := fun {p} hp ↦
    complementHypergraph_sepRooted hD.rootless (hD.sep p hp)
  have hordM : ∀ {p}, p ∈ ℳ → separationOrder p.1 p.2 < θ := fun hp ↦ hp.1.2.1
  have hord : ∀ ⦃C D⦄, (C, D) ∈ rootedLocationToLocation G
      (sideSet G ℒ ℳ) → separationOrder C D < θ ^ 2 := by
    rintro C D ⟨L, hL | ⟨p, hp, rfl⟩, heq⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact separationOrder_complement_le.trans_lt (hS.order_lt hL.1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only
      rw [hcompl hp]
      exact (hordM hp).trans_le hθθ
  refine ⟨isLocation_of_isRootedLocation hD.isRootedLocation, ?_, ?_, hord, ?_⟩
  · rintro _ ⟨L, hL | ⟨p, hp, rfl⟩, rfl⟩
    · exact hS.subset ⟨L, hL.1, rfl⟩
    · simp only
      rw [hcompl hp]
      exact hp.1.1
  · have hle : locationOrder (rootedLocationToLocation G (sideSet G ℒ ℳ)) ≤ θ ^ 2 - 1 := by
      refine csSup_le' ?_
      rintro _ ⟨p, hp, rfl⟩
      have := hord (C := p.1) (D := p.2) hp
      simp only
      omega
    omega
  · rintro C D ⟨L, hL | ⟨p, hp, rfl⟩, heq⟩ θ' 𝒯' h𝒯' hθ' hmem a b hd
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rcases hS.distinction h𝒯' hθ' ⟨L, hL.1, rfl⟩ hmem hd with h | ⟨A', B', hM, h₁, h₂⟩
      · exact h
      · exfalso
        have hsep : G.toHypergraph.IsSeparation A' B' := h𝒯.isSeparation hM.1.1
        have hB'A' : (B', A') ∈ 𝒯' := mem_tangle_of_le h𝒯' hsep
          (hM.1.2.1.trans_le (hθθ.trans hθ')) hd.1.2 h₂
        have hle := (hD.main_side (p := (A', B')) hL hM).1
        exact not_le_of_mem_tangle h𝒯' hB'A' hmem hle
    · obtain ⟨rfl, hD'⟩ := Prod.mk.inj heq
      have hDeq : D = p.2 := by
        rw [← hD']
        exact hcompl hp
      subst hDeq
      have hlt : separationOrder a b < θ :=
        (order_le_of_distinction hTB h𝒯 h𝒯' hd hp.1.1 hmem).trans_lt (hordM hp)
      rcases theorem_5_1_of_lt hTB h𝒯 h𝒯' hp hd hlt with h | h
      · exact h
      · exact (not_le_of_mem_tangle h𝒯' hd.1.2 hmem h.2).elim

/-- The data of (5.5) come from (5.2). -/
theorem sideData_of_tangle (hTB : IsTieBreaker G.toHypergraph lam)
    (h𝒯 : IsTangle G.toHypergraph θ₀ 𝒯) (hWG : W ⊆ zSet G.toHypergraph) (hr : G.rootSet = ∅)
    (hS : IsSuitable lam 𝒯 W θ G ℒ)
    (hside : ∀ C ∈ ℒ, ∀ ⦃A B⦄, InM lam G.toHypergraph 𝒯 W θ A B →
      (C.toHypergraph ≤ A ∧ B ≤ complementHypergraph G C) ∨
      (C.toHypergraph ≤ B ∧ A ≤ complementHypergraph G C)) :
    SideData G ℒ {p | InM lam G.toHypergraph 𝒯 W θ p.1 p.2} := by
  refine ⟨hr, fun p hp ↦ h𝒯.isSeparation hp.1.1, fun p hp q hq hne ↦ theorem_5_2_proof hTB h𝒯 hp hq
    hne,
    hS.isRootedLocation, hS.fine, fun C hC p hp ↦ hside C hC hp, fun p hp q hq heq ↦ ?_⟩
  by_contra hne
  have hsep : G.toHypergraph.IsSeparation q.1 q.2 := h𝒯.isSeparation hq.1.1
  have hle : q.1 ≤ q.2 := heq ▸ theorem_5_2_proof hTB h𝒯 hp hq hne
  refine hq.1.2.2.1 fun z hz ↦ ?_
  rcases mem_zSet_of_separation hsep (hWG hz) with h | h
  · exact zSet_mono hle h
  · exact h

end

/-- Graph Minors XX, (5.5) (page 340): "Let $\mathcal{F}$ be a well-behaved set of patchworks and
let $\theta \ge 1$. Then there is
a well-behaved set of patchworks $\mathcal{F}'$ with the following property. Let $P = (G,
\mu, \Delta)$ be a patchwork, let $\lambda$ be a tie-breaker in $G$, let $\mathcal{T}$ be a
tangle in $G$ of order $\ge \theta^2$, and let $W \subseteq Z(G)$ with $|W| \le \theta$.
Suppose that* * *$P$ is rootless,* * *$\mathcal{L}$ is a $W$-suitable rooted location in $G$
such that $\mathcal{F}$ contains a heart of $(P, \mathcal{L})$, and* * *for each $C \in
\mathcal{L}$ and each $(A^*, B^*) \in \mathcal{M}(\mathcal{T}, W, \theta)$, either* * *$C^-
\subseteq A^*$ and $B^* \subseteq (G \setminus C)^-$ or* * *$C^- \subseteq B^*$ and $A^*
\subseteq (G \setminus C)^-$.* *Then there is a fine rooted location $\mathcal{L}'$ such
that $\mathcal{L}'$ $\theta^2$-isolates $\mathcal{T}$ and $\mathcal{F}'$ contains a heart of
$(P, \mathcal{L}')$."

Lean uses an infinite ambient edge type to provide fresh edge labels. -/
theorem theorem_5_5_proof [Infinite β] {𝓕 : Set (UnlabeledPatchwork α β)}
  (h𝓕 : WellBehaved 𝓕) {θ : ℕ}
    (hθ : 1 ≤ θ) :
    ∃ 𝓕' : Set (UnlabeledPatchwork α β), WellBehaved 𝓕' ∧
      ∀ (P : UnlabeledPatchwork α β) (Λ : Type w) [LinearOrder Λ]
        (lam : Hypergraph α β × Hypergraph α β → Λ) (𝒯 : Set (Hypergraph α β × Hypergraph α β))
        (θ₀ : ℕ) (W : Set (α ⊕ β)) (ℒ : Set (RootedHypergraph α β)),
        IsTieBreaker P.G.toHypergraph lam → IsTangle P.G.toHypergraph θ₀ 𝒯 → θ ^ 2 ≤ θ₀ →
        W ⊆ zSet P.G.toHypergraph → W.ncard ≤ θ → IsRootless P →
        IsSuitable lam 𝒯 W θ P.G ℒ → (∃ Q ∈ 𝓕, HasPatchworkHeart P ℒ Q) →
        (∀ C ∈ ℒ, ∀ ⦃A B⦄, InM lam P.G.toHypergraph 𝒯 W θ A B →
          (C.toHypergraph ≤ A ∧ B ≤ complementHypergraph P.G C) ∨
          (C.toHypergraph ≤ B ∧ A ≤ complementHypergraph P.G C)) →
        ∃ ℒ' : Set (RootedHypergraph α β), IsFine P.G ℒ' ∧ IsRootedLocation P.G ℒ' ∧
          Isolates P.G.toHypergraph lam (θ ^ 2) 𝒯 (rootedLocationToLocation P.G ℒ') ∧
          ∃ Q ∈ 𝓕', HasPatchworkHeart P ℒ' Q := by
  let active : Set (UnlabeledPatchwork α β) := {P ∈ 𝓕 | IsActive P}
  have hsub : active ⊆ 𝓕 := fun _ h ↦ h.1
  have hactive : ∀ P ∈ active, IsActive P := fun _ h ↦ h.2
  refine ⟨locationReplaced active θ θ,
    wellBehaved_locationReplaced (h𝓕.mono hsub) hactive θ θ, ?_⟩
  intro P Λ _ lam 𝒯 θ₀ W ℒ hTB h𝒯 _ hWG hWθ hr hS hheart hside
  obtain ⟨Q, hQ, e, hQe⟩ := hheart
  have hD := sideData_of_tangle hTB h𝒯 hWG hr hS hside
  have hfinM := finite_inM (lam := lam) (W := W) (θ := θ) h𝒯
  have hWfin : W.Finite := (finite_zSet _).subset hWG
  have hcard := theorem_5_2_card (θ := θ) hTB h𝒯 hWfin hWG
  obtain ⟨Q', hQ', hrep⟩ := exists_sideSet_heart hD hQe hfinM (k := θ) fun p hp ↦ hp.1.2.1.le
  refine ⟨_, hD.isFine, hD.isRootedLocation, isolates_sideSet hTB h𝒯 hθ hS hD, Q', ?_, hQ'⟩
  refine locationReplaced_mono ?_ le_rfl (hcard.trans hWθ) hrep
  rintro _ rfl
  exact ⟨hQ, heart_isActive hS.fine hQe⟩

/-- Graph Minors XX, (5.6) (page 342):
"**5.6.** *Let $\mathcal{F}$ be a well-behaved set of patchworks, and let $\theta \ge 1$. Then there
is a well-behaved set of patchworks $\mathcal{F}'$ with the following property. Let $P = (G, \mu,
\Delta)$ be a rootless removable patchwork, let $\lambda$ be a tie-breaker in $G$, let $\mathcal{T}$
be a tangle in $G$ of order $\ge \theta^2$, and let $W \subseteq Z(G)$ with $|W| \le \theta$.
Suppose that $\mathcal{L}$ is a fine rooted location in $G$ such that $\mathcal{L}$
$\theta$-isolates $\mathcal{T}$ modulo $W$, and $\mathcal{F}$ contains a heart of $(P,
\mathcal{L})$. Then there is a fine rooted location $\mathcal{L}'$ in $G$ such that $\mathcal{L}$
$\theta^2$-isolates $\mathcal{T}$ and $\mathcal{F}'$ contains a heart of $(P, \mathcal{L}')$.*"
(Here "$\mathcal{L}$ $\theta^2$-isolates $\mathcal{T}$" is a misprint in the paper for
"$\mathcal{L}'$ $\theta^2$-isolates $\mathcal{T}$".)

Lean uses an infinite ambient edge type to provide fresh edge labels. -/
theorem theorem_5_6_proof [Infinite β] {𝓕 : Set (UnlabeledPatchwork α β)}
  (h𝓕 : WellBehaved 𝓕) {θ : ℕ}
    (hθ : 1 ≤ θ) :
    ∃ 𝓕' : Set (UnlabeledPatchwork α β), WellBehaved 𝓕' ∧
      ∀ (P : UnlabeledPatchwork α β) (Λ : Type w) [LinearOrder Λ]
        (lam : Hypergraph α β × Hypergraph α β → Λ) (𝒯 : Set (Hypergraph α β × Hypergraph α β))
        (θ₀ : ℕ) (W : Set (α ⊕ β)) (ℒ : Set (RootedHypergraph α β)),
        IsTieBreaker P.G.toHypergraph lam → IsTangle P.G.toHypergraph θ₀ 𝒯 → θ ^ 2 ≤ θ₀ →
        W ⊆ zSet P.G.toHypergraph → W.ncard ≤ θ → IsRootless P → P.IsRemovable → IsFine P.G ℒ →
        IsolatesModulo lam 𝒯 W θ P.G ℒ → (∃ Q ∈ 𝓕, HasPatchworkHeart P ℒ Q) →
        ∃ ℒ' : Set (RootedHypergraph α β), IsFine P.G ℒ' ∧ IsRootedLocation P.G ℒ' ∧
          Isolates P.G.toHypergraph lam (θ ^ 2) 𝒯 (rootedLocationToLocation P.G ℒ') ∧
          ∃ Q ∈ 𝓕', HasPatchworkHeart P ℒ' Q := by
  obtain ⟨𝓕₁, h₁, H₁⟩ := theorem_5_3_proof.{u, v, w} h𝓕 hθ
  obtain ⟨𝓕₂, h₂, H₂⟩ := theorem_5_4_proof.{u, v, w} h₁ θ
  obtain ⟨𝓕₃, h₃, H₃⟩ := theorem_5_5_proof.{u, v, w} h₂ hθ
  refine ⟨𝓕₃, h₃, ?_⟩
  intro P Λ _ lam 𝒯 θ₀ W ℒ hTB h𝒯 hθ₀ hWG hWθ hr hrem hfine hiso hheart
  obtain ⟨ℒ₁, W', hW', hS₁, hh₁, hM₁⟩ := H₁ P Λ lam 𝒯 θ₀ W ℒ hTB h𝒯 hθ₀ hWG hWθ hfine hiso hheart
  obtain ⟨ℒ₂, hS₂, hh₂, hM₂⟩ := H₂ P Λ lam 𝒯 θ₀ W' ℒ₁ hTB h𝒯 hθ₀ hrem hS₁ hh₁ hM₁
  have hWfin : W.Finite := (finite_zSet _).subset hWG
  exact H₃ P Λ lam 𝒯 θ₀ W' ℒ₂ hTB h𝒯 hθ₀ (hW'.trans hWG)
    ((Set.ncard_le_ncard hW' hWfin).trans hWθ) hr hS₂ hh₂ hM₂

end GraphMinor.GM20
