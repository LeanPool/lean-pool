/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Defs2
public import LeanPool.GraphMinor.GM11.Section6

/-!
# A tangle in a hypergraph with the same adjacencies

Graph Minors XIX, proof of (15.2), page 382, uses (14.1) of Graph Minors XVII to pass from a tangle
in `Γ` to a tangle in `sk(Γ)`.
There `G*` is a simple graph, and `sk(Γ)` is a drawing that may have parallel edges. So we show that
a tangle moves from `G*` to
any hypergraph on the same vertices (up to an injection `ι`) in which every adjacent pair of `G*`
lies in an edge. The result used
later is `isTangle_skeletonTangle`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Hypergraph GraphMinor.GM10 GraphMinor.GM17

universe u v u' v'

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- The set `𝒯'` of the proof of (15.2) (page 382): "the set of all separations $(A', B')$ of
$sk(\Gamma)$ of order $\le n$ such that there
exists $(A, B) \in \mathscr{T}$ with $V(A) = V(A')$ and $V(B) = V(B')$". -/
def skeletonTangle (ι : α → α') (H : Hypergraph α' β') (𝒯 : Set (Hypergraph α β × Hypergraph α β))
  (m : ℕ) : Set (Hypergraph α' β' × Hypergraph α' β') :=
  {p | H.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < m ∧ ∃ q ∈ 𝒯, ι '' q.1.vertexSet
    = p.1.vertexSet ∧ ι '' q.2.vertexSet = p.2.vertexSet}

/-- The part of `G*` with vertex set `P` and edge set `E`. -/
def skeletonPart (G : Hypergraph α β) (P : Set α) (E : Set (Sym2 α)) (hP : P ⊆ G.vertexSet)
  (hE : E ⊆ (oneSkeletonHypergraph G).edgeSet) (hEP : ∀ e ∈ E, ∀ v ∈ e, v ∈ P) : Hypergraph α
    (Sym2 α) where
  vertexSet := P
  edgeSet := E
  Inc e v := e ∈ E ∧ v ∈ e
  vertex_mem_of_inc := fun e v h ↦ hEP e h.1 v h.2
  edge_mem_of_inc := fun _ _ h ↦ h.1
  vertexSet_finite := G.vertexSet_finite.subset hP
  edgeSet_finite := (oneSkeletonHypergraph G).edgeSet_finite.subset hE

variable {ι : α → α'} {H : Hypergraph α' β'} {G : Hypergraph α β}

/-- A separation of `H` gives a separation of `G*` with the same vertex sets. An edge of `G*` goes
to the first side if an edge of
the first side of `H` contains it, and to the second side otherwise. -/
theorem exists_skeleton_separation (hV : H.vertexSet = ι '' G.vertexSet)
  (hadj : ∀ x y, G.skeleton.Adj x y → ∃ f ∈ H.edgeSet, H.Inc f (ι x) ∧ H.Inc f
    (ι y)) {A B : Hypergraph α' β'}
    (hsep : H.IsSeparation A B) : ∃ A' B' : Hypergraph α (Sym2 α), (oneSkeletonHypergraph
      G).IsSeparation A' B' ∧ A'.vertexSet = ι ⁻¹' A.vertexSet ∩ G.vertexSet ∧
      B'.vertexSet = ι ⁻¹' B.vertexSet ∩ G.vertexSet ∧ ∀ e ∈ (oneSkeletonHypergraph G).edgeSet,
        (∃ f ∈ A.edgeSet, ∀ v ∈ e, H.Inc f (ι v)) → e ∈ A'.edgeSet := by
  classical
  let E₁ : Set (Sym2 α) := {e | e ∈ (oneSkeletonHypergraph G).edgeSet
    ∧ ∃ f ∈ A.edgeSet, ∀ v ∈ e, H.Inc f (ι v)}
  let E₂ : Set (Sym2 α) := (oneSkeletonHypergraph G).edgeSet \ E₁
  have hE₀ : ∀ e ∈ (oneSkeletonHypergraph G).edgeSet, ∀ v ∈ e, v ∈ G.vertexSet := fun e he v hv ↦
    (oneSkeletonHypergraph G).vertex_mem_of_inc ⟨he, hv⟩
  have hinc : ∀ {X : Hypergraph α' β'}, X ≤ H → ∀ {f a}, f ∈ X.edgeSet → H.Inc f a
    → a ∈ X.vertexSet := by
    intro X hX f a hf ha
    have h₁ : a ∈ H.ends f := ha
    rw [hX.ends_eq f hf] at h₁
    exact X.vertex_mem_of_inc h₁
  have hP₁ : ∀ e ∈ E₁, ∀ v ∈ e, v ∈ ι ⁻¹' A.vertexSet ∩ G.vertexSet := by
    rintro e ⟨he, f, hf, hall⟩ v hv
    exact ⟨hinc hsep.left_le hf (hall v hv), hE₀ e he v hv⟩
  have hP₂ : ∀ e ∈ E₂, ∀ v ∈ e, v ∈ ι ⁻¹' B.vertexSet ∩ G.vertexSet := by
    rintro e ⟨he, hn⟩ v hv
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨f, hf, hx, hy⟩ := hadj x y he
      have hall : ∀ w ∈ s(x, y), H.Inc f (ι w) := fun w hw ↦ by
        rcases Sym2.mem_iff.mp hw with rfl | rfl
        · exact hx
        · exact hy
      have hfU : f ∈ (A ∪ B).edgeSet := by
        rw [hsep.union_eq]
        exact hf
      rcases hfU with hfA | hfB
      · exact absurd ⟨he, f, hfA, hall⟩ hn
      · exact ⟨hinc hsep.right_le hfB (hall v hv), hE₀ _ he v hv⟩
  let A' := skeletonPart G (ι ⁻¹' A.vertexSet ∩ G.vertexSet) E₁ inter_subset_right
    (fun _ h ↦ h.1) hP₁
  let B' := skeletonPart G (ι ⁻¹' B.vertexSet ∩ G.vertexSet) E₂ inter_subset_right
    (fun _ h ↦ h.1) hP₂
  have hle : ∀ {P E h₁ h₂ h₃}, skeletonPart G P E h₁ h₂ h₃ ≤ oneSkeletonHypergraph G
    := fun {P E h₁ h₂ h₃} ↦ ⟨h₁, h₂, fun e he ↦ by
    ext v
    exact ⟨fun h ↦ ⟨he, h.2⟩, fun h ↦ ⟨h₂ he, h.2⟩⟩⟩
  refine ⟨A', B', ⟨hle, hle, ?_, ?_⟩, rfl, rfl, fun e he hx ↦ ⟨he, hx⟩⟩
  · refine Hypergraph.ext ?_ ?_ ?_
    · change (ι ⁻¹' A.vertexSet ∩ G.vertexSet) ∪ (ι ⁻¹' B.vertexSet ∩ G.vertexSet) = G.vertexSet
      refine Subset.antisymm (union_subset inter_subset_right inter_subset_right) fun x hx ↦ ?_
      have h₁ : ι x ∈ H.vertexSet := hV ▸ mem_image_of_mem _ hx
      rw [← hsep.union_eq] at h₁
      rcases h₁ with h | h
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨h, hx⟩
    · change E₁ ∪ E₂ = _
      exact union_sdiff_cancel fun _ h ↦ h.1
    · ext e v
      constructor
      · rintro (h | h)
        · exact ⟨h.1.1, h.2⟩
        · exact ⟨h.1.1, h.2⟩
      · rintro ⟨he, hv⟩
        by_cases h : e ∈ E₁
        · exact Or.inl ⟨h, hv⟩
        · exact Or.inr ⟨⟨he, h⟩, hv⟩
  · ext e
    constructor
    · rintro ⟨h₁, h₂⟩
      exact absurd h₁ h₂.2
    · exact fun h ↦ absurd h (notMem_empty e)

/-- **`𝒯'` is a tangle.** -/
theorem isTangle_skeletonTangle (hι : Function.Injective ι) (hV : H.vertexSet = ι '' G.vertexSet)
  (hadj : ∀ x y, G.skeleton.Adj x y → ∃ f ∈ H.edgeSet, H.Inc f (ι x) ∧ H.Inc f (ι y))
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {m : ℕ} (h𝒯 : ∀ q ∈ 𝒯, G.IsSeparation q.1 q.2)
      (hT : IsTangle (oneSkeletonHypergraph G) m (oneSkeletonTangle G 𝒯 m)) : IsTangle H m
        (skeletonTangle ι H 𝒯 m) := by
  have hord : ∀ {A B A' B'}, H.IsSeparation A B → (A' : Hypergraph α (Sym2 α)).vertexSet
    = ι ⁻¹' A.vertexSet ∩ G.vertexSet → (B' : Hypergraph α (Sym2 α)).vertexSet
      = ι ⁻¹' B.vertexSet ∩ G.vertexSet →
      separationOrder A' B' = separationOrder A B := by
    intro A B A' B' hsep hA hB
    have hset : (A ∩ B).vertexSet = ι '' (A' ∩ B').vertexSet := by
      ext x
      constructor
      · rintro ⟨h₁, h₂⟩
        have hx : x ∈ ι '' G.vertexSet := hV ▸ hsep.left_le.vertexSet_subset h₁
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨y, ⟨hA ▸ ⟨h₁, hy⟩, hB ▸ ⟨h₂, hy⟩⟩, rfl⟩
      · rintro ⟨y, ⟨h₁, h₂⟩, rfl⟩
        rw [hA] at h₁
        rw [hB] at h₂
        exact ⟨h₁.1, h₂.1⟩
    rw [separationOrder, separationOrder, hset, ncard_image_of_injective _ hι]
  have hVeq : ∀ {A}, A ≤ H → ι '' (ι ⁻¹' A.vertexSet ∩ G.vertexSet) = A.vertexSet := by
    intro A hA
    ext x
    constructor
    · rintro ⟨y, ⟨h, -⟩, rfl⟩
      exact h
    · intro hx
      have hx' : x ∈ ι '' G.vertexSet := hV ▸ hA.vertexSet_subset hx
      obtain ⟨y, hy, rfl⟩ := hx'
      exact ⟨y, ⟨hx, hy⟩, rfl⟩
  have hback : ∀ {Q : Set α}, Q ⊆ G.vertexSet → ι ⁻¹' (ι '' Q) ∩ G.vertexSet = Q := fun {Q} hQ ↦ by
    rw [preimage_image_eq _ hι, inter_eq_left.mpr hQ]
  refine ⟨hT.one_le, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2.1, fun A B hsep ho ↦ ?_,
    fun A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ hU ↦ ?_, fun A B h hAV ↦ ?_⟩
  · obtain ⟨A', B', hs, hA, hB, -⟩ := exists_skeleton_separation hV hadj hsep
    have ho' : separationOrder A' B' < m := by rwa [hord hsep hA hB]
    rcases hT.axiom1 hs ho' with ⟨-, -, q, hq, h₁, h₂⟩ | ⟨-, -, q, hq, h₁, h₂⟩
    · exact Or.inl ⟨hsep, ho, q, hq, by rw [h₁, hA, hVeq hsep.left_le], by rw [h₂, hB,
        hVeq hsep.right_le]⟩
    · refine Or.inr ⟨hsep.symm, by rwa [separationOrder_comm], q, hq, ?_, ?_⟩
      · change ι '' q.1.vertexSet = B.vertexSet
        rw [h₁, hB, hVeq hsep.right_le]
      · change ι '' q.2.vertexSet = A.vertexSet
        rw [h₂, hA, hVeq hsep.left_le]
  · have hmem : ∀ {A B}, (A, B) ∈ skeletonTangle ι H 𝒯 m → ∃ A' B' : Hypergraph α (Sym2 α),
    (A', B') ∈ oneSkeletonTangle G 𝒯 m ∧ A'.vertexSet = ι ⁻¹' A.vertexSet ∩ G.vertexSet ∧
        ∀ e ∈ (oneSkeletonHypergraph G).edgeSet, (∃ f ∈ A.edgeSet, ∀ v ∈ e, H.Inc f (ι v))
          → e ∈ A'.edgeSet := fun {A B} h ↦ by
      obtain ⟨hs, ho, hc⟩ := h
      obtain ⟨A', B', hs', hA, hB, hE⟩ := exists_skeleton_separation hV hadj hs
      exact ⟨A', B', ⟨hs', by rwa [hord hs hA hB], Exists.elim hc fun q hq ↦ ⟨q, hq.1, by rw [hA, ←
        hq.2.1, hback (h𝒯 q hq.1).left_le.vertexSet_subset], by rw [hB, ← hq.2.2, hback
          (h𝒯 q hq.1).right_le.vertexSet_subset]⟩⟩, hA, hE⟩
    obtain ⟨X₁, Y₁, m₁, hX₁, hE₁⟩ := hmem h₁
    obtain ⟨X₂, Y₂, m₂, hX₂, hE₂⟩ := hmem h₂
    obtain ⟨X₃, Y₃, m₃, hX₃, hE₃⟩ := hmem h₃
    refine hT.axiom2 m₁ m₂ m₃ ?_
    have hs₁ := hT.isSeparation m₁
    have hs₂ := hT.isSeparation m₂
    have hs₃ := hT.isSeparation m₃
    set U := X₁ ∪ X₂ ∪ X₃ with hUdef
    have hincI : ∀ {X : Hypergraph α (Sym2 α)}, X ≤ oneSkeletonHypergraph G → ∀ {e v}, X.Inc e v →
      (oneSkeletonHypergraph G).Inc e v := fun {X} hX {e v} h ↦ by
      have h₀ : v ∈ X.ends e := h
      rw [← hX.ends_eq e (X.edge_mem_of_inc h)] at h₀
      exact h₀
    have hincE : ∀ {X : Hypergraph α (Sym2 α)}, X ≤ oneSkeletonHypergraph G
      → ∀ {e v}, e ∈ X.edgeSet → (oneSkeletonHypergraph G).Inc e v → X.Inc e v
        := fun {X} hX {e v} he h ↦ by
      have h₀ : v ∈ (oneSkeletonHypergraph G).ends e := h
      rw [hX.ends_eq e he] at h₀
      exact h₀
    have hends : ∀ e ∈ U.edgeSet, (oneSkeletonHypergraph G).ends e = U.ends e := by
      intro e he
      ext v
      constructor
      · intro hv
        rcases he with (h | h) | h
        · exact Or.inl (Or.inl (hincE hs₁.left_le h hv))
        · exact Or.inl (Or.inr (hincE hs₂.left_le h hv))
        · exact Or.inr (hincE hs₃.left_le h hv)
      · rintro ((h | h) | h)
        · exact hincI hs₁.left_le h
        · exact hincI hs₂.left_le h
        · exact hincI hs₃.left_le h
    refine le_antisymm (Hypergraph.IsSubhypergraph.mk ?_ ?_ hends) (Hypergraph.IsSubhypergraph.mk
      ?_ ?_ fun e he ↦ ?_)
    · rintro x ((h | h) | h)
      · exact hs₁.left_le.vertexSet_subset h
      · exact hs₂.left_le.vertexSet_subset h
      · exact hs₃.left_le.vertexSet_subset h
    · rintro x ((h | h) | h)
      · exact hs₁.left_le.edgeSet_subset h
      · exact hs₂.left_le.edgeSet_subset h
      · exact hs₃.left_le.edgeSet_subset h
    · intro x hx
      have h₀ : ι x ∈ H.vertexSet := hV ▸ mem_image_of_mem _ hx
      rw [← hU] at h₀
      rcases h₀ with (h | h) | h
      · exact Or.inl (Or.inl (hX₁ ▸ ⟨h, hx⟩))
      · exact Or.inl (Or.inr (hX₂ ▸ ⟨h, hx⟩))
      · exact Or.inr (hX₃ ▸ ⟨h, hx⟩)
    · have key : ∀ e ∈ (oneSkeletonHypergraph G).edgeSet, e ∈ U.edgeSet := by
        intro e he
        induction e using Sym2.ind with
        | _ x y =>
          obtain ⟨f, hf, hx, hy⟩ := hadj x y he
          have hall : ∀ w ∈ s(x, y), H.Inc f (ι w) := fun w hw ↦ by
            rcases Sym2.mem_iff.mp hw with rfl | rfl
            · exact hx
            · exact hy
          have hf' : f ∈ (A₁ ∪ A₂ ∪ A₃).edgeSet := by
            rw [hU]
            exact hf
          rcases hf' with (h | h) | h
          · exact Or.inl (Or.inl (hE₁ _ he ⟨f, h, hall⟩))
          · exact Or.inl (Or.inr (hE₂ _ he ⟨f, h, hall⟩))
          · exact Or.inr (hE₃ _ he ⟨f, h, hall⟩)
      exact key
    · have he' : e ∈ U.edgeSet := by
        induction e using Sym2.ind with
        | _ x y =>
          obtain ⟨f, hf, hx, hy⟩ := hadj x y he
          have hall : ∀ w ∈ s(x, y), H.Inc f (ι w) := fun w hw ↦ by
            rcases Sym2.mem_iff.mp hw with rfl | rfl
            · exact hx
            · exact hy
          have hf' : f ∈ (A₁ ∪ A₂ ∪ A₃).edgeSet := by
            rw [hU]
            exact hf
          rcases hf' with (h | h) | h
          · exact Or.inl (Or.inl (hE₁ _ he ⟨f, h, hall⟩))
          · exact Or.inl (Or.inr (hE₂ _ he ⟨f, h, hall⟩))
          · exact Or.inr (hE₃ _ he ⟨f, h, hall⟩)
      exact (hends e he').symm
  · have hs := h.1
    obtain ⟨A', B', hs', hA, hB, -⟩ := exists_skeleton_separation hV hadj hs
    obtain ⟨q, hq, h₁, h₂⟩ := h.2.2
    refine hT.axiom3 (A := A') (B := B') ⟨hs', (hord hs hA hB).trans_lt h.2.1, q, hq, by rw [hA, ←
      h₁, hback (h𝒯 q hq).left_le.vertexSet_subset], by rw [hB, ← h₂, hback
        (h𝒯 q hq).right_le.vertexSet_subset]⟩ ?_
    change _ = G.vertexSet
    rw [hA, hAV]
    rw [hV, preimage_image_eq _ hι, Set.inter_self]

end GraphMinor.GM19
