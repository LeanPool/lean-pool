/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section4g
import LeanPool.GraphMinor.GM18.Section5

/-!
# Graph Minors XX, Section 4, (4.13) by `w` uses of (4.12)

The paper deduces (4.13) "by $w$ applications of 4.12" (page 336). This file does that when the
new edges `f ∈ F` are not edges of `G₁` (`wellBehaved_replaceSet`). `GraphMinor.GM20.Section4i`
removes this condition by moving to a larger edge type.

`replaceSet 𝓕₁ k w` is the set of (4.13) for `𝓕₁`, `k` and `w`, with that condition. The proof is
by induction on `w`. Let `P₂` be a member with `|F| = w + 1`, and choose `f ∈ F`. We put the piece
`A_f` back in place of the edge `f` (`putBack`). The result `P'` lies in `replaceSet 𝓕₁ k w`, and
`P₂` comes from `P'` by (4.12) with the piece `A_f`. The new edges are not edges of `G₁`, so they
are not edges of `A_f` either, and `P'` is a patchwork.

One case is different. If `A_{f'} = A_f` for some other `f' ∈ F`, then `A_f` is no longer a piece of
the rest, and we take `P' = P₂ \ f` instead. Then `P₂` comes from `P'` by (4.12) with the piece that
has vertex set `πBar(A_f)` and no edges (`rootPiece`).
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

/-- The patchworks of (4.13) for `𝓕₁`, `k` and `w`, when the edges of `F` are not edges of
`G₁`. -/
def replaceSet (𝓕₁ : Set (UnlabeledPatchwork α β)) (k w : ℕ) : Set (UnlabeledPatchwork α β) :=
  {P₂ | ∃ F ⊆ P₂.dom, F.ncard ≤ w ∧ ∃ P₁ ∈ 𝓕₁, Disjoint F P₁.G.edgeSet ∧
    ∃ A : β → RootedHypergraph α β,
      IsRootedLocation P₁.G (A '' F) ∧ P₂.G.roots = P₁.G.roots ∧
      P₂.G.toHypergraph.deleteEdges F = rootedLocationCore P₁.G (A '' F) ∧
      IsCompletionOf (P₁.restrict (P₂.G.deleteEdges F)) (P₂.deleteEdges F) ∧
      ∀ f ∈ F, (A f).roots = P₂.μ f ∧ (P₂.G.ends f).ncard ≤ k}

/-- The set of (4.12) for `𝓕₁` and `k`. -/
def replaceOne (𝓕₁ : Set (UnlabeledPatchwork α β)) (k : ℕ) : Set (UnlabeledPatchwork α β) :=
  {P₂ | ∃ f ∈ P₂.dom, (P₂.G.ends f).ncard ≤ k ∧ ∃ P₁ ∈ 𝓕₁,
      ∃ (A : RootedHypergraph α β) (hA : IsComplemented P₁.G A),
        P₂.G.deleteEdges {f} = complement P₁.G A hA ∧ A.roots = P₂.μ f ∧
        IsCompletionOf (P₁.restrict (P₂.G.deleteEdges {f})) (P₂.deleteEdges {f})}

theorem core_empty (G : RootedHypergraph α β) : rootedLocationCore G ∅ = G.toHypergraph := by
  refine Hypergraph.ext ?_ ?_ ?_
  · ext v
    simp [rootedLocationCore, locationCore, rootedLocationToLocation]
  · ext e
    simp [rootedLocationCore, locationCore, rootedLocationToLocation]
  · funext e v
    simp [rootedLocationCore, locationCore, rootedLocationToLocation]

theorem hyper_deleteEdges_empty (G : Hypergraph α β) : G.deleteEdges ∅ = G := by
  refine Hypergraph.ext rfl (Set.sdiff_empty) ?_
  funext e v
  simp [Hypergraph.deleteEdges]

theorem hyper_deleteEdges_deleteEdges (G : Hypergraph α β) (F F' : Set β) :
    (G.deleteEdges F).deleteEdges F' = G.deleteEdges (F ∪ F') := by
  refine Hypergraph.ext rfl ?_ ?_
  · change (G.edgeSet \ F) \ F' = G.edgeSet \ (F ∪ F')
    rw [Set.sdiff_sdiff]
  · funext e v
    simp [Hypergraph.deleteEdges, not_or, and_assoc]

theorem deleteEdges_ends_of_notMem {G : Hypergraph α β} {F : Set β} {e : β} (he : e ∉ F) :
    (G.deleteEdges F).ends e = G.ends e := by
  ext v
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, he⟩⟩

/-- Facts about a member of `replaceSet`, in the notation of (4.13). -/
structure ReplaceData (P₁ P₂ : UnlabeledPatchwork α β) (F : Set β) (A : β → RootedHypergraph α β)
    (k : ℕ) : Prop where
  dom : F ⊆ P₂.dom
  disj : Disjoint F P₁.G.edgeSet
  loc : IsRootedLocation P₁.G (A '' F)
  roots : P₂.G.roots = P₁.G.roots
  core : P₂.G.toHypergraph.deleteEdges F = rootedLocationCore P₁.G (A '' F)
  res : IsCompletionOf (P₁.restrict (P₂.G.deleteEdges F)) (P₂.deleteEdges F)
  piece : ∀ f ∈ F, (A f).roots = P₂.μ f ∧ (P₂.G.ends f).ncard ≤ k

namespace ReplaceData

variable {P₁ P₂ : UnlabeledPatchwork α β} {F : Set β} {A : β → RootedHypergraph α β} {k : ℕ}

theorem edgeSet (h : ReplaceData P₁ P₂ F A k) : F ⊆ P₂.G.edgeSet := h.dom.trans P₂.dom_subset

theorem vertexSet_eq (h : ReplaceData P₁ P₂ F A k) :
    P₂.G.vertexSet = (rootedLocationCore P₁.G (A '' F)).vertexSet :=
  (congrArg Hypergraph.vertexSet h.core : (P₂.G.toHypergraph.deleteEdges F).vertexSet = _)

theorem mem_core_edgeSet_iff (h : ReplaceData P₁ P₂ F A k) {e : β} :
    e ∈ (rootedLocationCore P₁.G (A '' F)).edgeSet ↔ e ∈ P₂.G.edgeSet ∧ e ∉ F := by
  rw [← h.core]
  rfl

theorem le (h : ReplaceData P₁ P₂ F A k) :
    (P₂.G.deleteEdges F).toHypergraph ≤ P₁.G.toHypergraph := by
  change P₂.G.toHypergraph.deleteEdges F ≤ P₁.G.toHypergraph
  rw [h.core]
  exact core_le h.loc

theorem inc_iff (h : ReplaceData P₁ P₂ F A k) {e : β} (he : e ∈ P₂.G.edgeSet) (heF : e ∉ F)
    (v : α) : P₂.G.Inc e v ↔ P₁.G.Inc e v := by
  have h₁ : e ∈ (P₂.G.toHypergraph.deleteEdges F).edgeSet := ⟨he, heF⟩
  rw [← GM10.inc_iff_of_le h.le h₁]
  exact ⟨fun h' ↦ ⟨h', heF⟩, fun h' ↦ h'.1⟩

theorem ends_eq (h : ReplaceData P₁ P₂ F A k) {f : β} (hf : f ∈ F) :
    P₂.G.ends f = (A f).rootSet := by
  rw [← P₂.μ_set f (h.dom hf), ← (h.piece f hf).1]
  rfl

theorem isComplemented (h : ReplaceData P₁ P₂ F A k) {f : β} (hf : f ∈ F) :
    IsComplemented P₁.G (A f) :=
  h.loc.isComplemented (mem_image_of_mem A hf)

/-- A vertex of `G₂` in `A_f` is a root of `A_f`. -/
theorem root_of_mem (h : ReplaceData P₁ P₂ F A k) {f : β} (hf : f ∈ F) {v : α}
    (hv : v ∈ P₂.G.vertexSet) (hvA : v ∈ (A f).vertexSet) : v ∈ (A f).rootSet :=
  root_of_mem_core (mem_image_of_mem A hf) (h.vertexSet_eq ▸ hv) hvA

/-- An edge of a piece is not an edge of `G₂`. -/
theorem notMem_edgeSet (h : ReplaceData P₁ P₂ F A k) {f : β} (hf : f ∈ F) {e : β}
    (he : e ∈ (A f).edgeSet) : e ∉ P₂.G.edgeSet := by
  intro he₂
  have heG : e ∈ P₁.G.edgeSet := (h.isComplemented hf).le.edgeSet_subset he
  by_cases heF : e ∈ F
  · exact Set.disjoint_left.mp h.disj heF heG
  · exact (mem_core_edgeSet.mp (h.mem_core_edgeSet_iff.mpr ⟨he₂, heF⟩)).2 _
      (mem_image_of_mem A hf) he

theorem dom_iff (h : ReplaceData P₁ P₂ F A k) {e : β} (he : e ∈ P₂.G.edgeSet) (heF : e ∉ F) :
    e ∈ P₂.dom ↔ e ∈ P₁.dom := by
  have := h.res.dom_eq
  rw [Patchwork.restrict_dom h.le] at this
  constructor
  · intro hd
    have : e ∈ (P₂.deleteEdges F).dom := ⟨hd, heF⟩
    rw [h.res.dom_eq, Patchwork.restrict_dom h.le] at this
    exact this.1
  · intro hd
    have : e ∈ P₁.dom ∩ (P₂.G.deleteEdges F).edgeSet := ⟨hd, he, heF⟩
    rw [← Patchwork.restrict_dom h.le, ← h.res.dom_eq] at this
    exact this.1

theorem μ_eq (h : ReplaceData P₁ P₂ F A k) {e : β} (he : e ∈ P₂.G.edgeSet) (heF : e ∉ F)
    (hd : e ∈ P₁.dom) : P₂.μ e = P₁.μ e := by
  have : e ∈ (P₁.restrict (P₂.G.deleteEdges F)).dom := by
    rw [Patchwork.restrict_dom h.le]
    exact ⟨hd, he, heF⟩
  exact h.res.μ_eq this

theorem Δ_eq (h : ReplaceData P₁ P₂ F A k) {e : β} (he : e ∈ P₂.G.edgeSet) (heF : e ∉ F) :
    P₂.Δ e = P₁.Δ e := by
  have h₁ : e ∈ (P₂.G.deleteEdges F).edgeSet := ⟨he, heF⟩
  rw [← Patchwork.restrict_Δ h.le h₁]
  exact h.res.Δ_eq h₁

/-- Members of `replaceSet` are active if the members of `𝓕₁` are. -/
theorem isActive (h : ReplaceData P₁ P₂ F A k) (ha : IsActive P₁) : IsActive P₂ := by
  intro v hv
  by_cases hin : ∃ f ∈ F, v ∈ (A f).vertexSet
  · obtain ⟨f, hf, hvf⟩ := hin
    have hroot := h.root_of_mem hf hv hvf
    rw [← h.ends_eq hf] at hroot
    exact ⟨f, h.dom hf, hroot⟩
  · push Not at hin
    have hvc : v ∈ (rootedLocationCore P₁.G (A '' F)).vertexSet := h.vertexSet_eq ▸ hv
    obtain ⟨e, he, hinc⟩ := ha v ((core_le h.loc).vertexSet_subset hvc)
    have heA : ∀ f ∈ F, e ∉ (A f).edgeSet := fun f hf hef ↦
      hin f hf ((A f).vertex_mem_of_inc
        ((GM10.inc_iff_of_le (h.isComplemented hf).le hef).mpr hinc))
    have hec : e ∈ (rootedLocationCore P₁.G (A '' F)).edgeSet := by
      refine mem_core_edgeSet.mpr ⟨P₁.dom_subset he, ?_⟩
      rintro _ ⟨f, hf, rfl⟩
      exact heA f hf
    obtain ⟨he₂, heF⟩ := h.mem_core_edgeSet_iff.mp hec
    exact ⟨e, (h.dom_iff he₂ heF).mpr he, (h.inc_iff he₂ heF v).mpr hinc⟩

end ReplaceData

theorem mem_replaceSet_iff {𝓕₁ : Set (UnlabeledPatchwork α β)} {k w : ℕ}
    {P₂ : UnlabeledPatchwork α β} :
    P₂ ∈ replaceSet 𝓕₁ k w ↔ ∃ F, F.ncard ≤ w ∧ ∃ P₁ ∈ 𝓕₁, ∃ A, ReplaceData P₁ P₂ F A k := by
  constructor
  · rintro ⟨F, hF, hw, P₁, hP₁, hd, A, hl, hr, hc, hres, hp⟩
    exact ⟨F, hw, P₁, hP₁, A, ⟨hF, hd, hl, hr, hc, hres, hp⟩⟩
  · rintro ⟨F, hw, P₁, hP₁, A, h⟩
    exact ⟨F, h.dom, hw, P₁, hP₁, h.disj, A, h.loc, h.roots, h.core, h.res, h.piece⟩

/-- The case `w = 0`: `G₂ = G₁`, so `P₂` is a completion of `P₁`. -/
theorem replaceSet_zero_subset (𝓕₁ : Set (UnlabeledPatchwork α β)) (k : ℕ) :
    replaceSet 𝓕₁ k 0 ⊆ completions Unit 𝓕₁ := by
  intro P₂ hP₂
  obtain ⟨F, hw, P₁, hP₁, A, h⟩ := mem_replaceSet_iff.mp hP₂
  have hF : F = ∅ := (Set.ncard_eq_zero (P₂.G.edgeSet_finite.subset h.edgeSet)).mp
    (Nat.le_zero.mp hw)
  subst hF
  have hcore := h.core
  rw [image_empty, core_empty, hyper_deleteEdges_empty] at hcore
  have hG : P₂.G = P₁.G := RootedHypergraph.ext_of (congrArg (·.vertexSet) hcore)
    (congrArg (·.edgeSet) hcore) (congrArg (·.Inc) hcore) h.roots
  have hE : ∀ e, e ∈ P₂.G.edgeSet ↔ e ∈ P₁.G.edgeSet := fun e ↦ by rw [hG]
  refine ⟨P₁, hP₁, ⟨hG, ?_, fun e he ↦ ?_, fun e he ↦ ?_⟩⟩
  · ext e
    constructor
    · intro hd
      exact (h.dom_iff (P₂.dom_subset hd) (notMem_empty e)).mp hd
    · intro hd
      exact (h.dom_iff ((hE e).mpr (P₁.dom_subset hd)) (notMem_empty e)).mpr hd
  · exact h.μ_eq ((hE e).mpr (P₁.dom_subset he)) (notMem_empty e) he
  · exact h.Δ_eq ((hE e).mpr he) (notMem_empty e)

/-! ### The piece with no edges -/

/-- The rooted hypergraph with vertex set `πBar(A)`, no edges and roots `π(A)`. -/
def rootPiece (A : RootedHypergraph α β) : RootedHypergraph α β where
  vertexSet := A.rootSet
  edgeSet := ∅
  Inc _ _ := False
  vertex_mem_of_inc _ _ h := h.elim
  edge_mem_of_inc _ _ h := h.elim
  vertexSet_finite := A.roots.finite_toSet
  edgeSet_finite := finite_empty
  roots := A.roots
  roots_nodup := A.roots_nodup
  roots_subset _ hv := hv

theorem isComplemented_rootPiece {G A : RootedHypergraph α β} (h : A.rootSet ⊆ G.vertexSet) :
    IsComplemented G (rootPiece A) :=
  ⟨⟨h, empty_subset _, fun _ he ↦ he.elim⟩, fun _ hv _ ↦ hv, fun _ _ hv _ _ ↦ hv⟩

theorem complement_rootPiece {G A : RootedHypergraph α β} (h : A.rootSet ⊆ G.vertexSet) :
    complement G (rootPiece A) (isComplemented_rootPiece h) = G := by
  refine RootedHypergraph.ext_of ?_ ?_ ?_ rfl
  · ext v
    constructor
    · rintro (hv | hv)
      · exact hv.1
      · exact h hv
    · intro hv
      by_cases hvA : v ∈ A.rootSet
      · exact Or.inr hvA
      · exact Or.inl ⟨hv, hvA⟩
  · exact Set.sdiff_empty
  · funext e v
    apply propext
    exact ⟨fun h' ↦ h'.2, fun h' ↦ ⟨⟨G.edge_mem_of_inc h', notMem_empty e⟩, h'⟩⟩

/-! ### Putting a piece back -/

section PutBack

variable (P₂ P₁ : UnlabeledPatchwork α β) (A₀ : RootedHypergraph α β) (f : β)

/-- `P₂` with the edge `f` replaced by the piece `A₀` of `P₁`, for the induction step. -/
noncomputable def putBack (hdisj : Disjoint A₀.edgeSet P₂.G.edgeSet)
    (hle : A₀.toHypergraph ≤ P₁.G.toHypergraph) : UnlabeledPatchwork α β :=
  open Classical in
  { G :=
      { vertexSet := P₂.G.vertexSet ∪ A₀.vertexSet
        edgeSet := (P₂.G.edgeSet \ {f}) ∪ A₀.edgeSet
        Inc := fun e v ↦ (P₂.G.Inc e v ∧ e ≠ f) ∨ A₀.Inc e v
        vertex_mem_of_inc := fun _ _ h ↦ h.elim (fun h ↦ Or.inl (P₂.G.vertex_mem_of_inc h.1))
          fun h ↦ Or.inr (A₀.vertex_mem_of_inc h)
        edge_mem_of_inc := fun _ _ h ↦ h.elim (fun h ↦ Or.inl ⟨P₂.G.edge_mem_of_inc h.1, h.2⟩)
          fun h ↦ Or.inr (A₀.edge_mem_of_inc h)
        vertexSet_finite := P₂.G.vertexSet_finite.union A₀.vertexSet_finite
        edgeSet_finite := (P₂.G.edgeSet_finite.subset sdiff_subset).union A₀.edgeSet_finite
        roots := P₂.G.roots
        roots_nodup := P₂.G.roots_nodup
        roots_subset := fun v hv ↦ Or.inl (P₂.G.roots_subset v hv) }
    dom := (P₂.dom \ {f}) ∪ (P₁.dom ∩ A₀.edgeSet)
    μ := fun e ↦ if e ∈ A₀.edgeSet then P₁.μ e else P₂.μ e
    Δ := fun e ↦ if e ∈ A₀.edgeSet then P₁.Δ e else P₂.Δ e
    φ := fun _ ↦ ()
    dom_subset := by
      rintro e (⟨hd, hf⟩ | ⟨-, he⟩)
      · exact Or.inl ⟨P₂.dom_subset hd, hf⟩
      · exact Or.inr he
    μ_nodup := by
      rintro e (⟨hd, -⟩ | ⟨hd, he⟩)
      · have he : e ∉ A₀.edgeSet := fun he ↦
          Set.disjoint_left.mp hdisj he (P₂.dom_subset hd)
        simp only [he, ite_false]
        exact P₂.μ_nodup e hd
      · simp only [he, ite_true]
        exact P₁.μ_nodup e hd
    μ_set := by
      rintro e (⟨hd, hf⟩ | ⟨hd, he⟩)
      · have he : e ∉ A₀.edgeSet := fun he ↦
          Set.disjoint_left.mp hdisj he (P₂.dom_subset hd)
        simp only [he, ite_false]
        rw [P₂.μ_set e hd]
        ext v
        exact ⟨fun h ↦ Or.inl ⟨h, hf⟩, fun h ↦ h.elim (fun h ↦ h.1)
          fun h ↦ absurd (A₀.edge_mem_of_inc h) he⟩
      · simp only [he, ite_true]
        rw [P₁.μ_set e hd, hle.ends_eq e he]
        ext v
        exact ⟨fun h ↦ Or.inr h, fun h ↦ h.elim (fun h ↦ absurd (P₂.G.edge_mem_of_inc h.1)
          (Set.disjoint_left.mp hdisj he)) id⟩
    Δ_verts := by
      rintro e (⟨he₂, hf⟩ | he)
      · have he : e ∉ A₀.edgeSet := fun he ↦ Set.disjoint_left.mp hdisj he he₂
        simp only [he, ite_false]
        rw [P₂.Δ_verts e he₂]
        ext v
        exact ⟨fun h ↦ Or.inl ⟨h, hf⟩, fun h ↦ h.elim (fun h ↦ h.1)
          fun h ↦ absurd (A₀.edge_mem_of_inc h) he⟩
      · simp only [he, ite_true]
        rw [P₁.Δ_verts e (hle.edgeSet_subset he), hle.ends_eq e he]
        ext v
        exact ⟨fun h ↦ Or.inr h, fun h ↦ h.elim (fun h ↦ absurd (P₂.G.edge_mem_of_inc h.1)
          (Set.disjoint_left.mp hdisj he)) id⟩
    Δ_free := by
      rintro e (⟨he₂, hf⟩ | he) hnd
      · have he : e ∉ A₀.edgeSet := fun he ↦ Set.disjoint_left.mp hdisj he he₂
        simp only [he, ite_false]
        exact P₂.Δ_free e he₂ fun hd ↦ hnd (Or.inl ⟨hd, hf⟩)
      · simp only [he, ite_true]
        exact P₁.Δ_free e (hle.edgeSet_subset he) fun hd ↦ hnd (Or.inr ⟨hd, he⟩) }

variable {P₂ P₁ A₀ f}
variable (hdisj : Disjoint A₀.edgeSet P₂.G.edgeSet) (hle : A₀.toHypergraph ≤ P₁.G.toHypergraph)

theorem putBack_inc_iff {e : β} {v : α} :
    (putBack P₂ P₁ A₀ f hdisj hle).G.Inc e v ↔ (P₂.G.Inc e v ∧ e ≠ f) ∨ A₀.Inc e v := Iff.rfl

theorem putBack_ends_of_mem {e : β} (he : e ∈ A₀.edgeSet) :
    (putBack P₂ P₁ A₀ f hdisj hle).G.ends e = A₀.ends e := by
  ext v
  exact ⟨fun h ↦ h.elim (fun h ↦ absurd (P₂.G.edge_mem_of_inc h.1)
    (Set.disjoint_left.mp hdisj he)) id, fun h ↦ Or.inr h⟩

theorem putBack_ends_of_notMem {e : β} (he : e ∉ A₀.edgeSet) (hf : e ≠ f) :
    (putBack P₂ P₁ A₀ f hdisj hle).G.ends e = P₂.G.ends e := by
  ext v
  exact ⟨fun h ↦ h.elim (fun h ↦ h.1) fun h ↦ absurd (A₀.edge_mem_of_inc h) he,
    fun h ↦ Or.inl ⟨h, hf⟩⟩

theorem putBack_μ_of_notMem {e : β} (he : e ∉ A₀.edgeSet) :
    (putBack P₂ P₁ A₀ f hdisj hle).μ e = P₂.μ e := by
  simp [putBack, he]

theorem putBack_μ_of_mem {e : β} (he : e ∈ A₀.edgeSet) :
    (putBack P₂ P₁ A₀ f hdisj hle).μ e = P₁.μ e := by
  simp [putBack, he]

theorem putBack_Δ_of_notMem {e : β} (he : e ∉ A₀.edgeSet) :
    (putBack P₂ P₁ A₀ f hdisj hle).Δ e = P₂.Δ e := by
  simp [putBack, he]

theorem putBack_Δ_of_mem {e : β} (he : e ∈ A₀.edgeSet) :
    (putBack P₂ P₁ A₀ f hdisj hle).Δ e = P₁.Δ e := by
  simp [putBack, he]

end PutBack

/-! ### The induction step -/

private theorem mem_replaceOne_of_repeated_piece {𝓕₁ : Set (UnlabeledPatchwork α β)}
    (ha : ∀ P ∈ 𝓕₁, IsActive P) {P₁ P₂ : UnlabeledPatchwork α β}
    (hP₁ : P₁ ∈ 𝓕₁) {F : Set β} {A : β → RootedHypergraph α β} {f : β}
    (hf : f ∈ F) {k w : ℕ} (h : ReplaceData P₁ P₂ F A k) :
    let F' := F \ {f}
    F'.ncard ≤ w → (∃ f' ∈ F', A f' = A f) →
    P₂ ∈ replaceOne (replaceSet 𝓕₁ k w ∩ {P | IsActive P}) k := by
  classical
  intro F' hF'card hdup
  have hF' : F' = F \ {f} := rfl
  have hF'F : F' ⊆ F := sdiff_subset
  have hrootA₀ : (A f).rootSet ⊆ P₂.G.vertexSet := fun v hv ↦ by
    rw [← h.ends_eq hf] at hv
    exact P₂.G.vertex_mem_of_inc hv
  obtain ⟨f', hf', hAf'⟩ := hdup
  set X := P₂.deleteEdges {f} with hX
  have hset : A '' F' = A '' F := by
    refine (image_mono hF'F).antisymm ?_
    rintro _ ⟨g, hg, rfl⟩
    by_cases hgf : g = f
    · subst hgf
      exact ⟨f', hf', hAf'⟩
    · exact ⟨g, ⟨hg, hgf⟩, rfl⟩
  have hFeq : {f} ∪ F' = F := by
    rw [hF', Set.union_sdiff_self, Set.union_eq_right.mpr (singleton_subset_iff.mpr hf)]
  have hdel : X.G.deleteEdges F' = P₂.G.deleteEdges F := by
    refine RootedHypergraph.ext_of rfl ?_ ?_ rfl
    · change (P₂.G.edgeSet \ {f}) \ F' = P₂.G.edgeSet \ F
      rw [Set.sdiff_sdiff, hFeq]
    · have := hyper_deleteEdges_deleteEdges P₂.G.toHypergraph {f} F'
      rw [hFeq] at this
      exact congrArg (·.Inc) this
  have hXd : ReplaceData P₁ X F' A k := by
    refine ⟨fun g hg ↦ ⟨h.dom (hF'F hg), hg.2⟩, h.disj.mono_left hF'F, hset ▸ h.loc, h.roots,
      ?_, ?_, fun g hg ↦ ?_⟩
    · rw [hset, ← h.core]
      have := hyper_deleteEdges_deleteEdges P₂.G.toHypergraph {f} F'
      rw [hFeq] at this
      exact this
    · rw [hdel]
      have := deleteEdges_deleteEdges P₂ {f} F'
      rw [hFeq] at this
      exact h.res.trans this.symm
    · refine ⟨(h.piece g (hF'F hg)).1, ?_⟩
      have : X.G.ends g = P₂.G.ends g := deleteEdges_ends_of_notMem hg.2
      rw [this]
      exact (h.piece g (hF'F hg)).2
  have hXmem : X ∈ replaceSet 𝓕₁ k w := mem_replaceSet_iff.mpr ⟨F', hF'card, P₁, hP₁, A, hXd⟩
  have hrootX : (A f).rootSet ⊆ X.G.vertexSet := hrootA₀
  refine ⟨f, h.dom hf, (h.piece f hf).2, X, ⟨hXmem, hXd.isActive (ha P₁ hP₁)⟩, rootPiece (A f),
    isComplemented_rootPiece hrootX, ?_, (h.piece f hf).1, ?_⟩
  · rw [complement_rootPiece hrootX]
    rfl
  · refine ⟨rfl, ?_, fun _ _ ↦ rfl, fun e he ↦ ?_⟩
    · change X.dom = (X.restrict X.G).dom
      rw [Patchwork.restrict_dom le_rfl, Set.inter_eq_left.mpr X.dom_subset]
    · exact (Patchwork.restrict_Δ (P := X) (G' := X.G) le_rfl he).symm

/-- The induction step: a member of `replaceSet 𝓕₁ k (w + 1)` lies in `replaceSet 𝓕₁ k w` or comes
by (4.12) from an active member of `replaceSet 𝓕₁ k w`. -/
theorem replaceSet_succ_subset {𝓕₁ : Set (UnlabeledPatchwork α β)} (ha : ∀ P ∈ 𝓕₁, IsActive P)
    (k w : ℕ) : replaceSet 𝓕₁ k (w + 1) ⊆
      replaceSet 𝓕₁ k w ∪ replaceOne (replaceSet 𝓕₁ k w ∩ {P | IsActive P}) k := by
  classical
  intro P₂ hP₂
  obtain ⟨F, hw, P₁, hP₁, A, h⟩ := mem_replaceSet_iff.mp hP₂
  by_cases hcard : F.ncard ≤ w
  · exact Or.inl (mem_replaceSet_iff.mpr ⟨F, hcard, P₁, hP₁, A, h⟩)
  have hFfin : F.Finite := P₂.G.edgeSet_finite.subset h.edgeSet
  obtain ⟨f, hf⟩ : F.Nonempty := by
    rw [← Set.ncard_pos hFfin]
    omega
  set F' := F \ {f} with hF'
  have hF'card : F'.ncard ≤ w := by
    rw [hF', Set.ncard_sdiff (singleton_subset_iff.mpr hf) (Set.finite_singleton f),
      Set.ncard_singleton]
    omega
  have hF'F : F' ⊆ F := sdiff_subset
  have hfE : f ∈ P₂.G.edgeSet := h.edgeSet hf
  have hA₀ := h.isComplemented hf
  have hrootA₀ : (A f).rootSet ⊆ P₂.G.vertexSet := fun v hv ↦ by
    rw [← h.ends_eq hf] at hv
    exact P₂.G.vertex_mem_of_inc hv
  right
  by_cases hdup : ∃ f' ∈ F', A f' = A f
  · exact mem_replaceOne_of_repeated_piece ha hP₁ hf h hF'card hdup
  · -- Otherwise put `A_f` back in place of `f`.
    push Not at hdup
    set A₀ := A f with hA₀def
    have hdisj : Disjoint A₀.edgeSet P₂.G.edgeSet :=
      Set.disjoint_left.mpr fun _ he ↦ h.notMem_edgeSet hf he
    set X := putBack P₂ P₁ A₀ f hdisj hA₀.le with hX
    have hA₀mem : A₀ ∈ A '' F := mem_image_of_mem A hf
    -- `A₀` lies in the complement of every other piece.
    have hA₀le : ∀ g (hg : g ∈ F'), A₀.toHypergraph ≤ (complement P₁.G (A g)
        (h.isComplemented (hF'F hg))).toHypergraph := fun g hg ↦
      h.loc.le_complement hA₀mem (mem_image_of_mem A (hF'F hg)) (hdup g hg).symm
    have hF'G : ∀ g ∈ F', g ∉ P₁.G.edgeSet := fun g hg ↦
      Set.disjoint_left.mp h.disj (hF'F hg)
    have hF'A : ∀ g ∈ F', g ∉ A₀.edgeSet := fun g hg hgA ↦
      hF'G g hg (hA₀.le.edgeSet_subset hgA)
    have hloc' : IsRootedLocation P₁.G (A '' F') := h.loc.mono (image_mono hF'F)
    have hXle : (X.G.toHypergraph.deleteEdges F') ≤ P₁.G.toHypergraph := by
      refine ⟨?_, ?_, ?_⟩
      · rintro v (hv | hv)
        · exact (core_le h.loc).vertexSet_subset (h.vertexSet_eq ▸ hv)
        · exact hA₀.le.vertexSet_subset hv
      · rintro e ⟨(⟨he, hef⟩ | he), heF'⟩
        · have heF : e ∉ F := fun heF ↦ heF' ⟨heF, hef⟩
          exact (core_le h.loc).edgeSet_subset (h.mem_core_edgeSet_iff.mpr ⟨he, heF⟩)
        · exact hA₀.le.edgeSet_subset he
      · rintro e ⟨(⟨he, hef⟩ | he), heF'⟩
        · have heF : e ∉ F := fun heF ↦ heF' ⟨heF, hef⟩
          have heA : e ∉ A₀.edgeSet := fun heA ↦ Set.disjoint_left.mp hdisj heA he
          rw [deleteEdges_ends_of_notMem heF', putBack_ends_of_notMem (f := f) hdisj hA₀.le heA hef]
          ext v
          exact (h.inc_iff he heF v).symm
        · rw [deleteEdges_ends_of_notMem heF', putBack_ends_of_mem (f := f) hdisj hA₀.le he]
          exact hA₀.le.ends_eq e he
    have hXcore : X.G.toHypergraph.deleteEdges F' = rootedLocationCore P₁.G (A '' F') := by
      refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hXle (core_le hloc') ?_ ?_
      · ext v
        rw [mem_core_vertexSet]
        constructor
        · rintro (hv | hv)
          · have := mem_core_vertexSet.mp (h.vertexSet_eq ▸ hv)
            exact ⟨this.1, fun B hB ↦ this.2 B (image_mono hF'F hB)⟩
          · refine ⟨hA₀.le.vertexSet_subset hv, ?_⟩
            rintro _ ⟨g, hg, rfl⟩
            have hvc := (hA₀le g hg).vertexSet_subset hv
            rcases hvc with hvc | hvc
            · exact Or.inl hvc
            · exact Or.inr ⟨hA₀.le.vertexSet_subset hv, hvc⟩
        · rintro ⟨hvG, hall⟩
          by_cases hvA : v ∈ A₀.vertexSet
          · exact Or.inr hvA
          · left
            refine h.vertexSet_eq ▸ mem_core_vertexSet.mpr ⟨hvG, ?_⟩
            rintro _ ⟨g, hg, rfl⟩
            by_cases hgf : g = f
            · subst hgf
              exact Or.inl ⟨hvG, hvA⟩
            · exact hall _ ⟨g, ⟨hg, hgf⟩, rfl⟩
      · ext e
        rw [mem_core_edgeSet]
        constructor
        · rintro ⟨(⟨he, hef⟩ | he), heF'⟩
          · have heF : e ∉ F := fun heF ↦ heF' ⟨heF, hef⟩
            have := mem_core_edgeSet.mp (h.mem_core_edgeSet_iff.mpr ⟨he, heF⟩)
            exact ⟨this.1, fun B hB ↦ this.2 B (image_mono hF'F hB)⟩
          · refine ⟨hA₀.le.edgeSet_subset he, ?_⟩
            rintro _ ⟨g, hg, rfl⟩
            exact ((hA₀le g hg).edgeSet_subset he).2
        · rintro ⟨heG, hall⟩
          by_cases heA : e ∈ A₀.edgeSet
          · exact ⟨Or.inr heA, fun heF' ↦ hF'A e heF' heA⟩
          · have hcore : e ∈ (rootedLocationCore P₁.G (A '' F)).edgeSet := by
              refine mem_core_edgeSet.mpr ⟨heG, ?_⟩
              rintro _ ⟨g, hg, rfl⟩
              by_cases hgf : g = f
              · subst hgf
                exact heA
              · exact hall _ ⟨g, ⟨hg, hgf⟩, rfl⟩
            obtain ⟨he, heF⟩ := h.mem_core_edgeSet_iff.mp hcore
            exact ⟨Or.inl ⟨he, fun hef ↦ heF (hef ▸ hf)⟩, fun heF' ↦ heF heF'.1⟩
    have hXd : ReplaceData P₁ X F' A k := by
      refine ⟨fun g hg ↦ Or.inl ⟨h.dom (hF'F hg), hg.2⟩, h.disj.mono_left hF'F, hloc', h.roots,
        hXcore, ?_, fun g hg ↦ ?_⟩
      · have hXle' : (X.G.deleteEdges F').toHypergraph ≤ P₁.G.toHypergraph := hXle
        refine ⟨rfl, ?_, fun e he ↦ ?_, fun e he ↦ ?_⟩
        · rw [Patchwork.restrict_dom hXle']
          ext e
          constructor
          · rintro ⟨(⟨hd, hef⟩ | ⟨hd, he⟩), heF'⟩
            · have heF : e ∉ F := fun heF ↦ heF' ⟨heF, hef⟩
              exact ⟨(h.dom_iff (P₂.dom_subset hd) heF).mp hd,
                Or.inl ⟨P₂.dom_subset hd, hef⟩, heF'⟩
            · exact ⟨hd, Or.inr he, heF'⟩
          · rintro ⟨hd, (⟨he, hef⟩ | he), heF'⟩
            · have heF : e ∉ F := fun heF ↦ heF' ⟨heF, hef⟩
              exact ⟨Or.inl ⟨(h.dom_iff he heF).mpr hd, hef⟩, heF'⟩
            · exact ⟨Or.inr ⟨hd, he⟩, heF'⟩
        · rw [Patchwork.restrict_dom hXle'] at he
          obtain ⟨hd, (⟨he, hef⟩ | he), heF'⟩ := he
          · have heF : e ∉ F := fun heF ↦ heF' ⟨heF, hef⟩
            have heA : e ∉ A₀.edgeSet := fun heA ↦ Set.disjoint_left.mp hdisj heA he
            change X.μ e = P₁.μ e
            rw [putBack_μ_of_notMem (f := f) hdisj hA₀.le heA]
            exact h.μ_eq he heF hd
          · change X.μ e = P₁.μ e
            exact putBack_μ_of_mem (f := f) hdisj hA₀.le he
        · change X.Δ e = (P₁.restrict (X.G.deleteEdges F')).Δ e
          rw [Patchwork.restrict_Δ hXle' he]
          obtain ⟨(⟨he, hef⟩ | he), heF'⟩ := he
          · have heF : e ∉ F := fun heF ↦ heF' ⟨heF, hef⟩
            have heA : e ∉ A₀.edgeSet := fun heA ↦ Set.disjoint_left.mp hdisj heA he
            rw [putBack_Δ_of_notMem (f := f) hdisj hA₀.le heA]
            exact h.Δ_eq he heF
          · exact putBack_Δ_of_mem (f := f) hdisj hA₀.le he
      · have hgA := hF'A g hg
        refine ⟨?_, ?_⟩
        · rw [putBack_μ_of_notMem (f := f) hdisj hA₀.le hgA]
          exact (h.piece g (hF'F hg)).1
        · rw [putBack_ends_of_notMem (f := f) hdisj hA₀.le hgA hg.2]
          exact (h.piece g (hF'F hg)).2
    have hXmem : X ∈ replaceSet 𝓕₁ k w := mem_replaceSet_iff.mpr ⟨F', hF'card, P₁, hP₁, A, hXd⟩
    -- `A₀` is complemented in `X`.
    have hB : IsComplemented X.G A₀ := by
      refine ⟨⟨fun v hv ↦ Or.inr hv, fun e he ↦ Or.inr he, fun e he ↦
        putBack_ends_of_mem (f := f) hdisj hA₀.le he⟩, fun v hv hvr ↦ ?_, fun v e hv he hinc ↦ ?_⟩
      · have hvr' : v ∈ P₁.G.roots := h.roots ▸ hvr
        exact hA₀.roots_mem hv hvr'
      · rcases hinc with hinc | hinc
        · exact h.root_of_mem hf (P₂.G.vertex_mem_of_inc hinc.1) hv
        · exact absurd (A₀.edge_mem_of_inc hinc) he.2
    have hcompl : P₂.G.deleteEdges {f} = complement X.G A₀ hB := by
      refine RootedHypergraph.ext_of ?_ ?_ ?_ rfl
      · ext v
        constructor
        · intro hv
          by_cases hvA : v ∈ A₀.vertexSet
          · exact Or.inr (h.root_of_mem hf hv hvA)
          · exact Or.inl ⟨Or.inl hv, hvA⟩
        · rintro (⟨hv | hv, hvA⟩ | hv)
          · exact hv
          · exact absurd hv hvA
          · exact hrootA₀ hv
      · ext e
        constructor
        · rintro ⟨he, hef⟩
          exact ⟨Or.inl ⟨he, hef⟩, fun heA ↦ Set.disjoint_left.mp hdisj heA he⟩
        · rintro ⟨(⟨he, hef⟩ | he), heA⟩
          · exact ⟨he, hef⟩
          · exact absurd he heA
      · funext e v
        apply propext
        constructor
        · rintro ⟨hinc, hef⟩
          have he := P₂.G.edge_mem_of_inc hinc
          exact ⟨⟨Or.inl ⟨he, hef⟩, fun heA ↦ Set.disjoint_left.mp hdisj heA he⟩,
            Or.inl ⟨hinc, hef⟩⟩
        · rintro ⟨⟨-, heA⟩, hinc | hinc⟩
          · exact hinc
          · exact absurd (A₀.edge_mem_of_inc hinc) heA
    have hle₃ : (P₂.G.deleteEdges {f}).toHypergraph ≤ X.G.toHypergraph := by
      rw [hcompl]
      exact complement_le hB
    refine ⟨f, h.dom hf, (h.piece f hf).2, X, ⟨hXmem, hXd.isActive (ha P₁ hP₁)⟩, A₀, hB, hcompl,
      (h.piece f hf).1, ⟨rfl, ?_, fun e he ↦ ?_, fun e he ↦ ?_⟩⟩
    · rw [Patchwork.restrict_dom hle₃]
      ext e
      constructor
      · rintro ⟨hd, hef⟩
        exact ⟨Or.inl ⟨hd, hef⟩, P₂.dom_subset hd, hef⟩
      · rintro ⟨(hd | ⟨-, heA⟩), he, -⟩
        · exact hd
        · exact absurd he (Set.disjoint_left.mp hdisj heA)
    · rw [Patchwork.restrict_dom hle₃] at he
      have heA : e ∉ A₀.edgeSet := fun heA ↦ Set.disjoint_left.mp hdisj heA he.2.1
      exact (putBack_μ_of_notMem (f := f) hdisj hA₀.le heA).symm
    · change P₂.Δ e = (X.restrict (P₂.G.deleteEdges {f})).Δ e
      rw [Patchwork.restrict_Δ hle₃ he]
      have heA : e ∉ A₀.edgeSet := fun heA ↦ Set.disjoint_left.mp hdisj heA he.1
      exact (putBack_Δ_of_notMem (f := f) hdisj hA₀.le heA).symm

/-- Graph Minors XX, (4.13) (page 336), when the new edges are not edges of `G₁`: by `w` uses of
(4.12). -/
theorem wellBehaved_replaceSet {𝓕₁ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁)
    (ha : ∀ P ∈ 𝓕₁, IsActive P) (k : ℕ) : ∀ w, WellBehaved (replaceSet 𝓕₁ k w)
  | 0 => h.completions.mono (replaceSet_zero_subset 𝓕₁ k)
  | w + 1 => by
    have ih := wellBehaved_replaceSet h ha k w
    exact (ih.union (theorem_4_12_proof (ih.mono inter_subset_left) (fun _ hP ↦ hP.2) k
      (𝓕₂ := replaceOne (replaceSet 𝓕₁ k w ∩ {P | IsActive P}) k) fun _ hP ↦ hP)).mono
      (replaceSet_succ_subset ha k w)

end GraphMinor.GM20
