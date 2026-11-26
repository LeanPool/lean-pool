/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section3c

/-!
# Section 3 of "Quickly excluding a planar graph": the end of the proof of (3.2)

The paper's (7), (8), (9) in the proof of (3.2), and (3.2) itself, `theorem_3_2`.

As in the paper, the path `P` of (3.2) runs from `s` through `J` to `P'` and through `K` to `t`, so
that the vertices of `P` in `G'`
are exactly those of `P'` (`exists_path_through`), and the tangle `𝒯'` is defined on `G \ V(P)`
itself.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β : Type*} {G A B C E C' D' : Hypergraph α β} {θ k : ℕ} {T : Set
  (Hypergraph α β × Hypergraph α β)} {s t : α}

theorem IsGraph.of_le (hG : G.IsGraph) (hA : A ≤ G) : A.IsGraph := by
  intro e he
  have heq : A.ends e = G.ends e := by
    ext v
    exact inc_iff_of_le hA he
  rw [heq]
  exact hG e (hA.edgeSet_subset he)

private theorem ncard_pair_le (a b : α) : ({a, b} : Set α).ncard ≤ 2 :=
  (ncard_insert_le a {b}).trans (by rw [ncard_singleton])

/-- A separation of `B` turns the separation `(A, B)` of `G` into the separation `(A ∪ C, E)` of
`G`. -/
theorem sep_union_left (hs : G.IsSeparation A B) (hCE : B.IsSeparation C E) : G.IsSeparation
  (A ∪ C) E := by
  have hC := hCE.left_le.trans hs.right_le
  have hE := hCE.right_le.trans hs.right_le
  refine sep_of_sets (union_le hs.left_le hC) hE (fun x hx => ?_) (fun e he => ?_) ?_
  · rcases mem_V_or hs hx with h₁ | h₁
    · exact Or.inl (Or.inl h₁)
    · exact (mem_V_or hCE h₁).imp Or.inr id
  · rcases mem_E_or hs he with h₁ | h₁
    · exact Or.inl (Or.inl h₁)
    · exact (mem_E_or hCE h₁).imp Or.inr id
  · rintro e (he | he) he'
    · exact hs.notMem_edgeSet_right he (hCE.right_le.edgeSet_subset he')
    · exact hCE.notMem_edgeSet_right he he'

/-- The order computation in (7) (page 333). -/
theorem order_lift_lt {X Y W : Set α} (hW : W = (A ∩ B).vertexSet \ (X ∪ Y)) (hXZ : X ⊆
  (A ∩ B).vertexSet)
    (hYZ : Y ⊆ (A ∩ B).vertexSet) (hVC : C.vertexSet = C'.vertexSet ∪ W) (hVE : E.vertexSet
      = D'.vertexSet ∪ W)
    (hD' : D'.vertexSet ⊆ B.vertexSet) (hXC : X ⊆ C'.vertexSet)
    (ho : separationOrder C' D' < X.ncard) : separationOrder (A ∪ C) E < (A ∩ B).vertexSet.ncard
      := by
  have hZf : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
  have hXf : X.Finite := hZf.subset hXZ
  have hYf : Y.Finite := hZf.subset hYZ
  have hXYf : (X ∪ Y).Finite := hXf.union hYf
  have hsub : ((A ∪ C) ∩ E).vertexSet ⊆ (W ∪ (C' ∩ D').vertexSet) ∪ ((X ∪ Y) \ X) := by
    rintro x ⟨hx, hx'⟩
    rw [hVE] at hx'
    by_cases hxW : x ∈ W
    · exact Or.inl (Or.inl hxW)
    have hxD : x ∈ D'.vertexSet := hx'.resolve_right hxW
    rcases hx with hx | hx
    · have hxZ : x ∈ (A ∩ B).vertexSet := ⟨hx, hD' hxD⟩
      have hxXY : x ∈ X ∪ Y := by
        by_contra hn
        exact hxW (hW ▸ ⟨hxZ, hn⟩)
      by_cases hxX : x ∈ X
      · exact Or.inl (Or.inr ⟨hXC hxX, hxD⟩)
      · exact Or.inr ⟨hxXY, hxX⟩
    · rw [hVC] at hx
      exact Or.inl (Or.inr ⟨hx.resolve_right hxW, hxD⟩)
  have h₁ : separationOrder (A ∪ C) E ≤ W.ncard + separationOrder C' D' + ((X ∪ Y) \ X).ncard := by
    have hWf : W.Finite := hW ▸ hZf.sdiff
    refine (ncard_le_ncard hsub ((hWf.union (C' ∩ D').vertexSet_finite).union hXYf.sdiff)).trans ?_
    exact (ncard_union_le _ _).trans (Nat.add_le_add_right (ncard_union_le _ _) _)
  have h₂ := ncard_sdiff_add_ncard_of_subset (subset_union_left : X ⊆ X ∪ Y) hXYf
  have h₃ := ncard_sdiff_add_ncard_of_subset (union_subset hXZ hYZ) hZf
  rw [← hW] at h₃
  omega

/-- **(7)** in the proof of (3.2) (page 333), in the form in which it is used: the hypothesis of
(3.1) for `G'` and `Z'`. The paper's
(7) asks for paths with no internal vertex in `Z`, and the proof gives paths that avoid `Z - (X ∪
Y)`, which is what (3.1) needs. -/
theorem cand_linked (hG : G.IsGraph) (hT : IsTangle G θ T) {S R J K : Set α} {v w : α}
    (h : Cand G T k s t A B S R J K v w) :
    Linked (B.deleteVertices {v, w}) ((A ∩ B).vertexSet \ {v, w}) := by
  classical
  intro X Y hX hY hc
  have hs := hT.isSeparation h.mem
  have hBG : B.IsGraph := IsGraph.of_le hG hs.right_le
  have hvZ : v ∈ (A ∩ B).vertexSet := h.union_eq ▸ Or.inl h.vS
  have hwZ : w ∈ (A ∩ B).vertexSet := h.union_eq ▸ Or.inr h.wR
  have hXZ : X ⊆ (A ∩ B).vertexSet := hX.trans sdiff_subset
  have hYZ : Y ⊆ (A ∩ B).vertexSet := hY.trans sdiff_subset
  let W : Set α := (A ∩ B).vertexSet \ (X ∪ Y)
  have hWB : W ⊆ B.vertexSet := fun x hx => hx.1.2
  have hXH : X ⊆ (B.deleteVertices W).vertexSet := fun x hx => ⟨(hXZ hx).2, fun h' => h'.2
    (Or.inl hx)⟩
  have hYH : Y ⊆ (B.deleteVertices W).vertexSet := fun x hx => ⟨(hYZ hx).2, fun h' => h'.2
    (Or.inr hx)⟩
  have hvW : ∀ {x}, x ∈ ({v, w} : Set α) → x ∈ W := fun {x} hx => by
    refine ⟨?_, ?_⟩
    · rcases hx with rfl | rfl
      · exact hvZ
      · exact hwZ
    · rintro (h' | h')
      · exact (hX h').2 hx
      · exact (hY h').2 hx
  by_cases hsep : ∀ C' D', (B.deleteVertices W).IsSeparation C' D' → X ⊆ C'.vertexSet
    → Y ⊆ D'.vertexSet →
      X.ncard ≤ separationOrder C' D'
  · have hle : B.deleteVertices W ≤ B.deleteVertices {v, w} :=
      le_of_sets (deleteVertices_le _ _) (deleteVertices_le _ _) (fun x hx => ⟨hx.1, fun h' => hx.2
        (hvW h')⟩)
        fun e he => ⟨he.1, fun x hx => he.2 x (hvW hx)⟩
    exact HasDisjointPaths.mono (skeleton_mono hle) ((menger _ X Y hXH hYH _).1 hsep)
  exfalso
  push Not at hsep
  obtain ⟨C', D', hs', hXC, hYD, ho⟩ := hsep
  obtain ⟨C, E, hCE, hVC, hVE, -, -⟩ := exists_lift hBG hWB hs'
  have hD' : D'.vertexSet ⊆ B.vertexSet := (hs'.right_le.trans (deleteVertices_le _
    _)).vertexSet_subset
  have hC' : C'.vertexSet ⊆ B.vertexSet := (hs'.left_le.trans (deleteVertices_le _
    _)).vertexSet_subset
  have ho₁ := order_lift_lt (A := A) rfl hXZ hYZ hVC hVE hD' hXC ho
  have ho₂ := order_lift_lt (A := A) (C := E) (E := C) (X := Y) (Y := X) (W := W)
    (by simp only [W, Set.union_comm]) hYZ hXZ hVE hVC hC' hYD
    (by rw [separationOrder_comm, ← hc]; exact ho)
  have hnθ : (A ∩ B).vertexSet.ncard < θ := hT.order_lt h.mem
  have hs₁ := sep_union_left hs hCE
  have hs₂ := sep_union_left hs hCE.symm
  have hAG := hs.left_le
  have hm₁ : (E, A ∪ C) ∈ T := (hT.axiom1 hs₁ (ho₁.trans hnθ)).resolve_left fun hm =>
    h.no_lower _ _ hm ho₁ (le_union_left hAG (hCE.left_le.trans hs.right_le)) hCE.right_le
  have hm₂ : (C, A ∪ E) ∈ T := (hT.axiom1 hs₂ (ho₂.trans hnθ)).resolve_left fun hm =>
    h.no_lower _ _ hm ho₂ (le_union_left hAG (hCE.right_le.trans hs.right_le)) hCE.left_le
  refine hT.axiom2 h.mem hm₁ hm₂ ?_
  rw [← hs.union_eq, ← hCE.union_eq, GM10.union_assoc A E C, GM10.union_comm E C]

/-- The start of the proof of (3.2) (page 332): the candidate with `B = G`, `V(A) = {s, t}` and
`E(A)` empty. -/
theorem exists_cand (hT : IsTangle G θ T) (hk : 1 ≤ k) (hθ : 18 * k + 3 ≤ θ) (hst : s ≠ t)
  (hfree : IsFreeSet G T θ {s, t}) :
    ∃ A₀ B₀ S R J K v w, Cand G T k s t A₀ B₀ S R J K v w := by
  classical
  have hsub : ({s, t} : Set α) ⊆ G.vertexSet := hfree.1
  let A₀ := subOf G {s, t} ∅ hsub fun _ he => he.elim
  have hle : A₀ ≤ G := subOf_le
  have hsep : G.IsSeparation A₀ G := sep_of_sets hle le_rfl (fun _ h => Or.inr h) (fun _ h
    => Or.inr h) fun _ he => he.elim
  have hV : (A₀ ∩ G).vertexSet = {s, t} := subset_antisymm (fun _ h => h.1) fun x hx
    => ⟨hx, hsub hx⟩
  have ho : separationOrder A₀ G = 2 := by
    unfold separationOrder
    rw [hV, ncard_pair hst]
  have hm : (A₀, G) ∈ T := (hT.axiom1 hsep (by omega)).resolve_right fun h => hT.axiom3 h rfl
  refine ⟨A₀, G, {s}, {t}, {s}, {t}, s, t, ?_⟩
  exact {
    mem := hm
    no_lower := fun A' B' hm' ho' hA _ => by
      have := hfree.2.2 hm' (fun x hx => hA.vertexSet_subset hx)
      rw [ncard_pair hst] at this
      omega
    union_eq := by
      rw [hV]
      rfl
    disj := disjoint_singleton.2 hst
    cardS := by rw [ncard_singleton]; omega
    cardR := by rw [ncard_singleton]; omega
    s_mem := rfl
    t_mem := rfl
    connJ := conn_singleton
    connK := conn_singleton
    subJ := singleton_subset_iff.2 (Or.inl rfl)
    subK := singleton_subset_iff.2 (Or.inr rfl)
    disjJK := disjoint_singleton.2 hst
    v_mem := rfl
    w_mem := rfl
    vS := rfl
    wR := rfl
    eqJ := fun x hx _ => hx
    eqK := fun x hx _ => hx
    adjS := fun x hx hne => (hne hx).elim
    adjR := fun x hx hne => (hne hx).elim }

/-- The vertices of `Z'` that survive in `G \ V(P)`, and the tangle `𝒯'` of the proof of (3.2) (page
334). -/
def pathTangle (H : Hypergraph α β) (Z' : Set α) (k : ℕ) : Set (Hypergraph α β × Hypergraph α β) :=
  {p | H.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < k ∧ (p.1.vertexSet ∩ Z').ncard < 6 * k}

/-- The tangle `𝒯'` of the proof of (3.2) (page 334) is a tangle. Here `Z''` is the part of `Z'` in
`V(H)`, and `L` is `G' \ V(P')`. The
hypothesis `hgood` is (8). The paper has `< k` where the argument gives `< 6k`, as `𝒯'` is defined
with `6k`. -/
theorem isTangle_pathTangle {H L : Hypergraph α β} {Z' Z'' : Set α} (hk : 1 ≤ k) (hL : L ≤ H)
  (hZ'f : Z'.Finite)
    (hZ'' : Z'' ⊆ Z') (hZ''H : Z'' ⊆ H.vertexSet) (hc : 18 * k - 2 ≤ Z''.ncard)
    (hZL : ∀ x ∈ H.vertexSet, x ∈ Z' → x ∈ L.vertexSet)
    (hgood : ∀ A B, L.IsSeparation A B → separationOrder A B < k →
      ¬ (6 * k ≤ (A.vertexSet ∩ Z').ncard ∧ 6 * k ≤ (B.vertexSet ∩ Z').ncard)) :
    IsTangle H k (pathTangle H Z' k) := by
  have hZfin : ∀ X : Set α, (X ∩ Z').Finite := fun X => hZ'f.subset inter_subset_right
  have hbig : ∀ {X : Set α}, Z'' ⊆ X → 18 * k - 2 ≤ (X ∩ Z').ncard := fun {X} hX =>
    hc.trans (ncard_le_ncard (fun x hx => ⟨hX hx, hZ'' hx⟩) (hZfin _))
  refine ⟨hk, fun _ _ h => h.1, fun _ _ h => h.2.1, ?_, ?_, ?_⟩
  · intro A₁ B₁ hs ho
    have hsL := hs.restrict hL
    have hoL := (order_restrict_le A₁ B₁ L).trans_lt ho
    have hsize : ∀ {X : Hypergraph α β}, X ≤ H → (X.vertexSet ∩ Z').ncard ≤
      ((X ∩ L).vertexSet ∩ Z').ncard := fun {X} hX =>
      ncard_le_ncard (fun x hx => ⟨⟨hx.1, hZL x (hX.vertexSet_subset hx.1) hx.2⟩, hx.2⟩) (hZfin _)
    by_cases h₁ : (A₁.vertexSet ∩ Z').ncard < 6 * k
    · exact Or.inl ⟨hs, ho, h₁⟩
    · refine Or.inr ⟨hs.symm, by rwa [separationOrder_comm], ?_⟩
      by_contra h₂
      have h₂' : ¬ (B₁.vertexSet ∩ Z').ncard < 6 * k := h₂
      have h₃ := hsize hs.left_le
      have h₄ := hsize hs.right_le
      exact hgood _ _ hsL hoL ⟨by omega, by omega⟩
  · rintro A₁ B₁ A₂ B₂ A₃ B₃ ⟨-, -, h₁⟩ ⟨-, -, h₂⟩ ⟨-, -, h₃⟩ he
    have h₁' : (A₁.vertexSet ∩ Z').ncard < 6 * k := h₁
    have h₂' : (A₂.vertexSet ∩ Z').ncard < 6 * k := h₂
    have h₃' : (A₃.vertexSet ∩ Z').ncard < 6 * k := h₃
    have hb := hbig (X := (A₁.vertexSet ∪ A₂.vertexSet) ∪ A₃.vertexSet) (fun x hx => by
      have : x ∈ (A₁ ∪ A₂ ∪ A₃).vertexSet := he ▸ hZ''H hx
      exact this)
    have hle : (((A₁.vertexSet ∪ A₂.vertexSet) ∪ A₃.vertexSet) ∩ Z').ncard ≤
        ((A₁.vertexSet ∩ Z') ∪ (A₂.vertexSet ∩ Z') ∪ (A₃.vertexSet ∩ Z')).ncard :=
      le_of_eq (by rw [union_inter_distrib_right, union_inter_distrib_right])
    have h₄ := (ncard_union_le ((A₁.vertexSet ∩ Z') ∪ (A₂.vertexSet ∩ Z'))
      (A₃.vertexSet ∩ Z')).trans
      (Nat.add_le_add_right (ncard_union_le _ _) _)
    omega
  · rintro A₁ B₁ ⟨-, -, h₁⟩ he
    have h₁' : (A₁.vertexSet ∩ Z').ncard < 6 * k := h₁
    have hb := hbig (X := A₁.vertexSet) (fun x hx => he ▸ hZ''H hx)
    omega

/-- **(9)** in the proof of (3.2) (page 334): `𝒯'` is conformal with `𝒯`. The hypothesis `hC` says
that `C` holds at most four vertices of `Z` outside `Z'`
or in `Z'`, in the form used in the paper: the vertices of `Z` in `C` or not in `Z'` are in a set
`F` of size at most `4`. -/
theorem conformal_pathTangle (hT : IsTangle G θ T) (_hk : 1 ≤ k) {S R J K : Set α} {v w : α}
    (h : Cand G T k s t A B S R J K v w) (hZc : (A ∩ B).vertexSet.ncard
      = 18 * k + 2) {H : Hypergraph α β} {Z' F : Set α}
    (_hH : H ≤ G) (hF : F.Finite) (hFc : F.ncard ≤ 4)
    (hZF : ∀ x ∈ (A ∩ B).vertexSet, x ∈ H.vertexSet ∧ x ∈ Z' ∨ x ∈ F) :
    Conformal G H T (pathTangle H Z' k) θ k := by
  classical
  have hs := hT.isSeparation h.mem
  have hnθ : (A ∩ B).vertexSet.ncard < θ := hT.order_lt h.mem
  refine ⟨by omega, ?_⟩
  rintro ⟨A₀, B₀⟩ ⟨hs₀, ho₀, -, -, hsmall⟩
  have hsmall' : ((A₀ ∩ H).vertexSet ∩ Z').ncard < 6 * k := hsmall
  have ho₀' : separationOrder A₀ B₀ < k := ho₀
  by_contra hn
  have hBA : (B₀, A₀) ∈ T := (hT.axiom1 hs₀ (by omega)).resolve_left hn
  have hZf := (A ∩ B).vertexSet_finite
  let Y : Set α := (A ∩ B).vertexSet \ B₀.vertexSet
  have hY : Y ⊆ ((A₀ ∩ H).vertexSet ∩ Z') ∪ F := by
    rintro x ⟨hxZ, hxB⟩
    have hxG : x ∈ G.vertexSet := hs.left_le.vertexSet_subset hxZ.1
    have hxA := (mem_V_or hs₀ hxG).resolve_right hxB
    rcases hZF x hxZ with ⟨h₁, h₂⟩ | h₁
    · exact Or.inl ⟨⟨hxA, h₁⟩, h₂⟩
    · exact Or.inr h₁
  have hZ'f : ((A₀ ∩ H).vertexSet ∩ Z').Finite := (A₀ ∩ H).vertexSet_finite.subset inter_subset_left
  have hYc : Y.ncard ≤ 6 * k + 3 := by
    have := (ncard_le_ncard hY (hZ'f.union hF)).trans (ncard_union_le _ _)
    omega
  have hs₁ : G.IsSeparation (A ∪ B₀) (B ∩ A₀) := hs.union_inter hs₀.symm
  have hsub : ((A ∪ B₀) ∩ (B ∩ A₀)).vertexSet ⊆ (A₀ ∩ B₀).vertexSet ∪ Y := by
    rintro x ⟨hx, hxB, hxA⟩
    by_cases hxB₀ : x ∈ B₀.vertexSet
    · exact Or.inl ⟨hxA, hxB₀⟩
    · exact Or.inr ⟨⟨hx.resolve_right hxB₀, hxB⟩, hxB₀⟩
  have ho₁ : separationOrder (A ∪ B₀) (B ∩ A₀) < (A ∩ B).vertexSet.ncard := by
    have h₁ := (ncard_le_ncard hsub ((A₀ ∩ B₀).vertexSet_finite.union
      (hZf.subset sdiff_subset))).trans (ncard_union_le _ _)
    have h₂ : (A₀ ∩ B₀).vertexSet.ncard < k := ho₀'
    change ((A ∪ B₀) ∩ (B ∩ A₀)).vertexSet.ncard < _
    omega
  have hm₁ : (B ∩ A₀, A ∪ B₀) ∈ T := (hT.axiom1 hs₁ (ho₁.trans hnθ)).resolve_left fun hm =>
    h.no_lower _ _ hm ho₁ (le_union_left hs.left_le hs₀.right_le) (inter_le_left hs.right_le
      hs₀.left_le)
  refine hT.axiom2 h.mem hm₁ hBA ?_
  have hle : A ∪ (B ∩ A₀) ∪ B₀ ≤ G := union_le (union_le hs.left_le (inter_le hs.right_le
    hs₀.left_le)) hs₀.right_le
  refine sub_ext (G := G) hle le_rfl (subset_antisymm hle.vertexSet_subset fun x hx => ?_)
    (subset_antisymm hle.edgeSet_subset fun e he => ?_)
  · rcases mem_V_or hs hx with h₁ | h₁
    · exact Or.inl (Or.inl h₁)
    · rcases mem_V_or hs₀ hx with h₂ | h₂
      · exact Or.inl (Or.inr ⟨h₁, h₂⟩)
      · exact Or.inr h₂
  · rcases mem_E_or hs he with h₁ | h₁
    · exact Or.inl (Or.inl h₁)
    · rcases mem_E_or hs₀ he with h₂ | h₂
      · exact Or.inl (Or.inr ⟨h₁, h₂⟩)
      · exact Or.inr h₂

/-- The path `P` of the proof of (3.2) (page 334): "let $P$ be a path of $G$ from $s$ to $t$ with $P
\cap G' = P'$ (this exists
and can be chosen with $V(P) \subseteq V(J \cup K \cup P')$ because of (4))". Here a walk in `J`
from `s`, an edge into the path
`q` (which is `P'`), the path `q`, an edge out of it, and a walk in `K` to `t` give a path, when `q`
misses `J` and `K` and
these two are disjoint. Every vertex of `q` is on the path, and every other vertex of the path is in
`J` or `K`. -/
theorem exists_path_through {Gs : SimpleGraph α} {J K : Set α} {s y₁ x y y₂ t : α}
    (wJ : Gs.Walk s y₁) (hwJ : ∀ z ∈ wJ.support, z ∈ J) (q : Gs.Walk x y) (hq : q.IsPath)
    (wK : Gs.Walk y₂ t) (hwK : ∀ z ∈ wK.support, z ∈ K) (h₁ : Gs.Adj y₁ x) (h₂ : Gs.Adj y y₂)
    (hqJ : ∀ z ∈ q.support, z ∉ J) (hqK : ∀ z ∈ q.support, z ∉ K) (hJK : Disjoint J K) :
    ∃ P : Gs.Walk s t, P.IsPath ∧ (∀ z ∈ P.support, z ∈ J ∨ z ∈ q.support ∨ z ∈ K) ∧
      ∀ z ∈ q.support, z ∈ P.support := by
  classical
  let PJ := wJ.bypass
  let PK := wK.bypass
  have hPJ : ∀ z ∈ PJ.support, z ∈ J := fun z hz => hwJ z (wJ.support_bypass_subset_support hz)
  have hPK : ∀ z ∈ PK.support, z ∈ K := fun z hz => hwK z (wK.support_bypass_subset_support hz)
  refine ⟨PJ.append (SimpleGraph.Walk.cons h₁ (q.append (SimpleGraph.Walk.cons h₂ PK))), ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_cons, List.tail_cons,
      SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons, List.tail_cons]
    have n1 := (SimpleGraph.Walk.isPath_def _).mp wJ.bypass_isPath
    have n2 := (SimpleGraph.Walk.isPath_def _).mp hq
    have n3 := (SimpleGraph.Walk.isPath_def _).mp wK.bypass_isPath
    rw [List.nodup_append, List.nodup_append]
    refine ⟨n1, ⟨n2, n3, ?_⟩, ?_⟩
    · intro a ha b hb hab
      subst hab
      exact hqK a ha (hPK a hb)
    · intro a ha b hb hab
      subst hab
      rcases List.mem_append.mp hb with hb | hb
      · exact hqJ a hb (hPJ a ha)
      · exact disjoint_left.mp hJK (hPJ a ha) (hPK a hb)
  · intro z hz
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons, List.tail_cons,
      SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons, List.tail_cons] at hz
    rcases List.mem_append.mp hz with hz | hz
    · exact Or.inl (hPJ z hz)
    · rcases List.mem_append.mp hz with hz | hz
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr (hPK z hz))
  · intro z hz
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons, List.tail_cons,
      SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons, List.tail_cons]
    exact List.mem_append_right _ (List.mem_append_left _ hz)

/-- **(3.2)** (page 332). The proof is the paper's (pages 332–334): `(A, B)`, `S`, `T`, `J`, `K`
chosen with `A` maximal, (5)–(7),
then (8) from (3.1), the path `P` with `P ∩ G' = P'`, the tangle `𝒯'` on `G \ V(P)`, and (9). -/
theorem theorem_3_2 (hG : G.IsGraph) (hk : 1 ≤ k) (hst : s ≠ t) (hT : IsTangle G θ T)
  (hθ : 18 * k + 3 ≤ θ)
    (hfree : IsFreeSet G T θ {s, t}) :
    ∃ P : G.skeleton.Walk s t, P.IsPath ∧ ∃ T', IsTangle (G.deleteVertices {x | x ∈ P.support}) k
      T' ∧
      Conformal G (G.deleteVertices {x | x ∈ P.support}) T T' θ k := by
  classical
  obtain ⟨A₀, B₀, S₀, R₀, J₀, K₀, v₀, w₀, hc₀⟩ := exists_cand hT hk hθ hst hfree
  obtain ⟨A, ⟨B, S, R, J, K, v, w, h⟩, hmaxA⟩ := exists_max_measure
    (P := fun A => ∃ B S R J K v w, Cand G T k s t A B S R J K v w) size (size G)
    (fun _ ⟨_, _, _, _, _, _, _, hc⟩ => size_le_of_le (hT.isSeparation hc.mem).left_le)
    ⟨A₀, B₀, S₀, R₀, J₀, K₀, v₀, w₀, hc₀⟩
  have hmax : IsMaxCand G T k s t A := fun A' B' S' R' J' K' v' w' hc
    => hmaxA A' ⟨B', S', R', J', K', v', w', hc⟩
  have hS := card_S_eq hG hT hθ h hmax
  have hR := card_S_eq hG hT hθ h.swap hmax.swap
  have hs := hT.isSeparation h.mem
  have hAG := hs.left_le
  have hBG := hs.right_le
  have hZf : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
  have hmemZ : ∀ {x}, x ∈ S ∪ R → x ∈ (A ∩ B).vertexSet := fun hx => h.union_eq ▸ hx
  have hSf : S.Finite := hZf.subset fun _ hx => hmemZ (Or.inl hx)
  have hRf : R.Finite := hZf.subset fun _ hx => hmemZ (Or.inr hx)
  have hZc : (A ∩ B).vertexSet.ncard = 18 * k + 2 := by
    rw [← h.union_eq, ncard_union_eq h.disj hSf hRf, hS, hR]
    omega
  have hvR : v ∉ R := disjoint_left.1 h.disj h.vS
  have hwS : w ∉ S := fun hw => disjoint_left.1 h.disj hw h.wR
  have hunion : S \ {v} ∪ R \ {w} = (A ∩ B).vertexSet \ {v, w} := by
    rw [← h.union_eq]
    ext x
    constructor
    · rintro (⟨hx, hxv⟩ | ⟨hx, hxw⟩)
      · refine ⟨Or.inl hx, ?_⟩
        rintro (rfl | rfl)
        · exact hxv rfl
        · exact hwS hx
      · refine ⟨Or.inr hx, ?_⟩
        rintro (rfl | rfl)
        · exact hvR hx
        · exact hxw rfl
    · rintro ⟨hx | hx, hne⟩
      · exact Or.inl ⟨hx, fun e => hne (Or.inl e)⟩
      · exact Or.inr ⟨hx, fun e => hne (Or.inr e)⟩
  have hdis : Disjoint (S \ {v}) (R \ {w}) := h.disj.mono sdiff_subset sdiff_subset
  have hS' : (S \ {v}).ncard = 9 * k := by
    rw [ncard_sdiff_singleton_of_mem h.vS, hS]
    omega
  have hR' : (R \ {w}).ncard = 9 * k := by
    rw [ncard_sdiff_singleton_of_mem h.wR, hR]
    omega
  have hZ'c : ((A ∩ B).vertexSet \ {v, w}).ncard = 18 * k := by
    rw [← hunion, ncard_union_eq hdis hSf.sdiff hRf.sdiff, hS', hR']
    omega
  let G' := B.deleteVertices {v, w}
  have hG'B : G' ≤ B := deleteVertices_le _ _
  have hG'G : G' ≤ G := hG'B.trans hBG
  have hZ'sub : (A ∩ B).vertexSet \ {v, w} ⊆ G'.vertexSet := fun x hx => ⟨hx.1.2, hx.2⟩
  obtain ⟨p, hpends, hpgood⟩ := theorem_3_1 (IsGraph.of_le hG hG'G) hk hZ'sub hZ'c
    (cand_linked hG hT h) hunion hdis hS' hR'
  have hxS := p.first_mem
  have hyR := p.last_mem
  obtain ⟨y₁, hy₁, adj₁⟩ := h.adjS _ hxS.1 hxS.2
  obtain ⟨y₂, hy₂, adj₂⟩ := h.adjR _ hyR.1 hyR.2
  -- The path `P` of page 334, with `P ∩ G' = P'`.
  have hG'J : ∀ z, z ∈ G'.vertexSet → z ∉ J := fun z hz hzJ => hz.2 (Or.inl (h.eqJ z hzJ hz.1))
  have hG'K : ∀ z, z ∈ G'.vertexSet → z ∉ K := fun z hz hzK => hz.2 (Or.inr (h.eqK z hzK hz.1))
  have hpG' : ∀ z ∈ p.walk.support, z ∈ G'.vertexSet := fun z hz => support_mem p.walk (hZ'sub
    (hunion ▸ Or.inl hxS)) hz
  obtain ⟨wJ, hwJ⟩ := h.connJ.2 s h.s_mem y₁ hy₁
  obtain ⟨wK, hwK⟩ := h.connK.2 y₂ hy₂ t h.t_mem
  obtain ⟨P, hPpath, hPsub, hP'P⟩ := exists_path_through (wJ.mapLe (skeleton_mono hAG))
    (fun z hz => hwJ z (by simpa using hz)) (p.walk.mapLe (skeleton_mono hG'G)) (p.isPath.mapLe _)
    (wK.mapLe (skeleton_mono hAG)) (fun z hz => hwK z (by simpa using hz))
    (skeleton_mono hAG adj₁).symm (skeleton_mono hAG adj₂)
    (fun z hz => hG'J z (hpG' z (by simpa using hz))) (fun z hz => hG'K z (hpG' z
      (by simpa using hz))) h.disjJK
  -- `P ∩ G' = P'`, on vertices.
  have hPG' : ∀ z ∈ P.support, z ∈ G'.vertexSet → z ∈ pathV p := by
    intro z hz hzG'
    rcases hPsub z hz with hzJ | hzp | hzK
    · exact (hG'J z hzG' hzJ).elim
    · simpa [pathV] using hzp
    · exact (hG'K z hzG' hzK).elim
  have hpP : ∀ z ∈ pathV p, z ∈ P.support := fun z hz => hP'P z (by simpa [pathV] using hz)
  let C : Set α := {x | x ∈ P.support}
  let H := G.deleteVertices C
  let L := G'.deleteVertices (pathV p)
  have hLG : L ≤ G := (deleteVertices_le _ _).trans hG'G
  have hVL : ∀ u, u ∈ G'.vertexSet → u ∉ pathV p → u ∉ C := fun u hu hup huC => hup (hPG' u huC hu)
  have hHG : H ≤ G := deleteVertices_le _ _
  have hL : L ≤ H := by
    refine le_of_sets hLG hHG (fun u hu => ⟨hLG.vertexSet_subset hu, hVL u hu.1 hu.2⟩) fun e he
      => ?_
    refine ⟨hLG.edgeSet_subset he, fun u huC hi => ?_⟩
    have hu := end_mem hLG he hi
    exact hVL u hu.1 hu.2 huC
  have hZ'f : ((A ∩ B).vertexSet \ {v, w}).Finite := hZf.sdiff
  let Z'' := ((A ∩ B).vertexSet \ {v, w}) \ pathV p
  have hZ''H : Z'' ⊆ H.vertexSet := fun u hu =>
    ⟨hAG.vertexSet_subset hu.1.1.1, hVL u (hZ'sub hu.1) hu.2⟩
  have hsub₂ : (A ∩ B).vertexSet \ {v, w} ⊆ Z'' ∪ {p.first, p.last} := fun u hu => by
    by_cases hup : u ∈ pathV p
    · exact Or.inr (hpends u hu hup)
    · exact Or.inl ⟨hu, hup⟩
  have hZ''c : 18 * k - 2 ≤ Z''.ncard := by
    have h₁ := (ncard_le_ncard hsub₂ (hZ'f.sdiff.union (toFinite _))).trans (ncard_union_le _ _)
    have h₂ := ncard_pair_le p.first p.last
    omega
  have hZL : ∀ u ∈ H.vertexSet, u ∈ (A ∩ B).vertexSet \ {v, w} → u ∈ L.vertexSet := fun u hu huZ =>
    ⟨hZ'sub huZ, fun hup => hu.2 (hpP u hup)⟩
  have htan := isTangle_pathTangle hk hL hZ'f sdiff_subset hZ''H hZ''c hZL hpgood
  have hFc : ({v, w, p.first, p.last} : Set α).ncard ≤ 4 := by
    have h₁ := ncard_insert_le v ({w, p.first, p.last} : Set α)
    have h₂ := ncard_insert_le w ({p.first, p.last} : Set α)
    have h₃ := ncard_pair_le p.first p.last
    omega
  have hZF : ∀ x ∈ (A ∩ B).vertexSet, x ∈ H.vertexSet ∧ x ∈ (A ∩ B).vertexSet \ {v, w} ∨ x ∈
    ({v, w, p.first, p.last} : Set α) := by
    intro x hx
    by_cases hx₁ : x ∈ ({v, w} : Set α)
    · rcases hx₁ with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · have hxZ' : x ∈ (A ∩ B).vertexSet \ {v, w} := ⟨hx, hx₁⟩
      by_cases hxp : x ∈ pathV p
      · exact Or.inr (Or.inr (Or.inr (hpends x hxZ' hxp)))
      · exact Or.inl ⟨⟨hAG.vertexSet_subset hx.1, hVL x (hZ'sub hxZ') hxp⟩, hxZ'⟩
  exact ⟨P, hPpath, _, htan, conformal_pathTangle hT hk h hZc hHG (toFinite _) hFc hZF⟩

end GraphMinor.RST94
