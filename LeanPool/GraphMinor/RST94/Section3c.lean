/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section3b

/-!
# Section 3 of "Quickly excluding a planar graph": the first half of the proof of (3.2)

The choice at the start of the proof of (3.2) (page 332), and its properties (5) and (6). Here `J`
and `K` are given by their
vertex sets, and are connected in `A` in the sense of `Conn`.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β : Type*} {G A B : Hypergraph α β} {θ k : ℕ} {T : Set (Hypergraph α β × Hypergraph α
  β)} {s t : α}

/-- The conditions (1)-(4) in the proof of (3.2) (page 332). `S` and `R` are the paper's `S` and
`T`, and `v`, `w` are the
vertices of `V(J) ∩ V(A ∩ B)` and `V(K) ∩ V(A ∩ B)`. The paper's condition (4) is stated for `v ∈
V(A ∩ B) - V(J ∪ K)`, and
here for the vertices of `S` other than `v` and of `R` other than `w`, which are the same vertices.
-/
structure Cand (G : Hypergraph α β) (T : Set (Hypergraph α β × Hypergraph α β)) (k : ℕ) (s t : α)
    (A B : Hypergraph α β) (S R J K : Set α) (v w : α) : Prop where
  mem : (A, B) ∈ T
  no_lower : ∀ A' B', (A', B') ∈ T → separationOrder A' B' < separationOrder A B → A ≤ A' → B' ≤ B
    → False
  union_eq : S ∪ R = (A ∩ B).vertexSet
  disj : Disjoint S R
  cardS : S.ncard ≤ 9 * k + 1
  cardR : R.ncard ≤ 9 * k + 1
  s_mem : s ∈ J
  t_mem : t ∈ K
  connJ : Conn A J
  connK : Conn A K
  subJ : J ⊆ A.vertexSet
  subK : K ⊆ A.vertexSet
  disjJK : Disjoint J K
  v_mem : v ∈ J
  w_mem : w ∈ K
  vS : v ∈ S
  wR : w ∈ R
  eqJ : ∀ x ∈ J, x ∈ B.vertexSet → x = v
  eqK : ∀ x ∈ K, x ∈ B.vertexSet → x = w
  adjS : ∀ x ∈ S, x ≠ v → ∃ y ∈ J, A.skeleton.Adj x y
  adjR : ∀ x ∈ R, x ≠ w → ∃ y ∈ K, A.skeleton.Adj x y

/-- The conditions are symmetric. -/
theorem Cand.swap {S R J K : Set α} {v w : α} (h : Cand G T k s t A B S R J K v w) : Cand G T k t s
  A B R S K J w v where
  mem := h.mem
  no_lower := h.no_lower
  union_eq := by rw [Set.union_comm]; exact h.union_eq
  disj := h.disj.symm
  cardS := h.cardR
  cardR := h.cardS
  s_mem := h.t_mem
  t_mem := h.s_mem
  connJ := h.connK
  connK := h.connJ
  subJ := h.subK
  subK := h.subJ
  disjJK := h.disjJK.symm
  v_mem := h.w_mem
  w_mem := h.v_mem
  vS := h.wR
  wR := h.vS
  eqJ := h.eqK
  eqK := h.eqJ
  adjS := h.adjR
  adjR := h.adjS

/-- `A` has the largest size among all candidates. This is the paper's choice of `A` maximal. -/
def IsMaxCand (G : Hypergraph α β) (T : Set (Hypergraph α β × Hypergraph α β)) (k : ℕ) (s t : α)
  (A : Hypergraph α β) : Prop :=
  ∀ A' B' S R J K v w, Cand G T k s t A' B' S R J K v w → size A' ≤ size A

theorem IsMaxCand.swap (h : IsMaxCand G T k s t A) : IsMaxCand G T k t s A :=
  fun A' B' S R J K v w hc => h A' B' R S K J w v hc.swap

section Side

variable {A' B' D : Hypergraph α β} {n : ℕ} {P : Fin n → PathFromTo D.skeleton (A ∩ B).vertexSet
  (A' ∩ B').vertexSet}

/-- One side of the construction of `J'` in (5) (page 333). The set `I` holds the indices of the
paths that start in `S`, and
`i₀` is the index of the path that starts at `v`. -/
theorem exists_extended_side (hA : A ≤ A') (hB' : B' ≤ B) (hD : D ≤ A')
    (hZD : (A ∩ B).vertexSet ⊆ D.vertexSet)
    (hP : Pairwise fun i j => Disjoint (pathV (P i)) (pathV (P j)))
    (hlast : ∀ i, ∀ x ∈ pathV (P i), x ∈ (A' ∩ B').vertexSet → x = (P i).last)
    {J S : Set α} {v : α} (hJ : Conn A J) (hJA : J ⊆ A.vertexSet) (hv : v ∈ J)
      (heq : ∀ x ∈ J, x ∈ B.vertexSet → x = v)
    (hadj : ∀ x ∈ S, x ≠ v → ∃ y ∈ J, A.skeleton.Adj x y)
      (i₀ : Fin n) (hi₀ : (P i₀).first = v) :
    ∃ J' : Set α, Conn A' J' ∧ J ⊆ J' ∧ J' ⊆ A'.vertexSet ∧ (P i₀).last ∈ J' ∧
      (∀ x ∈ J', x ∈ B'.vertexSet → x = (P i₀).last) ∧
      (∀ i, (P i).first ∈ S → i ≠ i₀ → ∃ y ∈ J', A'.skeleton.Adj (P i).last y) ∧
      (∀ x ∈ J', x ∈ J ∨ x ∈ pathV (P i₀) ∨ ∃ i, (P i).first ∈ S ∧ x ∈ pathV (P i)) := by
  classical
  have hV : ∀ i, pathV (P i) ⊆ D.vertexSet := fun i _ hx => support_mem (P i).walk (hZD
    (P i).first_mem) hx
  have hVA' : ∀ i, pathV (P i) ⊆ A'.vertexSet := fun i => (hV i).trans hD.vertexSet_subset
  have hstart : ∀ i, (P i).first ∈ pathV (P i) := fun i => (P i).walk.start_mem_support
  have hend : ∀ i, (P i).last ∈ pathV (P i) := fun i => (P i).walk.end_mem_support
  let J' : Set α := J ∪ pathV (P i₀) ∪ {x | ∃ i, (P i).first ∈ S ∧ i ≠ i₀ ∧ x ∈ pathV (P i) ∧ x ≠
    (P i).last}
  have hne : ∀ i, (P i).first ∈ S → i ≠ i₀ → (P i).first ≠ v := fun i _ hi e =>
    disjoint_left.1 (hP hi) (hstart i) (by rw [e, ← hi₀]; exact hstart i₀)
  have hvM : v ∈ J' := Or.inl (Or.inl hv)
  have hconn : Conn A' J' := by
    refine conn_of_reach hvM ?_
    rintro x ((hx | hx) | ⟨i, hiS, hi, hx, hxl⟩)
    · obtain ⟨w, hw⟩ := (hJ.mono hA).2 x hx v hv
      exact ⟨w, fun z hz => Or.inl (Or.inl (hw z hz))⟩
    · obtain ⟨w, hw⟩ := ((conn_support (P i₀).walk).mono hD).2 x hx v
        (by rw [← hi₀]; exact hstart i₀)
      exact ⟨w, fun z hz => Or.inl (Or.inr (hw z hz))⟩
    · obtain ⟨y, hy, hadjy⟩ := hadj _ hiS (hne i hiS hi)
      obtain ⟨w₂, hw₂⟩ := (hJ.mono hA).2 y hy v hv
      refine ⟨(((P i).walk.takeUntil x hx).reverse.mapLe (skeleton_mono hD)).append
        (SimpleGraph.Walk.cons (skeleton_mono hA hadjy) w₂), fun z hz => ?_⟩
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz with hz | hz
      · have hz' : z ∈ ((P i).walk.takeUntil x hx).support := by simpa using hz
        refine Or.inr ⟨i, hiS, hi, (P i).walk.support_takeUntil_subset_support hx hz', fun e => ?_⟩
        exact notMem_takeUntil (P i).walk (P i).isPath hx hxl (e ▸ hz')
      · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · have hno : ∀ y ∈ ((P i).walk.takeUntil x hx).support, y ≠ (P i).last := fun y hy e =>
            notMem_takeUntil (P i).walk (P i).isPath hx hxl (e ▸ hy)
          exact Or.inr ⟨i, hiS, hi, hstart i, hno _ ((P i).walk.takeUntil x hx).start_mem_support⟩
        · exact Or.inl (Or.inl (hw₂ z hz))
  refine ⟨J', hconn, fun x hx => Or.inl (Or.inl hx), ?_, Or.inl (Or.inr (hend i₀)), ?_, ?_, ?_⟩
  · rintro x ((hx | hx) | ⟨i, -, -, hx, -⟩)
    · exact hA.vertexSet_subset (hJA hx)
    · exact hVA' _ hx
    · exact hVA' _ hx
  · rintro x ((hx | hx) | ⟨i, -, -, hx, hxl⟩) hxB
    · have hxv := heq x hx (hB'.vertexSet_subset hxB)
      refine hlast i₀ x ?_ ⟨hA.vertexSet_subset (hJA hx), hxB⟩
      rw [hxv, ← hi₀]
      exact hstart i₀
    · exact hlast i₀ x hx ⟨hVA' _ hx, hxB⟩
    · exact absurd (hlast i x hx ⟨hVA' _ hx, hxB⟩) hxl
  · intro i hiS hi
    by_cases hfl : (P i).first = (P i).last
    · obtain ⟨y, hy, hadjy⟩ := hadj _ hiS (hne i hiS hi)
      have h₁ := skeleton_mono hA hadjy
      rw [hfl] at h₁
      exact ⟨y, Or.inl (Or.inl hy), h₁⟩
    · obtain ⟨y, hadjy, q, hq⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne (Ne.symm hfl)
        (P i).walk.reverse
      have hy : y ∈ (P i).walk.reverse.support := by
        rw [hq]
        simp
      exact ⟨y, Or.inr ⟨i, hiS, hi, (by simpa using hy : y ∈ (P i).walk.support), hadjy.ne.symm⟩,
        skeleton_mono hD hadjy⟩
  · rintro x ((hx | hx) | ⟨i, hiS, -, hx, -⟩)
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr ⟨i, hiS, hx⟩)

end Side

/-- **(5)** in the proof of (3.2) (page 332). -/
theorem no_same_order (hT : IsTangle G θ T) {S R J K : Set α} {v w : α}
  (h : Cand G T k s t A B S R J K v w)
    (hmax : IsMaxCand G T k s t A) {A' B' : Hypergraph α β} (hm : (A', B') ∈ T)
    (ho : separationOrder A' B' = separationOrder A B) (hA : A ≤ A') (hB : B' ≤ B)
      (hne : A' ≠ A) : False := by
  classical
  have hs := hT.isSeparation h.mem
  have hs' := hT.isSeparation hm
  let D := B ∩ A'
  have hDB : D ≤ B := inter_le_left hs.right_le hs'.left_le
  have hDA' : D ≤ A' := inter_le_right hs.right_le hs'.left_le
  have hDG : D ≤ G := hDB.trans hs.right_le
  have hZD : (A ∩ B).vertexSet ⊆ D.vertexSet := fun x hx => ⟨hx.2, hA.vertexSet_subset hx.1⟩
  have hZ₂D : (A' ∩ B').vertexSet ⊆ D.vertexSet := fun x hx => ⟨hB.vertexSet_subset hx.2, hx.1⟩
  set n := separationOrder A B with hn
  have hZc : (A ∩ B).vertexSet.ncard = n := rfl
  have hZ₂c : (A' ∩ B').vertexSet.ncard = n := ho
  -- There is no separation of `D` of order less than `n` between the two sets, so there are `n`
  -- paths.
  have hmenger : ∀ C E, D.IsSeparation C E → (A ∩ B).vertexSet ⊆ C.vertexSet →
    (A' ∩ B').vertexSet ⊆ E.vertexSet →
      n ≤ separationOrder C E := by
    intro C E hCE hZC hZE
    by_contra hlt
    push Not at hlt
    have hC := hCE.left_le
    have hE := hCE.right_le
    have hsep : G.IsSeparation (A ∪ C) (B' ∪ E) := by
      refine sep_of_sets (union_le hs.left_le (hC.trans hDG)) (union_le hs'.right_le
        (hE.trans hDG)) (fun x hx => ?_)
        (fun e he => ?_) ?_
      · rcases mem_V_or hs hx with h₁ | h₁
        · exact Or.inl (Or.inl h₁)
        · rcases mem_V_or hs' hx with h₂ | h₂
          · exact (mem_V_or hCE ⟨h₁, h₂⟩).imp Or.inr Or.inr
          · exact Or.inr (Or.inl h₂)
      · rcases mem_E_or hs he with h₁ | h₁
        · exact Or.inl (Or.inl h₁)
        · rcases mem_E_or hs' he with h₂ | h₂
          · exact (mem_E_or hCE ⟨h₁, h₂⟩).imp Or.inr Or.inr
          · exact Or.inr (Or.inl h₂)
      · rintro e (he | he) (he' | he')
        · exact hs.notMem_edgeSet_right he (hB.edgeSet_subset he')
        · exact hs.notMem_edgeSet_right he (hDB.edgeSet_subset (hE.edgeSet_subset he'))
        · exact hs'.notMem_edgeSet_right (hDA'.edgeSet_subset (hC.edgeSet_subset he)) he'
        · exact hCE.notMem_edgeSet_right he he'
    have hsub : ((A ∪ C) ∩ (B' ∪ E)).vertexSet ⊆ (C ∩ E).vertexSet := by
      rintro x ⟨hx | hx, hx' | hx'⟩
      · exact ⟨hZC ⟨hx, hB.vertexSet_subset hx'⟩, hZE ⟨hA.vertexSet_subset hx, hx'⟩⟩
      · exact ⟨hZC ⟨hx, (hCE.right_le.trans hDB).vertexSet_subset hx'⟩, hx'⟩
      · exact ⟨hx, hZE ⟨(hC.trans hDA').vertexSet_subset hx, hx'⟩⟩
      · exact ⟨hx, hx'⟩
    have hlt' : separationOrder (A ∪ C) (B' ∪ E) < n :=
      (order_le_of_subset (C ∩ E).vertexSet_finite hsub).trans_lt hlt
    have hnθ : n < θ := hT.order_lt h.mem
    have hmem : (A ∪ C, B' ∪ E) ∈ T := GraphMinor.GM10.theorem_2_9_proof hT hm hsep
      (hlt'.trans hnθ) (Or.inr (Or.inl
      (union_subset hA.vertexSet_subset (hC.trans hDA').vertexSet_subset)))
    exact h.no_lower _ _ hmem hlt' (le_union_left hs.left_le (hC.trans hDG)) (union_le hB
      (hE.trans hDB))
  obtain ⟨P, hP⟩ : HasDisjointPaths D.skeleton (A ∩ B).vertexSet (A' ∩ B').vertexSet n :=
    (menger D _ _ hZD hZ₂D n).1 hmenger
  have hfin₁ : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
  have hfin₂ : (A' ∩ B').vertexSet.Finite := (A' ∩ B').vertexSet_finite
  have hstart : ∀ i, (P i).first ∈ pathV (P i) := fun i => (P i).walk.start_mem_support
  have hend : ∀ i, (P i).last ∈ pathV (P i) := fun i => (P i).walk.end_mem_support
  have hdis : Pairwise fun i j => Disjoint (pathV (P i)) (pathV (P j)) := hP
  have hinj₁ : Function.Injective fun i => (P i).first := fun i j he => by
    by_contra hij
    exact disjoint_left.1 (hdis hij) (hstart i) ((show (P i).first = (P j).first from he) ▸ hstart
      j)
  have hinj₂ : Function.Injective fun i => (P i).last := fun i j he => by
    by_contra hij
    exact disjoint_left.1 (hdis hij) (hend i) ((show (P i).last = (P j).last from he) ▸ hend j)
  have hidx₁ : ∀ {x}, x ∈ (A ∩ B).vertexSet → ∃ i, (P i).first = x := fun hx =>
    exists_index _ hfin₁ hZc hinj₁ (fun i => (P i).first_mem) hx
  have hidx₂ : ∀ {x}, x ∈ (A' ∩ B').vertexSet → ∃ i, (P i).last = x := fun hx =>
    exists_index _ hfin₂ hZ₂c hinj₂ (fun i => (P i).last_mem) hx
  have hfirst : ∀ i, ∀ x ∈ pathV (P i), x ∈ (A ∩ B).vertexSet → x = (P i).first := fun i x hx hxZ
    => by
    obtain ⟨j, rfl⟩ := hidx₁ hxZ
    by_cases hij : i = j
    · rw [hij]
    · exact (disjoint_left.1 (hdis hij) hx (hstart j)).elim
  have hlast : ∀ i, ∀ x ∈ pathV (P i), x ∈ (A' ∩ B').vertexSet → x = (P i).last := fun i x hx hxZ
    => by
    obtain ⟨j, rfl⟩ := hidx₂ hxZ
    by_cases hij : i = j
    · rw [hij]
    · exact (disjoint_left.1 (hdis hij) hx (hend j)).elim
  have hVZ : ∀ {y}, y ∈ S ∪ R → y ∈ (A ∩ B).vertexSet := fun hy => h.union_eq ▸ hy
  obtain ⟨i₁, hi₁⟩ := hidx₁ (hVZ (Or.inl h.vS))
  obtain ⟨i₂, hi₂⟩ := hidx₁ (hVZ (Or.inr h.wR))
  obtain ⟨J', hconnJ, hJJ', hJA, hvJ, heqJ, hadjJ, hsubJ⟩ := exists_extended_side hA hB hDA'
    hZD hdis hlast h.connJ
    h.subJ h.v_mem h.eqJ h.adjS i₁ hi₁
  obtain ⟨K', hconnK, hKK', hKA, hwK, heqK, hadjK, hsubK⟩ := exists_extended_side hA hB hDA'
    hZD hdis hlast h.connK
    h.subK h.w_mem h.eqK h.adjR i₂ hi₂
  let I : Set (Fin n) := {i | (P i).first ∈ S}
  let I' : Set (Fin n) := {i | (P i).first ∈ R}
  have hdisII' : ∀ i, i ∈ I → i ∉ I' := fun i h₁ h₂ => disjoint_left.1 h.disj h₁ h₂
  have hcovI : ∀ i, i ∈ I ∨ i ∈ I' := fun i => by
    have : (P i).first ∈ S ∪ R := by
      rw [h.union_eq]
      exact (P i).first_mem
    exact this
  have hcard : ∀ {W : Set α}, W ⊆ (A ∩ B).vertexSet → ((fun i => (P i).last) '' {i |
    (P i).first ∈ W}).ncard ≤ W.ncard := fun {W} hW => by
    refine (ncard_image_le (toFinite _)).trans ?_
    rw [← ncard_image_of_injective _ hinj₁]
    exact ncard_le_ncard (by rintro _ ⟨i, hi, rfl⟩; exact hi) (hfin₁.subset hW)
  have hPB : ∀ i, pathV (P i) ⊆ B.vertexSet := fun i _ hx =>
    hDB.vertexSet_subset (support_mem (P i).walk (hZD (P i).first_mem) hx)
  have hPJ : ∀ i, (P i).first ∈ R → Disjoint J (pathV (P i)) := fun i hi
    => disjoint_left.2 fun x hxJ hx => by
    have hxv := h.eqJ x hxJ (hPB i hx)
    have := hfirst i x hx (hxv ▸ hVZ (Or.inl h.vS))
    exact disjoint_left.1 h.disj (by rw [← this, hxv]; exact h.vS) hi
  have hPK : ∀ i, (P i).first ∈ S → Disjoint K (pathV (P i)) := fun i hi
    => disjoint_left.2 fun x hxK hx => by
    have hxw := h.eqK x hxK (hPB i hx)
    have := hfirst i x hx (hxw ▸ hVZ (Or.inr h.wR))
    exact disjoint_left.1 h.disj hi (by rw [← this, hxw]; exact h.wR)
  have hi₁S : (P i₁).first ∈ S := hi₁ ▸ h.vS
  have hi₂R : (P i₂).first ∈ R := hi₂ ▸ h.wR
  have hdisJ' : Disjoint J' K' := by
    refine disjoint_left.2 fun x hx hx' => ?_
    -- Each side reads as: in `J`, or on a path that starts in `S`.
    have hx₁ : x ∈ J ∨ ∃ i, (P i).first ∈ S ∧ x ∈ pathV (P i) := by
      rcases hsubJ x hx with h₁ | h₁ | h₁
      · exact Or.inl h₁
      · exact Or.inr ⟨i₁, hi₁S, h₁⟩
      · exact Or.inr h₁
    have hx₂ : x ∈ K ∨ ∃ i, (P i).first ∈ R ∧ x ∈ pathV (P i) := by
      rcases hsubK x hx' with h₁ | h₁ | h₁
      · exact Or.inl h₁
      · exact Or.inr ⟨i₂, hi₂R, h₁⟩
      · exact Or.inr h₁
    rcases hx₁ with h₁ | ⟨i, hi, h₁⟩ <;> rcases hx₂ with h₂ | ⟨j, hj, h₂⟩
    · exact disjoint_left.1 h.disjJK h₁ h₂
    · exact disjoint_left.1 (hPJ j hj) h₁ h₂
    · exact disjoint_left.1 (hPK i hi) h₂ h₁
    · by_cases hij : i = j
      · exact disjoint_left.1 h.disj hi (hij ▸ hj)
      · exact disjoint_left.1 (hdis hij) h₁ h₂
  have hc : Cand G T k s t A' B' ((fun i => (P i).last) '' I) ((fun i => (P i).last) '' I') J' K'
    (P i₁).last (P i₂).last := {
    mem := hm
    no_lower := fun A₁ B₁ hm₁ ho₁ hle₁ hle₂ => h.no_lower A₁ B₁ hm₁ (ho₁.trans_eq ho)
      (hA.trans hle₁) (hle₂.trans hB)
    union_eq := by
      ext x
      constructor
      · rintro (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) <;> exact (P i).last_mem
      · intro hx
        obtain ⟨i, rfl⟩ := hidx₂ hx
        exact (hcovI i).imp (fun hi => ⟨i, hi, rfl⟩) fun hi => ⟨i, hi, rfl⟩
    disj := by
      refine disjoint_left.2 ?_
      rintro _ ⟨i, hi, rfl⟩ ⟨j, hj, he⟩
      obtain rfl := hinj₂ he
      exact hdisII' _ hi hj
    cardS := (hcard fun x hx => hVZ (Or.inl hx)).trans h.cardS
    cardR := (hcard fun x hx => hVZ (Or.inr hx)).trans h.cardR
    s_mem := hJJ' h.s_mem
    t_mem := hKK' h.t_mem
    connJ := hconnJ
    connK := hconnK
    subJ := hJA
    subK := hKA
    disjJK := hdisJ'
    v_mem := hvJ
    w_mem := hwK
    vS := ⟨i₁, hi₁S, rfl⟩
    wR := ⟨i₂, hi₂R, rfl⟩
    eqJ := heqJ
    eqK := heqK
    adjS := by
      rintro _ ⟨i, hi, rfl⟩ hne'
      exact hadjJ i hi fun e => hne' (e ▸ rfl)
    adjR := by
      rintro _ ⟨i, hi, rfl⟩ hne'
      exact hadjK i hi fun e => hne' (e ▸ rfl) }
  have := hmax _ _ _ _ _ _ _ _ hc
  exact absurd (size_lt_of_lt hA hne.symm) (by omega)

/-- **(6)** in the proof of (3.2) (page 333). -/
theorem card_S_eq (hG : G.IsGraph) (hT : IsTangle G θ T) (hθ : 18 * k + 3
  ≤ θ) {S R J K : Set α} {v w : α}
    (h : Cand G T k s t A B S R J K v w) (hmax : IsMaxCand G T k s t A) : S.ncard = 9 * k + 1 := by
  classical
  by_contra hne
  have hS : S.ncard ≤ 9 * k := by
    have := h.cardS
    omega
  have hs := hT.isSeparation h.mem
  have hAG := hs.left_le
  have hBG := hs.right_le
  have hZ : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
  have hZA : ∀ {x}, x ∈ S ∪ R → x ∈ (A ∩ B).vertexSet := fun hx => h.union_eq ▸ hx
  have hvZ : v ∈ (A ∩ B).vertexSet := hZA (Or.inl h.vS)
  have hn : separationOrder A B ≤ 18 * k + 1 := by
    have h₁ : separationOrder A B = (S ∪ R).ncard := by
      unfold separationOrder
      rw [h.union_eq]
    have h₂ := ncard_union_le S R
    have h₃ := h.cardR
    omega
  have hvA : v ∈ A.vertexSet := hvZ.1
  -- There is an edge of `B` at `v`.
  obtain ⟨e, heB, hev⟩ : ∃ e ∈ B.edgeSet, G.Inc e v := by
    by_contra hno
    push Not at hno
    obtain ⟨B₁, hm, hVB, hEB⟩ := exists_trim hT h.mem (W := {v}) (singleton_subset_iff.2 hvA)
      fun e he x hx => (show x = v from hx) ▸ hno e he
    have hs₁ := hT.isSeparation hm
    have hle : B₁ ≤ B := le_of_sets hs₁.right_le hBG (hVB ▸ sdiff_subset) hEB.subset
    have hsub : (A ∩ B₁).vertexSet ⊆ (A ∩ B).vertexSet \ {v} := by
      rintro x ⟨h₁, h₂⟩
      rw [hVB] at h₂
      exact ⟨⟨h₁, h₂.1⟩, h₂.2⟩
    have hlt : separationOrder A B₁ < separationOrder A B :=
      (ncard_le_ncard hsub hZ.sdiff).trans_lt (ncard_sdiff_singleton_lt_of_mem hvZ hZ)
    exact h.no_lower A B₁ hm hlt le_rfl hle
  -- One end of `e` is not in `V(A)`.
  obtain ⟨u, heu, huA⟩ : ∃ u, G.Inc e u ∧ u ∉ A.vertexSet := by
    by_contra hno
    push Not at hno
    obtain ⟨A₁, B₁, hm, hVA, hEA, hVB, hEB⟩ := exists_move (F := {e}) hT h.mem (by
      rintro f rfl
      exact ⟨heB, hno⟩)
    have hs₁ := hT.isSeparation hm
    have hle₁ : A ≤ A₁ := le_of_sets hAG hs₁.left_le hVA.symm.subset (hEA ▸ subset_union_left)
    have hle₂ : B₁ ≤ B := le_of_sets hs₁.right_le hBG hVB.subset (hEB ▸ sdiff_subset)
    refine no_same_order hT h hmax hm ?_ hle₁ hle₂ fun e' => ?_
    · unfold separationOrder
      change (A₁.vertexSet ∩ B₁.vertexSet).ncard = (A.vertexSet ∩ B.vertexSet).ncard
      rw [hVA, hVB]
    · have : e ∈ A₁.edgeSet := hEA ▸ Or.inr rfl
      exact hs.notMem_edgeSet_right (e' ▸ this) heB
  have huv : v ≠ u := fun e' => huA (e' ▸ hvA)
  have hends : ∀ x, G.Inc e x → x = v ∨ x = u := fun x hx => end_eq_or hG hev heu huv hx
  have huG : u ∈ G.vertexSet := G.vertex_mem_of_inc heu
  have heG : e ∈ G.edgeSet := G.edge_mem_of_inc hev
  have huB : u ∈ B.vertexSet := end_mem hBG heB heu
  let A' := subOf G (A.vertexSet ∪ {u}) (A.edgeSet ∪ {e}) (union_subset hAG.vertexSet_subset
    (singleton_subset_iff.2 huG)) (by
    rintro f (hf | rfl)
    · exact ⟨hAG.edgeSet_subset hf, fun x hx => Or.inl (end_mem hAG hf hx)⟩
    · refine ⟨heG, fun x hx => ?_⟩
      rcases hends x hx with rfl | rfl
      · exact Or.inl hvA
      · exact Or.inr rfl)
  let B' := subOf G B.vertexSet (B.edgeSet \ {e}) hBG.vertexSet_subset (fun f hf =>
    ⟨hBG.edgeSet_subset hf.1, fun x hx => end_mem hBG hf.1 hx⟩)
  have hA'G : A' ≤ G := subOf_le
  have hB'G : B' ≤ G := subOf_le
  have hle₁ : A ≤ A' := le_of_sets hAG hA'G (fun _ hx => Or.inl hx) fun _ hx => Or.inl hx
  have hle₂ : B' ≤ B := le_of_sets hB'G hBG subset_rfl fun _ hx => hx.1
  have hs' : G.IsSeparation A' B' := by
    refine sep_of_sets hA'G hB'G (fun x hx => ?_) (fun f hf => ?_) ?_
    · exact (mem_V_or hs hx).imp Or.inl id
    · by_cases hfe : f = e
      · exact Or.inl (Or.inr hfe)
      · exact (mem_E_or hs hf).imp Or.inl fun h₁ => ⟨h₁, hfe⟩
    · rintro f (hf | rfl) hf'
      · exact hs.notMem_edgeSet_right hf hf'.1
      · exact hf'.2 rfl
  have hVeq : (A' ∩ B').vertexSet = insert u (A ∩ B).vertexSet := by
    ext x
    constructor
    · rintro ⟨h₁ | h₁, h₂⟩
      · exact Or.inr ⟨h₁, h₂⟩
      · exact Or.inl h₁
    · rintro (rfl | h₁)
      · exact ⟨Or.inr rfl, huB⟩
      · exact ⟨Or.inl h₁.1, h₁.2⟩
  have huZ : u ∉ (A ∩ B).vertexSet := fun hx => huA hx.1
  have ho : separationOrder A' B' = separationOrder A B + 1 := by
    unfold separationOrder
    rw [hVeq, ncard_insert_of_notMem huZ hZ]
  have hm' : (A', B') ∈ T := GraphMinor.GM10.theorem_2_9_proof hT h.mem hs' (by omega)
    (Or.inl subset_rfl)
  have hc : Cand G T k s t A' B' (insert u S) R J K v w := {
    mem := hm'
    no_lower := fun A₁ B₁ hm₁ ho₁ hle₃ hle₄ => by
      have ha := hle₁.trans hle₃
      have hb := hle₄.trans hle₂
      by_cases hlt : separationOrder A₁ B₁ < separationOrder A B
      · exact h.no_lower A₁ B₁ hm₁ hlt ha hb
      · refine no_same_order hT h hmax hm₁ (by omega) ha hb fun e' => ?_
        have : e ∈ A₁.edgeSet := hle₃.edgeSet_subset (Or.inr rfl)
        exact hs.notMem_edgeSet_right (e' ▸ this) heB
    union_eq := by
      rw [hVeq, ← h.union_eq, insert_union]
    disj := by
      refine disjoint_left.2 ?_
      rintro x (rfl | hx) hxR
      · exact huZ (hZA (Or.inr hxR))
      · exact disjoint_left.1 h.disj hx hxR
    cardS := (ncard_insert_le _ _).trans (by omega)
    cardR := h.cardR
    s_mem := h.s_mem
    t_mem := h.t_mem
    connJ := h.connJ.mono hle₁
    connK := h.connK.mono hle₁
    subJ := h.subJ.trans hle₁.vertexSet_subset
    subK := h.subK.trans hle₁.vertexSet_subset
    disjJK := h.disjJK
    v_mem := h.v_mem
    w_mem := h.w_mem
    vS := Or.inr h.vS
    wR := h.wR
    eqJ := fun x hx hxB => h.eqJ x hx (hle₂.vertexSet_subset hxB)
    eqK := fun x hx hxB => h.eqK x hx (hle₂.vertexSet_subset hxB)
    adjS := by
      rintro x (rfl | hx) hne'
      · refine ⟨v, h.v_mem, huv.symm, e, ?_, ?_⟩
        · exact (inc_iff_of_le hA'G (Or.inr rfl)).2 heu
        · exact (inc_iff_of_le hA'G (Or.inr rfl)).2 hev
      · obtain ⟨y, hy, hadj⟩ := h.adjS x hx hne'
        exact ⟨y, hy, skeleton_mono hle₁ hadj⟩
    adjR := fun x hx hne' => by
      obtain ⟨y, hy, hadj⟩ := h.adjR x hx hne'
      exact ⟨y, hy, skeleton_mono hle₁ hadj⟩ }
  have hlt : size A < size A' := size_lt_of_lt hle₁ fun e' => huA (e' ▸
    (Or.inr rfl : u ∈ A'.vertexSet))
  have := hmax _ _ _ _ _ _ _ _ hc
  omega

/-- Paths of a subgraph are paths of the graph. -/
theorem HasDisjointPaths.mono {K L : SimpleGraph α} (h : K ≤ L) {X Y : Set α} {n : ℕ}
  (hp : HasDisjointPaths K X Y n) :
    HasDisjointPaths L X Y n := by
  obtain ⟨P, hP⟩ := hp
  refine ⟨fun i => ⟨(P i).first, (P i).last, (P i).walk.mapLe h, (P i).isPath.mapLe h,
    (P i).first_mem, (P i).last_mem⟩, ?_⟩
  intro i j hij
  simpa using hP hij

end GraphMinor.RST94
