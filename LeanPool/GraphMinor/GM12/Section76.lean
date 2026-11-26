/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM11.Section64
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM11.CitedResults

/-!
# Graph Minors XII, (7.6): deleting vertices near a region

This file defines vertex deletion and proves the metric comparison used in **(7.6)** of
Graph Minors XII (page 266). The main induction is in `Section7Proved.lean`.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Function Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-! ## 1. Vertex deletion in a drawing -/

omit [T2Space S] in
/-- `Γ \ Z`, the subdrawing of `Γ` obtained by deleting a set `Z` of vertices and all edges incident
with `Z` (Graph Minors XII, Section 7, pages 261–268). -/
def deleteVertices (Γ : Drawing S) (Z : Set S) : Drawing S :=
  Γ.span (Γ.V \ Z) {e ∈ Γ.E | Disjoint (closure e ∩ Γ.V) Z}

theorem deleteVertices_isSubdrawing (Γ : Drawing S) (Z : Set S) :
    (deleteVertices Γ Z).IsSubdrawing Γ :=
  Γ.span_isSubdrawing _ _

theorem deleteVertices_E (Γ : Drawing S) (Z : Set S) :
    (deleteVertices Γ Z).E = {e ∈ Γ.E | Disjoint (closure e ∩ Γ.V) Z} := by
  rw [deleteVertices, Drawing.span_E]
  ext e
  simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
  exact fun h => h.1

theorem deleteVertices_V (Γ : Drawing S) (Z : Set S) :
    (deleteVertices Γ Z).V = Γ.V \ Z := by
  rw [deleteVertices, Drawing.span_V, Drawing.spanV]
  ext x
  simp only [mem_inter_iff, mem_union, mem_sdiff, mem_iUnion, exists_prop]
  constructor
  · rintro (⟨⟨hxV, hxZ⟩, _⟩ | ⟨e, ⟨⟨_, hdisj⟩, _⟩, hxe, hxV⟩)
    · exact ⟨hxV, hxZ⟩
    · exact ⟨hxV, disjoint_left.mp hdisj ⟨hxe, hxV⟩⟩
  · rintro ⟨hxV, hxZ⟩
    exact Or.inl ⟨⟨hxV, hxZ⟩, hxV⟩

theorem isSubdrawing_deleteVertices_iff {Γ Γ' : Drawing S} {Z : Set S} :
    Γ'.IsSubdrawing (deleteVertices Γ Z) ↔ Γ'.IsSubdrawing Γ ∧ Disjoint Γ'.V Z := by
  constructor
  · intro h
    refine ⟨h.trans (deleteVertices_isSubdrawing Γ Z), ?_⟩
    rw [disjoint_iff_inter_eq_empty]
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxV' hxZ
    have hx : x ∈ Γ.V \ Z := deleteVertices_V Γ Z ▸ h.1 hxV'
    exact hx.2 hxZ
  · rintro ⟨hSub, hDisj⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [deleteVertices_V]
      exact ⟨hSub.1 hx, disjoint_left.mp hDisj hx⟩
    · rw [deleteVertices_E]
      intro e he
      refine ⟨hSub.2 he, ?_⟩
      rw [← hSub.closure_inter_V he]
      exact Disjoint.mono_left inter_subset_right hDisj

/-! ## 2. Atom dichotomy when `Γ.U ⊆ Γ'.U ∪ r'` -/

omit [T2Space S] in
/-- If `r` is a region of `Γ` and `r'` is a region of a subdrawing `Γ'` of `Γ` with `r ∩ r'`
nonempty, then `r ⊆ r'`. -/
theorem region_subset_region_of_inter_nonempty {Γ Γ' : Drawing S}
    (hSub : Γ'.IsSubdrawing Γ) {r r' : Set S} (hr : r ∈ Γ.R) (hr' : r' ∈ Γ'.R)
    (hne : (r ∩ r').Nonempty) : r ⊆ r' := by
  obtain ⟨x, hxr, hxr'⟩ := hne
  obtain ⟨a', ha', hra'⟩ := exists_atom_superset_of_isSubdrawing hSub (Or.inr hr)
  have heq : a' = r' := atom_eq_of_inter_nonempty ha' (Or.inr hr') ⟨x, hra' hxr, hxr'⟩
  exact heq ▸ hra'

omit [T2Space S] in
/-- If `Γ'` is a subdrawing of `Γ`, `r' ∈ Γ'.R`, and `Γ.U ⊆ Γ'.U ∪ r'`, then for any atom `a ∈ Γ.A`
and `a' ∈ Γ'.A` with `a ⊆ a'`, either `a = a'` (and `a ∈ Γ.A ∩ Γ'.A`) or `a' = r'` (and `a ⊆ r'`).
-/
theorem atom_eq_or_eq_region_of_U_subset {Γ Γ' : Drawing S}
    (hSub : Γ'.IsSubdrawing Γ) {r' : Set S} (hr' : r' ∈ Γ'.R)
    (hU : Γ.U ⊆ Γ'.U ∪ r') {a a' : Set S} (ha : a ∈ Γ.A) (ha' : a' ∈ Γ'.A)
    (haa' : a ⊆ a') :
    (a = a' ∧ a ∈ Γ.A ∩ Γ'.A) ∨ (a' = r' ∧ a ⊆ r') := by
  obtain ⟨x, hxa⟩ := atom_nonempty' ha
  rcases ha with (⟨v, hv, rfl⟩ | haE) | haR
  · rcases hU (Γ.V_subset_U hv) with hvU' | hvr'
    · have hvV' : v ∈ Γ'.V := (isSubdrawing_U_inter_V hSub).subset ⟨hvU', hv⟩
      have hvA' : ({v} : Set S) ∈ Γ'.A := Or.inl (Or.inl ⟨v, hvV', rfl⟩)
      have heq : {v} = a' := atom_eq_of_inter_nonempty hvA' ha' ⟨v, rfl, haa' rfl⟩
      exact Or.inl ⟨heq, Or.inl (Or.inl ⟨v, hv, rfl⟩), hvA'⟩
    · have heq : a' = r' := atom_eq_of_inter_nonempty ha' (Or.inr hr') ⟨v, haa' rfl, hvr'⟩
      exact Or.inr ⟨heq, heq ▸ haa'⟩
  · by_cases haE' : a ∈ Γ'.E
    · have heq : a = a' :=
        atom_eq_of_inter_nonempty (Or.inl (Or.inr haE')) ha' ⟨x, hxa, haa' hxa⟩
      exact Or.inl ⟨heq, Or.inl (Or.inr haE), Or.inl (Or.inr haE')⟩
    · have hxr' : x ∈ r' := by
        rcases hU (haE.2.1 hxa).1 with hxU' | hxr'
        · by_cases hxV' : x ∈ Γ'.V
          · exact ((haE.2.1 hxa).2 (hSub.1 hxV')).elim
          · obtain ⟨e', he', hxe'⟩ := Γ'.exists_edge_of_mem hxU' hxV'
            have heq : a = e' := atom_eq_of_inter_nonempty (Or.inl (Or.inr haE))
              (Or.inl (Or.inr (hSub.2 he'))) ⟨x, hxa, hxe'⟩
            exact (haE' (heq ▸ he')).elim
        · exact hxr'
      have heq : a' = r' := atom_eq_of_inter_nonempty ha' (Or.inr hr') ⟨x, haa' hxa, hxr'⟩
      exact Or.inr ⟨heq, heq ▸ haa'⟩
  · have ha'R : a' ∈ Γ'.R := by
      rcases ha' with (⟨v, hv', rfl⟩ | ha'E) | ha'R
      · exact (region_subset haR hxa (Γ.V_subset_U (hSub.1 (mem_singleton_iff.mp
          (haa' hxa) ▸ hv')))).elim
      · exact (region_subset haR hxa ((hSub.2 ha'E).2.1 (haa' hxa)).1).elim
      · exact ha'R
    by_cases heq_r' : a' = r'
    · exact Or.inr ⟨heq_r', heq_r' ▸ haa'⟩
    · have hdisj_r' : Disjoint a' r' := by
        rw [disjoint_iff_inter_eq_empty]
        by_contra hne
        exact heq_r' (atom_eq_of_inter_nonempty (Or.inr ha'R) (Or.inr hr')
          (nonempty_iff_ne_empty.mpr hne))
      have ha'_off : a' ⊆ univ \ Γ.U := by
        intro y hya'
        refine ⟨mem_univ y, fun hyU => ?_⟩
        rcases hU hyU with hyU' | hyr'
        · exact region_subset ha'R hya' hyU'
        · exact disjoint_left.mp hdisj_r' hya' hyr'
      have ha'_sub_a : a' ⊆ a := by
        have hconn : IsPreconnected a' := region_isPreconnected ha'R
        have hsub := hconn.subset_connectedComponentIn (haa' hxa) ha'_off
        have hx_eq : connectedComponentIn (univ \ Γ.U) x ∈ Γ.R :=
          (mem_R_iff Γ).mpr ⟨x, (ha'_off (haa' hxa)).2, rfl⟩
        have heq_a : a = connectedComponentIn (univ \ Γ.U) x :=
          atom_eq_of_inter_nonempty (Or.inr haR) (Or.inr hx_eq)
            ⟨x, hxa, mem_connectedComponentIn (ha'_off (haa' hxa))⟩
        exact heq_a.symm ▸ hsub
      have heq : a = a' := Subset.antisymm haa' ha'_sub_a
      exact Or.inl ⟨heq, Or.inr haR, Or.inr (heq.symm ▸ ha'R)⟩

/-! ## 3. Statement of (7.5) and Proof of (7.6) -/

/-- **(7.5)** of Graph Minors XII (pages 263–264):
"(7.5) *Let $\mathscr{T}$ be a respectful tangle of order $\theta \ge 3$ in a 2-cell drawing
$\Gamma$ in a connected surface $\Sigma$, and let its metric be $d$. Let $r$ be a region of
$\Gamma$, and let $Z$ be the set of vertices of $\Gamma$ incident with $r$. Then there is a 2-cell*
...
subdrawing $\Gamma'$ of $\Gamma \setminus Z$, and a respectful tangle $\mathscr{T}'$ of order
$\theta - 2$ in $\Gamma'$, with metric $d'$, such that if $r'$ is the region of $\Gamma'$ with
$r \subseteq r'$, then
$$
\begin{aligned}
\text{(i)} \quad & U(\Gamma) \subseteq U(\Gamma') \cup r' \\
\text{(ii)} \quad & d'(a, b) \ge d(a, b) - 4 \text{ for all } a, b \in A(\Gamma) \cap A(\Gamma') \\
\text{(iii)} \quad & d'(a, r') \ge d(a, r) - 2 \text{ for all } a \in A(\Gamma) \cap A(\Gamma'),
\text{ and} \\
\text{(iv)} \quad & d(a, r) \le 3 \text{ for all } a \in A(\Gamma) \text{ with } a \subseteq r'.
\end{aligned}
$$" -/
def Theorem75Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T2Space S] [ConnectedSpace S],
    IsClosedSurface S →
    ∀ (Γ : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (r : Set S),
      3 ≤ θ →
      HasTangleMetric Γ θ T d →
      r ∈ Γ.R →
      ∃ (Γ' : Drawing S)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ) (r' : Set S),
        Γ'.IsSubdrawing (deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}) ∧
        (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
        HasTangleMetric Γ' (θ - 2) T' d' ∧
        r' ∈ Γ'.R ∧ r ⊆ r' ∧
        Γ.U ⊆ Γ'.U ∪ r' ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 ≤ d' a b) ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 ≤ d' a r') ∧
        (∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 3)

/-- The set `Z` of vertices of `Γ` within normal-line distance `k` of a region `r`
(Graph Minors XII, (7.6), page 266): the vertices `v` of `Γ` such that there is a `Γ`-normal line
`F` with `v ∈ F`, `F ∩ r ≠ ∅`, and `|F ∩ V(Γ)| ≤ k`. -/
def regionLineVertices (Γ : Drawing S) (r : Set S) (k : ℕ) : Set S :=
  {v ∈ Γ.V | ∃ F : Set S, IsLine F ∧ (PaintingOrDrawing.drawing Γ).IsNormal F ∧
    v ∈ F ∧ (F ∩ r).Nonempty ∧ (F ∩ Γ.V).ncard ≤ k}

/-- The "In particular" deduction of **(7.6)** (page 266): conditions `(i)`–`(iv)` imply
`d'(a', b') ≥ d(a, b) - 4k - 2` for all `a, b ∈ A(Γ)` and `a', b' ∈ A(Γ')` with `a ⊆ a'` and
`b ⊆ b'`. -/
theorem theorem_7_6_in_particular
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ Γ' : Drawing S} {θ θ' k : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {r r' : Set S}
    (hd : HasTangleMetric Γ θ T d)
    (hd' : HasTangleMetric Γ' θ' T' d')
    (hSub : Γ'.IsSubdrawing Γ)
    (hr : r ∈ Γ.R) (hr' : r' ∈ Γ'.R)
    (h_i : Γ.U ⊆ Γ'.U ∪ r')
    (h_ii : ∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 * k ≤ d' a b)
    (h_iii : ∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 * k ≤ d' a r')
    (h_iv : ∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 2 * k + 1)
    {a b a' b' : Set S} (ha : a ∈ Γ.A) (hb : b ∈ Γ.A)
    (ha' : a' ∈ Γ'.A) (hb' : b' ∈ Γ'.A)
    (haa' : a ⊆ a') (hbb' : b ⊆ b') :
    d a b - 4 * k - 2 ≤ d' a' b' := by
  obtain ⟨_, _, _, hsym, htri, _, _⟩ := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hd
  obtain ⟨_, _, _, hsym', _, _, _⟩ := GM11.gm15_theorem_9_1 Γ' θ' T' d' hS inferInstance hd'
  have hrA : r ∈ Γ.A := Or.inr hr
  have hr'A : r' ∈ Γ'.A := Or.inr hr'
  rcases atom_eq_or_eq_region_of_U_subset hSub hr' h_i ha ha' haa' with
    ⟨ha_eq, ha_mem⟩ | ⟨ha'_eq, har'⟩
  · rw [← ha_eq]
    rcases atom_eq_or_eq_region_of_U_subset hSub hr' h_i hb hb' hbb' with
      ⟨hb_eq, hb_mem⟩ | ⟨hb'_eq, hbr'⟩
    · rw [← hb_eq]
      have h := h_ii a ha_mem b hb_mem
      omega
    · rw [hb'_eq]
      have h1 := h_iii a ha_mem
      have h2 := h_iv b hb hbr'
      have h3 := htri a ha r hrA b hb
      have h4 := hsym b hb r hrA
      omega
  · rw [ha'_eq]
    rcases atom_eq_or_eq_region_of_U_subset hSub hr' h_i hb hb' hbb' with
      ⟨hb_eq, hb_mem⟩ | ⟨hb'_eq, hbr'⟩
    · rw [← hb_eq]
      have h1 := h_iii b hb_mem
      have h2 := h_iv a ha har'
      have h3 := htri a ha r hrA b hb
      have h4 := hsym' b hb_mem.2 r' hr'A
      have h5 := hsym b hb r hrA
      omega
    · rw [hb'_eq]
      have h1 := h_iv a ha har'
      have h2 := h_iv b hb hbr'
      have h3 := htri a ha r hrA b hb
      have h4 := hsym b hb r hrA
      omega


end GraphMinor.GM12
