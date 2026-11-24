/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Thomas.Claims
public import Mathlib.Data.DFinsupp.WellFounded

/-!
# Fatness and Theorem 3 of Bellenbaum and Diestel

This file defines the fatness of a tree-decomposition (Section 1 of Bellenbaum and Diestel,
*Two short proofs concerning tree-decompositions*, Combin. Probab. Comput. 11 (2002), 541–547)
and completes the proof of Theorem 3: every finite graph has a lean tree-decomposition of minimum
width.

## Main definitions and results

* `GraphMinor.Thomas.TreeDecomp.countParts`: number of parts of a given size $h$.
* `GraphMinor.Thomas.TreeDecomp.fatness`: the lexicographically ordered tuple
  $(a_{|G|}, \dots, a_1)$ where $a_h$ is the number of parts of size $h$.
* `GraphMinor.Thomas.TreeDecomp.fatness_combine_lt`: the amalgamated tree-decomposition
$\mathcal{D}'$
  constructed in the proof of Theorem 3 has strictly smaller fatness than $\mathcal{D}$.
* `GraphMinor.Thomas.theorem_3`: **Theorem 3** of Bellenbaum and Diestel (Section 3, page 3).
-/

namespace GraphMinor.Thomas

open SimpleGraph

universe u v w

public section

variable {α : Type u} {β : Type v} {ι : Type w} [Fintype ι] {G : SimpleGraph α} {V₀ : Set α}

namespace TreeDecomp

/-- The number of parts $V_t$ ($t \in T$) of size $h$ in a tree-decomposition $\mathcal{D}$. -/
noncomputable def countParts (D : TreeDecomp G V₀ ι) (h : ℕ) : ℕ :=
  open Classical in
  (Finset.univ.filter fun t : ι ↦ (D.bag t).ncard = h).card

/-- The fatness of a tree-decomposition $\mathcal{D}$ of $(G, V_0)$ is the $|V_0|$-tuple
$(a_{|V_0|}, \dots, a_1) \in \mathbb{N}^{|V_0|}$, ordered lexicographically, where $a_h$ is the
number of parts of $\mathcal{D}$ of size $h$ (Bellenbaum and Diestel, Section 1, page 2). -/
noncomputable def fatness (D : TreeDecomp G V₀ ι) : Lex (Fin V₀.ncard → ℕ) :=
  toLex fun i : Fin V₀.ncard ↦ D.countParts (V₀.ncard - i.val)

/-- Reindexing the tree nodes by an equivalence preserves `countParts`. -/
theorem countParts_reindex (D : TreeDecomp G V₀ ι) {ι' : Type*} [Fintype ι'] (e : ι ≃ ι') (h : ℕ) :
    (D.reindex e).countParts h = D.countParts h := by
  classical
  unfold countParts
  refine Finset.card_bij (fun t _ ↦ e.symm t) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨Finset.mem_univ _, ht.2⟩
  · intro t₁ _ t₂ _ hEq
    exact e.symm.injective hEq
  · intro t ht
    rw [Finset.mem_filter] at ht
    refine ⟨e t, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, e.symm_apply_apply t⟩
    change (D.bag (e.symm (e t))).ncard = h
    rw [e.symm_apply_apply]
    exact ht.2

/-- Reindexing the tree nodes by an equivalence preserves `fatness`. -/
theorem fatness_reindex (D : TreeDecomp G V₀ ι) {ι' : Type*} [Fintype ι'] (e : ι ≃ ι') :
    (D.reindex e).fatness = D.fatness := by
  unfold fatness
  congr 1
  ext i
  exact D.countParts_reindex e (V₀.ncard - i.val)

/-- If $\mathcal{D}$ has width $\le w$, then it has no parts of size $> w + 1$. -/
theorem countParts_eq_zero_of_widthLE (D : TreeDecomp G V₀ ι) {w h : ℕ}
    (hw : D.WidthLE w) (hh : w + 1 < h) : D.countParts h = 0 := by
  classical
  unfold countParts
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro t _
  have hle := hw t
  omega

/-- If $\mathcal{D}$ has fatness at most that of $\mathcal{D}_0$ and $\mathcal{D}_0$ has width
$\le w$, then $\mathcal{D}$ also has width $\le w$. -/
theorem widthLE_of_fatness_le (D : TreeDecomp G V₀ ι) {ι₀ : Type*} [Fintype ι₀]
    (D₀ : TreeDecomp G V₀ ι₀) (hV₀ : V₀.Finite) {w : ℕ}
    (hw : D₀.WidthLE w) (hle : D.fatness ≤ D₀.fatness) : D.WidthLE w := by
  intro t
  by_contra! hgt
  set h := (D.bag t).ncard
  have hh_le : h ≤ V₀.ncard := Set.ncard_le_ncard (D.bag_subset t) hV₀
  have hh_pos : 1 ≤ h := by omega
  let i : Fin V₀.ncard := ⟨V₀.ncard - h, by omega⟩
  have hi_val : V₀.ncard - i.val = h := Nat.sub_sub_self hh_le
  have hD_pos : 0 < D.fatness i := by
    classical
    change 0 < D.countParts (V₀.ncard - i.val)
    rw [hi_val]
    unfold countParts
    rw [Finset.card_pos]
    exact ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  have hD₀_zero : ∀ j : Fin V₀.ncard, j ≤ i → D₀.fatness j = 0 := by
    intro j hj
    change D₀.countParts (V₀.ncard - j.val) = 0
    apply D₀.countParts_eq_zero_of_widthLE hw
    have hj_le : j.val ≤ V₀.ncard - h := hj
    omega
  rcases lt_or_eq_of_le hle with hlt | heq
  · rcases hlt with ⟨j, hj_eq, hj_lt⟩
    rcases le_or_gt j i with hji | hij
    · exact Nat.not_lt_zero _ (hD₀_zero j hji ▸ hj_lt)
    · have h1 : D.fatness i = D₀.fatness i := hj_eq i hij
      have h0 : D₀.fatness i = 0 := hD₀_zero i le_rfl
      omega
  · have h1 : D.fatness i = D₀.fatness i := by rw [heq]
    have h0 := hD₀_zero i le_rfl
    omega

/-- In the proof of Theorem 3 of Bellenbaum and Diestel (Section 3, page 5), the combined
tree-decomposition $\mathcal{D}'$ has strictly smaller fatness than $\mathcal{D}$. -/
theorem fatness_combine_lt (D : TreeDecomp G V₀ ι) (hV₀ : V₀.Finite)
    {X C₁ C₂ : Set α} (hX : X ⊆ V₀) (hC₁ : C₁ ⊆ V₀) (hC₂ : C₂ ⊆ V₀)
    (hcov : V₀ ⊆ C₁ ∪ C₂ ∪ X) (hdisj : Disjoint C₁ C₂)
    (hsep : ∀ ⦃u v : α⦄, u ∈ V₀ → v ∈ V₀ → G.Adj u v →
      (u ∈ C₁ ∪ X ∧ v ∈ C₁ ∪ X) ∨ (u ∈ C₂ ∪ X ∧ v ∈ C₂ ∪ X))
    {home : α → ι} (hhome : ∀ x ∈ X, x ∈ D.bag (home x))
    {t₁ t₂ : ι}
    (hle₁ : ∀ t, (D.shiftBag X C₁ home t₂ t).ncard ≤ (D.bag t).ncard)
    (hle₂ : ∀ t, (D.shiftBag X C₂ home t₁ t).ncard ≤ (D.bag t).ncard)
    (hclaim₁ : ∀ t,
      ((D.shiftBag X C₁ home t₂ t).ncard = (D.bag t).ncard → D.shiftBag X C₂ home t₁ t ⊆ X) ∧
      ((D.shiftBag X C₂ home t₁ t).ncard = (D.bag t).ncard → D.shiftBag X C₁ home t₂ t ⊆ X))
    {t₀ : ι}
    (ht₀_X : X.ncard < (D.bag t₀).ncard)
    (ht₀_1 : (D.shiftBag X C₁ home t₂ t₀).ncard < (D.bag t₀).ncard)
    (ht₀_2 : (D.shiftBag X C₂ home t₁ t₀).ncard < (D.bag t₀).ncard) :
    (D.combine hX hC₁ hC₂ hcov hdisj hsep hhome t₁ t₂).fatness < D.fatness := by
  classical
  let D' := D.combine hX hC₁ hC₂ hcov hdisj hsep hhome t₁ t₂
  let M : Finset ι := Finset.univ.filter fun t : ι ↦
    (D.shiftBag X C₁ home t₂ t).ncard < (D.bag t).ncard ∧
    (D.shiftBag X C₂ home t₁ t).ncard < (D.bag t).ncard
  have ht₀_M : t₀ ∈ M := Finset.mem_filter.2 ⟨Finset.mem_univ _, ht₀_1, ht₀_2⟩
  let S : Finset ℕ := M.image fun t ↦ (D.bag t).ncard
  have hS_ne : S.Nonempty := ⟨(D.bag t₀).ncard, Finset.mem_image_of_mem _ ht₀_M⟩
  let hstar : ℕ := S.max' hS_ne
  have ht₀_le_hstar : (D.bag t₀).ncard ≤ hstar :=
    Finset.le_max' S _ (Finset.mem_image_of_mem _ ht₀_M)
  have hX_lt_hstar : X.ncard < hstar := lt_of_lt_of_le ht₀_X ht₀_le_hstar
  have hhstar_mem : hstar ∈ S := Finset.max'_mem S hS_ne
  obtain ⟨tmax, htmax_M, htmax_eq⟩ := Finset.mem_image.1 hhstar_mem
  have hhstar_le_V₀ : hstar ≤ V₀.ncard := by
    rw [← htmax_eq]
    exact Set.ncard_le_ncard (D.bag_subset tmax) hV₀
  have hM_le_hstar : ∀ t ∈ M, (D.bag t).ncard ≤ hstar :=
    fun t ht ↦ Finset.le_max' S _ (Finset.mem_image_of_mem _ ht)
  -- Key bijection for all h ≥ hstar: parts of D' of size h correspond to t ∉ M with |V_t| = h
  have hcount_eq : ∀ h : ℕ, hstar ≤ h →
      D'.countParts h = (Finset.univ.filter fun t : ι ↦ t ∉ M ∧ (D.bag t).ncard = h).card := by
    intro h hh
    have hX_lt_h : X.ncard < h := lt_of_lt_of_le hX_lt_hstar hh
    unfold countParts
    refine Finset.card_bij (fun (p : Bool × ι) _ ↦ p.2) ?_ ?_ ?_
    · rintro ⟨b, t⟩ hp
      rw [Finset.mem_filter] at hp
      have hp_card : (D'.bag (b, t)).ncard = h := hp.2
      have hbag_ge : h ≤ (D.bag t).ncard := by
        cases b
        · rw [← hp_card]; exact hle₁ t
        · rw [← hp_card]; exact hle₂ t
      have ht_not_M : t ∉ M := by
        intro htM
        have hle_star := hM_le_hstar t htM
        rw [Finset.mem_filter] at htM
        cases b
        · change (D.shiftBag X C₁ home t₂ t).ncard = h at hp_card
          have := htM.2.1; omega
        · change (D.shiftBag X C₂ home t₁ t).ncard = h at hp_card
          have := htM.2.2; omega
      have hbag_eq : (D.bag t).ncard = h := by
        have hnot_both : ¬ ((D.shiftBag X C₁ home t₂ t).ncard < (D.bag t).ncard ∧
            (D.shiftBag X C₂ home t₁ t).ncard < (D.bag t).ncard) := by
          intro hboth
          exact ht_not_M (Finset.mem_filter.2 ⟨Finset.mem_univ _, hboth⟩)
        have hle1 := hle₁ t
        have hle2 := hle₂ t
        cases b
        · change (D.shiftBag X C₁ home t₂ t).ncard = h at hp_card
          by_contra hne
          have hlt1 : (D.shiftBag X C₁ home t₂ t).ncard < (D.bag t).ncard := by omega
          have heq2 : (D.shiftBag X C₂ home t₁ t).ncard = (D.bag t).ncard := by omega
          have hsub1 : D.shiftBag X C₁ home t₂ t ⊆ X := (hclaim₁ t).2 heq2
          have hle_X : (D.shiftBag X C₁ home t₂ t).ncard ≤ X.ncard :=
            Set.ncard_le_ncard hsub1 (hV₀.subset hX)
          omega
        · change (D.shiftBag X C₂ home t₁ t).ncard = h at hp_card
          by_contra hne
          have hlt2 : (D.shiftBag X C₂ home t₁ t).ncard < (D.bag t).ncard := by omega
          have heq1 : (D.shiftBag X C₁ home t₂ t).ncard = (D.bag t).ncard := by omega
          have hsub2 : D.shiftBag X C₂ home t₁ t ⊆ X := (hclaim₁ t).1 heq1
          have hle_X : (D.shiftBag X C₂ home t₁ t).ncard ≤ X.ncard :=
            Set.ncard_le_ncard hsub2 (hV₀.subset hX)
          omega
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ht_not_M, hbag_eq⟩
    · rintro ⟨b₁, s₁⟩ hp₁ ⟨b₂, s₂⟩ hp₂ (rfl : s₁ = s₂)
      rw [Finset.mem_filter] at hp₁ hp₂
      congr 1
      by_contra hb_ne
      have hfalse : (D.shiftBag X C₁ home t₂ s₁).ncard = h := by
        cases b₁
        · exact hp₁.2
        · cases b₂
          · exact hp₂.2
          · exact (hb_ne rfl).elim
      have htrue : (D.shiftBag X C₂ home t₁ s₁).ncard = h := by
        cases b₁
        · cases b₂
          · exact (hb_ne rfl).elim
          · exact hp₂.2
        · exact hp₁.2
      have hle1 := hle₁ s₁
      have hle2 := hle₂ s₁
      have hbag_ge : h ≤ (D.bag s₁).ncard := by omega
      by_cases heq1 : (D.shiftBag X C₁ home t₂ s₁).ncard = (D.bag s₁).ncard
      · have hsub2 : D.shiftBag X C₂ home t₁ s₁ ⊆ X := (hclaim₁ s₁).1 heq1
        have hle_X : (D.shiftBag X C₂ home t₁ s₁).ncard ≤ X.ncard :=
          Set.ncard_le_ncard hsub2 (hV₀.subset hX)
        omega
      · have hlt1 : (D.shiftBag X C₁ home t₂ s₁).ncard < (D.bag s₁).ncard := by omega
        have hlt2 : (D.shiftBag X C₂ home t₁ s₁).ncard < (D.bag s₁).ncard := by omega
        have hs₁_M : s₁ ∈ M := Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt1, hlt2⟩
        have := hM_le_hstar s₁ hs₁_M
        omega
    · intro t ht
      rw [Finset.mem_filter] at ht
      rcases ht with ⟨_, ht_not_M, ht_card⟩
      have hnot_both : ¬ ((D.shiftBag X C₁ home t₂ t).ncard < (D.bag t).ncard ∧
          (D.shiftBag X C₂ home t₁ t).ncard < (D.bag t).ncard) :=
        fun hboth ↦ ht_not_M (Finset.mem_filter.2 ⟨Finset.mem_univ _, hboth⟩)
      have hle1 := hle₁ t
      have hle2 := hle₂ t
      by_cases heq1 : (D.shiftBag X C₁ home t₂ t).ncard = h
      · refine ⟨(false, t), Finset.mem_filter.2 ⟨Finset.mem_univ _, heq1⟩, rfl⟩
      · have heq2 : (D.shiftBag X C₂ home t₁ t).ncard = h := by omega
        refine ⟨(true, t), Finset.mem_filter.2 ⟨Finset.mem_univ _, heq2⟩, rfl⟩
  let istar : Fin V₀.ncard := ⟨V₀.ncard - hstar, by omega⟩
  have histar_val : V₀.ncard - istar.val = hstar := Nat.sub_sub_self hhstar_le_V₀
  refine ⟨istar, ?_, ?_⟩
  · intro j hj
    change D'.countParts (V₀.ncard - j.val) = D.countParts (V₀.ncard - j.val)
    have hj_lt : j.val < V₀.ncard - hstar := hj
    have hh_gt : hstar < V₀.ncard - j.val := by omega
    rw [hcount_eq (V₀.ncard - j.val) (le_of_lt hh_gt)]
    unfold countParts
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro ht_eq htM
    have := hM_le_hstar t htM
    omega
  · change D'.countParts (V₀.ncard - istar.val) < D.countParts (V₀.ncard - istar.val)
    rw [histar_val, hcount_eq hstar le_rfl]
    unfold countParts
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨tmax, Finset.mem_filter.2 ⟨Finset.mem_univ _, htmax_eq⟩, ?_⟩
      rw [Finset.mem_filter]
      intro h
      exact h.2.1 htmax_M
    · intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨Finset.mem_univ _, ht.2.2⟩

end TreeDecomp

/-- **Theorem 3** of Bellenbaum and Diestel (Section 3, page 3):
Every finite graph has a lean tree-decomposition of minimum width (that is, if `G` admits
a tree-decomposition of width $\le w$, then it admits a lean tree-decomposition of width $\le w$).
-/
theorem theorem_3 (G : Hypergraph α β)
    {ι₀ : Type w} [Fintype ι₀] (D₀ : TreeDecomp G.skeleton G.vertexSet ι₀) {w : ℕ}
    (hw₀ : D₀.WidthLE w) :
    ∃ (m : ℕ) (D : TreeDecomp G.skeleton G.vertexSet (Fin m)), D.IsLean ∧ D.WidthLE w := by
  classical
  have hV₀ : G.vertexSet.Finite := G.vertexSet_finite
  have hG : ∀ ⦃u v : α⦄, G.skeleton.Adj u v → u ∈ G.vertexSet ∧ v ∈ G.vertexSet :=
    fun _ _ ⟨_, _, hu, hv⟩ ↦ ⟨G.vertex_mem_of_inc hu, G.vertex_mem_of_inc hv⟩
  let Pack := Σ m : ℕ, TreeDecomp G.skeleton G.vertexSet (Fin m)
  let wf_fat : WellFounded (InvImage (· < ·) (fun p : Pack ↦ p.2.fatness)) :=
    InvImage.wf (fun p : Pack ↦ p.2.fatness) wellFounded_lt
  let S : Set Pack := {p | p.2.fatness ≤ D₀.fatness}
  have hS_ne : S.Nonempty := by
    refine ⟨⟨Fintype.card ι₀, D₀.reindex (Fintype.equivFin ι₀)⟩, ?_⟩
    rw [Set.mem_ofPred_eq, D₀.fatness_reindex]
  obtain ⟨⟨m, D⟩, hD_le, hD_min⟩ := wf_fat.has_min S hS_ne
  refine ⟨m, D, ?_, D.widthLE_of_fatness_le D₀ hV₀ hw₀ hD_le⟩
  by_contra hnot_lean
  -- There exists a violation of leanness
  have hex_viol : ∃ p : Fin m × Fin m × Set α × Set α × ℕ,
      D.ViolatesLean p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
    unfold TreeDecomp.IsLean at hnot_lean
    push Not at hnot_lean
    rcases hnot_lean with ⟨t₁, t₂, Z₁, Z₂, k, hZ₁, hZ₂, hk₁, hk₂, hpaths, hinter⟩
    exact ⟨(t₁, t₂, Z₁, Z₂, k), ⟨hZ₁, hZ₂, hk₁, hk₂, hpaths, hinter⟩⟩
  -- Minimize treeDist D.isTree t₁ t₂ among violations of leanness
  let wf_dist := InvImage.wf
    (fun p : Fin m × Fin m × Set α × Set α × ℕ ↦ treeDist D.isTree p.1 p.2.1) wellFounded_lt
  obtain ⟨⟨t₁, t₂, Z₁, Z₂, k⟩, hv, hmin_dist_raw⟩ :=
    wf_dist.has_min {p | D.ViolatesLean p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2} hex_viol
  have hmin_dist : ∀ t₁' t₂' Z₁' Z₂' k', D.ViolatesLean t₁' t₂' Z₁' Z₂' k' →
      treeDist D.isTree t₁ t₂ ≤ treeDist D.isTree t₁' t₂' := by
    intro t₁' t₂' Z₁' Z₂' k' hv'
    exact not_lt.1 (hmin_dist_raw (t₁', t₂', Z₁', Z₂', k') hv')
  -- By Menger's theorem, there exists a separator of Z₁ and Z₂ of size < k
  have hZ₁_V₀ : Z₁ ⊆ G.vertexSet := hv.subset_left.trans (D.bag_subset t₁)
  have hZ₂_V₀ : Z₂ ⊆ G.vertexSet := hv.subset_right.trans (D.bag_subset t₂)
  obtain ⟨X₀, hX₀_sep, hX₀_lt⟩ :=
    exists_separates_lt_of_not_hasDisjointPaths G hZ₁_V₀ hZ₂_V₀ hv.not_hasDisjointPaths
  -- First minimize |X| among separators of Z₁ and Z₂
  let wf_card := InvImage.wf (fun X : Set α ↦ X.ncard) wellFounded_lt
  obtain ⟨X₁, hX₁_sep, hmin_card_raw⟩ :=
    wf_card.has_min {X | Separates G.skeleton G.vertexSet Z₁ Z₂ X} ⟨X₀, hX₀_sep⟩
  have hmin_card₁ : ∀ X', Separates G.skeleton G.vertexSet Z₁ Z₂ X' → X₁.ncard ≤ X'.ncard :=
    fun X' hX' ↦ not_lt.1 (hmin_card_raw X' hX')
  -- Among minimum-order separators of Z₁ and Z₂, minimize sepDistSum
  let wf_sum := InvImage.wf (fun X : Set α ↦ D.sepDistSum hV₀ t₁ t₂ X) wellFounded_lt
  obtain ⟨X, ⟨hX_sep, hX_card_le⟩, hmin_sum_raw⟩ :=
    wf_sum.has_min {X | Separates G.skeleton G.vertexSet Z₁ Z₂ X ∧ X.ncard ≤ X₁.ncard}
      ⟨X₁, hX₁_sep, le_rfl⟩
  have hX_card_eq : X.ncard = X₁.ncard := le_antisymm hX_card_le (hmin_card₁ X hX_sep)
  have hmin_card : ∀ X', Separates G.skeleton G.vertexSet Z₁ Z₂ X' → X.ncard ≤ X'.ncard := by
    intro X' hX'
    rw [hX_card_eq]
    exact hmin_card₁ X' hX'
  have hX_lt : X.ncard < k := lt_of_le_of_lt (hmin_card X₀ hX₀_sep) hX₀_lt
  have hmin_sep : ∀ X', Separates G.skeleton G.vertexSet Z₁ Z₂ X' → X'.ncard ≤ X.ncard →
      D.sepDistSum hV₀ t₁ t₂ X ≤ D.sepDistSum hV₀ t₁ t₂ X' := by
    intro X' hX'_sep hX'_le
    rw [hX_card_eq] at hX'_le
    exact not_lt.1 (hmin_sum_raw X' ⟨hX'_sep, hX'_le⟩)
  -- Define C₁, C₂ and home
  let C₁ := sepCompLeft G.skeleton G.vertexSet X Z₁
  let C₂ := sepCompRight G.skeleton G.vertexSet X Z₁
  have hX : X ⊆ G.vertexSet := hX_sep.1
  have hC₁ : C₁ ⊆ G.vertexSet := sepCompLeft_subset G.skeleton G.vertexSet X Z₁
  have hC₂ : C₂ ⊆ G.vertexSet := sepCompRight_subset G.skeleton G.vertexSet X Z₁
  have hcov : G.vertexSet ⊆ C₁ ∪ C₂ ∪ X := subset_sepComp_union G.skeleton Z₁
  have hdisj : Disjoint C₁ C₂ := disjoint_sepCompLeft_sepCompRight G.skeleton G.vertexSet X Z₁
  have hdisj₁ : Disjoint C₁ X := disjoint_sepCompLeft_sep G.skeleton G.vertexSet X Z₁
  have hdisj₂ : Disjoint C₂ X := disjoint_sepCompRight_sep G.skeleton G.vertexSet X Z₁
  have hno_adj : ∀ ⦃a b : α⦄, a ∈ C₁ → b ∈ C₂ → ¬ G.skeleton.Adj a b :=
    fun _ _ ha hb ↦ not_adj_sepCompLeft_sepCompRight ha hb
  have hsep_adj : ∀ ⦃u v : α⦄, u ∈ G.vertexSet → v ∈ G.vertexSet → G.skeleton.Adj u v →
      (u ∈ C₁ ∪ X ∧ v ∈ C₁ ∪ X) ∨ (u ∈ C₂ ∪ X ∧ v ∈ C₂ ∪ X) :=
    fun _ _ hu hv hadj ↦ adj_mem_sepComp_or hu hv hadj
  have hZ₁C : Z₁ ⊆ C₁ ∪ X := subset_sepCompLeft_union G.skeleton hZ₁_V₀
  have hZ₂C : Z₂ ⊆ C₂ ∪ X := subset_sepCompRight_union hZ₂_V₀ hX_sep
  -- Obtain Menger paths for the minimum separator X
  obtain ⟨end₁, end₂, hend₁, hend₂, P₁, P₂, hP₁_sub, hP₁_disj, hP₂_sub, hP₂_disj⟩ :=
    exists_menger_walks_of_min_sep G hZ₁_V₀ hZ₂_V₀ hX_sep hmin_card hcov
      hdisj hdisj₁ hdisj₂ hno_adj hZ₁C hZ₂C
  let home := D.chooseHome t₁ t₂
  have hhome : ∀ x ∈ G.vertexSet, x ∈ D.bag (home x) := fun x hx ↦ D.chooseHome_mem_bag t₁ t₂ hx
  have hhome_X : ∀ x ∈ X, x ∈ D.bag (home x) := fun x hx ↦ hhome x (hX hx)
  have hhome_dist : ∀ x ∈ G.vertexSet, D.distToPath t₁ t₂ (home x) = D.vertDist t₁ t₂ x :=
    fun x hx ↦ D.distToPath_chooseHome t₁ t₂ hx
  -- Apply Lemma 2, Claim (1), and Claim (2)
  have hle₁ : ∀ t, (D.shiftBag X C₁ home t₂ t).ncard ≤ (D.bag t).ncard :=
    D.lemma_2 hV₀ hX hhome_X t₂ (fun x hx ↦ hv.subset_right (hend₂ x hx)) P₁ hP₁_sub hP₁_disj
  have hle₂ : ∀ t, (D.shiftBag X C₂ home t₁ t).ncard ≤ (D.bag t).ncard :=
    D.lemma_2 hV₀ hX hhome_X t₁ (fun x hx ↦ hv.subset_left (hend₁ x hx)) P₂ hP₂_sub hP₂_disj
  have hclaim₁ :=
    D.theorem_3_claim_1 hV₀ hG hv hmin_dist hX hC₁ hC₂ hcov hdisj hdisj₁ hdisj₂ hno_adj
      hZ₁C hZ₂C hX_lt hmin_sep hhome hhome_dist
  obtain ⟨t₀, ht₀_on, ht₀_1, ht₀_2⟩ :=
    D.theorem_3_claim_2 hV₀ hv hX hcov hdisj₁ hdisj₂ hZ₁C hZ₂C hX_lt hclaim₁ hle₁ hle₂
  have hk_le_t₀ : k ≤ (D.bag t₀).ncard := D.le_bag_ncard_of_violatesLean hV₀ hv ht₀_on
  have ht₀_X : X.ncard < (D.bag t₀).ncard := lt_of_lt_of_le hX_lt hk_le_t₀
  have hfat_lt :=
    D.fatness_combine_lt hV₀ hX hC₁ hC₂ hcov hdisj hsep_adj hhome_X hle₁ hle₂ hclaim₁
      ht₀_X ht₀_1 ht₀_2
  -- Reindex D' to Fin (2 * m) and contradict minimality of D
  let D' := D.combine hX hC₁ hC₂ hcov hdisj hsep_adj hhome_X t₁ t₂
  let m' := Fintype.card (Bool × Fin m)
  let D'' := D'.reindex (Fintype.equivFin (Bool × Fin m))
  have hfat_D'' : D''.fatness < D.fatness := by
    rw [D'.fatness_reindex]
    exact hfat_lt
  have hD''_mem : (⟨m', D''⟩ : Pack) ∈ S := le_trans (le_of_lt hfat_D'') hD_le
  exact hD_min ⟨m', D''⟩ hD''_mem hfat_D''

end

end GraphMinor.Thomas
