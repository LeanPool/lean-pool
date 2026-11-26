/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Thomas.Separator
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Claims ($\ast$), (1), and (2) in the proof of Theorem 3 (Bellenbaum–Diestel, Section 3)

This file formalizes the leanness condition (T4′), the tree-distance quantities $d_x$ and $t_x$, and
the three numbered claims ($\ast$), (1), and (2) in the proof of Theorem 3 of P. Bellenbaum and
R. Diestel, *Two short proofs concerning tree-decompositions*, Combin. Probab. Comput. 11 (2002)
541–547 (pages 3–5):

- **Claim ($\ast$)** (`theorem_3_star`, page 4):
  $$Y := W_t^1 \setminus V_t = \{\, x \in X \mid t \in t_x T t_2 \,\} \setminus V_t,$$
  and if $|W_t^1| = |V_t|$ then $|Y| = |V_t \cap V(C_2)|$.
- **Claim (1)** (`theorem_3_claim_1_left`, `theorem_3_claim_1`, pages 4–5):
  $$(\forall t \in T)(\forall i = 1, 2)\ \bigl(|W_t^i| = |V_t| \Rightarrow W_t^{3-i} \subseteq
  X\bigr).$$
- **Claim (2)** (`theorem_3_claim_2`, page 5):
  $$(\exists t \in t_1 T t_2)\ \bigl(|W_t^1|, |W_t^2| < |V_t|\bigr).$$
-/

@[expose] public section

namespace GraphMinor.Thomas

open SimpleGraph

variable {α ι : Type*}

/-! ## Distance in a tree -/

/-- Distance $d_T(t_1, t_2)$ in a tree $T$: the length of the unique path `treePath hT t₁ t₂`. -/
noncomputable def treeDist {T : SimpleGraph ι} (hT : T.IsTree) (t₁ t₂ : ι) : ℕ :=
  (treePath hT t₁ t₂).length

@[simp]
theorem treeDist_self {T : SimpleGraph ι} (hT : T.IsTree) (t : ι) :
    treeDist hT t t = 0 := by
  unfold treeDist
  rw [← eq_treePath hT Walk.nil Walk.IsPath.nil]
  rfl

theorem treeDist_pos_of_ne {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ : ι} (hne : t₁ ≠ t₂) :
    0 < treeDist hT t₁ t₂ := by
  unfold treeDist
  cases h : treePath hT t₁ t₂ with
  | nil => exact (hne rfl).elim
  | cons _ _ => simp

theorem treeDist_comm {T : SimpleGraph ι} (hT : T.IsTree) (t₁ t₂ : ι) :
    treeDist hT t₁ t₂ = treeDist hT t₂ t₁ := by
  unfold treeDist
  rw [← eq_treePath hT (treePath hT t₁ t₂).reverse (treePath_isPath hT t₁ t₂).reverse,
    Walk.length_reverse]

theorem treeDist_eq_add_of_onTreePath {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ t : ι}
    (ht : OnTreePath T t₁ t₂ t) :
    treeDist hT t₁ t₂ = treeDist hT t₁ t + treeDist hT t t₂ := by
  rw [onTreePath_iff_exists_append hT] at ht
  obtain ⟨p, q, hp, hq, hpq⟩ := ht
  unfold treeDist
  rw [← eq_treePath hT p hp, ← eq_treePath hT q hq, ← eq_treePath hT (p.append q) hpq,
    Walk.length_append]

theorem treeDist_lt_right_of_onTreePath {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ t : ι}
    (ht : OnTreePath T t₁ t₂ t) (hne : t ≠ t₁) :
    treeDist hT t t₂ < treeDist hT t₁ t₂ := by
  rw [treeDist_eq_add_of_onTreePath hT ht]
  have := treeDist_pos_of_ne hT hne.symm
  omega

theorem treeDist_lt_left_of_onTreePath {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ t : ι}
    (ht : OnTreePath T t₁ t₂ t) (hne : t ≠ t₂) :
    treeDist hT t₁ t < treeDist hT t₁ t₂ := by
  rw [treeDist_eq_add_of_onTreePath hT ht]
  have := treeDist_pos_of_ne hT hne
  omega

theorem onTreePathEdge_of_onTreePath_right {T : SimpleGraph ι} (hT : T.IsTree)
    {t₁ t₂ t s s' : ι} (ht : OnTreePath T t₁ t₂ t) (he : OnTreePathEdge T t t₂ s s') :
    OnTreePathEdge T t₁ t₂ s s' := by
  rw [onTreePath_iff_exists_append hT] at ht
  obtain ⟨p, q, hp, hq, hpq⟩ := ht
  rw [onTreePathEdge_iff_mem_treePath hT] at he ⊢
  refine ⟨he.1, ?_⟩
  rw [← eq_treePath hT (p.append q) hpq, Walk.edges_append, List.mem_append]
  right
  rw [eq_treePath hT q hq]
  exact he.2

/-! ## Symmetries of `HasDisjointPaths` -/

theorem hasDisjointPaths_symm {K : SimpleGraph α} {Z₁ Z₂ : Set α} {k : ℕ}
    (h : HasDisjointPaths K Z₁ Z₂ k) : HasDisjointPaths K Z₂ Z₁ k := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun i ↦
    { first := (P i).last
      last := (P i).first
      walk := (P i).walk.reverse
      isPath := (P i).isPath.reverse
      first_mem := (P i).last_mem
      last_mem := (P i).first_mem }, fun i j hij ↦ ?_⟩
  simpa [Walk.support_reverse] using hP hij

theorem hasDisjointPaths_comm (K : SimpleGraph α) (Z₁ Z₂ : Set α) (k : ℕ) :
    HasDisjointPaths K Z₁ Z₂ k ↔ HasDisjointPaths K Z₂ Z₁ k :=
  ⟨hasDisjointPaths_symm, hasDisjointPaths_symm⟩

namespace TreeDecomp

variable [Fintype ι] {G : SimpleGraph α} {V₀ : Set α} (D : TreeDecomp G V₀ ι)

/-! ## Leanness condition (T4′) -/

/-- A quadruple `(t₁, t₂, Z₁, Z₂)` violates the leanness condition (T4′) of `D` at order `k`
(Bellenbaum and Diestel, Section 3, page 3). -/
structure ViolatesLean (t₁ t₂ : ι) (Z₁ Z₂ : Set α) (k : ℕ) : Prop where
  subset_left : Z₁ ⊆ D.bag t₁
  subset_right : Z₂ ⊆ D.bag t₂
  ncard_left : Z₁.ncard = k
  ncard_right : Z₂.ncard = k
  not_hasDisjointPaths : ¬ HasDisjointPaths G Z₁ Z₂ k
  le_inter_ncard : ∀ ⦃t t' : ι⦄, OnTreePathEdge D.T t₁ t₂ t t' → k ≤ (D.bag t ∩ D.bag t').ncard

/-- A tree-decomposition `D = (V_t)_{t ∈ T}` is *lean* if it satisfies condition (T4′) of
Bellenbaum and Diestel (Section 3, page 3): given `t₁, t₂ ∈ T` and vertex sets `Z₁ ⊆ V_{t₁}` and
`Z₂ ⊆ V_{t₂}` such that `|Z₁| = |Z₂| = k`, either `G` contains `k` disjoint `Z₁`–`Z₂` paths or
there exists an edge `t t' ∈ t₁ T t₂` with `|V_t ∩ V_{t'}| < k`. -/
def IsLean : Prop :=
  ∀ (t₁ t₂ : ι) (Z₁ Z₂ : Set α) (k : ℕ),
    Z₁ ⊆ D.bag t₁ → Z₂ ⊆ D.bag t₂ → Z₁.ncard = k → Z₂.ncard = k →
      HasDisjointPaths G Z₁ Z₂ k ∨
        ∃ t t', OnTreePathEdge D.T t₁ t₂ t t' ∧ (D.bag t ∩ D.bag t').ncard < k

theorem not_isLean_iff :
    ¬ D.IsLean ↔ ∃ t₁ t₂ Z₁ Z₂ k, D.ViolatesLean t₁ t₂ Z₁ Z₂ k := by
  unfold IsLean
  push Not
  constructor
  · rintro ⟨t₁, t₂, Z₁, Z₂, k, h1, h2, h3, h4, h5, h6⟩
    exact ⟨t₁, t₂, Z₁, Z₂, k, ⟨h1, h2, h3, h4, h5, h6⟩⟩
  · rintro ⟨t₁, t₂, Z₁, Z₂, k, ⟨h1, h2, h3, h4, h5, h6⟩⟩
    exact ⟨t₁, t₂, Z₁, Z₂, k, h1, h2, h3, h4, h5, h6⟩

theorem ViolatesLean.symm {t₁ t₂ : ι} {Z₁ Z₂ : Set α} {k : ℕ}
    (h : D.ViolatesLean t₁ t₂ Z₁ Z₂ k) : D.ViolatesLean t₂ t₁ Z₂ Z₁ k where
  subset_left := h.subset_right
  subset_right := h.subset_left
  ncard_left := h.ncard_right
  ncard_right := h.ncard_left
  not_hasDisjointPaths hp := h.not_hasDisjointPaths (hasDisjointPaths_symm hp)
  le_inter_ncard _ _ he := h.le_inter_ncard (onTreePathEdge_symm_endpoints he)

theorem le_bag_ncard_of_violatesLean (hV₀ : V₀.Finite) {t₁ t₂ t : ι} {Z₁ Z₂ : Set α} {k : ℕ}
    (hv : D.ViolatesLean t₁ t₂ Z₁ Z₂ k) (ht : OnTreePath D.T t₁ t₂ t) :
    k ≤ (D.bag t).ncard := by
  by_cases htt₂ : t = t₂
  · subst htt₂
    rw [← hv.ncard_right]
    exact Set.ncard_le_ncard hv.subset_right (D.bag_finite hV₀ t)
  · obtain ⟨s, s', he, rfl, _⟩ :=
      exists_onTreePathEdge_of_prop D.isTree (· = t) rfl (Ne.symm htt₂)
    have he' := onTreePathEdge_of_onTreePath_right D.isTree ht he
    exact (hv.le_inter_ncard he').trans
      (Set.ncard_le_ncard Set.inter_subset_left (D.bag_finite hV₀ s))

/-! ## Distance to `t₁ T t₂` and home nodes `t_x` -/

/-- The distance in `D.T` from `s` to the path `t₁ T t₂`:
$\min\{\, d_T(r, s) \mid r \in t_1 T t_2 \,\}$. -/
noncomputable def distToPath (t₁ t₂ s : ι) : ℕ :=
  open Classical in
  ((Finset.univ.filter fun r : ι ↦ OnTreePath D.T t₁ t₂ r).image
    (fun r ↦ treeDist D.isTree r s)).min'
    (Finset.Nonempty.image ⟨t₁, by simp [onTreePath_left]⟩ _)

theorem distToPath_le {t₁ t₂ r s : ι} (hr : OnTreePath D.T t₁ t₂ r) :
    D.distToPath t₁ t₂ s ≤ treeDist D.isTree r s := by
  classical
  unfold distToPath
  apply Finset.min'_le
  rw [Finset.mem_image]
  exact ⟨r, Finset.mem_filter.2 ⟨Finset.mem_univ r, hr⟩, rfl⟩

theorem exists_onTreePath_treeDist_eq (t₁ t₂ s : ι) :
    ∃ r, OnTreePath D.T t₁ t₂ r ∧ treeDist D.isTree r s = D.distToPath t₁ t₂ s := by
  classical
  have hmem := Finset.min'_mem
    ((Finset.univ.filter fun r : ι ↦ OnTreePath D.T t₁ t₂ r).image
      (fun r ↦ treeDist D.isTree r s))
    (Finset.Nonempty.image ⟨t₁, by simp [onTreePath_left]⟩ _)
  rw [Finset.mem_image] at hmem
  obtain ⟨r, hr, hdist⟩ := hmem
  rw [Finset.mem_filter] at hr
  exact ⟨r, hr.2, hdist⟩

theorem distToPath_comm (t₁ t₂ s : ι) :
    D.distToPath t₁ t₂ s = D.distToPath t₂ t₁ s := by
  apply le_antisymm
  · obtain ⟨r, hr, hreq⟩ := D.exists_onTreePath_treeDist_eq t₂ t₁ s
    rw [← hreq]
    exact D.distToPath_le (onTreePath_symm hr)
  · obtain ⟨r, hr, hreq⟩ := D.exists_onTreePath_treeDist_eq t₁ t₂ s
    rw [← hreq]
    exact D.distToPath_le (onTreePath_symm hr)

/-- If $t \in s T t_2$ and $t \notin \mathring{t}_1 T t_2$, then $t$ separates $s$ from the whole
path $t_1 T t_2$ in $T$, so if $t \ne s$ the distance of $t$ from $t_1 T t_2$ is strictly smaller
than that of $s$ (Bellenbaum and Diestel, proof of Claim (1), page 5). -/
theorem distToPath_lt_of_onTreePath_of_not_inner {t₁ t₂ s t : ι}
    (ht : OnTreePath D.T s t₂ t) (hnot : OnTreePath D.T t₁ t₂ t → t = t₁) (hne : t ≠ s) :
    D.distToPath t₁ t₂ t < D.distToPath t₁ t₂ s := by
  obtain ⟨r, hr, hreq⟩ := D.exists_onTreePath_treeDist_eq t₁ t₂ s
  have h_rst : OnTreePath D.T r s t := by
    rcases onTreePath_left_or_right D.isTree r ht with h | h
    · exact onTreePath_symm h
    · have ht_on : OnTreePath D.T t₁ t₂ t := onTreePath_trans_right D.isTree hr h
      have ht₁ : t = t₁ := hnot ht_on
      subst ht₁
      have hr' : OnTreePath D.T t₂ t r := onTreePath_symm hr
      have h' : OnTreePath D.T t₂ r t := onTreePath_symm h
      have hrt : r = t := onTreePath_antisymm D.isTree hr' h'
      subst hrt
      exact onTreePath_left D.T r s
  have hlt : treeDist D.isTree r t < treeDist D.isTree r s :=
    treeDist_lt_left_of_onTreePath D.isTree h_rst hne
  exact (D.distToPath_le hr).trans_lt (hreq ▸ hlt)

/-- $d_x := \min\{\, d_T(r, t_x) \mid r \in t_1 T t_2 \text{ and } x \in V_{t_x} \,\}$
(Bellenbaum and Diestel, proof of Theorem 3, page 3). -/
noncomputable def vertDist (t₁ t₂ : ι) (x : α) : ℕ :=
  open Classical in
  if h : (Finset.univ.filter fun s : ι ↦ x ∈ D.bag s).Nonempty then
    ((Finset.univ.filter fun s : ι ↦ x ∈ D.bag s).image (D.distToPath t₁ t₂)).min' (h.image _)
  else 0

theorem vertDist_le {t₁ t₂ s : ι} {x : α} (hx : x ∈ D.bag s) :
    D.vertDist t₁ t₂ x ≤ D.distToPath t₁ t₂ s := by
  classical
  have hs : s ∈ Finset.univ.filter (fun s : ι ↦ x ∈ D.bag s) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ s, hx⟩
  have hne : (Finset.univ.filter fun s : ι ↦ x ∈ D.bag s).Nonempty := ⟨s, hs⟩
  unfold vertDist
  rw [dite_eq_left hne]
  apply Finset.min'_le
  exact Finset.mem_image.2 ⟨s, hs, rfl⟩

theorem exists_mem_bag_distToPath_eq (t₁ t₂ : ι) {x : α} (hx : x ∈ V₀) :
    ∃ s : ι, x ∈ D.bag s ∧ D.distToPath t₁ t₂ s = D.vertDist t₁ t₂ x := by
  classical
  obtain ⟨s₀, hs₀⟩ := D.exists_mem_bag hx
  have hne : (Finset.univ.filter fun s : ι ↦ x ∈ D.bag s).Nonempty :=
    ⟨s₀, Finset.mem_filter.2 ⟨Finset.mem_univ s₀, hs₀⟩⟩
  have hmem := Finset.min'_mem
    ((Finset.univ.filter fun s : ι ↦ x ∈ D.bag s).image (D.distToPath t₁ t₂)) (hne.image _)
  rw [Finset.mem_image] at hmem
  obtain ⟨s, hs, hdist⟩ := hmem
  rw [Finset.mem_filter] at hs
  refine ⟨s, hs.2, ?_⟩
  unfold vertDist
  rw [dite_eq_left hne]
  exact hdist

theorem vertDist_comm (t₁ t₂ : ι) (x : α) :
    D.vertDist t₁ t₂ x = D.vertDist t₂ t₁ x := by
  have h : D.distToPath t₁ t₂ = D.distToPath t₂ t₁ := funext (D.distToPath_comm t₁ t₂)
  unfold vertDist
  simp_rw [h]

/-- Choice of 'home' node $t_x \in T$ at minimum distance from $t_1 T t_2$ in $T$ such that
$x \in V_{t_x}$ (Bellenbaum and Diestel, proof of Theorem 3, page 3). -/
noncomputable def chooseHome (t₁ t₂ : ι) (x : α) : ι :=
  open Classical in
  if hx : x ∈ V₀ then (D.exists_mem_bag_distToPath_eq t₁ t₂ hx).choose else t₁

theorem chooseHome_mem_bag (t₁ t₂ : ι) {x : α} (hx : x ∈ V₀) :
    x ∈ D.bag (D.chooseHome t₁ t₂ x) := by
  classical
  unfold chooseHome
  rw [dite_eq_left hx]
  exact (D.exists_mem_bag_distToPath_eq t₁ t₂ hx).choose_spec.1

theorem distToPath_chooseHome (t₁ t₂ : ι) {x : α} (hx : x ∈ V₀) :
    D.distToPath t₁ t₂ (D.chooseHome t₁ t₂ x) = D.vertDist t₁ t₂ x := by
  classical
  unfold chooseHome
  rw [dite_eq_left hx]
  exact (D.exists_mem_bag_distToPath_eq t₁ t₂ hx).choose_spec.2

/-- $\sum_{x \in X} d_x$ for a vertex set $X \subseteq V_0$ (Bellenbaum and Diestel, page 3). -/
noncomputable def sepDistSum (hV₀ : V₀.Finite) (t₁ t₂ : ι) (X : Set α) : ℕ :=
  open Classical in
  ∑ x ∈ hV₀.toFinset.filter (· ∈ X), D.vertDist t₁ t₂ x

theorem sepDistSum_comm (hV₀ : V₀.Finite) (t₁ t₂ : ι) (X : Set α) :
    D.sepDistSum hV₀ t₁ t₂ X = D.sepDistSum hV₀ t₂ t₁ X := by
  have h : D.vertDist t₁ t₂ = D.vertDist t₂ t₁ := funext (D.vertDist_comm t₁ t₂)
  unfold sepDistSum
  rw [h]

/-! ## Claim ($\ast$), Claim (1), and Claim (2) of Theorem 3 -/

/-- **Claim ($\ast$)** in the proof of Theorem 3 of Bellenbaum and Diestel (Section 3, page 4):
For $Y := W_t^1 \setminus V_t$, we have
$$Y = \{\, x \in X \mid t \in t_x T t_2 \,\} \setminus V_t,$$
$V_t \setminus W_t^1 = V_t \cap C_2$, and if $|W_t^1| = |V_t|$ then $|Y| = |V_t \cap C_2|$. -/
theorem theorem_3_star (hV₀ : V₀.Finite) {X C₁ C₂ : Set α}
    (hX : X ⊆ V₀) (hcov : V₀ ⊆ C₁ ∪ C₂ ∪ X)
    (hdisj : Disjoint C₁ C₂) (hdisj₂ : Disjoint C₂ X)
    (home : α → ι) (t₂ t : ι) :
    D.shiftBag X C₁ home t₂ t \ D.bag t =
      {x ∈ X | OnTreePath D.T (home x) t₂ t} \ D.bag t ∧
    D.bag t \ D.shiftBag X C₁ home t₂ t = D.bag t ∩ C₂ ∧
    ((D.shiftBag X C₁ home t₂ t).ncard = (D.bag t).ncard →
      (D.shiftBag X C₁ home t₂ t \ D.bag t).ncard = (D.bag t ∩ C₂).ncard) := by
  have h1 := D.shiftBag_inter_compl_eq X C₁ home t₂ t
  have h2 : D.bag t \ D.shiftBag X C₁ home t₂ t = D.bag t ∩ C₂ := by
    ext x
    simp only [Set.mem_sdiff, mem_shiftBag, Set.mem_inter_iff]
    constructor
    · rintro ⟨hxt, hnot⟩
      refine ⟨hxt, ?_⟩
      rcases hcov (D.bag_subset t hxt) with (hC1 | hC2) | hX'
      · exact (hnot (Or.inl ⟨hxt, Or.inl hC1⟩)).elim
      · exact hC2
      · exact (hnot (Or.inl ⟨hxt, Or.inr hX'⟩)).elim
    · rintro ⟨hxt, hxC₂⟩
      refine ⟨hxt, ?_⟩
      rintro (⟨_, hxC₁ | hxX⟩ | ⟨hxX, _⟩)
      · exact Set.disjoint_left.1 hdisj hxC₁ hxC₂
      · exact Set.disjoint_left.1 hdisj₂ hxC₂ hxX
      · exact Set.disjoint_left.1 hdisj₂ hxC₂ hxX
  refine ⟨h1, h2, fun hcard ↦ ?_⟩
  rw [← h2]
  have hW_fin := D.shiftBag_finite hV₀ (C := C₁) hX home t₂ t
  have hV_fin := D.bag_finite hV₀ t
  apply le_antisymm
  · exact (Set.ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff hW_fin hV_fin).1 hcard.le
  · exact (Set.ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff hV_fin hW_fin).1 hcard.ge

/-- Separation step in the proof of **Claim (1)** of Theorem 3 (Bellenbaum and Diestel, page 4):
For $Y := W_t^1 \setminus V_t$ and $X' := (X \setminus Y) \cup (V_t \cap C_2)$, the set $X'$
separates both $Z_1$ and $V_t$ from $Z_2$ in $(G, V_0)$. -/
theorem theorem_3_claim_1_separates {X C₁ C₂ Z₁ Z₂ : Set α}
    (hX : X ⊆ V₀) (hC₂ : C₂ ⊆ V₀) (hcov : V₀ ⊆ C₁ ∪ C₂ ∪ X)
    (hdisj : Disjoint C₁ C₂) (hdisj₂ : Disjoint C₂ X)
    (hno_adj : ∀ ⦃a b : α⦄, a ∈ C₁ → b ∈ C₂ → ¬ G.Adj a b)
    (hZ₁C : Z₁ ⊆ C₁ ∪ X) (hZ₂C : Z₂ ⊆ C₂ ∪ X)
    {t₂ t : ι} (hZ₂_bag : Z₂ ⊆ D.bag t₂)
    {home : α → ι} (hhome : ∀ x ∈ X, x ∈ D.bag (home x)) :
    let Y := D.shiftBag X C₁ home t₂ t \ D.bag t
    let X' := (X \ Y) ∪ (D.bag t ∩ C₂)
    Separates G V₀ Z₁ Z₂ X' ∧ Separates G V₀ (D.bag t) Z₂ X' := by
  intro Y X'
  have hX'_sub : X' ⊆ V₀ :=
    Set.union_subset (Set.sdiff_subset.trans hX) (Set.inter_subset_right.trans hC₂)
  have hwalk_C₂ : ∀ {a v : α} (q : G.Walk a v), v ∈ Z₂ →
      (∀ z ∈ q.support, z ∈ V₀) → (∀ z ∈ q.support, z ∉ X') →
      ∀ z ∈ q.support, z ∈ C₂ := by
    intro a v q hv hqV hqX'
    induction q with
    | nil =>
      intro z hz
      simp only [Walk.support_nil, List.mem_singleton] at hz
      subst hz
      rcases hZ₂C hv with haC₂ | haX
      · exact haC₂
      · exfalso
        have ha_not_X' : z ∉ X' := hqX' z (by simp)
        have haY : z ∈ Y := by
          by_contra haY
          exact ha_not_X' (Or.inl ⟨haX, haY⟩)
        have ha_not_bag : z ∉ D.bag t := haY.2
        change z ∈ D.shiftBag X C₁ home t₂ t \ D.bag t at haY
        rw [D.shiftBag_inter_compl_eq] at haY
        have ha_path : OnTreePath D.T (home z) t₂ t := haY.1.2
        exact ha_not_bag (D.mem_bag_of_onTreePath ha_path (hhome z haX) (hZ₂_bag hv))
    | @cons a b v hadj r ih =>
      have hrC₂ : ∀ z ∈ r.support, z ∈ C₂ :=
        ih hv (fun z hz ↦ hqV z (List.mem_cons_of_mem _ hz))
          (fun z hz ↦ hqX' z (List.mem_cons_of_mem _ hz))
      have hbC₂ : b ∈ C₂ := hrC₂ b r.start_mem_support
      have haC₂ : a ∈ C₂ := by
        by_contra ha_not_C₂
        have haV : a ∈ V₀ := hqV a (List.Mem.head _)
        have haX : a ∈ X := by
          rcases hcov haV with (haC₁ | haC₂) | haX
          · exact (hno_adj haC₁ hbC₂ hadj).elim
          · exact (ha_not_C₂ haC₂).elim
          · exact haX
        have ha_not_X' : a ∉ X' := hqX' a (List.Mem.head _)
        have haY : a ∈ Y := by
          by_contra haY
          exact ha_not_X' (Or.inl ⟨haX, haY⟩)
        have ha_not_bag : a ∉ D.bag t := haY.2
        have ha_path : OnTreePath D.T (home a) t₂ t := by
          change a ∈ D.shiftBag X C₁ home t₂ t \ D.bag t at haY
          rw [D.shiftBag_inter_compl_eq] at haY
          exact haY.1.2
        obtain ⟨z, hz_supp, hz_bag⟩ :=
          D.lemma_1_vertex ha_path (hhome a haX) (hZ₂_bag hv) (Walk.cons hadj r) hqV
        simp only [Walk.support_cons, List.mem_cons] at hz_supp
        rcases hz_supp with rfl | hz_r
        · exact ha_not_bag hz_bag
        · exact hqX' z (List.mem_cons_of_mem _ hz_r) (Or.inr ⟨hz_bag, hrC₂ z hz_r⟩)
      intro z hz
      simp only [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact haC₂
      · exact hrC₂ z hz
  refine ⟨⟨hX'_sub, fun u v hu hv p hp ↦ ?_⟩, ⟨hX'_sub, fun u v hu hv p hp ↦ ?_⟩⟩
  · by_contra! hno
    have huC₂ : u ∈ C₂ := hwalk_C₂ p hv hp hno u p.start_mem_support
    rcases hZ₁C hu with huC₁ | huX
    · exact Set.disjoint_left.1 hdisj huC₁ huC₂
    · exact Set.disjoint_left.1 hdisj₂ huC₂ huX
  · by_contra! hno
    have huC₂ : u ∈ C₂ := hwalk_C₂ p hv hp hno u p.start_mem_support
    exact hno u p.start_mem_support (Or.inr ⟨hu, huC₂⟩)

/-- **Claim (1)** in the proof of Theorem 3 of Bellenbaum and Diestel (Section 3, pages 4–5),
for $i = 1$: if $|W_t^1| = |V_t|$, then $W_t^2 \subseteq X$. -/
theorem theorem_3_claim_1_left (hV₀ : V₀.Finite)
    (hG : ∀ ⦃u v : α⦄, G.Adj u v → u ∈ V₀ ∧ v ∈ V₀)
    {t₁ t₂ : ι} {Z₁ Z₂ : Set α} {k : ℕ}
    (hv : D.ViolatesLean t₁ t₂ Z₁ Z₂ k)
    (hmin_dist : ∀ t₁' t₂' Z₁' Z₂' k', D.ViolatesLean t₁' t₂' Z₁' Z₂' k' →
      treeDist D.isTree t₁ t₂ ≤ treeDist D.isTree t₁' t₂')
    {X C₁ C₂ : Set α}
    (hX : X ⊆ V₀) (hC₂ : C₂ ⊆ V₀)
    (hcov : V₀ ⊆ C₁ ∪ C₂ ∪ X)
    (hdisj : Disjoint C₁ C₂) (hdisj₂ : Disjoint C₂ X)
    (hno_adj : ∀ ⦃a b : α⦄, a ∈ C₁ → b ∈ C₂ → ¬ G.Adj a b)
    (hZ₁C : Z₁ ⊆ C₁ ∪ X) (hZ₂C : Z₂ ⊆ C₂ ∪ X)
    (hX_lt : X.ncard < k)
    (hmin_sep : ∀ X', Separates G V₀ Z₁ Z₂ X' → X'.ncard ≤ X.ncard →
      D.sepDistSum hV₀ t₁ t₂ X ≤ D.sepDistSum hV₀ t₁ t₂ X')
    {home : α → ι} (hhome : ∀ x ∈ V₀, x ∈ D.bag (home x))
    (hhome_dist : ∀ x ∈ V₀, D.distToPath t₁ t₂ (home x) = D.vertDist t₁ t₂ x)
    (t : ι) (hcard : (D.shiftBag X C₁ home t₂ t).ncard = (D.bag t).ncard) :
    D.shiftBag X C₂ home t₁ t ⊆ X := by
  classical
  have hstar := D.theorem_3_star hV₀ hX hcov hdisj hdisj₂ home t₂ t
  let Y := D.shiftBag X C₁ home t₂ t \ D.bag t
  let X' := (X \ Y) ∪ (D.bag t ∩ C₂)
  have hY_sub_X : Y ⊆ X := by
    change D.shiftBag X C₁ home t₂ t \ D.bag t ⊆ X
    rw [hstar.1]
    exact fun _ h ↦ h.1.1
  have hY_ncard : Y.ncard = (D.bag t ∩ C₂).ncard := hstar.2.2 hcard
  suffices hbag_C₂ : D.bag t ∩ C₂ = ∅ by
    rintro x (⟨hxt, hxC₂ | hxX⟩ | ⟨hxX, _⟩)
    · exfalso
      have : x ∈ D.bag t ∩ C₂ := ⟨hxt, hxC₂⟩
      rw [hbag_C₂] at this
      exact this
    · exact hxX
    · exact hxX
  by_contra hne_C₂
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.2 hne_C₂
  have ⟨hsep_Z₁, hsep_Vt⟩ :=
    D.theorem_3_claim_1_separates hX hC₂ hcov hdisj hdisj₂ hno_adj hZ₁C hZ₂C hv.subset_right
      (fun x hx ↦ hhome x (hX hx)) (t := t)
  have hX'_ncard : X'.ncard = X.ncard := by
    have hdisj_X'_parts : Disjoint (X \ Y) (D.bag t ∩ C₂) :=
      Disjoint.mono_left Set.sdiff_subset (Disjoint.mono_right Set.inter_subset_right hdisj₂.symm)
    rw [Set.ncard_union_eq hdisj_X'_parts ((hV₀.subset hX).sdiff)
      ((D.bag_finite hV₀ t).subset Set.inter_subset_left),
      ← hY_ncard, Set.ncard_sdiff_add_ncard_of_subset hY_sub_X (hV₀.subset hX)]
  have hnot_inner : OnTreePath D.T t₁ t₂ t → t = t₁ := by
    intro ht_on
    by_contra htt₁
    have hk_le : k ≤ (D.bag t).ncard := D.le_bag_ncard_of_violatesLean hV₀ hv ht_on
    obtain ⟨Z, hZ_sub, hZ_card⟩ := Set.exists_subset_card_eq hk_le
    have hv' : D.ViolatesLean t t₂ Z Z₂ k :=
      { subset_left := hZ_sub
        subset_right := hv.subset_right
        ncard_left := hZ_card
        ncard_right := hv.ncard_right
        not_hasDisjointPaths := fun hpaths ↦ by
          have hsep_Z : Separates G V₀ Z Z₂ X' :=
            ⟨hsep_Vt.1, fun u v hu hv p hp ↦ hsep_Vt.2 (hZ_sub hu) hv p hp⟩
          have hle := ncard_le_of_hasDisjointPaths_of_separates hV₀
            (hZ_sub.trans (D.bag_subset t)) hG hpaths hsep_Z
          omega
        le_inter_ncard := fun s s' he ↦
          hv.le_inter_ncard (onTreePathEdge_of_onTreePath_right D.isTree ht_on he) }
    have hlt := treeDist_lt_right_of_onTreePath D.isTree ht_on htt₁
    have hle := hmin_dist t t₂ Z Z₂ k hv'
    omega
  -- Now t ∉ tRing₁ T t₂; show sepDistSum X' < sepDistSum X
  let FX := hV₀.toFinset.filter (· ∈ X)
  let FY := hV₀.toFinset.filter (· ∈ Y)
  let FB := hV₀.toFinset.filter (· ∈ D.bag t ∩ C₂)
  let FX' := hV₀.toFinset.filter (· ∈ X')
  have hFY_sub_FX : FY ⊆ FX := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hY_sub_X hx.2⟩
  have hFX'_eq : FX' = (FX \ FY) ∪ FB := by
    ext x
    simp only [FX', FX, FY, FB, X', Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_union,
      Finset.mem_sdiff, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hxV, ⟨hxX, hxY⟩ | ⟨hxt, hxC₂⟩⟩
      · exact Or.inl ⟨⟨hxV, hxX⟩, fun h ↦ hxY h.2⟩
      · exact Or.inr ⟨hxV, hxt, hxC₂⟩
    · rintro (⟨⟨hxV, hxX⟩, hxY⟩ | ⟨hxV, hxt, hxC₂⟩)
      · exact ⟨hxV, Or.inl ⟨hxX, fun h ↦ hxY ⟨hxV, h⟩⟩⟩
      · exact ⟨hxV, Or.inr ⟨hxt, hxC₂⟩⟩
  have hdisj_FX_FB : Disjoint (FX \ FY) FB := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_sdiff, Finset.mem_filter] at hx1
    rw [Finset.mem_filter] at hx2
    exact Set.disjoint_left.1 hdisj₂ hx2.2.2 hx1.1.2
  have hFY_card : FY.card = Y.ncard := by
    rw [Set.ncard_eq_toFinset_card Y (hV₀.subset (hY_sub_X.trans hX))]
    congr 1
    ext x
    simp only [FY, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hX (hY_sub_X h), h⟩⟩
  have hFB_card : FB.card = (D.bag t ∩ C₂).ncard := by
    rw [Set.ncard_eq_toFinset_card (D.bag t ∩ C₂)
      (hV₀.subset (Set.inter_subset_right.trans hC₂))]
    congr 1
    ext x
    simp only [FB, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hC₂ h.2, h⟩⟩
  have hFB_pos : 0 < FB.card := by
    rw [Finset.card_pos]
    exact ⟨x₀, Finset.mem_filter.2 ⟨hV₀.mem_toFinset.2 (hC₂ hx₀.2), hx₀⟩⟩
  have hsum_FB : ∑ x' ∈ FB, D.vertDist t₁ t₂ x' ≤ FB.card * D.distToPath t₁ t₂ t := by
    rw [← smul_eq_mul]
    refine Finset.sum_le_card_nsmul FB (D.vertDist t₁ t₂) (D.distToPath t₁ t₂ t) ?_
    intro x' hx'
    rw [Finset.mem_filter] at hx'
    exact D.vertDist_le hx'.2.1
  have hsum_FY : FY.card * (D.distToPath t₁ t₂ t + 1) ≤ ∑ y ∈ FY, D.vertDist t₁ t₂ y := by
    rw [← smul_eq_mul]
    refine Finset.card_nsmul_le_sum FY (D.vertDist t₁ t₂) (D.distToPath t₁ t₂ t + 1) ?_
    intro y hy
    rw [Finset.mem_filter] at hy
    have hyY : y ∈ D.shiftBag X C₁ home t₂ t \ D.bag t := hy.2
    rw [hstar.1] at hyY
    have hyX : y ∈ X := hyY.1.1
    have hy_path : OnTreePath D.T (home y) t₂ t := hyY.1.2
    have hy_not_bag : y ∉ D.bag t := hyY.2
    have hne_ty : t ≠ home y := fun h ↦ hy_not_bag (h ▸ hhome y (hX hyX))
    have hlt := D.distToPath_lt_of_onTreePath_of_not_inner hy_path hnot_inner hne_ty
    rw [hhome_dist y (hX hyX)] at hlt
    omega
  have hsum_X' : D.sepDistSum hV₀ t₁ t₂ X' =
      (∑ x ∈ FX \ FY, D.vertDist t₁ t₂ x) + ∑ x' ∈ FB, D.vertDist t₁ t₂ x' := by
    rw [← Finset.sum_union hdisj_FX_FB, ← hFX'_eq]
    unfold sepDistSum
    congr 1
    ext x
    simp [FX']
  have hsum_X : D.sepDistSum hV₀ t₁ t₂ X =
      (∑ x ∈ FX \ FY, D.vertDist t₁ t₂ x) + ∑ y ∈ FY, D.vertDist t₁ t₂ y := by
    rw [Finset.sum_sdiff hFY_sub_FX]
    unfold sepDistSum
    congr 1
  have hcard_FY_FB : FY.card = FB.card := by rw [hFY_card, hFB_card, hY_ncard]
  rw [hcard_FY_FB, Nat.mul_add, Nat.mul_one] at hsum_FY
  have h_le_min := hmin_sep X' hsep_Z₁ (le_of_eq hX'_ncard)
  omega

/-- **Claim (1)** in the proof of Theorem 3 of Bellenbaum and Diestel (Section 3, page 4),
in both directions ($i = 1$ and $i = 2$):
$$(\forall t \in T)(\forall i = 1, 2)\ \bigl(|W_t^i| = |V_t| \Rightarrow W_t^{3-i} \subseteq
X\bigr).$$ -/
theorem theorem_3_claim_1 (hV₀ : V₀.Finite)
    (hG : ∀ ⦃u v : α⦄, G.Adj u v → u ∈ V₀ ∧ v ∈ V₀)
    {t₁ t₂ : ι} {Z₁ Z₂ : Set α} {k : ℕ}
    (hv : D.ViolatesLean t₁ t₂ Z₁ Z₂ k)
    (hmin_dist : ∀ t₁' t₂' Z₁' Z₂' k', D.ViolatesLean t₁' t₂' Z₁' Z₂' k' →
      treeDist D.isTree t₁ t₂ ≤ treeDist D.isTree t₁' t₂')
    {X C₁ C₂ : Set α}
    (hX : X ⊆ V₀) (hC₁ : C₁ ⊆ V₀) (hC₂ : C₂ ⊆ V₀)
    (hcov : V₀ ⊆ C₁ ∪ C₂ ∪ X)
    (hdisj : Disjoint C₁ C₂) (hdisj₁ : Disjoint C₁ X) (hdisj₂ : Disjoint C₂ X)
    (hno_adj : ∀ ⦃a b : α⦄, a ∈ C₁ → b ∈ C₂ → ¬ G.Adj a b)
    (hZ₁C : Z₁ ⊆ C₁ ∪ X) (hZ₂C : Z₂ ⊆ C₂ ∪ X)
    (hX_lt : X.ncard < k)
    (hmin_sep : ∀ X', Separates G V₀ Z₁ Z₂ X' → X'.ncard ≤ X.ncard →
      D.sepDistSum hV₀ t₁ t₂ X ≤ D.sepDistSum hV₀ t₁ t₂ X')
    {home : α → ι} (hhome : ∀ x ∈ V₀, x ∈ D.bag (home x))
    (hhome_dist : ∀ x ∈ V₀, D.distToPath t₁ t₂ (home x) = D.vertDist t₁ t₂ x)
    (t : ι) :
    ((D.shiftBag X C₁ home t₂ t).ncard = (D.bag t).ncard → D.shiftBag X C₂ home t₁ t ⊆ X) ∧
    ((D.shiftBag X C₂ home t₁ t).ncard = (D.bag t).ncard → D.shiftBag X C₁ home t₂ t ⊆ X) := by
  refine ⟨D.theorem_3_claim_1_left hV₀ hG hv hmin_dist hX hC₂ hcov hdisj hdisj₂
      hno_adj hZ₁C hZ₂C hX_lt hmin_sep hhome hhome_dist t, ?_⟩
  have hcov' : V₀ ⊆ C₂ ∪ C₁ ∪ X := by
    intro x hx
    rcases hcov hx with (h1 | h2) | h3
    · exact Or.inl (Or.inr h1)
    · exact Or.inl (Or.inl h2)
    · exact Or.inr h3
  have hno_adj' : ∀ ⦃a b : α⦄, a ∈ C₂ → b ∈ C₁ → ¬ G.Adj a b :=
    fun a b ha hb hadj ↦ hno_adj hb ha hadj.symm
  have hmin_dist' : ∀ t₁' t₂' Z₁' Z₂' k', D.ViolatesLean t₁' t₂' Z₁' Z₂' k' →
      treeDist D.isTree t₂ t₁ ≤ treeDist D.isTree t₁' t₂' := by
    intro t₁' t₂' Z₁' Z₂' k' hv'
    rw [treeDist_comm D.isTree t₂ t₁]
    exact hmin_dist t₁' t₂' Z₁' Z₂' k' hv'
  have hmin_sep' : ∀ X', Separates G V₀ Z₂ Z₁ X' → X'.ncard ≤ X.ncard →
      D.sepDistSum hV₀ t₂ t₁ X ≤ D.sepDistSum hV₀ t₂ t₁ X' := by
    intro X' hsep' hcard'
    rw [sepDistSum_comm D hV₀ t₂ t₁ X, sepDistSum_comm D hV₀ t₂ t₁ X']
    exact hmin_sep X' (separates_symm hsep') hcard'
  have hhome_dist' : ∀ x ∈ V₀, D.distToPath t₂ t₁ (home x) = D.vertDist t₂ t₁ x := by
    intro x hx
    rw [distToPath_comm D t₂ t₁, vertDist_comm D t₂ t₁]
    exact hhome_dist x hx
  exact D.theorem_3_claim_1_left hV₀ hG hv.symm hmin_dist' hX hC₁ hcov' hdisj.symm
    hdisj₁ hno_adj' hZ₂C hZ₁C hX_lt hmin_sep' hhome hhome_dist' t

/-- **Claim (2)** in the proof of Theorem 3 of Bellenbaum and Diestel (Section 3, page 5):
$$(\exists t \in t_1 T t_2)\ \bigl(|W_t^1| < |V_t| \land |W_t^2| < |V_t|\bigr).$$ -/
theorem theorem_3_claim_2 (hV₀ : V₀.Finite)
    {t₁ t₂ : ι} {Z₁ Z₂ : Set α} {k : ℕ}
    (hv : D.ViolatesLean t₁ t₂ Z₁ Z₂ k)
    {X C₁ C₂ : Set α}
    (hX : X ⊆ V₀) (hcov : V₀ ⊆ C₁ ∪ C₂ ∪ X)
    (hdisj₁ : Disjoint C₁ X) (hdisj₂ : Disjoint C₂ X)
    (hZ₁C : Z₁ ⊆ C₁ ∪ X) (hZ₂C : Z₂ ⊆ C₂ ∪ X)
    (hX_lt : X.ncard < k)
    {home : α → ι}
    (hclaim₁ : ∀ t : ι,
      ((D.shiftBag X C₁ home t₂ t).ncard = (D.bag t).ncard → D.shiftBag X C₂ home t₁ t ⊆ X) ∧
      ((D.shiftBag X C₂ home t₁ t).ncard = (D.bag t).ncard → D.shiftBag X C₁ home t₂ t ⊆ X))
    (hle₁ : ∀ t : ι, (D.shiftBag X C₁ home t₂ t).ncard ≤ (D.bag t).ncard)
    (hle₂ : ∀ t : ι, (D.shiftBag X C₂ home t₁ t).ncard ≤ (D.bag t).ncard) :
    ∃ t : ι, OnTreePath D.T t₁ t₂ t ∧
      (D.shiftBag X C₁ home t₂ t).ncard < (D.bag t).ncard ∧
      (D.shiftBag X C₂ home t₁ t).ncard < (D.bag t).ncard := by
  -- First show that V_{t₁} meets C₁ and V_{t₂} meets C₂
  have ht₁_C₁ : (D.bag t₁ ∩ C₁).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hZ₁_sub_X : Z₁ ⊆ X := by
      intro z hz
      rcases hZ₁C hz with hzC₁ | hzX
      · exfalso
        have : z ∈ D.bag t₁ ∩ C₁ := ⟨hv.subset_left hz, hzC₁⟩
        rw [h] at this
        exact this
      · exact hzX
    have := Set.ncard_le_ncard hZ₁_sub_X (hV₀.subset hX)
    rw [hv.ncard_left] at this
    omega
  have ht₂_C₂ : (D.bag t₂ ∩ C₂).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hZ₂_sub_X : Z₂ ⊆ X := by
      intro z hz
      rcases hZ₂C hz with hzC₂ | hzX
      · exfalso
        have : z ∈ D.bag t₂ ∩ C₂ := ⟨hv.subset_right hz, hzC₂⟩
        rw [h] at this
        exact this
      · exact hzX
    have := Set.ncard_le_ncard hZ₂_sub_X (hV₀.subset hX)
    rw [hv.ncard_right] at this
    omega
  -- Find t ∈ t₁ T t₂ such that V_t meets both C₁ and C₂
  have hex_cross : ∃ t, OnTreePath D.T t₁ t₂ t ∧
      (D.bag t ∩ C₁).Nonempty ∧ (D.bag t ∩ C₂).Nonempty := by
    by_contra hno
    have hnot_t₂ : ¬ (D.bag t₂ ∩ C₁).Nonempty :=
      fun h ↦ hno ⟨t₂, onTreePath_right D.T t₁ t₂, h, ht₂_C₂⟩
    obtain ⟨t, t', he, ht_C₁, ht'_not_C₁⟩ :=
      exists_onTreePathEdge_of_prop D.isTree (fun s ↦ (D.bag s ∩ C₁).Nonempty) ht₁_C₁ hnot_t₂
    have ht_not_C₂ : ¬ (D.bag t ∩ C₂).Nonempty :=
      fun h ↦ hno ⟨t, he.onTreePath_left, ht_C₁, h⟩
    have hinter_sub_X : D.bag t ∩ D.bag t' ⊆ X := by
      rintro x ⟨hxt, hxt'⟩
      rcases hcov (D.bag_subset t hxt) with (hxC₁ | hxC₂) | hxX
      · exact (ht'_not_C₁ ⟨x, hxt', hxC₁⟩).elim
      · exact (ht_not_C₂ ⟨x, hxt, hxC₂⟩).elim
      · exact hxX
    have hcard_le := Set.ncard_le_ncard hinter_sub_X (hV₀.subset hX)
    have hk_le := hv.le_inter_ncard he
    omega
  obtain ⟨t, ht_on, ⟨c₁, htc₁, hc₁⟩, ⟨c₂, htc₂, hc₂⟩⟩ := hex_cross
  refine ⟨t, ht_on, ?_, ?_⟩
  · apply lt_of_le_of_ne (hle₁ t)
    intro heq
    have hsub := (hclaim₁ t).1 heq
    have hc₂_W₂ : c₂ ∈ D.shiftBag X C₂ home t₁ t := Or.inl ⟨htc₂, Or.inl hc₂⟩
    exact Set.disjoint_left.1 hdisj₂ hc₂ (hsub hc₂_W₂)
  · apply lt_of_le_of_ne (hle₂ t)
    intro heq
    have hsub := (hclaim₁ t).2 heq
    have hc₁_W₁ : c₁ ∈ D.shiftBag X C₁ home t₂ t := Or.inl ⟨htc₁, Or.inl hc₁⟩
    exact Set.disjoint_left.1 hdisj₁ hc₁ (hsub hc₁_W₁)

end TreeDecomp

end GraphMinor.Thomas
