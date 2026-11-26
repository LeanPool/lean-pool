/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.TreeLemma.Lemma21

/-!
# The main tree lemma: Graph Minors IV, (2.2)

This file formalizes Graph Minors IV, (2.2) (pages 232–233), proved by induction on `n` from (2.1):

* Base case `n = 0` (`lemma_2_2_zero`): when `φᵢ(e) = 0` for every edge `e`, `v` precedes `w`
  whenever `v ≠ o(Tᵢ)` reaches `w`, so (2.2) reduces directly to (2.1).
* Inductive step `n + 1`: for each `i`, let `Fᵢ = {e ∈ E(Tᵢ) : φᵢ(e) = 0}` and let `Sᵢ` be the
  contraction of `Tᵢ` onto `Fᵢ` (`RootedTree.exists_isContraction`).
  - Claim (1) (`lemma_2_2_claim_1`): the contractions `Sᵢ` and `M` satisfy the adjacency hypothesis
    of (2.1).
  - Claim (2) (`lemma_2_2_claim_2`): applying (2.1) to `S₁, S₂, …` yields an increasing sequence
    `z₁, z₂, …` of `M`-independent vertices, each the root of a component `R_j` of some
    `Tᵢ \ Fᵢ`, such that the set `A` of heads of edges in `⋃ᵢ Fᵢ` with tails in `⋃_j V(R_j)` is
    `M`-rich.
  - Claim (3) (`lemma_2_2_claim_3`): applying the induction hypothesis to `R₁, R₂, …` with
    `φ'_j(e) = φᵢ(e) - 1` yields an infinite `M`-stable set `X ⊆ ⋃_j V(R_j)` meeting each `V(Tᵢ)` in
    at most one vertex such that the set `B` of heads of edges of `⋃_j R_j` with tails in `X` is
    `M`-rich.
  - Final step: every edge of `⋃ᵢ Tᵢ` with tail in `X` has head in `A ∪ B`, so the set `C` of such
    heads is `M`-rich.
-/

public section

namespace GraphMinor.GM04

variable {ι : Type*}

/-- Base case `n = 0` of Graph Minors IV, (2.2) (page 232). -/
theorem lemma_2_2_zero (T : ℕ → RootedTree ι) (φ : ℕ → ι → ℕ) (M : SimpleGraph ι)
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    (hφ : ∀ i, ∀ f ∈ (T i).edges, φ i f ≤ 0)
    (hM : ∀ i i', i < i' → ∀ u ∈ (T i).verts, ∀ w ∈ (T i').verts, ∀ v,
      M.Adj u w → (T i').Precedes (φ i') v w → M.Adj u v)
    (hroot : M.IsIndepSet (Set.range fun i ↦ (T i).root)) :
    ∃ X : Set ι, X.Infinite ∧ M.IsIndepSet X ∧ X ⊆ ⋃ i, ((T i).verts : Set ι) ∧
      (∀ i, (X ∩ (T i).verts).Subsingleton) ∧
      IsRich M {v | ∃ i, v ∈ (T i).edges ∧ (T i).parent v ∈ X} := by
  refine lemma_2_1 T M hdisj (fun i i' hii' u hu w hw v hadj hvr hvw ↦ ?_) hroot
  have hve : v ∈ (T i').edges := (T i').mem_edges.2 ⟨hvr, hvw.verts_left (T i')⟩
  have hwr : w ≠ (T i').root := by
    rintro rfl
    exact hvr (((T i').reaches_root_iff).1 hvw)
  have hwe : w ∈ (T i').edges := (T i').mem_edges.2 ⟨hwr, hw⟩
  have hv0 : φ i' v ≤ 0 := hφ i' v hve
  have hw0 : φ i' w ≤ 0 := hφ i' w hwe
  exact hM i i' hii' u hu w hw v hadj ⟨hvr, hvw, by omega, fun g _ _ _ ↦ by omega⟩

/-- Graph Minors IV, (2.2), claim (1) (page 232): if `Sᵢ` is the contraction of `Tᵢ` onto
`Fᵢ = {e ∈ E(Tᵢ) : φᵢ(e) = 0}`, then for `i < i'`, if `u ∈ V(Sᵢ)` is `M`-adjacent to `w ∈ V(S_{i'})`
and `v ≠ o(S_{i'})` reaches `w` in `S_{i'}`, then `u` is `M`-adjacent to `v`. -/
theorem lemma_2_2_claim_1 {T S : ℕ → RootedTree ι} {φ : ℕ → ι → ℕ} {M : SimpleGraph ι}
    (hS : ∀ i, (T i).IsContraction {e : ι | e ∈ (T i).edges ∧ φ i e = 0} (S i))
    (hM : ∀ i i', i < i' → ∀ u ∈ (T i).verts, ∀ w ∈ (T i').verts, ∀ v,
      M.Adj u w → (T i').Precedes (φ i') v w → M.Adj u v)
    {i i' : ℕ} (hii' : i < i') {u w v : ι} (hu : u ∈ (S i).verts) (hw : w ∈ (S i').verts)
    (hadj : M.Adj u w) (hvr : v ≠ (S i').root) (hvw : (S i').Reaches v w) :
    M.Adj u v := by
  have huT : u ∈ (T i).verts := (hS i).verts_subset (T i) hu
  have hwT : w ∈ (T i').verts := (hS i').verts_subset (T i') hw
  have hveS : v ∈ (S i').edges := (S i').mem_edges.2 ⟨hvr, hvw.verts_left (S i')⟩
  have hwr : w ≠ (S i').root := by
    rintro rfl
    exact hvr (((S i').reaches_root_iff).1 hvw)
  have hweS : w ∈ (S i').edges := (S i').mem_edges.2 ⟨hwr, hw⟩
  obtain ⟨⟨_, hv0⟩, -⟩ := ((hS i').mem_edges_iff (T i')).1 hveS
  obtain ⟨⟨_, hw0⟩, -⟩ := ((hS i').mem_edges_iff (T i')).1 hweS
  have hvwT : (T i').Reaches v w := (hS i').reaches_imp (T i') hvw
  have hprec : (T i').Precedes (φ i') v w :=
    ⟨(hS i').root_eq ▸ hvr, hvwT, by omega, fun g _ _ _ ↦ by omega⟩
  exact hM i i' hii' u huT w hwT v hadj hprec

/-- Graph Minors IV, (2.2), claim (2) (page 232): applying (2.1) to the contractions `Sᵢ` produces
an increasing sequence `z` with tree indices `idx` (`StrictMono idx`), where `z j` is the root of a
component `R j` of `T (idx j) \ F (idx j)`, such that `Set.range z` is `M`-stable and the set `A` of
heads of edges in `⋃ᵢ Fᵢ` with tails in `⋃_j V(R_j)` is `M`-rich. -/
theorem lemma_2_2_claim_2 (T : ℕ → RootedTree ι) (φ : ℕ → ι → ℕ) (M : SimpleGraph ι)
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    (hM : ∀ i i', i < i' → ∀ u ∈ (T i).verts, ∀ w ∈ (T i').verts, ∀ v,
      M.Adj u w → (T i').Precedes (φ i') v w → M.Adj u v)
    (hroot : M.IsIndepSet (Set.range fun i ↦ (T i).root)) :
    let F : ℕ → Set ι := fun i ↦ {e : ι | e ∈ (T i).edges ∧ φ i e = 0}
    ∃ (z : ℕ → ι) (idx : ℕ → ℕ) (hz_verts : ∀ j, z j ∈ (T (idx j)).verts)
      (hz_F : ∀ j, z j = (T (idx j)).root ∨ z j ∈ F (idx j)),
      StrictMono idx ∧ M.IsIndepSet (Set.range z) ∧
      IsRich M {v | ∃ i, v ∈ F i ∧
        (T i).parent v ∈ ⋃ j, (((T (idx j)).componentTree (F (idx j)) (z j)
          (hz_verts j) (hz_F j)).verts : Set ι)} := by
  intro F
  have hF_sub : ∀ i, F i ⊆ (T i).edges := fun i _ h ↦ h.1
  let S : ℕ → RootedTree ι := fun i ↦ ((T i).exists_isContraction (F i) (hF_sub i)).choose
  have hS : ∀ i, (T i).IsContraction (F i) (S i) :=
    fun i ↦ ((T i).exists_isContraction (F i) (hF_sub i)).choose_spec
  have hS_disj : Pairwise (fun i j ↦ Disjoint (S i).verts (S j).verts) :=
    fun i j hij ↦ (hdisj hij).mono ((hS i).verts_subset (T i)) ((hS j).verts_subset (T j))
  have hS_root : M.IsIndepSet (Set.range fun i ↦ (S i).root) := by
    have heq : (fun i ↦ (S i).root) = (fun i ↦ (T i).root) :=
      funext fun i ↦ (hS i).root_eq
    exact heq ▸ hroot
  obtain ⟨Z, hZ_inf, hZ_ind, hZ_sub, hZ_subsing, hZ_rich⟩ :=
    lemma_2_1 S M hS_disj (fun i i' hii' u hu w hw v hadj hvr hvw ↦
      lemma_2_2_claim_1 hS hM hii' hu hw hadj hvr hvw) hS_root
  obtain ⟨z, idx, hmono, _, hz_spec, hz_range⟩ :=
    exists_isIncreasing_of_infinite hS_disj hZ_inf hZ_sub
  have hrange_eq : Set.range z = Z := hz_range hZ_subsing
  have hz_verts : ∀ j, z j ∈ (T (idx j)).verts :=
    fun j ↦ (hS (idx j)).verts_subset (T (idx j)) (hz_spec j).2
  have hz_F : ∀ j, z j = (T (idx j)).root ∨ z j ∈ F (idx j) := by
    intro j
    rcases ((hS (idx j)).mem_verts_iff (T (idx j))).1 (hz_spec j).2 with hr | ⟨hF, -⟩
    · exact Or.inl hr
    · exact Or.inr hF
  refine ⟨z, idx, hz_verts, hz_F, hmono, hrange_eq.symm ▸ hZ_ind, ?_⟩
  refine hZ_rich.mono ?_
  rintro v ⟨i, hvF, hvp⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hvp
  rw [RootedTree.componentTree_verts, Finset.mem_coe, RootedTree.mem_componentAt] at hj
  have hvp_T : (T i).parent v ∈ (T i).verts :=
    (T i).parent_mem v ((T i).mem_verts_of_mem_edges hvF.1)
  have hi_eq : i = idx j := tree_eq_of_mem_verts hdisj hvp_T (hj.verts_right (T (idx j)))
  subst hi_eq
  have hve_S : v ∈ (S (idx j)).edges :=
    ((hS (idx j)).mem_edges_iff (T (idx j))).2 ⟨hvF, hvF.1⟩
  have hcomp_S : (T (idx j)).IsComponentRoot (F (idx j)) ((S (idx j)).parent v)
      ((T (idx j)).parent v) :=
    (hS (idx j)).parent_eq v hve_S
  have hp_eq : (S (idx j)).parent v = z j := hcomp_S.unique (T (idx j)) hj
  exact ⟨idx j, hve_S, hrange_eq ▸ ⟨j, hp_eq.symm⟩⟩

/-- Graph Minors IV, (2.2), claim (3) (page 233): applying the induction hypothesis to the
components `R_j` and `φ'_j(e) = φ_{idx j}(e) - 1` produces an infinite `M`-stable set
`X ⊆ ⋃_j V(R_j)` meeting each `V(Tᵢ)` in at most one vertex such that the set `B` of heads of edges
of `⋃_j R_j` with tails in `X` is `M`-rich. -/
theorem lemma_2_2_claim_3 {T : ℕ → RootedTree ι} {n : ℕ} {φ : ℕ → ι → ℕ} {M : SimpleGraph ι}
    (ih : ∀ (T' : ℕ → RootedTree ι) (φ' : ℕ → ι → ℕ),
      Pairwise (fun i j ↦ Disjoint (T' i).verts (T' j).verts) →
      (∀ i, ∀ f ∈ (T' i).edges, φ' i f ≤ n) →
      (∀ i i', i < i' → ∀ u ∈ (T' i).verts, ∀ w ∈ (T' i').verts, ∀ v,
        M.Adj u w → (T' i').Precedes (φ' i') v w → M.Adj u v) →
      M.IsIndepSet (Set.range fun i ↦ (T' i).root) →
      ∃ X : Set ι, X.Infinite ∧ M.IsIndepSet X ∧ X ⊆ ⋃ i, ((T' i).verts : Set ι) ∧
        (∀ i, (X ∩ (T' i).verts).Subsingleton) ∧
        IsRich M {v | ∃ i, v ∈ (T' i).edges ∧ (T' i).parent v ∈ X})
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    (hφ : ∀ i, ∀ f ∈ (T i).edges, φ i f ≤ n + 1)
    (hM : ∀ i i', i < i' → ∀ u ∈ (T i).verts, ∀ w ∈ (T i').verts, ∀ v,
      M.Adj u w → (T i').Precedes (φ i') v w → M.Adj u v)
    (z : ℕ → ι) (idx : ℕ → ℕ)
    (hz_verts : ∀ j, z j ∈ (T (idx j)).verts)
    (hz_F : ∀ j, z j = (T (idx j)).root ∨ z j ∈ {e : ι | e ∈ (T (idx j)).edges ∧ φ (idx j) e = 0})
    (hmono : StrictMono idx) (hz_ind : M.IsIndepSet (Set.range z)) :
    let F : ℕ → Set ι := fun i ↦ {e : ι | e ∈ (T i).edges ∧ φ i e = 0}
    let R : ℕ → RootedTree ι := fun j ↦
      (T (idx j)).componentTree (F (idx j)) (z j) (hz_verts j) (hz_F j)
    ∃ X : Set ι, X.Infinite ∧ M.IsIndepSet X ∧ X ⊆ ⋃ j, ((R j).verts : Set ι) ∧
      (∀ i, (X ∩ (T i).verts).Subsingleton) ∧
      IsRich M {v | ∃ j, v ∈ (R j).edges ∧ (R j).parent v ∈ X} := by
  intro F R
  let φ' : ℕ → ι → ℕ := fun j e ↦ φ (idx j) e - 1
  have hR_disj : Pairwise (fun j₁ j₂ ↦ Disjoint (R j₁).verts (R j₂).verts) := by
    intro j₁ j₂ hj
    exact (hdisj (hmono.injective.ne hj)).mono
      ((T (idx j₁)).componentAt_subset_verts (F (idx j₁)) (z j₁))
      ((T (idx j₂)).componentAt_subset_verts (F (idx j₂)) (z j₂))
  have hφ' : ∀ j, ∀ f ∈ (R j).edges, φ' j f ≤ n := by
    intro j f hf
    obtain ⟨hfT, -, -⟩ :=
      ((T (idx j)).mem_componentTree_edges_iff (F (idx j)) (z j) (hz_verts j) (hz_F j)).1 hf
    have hle := hφ (idx j) f hfT
    dsimp only [φ']
    omega
  have hR_M : ∀ j j', j < j' → ∀ u ∈ (R j).verts, ∀ w ∈ (R j').verts, ∀ v,
      M.Adj u w → (R j').Precedes (φ' j') v w → M.Adj u v := by
    intro j j' hjj' u hu w hw v hadj hprec
    have huT : u ∈ (T (idx j)).verts :=
      (T (idx j)).componentAt_subset_verts (F (idx j)) (z j) hu
    have hwT : w ∈ (T (idx j')).verts :=
      (T (idx j')).componentAt_subset_verts (F (idx j')) (z j') hw
    have hvR : v ∈ (R j').verts := hprec.2.1.verts_left (R j')
    have hprecT : (T (idx j')).Precedes (φ (idx j')) v w := by
      refine (T (idx j')).componentTree_precedes (F := F (idx j'))
        (fun e he ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨he, h⟩⟩)
        (z j') (hz_verts j') (hz_F j') hvR hprec
    exact hM (idx j) (idx j') (hmono hjj') u huT w hwT v hadj hprecT
  have hR_root : M.IsIndepSet (Set.range fun j ↦ (R j).root) := hz_ind
  obtain ⟨X, hX_inf, hX_ind, hX_sub, hX_subsing_R, hB_rich⟩ :=
    ih R φ' hR_disj hφ' hR_M hR_root
  refine ⟨X, hX_inf, hX_ind, hX_sub, fun i ↦ ?_, hB_rich⟩
  rintro x₁ ⟨hx₁X, hx₁T⟩ x₂ ⟨hx₂X, hx₂T⟩
  obtain ⟨j₁, hj₁⟩ := Set.mem_iUnion.1 (hX_sub hx₁X)
  obtain ⟨j₂, hj₂⟩ := Set.mem_iUnion.1 (hX_sub hx₂X)
  have hx₁_idx : x₁ ∈ (T (idx j₁)).verts :=
    (T (idx j₁)).componentAt_subset_verts (F (idx j₁)) (z j₁) hj₁
  have hx₂_idx : x₂ ∈ (T (idx j₂)).verts :=
    (T (idx j₂)).componentAt_subset_verts (F (idx j₂)) (z j₂) hj₂
  have hi₁ : idx j₁ = i := tree_eq_of_mem_verts hdisj hx₁_idx hx₁T
  have hi₂ : idx j₂ = i := tree_eq_of_mem_verts hdisj hx₂_idx hx₂T
  have hj12 : j₁ = j₂ := hmono.injective (hi₁.trans hi₂.symm)
  subst hj12
  exact hX_subsing_R j₁ ⟨hx₁X, hj₁⟩ ⟨hx₂X, hj₂⟩

private theorem lemma_2_2_ind (n : ℕ) :
    ∀ (T : ℕ → RootedTree ι) (φ : ℕ → ι → ℕ) (M : SimpleGraph ι),
      Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts) →
      (∀ i, ∀ f ∈ (T i).edges, φ i f ≤ n) →
      (∀ i i', i < i' → ∀ u ∈ (T i).verts, ∀ w ∈ (T i').verts, ∀ v,
        M.Adj u w → (T i').Precedes (φ i') v w → M.Adj u v) →
      M.IsIndepSet (Set.range fun i ↦ (T i).root) →
      ∃ X : Set ι, X.Infinite ∧ M.IsIndepSet X ∧ X ⊆ ⋃ i, ((T i).verts : Set ι) ∧
        (∀ i, (X ∩ (T i).verts).Subsingleton) ∧
        IsRich M {v | ∃ i, v ∈ (T i).edges ∧ (T i).parent v ∈ X} := by
  induction n with
  | zero => exact fun T φ M hdisj hφ hM hroot ↦ lemma_2_2_zero T φ M hdisj hφ hM hroot
  | succ n ih =>
    intro T φ M hdisj hφ hM hroot
    let F : ℕ → Set ι := fun i ↦ {e : ι | e ∈ (T i).edges ∧ φ i e = 0}
    obtain ⟨z, idx, hz_verts, hz_F, hmono, hz_ind, hA_rich⟩ :=
      lemma_2_2_claim_2 T φ M hdisj hM hroot
    let R : ℕ → RootedTree ι := fun j ↦
      (T (idx j)).componentTree (F (idx j)) (z j) (hz_verts j) (hz_F j)
    obtain ⟨X, hX_inf, hX_ind, hX_sub, hX_subsing, hB_rich⟩ :=
      lemma_2_2_claim_3 (fun T' φ' ↦ ih T' φ' M) hdisj hφ hM z idx hz_verts hz_F hmono hz_ind
    have hX_sub_T : X ⊆ ⋃ i, ((T i).verts : Set ι) := by
      refine hX_sub.trans ?_
      rintro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      exact Set.mem_iUnion.2 ⟨idx j, (T (idx j)).componentAt_subset_verts (F (idx j)) (z j) hj⟩
    refine ⟨X, hX_inf, hX_ind, hX_sub_T, hX_subsing, ?_⟩
    refine (hA_rich.union hB_rich).mono ?_
    rintro v ⟨i, hve, hvp⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hX_sub hvp)
    have hvp_T : (T i).parent v ∈ (T i).verts :=
      (T i).parent_mem v ((T i).mem_verts_of_mem_edges hve)
    have hvp_idx : (T i).parent v ∈ (T (idx j)).verts :=
      (T (idx j)).componentAt_subset_verts (F (idx j)) (z j) hj
    have hi_eq : i = idx j := tree_eq_of_mem_verts hdisj hvp_T hvp_idx
    subst hi_eq
    by_cases hφ0 : φ (idx j) v = 0
    · exact Or.inl ⟨idx j, ⟨hve, hφ0⟩, Set.mem_iUnion.2 ⟨j, hj⟩⟩
    · refine Or.inr ⟨j, ?_⟩
      have hv_not_F : v ∉ F (idx j) := fun h ↦ hφ0 h.2
      have hve_R : v ∈ (R j).edges :=
        ((T (idx j)).mem_componentTree_edges_iff (F (idx j)) (z j) (hz_verts j) (hz_F j)).2
          ⟨hve, hv_not_F, hj⟩
      have hne_root : v ≠ z j := (R j).ne_root_of_mem_edges hve_R
      have hp_eq : (R j).parent v = (T (idx j)).parent v :=
        (T (idx j)).componentTree_parent_of_ne (F (idx j)) (z j) (hz_verts j) (hz_F j) hne_root
      exact ⟨hve_R, hp_eq ▸ hvp⟩

/-- Graph Minors IV, (2.2) (page 232). -/
theorem lemma_2_2 : TreeLemma22Statement :=
  fun T n φ M hdisj hφ hM hroot ↦ lemma_2_2_ind n T φ M hdisj hφ hM hroot

end GraphMinor.GM04
