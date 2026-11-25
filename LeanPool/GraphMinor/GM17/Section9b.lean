/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section9
public import LeanPool.GraphMinor.GM17.ArcDisc

/-!
# Graph Minors XVII, Section 9 (continued): Linkages in a True Portrayal

This file formalizes (9.3) through (9.8) of Robertson and Seymour,
*Graph Minors. XVII. Taming a Vortex*, J. Combin. Theory Ser. B 77 (1999), 162–210
(pages 184–188).
The portrayal deductions that use painting results are proved in `Section9bProved`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology Metric
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

local notation "𝕀" => unitInterval

@[expose] public section

/-- There are `q` mutually vertex-disjoint paths in `H.skeleton` from `X` to `Y` avoiding `W`. -/
def HasDisjointPathsAvoiding {α : Type u} {β : Type v} (H : Hypergraph α β)
    (X Y W : Set α) (q : ℕ) : Prop :=
  ∃ L : Fin q → PathFromTo H.skeleton X Y,
    (Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support}) ∧
    ∀ i, Disjoint {z | z ∈ (L i).walk.support} W

end

theorem hasDisjointPathsAvoiding_iff_forall_isSeparation
    {α : Type u} {β : Type v} (H : Hypergraph α β) {X Y W : Set α}
    (hX : X ⊆ H.vertexSet) (hY : Y ⊆ H.vertexSet) (hW : W ⊆ H.vertexSet) (q : ℕ) :
    HasDisjointPathsAvoiding H X Y W q ↔
      ∀ G₁ G₂ : Hypergraph α β, H.IsSeparation G₁ G₂ →
        X ∪ W ⊆ G₁.vertexSet → Y ∪ W ⊆ G₂.vertexSet →
        q ≤ ((G₁ ∩ G₂).vertexSet \ W).ncard := by
  classical
  have hW_fin : W.Finite := H.vertexSet_finite.subset hW
  constructor
  · rintro ⟨L, hdisj, havoid⟩ G₁ G₂ hsep hXW hYW
    have hhit : ∀ i : Fin q, ∃ z ∈ (L i).walk.support, z ∈ (G₁ ∩ G₂).vertexSet \ W := by
      intro i
      obtain ⟨z, hz_sup, hz_inter⟩ :=
        walk_meets_separation hsep (L i).walk (hXW (Or.inl (L i).first_mem)) (hYW (Or.inl
          (L i).last_mem))
      exact ⟨z, hz_sup, hz_inter, Set.disjoint_left.mp (havoid i) hz_sup⟩
    choose f hf_sup hf_mem using hhit
    have hfin_diff : ((G₁ ∩ G₂).vertexSet \ W).Finite :=
      (G₁ ∩ G₂).vertexSet_finite.subset sdiff_subset
    have hinj : Function.Injective f := by
      intro i j hij
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hne) (hf_sup i) (hij ▸ hf_sup j)
    have hcard_range : (range f).ncard = q := by
      rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hsub : range f ⊆ (G₁ ∩ G₂).vertexSet \ W := by
      rintro _ ⟨i, rfl⟩
      exact hf_mem i
    exact hcard_range ▸ ncard_le_ncard hsub hfin_diff
  · intro hsep_all
    have hmenger : HasDisjointPaths H.skeleton (X ∪ W) (Y ∪ W) (q + W.ncard) := by
      rw [← GraphMinor.menger H (X ∪ W) (Y ∪ W) (union_subset hX hW) (union_subset hY hW)
        (q + W.ncard)]
      intro G₁ G₂ hsep hXW hYW
      have hle := hsep_all G₁ G₂ hsep hXW hYW
      have hW_sub : W ⊆ (G₁ ∩ G₂).vertexSet :=
        fun w hw => ⟨hXW (Or.inr hw), hYW (Or.inr hw)⟩
      have hfin_inter : (G₁ ∩ G₂).vertexSet.Finite := (G₁ ∩ G₂).vertexSet_finite
      have heq := ncard_sdiff_add_ncard_of_subset hW_sub hfin_inter
      change q + W.ncard ≤ (G₁ ∩ G₂).vertexSet.ncard
      omega
    rcases hmenger with ⟨P, hP_disj⟩
    let Bhit : Set (Fin (q + W.ncard)) :=
      {k | ∃ w ∈ W, w ∈ (P k).walk.support}
    let Bmiss : Set (Fin (q + W.ncard)) :=
      {k | Disjoint {z | z ∈ (P k).walk.support} W}
    have hBhit_le : Bhit.ncard ≤ W.ncard := by
      have hex : ∀ k : Bhit, ∃ w ∈ W, w ∈ (P k.1).walk.support := fun k => k.2
      choose g hg_W hg_sup using hex
      have hinj : Function.Injective g := by
        intro k₁ k₂ hEq
        ext1
        by_contra hne
        exact Set.disjoint_left.mp (hP_disj hne) (hg_sup k₁) (hEq ▸ hg_sup k₂)
      have hrange : (range g).ncard ≤ W.ncard :=
        ncard_le_ncard (by rintro _ ⟨k, rfl⟩; exact hg_W k) hW_fin
      rw [ncard_range_of_injective hinj, Nat.card_coe_set_eq] at hrange
      exact hrange
    have hcompl : Bmiss = Bhitᶜ := by
      ext k
      simp only [Bmiss, Bhit, mem_compl_iff, mem_ofPred_eq, Set.disjoint_left, not_exists, not_and]
      exact ⟨fun h w hw hsup => h hsup hw, fun h w hsup hw => h w hw hsup⟩
    have hBmiss_ge : q ≤ Bmiss.ncard := by
      have hadd := ncard_add_ncard_compl Bhit
      rw [← hcompl, Nat.card_eq_fintype_card, Fintype.card_fin] at hadd
      omega
    obtain ⟨S₀, hS₀_sub, hS₀_card⟩ := exists_subset_card_eq hBmiss_ge
    have hS₀_fin : Fintype S₀ := Fintype.ofFinite S₀
    have hcard_S₀ : Fintype.card S₀ = q := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hS₀_card]
    let e' : Fin q ≃ S₀ := (Fintype.equivFinOfCardEq hcard_S₀).symm
    refine ⟨fun i =>
      let k := (e' i).1
      have hk : Disjoint {z | z ∈ (P k).walk.support} W := hS₀_sub (e' i).2
      { first := (P k).first
        last := (P k).last
        walk := (P k).walk
        isPath := (P k).isPath
        first_mem := (P k).first_mem.resolve_right
          (Set.disjoint_left.mp hk (SimpleGraph.Walk.start_mem_support _))
        last_mem := (P k).last_mem.resolve_right
          (Set.disjoint_left.mp hk (SimpleGraph.Walk.end_mem_support _)) },
      fun i j hne => hP_disj (fun hEq => hne (e'.injective (Subtype.ext hEq))),
      fun i => hS₀_sub (e' i).2⟩

/-- **(9.5)** (Graph Minors XVII, Section 9, page 186):
"Let $H$ be a graph, let $A, B \subseteq V(H)$, and let $X \subseteq A$ and $Y \subseteq B$
with $|X| = |Y| = q$. Suppose that there is a linkage in $H \setminus (A - X)$ from $X$ to a
$q$-subset of $B$, and there is a linkage in $H \setminus (B - Y)$ from a $q$-subset of $A$
to $Y$. Then either there is a linkage in $H \setminus ((A - X) \cup (B - Y))$ from $X$ to
$Y$, or there are $q + 1$ mutually vertex-disjoint paths in $H$ from $A$ to $B$." -/
theorem theorem_9_5_proof {α : Type u} {β : Type v} (H : Hypergraph α β) {A B X Y : Set α} {q : ℕ}
    (hA : A ⊆ H.vertexSet) (hB : B ⊆ H.vertexSet) (hXA : X ⊆ A) (hYB : Y ⊆ B)
    (hXB : HasDisjointPathsAvoiding H X B (A \ X) q)
    (hAY : HasDisjointPathsAvoiding H A Y (B \ Y) q) :
    HasDisjointPathsAvoiding H X Y ((A \ X) ∪ (B \ Y)) q ∨
      HasDisjointPaths H.skeleton A B (q + 1) := by
  classical
  by_contra! hnot
  rcases hnot with ⟨hno_XY, hno_AB⟩
  have hX : X ⊆ H.vertexSet := hXA.trans hA
  have hY : Y ⊆ H.vertexSet := hYB.trans hB
  have hWA : A \ X ⊆ H.vertexSet := sdiff_subset.trans hA
  have hWB : B \ Y ⊆ H.vertexSet := sdiff_subset.trans hB
  have hW : (A \ X) ∪ (B \ Y) ⊆ H.vertexSet := union_subset hWA hWB
  rw [hasDisjointPathsAvoiding_iff_forall_isSeparation H hX hY hW q] at hno_XY
  push Not at hno_XY
  obtain ⟨C₁, C₂, hsepC, hXC₁, hYC₂, hltC⟩ := hno_XY
  rw [← GraphMinor.menger H A B hA hB (q + 1)] at hno_AB
  push Not at hno_AB
  obtain ⟨D₁, D₂, hsepD, hAD₁, hBD₂, hltD⟩ := hno_AB
  have hA_C₁ : A ⊆ C₁.vertexSet := by
    intro a ha
    by_cases haX : a ∈ X
    · exact hXC₁ (Or.inl haX)
    · exact hXC₁ (Or.inr (Or.inl ⟨ha, haX⟩))
  have hB_C₂ : B ⊆ C₂.vertexSet := by
    intro b hb
    by_cases hbY : b ∈ Y
    · exact hYC₂ (Or.inl hbY)
    · exact hYC₂ (Or.inr (Or.inr ⟨hb, hbY⟩))
  have hWB_C₁ : B \ Y ⊆ C₁.vertexSet := fun z hz => hXC₁ (Or.inr (Or.inr hz))
  have hWA_C₂ : A \ X ⊆ C₂.vertexSet := fun z hz => hYC₂ (Or.inr (Or.inl hz))
  have hsep1 : H.IsSeparation (C₁ ∩ D₁) (C₂ ∪ D₂) :=
    (hsepC.symm.union_inter hsepD.symm).symm
  have hsep2 : H.IsSeparation (C₁ ∪ D₁) (C₂ ∩ D₂) :=
    hsepC.union_inter hsepD
  have hq1 : q ≤ (((C₁ ∩ D₁) ∩ (C₂ ∪ D₂)).vertexSet \ (A \ X)).ncard := by
    have h1 := (hasDisjointPathsAvoiding_iff_forall_isSeparation H hX hB hWA q).mp hXB
    refine h1 (C₁ ∩ D₁) (C₂ ∪ D₂) hsep1 ?_ ?_
    · exact union_subset (hXA.trans (subset_inter hA_C₁ hAD₁)) (sdiff_subset.trans
      (subset_inter hA_C₁ hAD₁))
    · exact union_subset (hB_C₂.trans subset_union_left) (hWA_C₂.trans subset_union_left)
  have hq2 : q ≤ (((C₁ ∪ D₁) ∩ (C₂ ∩ D₂)).vertexSet \ (B \ Y)).ncard := by
    have h2 := (hasDisjointPathsAvoiding_iff_forall_isSeparation H hA hY hWB q).mp hAY
    refine h2 (C₁ ∪ D₁) (C₂ ∩ D₂) hsep2 ?_ ?_
    · exact union_subset (hA_C₁.trans subset_union_left) (hWB_C₁.trans subset_union_left)
    · exact union_subset (hYB.trans (subset_inter hB_C₂ hBD₂)) (sdiff_subset.trans
      (subset_inter hB_C₂ hBD₂))
  let U₁ := ((C₁ ∩ D₁) ∩ (C₂ ∪ D₂)).vertexSet \ (A \ X)
  let U₂ := ((C₁ ∪ D₁) ∩ (C₂ ∩ D₂)).vertexSet \ (B \ Y)
  let SC := (C₁ ∩ C₂).vertexSet \ ((A \ X) ∪ (B \ Y))
  let SD := (D₁ ∩ D₂).vertexSet
  have hWA_D₁ : A \ X ⊆ D₁.vertexSet := sdiff_subset.trans hAD₁
  have hWB_D₂ : B \ Y ⊆ D₂.vertexSet := sdiff_subset.trans hBD₂
  have h_union : U₁ ∪ U₂ ⊆ SC ∪ SD := by
    rintro z (⟨⟨⟨hzC₁, hzD₁⟩, hzC₂D₂⟩, hzWA⟩ | ⟨⟨hzC₁D₁, ⟨hzC₂, hzD₂⟩⟩, hzWB⟩)
    · by_cases hzD₂ : z ∈ D₂.vertexSet
      · exact Or.inr ⟨hzD₁, hzD₂⟩
      · have hzC₂ : z ∈ C₂.vertexSet := hzC₂D₂.resolve_right hzD₂
        have hzWB : z ∉ B \ Y := fun h => hzD₂ (hWB_D₂ h)
        exact Or.inl ⟨⟨hzC₁, hzC₂⟩, not_or.mpr ⟨hzWA, hzWB⟩⟩
    · by_cases hzD₁ : z ∈ D₁.vertexSet
      · exact Or.inr ⟨hzD₁, hzD₂⟩
      · have hzC₁ : z ∈ C₁.vertexSet := hzC₁D₁.resolve_right hzD₁
        have hzWA : z ∉ A \ X := fun h => hzD₁ (hWA_D₁ h)
        exact Or.inl ⟨⟨hzC₁, hzC₂⟩, not_or.mpr ⟨hzWA, hzWB⟩⟩
  have h_inter : U₁ ∩ U₂ ⊆ SC ∩ SD := by
    rintro z ⟨⟨⟨⟨hzC₁, hzD₁⟩, _⟩, hzWA⟩, ⟨⟨_, ⟨hzC₂, hzD₂⟩⟩, hzWB⟩⟩
    exact ⟨⟨⟨hzC₁, hzC₂⟩, not_or.mpr ⟨hzWA, hzWB⟩⟩, ⟨hzD₁, hzD₂⟩⟩
  have hSC_fin : SC.Finite := (C₁ ∩ C₂).vertexSet_finite.subset sdiff_subset
  have hSD_fin : SD.Finite := (D₁ ∩ D₂).vertexSet_finite
  have hU₁_fin : U₁.Finite := ((C₁ ∩ D₁) ∩ (C₂ ∪ D₂)).vertexSet_finite.subset sdiff_subset
  have hU₂_fin : U₂.Finite := ((C₁ ∪ D₁) ∩ (C₂ ∩ D₂)).vertexSet_finite.subset sdiff_subset
  have hsum_U := ncard_union_add_ncard_inter U₁ U₂ hU₁_fin hU₂_fin
  have hsum_S := ncard_union_add_ncard_inter SC SD hSC_fin hSD_fin
  have hle_union : (U₁ ∪ U₂).ncard ≤ (SC ∪ SD).ncard := ncard_le_ncard h_union
    (hSC_fin.union hSD_fin)
  have hle_inter : (U₁ ∩ U₂).ncard ≤ (SC ∩ SD).ncard := ncard_le_ncard h_inter
    (hSC_fin.inter_of_left SD)
  change SC.ncard < q at hltC
  change SD.ncard < q + 1 at hltD
  change q ≤ U₁.ncard at hq1
  change q ≤ U₂.ncard at hq2
  omega

theorem subset_closure_diff_ends_of_isLineWithEnds {S : Type*} [TopologicalSpace S]
    {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) :
    L ⊆ closure (L \ {u, v}) := by
  obtain ⟨f, hf0, hf1⟩ := hL
  let g : ℝ → S := fun t => (f (projIcc 0 1 zero_le_one t)).1
  have hg : Continuous g :=
    continuous_subtype_val.comp (f.continuous.comp continuous_projIcc)
  have hIoo_sub : g '' Ioo (0 : ℝ) 1 ⊆ L \ {u, v} := by
    rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
    refine ⟨(f _).2, ?_⟩
    have hp : projIcc (0 : ℝ) 1 zero_le_one t = ⟨t, h0.le, h1.le⟩ :=
      projIcc_of_mem zero_le_one ⟨h0.le, h1.le⟩
    rintro (hx | hx)
    · have : f (projIcc 0 1 zero_le_one t) = f 0 := Subtype.ext (hx.trans hf0.symm)
      have hval := congrArg Subtype.val (f.injective this)
      rw [hp] at hval; simp only [Icc.coe_zero] at hval; linarith
    · have : f (projIcc 0 1 zero_le_one t) = f 1 :=
        Subtype.ext ((mem_singleton_iff.mp hx).trans hf1.symm)
      have hval := congrArg Subtype.val (f.injective this)
      rw [hp] at hval; simp only [Icc.coe_one] at hval; linarith
  have hL_sub : L ⊆ g '' Icc (0 : ℝ) 1 := by
    intro x hxL
    obtain ⟨t, ht⟩ := f.surjective ⟨x, hxL⟩
    refine ⟨t.1, t.2, ?_⟩
    have : projIcc (0 : ℝ) 1 zero_le_one t.1 = t := projIcc_val zero_le_one t
    simp only [g, this, ht]
  calc L
    _ ⊆ g '' Icc (0 : ℝ) 1 := hL_sub
    _ = g '' closure (Ioo (0 : ℝ) 1) := by rw [closure_Ioo zero_ne_one]
    _ ⊆ closure (g '' Ioo (0 : ℝ) 1) := image_closure_subset_closure_image hg
    _ ⊆ closure (L \ {u, v}) := closure_mono hIoo_sub

theorem closure_border_cell_subset_cuffPoint_Icc {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {Θ c₀ : Set S} (hΘ : Θ ∈ cuffs S) (hc₀ : c₀ ∈ Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty) (f : Circle ≃ₜ Θ) {a b : ℝ}
    (hab : a < b) (hba : b < a + 2 * Real.pi)
    (haN : GM19.cuffPoint f a ∈ Γ.N) (hbN : GM19.cuffPoint f b ∈ Γ.N)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (ht₀_cl : GM19.cuffPoint f t₀ ∈ closure c₀) :
    closure c₀ ∩ Θ ⊆ GM19.cuffPoint f '' Icc a b := by
  let A : Set S := GM19.cuffPoint f '' Icc a b
  let B : Set S := GM19.cuffPoint f '' Icc b (a + 2 * Real.pi)
  have hA_cl : IsClosed A := (isCompact_Icc.image (cuffPoint_continuous f)).isClosed
  have hB_cl : IsClosed B := (isCompact_Icc.image (cuffPoint_continuous f)).isClosed
  have hAB_eq : A ∪ B = Θ := by
    refine Subset.antisymm ?_ ?_
    · rintro _ (⟨t, _, rfl⟩ | ⟨t, _, rfl⟩) <;> exact cuffPoint_mem f t
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := exists_cuffPoint_mem_Ico f a hy
      rcases le_total t b with hle | hle
      · exact Or.inl ⟨t, ⟨ht.1, hle⟩, rfl⟩
      · exact Or.inr ⟨t, ⟨hle, ht.2.le⟩, rfl⟩
  have hnot_B : ∀ t ∈ Ioo a b, GM19.cuffPoint f t ∉ B := by
    rintro t ⟨hat, htb⟩ ⟨t', ⟨hbt', ht'a⟩, hEq⟩
    rcases lt_or_eq_of_le ht'a with hlt | rfl
    · have hEq_t :=
        cuffPoint_injOn_Ico f a ⟨hat.le, htb.trans hba⟩ ⟨hab.le.trans hbt', hlt⟩ hEq.symm
      linarith
    · rw [cuffPoint_add_two_pi] at hEq
      have hEq_t := cuffPoint_injOn_Ico f a ⟨hat.le, htb.trans hba⟩ ⟨le_rfl, by linarith⟩ hEq.symm
      linarith
  have hAB_inter : A ∩ B ⊆ Γ.N := by
    rintro x ⟨⟨t, ⟨hat, htb⟩, rfl⟩, hxB⟩
    rcases eq_or_lt_of_le hat with rfl | hat'
    · exact haN
    · rcases eq_or_lt_of_le htb with rfl | htb'
      · exact hbN
      · exact (hnot_B t ⟨hat', htb'⟩ hxB).elim
  have hsub_cuff := Γ.border_cell_subset_cuff hc₀ hΘ hc₀_Θ
  have hbd : (c₀ ∩ bd S).Nonempty := hsub_cuff.2.1 ▸ hc₀_Θ
  obtain ⟨u, v, _, _, hL, hdiff, _, _⟩ := Γ.border_cell_exists_ends hc₀ hbd
  have hcl_sub_cl : closure c₀ ∩ Θ ⊆ closure (c₀ ∩ Θ) := by
    rw [← hsub_cuff.2.2.1, ← hsub_cuff.2.1, hdiff]
    exact subset_closure_diff_ends_of_isLineWithEnds hL
  have hc₀_sub : c₀ ∩ Θ ⊆ A ∪ B := hAB_eq ▸ inter_subset_right
  have hc₀_disj : Disjoint (c₀ ∩ Θ) (A ∩ B) :=
    Set.disjoint_left.mpr fun x ⟨hxc, _⟩ hxAB => (Γ.cell_subset_diff hc₀ hxc).2 (hAB_inter hxAB)
  have hc₀_pre : IsPreconnected (c₀ ∩ Θ) :=
    (Γ.isPathConnected_cell_inter_cuff hc₀ hΘ hc₀_Θ).isConnected.isPreconnected
  have hc₀_A_or_B : c₀ ∩ Θ ⊆ A ∨ c₀ ∩ Θ ⊆ B := by
    rw [isPreconnected_closed_iff] at hc₀_pre
    by_cases hA : c₀ ∩ Θ ⊆ A
    · exact Or.inl hA
    · right
      by_contra hB
      obtain ⟨x₁, hx₁c, hx₁A⟩ := not_subset.mp hA
      obtain ⟨x₂, hx₂c, hx₂B⟩ := not_subset.mp hB
      have hx₁B : x₁ ∈ B := (hc₀_sub hx₁c).resolve_left hx₁A
      have hx₂A : x₂ ∈ A := (hc₀_sub hx₂c).resolve_right hx₂B
      obtain ⟨z, hzc, hzA, hzB⟩ := hc₀_pre A B hA_cl hB_cl hc₀_sub ⟨x₂, hx₂c, hx₂A⟩ ⟨x₁, hx₁c, hx₁B⟩
      exact Set.disjoint_left.mp hc₀_disj hzc ⟨hzA, hzB⟩
  rcases hc₀_A_or_B with hc₀A | hc₀B
  · exact hcl_sub_cl.trans (hA_cl.closure_subset_iff.mpr hc₀A)
  · exfalso
    have ht₀_mem : GM19.cuffPoint f t₀ ∈ closure c₀ ∩ Θ := ⟨ht₀_cl, cuffPoint_mem f t₀⟩
    exact hnot_B t₀ ht₀ (hcl_sub_cl.trans (hB_cl.closure_subset_iff.mpr hc₀B) ht₀_mem)

theorem inOrderOn_of_mem_closure_border_cell_left {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {Θ c₀ : Set S} (hΘ : Θ ∈ cuffs S) (hc₀ : c₀ ∈ Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty) {m₁ m₂ m₃ m₄ : S}
    (h12 : m₁ ≠ m₂) (h23 : m₂ ≠ m₃) (h34 : m₃ ≠ m₄) (h41 : m₄ ≠ m₁)
    (hm₂N : m₂ ∈ Γ.N) (hm₄N : m₄ ∈ Γ.N)
    (hm₁_cl : m₁ ∈ closure c₀) (hord : GM19.InOrderOn Θ m₁ m₂ m₃ m₄)
    {u : S} (hu : u ∈ closure c₀ ∩ Θ) :
    GM19.InOrderOn Θ u m₂ m₃ m₄ := by
  obtain ⟨f, t₁, t₂, t₃, t₄, ht12, ht23, ht34, ht41, rfl, rfl, rfl, rfl⟩ := hord
  have hlt12 : t₁ < t₂ := lt_of_le_of_ne ht12 fun h => h12 (by rw [h])
  have hlt23 : t₂ < t₃ := lt_of_le_of_ne ht23 fun h => h23 (by rw [h])
  have hlt34 : t₃ < t₄ := lt_of_le_of_ne ht34 fun h => h34 (by rw [h])
  have hlt41 : t₄ < t₁ + 2 * Real.pi := lt_of_le_of_ne ht41 fun h =>
    h41 (by rw [h, cuffPoint_add_two_pi])
  have haN : GM19.cuffPoint f (t₄ - 2 * Real.pi) ∈ Γ.N := by
    rw [cuffPoint_sub_two_pi]; exact hm₄N
  have hcl := closure_border_cell_subset_cuffPoint_Icc Γ hΘ hc₀ hc₀_Θ f
    (a := t₄ - 2 * Real.pi) (b := t₂) (by linarith) (by linarith) haN hm₂N
    (t₀ := t₁) ⟨by linarith, hlt12⟩ hm₁_cl hu
  rcases hcl with ⟨tu, ⟨htu1, htu2⟩, rfl⟩
  exact ⟨f, tu, t₂, t₃, t₄, htu2, ht23, ht34, by linarith, rfl, rfl, rfl, rfl⟩

theorem inOrderOn_of_mem_closure_border_cell_mid {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {Θ c₀ : Set S} (hΘ : Θ ∈ cuffs S) (hc₀ : c₀ ∈ Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty) {m₁ m₂ m₃ m₄ : S}
    (h12 : m₁ ≠ m₂) (h23 : m₂ ≠ m₃) (h34 : m₃ ≠ m₄) (h41 : m₄ ≠ m₁)
    (hm₁N : m₁ ∈ Γ.N) (hm₃N : m₃ ∈ Γ.N)
    (hm₂_cl : m₂ ∈ closure c₀) (hord : GM19.InOrderOn Θ m₁ m₂ m₃ m₄)
    {u : S} (hu : u ∈ closure c₀ ∩ Θ) :
    GM19.InOrderOn Θ m₁ u m₃ m₄ := by
  obtain ⟨f, t₁, t₂, t₃, t₄, ht12, ht23, ht34, ht41, rfl, rfl, rfl, rfl⟩ := hord
  have hlt12 : t₁ < t₂ := lt_of_le_of_ne ht12 fun h => h12 (by rw [h])
  have hlt23 : t₂ < t₃ := lt_of_le_of_ne ht23 fun h => h23 (by rw [h])
  have hlt34 : t₃ < t₄ := lt_of_le_of_ne ht34 fun h => h34 (by rw [h])
  have hlt41 : t₄ < t₁ + 2 * Real.pi := lt_of_le_of_ne ht41 fun h =>
    h41 (by rw [h, cuffPoint_add_two_pi])
  have hcl := closure_border_cell_subset_cuffPoint_Icc Γ hΘ hc₀ hc₀_Θ f
    (a := t₁) (b := t₃) (by linarith) (by linarith) hm₁N hm₃N
    (t₀ := t₂) ⟨hlt12, hlt23⟩ hm₂_cl hu
  rcases hcl with ⟨tu, ⟨htu1, htu2⟩, rfl⟩
  exact ⟨f, t₁, tu, t₃, t₄, htu1, htu2, ht34, ht41, rfl, rfl, rfl, rfl⟩

@[expose] public section

open Classical in
/-- A painting obtained by moving a border node along its cuff and replacing two incident cells. -/
def IsIndentedBorderPainting {S : Type} [TopologicalSpace S]
    (Γ : Painting S) (Θ c₀ : Set S) (n₁ n₂ n_star : S) (R : Set (Set S)) (Γ' : Painting S) : Prop :=
  ∃ (n_star' : S) (c₁ c₂ : Set S) (cellMap : Set S → Set S),
    n_star' ∈ c₀ ∩ Θ ∧
    Γ'.N = (Γ.N \ {n_star}) ∪ {n_star'} ∧
    c₁ ∈ Γ'.C ∧ c₂ ∈ Γ'.C ∧ c₁ ≠ c₂ ∧
    (c₁ ∩ Θ).Nonempty ∧ (c₂ ∩ Θ).Nonempty ∧
    tilde c₁ = {n₁, n_star'} ∧ tilde c₂ = {n₂, n_star'} ∧
    Set.BijOn cellMap (Γ'.C \ {c₁, c₂}) (Γ.C \ R) ∧
    (∀ d ∈ Γ'.C \ {c₁, c₂}, ∀ Θ' ∈ cuffs S, ((d ∩ Θ').Nonempty ↔ ((cellMap d) ∩ Θ').Nonempty)) ∧
    (∀ d ∈ Γ'.C \ {c₁, c₂}, ((d ∩ bd S).Nonempty ↔ ((cellMap d) ∩ bd S).Nonempty)) ∧
    (∀ d ∈ Γ'.C \ {c₁, c₂},
      tilde d = (fun x => if x = n_star then n_star' else x) '' tilde (cellMap d))

end

@[expose] public section

/-- The border-indentation statement of Graph Minors XVII, (9.6). -/
def IndentedBorderPaintingStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S], IsSurface S →
    ∀ (Γ : Painting S),
      6 ≤ Γ.N.ncard →
      (∀ r ∈ Γ.regions, IsOpenDisc r) →
      (∀ r ∈ Γ.regions, IsOArc (closure r \ r)) →
      (∀ c ∈ Γ.C, 2 ≤ (tilde c).ncard) →
      (∀ F : Set S, IsLine F → Γ.IsNormal F → F ∩ bd S = lineEnds F → (F ∩ Γ.N).ncard = 2 →
        ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S ∧
          Δ ∩ Γ.N ⊆ F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard = 1) →
      (∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C, c₁ ≠ c₂ → tilde c₁ ⊆ tilde c₂ →
        (c₁ ∩ bd S).Nonempty ∧ (tilde c₂).ncard = 3) →
      ∀ Θ ∈ cuffs S, ∀ c₀ ∈ Γ.C, (c₀ ∩ Θ).Nonempty →
        ∀ n₁ n₂ : S, n₁ ≠ n₂ → tilde c₀ = {n₁, n₂} →
        ((¬ ∃ c ∈ Γ.C, ¬ (c ∩ bd S).Nonempty ∧ tilde c₀ ⊆ tilde c) →
          ∃ n₀ ∈ Γ.N \ bd S, ∃ Γ' : Painting S,
            IsIndentedBorderPainting Γ Θ c₀ n₁ n₂ n₀ {c₀} Γ') ∧
        (∀ c₃ ∈ Γ.C, ¬ (c₃ ∩ bd S).Nonempty → ∀ n₃ ∈ Γ.N \ bd S,
          tilde c₃ = {n₁, n₂, n₃} →
          ∃ Γ' : Painting S, IsIndentedBorderPainting Γ Θ c₀ n₁ n₂ n₃ {c₀, c₃} Γ')

end

theorem border_cell_vertex_mem_borderPlus_of_mem_other
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    {n₁ n₂ : π.S} (htc₀ : tilde c₀ = {n₁, n₂})
    {w : α} (hw₀ : w ∈ (π.cellGraph c₀).vertexSet)
    {d : Set π.S} (hd : d ∈ π.Γ.C) (hne : d ≠ c₀) (hwd : w ∈ (π.cellGraph d).vertexSet) :
    w ∈ π.borderPlus n₁ ∪ π.borderPlus n₂ := by
  obtain ⟨n, hn_tc, hwn⟩ := π.p6 c₀ hc₀ hbd₀ w hw₀ ⟨d, hd, hne, hwd⟩
  rw [htc₀] at hn_tc
  rcases hn_tc with rfl | rfl
  · exact Or.inl hwn
  · exact Or.inr hwn

theorem border_cell_vertex_inter_borderPlus_subset
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    {n₁ n₂ : π.S} (htc₀ : tilde c₀ = {n₁, n₂})
    {m : π.S} (hm : m ∈ π.Γ.N ∩ bd π.S)
    {w : α} (hw₀ : w ∈ (π.cellGraph c₀).vertexSet) (hwm : w ∈ π.borderPlus m) :
    w ∈ π.borderPlus n₁ ∪ π.borderPlus n₂ := by
  let Θ' := connectedComponentIn (bd π.S) m
  have hΘ' : Θ' ∈ cuffs π.S := ⟨m, hm.2, rfl⟩
  have hΘ'_arc : IsOArc Θ' := (cuff_statement.{0} π.S π.isSurface).2.2 Θ' hΘ'
  have hΘ'_bd : Θ' ⊆ bd π.S := connectedComponentIn_subset (bd π.S) m
  obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ' hΘ'_arc
  have hm_Θ' : m ∈ π.Γ.N ∩ Θ' := ⟨hm.1, mem_connectedComponentIn hm.2⟩
  rw [← E.range_node] at hm_Θ'
  rcases hm_Θ' with ⟨i, hi_eq⟩
  let d := E.cell i
  have hd_mem : d ∈ {c ∈ π.Γ.C | (c ∩ Θ').Nonempty} := E.range_cell ▸ ⟨i, rfl⟩
  have hd_bd : (d ∩ bd π.S).Nonempty := hd_mem.2.mono (inter_subset_inter_right _ hΘ'_bd)
  have hm_td : m ∈ tilde d := by rw [← hi_eq, E.cell_tilde i]; exact Or.inl rfl
  by_cases hdc₀ : d = c₀
  · subst hdc₀
    rw [htc₀] at hm_td
    rcases hm_td with rfl | rfl
    · exact Or.inl hwm
    · exact Or.inr hwm
  · have hwd : w ∈ (π.cellGraph d).vertexSet :=
      π.borderPlus_subset_cellGraph hd_mem.1 hd_bd hm_td hwm
    exact border_cell_vertex_mem_borderPlus_of_mem_other π hc₀ hbd₀ htc₀ hw₀ hd_mem.1 hdc₀ hwd

theorem nodeVertex_notMem_border_cellGraph_of_notMem_cuff
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ d ∈ π.Γ.C, n ∈ tilde d)
    {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C) (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ n₂ : π.S} (htc₀ : tilde c₀ = {n₁, n₂})
    {m : π.S} (hmN : m ∈ π.Γ.N) (hm_not_Θ : m ∉ Θ) :
    π.nodeVertex m ∉ (π.cellGraph c₀).vertexSet := by
  intro hmem
  have hsub_cuff := π.Γ.border_cell_subset_cuff hc₀ hΘ hc₀_Θ
  have hbd₀ : (c₀ ∩ bd π.S).Nonempty := hsub_cuff.2.1 ▸ hc₀_Θ
  have hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ := hsub_cuff.2.2.2.1 (htc₀ ▸ Or.inl rfl)
  have hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ := hsub_cuff.2.2.2.1 (htc₀ ▸ Or.inr rfl)
  obtain ⟨d, hd, hm_td⟩ := hnode_cell m hmN
  have hdc₀ : d ≠ c₀ := fun h => hm_not_Θ (hsub_cuff.2.2.2.1 (h ▸ hm_td)).2
  have hmd : π.nodeVertex m ∈ (π.cellGraph d).vertexSet := π.p2 d hd m ⟨hm_td, hdom ▸ hmN⟩
  have hbp := border_cell_vertex_mem_borderPlus_of_mem_other π hc₀ hbd₀ htc₀ hmem hd hdc₀ hmd
  rcases hbp with h1 | h2
  · rcases h1 with hbs | ⟨_, hEq⟩
    · exact π.p4_notMem Θ hΘ n₁ hn₁_Θ m (hdom ▸ hmN) hm_not_Θ hbs
    · exact hm_not_Θ (π.nodeVertex_injOn (hdom ▸ hmN) (hdom ▸ hn₁_Θ.1) hEq ▸ hn₁_Θ.2)
  · rcases h2 with hbs | ⟨_, hEq⟩
    · exact π.p4_notMem Θ hΘ n₂ hn₂_Θ m (hdom ▸ hmN) hm_not_Θ hbs
    · exact hm_not_Θ (π.nodeVertex_injOn (hdom ▸ hmN) (hdom ▸ hn₂_Θ.1) hEq ▸ hn₂_Θ.2)

theorem tilde_border_cell_subset_bd {S : Type} [TopologicalSpace S] (Γ : Painting S)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    tilde c ⊆ bd S := by
  obtain ⟨u, v, _, htc, _, _, hu, hv⟩ := Γ.border_cell_exists_ends hc hbd
  rw [htc]
  rintro x (rfl | rfl)
  · exact hu.2
  · exact hv.2

theorem internal_nodeVertex_mem_cellGraph_iff
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ d ∈ π.Γ.C, n ∈ tilde d)
    {n_star : π.S} (hn_star : n_star ∈ π.Γ.N \ bd π.S)
    {c : Set π.S} (hc : c ∈ π.Γ.C) :
    π.nodeVertex n_star ∈ (π.cellGraph c).vertexSet ↔ n_star ∈ tilde c := by
  constructor
  · intro hmem
    obtain ⟨c_star, hc_star, hn_tc_star⟩ := hnode_cell n_star hn_star.1
    have hmem_star : π.nodeVertex n_star ∈ (π.cellGraph c_star).vertexSet :=
      π.p2 c_star hc_star n_star ⟨hn_tc_star, hdom ▸ hn_star.1⟩
    by_cases hcc : c = c_star
    · exact hcc ▸ hn_tc_star
    · by_cases hbd : (c ∩ bd π.S).Nonempty
      · exfalso
        obtain ⟨m, hm_tc, hbp⟩ := π.p6 c hc hbd (π.nodeVertex n_star) hmem ⟨c_star, hc_star,
          Ne.symm hcc, hmem_star⟩
        have hmN : m ∈ π.Γ.N := π.Γ.tilde_subset_N hc hm_tc
        have hmbd : m ∈ bd π.S := tilde_border_cell_subset_bd π.Γ hc hbd hm_tc
        let Θ' := connectedComponentIn (bd π.S) m
        have hΘ' : Θ' ∈ cuffs π.S := ⟨m, hmbd, rfl⟩
        have hm_Θ' : m ∈ π.Γ.N ∩ Θ' := ⟨hmN, mem_connectedComponentIn hmbd⟩
        have hn_not_Θ' : n_star ∉ Θ' := fun h => hn_star.2 (connectedComponentIn_subset
          (bd π.S) m h)
        rcases hbp with hbs | ⟨_, hEq⟩
        · exact π.p4_notMem Θ' hΘ' m hm_Θ' n_star (hdom ▸ hn_star.1) hn_not_Θ' hbs
        · exact hn_star.2 (π.nodeVertex_injOn (hdom ▸ hn_star.1) (hdom ▸ hmN) hEq ▸ hmbd)
      · obtain ⟨m, ⟨hm_tc, hm_dom⟩, hEq⟩ :=
          π.p5 c hc hbd (π.nodeVertex n_star) hmem ⟨c_star, hc_star, Ne.symm hcc, hmem_star⟩
        exact π.nodeVertex_injOn (hdom ▸ hn_star.1) hm_dom hEq.symm ▸ hm_tc
  · intro hn_tc
    exact π.p2 c hc n_star ⟨hn_tc, hdom ▸ hn_star.1⟩

theorem isTruer_of_le_lt {α : Type u} {β : Type v} {G₁ G₂ : Hypergraph α β}
    {π₁ : Portrayal G₁} {π₂ : Portrayal G₂} {k₀ : Fin 6}
    (hle : ∀ i : Fin 6, i ≤ k₀ → π₁.truth i ≤ π₂.truth i)
    (hlt : π₁.truth k₀ < π₂.truth k₀) :
    π₁.IsTruer π₂ := by
  classical
  let P : ℕ → Prop := fun n => ∃ h : n < 6, π₁.truth ⟨n, h⟩ < π₂.truth ⟨n, h⟩
  have hex : ∃ n, P n := ⟨k₀.1, k₀.2, hlt⟩
  let n := Nat.find hex
  obtain ⟨hn6, hn_lt⟩ := Nat.find_spec hex
  have hn_le : n ≤ k₀.1 := Nat.find_min' hex ⟨k₀.2, hlt⟩
  refine ⟨⟨n, hn6⟩, fun i hi => ?_, hn_lt⟩
  have hi_not : ¬ P i.1 := Nat.find_min hex hi
  have hi_le : π₁.truth i ≤ π₂.truth i := hle i (Fin.le_iff_val_le_val.mpr (hi.le.trans hn_le))
  exact le_antisymm hi_le (not_lt.mp fun h => hi_not ⟨i.2, h⟩)

theorem linkagePairs_symm {α : Type u} (K : SimpleGraph α) (X Y : Set α) (k : ℕ) (x y : α)
    (h : Portrayal.LinkagePairs K X Y k x y) :
    Portrayal.LinkagePairs K Y X k y x := by
  intro P hdisj
  let P' : Fin k → PathFromTo K X Y := fun i =>
    { first := (P i).last
      last := (P i).first
      walk := (P i).walk.reverse
      isPath := (P i).isPath.reverse
      first_mem := (P i).last_mem
      last_mem := (P i).first_mem }
  have hdisj' : Pairwise fun i j =>
      Disjoint {z | z ∈ (P' i).walk.support} {z | z ∈ (P' j).walk.support} := by
    intro i j hij
    refine Set.disjoint_left.mpr fun z hzi hzj => ?_
    change z ∈ (P i).walk.reverse.support at hzi
    change z ∈ (P j).walk.reverse.support at hzj
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hzi hzj
    exact Set.disjoint_left.mp (hdisj hij) hzi hzj
  obtain ⟨i, hf, hl⟩ := h P' hdisj'
  exact ⟨i, hl, hf⟩

open Classical in
private noncomputable abbrev indentNodeMap {X : Type} (old new : X) (x : X) : X :=
  if x = old then new else x

open Classical in
private noncomputable abbrev indentBorderSet {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (A₁ A₂ : Hypergraph α β) (old new n : π.S) : Set α :=
  if n = new then (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex old}
  else π.borderSet n

private noncomputable abbrev indentBorderPlus {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Γ' : Painting π.S) (A₁ A₂ : Hypergraph α β)
    (old new : π.S) (nodeInv : π.S → π.S) (n : π.S) : Set α :=
  {w | w ∈ indentBorderSet π A₁ A₂ old new n ∨ (n ∈ Γ'.N ∧ w = π.nodeVertex (nodeInv n))}

open Classical in
private noncomputable abbrev indented_cuff_portrayal
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ d ∈ π.Γ.C, n ∈ tilde d)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    {n_star : π.S}
    (hne : n₁ ≠ n₂)
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hn_star : n_star ∈ π.Γ.N \ bd π.S)
    {R : Set (Set π.S)}
    (hc₀_R : c₀ ∈ R)
    (hR_cases : ∀ c ∈ R, c = c₀ ∨ ¬(c ∩ bd π.S).Nonempty ∧ tilde c = {n₁, n₂, n_star})
    {Γ' : Painting π.S}
    {A₁' : Hypergraph α β}
    {A₂' : Hypergraph α β}
    (hA₁'_le : A₁' ≤ G)
    (hA₂'_le : A₂' ≤ G)
    (hV_union : (π.cellsUnion R).vertexSet ⊆ A₁'.vertexSet ∪ A₂'.vertexSet)
    (hV_sub : A₁'.vertexSet ∪ A₂'.vertexSet ⊆ (π.cellsUnion R).vertexSet ∪ {π.nodeVertex n_star})
    (hE_union : A₁'.edgeSet ∪ A₂'.edgeSet = (π.cellsUnion R).edgeSet)
    (hE_disj : Disjoint A₁'.edgeSet A₂'.edgeSet)
    (hbp₁ : π.borderPlus n₁ ⊆ A₁'.vertexSet)
    (hbp₂ : π.borderPlus n₂ ⊆ A₂'.vertexSet)
    (hn_star_mem : π.nodeVertex n_star ∈ A₁'.vertexSet ∩ A₂'.vertexSet)
    (hbs_sub : (A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n_star} ⊆ (π.cellGraph
      c₀).vertexSet)
    (hbs₁_le : (π.borderSet n₁).ncard ≤ π.warpAt Θ)
    (hbs₂_le : (π.borderSet n₂).ncard ≤ π.warpAt Θ)
    (hbs_star_le : ((A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n_star}).ncard ≤ π.warpAt Θ)
    (hlp₁ : (π.borderPlus n₁).ncard = π.warpAt Θ + 1 → (A₁'.vertexSet ∩ A₂'.vertexSet).ncard =
      π.warpAt Θ + 1 → Portrayal.LinkagePairs A₁'.skeleton (π.borderPlus n₁) (A₁'.vertexSet ∩
      A₂'.vertexSet) (π.warpAt Θ + 1) (π.nodeVertex n₁) (π.nodeVertex n_star))
    (hlp₂ : (π.borderPlus n₂).ncard = π.warpAt Θ + 1 → (A₁'.vertexSet ∩ A₂'.vertexSet).ncard =
      π.warpAt Θ + 1 → Portrayal.LinkagePairs A₂'.skeleton (π.borderPlus n₂) (A₁'.vertexSet ∩
      A₂'.vertexSet) (π.warpAt Θ + 1) (π.nodeVertex n₂) (π.nodeVertex n_star))
    [T2Space π.S]
    (n_star' : π.S)
    (c₁ : Set π.S)
    (c₂ : Set π.S)
    (cellMap : Set π.S → Set π.S)
    (hn_star'_mem : n_star' ∈ c₀ ∩ Θ)
    (hN' : Γ'.N = π.Γ.N \ {n_star} ∪ {n_star'})
    (hc₁_C' : c₁ ∈ Γ'.C)
    (hc₂_C' : c₂ ∈ Γ'.C)
    (hc₁₂_ne : c₁ ≠ c₂)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (hc₂_Θ : (c₂ ∩ Θ).Nonempty)
    (htc₁ : tilde c₁ = {n₁, n_star'})
    (htc₂ : tilde c₂ = {n₂, n_star'})
    (hbij : BijOn cellMap (Γ'.C \ {c₁, c₂}) (π.Γ.C \ R))
    (hΘ_iff : ∀ d ∈ Γ'.C \ {c₁, c₂}, ∀ Θ' ∈ cuffs π.S, (d ∩ Θ').Nonempty ↔ (cellMap d ∩
      Θ').Nonempty)
    (hbd_iff : ∀ d ∈ Γ'.C \ {c₁, c₂}, (d ∩ bd π.S).Nonempty ↔ (cellMap d ∩ bd π.S).Nonempty)
    (htilde_map : ∀ d ∈ Γ'.C \ {c₁, c₂}, tilde d = (fun x => if x = n_star then n_star' else x) ''
      tilde (cellMap d))
    (hΘ_bd : Θ ⊆ bd π.S)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S)
    (hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S)
    (hn_star'_bd : n_star' ∈ bd π.S)
    (hn_star'_not_N : n_star' ∉ π.Γ.N)
    (hn_star'_ne_star : n_star' ≠ n_star)
    (hn₁_ne_star : n₁ ≠ n_star)
    (hn₂_ne_star : n₂ ≠ n_star)
    (hn₁_ne_star' : n₁ ≠ n_star')
    (hn₂_ne_star' : n₂ ≠ n_star')
    (hn_star'_N' : n_star' ∈ Γ'.N)
    (hn₁_N' : n₁ ∈ Γ'.N)
    (hn₂_N' : n₂ ∈ Γ'.N)
    (hnodeMap_inv : ∀ x ∈ π.Γ.N, (indentNodeMap n_star' n_star) ((indentNodeMap n_star n_star')
      x) = x)
    (hnodeMap_injOn : InjOn (indentNodeMap n_star n_star') π.Γ.N)
    (hnodeInv_mem : ∀ n ∈ Γ'.N, (indentNodeMap n_star' n_star) n ∈ π.Γ.N)
    (hnodeInv_injOn : InjOn (indentNodeMap n_star' n_star) Γ'.N)
    (cellG' : Set π.S → Hypergraph α β)
    (hcellG'_c₁ : cellG' c₁ = A₁')
    (hcellG'_c₂ : cellG' c₂ = A₂')
    (hcellG'_other : ∀ d ∈ Γ'.C \ {c₁, c₂}, cellG' d = π.cellGraph (cellMap d))
    (hcellMap_mem : ∀ d ∈ Γ'.C \ {c₁, c₂}, cellMap d ∈ π.Γ.C \ R)
    (hnodeV'_star' : (π.nodeVertex ∘ (indentNodeMap n_star' n_star)) n_star' = π.nodeVertex
      n_star)
    (hnodeV'_other : ∀ (n : π.S), n ≠ n_star' → (π.nodeVertex ∘ (indentNodeMap n_star' n_star))
      n = π.nodeVertex n)
    (hnodeV'_map : ∀ x ∈ π.Γ.N, (π.nodeVertex ∘ (indentNodeMap n_star' n_star)) ((indentNodeMap
      n_star n_star') x) = π.nodeVertex x)
    (hbp'_star' : (indentBorderPlus π Γ' A₁' A₂' n_star n_star' (indentNodeMap n_star' n_star))
      n_star' = A₁'.vertexSet ∩ A₂'.vertexSet)
    (hbp'_other : ∀ n ∈ π.Γ.N, n ≠ n_star → (indentBorderPlus π Γ' A₁' A₂' n_star n_star'
      (indentNodeMap n_star' n_star)) n = π.borderPlus n)
    (hbp'_other_bd : ∀ n ∈ π.Γ.N, n ∈ bd π.S → (indentBorderPlus π Γ' A₁' A₂' n_star n_star'
      (indentNodeMap n_star' n_star)) n = π.borderPlus n)
    (hborder_not_star : ∀ d ∈ Γ'.C \ {c₁, c₂}, (d ∩ bd π.S).Nonempty → n_star ∉ tilde (cellMap d)
      ∧ tilde d = tilde (cellMap d) ∧ n_star' ∉ tilde d) : Portrayal G :=
  let nodeMap := indentNodeMap n_star n_star'
  let nodeInv := indentNodeMap n_star' n_star
  let borderS' := indentBorderSet π A₁' A₂' n_star n_star'
  let nodeV' := π.nodeVertex ∘ nodeInv
  let bp' := indentBorderPlus π Γ' A₁' A₂' n_star n_star' nodeInv
  have hnodeV'_star' : nodeV' n_star' = π.nodeVertex n_star := hnodeV'_star'
  have hnodeV'_other : ∀ n ≠ n_star', nodeV' n = π.nodeVertex n := hnodeV'_other
  have hnodeV'_map : ∀ x ∈ π.Γ.N, nodeV' (nodeMap x) = π.nodeVertex x := hnodeV'_map
  have hbp'_star' : bp' n_star' = A₁'.vertexSet ∩ A₂'.vertexSet := hbp'_star'
  have hbp'_other : ∀ n ∈ π.Γ.N, n ≠ n_star → bp' n = π.borderPlus n := hbp'_other
  have hbp'_other_bd : ∀ n ∈ π.Γ.N, n ∈ bd π.S → bp' n = π.borderPlus n := hbp'_other_bd
  { S := π.S
    isSurface := π.isSurface
    connected := π.connected
    Γ := Γ'
    cellGraph := cellG'
    borderSet := borderS'
    domγ := Γ'.N
    nodeVertex := nodeV'
    cellGraph_le := by
      intro d hd
      by_cases hd₁ : d = c₁
      · subst hd₁; rw [hcellG'_c₁]; exact hA₁'_le
      · by_cases hd₂ : d = c₂
        · subst hd₂; rw [hcellG'_c₂]; exact hA₂'_le
        · have hd_diff : d ∈ Γ'.C \ {c₁, c₂} := ⟨hd, by rintro (rfl | rfl) <;> contradiction⟩
          rw [hcellG'_other d hd_diff]
          exact π.cellGraph_le (cellMap d) (hcellMap_mem d hd_diff).1
    borderSet_subset := by
      intro n hn
      dsimp [borderS', indentBorderSet]
      split_ifs with h
      · exact sdiff_subset.trans (inter_subset_left.trans hA₁'_le.1)
      · have hn_N : n ∈ π.Γ.N := by
          have := hn.1
          rw [hN'] at this
          rcases this with ⟨hnN, _⟩ | hn_eq
          · exact hnN
          · exact (h hn_eq).elim
        exact π.borderSet_subset n ⟨hn_N, hn.2⟩
    domγ_subset := Subset.rfl
    nodeVertex_mem := fun n hn => π.nodeVertex_mem (nodeInv n) (hdom ▸ hnodeInv_mem n hn)
    nodeVertex_injOn := by
      intro x hx y hy hEq
      exact hnodeInv_injOn hx hy
        (π.nodeVertex_injOn (hdom ▸ hnodeInv_mem x hx) (hdom ▸ hnodeInv_mem y hy) hEq)
    p1_vertex := by
      intro v hv
      obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
      by_cases hcR : c ∈ R
      · have hv_cu : v ∈ (π.cellsUnion R).vertexSet :=
          mem_iUnion₂.mpr ⟨c, ⟨hcR, hc⟩, hvc⟩
        rcases hV_union hv_cu with hv₁ | hv₂
        · exact ⟨c₁, hc₁_C', hcellG'_c₁.symm ▸ hv₁⟩
        · exact ⟨c₂, hc₂_C', hcellG'_c₂.symm ▸ hv₂⟩
      · obtain ⟨d, hd_diff, hd_eq⟩ := hbij.surjOn ⟨hc, hcR⟩
        exact ⟨d, hd_diff.1, by rw [hcellG'_other d hd_diff, hd_eq]; exact hvc⟩
    p1_edge := by
      intro e he
      obtain ⟨c, hc, hec⟩ := π.p1_edge e he
      by_cases hcR : c ∈ R
      · have he_cu : e ∈ (π.cellsUnion R).edgeSet :=
          mem_iUnion₂.mpr ⟨c, ⟨hcR, hc⟩, hec⟩
        rw [← hE_union] at he_cu
        rcases he_cu with he₁ | he₂
        · exact ⟨c₁, hc₁_C', hcellG'_c₁.symm ▸ he₁⟩
        · exact ⟨c₂, hc₂_C', hcellG'_c₂.symm ▸ he₂⟩
      · obtain ⟨d, hd_diff, hd_eq⟩ := hbij.surjOn ⟨hc, hcR⟩
        exact ⟨d, hd_diff.1, by rw [hcellG'_other d hd_diff, hd_eq]; exact hec⟩
    p1_disjoint := by
      intro d₁ hd₁ d₂ hd₂ hne_d
      have hdisj_R : ∀ i_e ∈ (π.cellsUnion R).edgeSet, ∀ d ∈ Γ'.C \ {c₁, c₂},
          i_e ∉ (cellG' d).edgeSet := by
        intro e he d hd_diff hed
        rw [hcellG'_other d hd_diff] at hed
        rcases mem_iUnion₂.mp he with ⟨c, ⟨hcR, hcC⟩, hec⟩
        have hcd_ne : c ≠ cellMap d := fun h => (hcellMap_mem d hd_diff).2 (h ▸ hcR)
        exact Set.disjoint_left.mp (π.p1_disjoint c hcC (cellMap d)
          (hcellMap_mem d hd_diff).1 hcd_ne) hec hed
      by_cases hd₁_pair : d₁ = c₁ ∨ d₁ = c₂ <;> by_cases hd₂_pair : d₂ = c₁ ∨ d₂ = c₂
      · rcases hd₁_pair with rfl | rfl <;> rcases hd₂_pair with rfl | rfl
        · exact (hne_d rfl).elim
        · rw [hcellG'_c₁, hcellG'_c₂]; exact hE_disj
        · rw [hcellG'_c₂, hcellG'_c₁]; exact hE_disj.symm
        · exact (hne_d rfl).elim
      · have hd₂_diff : d₂ ∈ Γ'.C \ {c₁, c₂} := ⟨hd₂, hd₂_pair⟩
        refine Set.disjoint_left.mpr fun e he₁ he₂ => hdisj_R e ?_ d₂ hd₂_diff he₂
        rw [← hE_union]
        rcases hd₁_pair with rfl | rfl
        · exact Or.inl (hcellG'_c₁ ▸ he₁)
        · exact Or.inr (hcellG'_c₂ ▸ he₁)
      · have hd₁_diff : d₁ ∈ Γ'.C \ {c₁, c₂} := ⟨hd₁, hd₁_pair⟩
        refine Set.disjoint_left.mpr fun e he₁ he₂ => hdisj_R e ?_ d₁ hd₁_diff he₁
        rw [← hE_union]
        rcases hd₂_pair with rfl | rfl
        · exact Or.inl (hcellG'_c₁ ▸ he₂)
        · exact Or.inr (hcellG'_c₂ ▸ he₂)
      · have hd₁_diff : d₁ ∈ Γ'.C \ {c₁, c₂} := ⟨hd₁, hd₁_pair⟩
        have hd₂_diff : d₂ ∈ Γ'.C \ {c₁, c₂} := ⟨hd₂, hd₂_pair⟩
        rw [hcellG'_other d₁ hd₁_diff, hcellG'_other d₂ hd₂_diff]
        exact π.p1_disjoint (cellMap d₁) (hcellMap_mem d₁ hd₁_diff).1
          (cellMap d₂) (hcellMap_mem d₂ hd₂_diff).1
          (fun h => hne_d (hbij.injOn hd₁_diff hd₂_diff h))
    p2 := by
      intro d hd n ⟨hn_td, _⟩
      by_cases hd₁ : d = c₁
      · rw [hd₁, hcellG'_c₁]
        rw [hd₁, htc₁] at hn_td
        rcases hn_td with hn_eq | hn_eq
        · rw [hn_eq, hnodeV'_other n₁ hn₁_ne_star']
          exact hbp₁ (Or.inr ⟨hdom ▸ hn₁_Θ.1, rfl⟩)
        · rw [mem_singleton_iff.mp hn_eq, hnodeV'_star']
          exact hn_star_mem.1
      · by_cases hd₂ : d = c₂
        · rw [hd₂, hcellG'_c₂]
          rw [hd₂, htc₂] at hn_td
          rcases hn_td with hn_eq | hn_eq
          · rw [hn_eq, hnodeV'_other n₂ hn₂_ne_star']
            exact hbp₂ (Or.inr ⟨hdom ▸ hn₂_Θ.1, rfl⟩)
          · rw [mem_singleton_iff.mp hn_eq, hnodeV'_star']
            exact hn_star_mem.2
        · have hd_diff : d ∈ Γ'.C \ {c₁, c₂} :=
            ⟨hd, by simp [hd₁, hd₂]⟩
          rw [hcellG'_other d hd_diff]
          rw [htilde_map d hd_diff] at hn_td
          rcases hn_td with ⟨x, hx_tc, rfl⟩
          have hxN : x ∈ π.Γ.N := π.Γ.tilde_subset_N (hcellMap_mem d hd_diff).1 hx_tc
          rw [hnodeV'_map x hxN]
          exact π.p2 (cellMap d) (hcellMap_mem d hd_diff).1 x ⟨hx_tc, hdom ▸ hxN⟩
    p3_notMem := by
      intro n hn
      dsimp [borderS', indentBorderSet]
      split_ifs with h
      · rw [h, hnodeV'_star']
        exact fun hmem => hmem.2 rfl
      · have hn_N : n ∈ π.Γ.N := by
          have := hn.1
          rw [hN'] at this
          rcases this with ⟨hnN, _⟩ | hn_eq
          · exact hnN
          · exact (h (mem_singleton_iff.mp hn_eq)).elim
        rw [hnodeV'_other n h]
        exact π.p3_notMem n ⟨hdom ▸ hn_N, hn.2⟩
    p3_subset := by
      intro d hd hbd_d n hn_td
      by_cases hd₁ : d = c₁
      · rw [hd₁, hcellG'_c₁]
        rw [hd₁, htc₁] at hn_td
        rcases hn_td with hn_eq | hn_eq
        · rw [hn_eq]; dsimp [borderS', indentBorderSet]
          simp only [hn₁_ne_star', ↓reduceIte]
          exact fun _ h => hbp₁ (Or.inl h)
        · rw [mem_singleton_iff.mp hn_eq]; dsimp [borderS', indentBorderSet]
          simp only [↓reduceIte]
          exact sdiff_subset.trans inter_subset_left
      · by_cases hd₂ : d = c₂
        · rw [hd₂, hcellG'_c₂]
          rw [hd₂, htc₂] at hn_td
          rcases hn_td with hn_eq | hn_eq
          · rw [hn_eq]; dsimp [borderS', indentBorderSet]
            simp only [hn₂_ne_star', ↓reduceIte]
            exact fun _ h => hbp₂ (Or.inl h)
          · rw [mem_singleton_iff.mp hn_eq]; dsimp [borderS', indentBorderSet]
            simp only [↓reduceIte]
            exact sdiff_subset.trans inter_subset_right
        · have hd_diff : d ∈ Γ'.C \ {c₁, c₂} :=
            ⟨hd, by simp [hd₁, hd₂]⟩
          obtain ⟨_, htd_eq, hnot_s'⟩ := hborder_not_star d hd_diff hbd_d
          have hn_ne_s' : n ≠ n_star' := fun h => hnot_s' (h ▸ hn_td)
          rw [hcellG'_other d hd_diff]
          dsimp [borderS', indentBorderSet]
          simp only [hn_ne_s', ↓reduceIte]
          exact π.p3_subset (cellMap d) (hcellMap_mem d hd_diff).1
            ((hbd_iff d hd_diff).mp hbd_d) n (htd_eq ▸ hn_td)
    p4_disjoint := by
      intro Θ₁ hΘ₁ Θ₂ hΘ₂ hΘ_ne m₁ hm₁ m₂ hm₂
      have hΘ₁_bd : Θ₁ ⊆ bd π.S := by
        rcases hΘ₁ with ⟨x, _, rfl⟩
        exact connectedComponentIn_subset _ x
      have hΘ₂_bd : Θ₂ ⊆ bd π.S := by
        rcases hΘ₂ with ⟨x, _, rfl⟩
        exact connectedComponentIn_subset _ x
      have hΘ_disj : Disjoint Θ₁ Θ₂ := by
        rcases hΘ₁ with ⟨x₁, _, rfl⟩; rcases hΘ₂ with ⟨x₂, _, rfl⟩
        exact Set.disjoint_left.mpr fun z hz₁ hz₂ => hΘ_ne
          ((connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₂).symm)
      refine Set.disjoint_left.mpr fun w hw₁ hw₂ => ?_
      dsimp [borderS', indentBorderSet] at hw₁ hw₂
      split_ifs at hw₁ with hm₁_s <;> split_ifs at hw₂ with hm₂_s
      · rw [hm₁_s] at hm₁; rw [hm₂_s] at hm₂
        exact (Set.disjoint_left.mp hΘ_disj hm₁.2 hm₂.2).elim
      · have hΘ₁_eq : Θ₁ = Θ := by
          rcases hΘ₁ with ⟨x₁, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
          exact (connectedComponentIn_eq (hm₁_s ▸ hm₁.2)).trans (connectedComponentIn_eq
            hn_star'_mem.2).symm
        have hm₂_N : m₂ ∈ π.Γ.N := by
          have := hm₂.1; rw [hN'] at this
          exact (this.resolve_right hm₂_s).1
        have hw_c₀ : w ∈ (π.cellGraph c₀).vertexSet := hbs_sub hw₁
        have hbp_u := border_cell_vertex_inter_borderPlus_subset π hc₀ hbd₀ htc₀
          ⟨hm₂_N, hΘ₂_bd hm₂.2⟩ hw_c₀ (Or.inl hw₂)
        rcases hbp_u with (hw_n₁ | ⟨_, hEq⟩) | (hw_n₂ | ⟨_, hEq⟩)
        · exact Set.disjoint_left.mp (π.p4_disjoint Θ hΘ Θ₂ hΘ₂ (hΘ₁_eq ▸ hΘ_ne) n₁ hn₁_Θ m₂
          ⟨hm₂_N, hm₂.2⟩) hw_n₁ hw₂
        · have hn₁_not_Θ₂ : n₁ ∉ Θ₂ := Set.disjoint_left.mp (hΘ₁_eq ▸ hΘ_disj) hn₁_Θ.2
          exact π.p4_notMem Θ₂ hΘ₂ m₂ ⟨hm₂_N, hm₂.2⟩ n₁ (hdom ▸ hn₁_Θ.1) hn₁_not_Θ₂ (hEq ▸ hw₂)
        · exact Set.disjoint_left.mp (π.p4_disjoint Θ hΘ Θ₂ hΘ₂ (hΘ₁_eq ▸ hΘ_ne) n₂ hn₂_Θ m₂
          ⟨hm₂_N, hm₂.2⟩) hw_n₂ hw₂
        · have hn₂_not_Θ₂ : n₂ ∉ Θ₂ := Set.disjoint_left.mp (hΘ₁_eq ▸ hΘ_disj) hn₂_Θ.2
          exact π.p4_notMem Θ₂ hΘ₂ m₂ ⟨hm₂_N, hm₂.2⟩ n₂ (hdom ▸ hn₂_Θ.1) hn₂_not_Θ₂ (hEq ▸ hw₂)
      · have hΘ₂_eq : Θ₂ = Θ := by
          rcases hΘ₂ with ⟨x₂, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
          exact (connectedComponentIn_eq (hm₂_s ▸ hm₂.2)).trans (connectedComponentIn_eq
            hn_star'_mem.2).symm
        have hm₁_N : m₁ ∈ π.Γ.N := by
          have := hm₁.1; rw [hN'] at this
          exact (this.resolve_right hm₁_s).1
        have hw_c₀ : w ∈ (π.cellGraph c₀).vertexSet := hbs_sub hw₂
        have hbp_u := border_cell_vertex_inter_borderPlus_subset π hc₀ hbd₀ htc₀
          ⟨hm₁_N, hΘ₁_bd hm₁.2⟩ hw_c₀ (Or.inl hw₁)
        rcases hbp_u with (hw_n₁ | ⟨_, hEq⟩) | (hw_n₂ | ⟨_, hEq⟩)
        · exact Set.disjoint_left.mp (π.p4_disjoint Θ₁ hΘ₁ Θ hΘ (hΘ₂_eq ▸ hΘ_ne) m₁ ⟨hm₁_N,
            hm₁.2⟩ n₁ hn₁_Θ) hw₁ hw_n₁
        · have hn₁_not_Θ₁ : n₁ ∉ Θ₁ := Set.disjoint_right.mp (hΘ₂_eq ▸ hΘ_disj) hn₁_Θ.2
          exact π.p4_notMem Θ₁ hΘ₁ m₁ ⟨hm₁_N, hm₁.2⟩ n₁ (hdom ▸ hn₁_Θ.1) hn₁_not_Θ₁ (hEq ▸ hw₁)
        · exact Set.disjoint_left.mp (π.p4_disjoint Θ₁ hΘ₁ Θ hΘ (hΘ₂_eq ▸ hΘ_ne) m₁ ⟨hm₁_N,
            hm₁.2⟩ n₂ hn₂_Θ) hw₁ hw_n₂
        · have hn₂_not_Θ₁ : n₂ ∉ Θ₁ := Set.disjoint_right.mp (hΘ₂_eq ▸ hΘ_disj) hn₂_Θ.2
          exact π.p4_notMem Θ₁ hΘ₁ m₁ ⟨hm₁_N, hm₁.2⟩ n₂ (hdom ▸ hn₂_Θ.1) hn₂_not_Θ₁ (hEq ▸ hw₁)
      · have hm₁_N : m₁ ∈ π.Γ.N := by
          have := hm₁.1; rw [hN'] at this; exact (this.resolve_right hm₁_s).1
        have hm₂_N : m₂ ∈ π.Γ.N := by
          have := hm₂.1; rw [hN'] at this; exact (this.resolve_right hm₂_s).1
        exact Set.disjoint_left.mp
          (π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hΘ_ne m₁ ⟨hm₁_N, hm₁.2⟩ m₂ ⟨hm₂_N, hm₂.2⟩) hw₁ hw₂
    p4_notMem := by
      intro Θ₁ hΘ₁ m₁ hm₁ m₂ hm₂ hm₂_not_Θ₁ hmem
      have hΘ₁_bd : Θ₁ ⊆ bd π.S := by
        rcases hΘ₁ with ⟨x, _, rfl⟩
        exact connectedComponentIn_subset _ x
      dsimp [borderS', indentBorderSet] at hmem
      split_ifs at hmem with hm₁_s
      · have hΘ₁_eq : Θ₁ = Θ := by
          rcases hΘ₁ with ⟨x₁, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
          exact (connectedComponentIn_eq (hm₁_s ▸ hm₁.2)).trans (connectedComponentIn_eq
            hn_star'_mem.2).symm
        have hm₂_ne_s' : m₂ ≠ n_star' := fun h => hm₂_not_Θ₁ (h ▸ hm₁_s ▸ hm₁.2)
        have hm₂_N : m₂ ∈ π.Γ.N := by
          rw [hN'] at hm₂; exact (hm₂.resolve_right hm₂_ne_s').1
        rw [hnodeV'_other m₂ hm₂_ne_s'] at hmem
        exact nodeVertex_notMem_border_cellGraph_of_notMem_cuff π hdom hnode_cell
          hΘ hc₀ hc₀_Θ htc₀ hm₂_N (hΘ₁_eq ▸ hm₂_not_Θ₁) (hbs_sub hmem)
      · have hm₁_N : m₁ ∈ π.Γ.N := by
          have := hm₁.1; rw [hN'] at this; exact (this.resolve_right hm₁_s).1
        have hm₂_inv_N : nodeInv m₂ ∈ π.Γ.N := hnodeInv_mem m₂ hm₂
        have hm₂_inv_not_Θ₁ : nodeInv m₂ ∉ Θ₁ := by
          dsimp [nodeInv, indentNodeMap]
          split_ifs with h
          · exact fun hΘ₁_s => hn_star.2 (hΘ₁_bd hΘ₁_s)
          · exact hm₂_not_Θ₁
        exact π.p4_notMem Θ₁ hΘ₁ m₁ ⟨hm₁_N, hm₁.2⟩ (nodeInv m₂) (hdom ▸ hm₂_inv_N) hm₂_inv_not_Θ₁
          hmem
    p5 := by
      intro d hd hint_d w hw ⟨d', hd', hne_d, hw'⟩
      have hbd₁ : (c₁ ∩ bd π.S).Nonempty := hc₁_Θ.mono (inter_subset_inter_right _ hΘ_bd)
      have hbd₂ : (c₂ ∩ bd π.S).Nonempty := hc₂_Θ.mono (inter_subset_inter_right _ hΘ_bd)
      have hd_diff : d ∈ Γ'.C \ {c₁, c₂} :=
        ⟨hd, by rintro (rfl | rfl) <;> [exact hint_d hbd₁; exact hint_d hbd₂]⟩
      let c := cellMap d
      have hc_mem : c ∈ π.Γ.C \ R := hcellMap_mem d hd_diff
      have hint_c : ¬ (c ∩ bd π.S).Nonempty := fun h => hint_d ((hbd_iff d hd_diff).mpr h)
      rw [hcellG'_other d hd_diff] at hw
      have hw_from_other : (∃ c' ∈ π.Γ.C, c' ≠ c ∧ w ∈ (π.cellGraph c').vertexSet) ∨
          w = π.nodeVertex n_star := by
        by_cases hd'_pair : d' = c₁ ∨ d' = c₂
        · have hw_u : w ∈ A₁'.vertexSet ∪ A₂'.vertexSet := by
            rcases hd'_pair with rfl | rfl
            · exact Or.inl (hcellG'_c₁ ▸ hw')
            · exact Or.inr (hcellG'_c₂ ▸ hw')
          rcases hV_sub hw_u with hw_cu | hw_star
          · rcases mem_iUnion₂.mp hw_cu with ⟨c_r, ⟨hc_rR, hc_rC⟩, hwc_r⟩
            exact Or.inl ⟨c_r, hc_rC, fun h => hc_mem.2 (h ▸ hc_rR), hwc_r⟩
          · exact Or.inr (mem_singleton_iff.mp hw_star)
        · have hd'_diff : d' ∈ Γ'.C \ {c₁, c₂} := ⟨hd', hd'_pair⟩
          rw [hcellG'_other d' hd'_diff] at hw'
          exact Or.inl ⟨cellMap d', (hcellMap_mem d' hd'_diff).1,
            fun h => hne_d (hbij.injOn hd'_diff hd_diff h), hw'⟩
      rcases hw_from_other with hex_c' | rfl
      · obtain ⟨x, ⟨hx_tc, hx_dom⟩, rfl⟩ := π.p5 c hc_mem.1 hint_c w hw hex_c'
        have hxN : x ∈ π.Γ.N := hdom ▸ hx_dom
        have hx_td : nodeMap x ∈ tilde d := by
          rw [htilde_map d hd_diff]
          exact ⟨x, hx_tc, rfl⟩
        have hx_N' : nodeMap x ∈ Γ'.N := Γ'.tilde_subset_N hd hx_td
        exact ⟨nodeMap x, ⟨hx_td, hx_N'⟩, hnodeV'_map x hxN⟩
      · have hn_tc : n_star ∈ tilde c :=
          (internal_nodeVertex_mem_cellGraph_iff π hdom hnode_cell hn_star hc_mem.1).mp hw
        have hn'_td : n_star' ∈ tilde d := by
          rw [htilde_map d hd_diff]
          exact ⟨n_star, hn_tc, by simp⟩
        exact ⟨n_star', ⟨hn'_td, hn_star'_N'⟩, hnodeV'_star'⟩
    p6 := by
      intro d hd hbd_d w hw ⟨d', hd', hne_d, hw'⟩
      have hw_R_case : ∀ x ∈ (π.cellsUnion R).vertexSet ∪ {π.nodeVertex n_star},
          (∃ c' ∈ π.Γ.C \ R, x ∈ (π.cellGraph c').vertexSet) →
          x ∈ π.borderPlus n₁ ∪ π.borderPlus n₂ ∪ {π.nodeVertex n_star} := by
        rintro x (hx_cu | hx_s) ⟨c', hc'_mem, hxc'⟩
        · rcases mem_iUnion₂.mp hx_cu with ⟨c_r, ⟨hc_rR, hc_rC⟩, hxc_r⟩
          have hne_c : c' ≠ c_r := fun h => hc'_mem.2 (h ▸ hc_rR)
          rcases hR_cases c_r hc_rR with rfl | ⟨hint_r, htc_r⟩
          · exact Or.inl (border_cell_vertex_mem_borderPlus_of_mem_other π hc₀ hbd₀ htc₀
              hxc_r hc'_mem.1 hne_c hxc')
          · obtain ⟨m, ⟨hm_tc, hm_dom⟩, rfl⟩ :=
              π.p5 c_r hc_rC hint_r x hxc_r ⟨c', hc'_mem.1, hne_c, hxc'⟩
            rw [htc_r] at hm_tc
            rcases hm_tc with rfl | rfl | rfl
            · exact Or.inl (Or.inl (Or.inr ⟨hm_dom, rfl⟩))
            · exact Or.inl (Or.inr (Or.inr ⟨hm_dom, rfl⟩))
            · exact Or.inr rfl
        · exact Or.inr hx_s
      by_cases hd₁ : d = c₁
      · rw [hd₁] at hw hne_d ⊢
        rw [hcellG'_c₁] at hw
        have hw_cases : w ∈ π.borderPlus n₁ ∨ w ∈ A₁'.vertexSet ∩ A₂'.vertexSet := by
          by_cases hd'₂ : d' = c₂
          · rw [hd'₂, hcellG'_c₂] at hw'
            exact Or.inr ⟨hw, hw'⟩
          · have hd'_diff : d' ∈ Γ'.C \ {c₁, c₂} :=
              ⟨hd', by rintro (hd1 | hd2) <;> [exact hne_d hd1; exact hd'₂ hd2]⟩
            rw [hcellG'_other d' hd'_diff] at hw'
            rcases hw_R_case w (hV_sub (Or.inl hw)) ⟨cellMap d', hcellMap_mem d' hd'_diff, hw'⟩
              with
              (hw_n₁ | hw_n₂) | hw_s
            · exact Or.inl hw_n₁
            · exact Or.inr ⟨hw, hbp₂ hw_n₂⟩
            · rw [mem_singleton_iff.mp hw_s]
              exact Or.inr hn_star_mem
        rcases hw_cases with hw_n₁ | hw_inter
        · refine ⟨n₁, htc₁ ▸ Or.inl rfl, ?_⟩
          change w ∈ bp' n₁
          rw [hbp'_other_bd n₁ hn₁_bd.1 hn₁_bd.2]
          exact hw_n₁
        · refine ⟨n_star', htc₁ ▸ Or.inr rfl, ?_⟩
          change w ∈ bp' n_star'
          rw [hbp'_star']
          exact hw_inter
      · by_cases hd₂ : d = c₂
        · rw [hd₂] at hw hne_d ⊢
          rw [hcellG'_c₂] at hw
          have hw_cases : w ∈ π.borderPlus n₂ ∨ w ∈ A₁'.vertexSet ∩ A₂'.vertexSet := by
            by_cases hd'₁ : d' = c₁
            · rw [hd'₁, hcellG'_c₁] at hw'
              exact Or.inr ⟨hw', hw⟩
            · have hd'_diff : d' ∈ Γ'.C \ {c₁, c₂} :=
                ⟨hd', by rintro (hd1 | hd2) <;> [exact hd'₁ hd1; exact hne_d hd2]⟩
              rw [hcellG'_other d' hd'_diff] at hw'
              rcases hw_R_case w (hV_sub (Or.inr hw)) ⟨cellMap d', hcellMap_mem d' hd'_diff, hw'⟩
                with
                (hw_n₁ | hw_n₂) | hw_s
              · exact Or.inr ⟨hbp₁ hw_n₁, hw⟩
              · exact Or.inl hw_n₂
              · rw [mem_singleton_iff.mp hw_s]
                exact Or.inr hn_star_mem
          rcases hw_cases with hw_n₂ | hw_inter
          · refine ⟨n₂, htc₂ ▸ Or.inl rfl, ?_⟩
            change w ∈ bp' n₂
            rw [hbp'_other_bd n₂ hn₂_bd.1 hn₂_bd.2]
            exact hw_n₂
          · refine ⟨n_star', htc₂ ▸ Or.inr rfl, ?_⟩
            change w ∈ bp' n_star'
            rw [hbp'_star']
            exact hw_inter
        · have hd_diff : d ∈ Γ'.C \ {c₁, c₂} :=
            ⟨hd, by simp [hd₁, hd₂]⟩
          obtain ⟨hnot_s, htd_eq, _⟩ := hborder_not_star d hd_diff hbd_d
          let c := cellMap d
          have hc_mem : c ∈ π.Γ.C \ R := hcellMap_mem d hd_diff
          have hbd_c : (c ∩ bd π.S).Nonempty := (hbd_iff d hd_diff).mp hbd_d
          rw [hcellG'_other d hd_diff] at hw
          have hex_c' : ∃ c' ∈ π.Γ.C, c' ≠ c ∧ w ∈ (π.cellGraph c').vertexSet := by
            by_cases hd'_pair : d' = c₁ ∨ d' = c₂
            · have hw_u : w ∈ A₁'.vertexSet ∪ A₂'.vertexSet := by
                rcases hd'_pair with rfl | rfl
                · exact Or.inl (hcellG'_c₁ ▸ hw')
                · exact Or.inr (hcellG'_c₂ ▸ hw')
              rcases hV_sub hw_u with hw_cu | hw_s
              · rcases mem_iUnion₂.mp hw_cu with ⟨c_r, ⟨hc_rR, hc_rC⟩, hwc_r⟩
                exact ⟨c_r, hc_rC, fun h => hc_mem.2 (h ▸ hc_rR), hwc_r⟩
              · exfalso
                rw [mem_singleton_iff] at hw_s
                exact hnot_s ((internal_nodeVertex_mem_cellGraph_iff π hdom hnode_cell hn_star
                  hc_mem.1).mp (hw_s ▸ hw))
            · have hd'_diff : d' ∈ Γ'.C \ {c₁, c₂} := ⟨hd', hd'_pair⟩
              rw [hcellG'_other d' hd'_diff] at hw'
              exact ⟨cellMap d', (hcellMap_mem d' hd'_diff).1,
                fun h => hne_d (hbij.injOn hd'_diff hd_diff h), hw'⟩
          obtain ⟨m, hm_tc, hbp_m⟩ := π.p6 c hc_mem.1 hbd_c w hw hex_c'
          have hmN : m ∈ π.Γ.N := π.Γ.tilde_subset_N hc_mem.1 hm_tc
          have hmbd : m ∈ bd π.S := tilde_border_cell_subset_bd π.Γ hc_mem.1 hbd_c hm_tc
          refine ⟨m, htd_eq ▸ hm_tc, ?_⟩
          change w ∈ bp' m
          rw [hbp'_other_bd m hmN hmbd]
          exact hbp_m
    p7 := by
      intro Θ₁ hΘ₁ m₁ hm₁ m₂ hm₂ m₃ hm₃ m₄ hm₄ hord w hw₁ hw₃
      have hΘ₁_bd : Θ₁ ⊆ bd π.S := by
        rcases hΘ₁ with ⟨x, _, rfl⟩
        exact connectedComponentIn_subset _ x
      have hp7_aux : ∀ a b c d_n : π.S,
          a ∈ Γ'.N ∩ Θ₁ → b ∈ Γ'.N ∩ Θ₁ → c ∈ Γ'.N ∩ Θ₁ → d_n ∈ Γ'.N ∩ Θ₁ →
          a ≠ b → b ≠ c → c ≠ d_n → d_n ≠ a →
          GM19.InOrderOn Θ₁ a b c d_n →
          (a = n_star' ∨ b = n_star' ∨ (a ≠ n_star' ∧ b ≠ n_star' ∧ c ≠ n_star' ∧ d_n ≠ n_star'))
            →
          w ∈ bp' a → w ∈ bp' c →
          w ∈ bp' b ∨ w ∈ bp' d_n := by
        intro a b c d_n ha hb hc hd_n hab hbc hcd hda hord' hcases hwa hwc
        have hN_of_ne : ∀ x ∈ Γ'.N ∩ Θ₁, x ≠ n_star' → x ∈ π.Γ.N ∩ Θ₁ := by
          intro x hx hx_ne
          have := hx.1; rw [hN'] at this
          exact ⟨(this.resolve_right hx_ne).1, hx.2⟩
        rcases hcases with ha_eq | hb_eq | ⟨ha_ne, hb_ne, hc_ne, hd_ne⟩
        · have hΘ₁_eq : Θ₁ = Θ := by
            rcases hΘ₁ with ⟨x₁, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
            exact (connectedComponentIn_eq (ha_eq ▸ ha.2)).trans (connectedComponentIn_eq
              hn_star'_mem.2).symm
          rw [ha_eq] at hab hda hord' hwa
          rw [hΘ₁_eq] at hb hc hd_n hord' hN_of_ne
          have hb_ne : b ≠ n_star' := Ne.symm hab
          have hd_ne : d_n ≠ n_star' := hda
          have hc_ne : c ≠ n_star' := fun h => by
            rcases eq_of_inOrder (h ▸ hord') with rfl | rfl <;> contradiction
          have hb_Θ := hN_of_ne b hb hb_ne
          have hc_Θ := hN_of_ne c hc hc_ne
          have hd_Θ := hN_of_ne d_n hd_n hd_ne
          rw [hbp'_other_bd b hb_Θ.1 (hΘ_bd hb_Θ.2), hbp'_other_bd d_n hd_Θ.1 (hΘ_bd hd_Θ.2)]
          rw [hbp'_other_bd c hc_Θ.1 (hΘ_bd hc_Θ.2)] at hwc
          have hw_ne_star : w ≠ π.nodeVertex n_star := by
            rintro rfl
            have hc_bd : c ∈ bd π.S := hΘ_bd hc_Θ.2
            have hn_star_not_Θ : n_star ∉ Θ := fun h => hn_star.2 (hΘ_bd h)
            rcases hwc with hbs_c | ⟨_, hEq⟩
            · exact π.p4_notMem Θ hΘ c hc_Θ n_star (hdom ▸ hn_star.1) hn_star_not_Θ hbs_c
            · exact hn_star.2 (π.nodeVertex_injOn (hdom ▸ hn_star.1) (hdom ▸ hc_Θ.1) hEq ▸ hc_bd)
          have hw_bs : w ∈ (A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n_star} := by
            rw [hbp'_star'] at hwa
            exact ⟨hwa, hw_ne_star⟩
          have hw_c₀ : w ∈ (π.cellGraph c₀).vertexSet := hbs_sub hw_bs
          have hbp_u := border_cell_vertex_inter_borderPlus_subset π hc₀ hbd₀ htc₀
            ⟨hc_Θ.1, hΘ_bd hc_Θ.2⟩ hw_c₀ hwc
          have hn_star'_cl : n_star' ∈ closure c₀ := subset_closure hn_star'_mem.1
          rcases hbp_u with hw_n₁ | hw_n₂
          · have hn₁_cl : n₁ ∈ closure c₀ ∩ Θ := ⟨(htc₀ ▸ Or.inl rfl : n₁ ∈ tilde c₀).1, hn₁_Θ.2⟩
            have hord₁ := inOrderOn_of_mem_closure_border_cell_left π.Γ hΘ hc₀ hc₀_Θ
              hab hbc hcd hda hb_Θ.1 hd_Θ.1 hn_star'_cl hord' hn₁_cl
            exact π.p7 Θ hΘ n₁ hn₁_Θ b hb_Θ c hc_Θ d_n hd_Θ hord₁ w hw_n₁ hwc
          · have hn₂_cl : n₂ ∈ closure c₀ ∩ Θ := ⟨(htc₀ ▸ Or.inr rfl : n₂ ∈ tilde c₀).1, hn₂_Θ.2⟩
            have hord₂ := inOrderOn_of_mem_closure_border_cell_left π.Γ hΘ hc₀ hc₀_Θ
              hab hbc hcd hda hb_Θ.1 hd_Θ.1 hn_star'_cl hord' hn₂_cl
            exact π.p7 Θ hΘ n₂ hn₂_Θ b hb_Θ c hc_Θ d_n hd_Θ hord₂ w hw_n₂ hwc
        · have hΘ₁_eq : Θ₁ = Θ := by
            rcases hΘ₁ with ⟨x₁, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
            exact (connectedComponentIn_eq (hb_eq ▸ hb.2)).trans (connectedComponentIn_eq
              hn_star'_mem.2).symm
          rw [hb_eq] at hab hbc hord' ⊢
          rw [hΘ₁_eq] at ha hc hd_n hord' hN_of_ne
          have ha_ne : a ≠ n_star' := hab
          have hc_ne : c ≠ n_star' := Ne.symm hbc
          have hd_ne : d_n ≠ n_star' := fun h => by
            rcases eq_of_inOrder (h ▸ inOrderOn_cyclic hord') with rfl | rfl <;> contradiction
          have ha_Θ := hN_of_ne a ha ha_ne
          have hc_Θ := hN_of_ne c hc hc_ne
          have hd_Θ := hN_of_ne d_n hd_n hd_ne
          rw [hbp'_star', hbp'_other_bd d_n hd_Θ.1 (hΘ_bd hd_Θ.2)]
          rw [hbp'_other_bd a ha_Θ.1 (hΘ_bd ha_Θ.2)] at hwa
          rw [hbp'_other_bd c hc_Θ.1 (hΘ_bd hc_Θ.2)] at hwc
          have hn_star'_cl : n_star' ∈ closure c₀ := subset_closure hn_star'_mem.1
          have hn₁_cl : n₁ ∈ closure c₀ ∩ Θ := ⟨(htc₀ ▸ Or.inl rfl : n₁ ∈ tilde c₀).1, hn₁_Θ.2⟩
          have hn₂_cl : n₂ ∈ closure c₀ ∩ Θ := ⟨(htc₀ ▸ Or.inr rfl : n₂ ∈ tilde c₀).1, hn₂_Θ.2⟩
          have hord₁ := inOrderOn_of_mem_closure_border_cell_mid π.Γ hΘ hc₀ hc₀_Θ
            hab hbc hcd hda ha_Θ.1 hc_Θ.1 hn_star'_cl hord' hn₁_cl
          have hord₂ := inOrderOn_of_mem_closure_border_cell_mid π.Γ hΘ hc₀ hc₀_Θ
            hab hbc hcd hda ha_Θ.1 hc_Θ.1 hn_star'_cl hord' hn₂_cl
          have hp₁ := π.p7 Θ hΘ a ha_Θ n₁ hn₁_Θ c hc_Θ d_n hd_Θ hord₁ w hwa hwc
          have hp₂ := π.p7 Θ hΘ a ha_Θ n₂ hn₂_Θ c hc_Θ d_n hd_Θ hord₂ w hwa hwc
          rcases hp₁ with hw_n₁ | hw_d
          · rcases hp₂ with hw_n₂ | hw_d
            · exact Or.inl ⟨hbp₁ hw_n₁, hbp₂ hw_n₂⟩
            · exact Or.inr hw_d
          · exact Or.inr hw_d
        · have ha_Θ := hN_of_ne a ha ha_ne
          have hb_Θ := hN_of_ne b hb hb_ne
          have hc_Θ := hN_of_ne c hc hc_ne
          have hd_Θ := hN_of_ne d_n hd_n hd_ne
          rw [hbp'_other_bd b hb_Θ.1 (hΘ₁_bd hb_Θ.2), hbp'_other_bd d_n hd_Θ.1 (hΘ₁_bd hd_Θ.2)]
          rw [hbp'_other_bd a ha_Θ.1 (hΘ₁_bd ha_Θ.2)] at hwa
          rw [hbp'_other_bd c hc_Θ.1 (hΘ₁_bd hc_Θ.2)] at hwc
          exact π.p7 Θ₁ hΘ₁ a ha_Θ b hb_Θ c hc_Θ d_n hd_Θ hord' w hwa hwc
      by_cases h12 : m₁ = m₂
      · exact Or.inl (h12 ▸ hw₁)
      by_cases h23 : m₂ = m₃
      · exact Or.inl (h23.symm ▸ hw₃)
      by_cases h34 : m₃ = m₄
      · exact Or.inr (h34 ▸ hw₃)
      by_cases h41 : m₄ = m₁
      · exact Or.inr (h41.symm ▸ hw₁)
      by_cases hm₁_s : m₁ = n_star'
      · exact hp7_aux m₁ m₂ m₃ m₄ hm₁ hm₂ hm₃ hm₄ h12 h23 h34 h41 hord (Or.inl hm₁_s) hw₁ hw₃
      by_cases hm₂_s : m₂ = n_star'
      · exact hp7_aux m₁ m₂ m₃ m₄ hm₁ hm₂ hm₃ hm₄ h12 h23 h34 h41 hord (Or.inr
        (Or.inl hm₂_s)) hw₁ hw₃
      by_cases hm₃_s : m₃ = n_star'
      · exact (hp7_aux m₃ m₄ m₁ m₂ hm₃ hm₄ hm₁ hm₂ h34 h41 h12 h23
          (inOrderOn_cyclic2 hord) (Or.inl hm₃_s) hw₃ hw₁).symm
      by_cases hm₄_s : m₄ = n_star'
      · exact (hp7_aux m₃ m₄ m₁ m₂ hm₃ hm₄ hm₁ hm₂ h34 h41 h12 h23
          (inOrderOn_cyclic2 hord) (Or.inr (Or.inl hm₄_s)) hw₃ hw₁).symm
      exact hp7_aux m₁ m₂ m₃ m₄ hm₁ hm₂ hm₃ hm₄ h12 h23 h34 h41 hord
        (Or.inr (Or.inr ⟨hm₁_s, hm₂_s, hm₃_s, hm₄_s⟩)) hw₁ hw₃ }

/-- A bound on both borders and the required linkage bound the warp of a two-ended cell. -/
theorem Portrayal.cellWarp_le_of_two_ends {α β : Type*} {G : Hypergraph α β}
    (π : Portrayal G) {c : Set π.S} {n m : π.S} {p : ℕ} (ht : tilde c = {n, m})
    (hn : (π.borderSet n).ncard ≤ p) (hm : (π.borderSet m).ncard ≤ p)
    (hlink : (π.borderPlus n).ncard = p + 1 → (π.borderPlus m).ncard = p + 1 →
      Portrayal.LinkagePairs (π.cellGraph c).skeleton (π.borderPlus n) (π.borderPlus m)
        (p + 1) (π.nodeVertex n) (π.nodeVertex m)) :
    π.cellWarp c ≤ p := by
  apply csInf_le (OrderBot.bddBelow _)
  intro u hu v hv huv
  change u ∈ tilde c at hu
  change v ∈ tilde c at hv
  simp only [ht, mem_insert_iff, mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (huv rfl).elim
  · exact ⟨hn, hm, hlink⟩
  · exact ⟨hm, hn, fun h1 h2 => linkagePairs_symm _ _ _ _ _ _ (hlink h2 h1)⟩
  · exact (huv rfl).elim

private theorem isTruer_of_fewer_internal_nodes {α β : Type*} {G : Hypergraph α β}
    (π' π : Portrayal G)
    (hcells : ∀ i : Fin 6, i.1 < 4 → π'.truth i ≤ π.truth i)
    (hnodes : (π'.Γ.N \ bd π'.S).ncard < (π.Γ.N \ bd π.S).ncard) :
    π'.IsTruer π := by
  let k : Fin 6 := ⟨4, by decide⟩
  apply isTruer_of_le_lt (k₀ := k)
  · intro i hi
    rcases lt_or_eq_of_le hi with hlt | rfl
    · exact hcells i hlt
    · simpa only [Portrayal.truth, k, Nat.not_lt.mpr (le_refl 4), ↓reduceIte] using hnodes.le
  · simpa only [Portrayal.truth, k, Nat.not_lt.mpr (le_refl 4), ↓reduceIte] using hnodes

private theorem resembling_of_central_warp_le {α β : Type*} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {π' π : Portrayal G}
    (hπ : π.IsZeroRedundant 𝒯) (hπ' : π'.IsCentral 𝒯)
    (ψ : π'.S ≃ₜ π.S)
    (hwarp : ∀ Θ ∈ cuffs π'.S, π'.warpAt Θ ≤ π.warpAt (ψ '' Θ)) :
    π'.Resembles π := by
  refine ⟨ψ, fun Θ hΘ => le_antisymm (hwarp Θ hΘ) ?_⟩
  by_contra hlt
  exact hπ π' hπ' (Or.inr ⟨ψ, hwarp, Θ, hΘ, lt_of_not_ge hlt⟩)

open Classical in
private theorem unmodified_border_cell_has_same_ends
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {n_star : π.S}
    (hn_star : n_star ∈ π.Γ.N \ bd π.S)
    {R : Set (Set π.S)}
    {Γ' : Painting π.S}
    (n_star' : π.S)
    (c₁ : Set π.S)
    (c₂ : Set π.S)
    (cellMap : Set π.S → Set π.S)
    (hbd_iff : ∀ d ∈ Γ'.C \ {c₁, c₂}, (d ∩ bd π.S).Nonempty ↔ (cellMap d ∩ bd π.S).Nonempty)
    (htilde_map : ∀ d ∈ Γ'.C \ {c₁, c₂}, tilde d = (fun x => if x = n_star then n_star' else x) ''
      tilde (cellMap d))
    (hn_star'_not_N : n_star' ∉ π.Γ.N)
    (hcellMap_mem : ∀ d ∈ Γ'.C \ {c₁, c₂}, cellMap d ∈ π.Γ.C \ R) :
    ∀ d ∈ Γ'.C \ {c₁, c₂}, (d ∩ bd π.S).Nonempty → n_star ∉ tilde (cellMap d) ∧ tilde d = tilde
      (cellMap d) ∧ n_star' ∉ tilde d := by
  intro d hd hbd_d
  have hc_mem := (hcellMap_mem d hd).1
  have hbd_c : (cellMap d ∩ bd π.S).Nonempty := (hbd_iff d hd).mp hbd_d
  have hsub_bd := tilde_border_cell_subset_bd π.Γ hc_mem hbd_c
  have hnot_s : n_star ∉ tilde (cellMap d) := fun h => hn_star.2 (hsub_bd h)
  have htd_eq : tilde d = tilde (cellMap d) := by
    rw [htilde_map d hd]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy_ne : y ≠ n_star := fun h => hnot_s (h ▸ hy)
      simpa [hy_ne] using hy
    · intro hx
      have hx_ne : x ≠ n_star := fun h => hnot_s (h ▸ hx)
      exact ⟨x, hx, by simp [hx_ne]⟩
  refine ⟨hnot_s, htd_eq, ?_⟩
  rw [htd_eq]
  exact fun h => hn_star'_not_N (π.Γ.tilde_subset_N hc_mem h)

open Classical in
private theorem indent_node_inverse_injective
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {n_star : π.S}
    {Γ' : Painting π.S}
    (n_star' : π.S)
    (hN' : Γ'.N = π.Γ.N \ {n_star} ∪ {n_star'})
    (hn_star'_not_N : n_star' ∉ π.Γ.N) :
    InjOn (fun n => if n = n_star' then n_star else n) Γ'.N := by
  let nodeInv := fun n => if n = n_star' then n_star else n
  intro x hx y hy hEq
  rw [hN'] at hx hy
  dsimp [nodeInv] at hEq
  rcases hx with ⟨hxN, hx_ne⟩ | hx_eq <;> rcases hy with ⟨hyN, hy_ne⟩ | hy_eq
  · have hx' : x ≠ n_star' := fun h => hn_star'_not_N (h ▸ hxN)
    have hy' : y ≠ n_star' := fun h => hn_star'_not_N (h ▸ hyN)
    simpa [hx', hy'] using hEq
  · have hx' : x ≠ n_star' := fun h => hn_star'_not_N (h ▸ hxN)
    have hy' : y = n_star' := mem_singleton_iff.mp hy_eq
    simp only [hx', hy', ↓reduceIte] at hEq
    exact (hx_ne hEq).elim
  · have hx' : x = n_star' := mem_singleton_iff.mp hx_eq
    have hy' : y ≠ n_star' := fun h => hn_star'_not_N (h ▸ hyN)
    simp only [hx', hy', ↓reduceIte] at hEq
    exact (hy_ne hEq.symm).elim
  · exact (mem_singleton_iff.mp hx_eq).trans (mem_singleton_iff.mp hy_eq).symm

private theorem central_of_replacing_two_cells {α β : Type*} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {π : Portrayal G} (π' : Portrayal G)
    (c₁ c₂ : Set π'.S)
    (h₁ : ∃ B, (π'.cellGraph c₁, B) ∈ 𝒯) (h₂ : ∃ B, (π'.cellGraph c₂, B) ∈ 𝒯)
    (hπ : π.IsCentral 𝒯) (cellMap : Set π'.S → Set π.S)
    (hmem : ∀ d ∈ π'.Γ.C \ {c₁, c₂}, cellMap d ∈ π.Γ.C)
    (hgraph : ∀ d ∈ π'.Γ.C \ {c₁, c₂}, π'.cellGraph d = π.cellGraph (cellMap d)) :
    π'.IsCentral 𝒯 := by
  intro d hd
  rcases eq_or_ne d c₁ with rfl | hne₁
  · exact h₁
  rcases eq_or_ne d c₂ with rfl | hne₂
  · exact h₂
  have hdiff : d ∈ π'.Γ.C \ {c₁, c₂} := ⟨hd, by simp [hne₁, hne₂]⟩
  rw [hgraph d hdiff]
  exact hπ (cellMap d) (hmem d hdiff)

private theorem ncard_internal_cells_le_of_map {S : Type} [TopologicalSpace S]
    (Γ' Γ : Painting S) (c₁ c₂ : Set S) (cellMap : Set S → Set S) (nodeMap : S → S) (k : ℕ)
    (hbd₁ : (c₁ ∩ bd S).Nonempty) (hbd₂ : (c₂ ∩ bd S).Nonempty)
    (hinjCell : InjOn cellMap (Γ'.C \ {c₁, c₂}))
    (hcellMap_mem : ∀ d ∈ Γ'.C \ {c₁, c₂}, cellMap d ∈ Γ.C)
    (hbd_iff : ∀ d ∈ Γ'.C \ {c₁, c₂}, (d ∩ bd S).Nonempty ↔ (cellMap d ∩ bd S).Nonempty)
    (htilde_map : ∀ d ∈ Γ'.C \ {c₁, c₂}, tilde d = nodeMap '' tilde (cellMap d))
    (hnodeMap_injOn : InjOn nodeMap Γ.N) :
    {d ∈ Γ'.C | ¬ (d ∩ bd S).Nonempty ∧ (tilde d).ncard = k}.ncard ≤
      {d ∈ Γ.C | ¬ (d ∩ bd S).Nonempty ∧ (tilde d).ncard = k}.ncard := by
  have hmaps : MapsTo cellMap
      {d ∈ Γ'.C | ¬ (d ∩ bd S).Nonempty ∧ (tilde d).ncard = k}
      {c ∈ Γ.C | ¬ (c ∩ bd S).Nonempty ∧ (tilde c).ncard = k} := by
    rintro d ⟨hd_C', hint_d, hcard_d⟩
    have hd_diff : d ∈ Γ'.C \ {c₁, c₂} :=
      ⟨hd_C', by rintro (rfl | rfl) <;> [exact hint_d hbd₁; exact hint_d hbd₂]⟩
    have hc_mem := hcellMap_mem d hd_diff
    have hint_c : ¬ (cellMap d ∩ bd S).Nonempty :=
      fun h => hint_d ((hbd_iff d hd_diff).mpr h)
    have hcard_c : (tilde (cellMap d)).ncard = k := by
      rw [← hcard_d, htilde_map d hd_diff]
      exact (hnodeMap_injOn.mono (Γ.tilde_subset_N hc_mem)).ncard_image.symm
    exact ⟨hc_mem, hint_c, hcard_c⟩
  have hinj : InjOn cellMap {d ∈ Γ'.C | ¬ (d ∩ bd S).Nonempty ∧ (tilde d).ncard = k}
    := by
    refine hinjCell.mono fun d ⟨hd_C', hint_d, _⟩ => ?_
    exact ⟨hd_C', by rintro (rfl | rfl) <;> [exact hint_d hbd₁; exact hint_d hbd₂]⟩
  rw [← hinj.ncard_image]
  exact ncard_le_ncard hmaps.image_subset (Γ.finite_cells.subset fun _ h => h.1)

open Classical in
private theorem indent_node_map_and_inverse {S : Type*} (A B : Set S) (x y : S)
    (hx : x ∈ A) (hy : y ∉ A) (hB : B = A \ {x} ∪ {y}) :
    let replace := fun z : S => if z = x then y else z
    let restore := fun z : S => if z = y then x else z
    (∀ z ∈ A, restore (replace z) = z) ∧ InjOn replace A ∧ MapsTo restore B A := by
  intro replace restore
  have hleft : ∀ z ∈ A, restore (replace z) = z := by
    intro z hz
    by_cases h : z = x
    · simp [replace, restore, h]
    · have hzy : z ≠ y := fun he => hy (he ▸ hz)
      simp [replace, restore, h, hzy]
  refine ⟨hleft, fun u hu v hv h => ?_, fun z hz => ?_⟩
  · rw [← hleft u hu, ← hleft v hv, h]
  · rw [hB] at hz
    rcases hz with ⟨hzA, _⟩ | hz
    · have hzy : z ≠ y := fun he => hy (he ▸ hzA)
      simpa [restore, hzy] using hzA
    · simpa [restore, mem_singleton_iff.mp hz] using hx

theorem not_indentedPortrayal
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (π : Portrayal G) (htrue : π.IsTrue 𝒯)
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ d ∈ π.Γ.C, n ∈ tilde d)
    {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C) (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ n₂ n_star : π.S} (hne : n₁ ≠ n₂) (htc₀ : tilde c₀ = {n₁, n₂})
    (hn_star : n_star ∈ π.Γ.N \ bd π.S)
    {R : Set (Set π.S)} (hc₀_R : c₀ ∈ R) (_hR_sub : R ⊆ π.Γ.C)
    (hR_cases : ∀ c ∈ R, c = c₀ ∨ (¬ (c ∩ bd π.S).Nonempty ∧ tilde c = {n₁, n₂, n_star}))
    {Γ' : Painting π.S} (hind : IsIndentedBorderPainting π.Γ Θ c₀ n₁ n₂ n_star R Γ')
    {A₁' A₂' : Hypergraph α β} (hA₁'_le : A₁' ≤ G) (hA₂'_le : A₂' ≤ G)
    (hV_union : (π.cellsUnion R).vertexSet ⊆ A₁'.vertexSet ∪ A₂'.vertexSet)
    (hV_sub : A₁'.vertexSet ∪ A₂'.vertexSet ⊆ (π.cellsUnion R).vertexSet ∪ {π.nodeVertex n_star})
    (hE_union : A₁'.edgeSet ∪ A₂'.edgeSet = (π.cellsUnion R).edgeSet)
    (hE_disj : Disjoint A₁'.edgeSet A₂'.edgeSet)
    (hbp₁ : π.borderPlus n₁ ⊆ A₁'.vertexSet)
    (hbp₂ : π.borderPlus n₂ ⊆ A₂'.vertexSet)
    (hn_star_mem : π.nodeVertex n_star ∈ A₁'.vertexSet ∩ A₂'.vertexSet)
    (hbs_sub : (A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n_star} ⊆ (π.cellGraph c₀).vertexSet)
    (hsmall₁ : ∃ B, (A₁', B) ∈ 𝒯)
    (hsmall₂ : ∃ B, (A₂', B) ∈ 𝒯)
    (hbs₁_le : (π.borderSet n₁).ncard ≤ π.warpAt Θ)
    (hbs₂_le : (π.borderSet n₂).ncard ≤ π.warpAt Θ)
    (hbs_star_le : ((A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n_star}).ncard ≤ π.warpAt Θ)
    (hlp₁ : (π.borderPlus n₁).ncard = π.warpAt Θ + 1 →
      (A₁'.vertexSet ∩ A₂'.vertexSet).ncard = π.warpAt Θ + 1 →
      Portrayal.LinkagePairs A₁'.skeleton (π.borderPlus n₁) (A₁'.vertexSet ∩ A₂'.vertexSet)
        (π.warpAt Θ + 1) (π.nodeVertex n₁) (π.nodeVertex n_star))
    (hlp₂ : (π.borderPlus n₂).ncard = π.warpAt Θ + 1 →
      (A₁'.vertexSet ∩ A₂'.vertexSet).ncard = π.warpAt Θ + 1 →
      Portrayal.LinkagePairs A₂'.skeleton (π.borderPlus n₂) (A₁'.vertexSet ∩ A₂'.vertexSet)
        (π.warpAt Θ + 1) (π.nodeVertex n₂) (π.nodeVertex n_star)) :
    False := by
  classical
  have : T2Space π.S := π.isSurface.2.1
  obtain ⟨n_star', c₁, c₂, cellMap, hn_star'_mem, hN', hc₁_C', hc₂_C', hc₁₂_ne,
    hc₁_Θ, hc₂_Θ, htc₁, htc₂, hbij, hΘ_iff, hbd_iff, htilde_map⟩ := hind
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hsub_cuff₀ := π.Γ.border_cell_subset_cuff hc₀ hΘ hc₀_Θ
  have hbd₀ : (c₀ ∩ bd π.S).Nonempty := hsub_cuff₀.2.1 ▸ hc₀_Θ
  have hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 (htc₀ ▸ Or.inl rfl)
  have hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 (htc₀ ▸ Or.inr rfl)
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := ⟨hn₁_Θ.1, hΘ_bd hn₁_Θ.2⟩
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S := ⟨hn₂_Θ.1, hΘ_bd hn₂_Θ.2⟩
  have hn_star'_bd : n_star' ∈ bd π.S := hΘ_bd hn_star'_mem.2
  have hn_star'_not_N : n_star' ∉ π.Γ.N := (π.Γ.cell_subset_diff hc₀ hn_star'_mem.1).2
  have hn_star'_ne_star : n_star' ≠ n_star := fun h => hn_star.2 (h ▸ hn_star'_bd)
  have hn₁_ne_star : n₁ ≠ n_star := fun h => hn_star.2 (h ▸ hn₁_bd.2)
  have hn₂_ne_star : n₂ ≠ n_star := fun h => hn_star.2 (h ▸ hn₂_bd.2)
  have hn₁_ne_star' : n₁ ≠ n_star' := fun h => hn_star'_not_N (h ▸ hn₁_Θ.1)
  have hn₂_ne_star' : n₂ ≠ n_star' := fun h => hn_star'_not_N (h ▸ hn₂_Θ.1)
  have hn_star'_N' : n_star' ∈ Γ'.N := hN' ▸ Or.inr rfl
  have hn₁_N' : n₁ ∈ Γ'.N := hN' ▸ Or.inl ⟨hn₁_Θ.1, hn₁_ne_star⟩
  have hn₂_N' : n₂ ∈ Γ'.N := hN' ▸ Or.inl ⟨hn₂_Θ.1, hn₂_ne_star⟩
  let nodeMap : π.S → π.S := fun x => if x = n_star then n_star' else x
  let nodeInv : π.S → π.S := fun n => if n = n_star' then n_star else n
  obtain ⟨hnodeMap_inv, hnodeMap_injOn, hnodeInv_mem⟩ :=
    indent_node_map_and_inverse π.Γ.N Γ'.N n_star n_star' hn_star.1 hn_star'_not_N hN'
  have hnodeInv_injOn : InjOn nodeInv Γ'.N := by
    exact indent_node_inverse_injective (α := α) (β := β) (G := G) π (n_star := n_star) (Γ' := Γ')
      n_star' hN' hn_star'_not_N
  let cellG' : Set π.S → Hypergraph α β := fun d =>
    if d = c₁ then A₁' else if d = c₂ then A₂' else π.cellGraph (cellMap d)
  let borderS' : π.S → Set α := fun n =>
    if n = n_star' then (A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n_star}
    else π.borderSet n
  let nodeV' : π.S → α := fun n => π.nodeVertex (nodeInv n)
  let bp' : π.S → Set α := fun n => {w | w ∈ borderS' n ∨ (n ∈ Γ'.N ∧ w = nodeV' n)}
  have hcellG'_c₁ : cellG' c₁ = A₁' := by simp [cellG']
  have hcellG'_c₂ : cellG' c₂ = A₂' := by simp [cellG', hc₁₂_ne.symm]
  have hcellG'_other : ∀ d ∈ Γ'.C \ {c₁, c₂}, cellG' d = π.cellGraph (cellMap d) := by
    rintro d ⟨_, hnot⟩
    have hd₁ : d ≠ c₁ := fun h => hnot (Or.inl h)
    have hd₂ : d ≠ c₂ := fun h => hnot (Or.inr h)
    simp [cellG', hd₁, hd₂]
  have hcellMap_mem : ∀ d ∈ Γ'.C \ {c₁, c₂}, cellMap d ∈ π.Γ.C \ R :=
    fun d hd => hbij.mapsTo hd
  have hnodeV'_star' : nodeV' n_star' = π.nodeVertex n_star := by simp [nodeV', nodeInv]
  have hnodeV'_other : ∀ n ≠ n_star', nodeV' n = π.nodeVertex n := by
    intro n hn; simp [nodeV', nodeInv, hn]
  have hnodeV'_map : ∀ x ∈ π.Γ.N, nodeV' (nodeMap x) = π.nodeVertex x := by
    intro x hx
    change π.nodeVertex (nodeInv (nodeMap x)) = π.nodeVertex x
    exact congrArg π.nodeVertex (hnodeMap_inv x hx)
  have hbp'_star' : bp' n_star' = A₁'.vertexSet ∩ A₂'.vertexSet := by
    ext w
    simp only [bp', borderS', ite_true, mem_ofPred_eq, mem_sdiff, mem_inter_iff, mem_singleton_iff,
      hn_star'_N', true_and, hnodeV'_star']
    exact ⟨fun h => h.elim And.left (fun hEq => hEq ▸ hn_star_mem),
      fun hw => by
        by_cases h : w = π.nodeVertex n_star
        · exact Or.inr h
        · exact Or.inl ⟨hw, h⟩⟩
  have hbp'_other : ∀ n ∈ π.Γ.N, n ≠ n_star → bp' n = π.borderPlus n := by
    intro n hnN hns
    have hn' : n ≠ n_star' := fun h => hn_star'_not_N (h ▸ hnN)
    have hnN' : n ∈ Γ'.N := hN' ▸ Or.inl ⟨hnN, hns⟩
    have hndom : n ∈ π.domγ := hdom ▸ hnN
    ext w
    simp [bp', borderS', hn', hnN', hnodeV'_other n hn', Portrayal.borderPlus, hndom]
  have hbp'_other_bd : ∀ n ∈ π.Γ.N, n ∈ bd π.S → bp' n = π.borderPlus n :=
    fun n hnN hnbd => hbp'_other n hnN (fun h => hn_star.2 (h ▸ hnbd))
  have hborder_not_star : ∀ d ∈ Γ'.C \ {c₁, c₂}, (d ∩ bd π.S).Nonempty →
      n_star ∉ tilde (cellMap d) ∧ tilde d = tilde (cellMap d) ∧ n_star' ∉ tilde d := by
    exact unmodified_border_cell_has_same_ends (α := α) (β := β) (G := G) π (n_star := n_star)
      hn_star (R := R) (Γ' := Γ') n_star' c₁ c₂ cellMap hbd_iff htilde_map hn_star'_not_N
      hcellMap_mem
  let π' : Portrayal G :=
    indented_cuff_portrayal (α := α) (β := β) (G := G) π hdom hnode_cell (Θ := Θ) (c₀ := c₀) hΘ
      hc₀ hc₀_Θ (n₁ := n₁) (n₂ := n₂) (n_star := n_star) hne htc₀ hn_star (R := R) hc₀_R hR_cases
      (Γ' := Γ') (A₁' := A₁') (A₂' := A₂') hA₁'_le hA₂'_le hV_union hV_sub hE_union hE_disj hbp₁
      hbp₂ hn_star_mem hbs_sub hbs₁_le hbs₂_le hbs_star_le hlp₁ hlp₂ n_star' c₁ c₂ cellMap
      hn_star'_mem hN' hc₁_C' hc₂_C' hc₁₂_ne hc₁_Θ hc₂_Θ htc₁ htc₂ hbij hΘ_iff hbd_iff htilde_map
      hΘ_bd hsub_cuff₀ hbd₀ hn₁_Θ hn₂_Θ hn₁_bd hn₂_bd hn_star'_bd hn_star'_not_N hn_star'_ne_star
      hn₁_ne_star hn₂_ne_star hn₁_ne_star' hn₂_ne_star' hn_star'_N' hn₁_N' hn₂_N'
      hnodeMap_inv hnodeMap_injOn hnodeInv_mem hnodeInv_injOn cellG'
      hcellG'_c₁ hcellG'_c₂ hcellG'_other hcellMap_mem hnodeV'_star' hnodeV'_other hnodeV'_map
      hbp'_star' hbp'_other hbp'_other_bd hborder_not_star
  have hπ'_central : π'.IsCentral 𝒯 := by
    apply central_of_replacing_two_cells π' c₁ c₂ _ _ htrue.1 cellMap
      (fun d hd => (hcellMap_mem d hd).1) hcellG'_other
    · change ∃ B, (cellG' c₁, B) ∈ 𝒯
      rwa [hcellG'_c₁]
    · change ∃ B, (cellG' c₂, B) ∈ 𝒯
      rwa [hcellG'_c₂]
  have hbp'_eq_star' : π'.borderPlus n_star' = A₁'.vertexSet ∩ A₂'.vertexSet := hbp'_star'
  have hbp'_eq_other_bd : ∀ n ∈ π.Γ.N, n ∈ bd π.S → π'.borderPlus n = π.borderPlus n
    := hbp'_other_bd
  have hbs'_star' : π'.borderSet n_star' = (A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n_star}
    := by
    change borderS' n_star' = _; simp [borderS']
  have hbs'_other : ∀ n ∈ π.Γ.N, π'.borderSet n = π.borderSet n := by
    intro n hnN
    have hn' : n ≠ n_star' := fun h => hn_star'_not_N (h ▸ hnN)
    change borderS' n = _; simp [borderS', hn']
  have hcw_c₁ : π'.cellWarp c₁ ≤ π.warpAt Θ := by
    apply Portrayal.cellWarp_le_of_two_ends π' htc₁
    · rw [hbs'_other n₁ hn₁_Θ.1]
      exact hbs₁_le
    · rw [hbs'_star']
      exact hbs_star_le
    · rw [show π'.cellGraph c₁ = A₁' from hcellG'_c₁,
        hbp'_eq_other_bd n₁ hn₁_bd.1 hn₁_bd.2, hbp'_eq_star',
        show π'.nodeVertex n₁ = π.nodeVertex n₁ from hnodeV'_other n₁ hn₁_ne_star',
        show π'.nodeVertex n_star' = π.nodeVertex n_star from hnodeV'_star']
      exact hlp₁
  have hcw_c₂ : π'.cellWarp c₂ ≤ π.warpAt Θ := by
    apply Portrayal.cellWarp_le_of_two_ends π' htc₂
    · rw [hbs'_other n₂ hn₂_Θ.1]
      exact hbs₂_le
    · rw [hbs'_star']
      exact hbs_star_le
    · rw [show π'.cellGraph c₂ = A₂' from hcellG'_c₂,
        hbp'_eq_other_bd n₂ hn₂_bd.1 hn₂_bd.2, hbp'_eq_star',
        show π'.nodeVertex n₂ = π.nodeVertex n₂ from hnodeV'_other n₂ hn₂_ne_star',
        show π'.nodeVertex n_star' = π.nodeVertex n_star from hnodeV'_star']
      exact hlp₂
  have hcw_other : ∀ d ∈ Γ'.C \ {c₁, c₂}, (d ∩ bd π.S).Nonempty →
      π'.cellWarp d = π.cellWarp (cellMap d) := by
    intro d hd_diff hbd_d
    obtain ⟨_, htd_eq, _⟩ := hborder_not_star d hd_diff hbd_d
    have hc_mem := (hcellMap_mem d hd_diff).1
    have hbd_c : (cellMap d ∩ bd π.S).Nonempty := (hbd_iff d hd_diff).mp hbd_d
    have hsub_bd := tilde_border_cell_subset_bd π.Γ hc_mem hbd_c
    have hcg : π'.cellGraph d = π.cellGraph (cellMap d) := hcellG'_other d hd_diff
    change sInf {p | π'.CellWarpLE d p} = sInf {p | π.CellWarpLE (cellMap d) p}
    congr 1; ext q'
    simp only [Portrayal.CellWarpLE, htd_eq, hcg]
    refine forall₂_congr fun u₁ hu₁ => forall₂_congr fun u₂ hu₂ => forall_congr' fun _ => ?_
    have hu₁N : u₁ ∈ π.Γ.N := π.Γ.tilde_subset_N hc_mem hu₁
    have hu₂N : u₂ ∈ π.Γ.N := π.Γ.tilde_subset_N hc_mem hu₂
    have hu₁_ne : u₁ ≠ n_star' := fun h => hn_star'_not_N (h ▸ hu₁N)
    have hu₂_ne : u₂ ≠ n_star' := fun h => hn_star'_not_N (h ▸ hu₂N)
    have hnv₁ : π'.nodeVertex u₁ = π.nodeVertex u₁ := hnodeV'_other u₁ hu₁_ne
    have hnv₂ : π'.nodeVertex u₂ = π.nodeVertex u₂ := hnodeV'_other u₂ hu₂_ne
    rw [hbs'_other u₁ hu₁N, hbs'_other u₂ hu₂N,
        hbp'_eq_other_bd u₁ hu₁N (hsub_bd hu₁), hbp'_eq_other_bd u₂ hu₂N (hsub_bd hu₂), hnv₁, hnv₂]
  have hwarpAt_le : ∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' ≤ π.warpAt Θ' := by
    intro Θ' hΘ'
    apply csSup_le'
    rintro r ⟨d, hd_C', hd_Θ', rfl⟩
    by_cases hd₁ : d = c₁
    · rw [hd₁] at hd_Θ' ⊢
      have hΘ'_eq : Θ' = Θ :=
        (Γ'.border_cell_subset_cuff hc₁_C' hΘ hc₁_Θ).2.2.2.2 Θ' hΘ' hd_Θ'
      exact hΘ'_eq ▸ hcw_c₁
    · by_cases hd₂ : d = c₂
      · rw [hd₂] at hd_Θ' ⊢
        have hΘ'_eq : Θ' = Θ :=
          (Γ'.border_cell_subset_cuff hc₂_C' hΘ hc₂_Θ).2.2.2.2 Θ' hΘ' hd_Θ'
        exact hΘ'_eq ▸ hcw_c₂
      · have hd_diff : d ∈ Γ'.C \ {c₁, c₂} := ⟨hd_C', by simp [hd₁, hd₂]⟩
        have hΘ'_bd : Θ' ⊆ bd π.S := by
          rcases hΘ' with ⟨x, _, rfl⟩
          exact connectedComponentIn_subset _ x
        have hbd_d : (d ∩ bd π.S).Nonempty := hd_Θ'.mono (inter_subset_inter_right _ hΘ'_bd)
        rw [hcw_other d hd_diff hbd_d]
        exact π.cellWarp_le_warpAt (hcellMap_mem d hd_diff).1 ((hΘ_iff d hd_diff Θ' hΘ').mp hd_Θ')
  have hπ'_res : π'.Resembles π := by
    apply resembling_of_central_warp_le htrue.2.1 hπ'_central (Homeomorph.refl π.S)
    intro Θ' hΘ'
    rw [Homeomorph.refl_apply, image_id]
    exact hwarpAt_le Θ' hΘ'
  have hπ'_truer : π'.IsTruer π := by
    apply isTruer_of_fewer_internal_nodes π' π
    · intro i hi
      simp only [Portrayal.truth, hi, ↓reduceIte]
      change {d ∈ Γ'.C | ¬ (d ∩ bd π.S).Nonempty ∧ (tilde d).ncard = 3 - i.1}.ncard ≤
        {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - i.1}.ncard
      exact ncard_internal_cells_le_of_map Γ' π.Γ c₁ c₂ cellMap nodeMap (3 - i.1)
        (hc₁_Θ.mono (inter_subset_inter_right _ hΘ_bd))
        (hc₂_Θ.mono (inter_subset_inter_right _ hΘ_bd)) hbij.injOn
        (fun d hd => (hcellMap_mem d hd).1) hbd_iff htilde_map hnodeMap_injOn
    · change (Γ'.N \ bd π.S).ncard < (π.Γ.N \ bd π.S).ncard
      have hsub : Γ'.N \ bd π.S ⊆ (π.Γ.N \ bd π.S) \ {n_star} := by
        rintro x ⟨hxN', hxbd⟩
        rw [hN'] at hxN'
        rcases hxN' with ⟨hxN, hx_ne⟩ | rfl
        · exact ⟨⟨hxN, hxbd⟩, hx_ne⟩
        · exact (hxbd hn_star'_bd).elim
      have hle := ncard_le_ncard hsub ((π.Γ.finite_N.subset sdiff_subset).subset sdiff_subset)
      have hlt := ncard_sdiff_singleton_lt_of_mem hn_star (π.Γ.finite_N.subset sdiff_subset)
      omega
  exact htrue.2.2 π' hπ'_central hπ'_truer hπ'_res

@[expose] public section

/-- The subhypergraph on the given vertices with no edges. -/
def edgelessSubhypergraph {α : Type u} {β : Type v} (G : Hypergraph α β) (S : Set α)
    (hS : S ⊆ G.vertexSet) : Hypergraph α β where
  vertexSet := S
  edgeSet := ∅
  Inc _ _ := False
  vertex_mem_of_inc _ _ h := h.elim
  edge_mem_of_inc _ _ h := h.elim
  vertexSet_finite := G.vertexSet_finite.subset hS
  edgeSet_finite := Set.finite_empty

end

theorem edgelessSubhypergraph_le {α : Type u} {β : Type v} (G : Hypergraph α β) (S : Set α)
    (hS : S ⊆ G.vertexSet) : edgelessSubhypergraph G S hS ≤ G :=
  ⟨hS, empty_subset _, fun _ he => he.elim⟩

@[expose] public section

/-- Adjoin an isolated vertex to a subhypergraph. -/
def addVertexSubhypergraph {α : Type u} {β : Type v} (A : Hypergraph α β) (x : α) :
    Hypergraph α β where
  vertexSet := A.vertexSet ∪ {x}
  edgeSet := A.edgeSet
  Inc := A.Inc
  vertex_mem_of_inc _ _ h := Or.inl (A.vertex_mem_of_inc h)
  edge_mem_of_inc _ _ h := A.edge_mem_of_inc h
  vertexSet_finite := A.vertexSet_finite.union (Set.finite_singleton x)
  edgeSet_finite := A.edgeSet_finite

end

theorem addVertexSubhypergraph_le {α : Type u} {β : Type v} {G A : Hypergraph α β} {x : α}
    (hA : A ≤ G) (hx : x ∈ G.vertexSet) : addVertexSubhypergraph A x ≤ G :=
  ⟨union_subset hA.1 (singleton_subset_iff.mpr hx), hA.2, hA.3⟩

theorem first_eq_last_of_mem_walk_not_mem_vertexSet {α : Type u} {β : Type v}
    (A : Hypergraph α β) {x u v : α} (hx : x ∉ A.vertexSet)
    (w : A.skeleton.Walk u v) (hmem : x ∈ w.support) :
    u = x ∧ v = x := by
  induction w with
  | @nil a =>
    rw [SimpleGraph.Walk.support_nil] at hmem
    have hEq : x = a := List.mem_singleton.mp hmem
    exact ⟨hEq.symm, hEq.symm⟩
  | @cons a b c hab w' ih =>
    rcases hab with ⟨_, e, ha, hb⟩
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact (hx (A.vertex_mem_of_inc ha)).elim
    · obtain ⟨rfl, rfl⟩ := ih hmem'
      exact (hx (A.vertex_mem_of_inc hb)).elim

theorem injective_first_of_disjoint_paths {α : Type u} {K : SimpleGraph α} {X Y : Set α} {k : ℕ}
    (P : Fin k → PathFromTo K X Y)
    (hdisj : Pairwise fun i j ↦ Disjoint {z | z ∈ (P i).walk.support} {z | z ∈
      (P j).walk.support}) :
    Function.Injective (fun i : Fin k ↦ (P i).first) := by
  intro i j hEq
  by_contra hij
  have hi : (P i).first ∈ (P i).walk.support := (P i).walk.start_mem_support
  have hj : (P i).first ∈ (P j).walk.support := by
    change (fun m => (P m).first) i ∈ (P j).walk.support
    rw [hEq]
    exact (P j).walk.start_mem_support
  exact Set.disjoint_left.mp (hdisj hij) hi hj

theorem injective_last_of_disjoint_paths {α : Type u} {K : SimpleGraph α} {X Y : Set α} {k : ℕ}
    (P : Fin k → PathFromTo K X Y)
    (hdisj : Pairwise fun i j ↦ Disjoint {z | z ∈ (P i).walk.support} {z | z ∈
      (P j).walk.support}) :
    Function.Injective (fun i : Fin k ↦ (P i).last) := by
  intro i j hEq
  by_contra hij
  have hi : (P i).last ∈ (P i).walk.support := (P i).walk.end_mem_support
  have hj : (P i).last ∈ (P j).walk.support := by
    change (fun m => (P m).last) i ∈ (P j).walk.support
    rw [hEq]
    exact (P j).walk.end_mem_support
  exact Set.disjoint_left.mp (hdisj hij) hi hj

theorem le_ncard_of_disjoint_paths_first {α : Type u} {K : SimpleGraph α} {X Y : Set α} {k : ℕ}
    (hX_fin : X.Finite) (P : Fin k → PathFromTo K X Y)
    (hdisj : Pairwise fun i j ↦ Disjoint {z | z ∈ (P i).walk.support} {z | z ∈
      (P j).walk.support}) :
    k ≤ X.ncard := by
  have hsub : range (fun i : Fin k ↦ (P i).first) ⊆ X := by
    rintro _ ⟨i, rfl⟩; exact (P i).first_mem
  have hcard : (range (fun i : Fin k ↦ (P i).first)).ncard = k := by
    rw [ncard_range_of_injective (injective_first_of_disjoint_paths P hdisj),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← hcard]
  exact ncard_le_ncard hsub hX_fin

theorem le_ncard_of_disjoint_paths_last {α : Type u} {K : SimpleGraph α} {X Y : Set α} {k : ℕ}
    (hY_fin : Y.Finite) (P : Fin k → PathFromTo K X Y)
    (hdisj : Pairwise fun i j ↦ Disjoint {z | z ∈ (P i).walk.support} {z | z ∈
      (P j).walk.support}) :
    k ≤ Y.ncard := by
  have hsub : range (fun i : Fin k ↦ (P i).last) ⊆ Y := by
    rintro _ ⟨i, rfl⟩; exact (P i).last_mem
  have hcard : (range (fun i : Fin k ↦ (P i).last)).ncard = k := by
    rw [ncard_range_of_injective (injective_last_of_disjoint_paths P hdisj),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← hcard]
  exact ncard_le_ncard hsub hY_fin

theorem exists_first_eq_of_ncard_le {α : Type u} {K : SimpleGraph α} {X Y : Set α} {k : ℕ}
    (hX_fin : X.Finite) (hcard : X.ncard ≤ k)
    (P : Fin k → PathFromTo K X Y)
    (hdisj : Pairwise fun i j ↦ Disjoint {z | z ∈ (P i).walk.support} {z | z ∈ (P j).walk.support})
    {x : α} (hx : x ∈ X) :
    ∃ i : Fin k, (P i).first = x := by
  have hsub : range (fun i : Fin k ↦ (P i).first) ⊆ X := by
    rintro _ ⟨i, rfl⟩; exact (P i).first_mem
  have hr_card : (range (fun i : Fin k ↦ (P i).first)).ncard = k := by
    rw [ncard_range_of_injective (injective_first_of_disjoint_paths P hdisj),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hEq : range (fun i : Fin k ↦ (P i).first) = X :=
    eq_of_subset_of_ncard_le hsub (by omega) hX_fin
  have hx' : x ∈ range (fun i : Fin k ↦ (P i).first) := by rwa [hEq]
  exact hx'

theorem exists_last_eq_of_ncard_le {α : Type u} {K : SimpleGraph α} {X Y : Set α} {k : ℕ}
    (hY_fin : Y.Finite) (hcard : Y.ncard ≤ k)
    (P : Fin k → PathFromTo K X Y)
    (hdisj : Pairwise fun i j ↦ Disjoint {z | z ∈ (P i).walk.support} {z | z ∈ (P j).walk.support})
    {y : α} (hy : y ∈ Y) :
    ∃ i : Fin k, (P i).last = y := by
  have hsub : range (fun i : Fin k ↦ (P i).last) ⊆ Y := by
    rintro _ ⟨i, rfl⟩; exact (P i).last_mem
  have hr_card : (range (fun i : Fin k ↦ (P i).last)).ncard = k := by
    rw [ncard_range_of_injective (injective_last_of_disjoint_paths P hdisj),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hEq : range (fun i : Fin k ↦ (P i).last) = Y :=
    eq_of_subset_of_ncard_le hsub (by omega) hY_fin
  have hy' : y ∈ range (fun i : Fin k ↦ (P i).last) := by rwa [hEq]
  exact hy'

theorem ncard_borderPlus_le_warpAt_succ
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) {n : π.S} (hn : n ∈ π.Γ.N ∩ Θ) :
    (π.borderPlus n).ncard ≤ π.warpAt Θ + 1 := by
  have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hbs_le : (π.borderSet n).ncard ≤ π.warpAt Θ := π.ncard_borderSet_le_warpAt hΘ hΘ_arc hn
  have hbp_le : (π.borderPlus n).ncard ≤ (π.borderSet n).ncard + 1 :=
    π.ncard_borderPlus_le ⟨hn.1, hΘ_bd hn.2⟩
  omega

theorem cyclicDist_succ_pred_le {k : ℕ} (hk : 2 ≤ k) {i m : Fin k} (hm : m ≠ i) :
    let hk_pos : 0 < k := by omega
    let i_next : Fin k := ⟨(i.1 + 1) % k, Nat.mod_lt _ hk_pos⟩
    let i_prev : Fin k := cyclicPred hk_pos i
    cyclicDist i i_next + cyclicDist i_next m + cyclicDist m i_prev ≤ k := by
  intro hk_pos i_next i_prev
  have hm_val : m.1 ≠ i.1 := fun h => hm (Fin.ext h)
  have hi_lt : i.1 < k := i.2
  have hm_lt : m.1 < k := m.2
  have hnext_val : i_next.1 = if i.1 + 1 < k then i.1 + 1 else 0 := by
    dsimp [i_next]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · have : i.1 + 1 = k := by omega
      rw [this, Nat.mod_self]
  have hprev_val : i_prev.1 = if i.1 = 0 then k - 1 else i.1 - 1 := by
    dsimp [i_prev, cyclicPred]
    split_ifs with h
    · rw [h, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    · have h1 : i.1 + k - 1 = (i.1 - 1) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [cyclicDist_eq_ite, cyclicDist_eq_ite, cyclicDist_eq_ite]
  revert hnext_val hprev_val
  split_ifs <;> intro hnext_val hprev_val <;> omega

theorem exists_other_border_cell_of_mem_tilde
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C) (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ n₂ : π.S} (hne₁₂ : n₁ ≠ n₂) (htc₀ : tilde c₀ = {n₁, n₂}) :
    ∃ c₁ ∈ π.Γ.C, (c₁ ∩ Θ).Nonempty ∧ c₁ ≠ c₀ ∧
      ∃ n₃ : π.S, n₁ ≠ n₃ ∧ tilde c₁ = {n₁, n₃} ∧
        (∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁)) ∧
        (∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ →
          ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m →
            v ∈ π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃) := by
  have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hsub_cuff₀ := π.Γ.border_cell_subset_cuff hc₀ hΘ hc₀_Θ
  have hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 (htc₀ ▸ Or.inl rfl)
  set k := (π.Γ.N ∩ Θ).ncard
  obtain ⟨E⟩ : Nonempty (π.Γ.CuffEnumeration Θ k) := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  have hk_ge2 : 2 ≤ k := E.two_le
  have hk_pos : 0 < k := by omega
  have hn₁_range : n₁ ∈ range E.node := E.range_node ▸ hn₁_Θ
  rcases hn₁_range with ⟨i, hi_eq⟩
  let i_next : Fin k := ⟨(i.1 + 1) % k, Nat.mod_lt _ hk_pos⟩
  let i_prev : Fin k := cyclicPred hk_pos i
  have hi_ne_next : i ≠ i_next := by
    intro hEq
    have hval : i.1 = (i.1 + 1) % k := congrArg Fin.val hEq
    have hi_lt : i.1 < k := i.2
    by_cases hlast : i.1 + 1 = k
    · rw [hlast, Nat.mod_self] at hval; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
  have hi_ne_prev : i ≠ i_prev := by
    intro hEq
    have hval : i.1 = (i.1 + k - 1) % k := congrArg Fin.val hEq
    have hi_lt : i.1 < k := i.2
    by_cases hi0 : i.1 = 0
    · rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hval; omega
    · have hmod : (i.1 + k - 1) % k = i.1 - 1 := by
        rw [show i.1 + k - 1 = (i.1 - 1) + k by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      omega
  have hprev_succ : (⟨(i_prev.1 + 1) % k, Nat.mod_lt _ hk_pos⟩ : Fin k) = i := by
    apply Fin.ext
    dsimp [i_prev, cyclicPred]
    have hi_lt : i.1 < k := i.2
    by_cases hi0 : i.1 = 0
    · simp [hi0, Nat.sub_add_cancel hk_pos]
    · have hmod : (i.1 + k - 1) % k = i.1 - 1 := by
        rw [show i.1 + k - 1 = (i.1 - 1) + k by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [hmod, Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hi_lt]
  have hcell_tilde_i : tilde (E.cell i) = {n₁, E.node i_next} := by
    rw [E.cell_tilde i, hi_eq]
  have hcell_tilde_prev : tilde (E.cell i_prev) = {n₁, E.node i_prev} := by
    rw [E.cell_tilde i_prev, hprev_succ, hi_eq, Set.pair_comm]
  have hmem_tilde_iff : ∀ j : Fin k, n₁ ∈ tilde (E.cell j) ↔ j = i ∨ j = i_prev := by
    intro j
    rw [E.cell_tilde j, ← hi_eq]
    simp only [mem_insert_iff, mem_singleton_iff, E.injective_node.eq_iff]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with rfl | hEq
      · exact Or.inl rfl
      · right
        apply Fin.ext
        dsimp [i_prev, cyclicPred]
        have hi_lt : i.1 < k := i.2
        have hj_lt : j.1 < k := j.2
        have hval : (j.1 + 1) % k = i.1 := congrArg Fin.val hEq.symm
        by_cases hj_last : j.1 + 1 = k
        · rw [hj_last, Nat.mod_self] at hval
          rw [← hval, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
          omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hval
          have h1 : i.1 + k - 1 = j.1 + k := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hj_lt]
    · rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hprev_succ.symm
  have hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty →
      (n₁ ∈ tilde d ↔ d = E.cell i ∨ d = E.cell i_prev) := by
    intro d hd hbd_d
    constructor
    · intro hn₁_td
      rcases hbd_d with ⟨x, hxd, hxbd⟩
      let Θ' := connectedComponentIn (bd π.S) x
      have hΘ' : Θ' ∈ cuffs π.S := ⟨x, hxbd, rfl⟩
      have hd_Θ' : (d ∩ Θ').Nonempty := ⟨x, hxd, mem_connectedComponentIn hxbd⟩
      have hn₁_Θ' : n₁ ∈ π.Γ.N ∩ Θ' :=
        (π.Γ.border_cell_subset_cuff hd hΘ' hd_Θ').2.2.2.1 hn₁_td
      have hΘ'_eq : Θ' = Θ := by
        rcases hΘ with ⟨x₀, _, rfl⟩
        exact (connectedComponentIn_eq hn₁_Θ'.2).trans (connectedComponentIn_eq hn₁_Θ.2).symm
      have hd_mem : d ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := ⟨hd, hΘ'_eq ▸ hd_Θ'⟩
      rw [← E.range_cell] at hd_mem
      rcases hd_mem with ⟨j, rfl⟩
      rcases (hmem_tilde_iff j).mp hn₁_td with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · rw [hcell_tilde_i]; exact Or.inl rfl
      · rw [hcell_tilde_prev]; exact Or.inl rfl
  have hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ →
      ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m →
        v ∈ π.borderPlus (E.node i_next) ∨ v ∈ π.borderPlus (E.node i_prev) := by
    intro m hm hm_ne v hv₁ hvm
    have hm_range : m ∈ range E.node := E.range_node ▸ hm
    rcases hm_range with ⟨jm, rfl⟩
    have hjm_ne : jm ≠ i := fun h => hm_ne (h ▸ hi_eq)
    rw [← hi_eq] at hv₁
    exact π.p7_of_cyclicDist E (cyclicDist_succ_pred_le hk_ge2 hjm_ne) hv₁ hvm
  have hbd₀ : (c₀ ∩ bd π.S).Nonempty := hsub_cuff₀.2.1 ▸ hc₀_Θ
  have hn₁_tc₀ : n₁ ∈ tilde c₀ := htc₀ ▸ Or.inl rfl
  rcases (hd_iff c₀ hc₀ hbd₀).mp hn₁_tc₀ with hc₀_eq | hc₀_eq
  · have hn₂_eq : n₂ = E.node i_next := by
      have hpair : ({n₁, n₂} : Set π.S) = {n₁, E.node i_next} :=
        htc₀.symm.trans (hc₀_eq ▸ hcell_tilde_i)
      have hmem : n₂ ∈ ({n₁, E.node i_next} : Set π.S) := hpair ▸ Or.inr rfl
      exact hmem.resolve_left hne₁₂.symm
    have hc₁_mem : E.cell i_prev ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} :=
      E.range_cell ▸ ⟨i_prev, rfl⟩
    refine ⟨E.cell i_prev, hc₁_mem.1, hc₁_mem.2, ?_, E.node i_prev, ?_, hcell_tilde_prev, ?_, ?_⟩
    · rw [hc₀_eq]
      exact E.injective_cell.ne hi_ne_prev.symm
    · rw [← hi_eq]
      exact E.injective_node.ne hi_ne_prev
    · intro d hd hbd_d
      rw [hd_iff d hd hbd_d, hc₀_eq]
    · intro m hm hm_ne v hv₁ hvm
      rw [hn₂_eq]
      exact hneighbors m hm hm_ne v hv₁ hvm
  · have hn₂_eq : n₂ = E.node i_prev := by
      have hpair : ({n₁, n₂} : Set π.S) = {n₁, E.node i_prev} :=
        htc₀.symm.trans (hc₀_eq ▸ hcell_tilde_prev)
      have hmem : n₂ ∈ ({n₁, E.node i_prev} : Set π.S) := hpair ▸ Or.inr rfl
      exact hmem.resolve_left hne₁₂.symm
    have hc₁_mem : E.cell i ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} :=
      E.range_cell ▸ ⟨i, rfl⟩
    refine ⟨E.cell i, hc₁_mem.1, hc₁_mem.2, ?_, E.node i_next, ?_, hcell_tilde_i, ?_, ?_⟩
    · rw [hc₀_eq]
      exact E.injective_cell.ne hi_ne_prev
    · rw [← hi_eq]
      exact E.injective_node.ne hi_ne_next
    · intro d hd hbd_d
      rw [hd_iff d hd hbd_d, hc₀_eq, or_comm]
    · intro m hm hm_ne v hv₁ hvm
      rw [hn₂_eq, or_comm]
      exact hneighbors m hm hm_ne v hv₁ hvm

theorem extract_linkage_from_plus_linkage
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    (hdom : π.domγ = π.Γ.N)
    {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C) (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ n₂ : π.S} (hn₁_tc : n₁ ∈ tilde c₀) (hn₂_tc : n₂ ∈ tilde c₀) (hne : n₁ ≠ n₂)
    (hbs₁_eq : (π.borderSet n₁).ncard = π.warpAt Θ)
    (hbs₂_eq : (π.borderSet n₂).ncard = π.warpAt Θ)
    (hpaths : HasDisjointPaths (π.cellGraph c₀).skeleton (π.borderPlus n₁) (π.borderPlus n₂)
      (π.warpAt Θ + 1)) :
    ∃ L : Fin (π.warpAt Θ) →
        PathFromTo (π.cellGraph c₀).skeleton (π.borderSet n₁) (π.borderSet n₂),
      (Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support}) ∧
      (∀ i, π.nodeVertex n₁ ∉ (L i).walk.support ∧ π.nodeVertex n₂ ∉ (L i).walk.support) ∧
      ∃ L₀ : PathFromTo (π.cellGraph c₀).skeleton {π.nodeVertex n₁} {π.nodeVertex n₂},
        ∀ i, Disjoint {z | z ∈ L₀.walk.support} {z | z ∈ (L i).walk.support} := by
  have hsub_cuff₀ := π.Γ.border_cell_subset_cuff hc₀ hΘ hc₀_Θ
  have hbd₀ : (c₀ ∩ bd π.S).Nonempty := hsub_cuff₀.2.1 ▸ hc₀_Θ
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 hn₁_tc
  have hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 hn₂_tc
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := ⟨hn₁_Θ.1, hΘ_bd hn₁_Θ.2⟩
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S := ⟨hn₂_Θ.1, hΘ_bd hn₂_Θ.2⟩
  have hbp₁_eq : π.borderPlus n₁ = insert (π.nodeVertex n₁) (π.borderSet n₁) := by
    ext x
    simp [Portrayal.borderPlus, hdom ▸ hn₁_Θ.1, or_comm]
  have hbp₂_eq : π.borderPlus n₂ = insert (π.nodeVertex n₂) (π.borderSet n₂) := by
    ext x
    simp [Portrayal.borderPlus, hdom ▸ hn₂_Θ.1, or_comm]
  have hbs₁_fin : (π.borderSet n₁).Finite :=
    (π.cellGraph c₀).vertexSet_finite.subset (π.p3_subset c₀ hc₀ hbd₀ n₁ hn₁_tc)
  have hbs₂_fin : (π.borderSet n₂).Finite :=
    (π.cellGraph c₀).vertexSet_finite.subset (π.p3_subset c₀ hc₀ hbd₀ n₂ hn₂_tc)
  have hbp₁_card : (π.borderPlus n₁).ncard = π.warpAt Θ + 1 := by
    rw [hbp₁_eq, ncard_insert_of_notMem (π.p3_notMem n₁ ⟨hdom ▸ hn₁_bd.1, hn₁_bd.2⟩) hbs₁_fin,
      hbs₁_eq]
  have hbp₂_card : (π.borderPlus n₂).ncard = π.warpAt Θ + 1 := by
    rw [hbp₂_eq, ncard_insert_of_notMem (π.p3_notMem n₂ ⟨hdom ▸ hn₂_bd.1, hn₂_bd.2⟩) hbs₂_fin,
      hbs₂_eq]
  have hcw₀ : π.CellWarpLE c₀ (π.warpAt Θ) :=
    (π.cellWarp_le_iff hc₀ hbd₀).mp (π.cellWarp_le_warpAt hc₀ hc₀_Θ)
  have hlp := (hcw₀ n₁ hn₁_tc n₂ hn₂_tc hne).2.2 hbp₁_card hbp₂_card
  rcases hpaths with ⟨P, hdisj⟩
  obtain ⟨i₀, hi₀_first, hi₀_last⟩ := hlp P hdisj
  let L₀ : PathFromTo (π.cellGraph c₀).skeleton {π.nodeVertex n₁} {π.nodeVertex n₂} :=
    { first := (P i₀).first
      last := (P i₀).last
      walk := (P i₀).walk
      isPath := (P i₀).isPath
      first_mem := hi₀_first
      last_mem := hi₀_last }
  let emb : Fin (π.warpAt Θ) ↪ Fin (π.warpAt Θ + 1) := i₀.succAboveEmb
  have hemb_ne : ∀ j : Fin (π.warpAt Θ), emb j ≠ i₀ := fun j => Fin.succAbove_ne i₀ j
  have hfirst_bs₁ : ∀ j : Fin (π.warpAt Θ), (P (emb j)).first ∈ π.borderSet n₁ := by
    intro j
    rcases (P (emb j)).first_mem with hbs | ⟨_, hEq⟩
    · exact hbs
    · exfalso
      exact hemb_ne j (injective_first_of_disjoint_paths P hdisj (hEq.trans hi₀_first.symm))
  have hlast_bs₂ : ∀ j : Fin (π.warpAt Θ), (P (emb j)).last ∈ π.borderSet n₂ := by
    intro j
    rcases (P (emb j)).last_mem with hbs | ⟨_, hEq⟩
    · exact hbs
    · exfalso
      exact hemb_ne j (injective_last_of_disjoint_paths P hdisj (hEq.trans hi₀_last.symm))
  let L : Fin (π.warpAt Θ) →
      PathFromTo (π.cellGraph c₀).skeleton (π.borderSet n₁) (π.borderSet n₂) := fun j =>
    { first := (P (emb j)).first
      last := (P (emb j)).last
      walk := (P (emb j)).walk
      isPath := (P (emb j)).isPath
      first_mem := hfirst_bs₁ j
      last_mem := hlast_bs₂ j }
  have hL_disj : Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈
    (L j).walk.support} := by
    intro i j hij
    exact hdisj (emb.injective.ne hij)
  have hL₀_disj : ∀ j : Fin (π.warpAt Θ),
      Disjoint {z | z ∈ L₀.walk.support} {z | z ∈ (L j).walk.support} :=
    fun j => hdisj (hemb_ne j).symm
  have hL_avoid : ∀ j : Fin (π.warpAt Θ),
      π.nodeVertex n₁ ∉ (L j).walk.support ∧ π.nodeVertex n₂ ∉ (L j).walk.support := by
    intro j
    have hn₁_L₀ : π.nodeVertex n₁ ∈ L₀.walk.support := by
      change π.nodeVertex n₁ ∈ (P i₀).walk.support
      rw [← hi₀_first]
      exact (P i₀).walk.start_mem_support
    have hn₂_L₀ : π.nodeVertex n₂ ∈ L₀.walk.support := by
      change π.nodeVertex n₂ ∈ (P i₀).walk.support
      rw [← hi₀_last]
      exact (P i₀).walk.end_mem_support
    exact ⟨Set.disjoint_left.mp (hL₀_disj j) hn₁_L₀, Set.disjoint_left.mp (hL₀_disj j) hn₂_L₀⟩
  exact ⟨L, hL_disj, hL_avoid, L₀, hL₀_disj⟩

theorem hasDisjointPathsAvoiding_symm {α : Type u} {β : Type v} (H : Hypergraph α β)
    (X Y W : Set α) (q : ℕ) (h : HasDisjointPathsAvoiding H X Y W q) :
    HasDisjointPathsAvoiding H Y X W q := by
  rcases h with ⟨L, hdisj, havoid⟩
  let L' : Fin q → PathFromTo H.skeleton Y X := fun i =>
    { first := (L i).last
      last := (L i).first
      walk := (L i).walk.reverse
      isPath := (L i).isPath.reverse
      first_mem := (L i).last_mem
      last_mem := (L i).first_mem }
  have hsup : ∀ i, {z | z ∈ (L' i).walk.support} = {z | z ∈ (L i).walk.support} := by
    intro i; ext z
    change z ∈ (L i).walk.reverse.support ↔ z ∈ (L i).walk.support
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
  refine ⟨L', fun i j hij => ?_, fun i => ?_⟩
  · dsimp only; rw [hsup i, hsup j]; exact hdisj hij
  · rw [hsup i]; exact havoid i

end GraphMinor.GM17
