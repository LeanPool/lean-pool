/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.GM14.Cited
public import LeanPool.GraphMinor.GM14.Adapted
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2a
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.PlanarNests
import LeanPool.GraphMinor.GM09.Bridge


/-!
# Graph Minors XIV, Section 8 (Part 1): (8.2) and Claim (1) of (8.4)

This file formalizes the first part of Section 8 (pages 39–41) of N. Robertson and P. D. Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B **65** (1995) 23–50:

- `empty_isCrookedTransaction`: the empty set of paths `∅` is a crooked transaction in any society.
- `unique_path_of_two_le_inter_bar`: in any transaction `P_set`, at most one path `P ∈ P_set` has
  `≥ 2` vertices in `S₀.Ω.bar` when `|S₀.Ω.bar| ≤ 3`.
- `IsCrookedTransaction.mono`: monotonicity of `IsCrookedTransaction` when enlarging the graph of a
  society while keeping its cyclic permutation fixed.
- `theorem_8_2`: Graph Minors XIV, (8.2) (page 40), deduced from Graph Minors IX, (10.4)
  (`GM09Theorem104Statement`).
- `claim_1_of_8_4`: Claim (1) in the proof of Graph Minors XIV, (8.4) (page 41), showing that
  if a society `S₀` in a 3-segregation is replaced by a subgraph `A' ≤ S₀.G` with
  `S₀.Ω.bar ⊆ V(A')` that preserves `S₀.Ω.bar`-avoiding paths between pairs of vertices in
  `S₀.Ω.bar`, then any crooked transaction of cardinality `≥ π` can be routed through `A'`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09

universe u v w

/-! ## 1. Basic Lemmas on Transactions and 3-Societies -/

/-- The empty set `∅` is a crooked transaction in any society `S`, with
`S.transactionEnds ∅ = ∅`. -/
theorem empty_isCrookedTransaction {α : Type u} {β : Type v} (S : Society α β) :
    S.IsCrookedTransaction ∅ := by
  refine ⟨⟨S.Ω.bar, ∅, ⟨fun _ h => False.elim h, fun _ h => False.elim h⟩, ?_,
    fun _ h => False.elim h⟩, fun _ h => False.elim h⟩
  exact ⟨Subset.rfl, empty_subset S.Ω.bar, disjoint_empty S.Ω.bar, union_empty S.Ω.bar,
    fun _ _ _ _ _ _ hb => False.elim hb⟩

/-- The transaction ends of `∅` is `∅`. -/
@[simp]
theorem transactionEnds_empty {α : Type u} {β : Type v} (S : Society α β) :
    S.transactionEnds ∅ = ∅ := by
  ext v
  simp [Society.transactionEnds]

/-- Two disjoint sets `X₁, X₂` cannot both intersect a set `B` of cardinality `≤ 3` in `≥ 2`
elements. -/
theorem not_both_two_le_inter_of_ncard_le_three {α : Type u} {B X₁ X₂ : Set α}
    (hB_fin : B.Finite) (hB : B.ncard ≤ 3) (hdisj : Disjoint X₁ X₂)
    (h₁ : 2 ≤ (X₁ ∩ B).ncard) (h₂ : 2 ≤ (X₂ ∩ B).ncard) : False := by
  have hfin₁ : (X₁ ∩ B).Finite := hB_fin.subset inter_subset_right
  have hfin₂ : (X₂ ∩ B).Finite := hB_fin.subset inter_subset_right
  have hd : Disjoint (X₁ ∩ B) (X₂ ∩ B) :=
    hdisj.mono inter_subset_left inter_subset_left
  have hsub : (X₁ ∩ B) ∪ (X₂ ∩ B) ⊆ B :=
    union_subset inter_subset_right inter_subset_right
  have hunion : ((X₁ ∩ B) ∪ (X₂ ∩ B)).ncard = (X₁ ∩ B).ncard + (X₂ ∩ B).ncard :=
    ncard_union_eq hd hfin₁ hfin₂
  have hle : ((X₁ ∩ B) ∪ (X₂ ∩ B)).ncard ≤ B.ncard :=
    ncard_le_ncard hsub hB_fin
  omega

/-- In any set of pairwise vertex-disjoint paths `P_set`, at most one path `P ∈ P_set` can contain
at least two vertices of a set `B` with `|B| ≤ 3`. -/
theorem unique_path_of_two_le_inter_bar {α : Type u} {β : Type v}
    {S : Society α β} {P_set : Set (Graph α β)} {B : Set α}
    (hdisj : S.IsDisjointOmegaPathSet P_set) (hB_fin : B.Finite) (hB : B.ncard ≤ 3)
    {P₁ P₂ : Graph α β} (hP₁ : P₁ ∈ P_set) (hP₂ : P₂ ∈ P_set)
    (h₁ : 2 ≤ (V(P₁) ∩ B).ncard) (h₂ : 2 ≤ (V(P₂) ∩ B).ncard) : P₁ = P₂ := by
  by_contra hne
  exact not_both_two_le_inter_of_ncard_le_three hB_fin hB (hdisj.2 hP₁ hP₂ hne) h₁ h₂

/-- If `S_sub.G ≤ S_sup.G`, `S_sub.Ω = S_sup.Ω`, and `P ≤ S_sub.G`, then `P` is an `Ω`-path with
ends `u, v` in `S_sup` if and only if it is an `Ω`-path with ends `u, v` in `S_sub`. -/
theorem isOmegaPathWithEnds_iff_of_le {α : Type u} {β : Type v}
    {S_sub S_sup : Society α β} (hle : S_sub.G ≤ S_sup.G) (hΩ : S_sub.Ω = S_sup.Ω)
    {P : Graph α β} (hP : P ≤ S_sub.G) {u v : α} :
    S_sup.IsOmegaPathWithEnds P u v ↔ S_sub.IsOmegaPathWithEnds P u v := by
  unfold Society.IsOmegaPathWithEnds
  rw [hΩ]
  exact ⟨fun ⟨hp, hrest⟩ => ⟨hp.of_le hP, hrest⟩,
    fun ⟨hp, hrest⟩ => ⟨hp.mono hle, hrest⟩⟩

/-- Monotonicity of `IsCrookedTransaction` when enlarging the underlying graph of a society while
keeping its cyclic permutation fixed. -/
theorem IsCrookedTransaction.mono {α : Type u} {β : Type v}
    {S_sub S_sup : Society α β} (hle : S_sub.G ≤ S_sup.G) (hΩ : S_sub.Ω = S_sup.Ω)
    {P_set : Set (Graph α β)} (hCrooked : S_sub.IsCrookedTransaction P_set) :
    S_sup.IsCrookedTransaction P_set ∧
      S_sup.transactionEnds P_set = S_sub.transactionEnds P_set := by
  obtain ⟨⟨A, B, ⟨hPaths, hDisj⟩, hFence, hAB⟩, hCross⟩ := hCrooked
  have hP_le : ∀ P ∈ P_set, P ≤ S_sub.G := by
    intro P hP
    obtain ⟨_, _, hp⟩ := hPaths P hP
    exact hp.1.le
  have hEnds_eq : S_sup.transactionEnds P_set = S_sub.transactionEnds P_set := by
    ext x
    simp only [Society.transactionEnds, mem_ofPred_eq]
    refine exists_congr fun P => and_congr_right fun hP => exists_congr fun b => ?_
    exact isOmegaPathWithEnds_iff_of_le hle hΩ (hP_le P hP)
  refine ⟨⟨⟨A, B, ⟨fun P hP => ?_, hDisj⟩, hΩ ▸ hFence, fun P hP => ?_⟩, ?_⟩, hEnds_eq⟩
  · obtain ⟨a, b, hp⟩ := hPaths P hP
    exact ⟨a, b, (isOmegaPathWithEnds_iff_of_le hle hΩ (hP_le P hP)).mpr hp⟩
  · obtain ⟨a, ha, b, hb, hp⟩ := hAB P hP
    exact ⟨a, ha, b, hb, (isOmegaPathWithEnds_iff_of_le hle hΩ (hP_le P hP)).mpr hp⟩
  · intro P hP
    rw [Society.IsPeripheralIn, hEnds_eq, ← hΩ]
    intro ⟨_, a, b, hp, hdisj⟩
    have hp_sub := (isOmegaPathWithEnds_iff_of_le hle hΩ (hP_le P hP)).mp hp
    exact hCross P hP ⟨hP, a, b, hp_sub, hdisj⟩

/-- If `P` is an `Ω`-path with ends `a, b` in `S` and `pathInternalVerts S.G P` is disjoint from
`S.Ω.bar`, then `V(P) ∩ S.Ω.bar = {a, b}`. -/
theorem inter_bar_eq_pair_of_disjoint_pathInternalVerts {α : Type u} {β : Type v}
    {S : Society α β} {P : Graph α β} {a b : α}
    (hP : S.IsOmegaPathWithEnds P a b)
    (hdisj : Disjoint (pathInternalVerts S.G P) S.Ω.bar) :
    V(P) ∩ S.Ω.bar = {a, b} := by
  rw [hP.1.pathInternalVerts_eq] at hdisj
  apply subset_antisymm
  · rintro x ⟨hxP, hxBar⟩
    by_contra hne
    exact disjoint_left.mp hdisj ⟨hxP, hne⟩ hxBar
  · rintro x (rfl | rfl)
    · exact ⟨hP.1.left_mem, hP.2.2.1⟩
    · exact ⟨hP.1.right_mem, hP.2.2.2⟩

/-! ## 2. Proof of (8.2) (page 40) -/

/-- Graph Minors XIV, (8.2) (page 40):
"Let $\pi \ge 0$ be an integer with $\pi \ne 1, 3$, and let $(G, \Omega_1)$ be the
composition of a society $(G_2, \Omega_2)$ with a rural neighbourhood $(G_1, \Omega_1,
\Omega_2)$ of breadth $\ge \pi + 5$. Suppose that $X \subseteq \bar{\Omega}_1$ and there are
$2\pi + 8$ mutually disjoint paths of $G_1$, each from $X$ to $\bar{\Omega}_2$ with no
vertex in $\bar{\Omega}_1$ except its initial vertex. If there is a crooked transaction
$\mathscr{P}$ in $(G, \Omega_1)$ with cardinality $\ge \pi$, then $\mathscr{P}$ may be
chosen so that in addition $V(\mathscr{P}) \subseteq X$ and no member of $\mathscr{P}$ has
any internal vertex in $\bar{\Omega}_1$." -/
theorem theorem_8_2_proof
    {α : Type u} {β : Type v}
    (pi : ℕ) (S_comp S₂ : Society α β) (N : Neighborhood α β) (X : Set α)
    (P : Fin (2 * pi + 8) → Graph α β) (x y : Fin (2 * pi + 8) → α)
    (P_set : Set (Graph α β))
    (hpi1 : pi ≠ 1) (hpi3 : pi ≠ 3)
    (hcomp : S_comp.IsComposition S₂ N)
    (hbreadth : N.HasBreadthGe (pi + 5))
    (hX : X ⊆ N.Ω.bar)
    (hP_path : ∀ i, IsFromToPathWithEnds N.G (P i) N.Ω.bar N.Ω₀.bar (x i) (y i) ∧ x i ∈ X)
    (hP_disj : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hCrooked : S_comp.IsCrookedTransaction P_set)
    (hcard : pi ≤ P_set.ncard) :
    ∃ P_set' : Set (Graph α β),
      S_comp.IsCrookedTransaction P_set' ∧
      pi ≤ P_set'.ncard ∧
      S_comp.transactionEnds P_set' ⊆ X ∧
      ∀ Q ∈ P_set', Disjoint (pathInternalVerts S_comp.G Q) S_comp.Ω.bar := by
  by_cases hpi0 : pi = 0
  · subst hpi0
    refine ⟨∅, empty_isCrookedTransaction S_comp, Nat.zero_le _, ?_, fun _ h => False.elim h⟩
    rw [transactionEnds_empty]
    exact empty_subset X
  · have hpi2 : 2 ≤ pi := by omega
    rcases hbreadth with ⟨P_pres, hbreadth_ge⟩
    have hRural : N.IsRural :=
      ⟨P_pres.Γ, P_pres.Δ, P_pres.Δ₀, P_pres.isClosedDisc_Δ, P_pres.Δ₀_subset_Δ,
        P_pres.U_subset, P_pres.mem_bd_Δ_iff, P_pres.mem_bd_Δ₀_iff,
        P_pres.agrees_Δ, P_pres.agrees_Δ₀⟩
    let X' : Set α := range x
    have hX'_sub : X' ⊆ X := by
      rintro _ ⟨i, rfl⟩
      exact (hP_path i).2
    have hx_inj : Injective x := by
      intro i j hxy
      by_contra hne
      have hxi : x i ∈ V(P i) := (hP_path i).1.1.left_mem
      have hxj : x i ∈ V(P j) := hxy ▸ (hP_path j).1.1.left_mem
      exact disjoint_left.mp (hP_disj hne) hxi hxj
    have hX'_card : X'.ncard = 2 * pi + 8 := by
      rw [ncard_range_of_injective hx_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hLinked : N.IsLinked X' := by
      refine ⟨hX'_sub.trans hX, fun k => P (Fin.cast hX'_card k), fun k => ?_, fun i j hne => ?_⟩
      · let i := Fin.cast hX'_card k
        have hy_bar : y i ∈ N.Ω₀.bar := by
          have : y i ∈ V(P i) ∩ N.Ω₀.bar := by
            rw [(hP_path i).1.2.2]
            exact mem_singleton (y i)
          exact this.2
        exact ⟨x i, mem_range_self i, y i, hy_bar, (hP_path i).1⟩
      · have hne' : Fin.cast hX'_card i ≠ Fin.cast hX'_card j :=
          fun h => hne ((Fin.cast_injective hX'_card) h)
        exact hP_disj hne'
    obtain ⟨P_set', hCr', hcard', hEnds', hInt'⟩ :=
      GM09.gm14_theorem_10_4 S_comp S₂ N pi X' P_set hpi2 hpi3 hRural ⟨P_pres, hbreadth_ge⟩ hLinked
        (Nat.le_of_eq hX'_card.symm) hcomp hCrooked hcard
    exact ⟨P_set', hCr', hcard', hEnds'.trans hX'_sub, hInt'⟩

/-! ## 3. Claim (1) of (8.4): Subgraph Replacement in a 3-Segregation (page 41) -/

/-- In a simple walk `W` from `a` to `b`, if an edge `f ∈ W.edges` links `a` and `b`, then `W` has
support `[a, b]` and edges `[f]`. -/
private theorem walk_eq_single_edge_of_isLink_ends {α : Type u} {β : Type v}
    {G : Graph α β} {a b : α} {W : GraphWalk G a b} (hW : W.IsSimple)
    {f : β} (hf : f ∈ W.edges) (hlink : G.IsLink f a b) :
    W.support = [a, b] ∧ W.edges = [f] := by
  cases W with
  | nil _ => simp [GraphWalk.edges] at hf
  | @cons _ y _ e hxy W' =>
    cases W' with
    | nil _ =>
      simp only [GraphWalk.edges, List.mem_singleton] at hf
      subst hf
      exact ⟨rfl, rfl⟩
    | @cons _ z _ e₂ hyz W'' =>
      have hnd : (a :: y :: W''.support).Nodup := hW
      have ha_not : a ∉ y :: W''.support := (List.nodup_cons.mp hnd).1
      have hy_not : y ∉ W''.support := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
      rcases List.mem_cons.mp hf with rfl | hf'
      · have hyb : y = b := by
          rcases hxy.symm.left_eq_or_eq hlink.symm with rfl | rfl
          · rfl
          · exact False.elim (ha_not List.mem_cons_self)
        exact False.elim (hy_not (hyb ▸ W''.end_mem_support))
      · have ha_mem : a ∈ (GraphWalk.cons hyz W'').support :=
          (GraphWalk.cons hyz W'').left_mem_support_of_mem_edges hf' hlink
        exact False.elim (ha_not ha_mem)

/-- Every walk in `G` from `u ∈ V(B)` to `v ∈ V(A)` in a separation `(A, B)` of `G` with
`V(A) ∩ V(B) = Ω_bar` meets `Ω_bar`. -/
theorem walk_inter_bar_of_isGraphSeparation {α : Type u} {β : Type v}
    {G A B : Graph α β} {Ω_bar : Set α}
    (hSep : IsGraphSeparation G A B) (hInter : V(A) ∩ V(B) = Ω_bar)
    {u v : α} (R : GraphWalk G u v) (huB : u ∈ V(B)) (hvA : v ∈ V(A)) :
    ∃ w ∈ R.support, w ∈ Ω_bar := by
  obtain ⟨w, hw, hwAB⟩ := exists_mem_inter_of_graphWalk (IsGraphSeparation.symm hSep) R huB hvA
  exact ⟨w, hw, hInter ▸ ⟨hwAB.2, hwAB.1⟩⟩

/-- Any path `R` in `G` starting at `s ∈ V(B)` with `V(R) ∩ Ω_bar ⊆ {t}` lies in `B`. -/
theorem path_le_right_of_inter_bar_sub_singleton {α : Type u} {β : Type v}
    {G A B R : Graph α β} {Ω_bar : Set α} {s t : α}
    (hSep : IsGraphSeparation G A B) (hInter : V(A) ∩ V(B) = Ω_bar)
    (hR : IsGraphPathWithEnds G R s t) (hsB : s ∈ V(B)) (hR_bar : V(R) ∩ Ω_bar ⊆ {t}) :
    R ≤ B := by
  have hAG : A ≤ G := hSep.1
  have hBG : B ≤ G := hSep.2.1
  have hRG : R ≤ G := hR.le
  obtain ⟨_, WR, hWR, hVR, hER⟩ := hR
  have hV_sub : V(R) ⊆ V(B) := by
    intro x hx
    have hxW : x ∈ WR.support := by
      have hx' := hx
      rwa [hVR, mem_ofPred_eq] at hx'
    by_contra hxB
    have hxG : x ∈ V(G) := hRG.vertexSet_mono hx
    have hxA : x ∈ V(A) := by
      have hxAB : x ∈ V(A) ∪ V(B) := hSep.2.2.1.symm ▸ hxG
      exact hxAB.resolve_right hxB
    obtain ⟨W_pre, W_suf, hW_eq⟩ := WR.exists_append_of_mem hxW
    obtain ⟨W_pre_G, hs_pre, _⟩ := exists_walk_up_of_le hRG W_pre
    obtain ⟨w, hw_pre_G, hwBar⟩ := walk_inter_bar_of_isGraphSeparation hSep hInter W_pre_G hsB hxA
    have hw_pre : w ∈ W_pre.support := hs_pre ▸ hw_pre_G
    have hwR : w ∈ V(R) := by
      rw [hVR, hW_eq, mem_ofPred_eq, GraphWalk.mem_support_append]
      exact Or.inl hw_pre
    have hwt : w = t := mem_singleton_iff.mp (hR_bar ⟨hwR, hwBar⟩)
    subst hwt
    have hnd : (W_pre.support ++ W_suf.support.tail).Nodup := by
      have h' : (W_pre.append W_suf).support.Nodup := hW_eq ▸ hWR
      rwa [GraphWalk.support_append] at h'
    have hx_ne_w : x ≠ w := fun hxw => hxB (hxw ▸ (hInter ▸ hwBar).2)
    have hw_tail : w ∈ W_suf.support.tail := by
      have hw_end : w ∈ W_suf.support := W_suf.end_mem_support
      rw [W_suf.support_eq_cons] at hw_end
      rcases List.mem_cons.mp hw_end with hwx | htail
      · exact False.elim (hx_ne_w hwx.symm)
      · exact htail
    exact (List.nodup_append.mp hnd).2.2 w hw_pre w hw_tail rfl
  rw [(Compatible.of_le_le hRG hBG).le_iff]
  refine ⟨hV_sub, fun e he => ?_⟩
  by_contra heB
  have heG : e ∈ E(G) := hRG.edgeSet_mono he
  have heA : e ∈ E(A) := (hSep.2.2.2.1.symm ▸ heG).resolve_right heB
  obtain ⟨x, y, hxyR⟩ := R.exists_isLink_of_mem_edgeSet he
  have hxyA : A.IsLink e x y := (hAG.isLink_iff heA).mpr (hxyR.mono hRG)
  have hxBar : x ∈ Ω_bar := hInter ▸ ⟨hxyA.left_mem, hV_sub hxyR.left_mem⟩
  have hyBar : y ∈ Ω_bar := hInter ▸ ⟨hxyA.right_mem, hV_sub hxyR.right_mem⟩
  have hxt : x = t := mem_singleton_iff.mp (hR_bar ⟨hxyR.left_mem, hxBar⟩)
  have hyt : y = t := mem_singleton_iff.mp (hR_bar ⟨hxyR.right_mem, hyBar⟩)
  have hloop : G.IsLink e t t := by
    have hxyG : G.IsLink e x y := hxyR.mono hRG
    rwa [hxt, hyt] at hxyG
  exact IsGraphPathWithEnds.not_isLoopAt ⟨hRG, WR, hWR, hVR, hER⟩ he t hloop

/-- If `P` is a path in `G` with ends `a, b ∈ V(B)` such that `¬ (P ≤ B)`, then `V(P) ∩ Ω_bar` has
at least 2 vertices. -/
theorem two_le_ncard_inter_bar_of_not_le_right {α : Type u} {β : Type v}
    {G A B P : Graph α β} {Ω_bar : Set α} {a b : α}
    (hSep : IsGraphSeparation G A B) (hInter : V(A) ∩ V(B) = Ω_bar)
    (hBar_fin : Ω_bar.Finite) (hP : IsGraphPathWithEnds G P a b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B)) (hnotB : ¬ (P ≤ B)) :
    2 ≤ (V(P) ∩ Ω_bar).ncard := by
  by_contra! hlt
  have hfin : (V(P) ∩ Ω_bar).Finite := hBar_fin.subset inter_subset_right
  rcases (V(P) ∩ Ω_bar).eq_empty_or_nonempty with hemp | ⟨t, htP, htBar⟩
  · have hsub : V(P) ∩ Ω_bar ⊆ {b} := by rw [hemp]; exact empty_subset _
    exact hnotB (path_le_right_of_inter_bar_sub_singleton hSep hInter hP haB hsub)
  · have hsub : V(P) ∩ Ω_bar ⊆ {t} := by
      intro z hz
      rw [mem_singleton_iff]
      by_contra hzt
      have hpair : ({z, t} : Set α) ⊆ V(P) ∩ Ω_bar := by
        rintro w (rfl | rfl)
        · exact hz
        · exact ⟨htP, htBar⟩
      have h2 : 2 ≤ (V(P) ∩ Ω_bar).ncard := by
        rw [← ncard_pair hzt]
        exact ncard_le_ncard hpair hfin
      omega
    obtain ⟨P₁, P₂, hP₁P, hP₂P, hP₁, hP₂, hunion, _, _⟩ := hP.exists_split_at htP
    have hP₁B : P₁ ≤ B := path_le_right_of_inter_bar_sub_singleton hSep hInter
      (hP₁.mono hP.le) haB ((inter_subset_inter_left _ hP₁P.vertexSet_mono).trans hsub)
    have hP₂B : P₂ ≤ B := path_le_right_of_inter_bar_sub_singleton hSep hInter
      (hP₂.symm.mono hP.le) hbB ((inter_subset_inter_left _ hP₂P.vertexSet_mono).trans hsub)
    have hPB : P ≤ B := by
      rw [(Compatible.of_le_le hP.le hSep.2.1).le_iff]
      have hVP : V(P) = V(P₁) ∪ V(P₂) := by
        rw [← vertexSet_subgraphUnion P P₁ P₂, hunion]
      have hEP : E(P) = E(P₁) ∪ E(P₂) := by
        rw [← edgeSet_subgraphUnion hP₁P hP₂P, hunion]
      rw [hVP, hEP]
      exact ⟨union_subset hP₁B.vertexSet_mono hP₂B.vertexSet_mono,
        union_subset hP₁B.edgeSet_mono hP₂B.edgeSet_mono⟩
    exact hnotB hPB

/-- If `P` is a path in `G` with ends `a, b ∈ V(B)` such that `¬ (P ≤ B)` and `V(P) ∩ Ω_bar ⊆ {a,
b}`,
then `P ≤ A`, `a ∈ Ω_bar`, `b ∈ Ω_bar`, and `a ≠ b`. -/
private theorem path_le_left_of_not_le_right_of_inter_sub_ends {α : Type u} {β : Type v}
    {G A B P : Graph α β} {Ω_bar : Set α} {a b : α}
    (hSep : IsGraphSeparation G A B) (hInter : V(A) ∩ V(B) = Ω_bar)
    (hP : IsGraphPathWithEnds G P a b) (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hnotB : ¬ (P ≤ B)) (hBar_sub : V(P) ∩ Ω_bar ⊆ {a, b}) :
    P ≤ A ∧ a ∈ Ω_bar ∧ b ∈ Ω_bar ∧ a ≠ b := by
  have hAG : A ≤ G := hSep.1
  have hBG : B ≤ G := hSep.2.1
  have hPG : P ≤ G := hP.le
  have hSep_symm : IsGraphSeparation G B A := IsGraphSeparation.symm hSep
  have hInter_symm : V(B) ∩ V(A) = Ω_bar := inter_comm V(B) V(A) ▸ hInter
  by_cases hVB : V(P) ⊆ V(B)
  · have hexE : ∃ f ∈ E(P), f ∉ E(B) := by
      by_contra! hEB
      exact hnotB ((Compatible.of_le_le hPG hBG).le_iff.mpr ⟨hVB, hEB⟩)
    obtain ⟨f, hfP, hfB⟩ := hexE
    have hfG : f ∈ E(G) := hPG.edgeSet_mono hfP
    have hfA : f ∈ E(A) := (hSep.2.2.2.1.symm ▸ hfG).resolve_right hfB
    obtain ⟨u, v, huvP⟩ := P.exists_isLink_of_mem_edgeSet hfP
    have huvA : A.IsLink f u v := (hAG.isLink_iff hfA).mpr (huvP.mono hPG)
    have huBar : u ∈ Ω_bar := hInter ▸ ⟨huvA.left_mem, hVB huvP.left_mem⟩
    have hvBar : v ∈ Ω_bar := hInter ▸ ⟨huvA.right_mem, hVB huvP.right_mem⟩
    have hu_ab : u = a ∨ u = b :=
      mem_insert_iff.mp (hBar_sub ⟨huvP.left_mem, huBar⟩)
    have hv_ab : v = a ∨ v = b :=
      mem_insert_iff.mp (hBar_sub ⟨huvP.right_mem, hvBar⟩)
    have huv_ne : u ≠ v := by
      intro huv_eq
      have hloop : G.IsLink f u u := by
        have huvG : G.IsLink f u v := huvP.mono hPG
        rwa [← huv_eq] at huvG
      exact IsGraphPathWithEnds.not_isLoopAt hP hfP u hloop
    have hlink_ab : P.IsLink f a b ∧ a ∈ Ω_bar ∧ b ∈ Ω_bar ∧ a ≠ b := by
      rcases hu_ab with rfl | rfl <;> rcases hv_ab with rfl | rfl
      · exact False.elim (huv_ne rfl)
      · exact ⟨huvP, huBar, hvBar, huv_ne⟩
      · exact ⟨huvP.symm, hvBar, huBar, huv_ne.symm⟩
      · exact False.elim (huv_ne rfl)
    obtain ⟨_, W, hW, hVP, hEP⟩ := hP
    have hfW : f ∈ W.edges := by
      have hfP' := hfP
      rwa [hEP, mem_ofPred_eq] at hfP'
    obtain ⟨hsupp, hedges⟩ := walk_eq_single_edge_of_isLink_ends hW hfW hlink_ab.1
    have hPA : P ≤ A := by
      rw [(Compatible.of_le_le hPG hAG).le_iff]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [hVP, mem_ofPred_eq, hsupp] at hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact (hInter ▸ hlink_ab.2.1).1
        · rcases List.mem_singleton.mp hx' with rfl
          exact (hInter ▸ hlink_ab.2.2.1).1
      · intro e he
        rw [hEP, mem_ofPred_eq, hedges] at he
        rcases List.mem_singleton.mp he with rfl
        exact hfA
    exact ⟨hPA, hlink_ab.2.1, hlink_ab.2.2.1, hlink_ab.2.2.2⟩
  · obtain ⟨y, hyP, hyB⟩ := not_subset.mp hVB
    have hyA : y ∈ V(A) := (hSep.2.2.1.symm ▸ hPG.vertexSet_mono hyP).resolve_right hyB
    have hya : y ≠ a := fun h => hyB (h ▸ haB)
    have hyb : y ≠ b := fun h => hyB (h ▸ hbB)
    obtain ⟨P₁, P₂, hP₁P, hP₂P, hP₁, hP₂, hunion, hinter, _⟩ := hP.exists_split_at hyP
    have hb_not_P₁ : b ∉ V(P₁) := fun hb₁ => by
      have : b ∈ V(P₁) ∩ V(P₂) := ⟨hb₁, hP₂.right_mem⟩
      rw [hinter, mem_singleton_iff] at this
      exact hyb this.symm
    have ha_not_P₂ : a ∉ V(P₂) := fun ha₂ => by
      have : a ∈ V(P₁) ∩ V(P₂) := ⟨hP₁.left_mem, ha₂⟩
      rw [hinter, mem_singleton_iff] at this
      exact hya this.symm
    have hP₁_bar : V(P₁) ∩ Ω_bar ⊆ {a} := by
      intro z hz
      have hz_ab := hBar_sub ⟨hP₁P.vertexSet_mono hz.1, hz.2⟩
      rcases mem_insert_iff.mp hz_ab with rfl | hzb
      · rfl
      · exact False.elim (hb_not_P₁ (mem_singleton_iff.mp hzb ▸ hz.1))
    have hP₂_bar : V(P₂) ∩ Ω_bar ⊆ {b} := by
      intro z hz
      have hz_ab := hBar_sub ⟨hP₂P.vertexSet_mono hz.1, hz.2⟩
      rcases mem_insert_iff.mp hz_ab with rfl | hzb
      · exact False.elim (ha_not_P₂ hz.1)
      · exact hzb
    have haBar : a ∈ Ω_bar := by
      obtain ⟨w, hwP₁, hwAB⟩ :=
        exists_mem_inter_of_isGraphPathWithEnds hSep_symm (hP₁.mono hPG) haB hyA
      have hwBar : w ∈ Ω_bar := hInter ▸ ⟨hwAB.2, hwAB.1⟩
      have hwa : w = a := mem_singleton_iff.mp (hP₁_bar ⟨hwP₁, hwBar⟩)
      exact hwa ▸ hwBar
    have hbBar : b ∈ Ω_bar := by
      obtain ⟨w, hwP₂, hwAB⟩ :=
        exists_mem_inter_of_isGraphPathWithEnds hSep_symm (hP₂.symm.mono hPG) hbB hyA
      have hwBar : w ∈ Ω_bar := hInter ▸ ⟨hwAB.2, hwAB.1⟩
      have hwb : w = b := mem_singleton_iff.mp (hP₂_bar ⟨hwP₂, hwBar⟩)
      exact hwb ▸ hwBar
    have hab : a ≠ b := fun hab_eq => hb_not_P₁ (hab_eq ▸ hP₁.left_mem)
    have hP₁A : P₁ ≤ A :=
      path_le_right_of_inter_bar_sub_singleton hSep_symm hInter_symm
        (hP₁.symm.mono hPG) hyA hP₁_bar
    have hP₂A : P₂ ≤ A :=
      path_le_right_of_inter_bar_sub_singleton hSep_symm hInter_symm
        (hP₂.mono hPG) hyA hP₂_bar
    have hPA : P ≤ A := by
      rw [(Compatible.of_le_le hPG hAG).le_iff]
      have hVP : V(P) = V(P₁) ∪ V(P₂) := by
        rw [← vertexSet_subgraphUnion P P₁ P₂, hunion]
      have hEP : E(P) = E(P₁) ∪ E(P₂) := by
        rw [← edgeSet_subgraphUnion hP₁P hP₂P, hunion]
      rw [hVP, hEP]
      exact ⟨union_subset hP₁A.vertexSet_mono hP₂A.vertexSet_mono,
        union_subset hP₁A.edgeSet_mono hP₂A.edgeSet_mono⟩
    exact ⟨hPA, haBar, hbBar, hab⟩

/-- If `(A, B)` is a separation of `G` with `V(A) ∩ V(B) = Ω_bar`, `A' ≤ A` with `Ω_bar ⊆ V(A')`,
and `P` is a path in `G` with ends `a, b ∈ V(B)`, then under the chord-replacement hypothesis
`hRepl`, there is a path `P'` in `subgraphUnion G A' B` with ends `a, b` such that
`V(P') ⊆ V(P) ∪ V(A')` and `V(P') ∩ V(B) ⊆ V(P) ∩ V(B)`. -/
theorem exists_chord_endpoints_of_not_le {α : Type u} {β : Type v}
    {G A B A' P : Graph α β} {Ω_bar : Set α} {a b : α}
    (hSep : IsGraphSeparation G A B) (hInter : V(A) ∩ V(B) = Ω_bar)
    (hA'_le : A' ≤ A)
    (hP : IsGraphPathWithEnds G P a b) (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hRepl : ∀ u ∈ Ω_bar, ∀ v ∈ Ω_bar, u ≠ v →
      (∃ Q : Graph α β, IsGraphPathWithEnds A Q u v ∧ V(Q) ∩ Ω_bar = {u, v}) →
      ∃ Q' : Graph α β, IsGraphPathWithEnds A' Q' u v ∧ V(Q') ∩ Ω_bar = {u, v}) :
    ∃ P' : Graph α β,
      IsGraphPathWithEnds (subgraphUnion G A' B) P' a b ∧
      V(P') ⊆ V(P) ∪ V(A') ∧
      V(P') ∩ V(B) ⊆ V(P) ∩ V(B) := by
  classical
  have hAG : A ≤ G := hSep.1
  have hBG : B ≤ G := hSep.2.1
  have hA'G : A' ≤ G := hA'_le.trans hAG
  let U := subgraphUnion G A' B
  have hA'U : A' ≤ U := le_subgraphUnion_left hA'G hBG
  have hBU : B ≤ U := le_subgraphUnion_right hA'G hBG
  have hind : ∀ (n : ℕ) {a₁ b₁ : α} {R : Graph α β},
      IsGraphPathWithEnds G R a₁ b₁ → V(R).ncard = n → a₁ ∈ V(B) → b₁ ∈ V(B) →
      ∃ R' : Graph α β,
        IsGraphPathWithEnds U R' a₁ b₁ ∧
        V(R') ⊆ V(R) ∪ V(A') ∧
        V(R') ∩ V(B) ⊆ V(R) ∩ V(B) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro a₁ b₁ R hR hcard ha₁B hb₁B
      by_cases hRB : R ≤ B
      · exact ⟨R, (hR.of_le hRB).mono hBU, subset_union_left, Subset.rfl⟩
      · by_cases hInt : ∃ w ∈ V(R) ∩ Ω_bar, w ≠ a₁ ∧ w ≠ b₁
        · obtain ⟨w, ⟨hwR, hwBar⟩, hwa₁, hwb₁⟩ := hInt
          have hwB : w ∈ V(B) := (hInter ▸ hwBar).2
          obtain ⟨R₁, R₂, hR₁R, hR₂R, hR₁, hR₂, hunion, hinter, _⟩ := hR.exists_split_at hwR
          have hfin : V(R).Finite := hR.vertexSet_finite
          have hb₁_not_R₁ : b₁ ∉ V(R₁) := fun hb₁ => by
            have : b₁ ∈ V(R₁) ∩ V(R₂) := ⟨hb₁, hR₂.right_mem⟩
            rw [hinter, mem_singleton_iff] at this
            exact hwb₁ this.symm
          have ha₁_not_R₂ : a₁ ∉ V(R₂) := fun ha₁ => by
            have : a₁ ∈ V(R₁) ∩ V(R₂) := ⟨hR₁.left_mem, ha₁⟩
            rw [hinter, mem_singleton_iff] at this
            exact hwa₁ this.symm
          have hlt₁ : V(R₁).ncard < n := by
            rw [← hcard]
            exact Set.ncard_lt_ncard
              ⟨hR₁R.vertexSet_mono, fun hsub => hb₁_not_R₁ (hsub hR.right_mem)⟩ hfin
          have hlt₂ : V(R₂).ncard < n := by
            rw [← hcard]
            exact Set.ncard_lt_ncard
              ⟨hR₂R.vertexSet_mono, fun hsub => ha₁_not_R₂ (hsub hR.left_mem)⟩ hfin
          obtain ⟨R₁', hR₁', hV₁_sub, hV₁_B⟩ :=
            ih V(R₁).ncard hlt₁ (hR₁.mono hR.le) rfl ha₁B hwB
          obtain ⟨R₂', hR₂', hV₂_sub, hV₂_B⟩ :=
            ih V(R₂).ncard hlt₂ (hR₂.mono hR.le) rfl hwB hb₁B
          obtain ⟨hR₁'U, W₁, _, hVR₁', _⟩ := hR₁'
          obtain ⟨hR₂'U, W₂, _, hVR₂', _⟩ := hR₂'
          obtain ⟨W₁', hs₁, _⟩ := exists_walk_up_of_le hR₁'U W₁
          obtain ⟨W₂', hs₂, _⟩ := exists_walk_up_of_le hR₂'U W₂
          obtain ⟨W₀, hW₀, hsupp₀, _⟩ := exists_isSimple_subwalk (W₁'.append W₂')
          let R' := walkSubgraph W₀
          have hR'_path : IsGraphPathWithEnds U R' a₁ b₁ := isGraphPathWithEnds_walkSubgraph hW₀
          have hVR'_sub : V(R') ⊆ V(R₁') ∪ V(R₂') := by
            intro x hx
            rw [vertexSet_walkSubgraph, mem_ofPred_eq] at hx
            have hx_app := hsupp₀ x hx
            rw [GraphWalk.mem_support_append, hs₁, hs₂] at hx_app
            rcases hx_app with hx₁ | hx₂
            · exact Or.inl (by rw [hVR₁', mem_ofPred_eq]; exact hx₁)
            · exact Or.inr (by rw [hVR₂', mem_ofPred_eq]; exact hx₂)
          refine ⟨R', hR'_path, ?_, ?_⟩
          · intro x hx
            rcases hVR'_sub hx with hx₁ | hx₂
            · rcases hV₁_sub hx₁ with hxR₁ | hxA'
              · exact Or.inl (hR₁R.vertexSet_mono hxR₁)
              · exact Or.inr hxA'
            · rcases hV₂_sub hx₂ with hxR₂ | hxA'
              · exact Or.inl (hR₂R.vertexSet_mono hxR₂)
              · exact Or.inr hxA'
          · intro x ⟨hxR', hxB⟩
            rcases hVR'_sub hxR' with hx₁ | hx₂
            · exact ⟨hR₁R.vertexSet_mono (hV₁_B ⟨hx₁, hxB⟩).1, hxB⟩
            · exact ⟨hR₂R.vertexSet_mono (hV₂_B ⟨hx₂, hxB⟩).1, hxB⟩
        · have hBar_sub : V(R) ∩ Ω_bar ⊆ {a₁, b₁} := by
            intro w hw
            simp only [mem_insert_iff, mem_singleton_iff]
            by_contra! hne
            exact hInt ⟨w, hw, hne.1, hne.2⟩
          obtain ⟨hRA, ha₁Bar, hb₁Bar, hab₁⟩ :=
            path_le_left_of_not_le_right_of_inter_sub_ends hSep hInter hR ha₁B hb₁B hRB hBar_sub
          have hR_bar : V(R) ∩ Ω_bar = {a₁, b₁} := by
            refine Subset.antisymm hBar_sub ?_
            rintro w (rfl | rfl)
            · exact ⟨hR.left_mem, ha₁Bar⟩
            · exact ⟨hR.right_mem, hb₁Bar⟩
          obtain ⟨Q', hQ', hQ'_bar⟩ :=
            hRepl a₁ ha₁Bar b₁ hb₁Bar hab₁ ⟨R, hR.of_le hRA, hR_bar⟩
          refine ⟨Q', hQ'.mono hA'U, ?_, ?_⟩
          · exact hQ'.le.vertexSet_mono.trans subset_union_right
          · intro x ⟨hxQ', hxB⟩
            have hxA : x ∈ V(A) := hA'_le.vertexSet_mono (hQ'.le.vertexSet_mono hxQ')
            have hxBar : x ∈ Ω_bar := hInter ▸ ⟨hxA, hxB⟩
            have hx_ab : x ∈ ({a₁, b₁} : Set α) := hQ'_bar ▸ ⟨hxQ', hxBar⟩
            rw [← hR_bar] at hx_ab
            exact ⟨hx_ab.1, hxB⟩
  exact hind V(P).ncard hP rfl haB hbB

/-- **Claim (1) of Graph Minors XIV, (8.4)** (page 41):
If `(A, B)` is a separation of `S₁.G` with `V(A) ∩ V(B) = Ω_bar` (`|Ω_bar| ≤ 3`), `A' ≤ A` with
`Ω_bar ⊆ V(A')` preserves the existence of paths between pairs of vertices in `Ω_bar`, and
`S₁.Ω.bar ⊆ V(B)`, then any crooked transaction of cardinality `≥ pi` in `S₁` yields a crooked
transaction of cardinality `≥ pi` in `S₁'` (where `S₁'.G = subgraphUnion S₁.G A' B` and
`S₁'.Ω = S₁.Ω`). -/
theorem claim_1_of_8_4 {α : Type u} {β : Type v}
    {S₁ S₁' : Society α β} {A B A' : Graph α β} {Ω_bar : Set α}
    (hSep : IsGraphSeparation S₁.G A B) (hInter : V(A) ∩ V(B) = Ω_bar)
    (hBar_fin : Ω_bar.Finite) (hBar_card : Ω_bar.ncard ≤ 3)
    (hA'_le : A' ≤ A)
    (hRepl : ∀ u ∈ Ω_bar, ∀ v ∈ Ω_bar, u ≠ v →
      (∃ Q : Graph α β, IsGraphPathWithEnds A Q u v ∧ V(Q) ∩ Ω_bar = {u, v}) →
      ∃ Q' : Graph α β, IsGraphPathWithEnds A' Q' u v ∧ V(Q') ∩ Ω_bar = {u, v})
    (hΩ₁_B : S₁.Ω.bar ⊆ V(B))
    (hS₁'_G : S₁'.G = subgraphUnion S₁.G A' B) (hS₁'_Ω : S₁'.Ω = S₁.Ω)
    {P_set : Set (Graph α β)} {pi : ℕ}
    (hCrooked : S₁.IsCrookedTransaction P_set)
    (hcard : pi ≤ P_set.ncard) :
    ∃ P_set' : Set (Graph α β),
      S₁'.IsCrookedTransaction P_set' ∧
      pi ≤ P_set'.ncard := by
  classical
  have hAG : A ≤ S₁.G := hSep.1
  have hBG : B ≤ S₁.G := hSep.2.1
  have hA'G : A' ≤ S₁.G := hA'_le.trans hAG
  have hUG : S₁'.G ≤ S₁.G := hS₁'_G ▸ subgraphUnion_le hA'G hBG
  have hBU : B ≤ S₁'.G := hS₁'_G ▸ le_subgraphUnion_right hA'G hBG
  obtain ⟨⟨A_f, B_f, ⟨hPaths, hDisj⟩, hFence, hAB_f⟩, hCross⟩ := hCrooked
  by_cases hall : ∀ P ∈ P_set, P ≤ S₁'.G
  · refine ⟨P_set, ?_, hcard⟩
    have hEnds_eq : S₁'.transactionEnds P_set = S₁.transactionEnds P_set := by
      ext x
      simp only [Society.transactionEnds, mem_ofPred_eq]
      refine exists_congr fun P => and_congr_right fun hP => exists_congr fun b => ?_
      exact (isOmegaPathWithEnds_iff_of_le hUG hS₁'_Ω (hall P hP)).symm
    refine ⟨⟨A_f, B_f, ⟨fun P hP => ?_, hDisj⟩, hS₁'_Ω ▸ hFence, fun P hP => ?_⟩, ?_⟩
    · obtain ⟨a, b, hp⟩ := hPaths P hP
      exact ⟨a, b, (isOmegaPathWithEnds_iff_of_le hUG hS₁'_Ω (hall P hP)).mp hp⟩
    · obtain ⟨a, ha, b, hb, hp⟩ := hAB_f P hP
      exact ⟨a, ha, b, hb, (isOmegaPathWithEnds_iff_of_le hUG hS₁'_Ω (hall P hP)).mp hp⟩
    · intro P hP ⟨_, a, b, hp, hdisj⟩
      have hp_sup := (isOmegaPathWithEnds_iff_of_le hUG hS₁'_Ω (hall P hP)).mpr hp
      exact hCross P hP ⟨hP, a, b, hp_sup, hEnds_eq ▸ hS₁'_Ω ▸ hdisj⟩
  · obtain ⟨P₀, hP₀_mem, hP₀_notU⟩ : ∃ P ∈ P_set, ¬ P ≤ S₁'.G := by
      by_contra! h
      exact hall h
    have hP₀_notB : ¬ (P₀ ≤ B) := fun hB => hP₀_notU (hB.trans hBU)
    obtain ⟨a₀, ha₀_Af, b₀, hb₀_Bf, hP₀_ends⟩ := hAB_f P₀ hP₀_mem
    have ha₀B : a₀ ∈ V(B) := hΩ₁_B hP₀_ends.2.2.1
    have hb₀B : b₀ ∈ V(B) := hΩ₁_B hP₀_ends.2.2.2
    obtain ⟨P₀', hP₀'_path_U, hP₀'_V, hP₀'_B⟩ :=
      exists_chord_endpoints_of_not_le hSep hInter hA'_le hP₀_ends.1 ha₀B hb₀B hRepl
    have hP₀'_path : IsGraphPathWithEnds S₁'.G P₀' a₀ b₀ := hS₁'_G ▸ hP₀'_path_U
    have hP₀'_omega : S₁'.IsOmegaPathWithEnds P₀' a₀ b₀ :=
      ⟨hP₀'_path, hP₀_ends.2.1, hS₁'_Ω ▸ hP₀_ends.2.2.1, hS₁'_Ω ▸ hP₀_ends.2.2.2⟩
    have hother_B : ∀ Q ∈ P_set, Q ≠ P₀ → Q ≤ B := by
      intro Q hQ_mem hQP₀
      by_contra hQ_notB
      obtain ⟨a_Q, b_Q, hQ_ends⟩ := hPaths Q hQ_mem
      have h2_P₀ : 2 ≤ (V(P₀) ∩ Ω_bar).ncard :=
        two_le_ncard_inter_bar_of_not_le_right hSep hInter hBar_fin hP₀_ends.1
          ha₀B hb₀B hP₀_notB
      have h2_Q : 2 ≤ (V(Q) ∩ Ω_bar).ncard :=
        two_le_ncard_inter_bar_of_not_le_right hSep hInter hBar_fin hQ_ends.1
          (hΩ₁_B hQ_ends.2.2.1) (hΩ₁_B hQ_ends.2.2.2) hQ_notB
      exact not_both_two_le_inter_of_ncard_le_three hBar_fin hBar_card
        (hDisj hP₀_mem hQ_mem hQP₀.symm) h2_P₀ h2_Q
    let P_set' : Set (Graph α β) := insert P₀' (P_set \ {P₀})
    have hP₀'_not_diff : P₀' ∉ P_set \ {P₀} := by
      rintro ⟨hP₀'_in, hne⟩
      have ha₀_in : a₀ ∈ V(P₀') ∩ V(P₀) := ⟨hP₀'_path.left_mem, hP₀_ends.1.left_mem⟩
      exact disjoint_left.mp (hDisj hP₀'_in hP₀_mem hne) ha₀_in.1 ha₀_in.2
    have hEnds_eq : S₁'.transactionEnds P_set' = S₁.transactionEnds P_set := by
      ext v
      simp only [Society.transactionEnds, mem_ofPred_eq, P_set', mem_insert_iff, mem_sdiff,
        mem_singleton_iff]
      constructor
      · rintro ⟨Q, rfl | ⟨hQ_in, hQP₀⟩, c, hQc⟩
        · rcases hP₀'_omega.ends_eq S₁' hQc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨P₀, hP₀_mem, c, hP₀_ends⟩
          · exact ⟨P₀, hP₀_mem, c, hP₀_ends.symm S₁⟩
        · exact ⟨Q, hQ_in, c,
            (isOmegaPathWithEnds_iff_of_le hUG hS₁'_Ω ((hother_B Q hQ_in hQP₀).trans hBU)).mpr hQc⟩
      · rintro ⟨Q, hQ_in, c, hQc⟩
        by_cases hQP₀ : Q = P₀
        · subst hQP₀
          rcases hP₀_ends.ends_eq S₁ hQc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨P₀', Or.inl rfl, c, hP₀'_omega⟩
          · exact ⟨P₀', Or.inl rfl, c, hP₀'_omega.symm S₁'⟩
        · exact ⟨Q, Or.inr ⟨hQ_in, hQP₀⟩, c,
            (isOmegaPathWithEnds_iff_of_le hUG hS₁'_Ω ((hother_B Q hQ_in hQP₀).trans hBU)).mp hQc⟩
    have hDisj' : S₁'.IsDisjointOmegaPathSet P_set' := by
      refine ⟨?_, ?_⟩
      · rintro Q (rfl | ⟨hQ_in, hQP₀⟩)
        · exact ⟨a₀, b₀, hP₀'_omega⟩
        · obtain ⟨a_Q, b_Q, hQ_ends⟩ := hPaths Q hQ_in
          exact ⟨a_Q, b_Q,
            (isOmegaPathWithEnds_iff_of_le hUG hS₁'_Ω ((hother_B Q hQ_in hQP₀).trans hBU)).mp
              hQ_ends⟩
      · rintro Q₁ (rfl | ⟨hQ₁_in, hQ₁P₀⟩) Q₂ (rfl | ⟨hQ₂_in, hQ₂P₀⟩) hne
        · exact False.elim (hne rfl)
        · rw [disjoint_left]
          intro x hx₁ hx₂
          have hQ₂_ne : Q₂ ≠ P₀ := hQ₂P₀
          have hxB : x ∈ V(B) := (hother_B Q₂ hQ₂_in hQ₂_ne).vertexSet_mono hx₂
          have hxP₀ : x ∈ V(P₀) := (hP₀'_B ⟨hx₁, hxB⟩).1
          exact disjoint_left.mp (hDisj hP₀_mem hQ₂_in hQ₂_ne.symm) hxP₀ hx₂
        · rw [disjoint_left]
          intro x hx₁ hx₂
          have hQ₁_ne : Q₁ ≠ P₀ := hQ₁P₀
          have hxB : x ∈ V(B) := (hother_B Q₁ hQ₁_in hQ₁_ne).vertexSet_mono hx₁
          have hxP₀ : x ∈ V(P₀) := (hP₀'_B ⟨hx₂, hxB⟩).1
          exact disjoint_left.mp (hDisj hQ₁_in hP₀_mem hQ₁_ne) hx₁ hxP₀
        · exact hDisj hQ₁_in hQ₂_in hne
    have hFenceFor' : S₁'.IsFenceFor P_set' A_f B_f := by
      refine ⟨hDisj', hS₁'_Ω ▸ hFence, ?_⟩
      rintro Q (rfl | ⟨hQ_in, hQP₀⟩)
      · exact ⟨a₀, ha₀_Af, b₀, hb₀_Bf, hP₀'_omega⟩
      · obtain ⟨a_Q, ha_Q, b_Q, hb_Q, hQ_ends⟩ := hAB_f Q hQ_in
        exact ⟨a_Q, ha_Q, b_Q, hb_Q,
          (isOmegaPathWithEnds_iff_of_le hUG hS₁'_Ω ((hother_B Q hQ_in hQP₀).trans hBU)).mp hQ_ends⟩
    have hCrooked' : S₁'.IsCrookedTransaction P_set' := by
      refine ⟨⟨A_f, B_f, hFenceFor'⟩, ?_⟩
      rintro Q (rfl | ⟨hQ_in, hQP₀⟩) ⟨_, a_Q, b_Q, hQ_ends, hdisj_int⟩
      · rcases hP₀'_omega.ends_eq S₁' hQ_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hCross P₀ hP₀_mem ⟨hP₀_mem, a_Q, b_Q, hP₀_ends, hEnds_eq ▸ hS₁'_Ω ▸ hdisj_int⟩
        · exact hCross P₀ hP₀_mem ⟨hP₀_mem, a_Q, b_Q, hP₀_ends.symm S₁,
            hEnds_eq ▸ hS₁'_Ω ▸ hdisj_int⟩
      · have hQ_ends_G : S₁.IsOmegaPathWithEnds Q a_Q b_Q :=
          (isOmegaPathWithEnds_iff_of_le hUG hS₁'_Ω ((hother_B Q hQ_in hQP₀).trans hBU)).mpr hQ_ends
        exact hCross Q hQ_in ⟨hQ_in, a_Q, b_Q, hQ_ends_G, hEnds_eq ▸ hS₁'_Ω ▸ hdisj_int⟩
    have hcard' : P_set'.ncard = P_set.ncard := by
      have hfin : P_set.Finite := Society.IsDisjointOmegaPathSet.finite S₁ ⟨hPaths, hDisj⟩
      have hfin_diff : (P_set \ {P₀}).Finite := hfin.subset sdiff_subset
      rw [ncard_insert_of_notMem hP₀'_not_diff hfin_diff]
      have h_ins : insert P₀ (P_set \ {P₀}) = P_set :=
        insert_sdiff_singleton.trans (insert_eq_of_mem hP₀_mem)
      have hP₀_not_diff : P₀ ∉ P_set \ {P₀} := fun h => h.2 rfl
      rw [← h_ins, ncard_insert_of_notMem hP₀_not_diff hfin_diff, h_ins]
    exact ⟨P_set', hCrooked', hcard' ▸ hcard⟩

/-! ## 4. Circuit and Forest Lemmas for Claim (2) of (8.4) (page 42) -/

/-- A subgraph `A' ≤ S₀.G` preserves `ΩBar`-chords if for all distinct `u, v ∈ ΩBar`, whenever `u`
and
`v` are joined by a path `Q` of `S₀.G` with `V(Q) ∩ ΩBar = {u, v}`, they are also joined by such a
path in `A'` (Graph Minors XIV, Section 8, Claim (1) of (8.4), page 41). -/
def PreservesBarPaths {α : Type u} {β : Type v} (S₀ : Society α β) (A' : Graph α β) : Prop :=
  ∀ u ∈ S₀.Ω.bar, ∀ v ∈ S₀.Ω.bar, u ≠ v →
    (∃ Q : Graph α β, IsGraphPathWithEnds S₀.G Q u v ∧ V(Q) ∩ S₀.Ω.bar = {u, v}) →
    ∃ Q' : Graph α β, IsGraphPathWithEnds A' Q' u v ∧ V(Q') ∩ S₀.Ω.bar = {u, v}

/-- Two internally disjoint and edge-disjoint paths in `G` with the same distinct ends `a, b` form a
circuit `subgraphUnion G P Q` in `G`. -/
theorem isGraphCircuit_subgraphUnion {α : Type u} {β : Type v} {G P Q : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hQ : IsGraphPathWithEnds G Q a b) (hab : a ≠ b)
    (hV : V(P) ∩ V(Q) = {a, b}) (hE : Disjoint E(P) E(Q)) :
    IsGraphCircuit G (subgraphUnion G P Q) := by
  obtain ⟨hPG, W₁, hW₁, hV₁, hE₁⟩ := hP
  obtain ⟨hQG, W₂, hW₂, hV₂, hE₂⟩ := hQ
  have hl := le_subgraphUnion_left hPG hQG
  have hr := le_subgraphUnion_right hPG hQG
  obtain ⟨X₁, hs₁, he₁⟩ := exists_walk_up_of_le hl W₁
  obtain ⟨X₂, hs₂, he₂⟩ := exists_walk_up_of_le hr W₂.reverse
  have hX₁ : X₁.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₁]; exact hW₁
  have hX₂ : X₂.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₂]; exact hW₂.reverse
  have hmem₂ : ∀ x, x ∈ X₂.support ↔ x ∈ W₂.support := by
    intro x
    rw [hs₂, GraphWalk.support_reverse, List.mem_reverse]
  have hmemE₂ : ∀ e, e ∈ X₂.edges ↔ e ∈ W₂.edges := by
    intro e
    rw [he₂, GraphWalk.edges_reverse, List.mem_reverse]
  have hsc := GraphWalk.isSimpleClosed_append hX₁ hX₂ (fun x hx₁ hx₂ => by
      have h₁ : x ∈ V(P) := by rw [hV₁, mem_ofPred_eq]; rwa [hs₁] at hx₁
      have h₂ : x ∈ V(Q) := by rw [hV₂, mem_ofPred_eq]; exact (hmem₂ x).mp hx₂
      have : x ∈ V(P) ∩ V(Q) := ⟨h₁, h₂⟩
      rwa [hV] at this)
    (fun e he₁' he₂' => by
      have h₁ : e ∈ E(P) := by rw [hE₁, mem_ofPred_eq]; rwa [he₁] at he₁'
      have h₂ : e ∈ E(Q) := by rw [hE₂, mem_ofPred_eq]; exact (hmemE₂ e).mp he₂'
      exact disjoint_left.mp hE h₁ h₂)
  refine ⟨subgraphUnion_le hPG hQG, a, X₁.append X₂, hsc, ?_, ?_, ?_⟩
  · rw [GraphWalk.length_append]
    have : X₁.length ≠ 0 := fun h => hab (GraphWalk.eq_of_length_eq_zero h)
    omega
  · rw [vertexSet_subgraphUnion, hV₁, hV₂]
    ext x
    simp only [mem_union, mem_ofPred_eq, GraphWalk.mem_support_append, hmem₂, hs₁]
  · rw [edgeSet_subgraphUnion hPG hQG, hE₁, hE₂]
    ext e
    simp only [mem_union, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append, hmemE₂, he₁]

/-- Any circuit `C` in `G` and any two distinct vertices `a, b ∈ V(C)` decompose `C` into two
edge-disjoint paths `Q₁, Q₂` between `a` and `b` with `V(Q₁) ∩ V(Q₂) = {a, b}`, nonempty edge
sets, and `subgraphUnion G Q₁ Q₂ = C`. -/
theorem IsGraphCircuit.exists_two_paths {α : Type u} {β : Type v}
    {G C : Graph α β} (hC : IsGraphCircuit G C)
    {a b : α} (ha : a ∈ V(C)) (hb : b ∈ V(C)) (hab : a ≠ b) :
    ∃ Q₁ Q₂ : Graph α β,
      Q₁ ≤ C ∧ Q₂ ≤ C ∧
      IsGraphPathWithEnds G Q₁ a b ∧ IsGraphPathWithEnds G Q₂ a b ∧
      E(Q₁).Nonempty ∧ E(Q₂).Nonempty ∧
      V(Q₁) ∩ V(Q₂) = {a, b} ∧ Disjoint E(Q₁) E(Q₂) ∧
      subgraphUnion G Q₁ Q₂ = C := by
  obtain ⟨hCG, u, W, ⟨hnd, hed⟩, -, hV, hE⟩ := hC
  rw [hV] at ha hb
  obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem ha
  set Rot := W₂.append W₁ with hRot
  have hmemRot : ∀ x, x ∈ Rot.support ↔ x ∈ (W₁.append W₂).support := by
    intro x
    rw [hRot, GraphWalk.mem_support_append, GraphWalk.mem_support_append, or_comm]
  have hmemE : ∀ e, e ∈ Rot.edges ↔ e ∈ (W₁.append W₂).edges := by
    intro e
    rw [hRot, GraphWalk.edges_append, GraphWalk.edges_append, List.mem_append, List.mem_append,
      or_comm]
  have htail : Rot.support.tail.Nodup := by
    have h1 : (W₁.append W₂).support.tail = W₁.support.tail ++ W₂.support.tail := by
      rw [GraphWalk.support_append, W₁.support_eq_cons]; simp
    have h2 : Rot.support.tail = W₂.support.tail ++ W₁.support.tail := by
      rw [hRot, GraphWalk.support_append, W₂.support_eq_cons]; simp
    rw [h2]
    rw [h1] at hnd
    exact (List.perm_append_comm.nodup_iff).mp hnd
  have hedRot : Rot.edges.Nodup := by
    rw [hRot, GraphWalk.edges_append]
    rw [GraphWalk.edges_append] at hed
    exact (List.perm_append_comm.nodup_iff).mp hed
  obtain ⟨R₁, R₂, hR⟩ := Rot.exists_append_of_mem ((hmemRot b).mpr hb)
  have htail' : (R₁.support.tail ++ R₂.support.tail).Nodup := by
    have : Rot.support.tail = R₁.support.tail ++ R₂.support.tail := by
      rw [hR, GraphWalk.support_append, R₁.support_eq_cons]; simp
    rwa [this] at htail
  have hdisjT := List.nodup_append.mp htail'
  have hbt₁ : b ∈ R₁.support.tail := by
    have h := R₁.end_mem_support
    rw [R₁.support_eq_cons] at h
    exact (List.mem_cons.mp h).resolve_left hab.symm
  have hat₂ : a ∈ R₂.support.tail := by
    have h := R₂.end_mem_support
    rw [R₂.support_eq_cons] at h
    exact (List.mem_cons.mp h).resolve_left hab
  have hS₁ : R₁.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [R₁.support_eq_cons]
    exact List.nodup_cons.mpr ⟨fun h => hdisjT.2.2 a h a hat₂ rfl, hdisjT.1⟩
  have hS₂ : R₂.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [R₂.support_eq_cons]
    exact List.nodup_cons.mpr ⟨fun h => hdisjT.2.2 b hbt₁ b h rfl, hdisjT.2.1⟩
  have hedR : (R₁.edges ++ R₂.edges).Nodup := by
    rw [hR, GraphWalk.edges_append] at hedRot
    exact hedRot
  have hedD := List.nodup_append.mp hedR
  let Q₁ := walkSubgraph R₁
  let Q₂ := walkSubgraph R₂.reverse
  have hQ₁C : Q₁ ≤ C := walkSubgraph_le R₁
  have hQ₂C : Q₂ ≤ C := walkSubgraph_le R₂.reverse
  have hQ₁_path : IsGraphPathWithEnds G Q₁ a b :=
    (isGraphPathWithEnds_walkSubgraph hS₁).mono hCG
  have hQ₂_path : IsGraphPathWithEnds G Q₂ a b :=
    (isGraphPathWithEnds_walkSubgraph hS₂.reverse).mono hCG
  have hE_ne : ∀ {x y : α} (R : GraphWalk C x y), x ≠ y → E(walkSubgraph R).Nonempty := by
    intro x y R hxy
    have hne : R.edges ≠ [] := by
      intro h
      have : R.length = 0 := by simp [GraphWalk.length, h]
      exact hxy (GraphWalk.eq_of_length_eq_zero this)
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨e, by rw [edgeSet_walkSubgraph]; exact he⟩
  refine ⟨Q₁, Q₂, hQ₁C, hQ₂C, hQ₁_path, hQ₂_path, hE_ne R₁ hab, hE_ne R₂.reverse hab, ?_, ?_, ?_⟩
  · rw [vertexSet_walkSubgraph, vertexSet_walkSubgraph]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_reverse, List.mem_reverse,
      mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      rw [R₁.support_eq_cons] at h₁
      rw [R₂.support_eq_cons] at h₂
      rcases List.mem_cons.mp h₁ with h₁ | h₁
      · exact Or.inl h₁
      · rcases List.mem_cons.mp h₂ with h₂ | h₂
        · exact Or.inr h₂
        · exact (hdisjT.2.2 x h₁ x h₂ rfl).elim
    · rintro (rfl | rfl)
      · exact ⟨R₁.start_mem_support, R₂.end_mem_support⟩
      · exact ⟨R₁.end_mem_support, R₂.start_mem_support⟩
  · rw [edgeSet_walkSubgraph, edgeSet_walkSubgraph]
    refine disjoint_left.mpr fun e he₁ he₂ => ?_
    simp only [mem_ofPred_eq, GraphWalk.edges_reverse, List.mem_reverse] at he₁ he₂
    exact hedD.2.2 e he₁ e he₂ rfl
  · refine (Compatible.of_le_le (subgraphUnion_le (hQ₁C.trans hCG) (hQ₂C.trans hCG)) hCG).ext ?_ ?_
    · rw [vertexSet_subgraphUnion, vertexSet_walkSubgraph, vertexSet_walkSubgraph, hV]
      ext x
      simp only [mem_union, mem_ofPred_eq, GraphWalk.support_reverse, List.mem_reverse]
      rw [← hmemRot x, hR, GraphWalk.mem_support_append]
    · rw [edgeSet_subgraphUnion (hQ₁C.trans hCG) (hQ₂C.trans hCG), edgeSet_walkSubgraph,
        edgeSet_walkSubgraph, hE]
      ext e
      simp only [mem_union, mem_ofPred_eq, GraphWalk.edges_reverse, List.mem_reverse]
      rw [← hmemE e, hR, GraphWalk.edges_append, List.mem_append]

/-- If `s` is finite and `s.ncard ≤ 1`, any two elements of `s` are equal. -/
private theorem eq_of_mem_of_ncard_le_one {γ : Type*} {s : Set γ}
    (hs : s.Finite) (h : s.ncard ≤ 1) {a b : γ} (ha : a ∈ s) (hb : b ∈ s) : a = b := by
  by_contra hab
  have hsub : ({a, b} : Set γ) ⊆ s := by
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  have h2 : 2 ≤ s.ncard := by
    rw [← ncard_pair hab]
    exact ncard_le_ncard hsub hs
  omega

/-- Given a circuit `C` in `G`, two distinct vertices `a ≠ b` of `C`, and a finite set `Z` with
`Z.ncard ≤ 1`, at least one of the two arcs of `C` between `a` and `b` avoids `Z \ {a, b}`. -/
theorem exists_path_in_circuit_avoiding_of_ncard_le_one {α : Type u} {β : Type v}
    {G C : Graph α β} {a b : α} {Z : Set α}
    (hC : IsGraphCircuit G C) (ha : a ∈ V(C)) (hb : b ∈ V(C)) (hab : a ≠ b)
    (hZ_fin : Z.Finite) (hZ : Z.ncard ≤ 1) :
    ∃ R : Graph α β, IsGraphPathWithEnds C R a b ∧ V(R) ∩ Z ⊆ {a, b} := by
  obtain ⟨Q₁, Q₂, hQ₁C, hQ₂C, hQ₁, hQ₂, -, -, hV, -, -⟩ :=
    IsGraphCircuit.exists_two_paths hC ha hb hab
  by_cases hz : ∃ z ∈ Z, z ∈ V(Q₁) \ {a, b}
  · obtain ⟨z, hzZ, hzQ₁⟩ := hz
    refine ⟨Q₂, hQ₂.of_le hQ₂C, ?_⟩
    rintro x ⟨hxQ₂, hxZ⟩
    have hxz : x = z := eq_of_mem_of_ncard_le_one hZ_fin hZ hxZ hzZ
    subst hxz
    have hx_inter : x ∈ V(Q₁) ∩ V(Q₂) := ⟨hzQ₁.1, hxQ₂⟩
    rwa [hV] at hx_inter
  · refine ⟨Q₁, hQ₁.of_le hQ₁C, ?_⟩
    rintro x ⟨hxQ₁, hxZ⟩
    by_contra hx_ab
    exact hz ⟨x, hxZ, hxQ₁, hx_ab⟩

/-- Every walk `W` meeting a vertex set `X` splits at the first vertex `v ∈ X` into a prefix `W₁`
(meeting `X` only at its last vertex `v`) and a suffix `W₂` starting at `v`. -/
private theorem exists_first_hit_split {α : Type u} {β : Type v} {G : Graph α β} {a b : α}
    (W : GraphWalk G a b) {X : Set α} (hne : ∃ x ∈ W.support, x ∈ X) :
    ∃ v ∈ X, ∃ (W₁ : GraphWalk G a v) (W₂ : GraphWalk G v b),
      W = W₁.append W₂ ∧ ∀ x ∈ W₁.support, x ∈ X → x = v := by
  induction W with
  | @nil a h =>
    obtain ⟨x, hx, hxX⟩ := hne
    have hxa : x = a := List.mem_singleton.mp hx
    exact ⟨a, hxa ▸ hxX, .nil h, .nil h, rfl, fun y hy _ => List.mem_singleton.mp hy⟩
  | @cons a w b e hl r ih =>
    by_cases haX : a ∈ X
    · exact ⟨a, haX, .nil hl.left_mem, .cons hl r, rfl, fun y hy _ => List.mem_singleton.mp hy⟩
    · have hne_r : ∃ x ∈ r.support, x ∈ X := by
        obtain ⟨x, hx, hxX⟩ := hne
        rcases List.mem_cons.mp hx with rfl | hxr
        · exact (haX hxX).elim
        · exact ⟨x, hxr, hxX⟩
      obtain ⟨v, hvX, W₁, W₂, rfl, hfirst⟩ := ih hne_r
      refine ⟨v, hvX, .cons hl W₁, W₂, rfl, fun x hx hxX => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx₁
      · exact (haX hxX).elim
      · exact hfirst x hx₁ hxX

/-- In a simple walk `W`, no edge in `W.edges` can be a loop `G.IsLink f z z`. -/
private theorem not_isLink_self_of_mem_edges_of_isSimple {α : Type u} {β : Type v}
    {G : Graph α β} {a b z : α} {f : β}
    (W : GraphWalk G a b) (hW : W.IsSimple) (hf : f ∈ W.edges) (hl : G.IsLink f z z) : False := by
  induction W with
  | nil _ => simp at hf
  | @cons u v _ e₀ hl₀ r₀ ih =>
    rcases List.mem_cons.mp hf with rfl | hfr₀
    · have huz : u = z := by rcases hl₀.left_eq_or_eq hl with h | h <;> exact h
      have hvz : v = z := by rcases hl₀.symm.left_eq_or_eq hl with h | h <;> exact h
      have huv : u = v := huz.trans hvz.symm
      exact (List.nodup_cons.mp hW).1 (huv ▸ r₀.start_mem_support)
    · exact ih (List.nodup_cons.mp hW).2 hfr₀

/-- Along a simple walk `W : GraphWalk G a b` with `a, b ∈ V(C)` (where `C ≤ G`), either every
vertex and edge of `W` lies in `C`, or there is a detour path `P_sub` in `G` between distinct
vertices `v, v' ∈ V(C)` with `V(P_sub) ∩ V(C) = {v, v'}` and `Disjoint E(P_sub) E(C)`. -/
private theorem walk_le_or_exists_detour {α : Type u} {β : Type v}
    {G C : Graph α β} (hCG : C ≤ G) {a b : α} (W : GraphWalk G a b)
    (hW : W.IsSimple) (ha : a ∈ V(C)) (hb : b ∈ V(C)) :
    ((∀ x ∈ W.support, x ∈ V(C)) ∧ (∀ e ∈ W.edges, e ∈ E(C))) ∨
      ∃ v ∈ V(C), ∃ v' ∈ V(C), v ≠ v' ∧
        ∃ P_sub : Graph α β, IsGraphPathWithEnds G P_sub v v' ∧
          V(P_sub) ∩ V(C) = {v, v'} ∧ Disjoint E(P_sub) E(C) := by
  induction W with
  | @nil a _ =>
    left
    exact ⟨fun x hx => (List.mem_singleton.mp hx) ▸ ha, fun _ he => (List.not_mem_nil he).elim⟩
  | @cons a w b e hl r ih =>
    have ha_not_r : a ∉ r.support := (List.nodup_cons.mp hW).1
    have hr_s : r.IsSimple := (List.nodup_cons.mp hW).2
    by_cases heC : e ∈ E(C)
    · have hlC : C.IsLink e a w := (hCG.isLink_iff heC).mpr hl
      have hwC : w ∈ V(C) := hlC.right_mem
      rcases ih hr_s hwC hb with ⟨hV_r, hE_r⟩ | hex
      · left
        refine ⟨fun x hx => ?_, fun f hf => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hxr
          · exact ha
          · exact hV_r x hxr
        · rcases List.mem_cons.mp hf with rfl | hfr
          · exact heC
          · exact hE_r f hfr
      · exact Or.inr hex
    · right
      have hhit : ∃ x ∈ r.support, x ∈ V(C) := ⟨b, r.end_mem_support, hb⟩
      obtain ⟨v', hv'C, r₁, r₂, hsplit_r, hr₁_first⟩ := exists_first_hit_split r hhit
      have hr₁_s : r₁.IsSimple := (isSimple_of_append (hsplit_r ▸ hr_s)).1
      have ha_not_r₁ : a ∉ r₁.support := fun ha_in =>
        ha_not_r (hsplit_r ▸ (GraphWalk.mem_support_append r₁ r₂).mpr (Or.inl ha_in))
      have hcons_r₁_s : (GraphWalk.cons hl r₁).IsSimple :=
        List.nodup_cons.mpr ⟨ha_not_r₁, hr₁_s⟩
      have hav' : a ≠ v' := fun h => ha_not_r₁ (h ▸ r₁.end_mem_support)
      have hr₁_no_edge : ∀ f ∈ r₁.edges, f ∉ E(C) := by
        intro f hf₁ hfC
        obtain ⟨x, y, hxyC⟩ := C.exists_isLink_of_mem_edgeSet hfC
        have hxyG : G.IsLink f x y := hxyC.mono hCG
        have hx_s : x ∈ r₁.support := r₁.left_mem_support_of_mem_edges hf₁ hxyG
        have hy_s : y ∈ r₁.support := r₁.left_mem_support_of_mem_edges hf₁ hxyG.symm
        have hxv' : x = v' := hr₁_first x hx_s hxyC.left_mem
        have hyv' : y = v' := hr₁_first y hy_s hxyC.right_mem
        subst hxv' hyv'
        exact not_isLink_self_of_mem_edges_of_isSimple r₁ hr₁_s hf₁ hxyG
      refine ⟨a, ha, v', hv'C, hav', walkSubgraph (GraphWalk.cons hl r₁),
        isGraphPathWithEnds_walkSubgraph hcons_r₁_s, ?_, ?_⟩
      · rw [vertexSet_walkSubgraph]
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons,
          mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨rfl | hx₁, hxC⟩
          · exact Or.inl rfl
          · exact Or.inr (hr₁_first x hx₁ hxC)
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, ha⟩
          · exact ⟨Or.inr r₁.end_mem_support, hv'C⟩
      · rw [edgeSet_walkSubgraph]
        refine disjoint_left.mpr fun f hf hfC => ?_
        rcases List.mem_cons.mp hf with rfl | hf₁
        · exact heC hfC
        · exact hr₁_no_edge f hf₁ hfC

/-- In a graph `G` with no circuits (a forest), any two paths `P₁, P₂` with the same ends `u, v`
are equal. -/
theorem eq_of_isGraphPathWithEnds_of_no_circuit {α : Type u} {β : Type v}
    {G P₁ P₂ : Graph α β} {u v : α}
    (hForest : ¬ ∃ C : Graph α β, IsGraphCircuit G C)
    (hP₁ : IsGraphPathWithEnds G P₁ u v)
    (hP₂ : IsGraphPathWithEnds G P₂ u v) :
    P₁ = P₂ := by
  have hle : ∀ {A B : Graph α β},
      IsGraphPathWithEnds G A u v → IsGraphPathWithEnds G B u v → A ≤ B := by
    intro A B hA hB
    obtain ⟨hAG, W, hW, hVA, hEA⟩ := hA
    obtain ⟨WG, hsG, heG⟩ := exists_walk_up_of_le hAG W
    have hWG_s : WG.IsSimple := by unfold GraphWalk.IsSimple; rw [hsG]; exact hW
    rcases walk_le_or_exists_detour hB.1 WG hWG_s hB.left_mem hB.right_mem with
      ⟨hV_sub, hE_sub⟩ | ⟨x, hxB, y, hyB, hxy, P_sub, hP_sub, hVC, hEC⟩
    · rw [(Compatible.of_le_le hAG hB.1).le_iff, hVA, hEA]
      refine ⟨fun z hz => hV_sub z (hsG ▸ hz), fun e he => hE_sub e (heG ▸ he)⟩
    · exfalso
      obtain ⟨Q, hQB, hQ_path, hQG⟩ := hB.exists_subpath hxB hyB
      have hVQ : V(P_sub) ∩ V(Q) = {x, y} := by
        refine Subset.antisymm ?_ ?_
        · rw [← hVC]
          exact inter_subset_inter_right _ hQB.vertexSet_mono
        · rintro z (rfl | rfl)
          · exact ⟨hP_sub.left_mem, hQ_path.left_mem⟩
          · exact ⟨hP_sub.right_mem, hQ_path.right_mem⟩
      have hEQ : Disjoint E(P_sub) E(Q) :=
        hEC.mono_right hQB.edgeSet_mono
      exact hForest ⟨subgraphUnion G P_sub Q,
        isGraphCircuit_subgraphUnion hP_sub hQG hxy hVQ hEQ⟩
  exact (Compatible.of_le_le hP₁.1 hP₂.1).ext
    (Subset.antisymm (hle hP₁ hP₂).vertexSet_mono (hle hP₂ hP₁).vertexSet_mono)
    (Subset.antisymm (hle hP₁ hP₂).edgeSet_mono (hle hP₂ hP₁).edgeSet_mono)

/-- If every two elements of `s` are equal, then `s.ncard ≤ 1`. -/
private theorem ncard_le_one_of_subsingleton_set {γ : Type*} {s : Set γ}
    (h : ∀ a ∈ s, ∀ b ∈ s, a = b) : s.ncard ≤ 1 := by
  by_cases hne : s.Nonempty
  · obtain ⟨a, ha⟩ := hne
    have heq : s = {a} := Subset.antisymm
      (fun b hb => mem_singleton_iff.mpr (h b hb a ha))
      (singleton_subset_iff.mpr ha)
    rw [heq, ncard_singleton]
  · rw [not_nonempty_iff_eq_empty.mp hne, ncard_empty]
    exact Nat.zero_le 1

/-- If a graph `G` has at most 1 edge (`E(G).Subsingleton`), then it has at most 1 circuit. -/
theorem ncard_circuits_le_one_of_ncard_edges_le_one {α : Type u} {β : Type v}
    {G : Graph α β} (hE : E(G).Subsingleton) :
    {C : Graph α β | IsGraphCircuit G C}.ncard ≤ 1 := by
  refine ncard_le_one_of_subsingleton_set fun C₁ hC₁ C₂ hC₂ => ?_
  have hchar : ∀ {C : Graph α β}, IsGraphCircuit G C →
      ∃ e ∈ E(G), ∃ x y : α, G.IsLink e x y ∧ V(C) = {x, y} ∧ E(C) = {e} := by
    intro C ⟨hCG, u, W, _, hlen, hVC, hEC⟩
    cases W with
    | nil _ => simp [GraphWalk.length] at hlen
    | @cons u w _ e₁ hl₁ r₁ =>
      have he₁C : e₁ ∈ E(C) := by rw [hEC]; exact List.mem_cons_self
      have he₁G : e₁ ∈ E(G) := hCG.edgeSet_mono he₁C
      have hl₁G : G.IsLink e₁ u w := hl₁.mono hCG
      have hEC_eq : E(C) = {e₁} := by
        refine Subset.antisymm (fun f hf => ?_) (singleton_subset_iff.mpr he₁C)
        have hfG : f ∈ E(G) := hCG.edgeSet_mono hf
        exact mem_singleton_iff.mpr (hE hfG he₁G)
      have hVC_eq : V(C) = {u, w} := by
        refine Subset.antisymm (fun z hz => ?_) ?_
        · rw [hVC, mem_ofPred_eq] at hz
          rcases List.mem_cons.mp hz with rfl | hzr₁
          · exact Or.inl rfl
          · have hwalk : ∀ {a b : α} (R : GraphWalk C a b),
                b ∈ ({u, w} : Set α) → ∀ x ∈ R.support, x ∈ ({u, w} : Set α) := by
              intro a b R hbR
              induction R with
              | nil _ =>
                intro x hx
                rw [List.mem_singleton.mp hx]
                exact hbR
              | @cons a a' b f hlf Rf ih =>
                intro x hx
                rcases List.mem_cons.mp hx with rfl | hxRf
                · have hfC : f ∈ E(C) := hlf.edge_mem
                  rw [hEC_eq, mem_singleton_iff] at hfC
                  subst hfC
                  rcases hlf.left_eq_or_eq hl₁ with h | h
                  · exact Or.inl h
                  · exact Or.inr h
                · exact ih hbR x hxRf
            exact hwalk r₁ (Or.inl rfl) z hzr₁
        · rintro z (rfl | rfl)
          · exact hl₁.left_mem
          · exact hl₁.right_mem
      exact ⟨e₁, he₁G, u, w, hl₁G, hVC_eq, hEC_eq⟩
  obtain ⟨e₁, he₁G, x₁, y₁, hl₁, hV₁, hE₁⟩ := hchar hC₁
  obtain ⟨e₂, he₂G, x₂, y₂, hl₂, hV₂, hE₂⟩ := hchar hC₂
  have he₁₂ : e₁ = e₂ := hE he₁G he₂G
  subst he₁₂
  have hxy_eq : ({x₁, y₁} : Set α) = {x₂, y₂} := by
    ext z
    simp only [mem_insert_iff, mem_singleton_iff]
    exact ⟨fun h => by
        rcases h with rfl | rfl
        · exact hl₁.left_eq_or_eq hl₂
        · exact hl₁.symm.left_eq_or_eq hl₂,
      fun h => by
        rcases h with rfl | rfl
        · exact hl₂.left_eq_or_eq hl₁
        · exact hl₂.symm.left_eq_or_eq hl₁⟩
  exact (Compatible.of_le_le hC₁.1 hC₂.1).ext
    (hV₁.trans (hxy_eq.trans hV₂.symm))
    (hE₁.trans hE₂.symm)

/-- If a graph `G` has no circuits, then `{C | IsGraphCircuit G C}.ncard ≤ 1`. -/
theorem ncard_circuits_le_one_of_no_circuits {α : Type u} {β : Type v}
    {G : Graph α β} (hForest : ¬ ∃ C : Graph α β, IsGraphCircuit G C) :
    {C : Graph α β | IsGraphCircuit G C}.ncard ≤ 1 := by
  refine ncard_le_one_of_subsingleton_set fun C hC => (hForest ⟨C, hC⟩).elim

/-- If `W : GraphWalk G x y` is a simple walk and `e ∈ W.edges` satisfies `G.IsLink e x y`, then
`V(walkSubgraph W) = {x, y}` and `E(walkSubgraph W) = {e}`. -/
private theorem walkSubgraph_eq_of_mem_edges_isLink_ends {α : Type u} {β : Type v}
    {G : Graph α β} {x y : α} {e : β} (W : GraphWalk G x y) (hW : W.IsSimple)
    (he : e ∈ W.edges) (hl : G.IsLink e x y) :
    V(walkSubgraph W) = {x, y} ∧ E(walkSubgraph W) = {e} := by
  cases W with
  | nil _ => simp at he
  | @cons x w y e₀ hl₀ r =>
    have hx_not_r : x ∉ r.support := (List.nodup_cons.mp hW).1
    have hr_s : r.IsSimple := (List.nodup_cons.mp hW).2
    have he_not_r : e ∉ r.edges := fun he_r =>
      hx_not_r (r.left_mem_support_of_mem_edges he_r hl)
    have he_eq : e = e₀ := (List.mem_cons.mp he).resolve_right he_not_r
    subst he_eq
    have hwy : w = y := by
      rcases hl₀.symm.left_eq_or_eq hl.symm with h | h
      · exact h
      · exact (hx_not_r (h ▸ r.start_mem_support)).elim
    subst hwy
    cases r with
    | nil _ =>
      rw [vertexSet_walkSubgraph, edgeSet_walkSubgraph]
      refine ⟨?_, ?_⟩
      · ext z
        simp [GraphWalk.support_cons, GraphWalk.support_nil]
      · ext f
        simp [GraphWalk.edges_cons, GraphWalk.edges_nil]
    | @cons w _ _ e₁ hl₁ r₁ =>
      exfalso
      exact (List.nodup_cons.mp hr_s).1 r₁.end_mem_support

/-- Adding a single edge `e` (with distinct endpoints `x ≠ y`) to a forest `B` produces a graph `G`
with at most one circuit. -/
theorem ncard_circuits_le_one_of_insert_edge {α : Type u} {β : Type v}
    {G B : Graph α β} {e : β} {x y : α}
    (hBG : B ≤ G)
    (hForest : ¬ ∃ C : Graph α β, IsGraphCircuit B C)
    (hl : G.IsLink e x y)
    (hxy : x ≠ y)
    (hV : V(G) = V(B))
    (hE : E(G) ⊆ insert e E(B)) :
    {C : Graph α β | IsGraphCircuit G C}.ncard ≤ 1 := by
  have hchar : ∀ {C : Graph α β}, IsGraphCircuit G C →
      ∃ Q : Graph α β, IsGraphPathWithEnds B Q x y ∧
        V(C) = V(Q) ∧ E(C) = insert e E(Q) := by
    intro C hC
    have heC : e ∈ E(C) := by
      by_contra he_not
      have hCB : C ≤ B := by
        rw [(Compatible.of_le_le hC.1 hBG).le_iff]
        refine ⟨hV ▸ hC.1.vertexSet_mono, fun f hf => ?_⟩
        rcases mem_insert_iff.mp (hE (hC.1.edgeSet_mono hf)) with rfl | hfB
        · exact (he_not hf).elim
        · exact hfB
      obtain ⟨_, u, W, hW_sc, hW_len, hVC, hEC⟩ := hC
      exact hForest ⟨C, hCB, u, W, hW_sc, hW_len, hVC, hEC⟩
    have hlC : C.IsLink e x y := (hC.1.isLink_iff heC).mpr hl
    have hxC : x ∈ V(C) := hlC.left_mem
    have hyC : y ∈ V(C) := hlC.right_mem
    obtain ⟨Q₁, Q₂, hQ₁C, hQ₂C, hQ₁, hQ₂, -, -, hVQ, hEQ, hUnion⟩ :=
      IsGraphCircuit.exists_two_paths hC hxC hyC hxy
    have he_union : e ∈ E(Q₁) ∪ E(Q₂) := by
      rw [← edgeSet_subgraphUnion (hQ₁C.trans hC.1) (hQ₂C.trans hC.1), hUnion]
      exact heC
    have hbranch : ∀ {A D : Graph α β},
        A ≤ C → D ≤ C →
        IsGraphPathWithEnds G A x y → IsGraphPathWithEnds G D x y →
        Disjoint E(A) E(D) → subgraphUnion G A D = C → e ∈ E(A) →
        IsGraphPathWithEnds B D x y ∧ V(C) = V(D) ∧ E(C) = insert e E(D) := by
      intro A D _ _ hA hD hED hAD heA
      obtain ⟨hAG, WA, hWA_s, hVA, hEA⟩ := hA
      obtain ⟨WAG, hsA, heA_walk⟩ := exists_walk_up_of_le hAG WA
      have hWAG_s : WAG.IsSimple := by unfold GraphWalk.IsSimple; rw [hsA]; exact hWA_s
      have he_WAG : e ∈ WAG.edges := by
        rw [heA_walk]
        rwa [hEA] at heA
      obtain ⟨hVA_eq, hEA_eq⟩ := walkSubgraph_eq_of_mem_edges_isLink_ends WAG hWAG_s he_WAG hl
      have hVA' : V(A) = {x, y} := by
        rw [hVA, ← hsA, ← vertexSet_walkSubgraph, hVA_eq]
      have hEA' : E(A) = {e} := by
        rw [hEA, ← heA_walk, ← edgeSet_walkSubgraph, hEA_eq]
      have he_not_D : e ∉ E(D) := disjoint_left.mp hED heA
      have hDB : D ≤ B := by
        rw [(Compatible.of_le_le hD.1 hBG).le_iff]
        refine ⟨hV ▸ hD.1.vertexSet_mono, fun f hf => ?_⟩
        rcases mem_insert_iff.mp (hE (hD.1.edgeSet_mono hf)) with rfl | hfB
        · exact (he_not_D hf).elim
        · exact hfB
      refine ⟨hD.of_le hDB, ?_, ?_⟩
      · rw [← hAD, vertexSet_subgraphUnion, hVA']
        exact union_eq_right.mpr (by
          rintro z (rfl | rfl)
          · exact hD.left_mem
          · exact hD.right_mem)
      · rw [← hAD, edgeSet_subgraphUnion hAG hD.1, hEA', singleton_union]
    rcases he_union with he₁ | he₂
    · obtain ⟨hQ₂B, hVC, hEC⟩ := hbranch hQ₁C hQ₂C hQ₁ hQ₂ hEQ hUnion he₁
      exact ⟨Q₂, hQ₂B, hVC, hEC⟩
    · have hUnion' : subgraphUnion G Q₂ Q₁ = C := by
        rw [← hUnion]
        refine (Compatible.of_le_le (subgraphUnion_le hQ₂.1 hQ₁.1)
          (subgraphUnion_le hQ₁.1 hQ₂.1)).ext ?_ ?_
        · rw [vertexSet_subgraphUnion, vertexSet_subgraphUnion, union_comm]
        · rw [edgeSet_subgraphUnion hQ₂.1 hQ₁.1, edgeSet_subgraphUnion hQ₁.1 hQ₂.1, union_comm]
      obtain ⟨hQ₁B, hVC, hEC⟩ := hbranch hQ₂C hQ₁C hQ₂ hQ₁ hEQ.symm hUnion' he₂
      exact ⟨Q₁, hQ₁B, hVC, hEC⟩
  refine ncard_le_one_of_subsingleton_set fun C₁ hC₁ C₂ hC₂ => ?_
  obtain ⟨Q₁, hQ₁, hV₁, hE₁⟩ := hchar hC₁
  obtain ⟨Q₂, hQ₂, hV₂, hE₂⟩ := hchar hC₂
  have hQ_eq : Q₁ = Q₂ := eq_of_isGraphPathWithEnds_of_no_circuit hForest hQ₁ hQ₂
  subst hQ_eq
  exact (Compatible.of_le_le hC₁.1 hC₂.1).ext (hV₁.trans hV₂.symm) (hE₁.trans hE₂.symm)

/-- Given a separation `(A, B)` of `G` with `V(A) ∩ V(B) = Ω_bar`, a subgraph `C ≤ A`, and three
mutually vertex-disjoint paths `P₀, P₁, P₂` in `G` from `u i ∈ V(C)` to `v i ∈ V(B) ∪ Ω_bar`, there
are three mutually vertex-disjoint paths `Q₀, Q₁, Q₂` in `A` (`Q i ≤ P i`) with
`IsFromToPathWithEnds A (Q i) V(C) Ω_bar (x i) (y i)` (Graph Minors XIV, Section 6, Claim (2) of
(6.5), page 35, and Section 8, Claim (2) of (8.4), page 42). -/
theorem exists_three_disjoint_paths_from_circuit_to_bar {α : Type u} {β : Type v}
    {G A B C : Graph α β} {Ω_bar : Set α}
    (hSep : IsGraphSeparation G A B) (hInter : V(A) ∩ V(B) = Ω_bar) (hCA : C ≤ A)
    {P : Fin 3 → Graph α β} {u v : Fin 3 → α}
    (hP : ∀ i, IsGraphPathWithEnds G (P i) (u i) (v i) ∧ u i ∈ V(C) ∧ v i ∈ V(B) ∪ Ω_bar)
    (hDisj : Pairwise (fun i j => Disjoint V(P i) V(P j))) :
    ∃ (Q : Fin 3 → Graph α β) (x y : Fin 3 → α),
      (∀ i, Q i ≤ P i ∧ IsFromToPathWithEnds A (Q i) V(C) Ω_bar (x i) (y i)) ∧
      Pairwise (fun i j => Disjoint V(Q i) V(Q j)) := by
  have hSep_symm : IsGraphSeparation G B A := IsGraphSeparation.symm hSep
  have hInter_symm : V(B) ∩ V(A) = Ω_bar := inter_comm V(B) V(A) ▸ hInter
  have hex : ∀ i : Fin 3, ∃ x y : α, ∃ Q : Graph α β,
      Q ≤ P i ∧ IsFromToPathWithEnds A Q V(C) Ω_bar x y := by
    intro i
    obtain ⟨hPi, huC, hvB⟩ := hP i
    have huA : u i ∈ V(A) := hCA.vertexSet_mono huC
    have hw_ex : ∃ w ∈ V(P i), w ∈ Ω_bar := by
      rcases hvB with hv_in_B | hv_in_bar
      · obtain ⟨hPiG, W, _, hVP, _⟩ := hPi
        obtain ⟨WG, hsG, _⟩ := exists_walk_up_of_le hPiG W
        obtain ⟨w, hwW, hwBar⟩ :=
          walk_inter_bar_of_isGraphSeparation hSep_symm hInter_symm WG huA hv_in_B
        exact ⟨w, by rw [hVP, mem_ofPred_eq]; exact hsG ▸ hwW, hwBar⟩
      · exact ⟨v i, hPi.right_mem, hv_in_bar⟩
    obtain ⟨w, hwP, hwBar⟩ := hw_ex
    obtain ⟨P₁, _, hP₁P, _, hP₁, _, _, _, _⟩ := hPi.exists_split_at hwP
    obtain ⟨x, _, y, _, Q, hQP₁, hQ_ft⟩ :=
      (hP₁.mono hPi.le).exists_isFromToPathWithEnds huC hwBar
    have hxC : x ∈ V(C) := (hQ_ft.2.1 ▸ mem_singleton x).2
    have hQA : Q ≤ A :=
      path_le_right_of_inter_bar_sub_singleton hSep_symm hInter_symm hQ_ft.1
        (hCA.vertexSet_mono hxC) (le_of_eq hQ_ft.2.2)
    exact ⟨x, y, Q, hQP₁.trans hP₁P, hQ_ft.1.of_le hQA, hQ_ft.2⟩
  choose x y Q hQ using hex
  refine ⟨Q, x, y, hQ, fun i j hij => ?_⟩
  exact (hDisj hij).mono (hQ i).1.vertexSet_mono (hQ j).1.vertexSet_mono

/-- Circuit case of Claim (2) of (8.4) (page 42): if `H_inter_A ≤ S₀.G` contains a circuit `C` and
three mutually vertex-disjoint paths `P₀, P₁, P₂` from `V(C)` to `S₀.Ω.bar` (with
`S₀.Ω.bar.ncard ≤ 3`), then `S₀.Ω.bar ⊆ V(H_inter_A)`, `E(H_inter_A).Nonempty`, and
`PreservesBarPaths S₀ H_inter_A`. -/
theorem preservesBarPaths_of_three_disjoint_paths_from_circuit {α : Type u} {β : Type v}
    {S₀ : Society α β} {H_inter_A C : Graph α β}
    (hBar3 : S₀.Ω.bar.ncard ≤ 3)
    (hC : IsGraphCircuit H_inter_A C)
    {P : Fin 3 → Graph α β} {x y : Fin 3 → α}
    (hP : ∀ i, IsFromToPathWithEnds H_inter_A (P i) V(C) S₀.Ω.bar (x i) (y i))
    (hDisj : Pairwise (fun i j => Disjoint V(P i) V(P j))) :
    S₀.Ω.bar ⊆ V(H_inter_A) ∧ E(H_inter_A).Nonempty ∧ PreservesBarPaths S₀ H_inter_A := by
  classical
  have hy_mem_bar : ∀ i, y i ∈ S₀.Ω.bar := fun i =>
    ((hP i).2.2 ▸ mem_singleton (y i)).2
  have hx_mem_C : ∀ i, x i ∈ V(C) := fun i =>
    ((hP i).2.1 ▸ mem_singleton (x i)).2
  have hy_inj : Function.Injective y := by
    intro i j hij
    by_contra hne
    have hyi : y i ∈ V(P i) := (hP i).1.right_mem
    have hyj : y i ∈ V(P j) := hij ▸ (hP j).1.right_mem
    exact disjoint_left.mp (hDisj hne) hyi hyj
  have hx_inj : Function.Injective x := by
    intro i j hij
    by_contra hne
    have hxi : x i ∈ V(P i) := (hP i).1.left_mem
    have hxj : x i ∈ V(P j) := hij ▸ (hP j).1.left_mem
    exact disjoint_left.mp (hDisj hne) hxi hxj
  have hy_range_sub : range y ⊆ S₀.Ω.bar := by
    rintro z ⟨i, rfl⟩
    exact hy_mem_bar i
  have hy_range_card : (range y).ncard = 3 := by
    rw [ncard_range_of_injective hy_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hy_range_eq : range y = S₀.Ω.bar :=
    eq_of_subset_of_ncard_le hy_range_sub (by omega) S₀.Ω.finite_bar
  have hBar_sub : S₀.Ω.bar ⊆ V(H_inter_A) := by
    intro z hz
    rw [← hy_range_eq] at hz
    rcases hz with ⟨i, rfl⟩
    exact (hP i).1.1.vertexSet_mono (hP i).1.right_mem
  have hE_ne : E(H_inter_A).Nonempty := by
    obtain ⟨hCH, u, W, _, hlen, _, hEC⟩ := hC
    have hW_ne : W.edges ≠ [] := fun h => by simp [GraphWalk.length, h] at hlen
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hW_ne
    exact ⟨e, hCH.edgeSet_mono (by rw [hEC]; exact he)⟩
  refine ⟨hBar_sub, hE_ne, ?_⟩
  intro u hu v hv huv _
  have hu_r : u ∈ range y := hy_range_eq.symm ▸ hu
  have hv_r : v ∈ range y := hy_range_eq.symm ▸ hv
  rcases hu_r with ⟨i, rfl⟩
  rcases hv_r with ⟨j, rfl⟩
  have hij : i ≠ j := fun h => huv (h ▸ rfl)
  have hxi_C : x i ∈ V(C) := hx_mem_C i
  have hxj_C : x j ∈ V(C) := hx_mem_C j
  have hxi_ne_xj : x i ≠ x j := fun h => hij (hx_inj h)
  let Z : Set α := (fun k => x k) '' {k : Fin 3 | k ≠ i ∧ k ≠ j}
  have hZ_fin : Z.Finite := (toFinite _).image _
  have hZ_le : Z.ncard ≤ 1 := by
    refine ncard_le_one_of_subsingleton_set ?_
    rintro z₁ ⟨k₁, ⟨hk₁i, hk₁j⟩, rfl⟩ z₂ ⟨k₂, ⟨hk₂i, hk₂j⟩, rfl⟩
    have hk_eq : k₁ = k₂ := by omega
    rw [hk_eq]
  obtain ⟨R, hR_path, hRZ⟩ :=
    exists_path_in_circuit_avoiding_of_ncard_le_one hC hxi_C hxj_C hxi_ne_xj hZ_fin hZ_le
  have hR_H : IsGraphPathWithEnds H_inter_A R (x i) (x j) := hR_path.mono hC.1
  obtain ⟨hPi_le, Wi, hWi_s, hVi, _⟩ := (hP i).1.symm
  obtain ⟨hR_le, WR, hWR_s, hVR, _⟩ := hR_H
  obtain ⟨hPj_le, Wj, hWj_s, hVj, _⟩ := (hP j).1
  obtain ⟨Wi', hs_i, _⟩ := exists_walk_up_of_le hPi_le Wi
  obtain ⟨WR', hs_R, _⟩ := exists_walk_up_of_le hR_le WR
  obtain ⟨Wj', hs_j, _⟩ := exists_walk_up_of_le hPj_le Wj
  obtain ⟨W₀, hW₀_s, hsupp₀, _⟩ := exists_isSimple_subwalk ((Wi'.append WR').append Wj')
  let Q' := walkSubgraph W₀
  refine ⟨Q', isGraphPathWithEnds_walkSubgraph hW₀_s, ?_⟩
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨hzQ', hzBar⟩
    rw [vertexSet_walkSubgraph, mem_ofPred_eq] at hzQ'
    have hz_app := hsupp₀ z hzQ'
    rw [GraphWalk.mem_support_append, GraphWalk.mem_support_append, hs_i, hs_R, hs_j] at hz_app
    have hz_V : z ∈ (V(P i) ∪ V(R)) ∪ V(P j) := by
      rcases hz_app with (hzi | hzR) | hzj
      · exact Or.inl (Or.inl (by rw [hVi]; exact hzi))
      · exact Or.inl (Or.inr (by rw [hVR]; exact hzR))
      · exact Or.inr (by rw [hVj]; exact hzj)
    rcases hz_V with (hzi | hzR) | hzj
    · have : z ∈ V(P i) ∩ S₀.Ω.bar := ⟨hzi, hzBar⟩
      rw [(hP i).2.2, mem_singleton_iff] at this
      exact Or.inl this
    · have hzC : z ∈ V(C) := hR_path.1.vertexSet_mono hzR
      have hz_r : z ∈ range y := hy_range_eq.symm ▸ hzBar
      rcases hz_r with ⟨m, rfl⟩
      have hym_C : y m ∈ V(P m) ∩ V(C) := ⟨(hP m).1.right_mem, hzC⟩
      rw [(hP m).2.1, mem_singleton_iff] at hym_C
      by_cases hmi : m = i
      · subst hmi; exact Or.inl rfl
      · by_cases hmj : m = j
        · subst hmj; exact Or.inr rfl
        · exfalso
          have hxm_Z : x m ∈ Z := ⟨m, ⟨hmi, hmj⟩, rfl⟩
          have hxm_R : x m ∈ V(R) := hym_C ▸ hzR
          have hxm_ij : x m ∈ {x i, x j} := hRZ ⟨hxm_R, hxm_Z⟩
          rcases hxm_ij with h_eq | h_eq
          · exact hmi (hx_inj h_eq)
          · exact hmj (hx_inj h_eq)
    · have : z ∈ V(P j) ∩ S₀.Ω.bar := ⟨hzj, hzBar⟩
      rw [(hP j).2.2, mem_singleton_iff] at this
      exact Or.inr this
  · rintro z (rfl | rfl)
    · exact ⟨by rw [vertexSet_walkSubgraph]; exact W₀.start_mem_support, hy_mem_bar i⟩
    · exact ⟨by rw [vertexSet_walkSubgraph]; exact W₀.end_mem_support, hy_mem_bar j⟩

/-- In the forest case of Claim (2) of (8.4) (page 42), if `P₁` is a path in `A'` from `u` to `x`
with `V(P₁) ∩ S₀.Ω.bar ⊆ {u, v}`, `A'.IsLink e x y`, and `P₂` is a path in `A'` from `y` to `v` with
`V(P₂) ∩ S₀.Ω.bar ⊆ {u, v}` (for `u, v ∈ S₀.Ω.bar`), then there is a path `Q'` in `A'` from `u` to
`v` with `V(Q') ∩ S₀.Ω.bar = {u, v}`. -/
theorem exists_bar_chord_of_link_between_branches {α : Type u} {β : Type v}
    {S₀ : Society α β} {A' P₁ P₂ : Graph α β} {u v x y : α} {e : β}
    (hu : u ∈ S₀.Ω.bar) (hv : v ∈ S₀.Ω.bar)
    (hP₁ : IsGraphPathWithEnds A' P₁ u x) (hP₁_bar : V(P₁) ∩ S₀.Ω.bar ⊆ {u, v})
    (hl : A'.IsLink e x y)
    (hP₂ : IsGraphPathWithEnds A' P₂ y v) (hP₂_bar : V(P₂) ∩ S₀.Ω.bar ⊆ {u, v}) :
    ∃ Q' : Graph α β, IsGraphPathWithEnds A' Q' u v ∧ V(Q') ∩ S₀.Ω.bar = {u, v} := by
  obtain ⟨hP₁_le, W₁, _, hV₁, _⟩ := hP₁
  obtain ⟨hP₂_le, W₂, _, hV₂, _⟩ := hP₂
  obtain ⟨W₁', hs₁, _⟩ := exists_walk_up_of_le hP₁_le W₁
  obtain ⟨W₂', hs₂, _⟩ := exists_walk_up_of_le hP₂_le W₂
  obtain ⟨W₀, hW₀_s, hsupp₀, _⟩ := exists_isSimple_subwalk (W₁'.append (GraphWalk.cons hl W₂'))
  let Q' := walkSubgraph W₀
  refine ⟨Q', isGraphPathWithEnds_walkSubgraph hW₀_s, ?_⟩
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨hzQ', hzBar⟩
    rw [vertexSet_walkSubgraph, mem_ofPred_eq] at hzQ'
    have hz_app := hsupp₀ z hzQ'
    rw [GraphWalk.mem_support_append, GraphWalk.support_cons, List.mem_cons, hs₁, hs₂] at hz_app
    rcases hz_app with hz₁ | (rfl | hz₂)
    · exact hP₁_bar ⟨by rw [hV₁]; exact hz₁, hzBar⟩
    · exact hP₁_bar ⟨by rw [hV₁]; exact W₁.end_mem_support, hzBar⟩
    · exact hP₂_bar ⟨by rw [hV₂]; exact hz₂, hzBar⟩
  · rintro z (rfl | rfl)
    · exact ⟨by rw [vertexSet_walkSubgraph]; exact W₀.start_mem_support, hu⟩
    · exact ⟨by rw [vertexSet_walkSubgraph]; exact W₀.end_mem_support, hv⟩

end GraphMinor.GM14
