/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2a
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section2e
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.Section4a
import LeanPool.GraphMinor.GM09.Section4c
import LeanPool.GraphMinor.GM09.Section5a
import LeanPool.GraphMinor.GM09.Section5b
import LeanPool.GraphMinor.GM09.Section6
import LeanPool.GraphMinor.GM09.Section7
import LeanPool.GraphMinor.GM09.Section8
import LeanPool.GraphMinor.GM09.Section9
import LeanPool.GraphMinor.GM09.Section11b
import LeanPool.GraphMinor.GM09.NestUncrossing
import LeanPool.GraphMinor.GM06.Section2Dual
import LeanPool.GraphMinor.GM06.Section3Dual
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.Crossing
import Mathlib.Data.Set.Card

/-!
# Graph Minors IX, Section 10: Rural Neighborhoods of Large Breadth ((10.2)–(10.5))

This file formalizes (10.2), (10.3), (10.4), and (10.5) from Section 10 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 64–67).
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06

universe u v w

variable {α : Type u} {β : Type v}

/-- In a nest `C : Fin m → Graph α β` of `N`, any circuit `C j` with `j < k` is vertex-disjoint
from `N.Ω.bar`. -/
theorem disjoint_vertexSet_bar_of_isNest_lt {N : Neighborhood α β} {P_pres : Presentation N}
    {m : ℕ} {C : Fin m → Graph α β} (hC : N.IsNest P_pres C) {j k : Fin m} (hjk : j < k) :
    Disjoint V(C j) N.Ω.bar := by
  obtain ⟨hC_cir, hC_disj, D, hD_disc, hD_sub, hD_mono⟩ := hC
  rw [disjoint_left]
  intro v hvCj hv_bar
  have hvN : v ∈ V(N.G) := N.bar_subset hv_bar
  have hv_bdΔ : graphDrawingVertexSet P_pres.Γ v ⊆ subBd P_pres.Δ :=
    (P_pres.mem_bd_Δ_iff v hvN).mpr hv_bar
  have hv_Dj : graphDrawingVertexSet P_pres.Γ v ⊆ D j := by
    refine (graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hvCj).trans ?_
    rw [← (hD_disc j).2]
    exact subBd_subset_of_isClosed (isClosed_of_isClosedDisc (hD_disc j).1)
  have hv_Dk : graphDrawingVertexSet P_pres.Γ v ⊆ D k :=
    hv_Dj.trans (hD_mono j k (le_of_lt hjk))
  have hv_bdDk : graphDrawingVertexSet P_pres.Γ v ⊆ graphDrawingSubgraphU P_pres.Γ (C k) := by
    rw [← (hD_disc k).2]
    exact (subset_inter hv_Dk hv_bdΔ).trans (inter_subBd_subset_subBd (hD_sub k).2)
  have hvCk : v ∈ V(C k) :=
    mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU P_pres.Γ (hC_cir k).1 hvN hv_bdDk
  exact disjoint_left.mp (hC_disj (ne_of_lt hjk)) hvCj hvCk

/-- Every walk in `N.G` from `x ∈ N.Ω.bar` to `y ∈ N.Ω₀.bar` meets every circuit `C j` of a nest `C`
in `N`. -/
theorem exists_mem_support_circuit_of_isNest {N : Neighborhood α β} {P_pres : Presentation N}
    {m : ℕ} {C : Fin m → Graph α β} (hC : N.IsNest P_pres C) (j : Fin m)
    {x y : α} (W : GraphWalk N.G x y) (hx : x ∈ N.Ω.bar) (hy : y ∈ N.Ω₀.bar) :
    ∃ v ∈ W.support, v ∈ V(C j) := by
  by_cases hxC : x ∈ V(C j)
  · exact ⟨x, W.start_mem_support, hxC⟩
  · obtain ⟨hC_cir, _, D, hD_disc, hD_sub, _⟩ := hC
    have hxN : x ∈ V(N.G) := N.bar_subset hx
    have hyN : y ∈ V(N.G) := N.bar₀_subset hy
    have hxc : graphDrawingVertexSet P_pres.Γ x ⊆ (D j)ᶜ := by
      intro p hp hpD
      have hp_sub : graphDrawingVertexSet P_pres.Γ x ⊆ {p} := by
        rw [graphDrawingVertexSet_eq_singleton P_pres.Γ hxN] at hp ⊢
        rw [mem_singleton_iff.mp hp]
      have hp_bdΔ : p ∈ subBd P_pres.Δ := (P_pres.mem_bd_Δ_iff x hxN).mpr hx hp
      have hp_bdDj : p ∈ graphDrawingSubgraphU P_pres.Γ (C j) := by
        rw [← (hD_disc j).2]
        exact inter_subBd_subset_subBd (hD_sub j).2 ⟨hpD, hp_bdΔ⟩
      have hv_sub : graphDrawingVertexSet P_pres.Γ x ⊆ graphDrawingSubgraphU P_pres.Γ (C j) :=
        hp_sub.trans (singleton_subset_iff.mpr hp_bdDj)
      exact hxC (mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU P_pres.Γ
        (hC_cir j).1 hxN hv_sub)
    have hyD : graphDrawingVertexSet P_pres.Γ y ⊆ D j := by
      refine ((P_pres.mem_bd_Δ₀_iff y hyN).mpr hy).trans ?_
      refine inter_subset_left.trans ?_
      rw [← (isClosed_of_isClosedDisc (hD_disc j).1).closure_eq]
      exact closure_mono (hD_sub j).1
    exact exists_mem_support_of_subBd_eq_subgraphU P_pres.Γ (hC_cir j).1 (hD_disc j).2 W hxc hyD

/-- In a composition `S_comp.IsComposition S₀ N` with `Y ⊆ V(S₀.G)`, every path `R` in `S_comp.G`
from `S_comp.Ω.bar` to `Y` meets every circuit `C j` of a nest `C` in `N`. -/
theorem nonempty_inter_circuit_of_isFromToPath_comp {S_comp S₀ : Society α β}
    {N : Neighborhood α β} {Y : Set α} (hcomp : S_comp.IsComposition S₀ N) (hY : Y ⊆ V(S₀.G))
    {P_pres : Presentation N} {m : ℕ} {C : Fin m → Graph α β} (hC : N.IsNest P_pres C)
    (j : Fin m) {R : Graph α β} (hR : IsFromToPath S_comp.G R S_comp.Ω.bar Y) :
    (V(R) ∩ V(C j)).Nonempty := by
  obtain ⟨x₀, y₀, hR_ends⟩ := hR
  have hx₀ : x₀ ∈ S_comp.Ω.bar := hR_ends.left_mem_X
  have hy₀ : y₀ ∈ Y := hR_ends.right_mem_Y
  obtain ⟨x', hx'x₀, v₀, hv₀S₀, Q, hQR, hQ_ends⟩ :=
    hR_ends.1.exists_isFromToPathWithEnds (X := {x₀}) (Y := V(S₀.G)) (mem_singleton x₀) (hY hy₀)
  rw [mem_singleton_iff] at hx'x₀
  subst x'
  have hQ_p : IsGraphPathWithEnds S_comp.G Q x₀ v₀ := hQ_ends.1
  have hEQ_N : E(Q) ⊆ E(N.G) := by
    intro e heQ
    have he_comp : e ∈ E(S_comp.G) := hQ_p.le.edgeSet_mono heQ
    rw [← hcomp.1.1.2.2.2.1] at he_comp
    rcases he_comp with heS₀ | heN
    · exfalso
      obtain ⟨a, b, habS₀⟩ := S₀.G.exists_isLink_of_mem_edgeSet heS₀
      obtain ⟨a', b', habQ⟩ := Q.exists_isLink_of_mem_edgeSet heQ
      have ha'S₀ : a' ∈ V(S₀.G) := by
        rcases (habQ.mono hQ_p.le).left_eq_or_eq (habS₀.mono hcomp.1.1.1) with rfl | rfl
        · exact habS₀.left_mem
        · exact habS₀.right_mem
      have hb'S₀ : b' ∈ V(S₀.G) := by
        rcases (habQ.symm.mono hQ_p.le).left_eq_or_eq (habS₀.mono hcomp.1.1.1) with rfl | rfl
        · exact habS₀.left_mem
        · exact habS₀.right_mem
      have ha'v₀ : a' = v₀ := by
        have : a' ∈ V(Q) ∩ V(S₀.G) := ⟨habQ.left_mem, ha'S₀⟩
        rwa [hQ_ends.2.2, mem_singleton_iff] at this
      have hb'v₀ : b' = v₀ := by
        have : b' ∈ V(Q) ∩ V(S₀.G) := ⟨habQ.right_mem, hb'S₀⟩
        rwa [hQ_ends.2.2, mem_singleton_iff] at this
      subst a' b'
      exact hQ_p.not_isLoopAt heQ v₀ (habQ.mono hQ_p.le)
    · exact heN
  have hx₀_bar : x₀ ∈ N.Ω.bar := hcomp.2.1.symm ▸ hx₀
  have hVQ_N : V(Q) ⊆ V(N.G) := by
    intro z hzQ
    rcases eq_or_ne z x₀ with rfl | hzx₀
    · exact N.bar_subset hx₀_bar
    · have hne : x₀ ≠ v₀ := by
        rintro rfl
        obtain ⟨Q₁, Q₂, _, _, hQ₁, hQ₂, _, hinter, _⟩ := hQ_p.exists_split_at hzQ
        have hx₀_in : x₀ ∈ V(Q₁) ∩ V(Q₂) := ⟨hQ₁.left_mem, hQ₂.right_mem⟩
        rw [hinter, mem_singleton_iff] at hx₀_in
        exact hzx₀ hx₀_in.symm
      obtain ⟨e, heQ, w, hzw⟩ := hQ_p.exists_inc_of_mem_of_ne hne hzQ
      obtain ⟨a, b, habN⟩ := N.G.exists_isLink_of_mem_edgeSet (hEQ_N heQ)
      rcases (hzw.mono hQ_p.le).left_eq_or_eq (habN.mono hcomp.1.1.2.1) with rfl | rfl
      · exact habN.left_mem
      · exact habN.right_mem
  have hQ_N : Q ≤ N.G :=
    (Compatible.of_le_le hQ_p.le hcomp.1.1.2.1).le_iff.mpr ⟨hVQ_N, hEQ_N⟩
  have hQ_pathN : IsGraphPathWithEnds N.G Q x₀ v₀ := hQ_p.of_le hQ_N
  obtain ⟨_, W_Q, _, hVQ, _⟩ := hQ_pathN
  obtain ⟨WN, hsN, _⟩ := exists_walk_up_of_le hQ_N W_Q
  have hv₀_bar₀ : v₀ ∈ N.Ω₀.bar := by
    rw [hcomp.2.2.1, hcomp.2.2.2]
    exact ⟨hv₀S₀, hVQ_N hQ_p.right_mem⟩
  obtain ⟨v, hvWN, hvCj⟩ := exists_mem_support_circuit_of_isNest hC j WN hx₀_bar hv₀_bar₀
  rw [hsN] at hvWN
  have hvQ : v ∈ V(Q) := by rw [hVQ]; exact hvWN
  exact ⟨v, hQR.vertexSet_mono hvQ, hvCj⟩

/-- If `C` is a circuit in `G` and `(V(C) ∩ Z).ncard ≤ 1`, then any two vertices `u, v ∈ V(C) \ Z`
are joined by a path `Q ≤ C` avoiding `Z`. -/
theorem exists_path_in_circuit_avoiding_of_ncard_le_one {G C : Graph α β}
    (hC : IsGraphCircuit G C) {Z : Set α} (hZ : (V(C) ∩ Z).ncard ≤ 1)
    {u v : α} (huC : u ∈ V(C)) (hvC : v ∈ V(C)) (huZ : u ∉ Z) (hvZ : v ∉ Z) :
    ∃ Q : Graph α β, Q ≤ C ∧ IsGraphPathWithEnds G Q u v ∧ Disjoint V(Q) Z := by
  classical
  by_cases huv : u = v
  · subst huv
    let W₀ : GraphWalk C u u := .nil huC
    have hW₀_s : W₀.IsSimple := by simp [W₀, GraphWalk.IsSimple]
    refine ⟨walkSubgraph W₀, walkSubgraph_le W₀,
      (isGraphPathWithEnds_walkSubgraph hW₀_s).mono hC.1, ?_⟩
    rw [vertexSet_walkSubgraph]
    simp [W₀, huZ]
  · obtain ⟨Q₁, Q₂, hQ₁C, hQ₂C, hQ₁_p, hQ₂_p, _, _, hVQ_inter, _, _⟩ :=
      hC.exists_two_paths huC hvC huv
    by_cases hdisj₁ : Disjoint V(Q₁) Z
    · exact ⟨Q₁, hQ₁C, hQ₁_p, hdisj₁⟩
    · refine ⟨Q₂, hQ₂C, hQ₂_p, ?_⟩
      by_contra hdisj₂
      rw [not_disjoint_iff_nonempty_inter] at hdisj₁ hdisj₂
      obtain ⟨z₁, hz₁Q₁, hz₁Z⟩ := hdisj₁
      obtain ⟨z₂, hz₂Q₂, hz₂Z⟩ := hdisj₂
      have hz₁_not_Q₂ : z₁ ∉ V(Q₂) := by
        intro hz₁Q₂
        have : z₁ ∈ V(Q₁) ∩ V(Q₂) := ⟨hz₁Q₁, hz₁Q₂⟩
        rw [hVQ_inter] at this
        rcases this with rfl | rfl
        · exact huZ hz₁Z
        · exact hvZ hz₁Z
      have hz₁₂ : z₁ ≠ z₂ := fun h => hz₁_not_Q₂ (h ▸ hz₂Q₂)
      have hVC_fin : V(C).Finite := by
        obtain ⟨_, _, W, _, _, hVC, _⟩ := hC
        rw [hVC]
        exact W.support.toFinset.finite_toSet.subset fun x hx => List.mem_toFinset.mpr hx
      have hsub : ({z₁, z₂} : Set α) ⊆ V(C) ∩ Z := by
        rintro x (rfl | rfl)
        · exact ⟨hQ₁C.vertexSet_mono hz₁Q₁, hz₁Z⟩
        · exact ⟨hQ₂C.vertexSet_mono hz₂Q₂, hz₂Z⟩
      have hcard := ncard_le_ncard hsub (hVC_fin.inter_of_left Z)
      rw [ncard_pair hz₁₂] at hcard
      omega

/-- Pigeonhole principle for `r` pairwise disjoint sets `A i`: if `Z` is finite with `Z.ncard < r`,
then some `A i` is disjoint from `Z`. -/
theorem exists_disjoint_of_pairwise_disjoint_of_ncard_lt {r : ℕ} {A : Fin r → Set α}
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) {Z : Set α} (hZ : Z.Finite)
    (hcard : Z.ncard < r) :
    ∃ i : Fin r, Disjoint (A i) Z := by
  induction r generalizing Z with
  | zero => omega
  | succ r ih =>
    by_cases h0 : Disjoint (A 0) Z
    · exact ⟨0, h0⟩
    · rw [not_disjoint_iff_nonempty_inter] at h0
      have hpos : 1 ≤ (Z ∩ A 0).ncard := (ncard_pos (hZ.inter_of_left _)).mpr
        (by rwa [inter_comm])
      have h_add := ncard_inter_add_ncard_sdiff_eq_ncard Z (A 0) hZ
      have hcard' : (Z \ A 0).ncard < r := by omega
      have hdisj' : Pairwise (fun i j : Fin r => Disjoint (A i.succ) (A j.succ)) :=
        fun i j hij => hdisj (Fin.succ_inj.ne.mpr hij)
      obtain ⟨i, hi⟩ := ih hdisj' hZ.sdiff hcard'
      refine ⟨i.succ, disjoint_left.mpr fun x hxA hxZ => ?_⟩
      have hx_not_0 : x ∉ A 0 :=
        disjoint_left.mp (hdisj (Fin.succ_ne_zero i)) hxA
      exact disjoint_left.mp hi hxA ⟨hxZ, hx_not_0⟩

/-- Pigeonhole principle for `s` pairwise disjoint sets `A j`: if `Z` is finite with
`Z.ncard < 2 * s`, then some `A j` meets `Z` in at most 1 element. -/
theorem exists_ncard_inter_le_one_of_pairwise_disjoint {s : ℕ} {A : Fin s → Set α}
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) {Z : Set α} (hZ : Z.Finite)
    (hcard : Z.ncard < 2 * s) :
    ∃ j : Fin s, (A j ∩ Z).ncard ≤ 1 := by
  induction s generalizing Z with
  | zero => omega
  | succ s ih =>
    by_cases h0 : (A 0 ∩ Z).ncard ≤ 1
    · exact ⟨0, h0⟩
    · have hge2 : 2 ≤ (Z ∩ A 0).ncard := by rw [inter_comm]; omega
      have h_add := ncard_inter_add_ncard_sdiff_eq_ncard Z (A 0) hZ
      have hcard' : (Z \ A 0).ncard < 2 * s := by omega
      have hdisj' : Pairwise (fun i j : Fin s => Disjoint (A i.succ) (A j.succ)) :=
        fun i j hij => hdisj (Fin.succ_inj.ne.mpr hij)
      obtain ⟨j, hj⟩ := ih hdisj' hZ.sdiff hcard'
      refine ⟨j.succ, ?_⟩
      have heq : A j.succ ∩ Z = A j.succ ∩ (Z \ A 0) := by
        ext x
        simp only [mem_inter_iff, mem_sdiff]
        exact ⟨fun ⟨hxA, hxZ⟩ => ⟨hxA, hxZ, disjoint_left.mp (hdisj (Fin.succ_ne_zero j)) hxA⟩,
          fun ⟨hxA, hxZ, _⟩ => ⟨hxA, hxZ⟩⟩
      rwa [heq]

/-! ## 2. Proof of (10.5) (pages 66–67) -/

/-- **Graph Minors IX, (10.5)** (page 66):
"Let $p \ge 0$ and let $(G, \Omega, \Omega_0)$ be a rural neighborhood of breadth
$\ge \frac{1}{2} p + 1$. Let $X \subseteq \bar{\Omega}$ be linked, with $|X| \ge p$. Let
$(G \cup G_0, \Omega)$ be the composition of some society $(G_0, \Omega_0)$ with $(G, \Omega,
\Omega_0)$,
and let $Y \subseteq V(G_0)$. Then either there are $p$ mutually disjoint paths of $G \cup G_0$ from
$X$ to $Y$, each with only its initial vertex in $\bar{\Omega}$, or there exists
$W \subseteq V(G \cup G_0)$ with $|W| < p$ and $W \cap \bar{\Omega} = \emptyset$ such that every
path of
$G \cup G_0$ from $\bar{\Omega}$ to $Y$ has a vertex in $W$." -/
theorem theorem_10_5_proof {S_comp S₀ : Society α β} {N : Neighborhood α β}
    {p : ℕ} {X Y : Set α}
    (_hrural : N.IsRural) (hbreadth : N.HasBreadthGe ((p + 1) / 2 + 1))
    (hX : N.IsLinked X) (hpX : p ≤ X.ncard)
    (hcomp : S_comp.IsComposition S₀ N) (hY : Y ⊆ V(S₀.G)) :
    (∃ P : Fin p → Graph α β,
      (∀ i, ∃ x ∈ X, ∃ y ∈ Y, IsFromToPathWithEnds S_comp.G (P i) S_comp.Ω.bar Y x y) ∧
      Pairwise (fun i j => Disjoint V(P i) V(P j))) ∨
    (∃ W ⊆ V(S_comp.G), W.ncard < p ∧ Disjoint W S_comp.Ω.bar ∧
      ∀ P : Graph α β, IsFromToPath S_comp.G P S_comp.Ω.bar Y → (V(P) ∩ W).Nonempty) := by
  let s := (p + 1) / 2
  obtain ⟨P_pres, C', hC'⟩ := hbreadth
  let C : Fin s → Graph α β := fun j => C' ⟨j.1, by omega⟩
  have hC_disj_bar : ∀ j : Fin s, Disjoint V(C j) S_comp.Ω.bar := by
    intro j
    rw [← hcomp.2.1]
    exact disjoint_vertexSet_bar_of_isNest_lt hC' (k := ⟨s, Nat.lt_succ_self s⟩) j.2
  have hC_disj : Pairwise (fun i j : Fin s => Disjoint V(C i) V(C j)) :=
    fun i j hij => hC'.2.1 (by intro h; exact hij (Fin.ext (Fin.mk.inj h)))
  let G' := deleteVertices S_comp.G (S_comp.Ω.bar \ X)
  have hG'_le : G' ≤ S_comp.G := deleteVertices_le S_comp.G (S_comp.Ω.bar \ X)
  have hG'_fin : Finite V(G') := S_comp.finite_V.subset hG'_le.vertexSet_mono
  have hX_Nbar : X ⊆ N.Ω.bar := hX.1
  have hX_bar : X ⊆ S_comp.Ω.bar := hcomp.2.1 ▸ hX_Nbar
  have hX_G' : X ⊆ V(G') := fun x hx =>
    ⟨S_comp.bar_subset (hX_bar hx), fun ⟨_, hx_not_X⟩ => hx_not_X hx⟩
  have hYG'_G' : Y ∩ V(G') ⊆ V(G') := inter_subset_right
  rcases exists_fromToPaths_or_graphSeparation hX_G' hYG'_G' p with
    ⟨Q, hQ_disj, hQ_path⟩ | ⟨G₁, G₂, hsep, _, hX_G₁, hY_G₂, hZ_lt⟩
  · left
    refine ⟨Q, fun i => ?_, hQ_disj⟩
    obtain ⟨x, y, hQi_ends⟩ := hQ_path i
    have hxX : x ∈ X := hQi_ends.left_mem_X
    have hyY : y ∈ Y := hQi_ends.right_mem_Y.1
    obtain ⟨hQi_p, hQi_X, hQi_Y⟩ := hQi_ends
    refine ⟨x, hxX, y, hyY, ⟨hQi_p.mono hG'_le, ?_, ?_⟩⟩
    · ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hzQ, hz_bar⟩ => ?_, fun hzx =>
        hzx ▸ ⟨hQi_p.left_mem, hX_bar hxX⟩⟩
      have hz_X : z ∈ X := by
        by_contra hz_not_X
        exact (hQi_p.le.vertexSet_mono hzQ).2 ⟨hz_bar, hz_not_X⟩
      have : z ∈ V(Q i) ∩ X := ⟨hzQ, hz_X⟩
      rwa [hQi_X, mem_singleton_iff] at this
    · ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hzQ, hzY⟩ => ?_, fun hzy =>
        hzy ▸ ⟨hQi_p.right_mem, hyY⟩⟩
      have : z ∈ V(Q i) ∩ (Y ∩ V(G')) := ⟨hzQ, hzY, hQi_p.le.vertexSet_mono hzQ⟩
      rwa [hQi_Y, mem_singleton_iff] at this
  · right
    let Z := V(G₁) ∩ V(G₂)
    have hZ_sub_G' : Z ⊆ V(G') := inter_subset_left.trans hsep.1.vertexSet_mono
    have hZ_sub : Z ⊆ V(S_comp.G) := hZ_sub_G'.trans hG'_le.vertexSet_mono
    have hZ_fin : Z.Finite := S_comp.finite_V.subset hZ_sub
    let W := Z \ S_comp.Ω.bar
    refine ⟨W, sdiff_subset.trans hZ_sub,
      lt_of_le_of_lt (ncard_le_ncard sdiff_subset hZ_fin) hZ_lt,
      disjoint_sdiff_left, fun R hR => ?_⟩
    by_contra hRW_empty
    rw [not_nonempty_iff_eq_empty] at hRW_empty
    -- Step 1: Pick a linked path P₁ in N.G avoiding Z.
    obtain ⟨_, P_link, hPlink_ends, hPlink_disj⟩ := hX
    have hZ_lt_r : Z.ncard < X.ncard := lt_of_lt_of_le hZ_lt hpX
    obtain ⟨i₀, hPi₀_disj⟩ :=
      exists_disjoint_of_pairwise_disjoint_of_ncard_lt hPlink_disj hZ_fin hZ_lt_r
    obtain ⟨x₁, hx₁X, y₁, hy₁₀, hP₁_ends⟩ := hPlink_ends i₀
    let P₁ := P_link i₀
    -- Step 2: Pick a circuit C j₀ of the nest meeting Z in at most 1 vertex.
    have hp_le_2s : p ≤ 2 * s := by dsimp [s]; omega
    have hZ_lt_2s : Z.ncard < 2 * s := lt_of_lt_of_le hZ_lt hp_le_2s
    obtain ⟨j₀, hj₀⟩ :=
      exists_ncard_inter_le_one_of_pairwise_disjoint hC_disj hZ_fin hZ_lt_2s
    let j₀' : Fin (s + 1) := ⟨j₀.1, by omega⟩
    -- Step 3: P₁ meets C j₀ at some u₁.
    obtain ⟨hP₁_N, W_P₁, _, hVP₁, _⟩ := hP₁_ends.1
    obtain ⟨WN_P₁, hs_P₁, _⟩ := exists_walk_up_of_le hP₁_N W_P₁
    obtain ⟨u₁, hu₁_supp, hu₁_C⟩ :=
      exists_mem_support_circuit_of_isNest hC' j₀' WN_P₁ (hX_Nbar hx₁X) hy₁₀
    have hu₁_P₁ : u₁ ∈ V(P₁) := by rw [hVP₁, ← hs_P₁]; exact hu₁_supp
    have hu₁_not_Z : u₁ ∉ Z := disjoint_left.mp hPi₀_disj hu₁_P₁
    -- Step 4: R meets C j₀ at some v, and the subpath P₂ of R from v to y_R avoids Ω.bar and Z.
    have hRC_ne := nonempty_inter_circuit_of_isFromToPath_comp hcomp hY hC' j₀' hR
    obtain ⟨v, hvR, hvC⟩ := hRC_ne
    obtain ⟨x₀, y₀, hR_ends⟩ := hR
    have hx₀_bar : x₀ ∈ S_comp.Ω.bar := hR_ends.left_mem_X
    have hy₀Y : y₀ ∈ Y := hR_ends.right_mem_Y
    obtain ⟨hR_path, hR_bar, _⟩ := hR_ends
    obtain ⟨R₁, R₂, hR₁_le, hR₂_le, hR₁_path, hR₂_path, _, hVR₁₂_inter, _⟩ :=
      hR_path.exists_split_at hvR
    have hv_ne_x₀ : v ≠ x₀ := by
      rintro rfl
      exact disjoint_left.mp (hC_disj_bar j₀) hvC hx₀_bar
    have hR₂_disj_bar : Disjoint V(R₂) S_comp.Ω.bar := by
      rw [disjoint_left]
      intro z hzR₂ hz_bar
      have hz_x₀ : z = x₀ := by
        have : z ∈ V(R) ∩ S_comp.Ω.bar := ⟨hR₂_le.vertexSet_mono hzR₂, hz_bar⟩
        rwa [hR_bar, mem_singleton_iff] at this
      subst hz_x₀
      have : z ∈ V(R₁) ∩ V(R₂) := ⟨hR₁_path.left_mem, hzR₂⟩
      rw [hVR₁₂_inter, mem_singleton_iff] at this
      exact hv_ne_x₀ this.symm
    have hR₂_disj_Z : Disjoint V(R₂) Z := by
      rw [disjoint_left]
      intro z hzR₂ hzZ
      have hzW : z ∈ W := ⟨hzZ, disjoint_left.mp hR₂_disj_bar hzR₂⟩
      have : z ∈ V(R) ∩ W := ⟨hR₂_le.vertexSet_mono hzR₂, hzW⟩
      rw [hRW_empty] at this
      exact this
    have hv_not_Z : v ∉ Z := disjoint_left.mp hR₂_disj_Z hR₂_path.left_mem
    -- Step 5: C j₀ contains a path Q_C from u₁ to v avoiding Z.
    obtain ⟨Q_C, hQC_le, hQC_path, hQC_disj_Z⟩ :=
      exists_path_in_circuit_avoiding_of_ncard_le_one (hC'.1 j₀') hj₀ hu₁_C hvC hu₁_not_Z hv_not_Z
    -- Step 6: P₁, Q_C, and R₂ all lie in G', giving a walk in G' from x₁ ∈ X to y₀ ∈ Y ∩ V(G')
    -- that avoids Z = V(G₁) ∩ V(G₂), contradicting that (G₁, G₂) separates X from Y ∩ V(G').
    have hP₁_G' : P₁ ≤ G' := by
      refine le_deleteVertices (hP₁_N.trans hcomp.1.1.2.1) ?_
      rw [disjoint_left]
      intro z hzP₁ ⟨hz_bar, hz_not_X⟩
      have : z ∈ V(P₁) ∩ N.Ω.bar := ⟨hzP₁, hcomp.2.1 ▸ hz_bar⟩
      rw [hP₁_ends.2.1, mem_singleton_iff] at this
      exact hz_not_X (this ▸ hx₁X)
    have hQC_G' : Q_C ≤ G' := by
      refine le_deleteVertices (hQC_le.trans ((hC'.1 j₀').1.trans hcomp.1.1.2.1)) ?_
      exact disjoint_of_subset hQC_le.vertexSet_mono sdiff_subset (hC_disj_bar j₀)
    have hR₂_G' : R₂ ≤ G' :=
      le_deleteVertices (hR₂_le.trans hR_path.1)
        (disjoint_of_subset_right sdiff_subset hR₂_disj_bar)
    obtain ⟨P₁_a, _, hP₁a_le, _, hP₁a_path, _, _, _, _⟩ := hP₁_ends.1.exists_split_at hu₁_P₁
    obtain ⟨_, W_1, _, hV1, _⟩ := hP₁a_path
    obtain ⟨W_1G', hs1, _⟩ := exists_walk_up_of_le (hP₁a_le.trans hP₁_G') W_1
    obtain ⟨_, W_C, _, hVC, _⟩ := hQC_path
    obtain ⟨W_CG', hsC, _⟩ := exists_walk_up_of_le hQC_G' W_C
    have hy₀_R₂ : y₀ ∈ V(R₂) := hR₂_path.right_mem
    obtain ⟨_, W_2, _, hV2, _⟩ := hR₂_path
    obtain ⟨W_2G', hs2, _⟩ := exists_walk_up_of_le hR₂_G' W_2
    let W_total : GraphWalk G' x₁ y₀ := (W_1G'.append W_CG').append W_2G'
    have hx₁_G₁ : x₁ ∈ V(G₁) := hX_G₁ hx₁X
    have hy₀_G₂ : y₀ ∈ V(G₂) := hY_G₂ ⟨hy₀Y, hR₂_G'.vertexSet_mono hy₀_R₂⟩
    obtain ⟨z, hz_supp, hz_Z⟩ := exists_mem_inter_of_graphWalk hsep W_total hx₁_G₁ hy₀_G₂
    rw [GraphWalk.mem_support_append, GraphWalk.mem_support_append] at hz_supp
    rcases hz_supp with (hz1 | hzC) | hz2
    · rw [hs1] at hz1
      have hz_P₁ : z ∈ V(P₁) := hP₁a_le.vertexSet_mono (by rw [hV1]; exact hz1)
      exact disjoint_left.mp hPi₀_disj hz_P₁ hz_Z
    · rw [hsC] at hzC
      have hz_QC : z ∈ V(Q_C) := by rw [hVC]; exact hzC
      exact disjoint_left.mp hQC_disj_Z hz_QC hz_Z
    · rw [hs2] at hz2
      have hz_R₂ : z ∈ V(R₂) := by rw [hV2]; exact hz2
      exact disjoint_left.mp hR₂_disj_Z hz_R₂ hz_Z

end GraphMinor.GM09
