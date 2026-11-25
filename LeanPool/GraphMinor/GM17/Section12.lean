/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section11
import LeanPool.GraphMinor.GM17.PasteCuff
import LeanPool.GraphMinor.GM17.ArcDisc
import LeanPool.GraphMinor.GM17.MarkCross
import LeanPool.GraphMinor.GM17.ReplaceDisc
import LeanPool.GraphMinor.GM17.RegionDisc
import LeanPool.GraphMinor.GM17.RegionBoundary
import LeanPool.GraphMinor.GM17.CutArcPaint
import LeanPool.GraphMinor.GM17.PushNode
import LeanPool.GraphMinor.GM17.IndentMain
import LeanPool.GraphMinor.GM17.CliqueDisc

import LeanPool.GraphMinor.GM17.Section5Proved

import LeanPool.GraphMinor.GM17.Section6Proved

import LeanPool.GraphMinor.GM17.Section8Proved

import LeanPool.GraphMinor.GM17.Section9bProved

/-!
# Graph Minors XVII, Section 12: Filling Out a Portrayal of the 1-Skeleton

This file formalizes Section 12 (pages 196–201) of Robertson and Seymour, *Graph Minors. XVII.
Taming a Vortex*, J. Combin. Theory Ser. B 77 (1999), 162–210:

- **(12.1)** (`theorem_12_1`, page 197)
- **(12.2)** (`theorem_12_2`, page 198)
- **(12.3)** (`theorem_12_3`, page 199)
- **(12.4)** (`theorem_12_4`, page 200)
- **(12.5)** (`theorem_12_5`, page 200)
- **(12.6)** (`theorem_12_6`, page 200)
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.GM19
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Cliques on a Cuff: (12.1) (Pages 196–197) -/

theorem cuffs_eq_of_nonempty_inter {S : Type} [TopologicalSpace S] {Θ₁ Θ₂ : Set S}
    (hΘ₁ : Θ₁ ∈ cuffs S) (hΘ₂ : Θ₂ ∈ cuffs S) (hne : (Θ₁ ∩ Θ₂).Nonempty) :
    Θ₁ = Θ₂ := by
  rcases hΘ₁ with ⟨x₁, _, rfl⟩
  rcases hΘ₂ with ⟨x₂, _, rfl⟩
  rcases hne with ⟨x, hx₁, hx₂⟩
  have h1 := connectedComponentIn_eq hx₁
  have h2 := connectedComponentIn_eq hx₂
  exact h1.trans h2.symm

theorem Painting.exists_cuff_of_border_cell {S : Type} [TopologicalSpace S] (Γ : Painting S)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    ∃ Θ ∈ cuffs S, (c ∩ Θ).Nonempty ∧ tilde c ⊆ Γ.N ∩ Θ := by
  rcases hbd with ⟨x, hxc, hxbd⟩
  refine ⟨connectedComponentIn (bd S) x, ⟨x, hxbd, rfl⟩,
    ⟨x, hxc, mem_connectedComponentIn hxbd⟩, ?_⟩
  exact (Γ.border_cell_subset_cuff hc ⟨x, hxbd, rfl⟩ ⟨x, hxc, mem_connectedComponentIn
    hxbd⟩).2.2.2.1

/-- Under the standing hypotheses of Section 8 (`(2p + 3)`-redundancy and `4p + 5 < θ`), for every
cell $c \in C(\Gamma)$ and node $n \in N(\Gamma)$, $\gamma(n) \in V(\alpha(c))$ if and only if
$n \in \tilde{c}$. -/
theorem nodeVertex_mem_cellGraph_iff
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {c : Set π.S} (hc : c ∈ π.Γ.C) {n : π.S} (hn : n ∈ π.Γ.N) :
    π.nodeVertex n ∈ (π.cellGraph c).vertexSet ↔ n ∈ tilde c := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof h𝒯 π htrue hred hwarp hθ
  have hn_dom : n ∈ π.domγ := hdom.symm ▸ hn
  refine ⟨fun hvc => ?_, fun hnt => π.p2 c hc n ⟨hnt, hn_dom⟩⟩
  have h87 := (theorem_8_7_proof h𝒯 π htrue hred hwarp hθ hn).1
  have hex_other : ∃ d ∈ π.Γ.C, d ≠ c ∧ n ∈ tilde d := by
    by_contra! hall
    have hsub : {d ∈ π.Γ.CStar | n ∈ tilde d} ⊆ {c} :=
      fun d hd => mem_singleton_iff.mpr (by by_contra hne; exact hall d hd.1.1 hne hd.2)
    have hle : {d ∈ π.Γ.CStar | n ∈ tilde d}.ncard ≤ ({c} : Set (Set π.S)).ncard :=
      ncard_le_ncard hsub (finite_singleton c)
    rw [ncard_singleton] at hle
    omega
  obtain ⟨d, hd, hdc, hnd⟩ := hex_other
  have hvd : π.nodeVertex n ∈ (π.cellGraph d).vertexSet := π.p2 d hd n ⟨hnd, hn_dom⟩
  by_cases hbd : (c ∩ bd π.S).Nonempty
  · obtain ⟨n₁, n₂, hne12, htilde, _, _, _, _⟩ := π.Γ.border_cell_exists_ends hc hbd
    obtain ⟨Θ, hΘ, hcΘ, _⟩ := π.Γ.exists_cuff_of_border_cell hc hbd
    have hn₁_t : n₁ ∈ tilde c := htilde ▸ mem_insert _ _
    have hn₂_t : n₂ ∈ tilde c := htilde ▸ mem_insert_of_mem _ (mem_singleton _)
    obtain ⟨-, -, hdisj₁, hdisj₂, -⟩ :=
      theorem_9_8_proof h𝒯 π htrue hred hwarp hθ hΘ hc hcΘ hn₁_t hn₂_t hne12
    obtain ⟨m, hmt, hmem | ⟨hm_dom, hEq⟩⟩ := π.p6 c hc hbd (π.nodeVertex n) hvc ⟨d, hd, hdc, hvd⟩
    · exfalso
      rcases (htilde ▸ hmt : m ∈ ({n₁, n₂} : Set π.S)) with rfl | rfl
      · exact Set.disjoint_left.mp hdisj₁ hmem ⟨n, hn, rfl⟩
      · exact Set.disjoint_left.mp hdisj₂ hmem ⟨n, hn, rfl⟩
    · have hmn : m = n := π.nodeVertex_injOn hm_dom hn_dom hEq.symm
      exact hmn ▸ hmt
  · obtain ⟨m, ⟨hmt, hm_dom⟩, hEq⟩ := π.p5 c hc hbd (π.nodeVertex n) hvc ⟨d, hd, hdc, hvd⟩
    have hmn : m = n := π.nodeVertex_injOn hm_dom hn_dom hEq
    exact hmn ▸ hmt

/-- Arithmetic helper on `cyclicDist` for a cuff enumeration `E`: if `m ∈ {j, cyclicSucc hk0 j}`,
then `cyclicDist i m ≤ cyclicDist i b` whenever `cyclicDist i j < cyclicDist i b`. -/
private theorem cyclicDist_end_le_of_lt {k : ℕ} (hk2 : 2 ≤ k) {i j b : Fin k}
    (hlt : cyclicDist i j < cyclicDist i b) {m : Fin k}
    (hm : m = j ∨ m = cyclicSucc (by omega : 0 < k) j) :
    cyclicDist i m ≤ cyclicDist i b := by
  have hk0 : 0 < k := by omega
  rcases hm with rfl | rfl
  · exact hlt.le
  · have hi := i.2; have hj := j.2; have hb := b.2
    rw [cyclicDist_eq_ite i j, cyclicDist_eq_ite i b] at hlt
    rw [cyclicDist_eq_ite i (cyclicSucc hk0 j), cyclicDist_eq_ite i b]
    dsimp [cyclicSucc]
    by_cases hj1 : j.1 + 1 < k
    · have hmod : (j.1 + 1) % k = j.1 + 1 := Nat.mod_eq_of_lt hj1
      simp only [hmod]
      split_ifs at hlt ⊢ <;> omega
    · have hmod : (j.1 + 1) % k = 0 := by
        have : j.1 + 1 = k := by omega
        rw [this, Nat.mod_self]
      simp only [hmod]
      split_ifs at hlt ⊢ <;> omega

private theorem cyclicDist_three_sum_le {k : ℕ} (hk : 0 < k) {i x b y : Fin k}
    (hxb : cyclicDist i x ≤ cyclicDist i b) (hby : cyclicDist i b ≤ cyclicDist i y)
    (hx_pos : 0 < cyclicDist i x) :
    cyclicDist x b + cyclicDist b y + cyclicDist y i ≤ k := by
  have hi := i.2; have hx := x.2; have hb := b.2; have hy := y.2
  rw [cyclicDist_eq_ite i x, cyclicDist_eq_ite i b] at hxb
  rw [cyclicDist_eq_ite i b, cyclicDist_eq_ite i y] at hby
  rw [cyclicDist_eq_ite i x] at hx_pos
  rw [cyclicDist_eq_ite x b, cyclicDist_eq_ite b y, cyclicDist_eq_ite y i]
  split_ifs at hxb hby hx_pos ⊢ <;> omega

/-- If $j_a, j_b, j_c$ are cell indices around $\Theta$ with
$\operatorname{cyclicDist} i\, j_a < \operatorname{cyclicDist} i\, j_b < \operatorname{cyclicDist}
i\, j_c$,
and $v \in V(\alpha(c_a)) \cap V(\alpha(c_c)) \setminus V(\alpha(c_b))$, then
$v \in \beta(n_i+)$. -/
private theorem mem_borderPlus_of_cyclicDist_lt {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    (i ja jb jc : Fin k)
    (hab : cyclicDist i ja < cyclicDist i jb)
    (hbc : cyclicDist i jb < cyclicDist i jc)
    {v : α}
    (hva : v ∈ (π.cellGraph (E.cell ja)).vertexSet)
    (hvb : v ∉ (π.cellGraph (E.cell jb)).vertexSet)
    (hvc : v ∈ (π.cellGraph (E.cell jc)).vertexSet) :
    v ∈ π.borderPlus (E.node i) := by
  have hk2 : 2 ≤ k := E.two_le
  have hk0 : 0 < k := by omega
  have hcell_mem : ∀ j : Fin k, E.cell j ∈ π.Γ.C ∧ (E.cell j ∩ bd π.S).Nonempty := by
    intro j
    have hrange : E.cell j ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self j
    have hΘ_bd : Θ ⊆ bd π.S := by
      rcases E.cuff_mem with ⟨x₀, _, rfl⟩
      exact connectedComponentIn_subset (bd π.S) x₀
    exact ⟨hrange.1, hrange.2.mono (inter_subset_inter_right _ hΘ_bd)⟩
  have hne_ac : E.cell ja ≠ E.cell jc := by
    intro hEq
    have hja_jc : ja = jc := E.injective_cell hEq
    subst hja_jc
    omega
  obtain ⟨na, hna_t, hv_na⟩ := π.p6 (E.cell ja) (hcell_mem ja).1 (hcell_mem ja).2 v hva
    ⟨E.cell jc, (hcell_mem jc).1, hne_ac.symm, hvc⟩
  obtain ⟨nc, hnc_t, hv_nc⟩ := π.p6 (E.cell jc) (hcell_mem jc).1 (hcell_mem jc).2 v hvc
    ⟨E.cell ja, (hcell_mem ja).1, hne_ac, hva⟩
  rw [E.cell_tilde ja] at hna_t
  rw [E.cell_tilde jc] at hnc_t
  have hma_ex : ∃ ma : Fin k, (ma = ja ∨ ma = cyclicSucc hk0 ja) ∧ na = E.node ma := by
    rcases hna_t with rfl | hna_t
    · exact ⟨ja, Or.inl rfl, rfl⟩
    · exact ⟨cyclicSucc hk0 ja, Or.inr rfl, mem_singleton_iff.mp hna_t⟩
  have hmc_ex : ∃ mc : Fin k, (mc = jc ∨ mc = cyclicSucc hk0 jc) ∧ nc = E.node mc := by
    rcases hnc_t with rfl | hnc_t
    · exact ⟨jc, Or.inl rfl, rfl⟩
    · exact ⟨cyclicSucc hk0 jc, Or.inr rfl, mem_singleton_iff.mp hnc_t⟩
  obtain ⟨ma, hma_cases, rfl⟩ := hma_ex
  obtain ⟨mc, hmc_cases, rfl⟩ := hmc_ex
  change v ∈ π.borderPlus (E.node ma) at hv_na
  change v ∈ π.borderPlus (E.node mc) at hv_nc
  by_cases hma_i : ma = i
  · exact hma_i ▸ hv_na
  by_cases hmc_i : mc = i
  · exact hmc_i ▸ hv_nc
  have hd_ma_pos : 0 < cyclicDist i ma := cyclicDist_pos_of_ne (Ne.symm hma_i)
  have hd_mc_pos : 0 < cyclicDist i mc := cyclicDist_pos_of_ne (Ne.symm hmc_i)
  have hd_ma_le : cyclicDist i ma ≤ cyclicDist i jb :=
    cyclicDist_end_le_of_lt hk2 hab hma_cases
  have hd_jb_le : cyclicDist i jb ≤ cyclicDist i mc := by
    rcases hmc_cases with rfl | rfl
    · exact hbc.le
    · have hi := i.2; have hjc := jc.2; have hjb := jb.2
      rw [cyclicDist_eq_ite i jb, cyclicDist_eq_ite i jc] at hbc
      rw [cyclicDist_eq_ite i (cyclicSucc hk0 jc)] at hd_mc_pos
      rw [cyclicDist_eq_ite i jb, cyclicDist_eq_ite i (cyclicSucc hk0 jc)]
      dsimp [cyclicSucc] at hd_mc_pos ⊢
      by_cases hj1 : jc.1 + 1 < k
      · have hmod : (jc.1 + 1) % k = jc.1 + 1 := Nat.mod_eq_of_lt hj1
        simp only [hmod] at hd_mc_pos ⊢
        split_ifs at hbc hd_mc_pos ⊢ <;> omega
      · have hmod : (jc.1 + 1) % k = 0 := by
          have : jc.1 + 1 = k := by omega
          rw [this, Nat.mod_self]
        simp only [hmod] at hd_mc_pos ⊢
        split_ifs at hbc hd_mc_pos ⊢ <;> omega
  have hsum : cyclicDist ma jb + cyclicDist jb mc + cyclicDist mc i ≤ k :=
    cyclicDist_three_sum_le hk0 hd_ma_le hd_jb_le hd_ma_pos
  have hv_not_jb : v ∉ π.borderPlus (E.node jb) := by
    intro hv_jb
    have hjb_t : E.node jb ∈ tilde (E.cell jb) := by
      rw [E.cell_tilde jb]; exact mem_insert _ _
    exact hvb (π.borderPlus_subset_cellGraph (hcell_mem jb).1 (hcell_mem jb).2 hjb_t hv_jb)
  exact (π.p7_of_cyclicDist E hsum hv_na hv_nc).resolve_left hv_not_jb

private theorem cover_two_border_vertices
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ : ℕ}
    {p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hwarp : π.warp ≤ p)
    {Θ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hred3 : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hθ5 : 4 * p + 5 < θ)
    (hΘ_bd : Θ ⊆ bd π.S)
    (n : ℕ)
    (K : Set α)
    (hcard : K.ncard = n)
    (hK : IsClique G K)
    (hK_sub : K ⊆ ⋃ c ∈ {c | c ∈ π.Γ.C ∧ (c ∩ Θ).Nonempty}, (π.cellGraph c).vertexSet)
    (hn2 : n = 2) :
    ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ K ⊆ (π.cellGraph c).vertexSet := by
  obtain ⟨x₁, x₂, hne12, hK_eq⟩ := ncard_eq_two.mp (hcard.trans hn2)
  have hx₁K : x₁ ∈ K := hK_eq ▸ mem_insert _ _
  have hx₂K : x₂ ∈ K := hK_eq ▸ mem_insert_of_mem _ (mem_singleton _)
  obtain ⟨_, e, he₁, he₂⟩ := hK.2 x₁ hx₁K x₂ hx₂K hne12
  have heG : e ∈ G.edgeSet := G.edge_mem_of_inc he₁
  obtain ⟨c, hc, hec⟩ := π.p1_edge e heG
  have hx₁c : x₁ ∈ (π.cellGraph c).vertexSet :=
    (π.cellGraph c).vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le c hc) hec).mpr he₁)
  have hx₂c : x₂ ∈ (π.cellGraph c).vertexSet :=
    (π.cellGraph c).vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le c hc) hec).mpr he₂)
  by_cases hcΘ : (c ∩ Θ).Nonempty
  · refine ⟨c, hc, hcΘ, ?_⟩
    rw [hK_eq]
    rintro x (rfl | rfl) <;> assumption
  · obtain ⟨c₁, ⟨hc₁, hc₁Θ⟩, hx₁c₁⟩ := mem_iUnion₂.mp (hK_sub hx₁K)
    obtain ⟨c₂, ⟨hc₂, hc₂Θ⟩, hx₂c₂⟩ := mem_iUnion₂.mp (hK_sub hx₂K)
    have hne_c₁ : c ≠ c₁ := fun h => hcΘ (h ▸ hc₁Θ)
    have hne_c₂ : c ≠ c₂ := fun h => hcΘ (h ▸ hc₂Θ)
    have hbd₁ : (c₁ ∩ bd π.S).Nonempty := hc₁Θ.mono (inter_subset_inter_right _ hΘ_bd)
    have hbd₂ : (c₂ ∩ bd π.S).Nonempty := hc₂Θ.mono (inter_subset_inter_right _ hΘ_bd)
    obtain ⟨n₁, hn₁_t, hx₁_bp⟩ := π.p6 c₁ hc₁ hbd₁ x₁ hx₁c₁ ⟨c, hc, hne_c₁, hx₁c⟩
    obtain ⟨n₂, hn₂_t, hx₂_bp⟩ := π.p6 c₂ hc₂ hbd₂ x₂ hx₂c₂ ⟨c, hc, hne_c₂, hx₂c⟩
    have hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ := (π.Γ.border_cell_subset_cuff hc₁ hΘ hc₁Θ).2.2.2.1 hn₁_t
    have hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ := (π.Γ.border_cell_subset_cuff hc₂ hΘ hc₂Θ).2.2.2.1 hn₂_t
    have hint : ¬ (c ∩ bd π.S).Nonempty := by
      intro hbd_c
      obtain ⟨Θ', hΘ', hcΘ', htilde_c⟩ := π.Γ.exists_cuff_of_border_cell hc hbd_c
      obtain ⟨n', hn'_t, hx₁_bp'⟩ := π.p6 c hc hbd_c x₁ hx₁c ⟨c₁, hc₁, hne_c₁.symm, hx₁c₁⟩
      have hn'_Θ' : n' ∈ π.Γ.N ∩ Θ' := htilde_c hn'_t
      have hΘ'_bd : Θ' ⊆ bd π.S := by
        rcases hΘ' with ⟨y₀, _, rfl⟩
        exact connectedComponentIn_subset (bd π.S) y₀
      obtain ⟨Θ₀, hΘ₀, hn₁Θ₀, hn'Θ₀⟩ := π.cuff_eq_of_borderPlus_inter_nonempty
        ⟨hn₁_Θ.1, hΘ_bd hn₁_Θ.2⟩ ⟨hn'_Θ'.1, hΘ'_bd hn'_Θ'.2⟩ hx₁_bp hx₁_bp'
      have hΘ₀_eq_Θ : Θ₀ = Θ :=
        cuffs_eq_of_nonempty_inter hΘ₀ hΘ ⟨n₁, hn₁Θ₀, hn₁_Θ.2⟩
      have hΘ₀_eq_Θ' : Θ₀ = Θ' :=
        cuffs_eq_of_nonempty_inter hΘ₀ hΘ' ⟨n', hn'Θ₀, hn'_Θ'.2⟩
      exact hcΘ (hΘ₀_eq_Θ ▸ hΘ₀_eq_Θ' ▸ hcΘ')
    obtain ⟨m₁, ⟨hm₁_t, hm₁_dom⟩, hm₁_eq⟩ :=
      π.p5 c hc hint x₁ hx₁c ⟨c₁, hc₁, hne_c₁.symm, hx₁c₁⟩
    obtain ⟨m₂, ⟨hm₂_t, hm₂_dom⟩, hm₂_eq⟩ :=
      π.p5 c hc hint x₂ hx₂c ⟨c₂, hc₂, hne_c₂.symm, hx₂c₂⟩
    have hdisj_n₁ : Disjoint (π.borderSet n₁) (π.nodeVertex '' π.Γ.N) :=
      theorem_9_7_proof h𝒯 π htrue hred3 hwarp hθ5 ⟨hn₁_Θ.1, hΘ_bd hn₁_Θ.2⟩
    have hdisj_n₂ : Disjoint (π.borderSet n₂) (π.nodeVertex '' π.Γ.N) :=
      theorem_9_7_proof h𝒯 π htrue hred3 hwarp hθ5 ⟨hn₂_Θ.1, hΘ_bd hn₂_Θ.2⟩
    have hx₁_eq : x₁ = π.nodeVertex n₁ := by
      rcases hx₁_bp with hx₁_bs | ⟨_, hEq⟩
      · exfalso
        exact Set.disjoint_left.mp hdisj_n₁ hx₁_bs
          ⟨m₁, π.domγ_subset hm₁_dom, hm₁_eq⟩
      · exact hEq
    have hx₂_eq : x₂ = π.nodeVertex n₂ := by
      rcases hx₂_bp with hx₂_bs | ⟨_, hEq⟩
      · exfalso
        exact Set.disjoint_left.mp hdisj_n₂ hx₂_bs
          ⟨m₂, π.domγ_subset hm₂_dom, hm₂_eq⟩
      · exact hEq
    have hn₁_tc : n₁ ∈ tilde c :=
      (nodeVertex_mem_cellGraph_iff h𝒯 π htrue hred3 hwarp hθ5 hc hn₁_Θ.1).mp
        (hx₁_eq ▸ hx₁c)
    have hn₂_tc : n₂ ∈ tilde c :=
      (nodeVertex_mem_cellGraph_iff h𝒯 π htrue hred3 hwarp hθ5 hc hn₂_Θ.1).mp
        (hx₂_eq ▸ hx₂c)
    have hne_n : n₁ ≠ n₂ := fun h => hne12 (hx₁_eq.trans (h ▸ hx₂_eq.symm))
    have hcl_eq : closure c ∩ bd π.S = tilde c ∩ bd π.S :=
      Painting.closure_cell_inter_bd_eq_tilde_inter_bd hint
    have hn₁_cl : n₁ ∈ closure c ∩ bd π.S := hcl_eq.symm ▸ ⟨hn₁_tc, hΘ_bd hn₁_Θ.2⟩
    have hn₂_cl : n₂ ∈ closure c ∩ bd π.S := hcl_eq.symm ▸ ⟨hn₂_tc, hΘ_bd hn₂_Θ.2⟩
    have h86 := theorem_8_6_proof h𝒯 π htrue hred3 hwarp hθ5 hc hint
    have hpair_sub : ({n₁, n₂} : Set π.S) ⊆ closure c ∩ bd π.S := by
      rintro x (rfl | rfl) <;> assumption
    have hfin_cl : (closure c ∩ bd π.S).Finite := by
      rw [hcl_eq]
      exact (π.Γ.finite_tilde_cell hc).inter_of_left _
    have hge2 : 2 ≤ (closure c ∩ bd π.S).ncard := by
      have := ncard_le_ncard hpair_sub hfin_cl
      rw [ncard_pair hne_n] at this
      exact this
    have heq2 : (closure c ∩ bd π.S).ncard = 2 := le_antisymm h86.1 hge2
    obtain ⟨c₀, hc₀, hbd₀, htilde₀⟩ := (h86.2 heq2).2 n₁ hn₁_cl n₂ hn₂_cl hne_n
    obtain ⟨Θ₀, hΘ₀, hc₀Θ₀, htilde₀_sub⟩ := π.Γ.exists_cuff_of_border_cell hc₀ hbd₀
    have hn₁_t₀ : n₁ ∈ tilde c₀ := htilde₀ ▸ mem_insert _ _
    have hn₂_t₀ : n₂ ∈ tilde c₀ := htilde₀ ▸ mem_insert_of_mem _ (mem_singleton _)
    have hΘ₀_eq : Θ₀ = Θ :=
      cuffs_eq_of_nonempty_inter hΘ₀ hΘ ⟨n₁, (htilde₀_sub hn₁_t₀).2, hn₁_Θ.2⟩
    have hc₀Θ : (c₀ ∩ Θ).Nonempty := hΘ₀_eq ▸ hc₀Θ₀
    have hdom : π.domγ = π.Γ.N :=
      theorem_8_4_proof h𝒯 π htrue hred3 hwarp hθ5
    have hx₁_c₀ : x₁ ∈ (π.cellGraph c₀).vertexSet :=
      hx₁_eq ▸ π.p2 c₀ hc₀ n₁ ⟨hn₁_t₀, hdom.symm ▸ hn₁_Θ.1⟩
    have hx₂_c₀ : x₂ ∈ (π.cellGraph c₀).vertexSet :=
      hx₂_eq ▸ π.p2 c₀ hc₀ n₂ ⟨hn₂_t₀, hdom.symm ▸ hn₂_Θ.1⟩
    refine ⟨c₀, hc₀, hc₀Θ, ?_⟩
    rw [hK_eq]
    rintro x (rfl | rfl) <;> assumption

/-- **Graph Minors XVII, (12.1)** (page 197):
"Let $\mathscr{T}$ be a tangle of order $> 4p+9$ in a hypergraph $G$, let
$\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a true, $(2p+7)$-redundant,
$\mathscr{T}$-central portrayal of $G$ with warp $\le p$, and let $\Theta$ be a cuff of $\Sigma$.
For every clique $K$ of $G$ with
$$K \subseteq \bigcup (V(\alpha(c)) \colon c \in C(\Gamma) \text{ bordering } \Theta)$$
there is a cell $c$ bordering $\Theta$ with $K \subseteq V(\alpha(c))$." -/
theorem theorem_12_1_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 7))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 9 < θ)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S)
    {K : Set α} (hK : IsClique G K)
    (hK_sub : K ⊆ ⋃ c ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty}, (π.cellGraph c).vertexSet) :
    ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ K ⊆ (π.cellGraph c).vertexSet := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hp1 : 1 ≤ p := π.one_le_warp.trans hwarp
  have hred3 : π.IsRedundant 𝒯 θ (2 * p + 3) := hred.mono (by omega)
  have hθ5 : 4 * p + 5 < θ := by omega
  have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  set k := (π.Γ.N ∩ Θ).ncard
  have hk2 : 2 ≤ k := E.two_le
  -- Strong induction on `K.ncard`
  suffices hind : ∀ n : ℕ, ∀ K : Set α, K.ncard = n → IsClique G K →
      K ⊆ ⋃ c ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty}, (π.cellGraph c).vertexSet →
      ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ K ⊆ (π.cellGraph c).vertexSet from
    hind K.ncard K rfl hK hK_sub
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro K hcard hK hK_sub
    have hK_fin : K.Finite := G.vertexSet_finite.subset hK.1
    by_cases hn1 : n ≤ 1
    · by_cases hKne : K.Nonempty
      · obtain ⟨x, hx⟩ := hKne
        have hK_eq : K = {x} :=
          ( eq_of_subset_of_ncard_le (singleton_subset_iff.mpr hx)
              (by rw [ncard_singleton]; omega) hK_fin ).symm
        obtain ⟨c, ⟨hc, hcΘ⟩, hxc⟩ := mem_iUnion₂.mp (hK_sub hx)
        exact ⟨c, hc, hcΘ, hK_eq.symm ▸ singleton_subset_iff.mpr hxc⟩
      · rw [not_nonempty_iff_eq_empty] at hKne
        have hc0 : E.cell ⟨0, by omega⟩ ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
          rw [← E.range_cell]; exact mem_range_self _
        exact ⟨E.cell ⟨0, by omega⟩, hc0.1, hc0.2, hKne.symm ▸ empty_subset _⟩
    by_cases hn2 : n = 2
    · exact cover_two_border_vertices (α := α) (β := β) (G := G) (𝒯 := 𝒯) (θ := θ) (p := p) h𝒯 π
        htrue hwarp (Θ := Θ) hΘ hred3 hθ5 hΘ_bd n K hcard hK hK_sub hn2
    · -- Now `3 ≤ n`
      have hn3 : 3 ≤ n := by omega
      obtain ⟨x₁, hx₁K⟩ : K.Nonempty := (ncard_pos hK_fin).mp (by omega)
      have hK1_card : (K \ {x₁}).ncard = n - 1 := by
        rw [ncard_sdiff_singleton_of_mem hx₁K, hcard]
      obtain ⟨x₂, hx₂_mem⟩ : (K \ {x₁}).Nonempty :=
        (ncard_pos hK_fin.sdiff).mp (by omega)
      have hx₂K : x₂ ∈ K := hx₂_mem.1
      have hne12 : x₁ ≠ x₂ := Ne.symm hx₂_mem.2
      have hK12_card : (K \ {x₁, x₂}).ncard = n - 2 := by
        have hsub12 : ({x₁, x₂} : Set α) ⊆ K := by
          rintro x (rfl | rfl) <;> assumption
        have heq := ncard_sdiff_add_ncard_of_subset hsub12 hK_fin
        rw [ncard_pair hne12, hcard] at heq
        omega
      obtain ⟨x₃, hx₃_mem⟩ : (K \ {x₁, x₂}).Nonempty :=
        (ncard_pos hK_fin.sdiff).mp (by omega)
      have hx₃K : x₃ ∈ K := hx₃_mem.1
      have hne13 : x₁ ≠ x₃ := fun h => hx₃_mem.2 (Or.inl h.symm)
      have hne23 : x₂ ≠ x₃ := fun h => hx₃_mem.2 (Or.inr h.symm)
      have hclique_diff : ∀ x ∈ K, IsClique G (K \ {x}) ∧ (K \ {x}).ncard = n - 1 := by
        intro x hx
        refine ⟨⟨sdiff_subset.trans hK.1, fun u hu v hv huv => hK.2 u hu.1 v hv.1 huv⟩, ?_⟩
        rw [ncard_sdiff_singleton_of_mem hx, hcard]
      obtain ⟨c₁, hc₁, hc₁Θ, hsub₁⟩ := ih (n - 1) (by omega) (K \ {x₁})
        (hclique_diff x₁ hx₁K).2 (hclique_diff x₁ hx₁K).1 (sdiff_subset.trans hK_sub)
      obtain ⟨c₂, hc₂, hc₂Θ, hsub₂⟩ := ih (n - 1) (by omega) (K \ {x₂})
        (hclique_diff x₂ hx₂K).2 (hclique_diff x₂ hx₂K).1 (sdiff_subset.trans hK_sub)
      obtain ⟨c₃, hc₃, hc₃Θ, hsub₃⟩ := ih (n - 1) (by omega) (K \ {x₃})
        (hclique_diff x₃ hx₃K).2 (hclique_diff x₃ hx₃K).1 (sdiff_subset.trans hK_sub)
      by_cases hx₁_in : x₁ ∈ (π.cellGraph c₁).vertexSet
      · refine ⟨c₁, hc₁, hc₁Θ, fun y hy => ?_⟩
        by_cases hyx : y = x₁
        · exact hyx ▸ hx₁_in
        · exact hsub₁ ⟨hy, hyx⟩
      by_cases hx₂_in : x₂ ∈ (π.cellGraph c₂).vertexSet
      · refine ⟨c₂, hc₂, hc₂Θ, fun y hy => ?_⟩
        by_cases hyx : y = x₂
        · exact hyx ▸ hx₂_in
        · exact hsub₂ ⟨hy, hyx⟩
      by_cases hx₃_in : x₃ ∈ (π.cellGraph c₃).vertexSet
      · refine ⟨c₃, hc₃, hc₃Θ, fun y hy => ?_⟩
        by_cases hyx : y = x₃
        · exact hyx ▸ hx₃_in
        · exact hsub₃ ⟨hy, hyx⟩
      exfalso
      have hc₁_range : c₁ ∈ Set.range E.cell := by rw [E.range_cell]; exact ⟨hc₁, hc₁Θ⟩
      have hc₂_range : c₂ ∈ Set.range E.cell := by rw [E.range_cell]; exact ⟨hc₂, hc₂Θ⟩
      have hc₃_range : c₃ ∈ Set.range E.cell := by rw [E.range_cell]; exact ⟨hc₃, hc₃Θ⟩
      obtain ⟨j₁, hj₁⟩ := hc₁_range
      obtain ⟨j₂, hj₂⟩ := hc₂_range
      obtain ⟨j₃, hj₃⟩ := hc₃_range
      subst hj₁ hj₂ hj₃
      have hx₁_2 : x₁ ∈ (π.cellGraph (E.cell j₂)).vertexSet := hsub₂ ⟨hx₁K, hne12⟩
      have hx₁_3 : x₁ ∈ (π.cellGraph (E.cell j₃)).vertexSet := hsub₃ ⟨hx₁K, hne13⟩
      have hx₂_1 : x₂ ∈ (π.cellGraph (E.cell j₁)).vertexSet := hsub₁ ⟨hx₂K, hne12.symm⟩
      have hx₂_3 : x₂ ∈ (π.cellGraph (E.cell j₃)).vertexSet := hsub₃ ⟨hx₂K, hne23⟩
      have hx₃_1 : x₃ ∈ (π.cellGraph (E.cell j₁)).vertexSet := hsub₁ ⟨hx₃K, hne13.symm⟩
      have hx₃_2 : x₃ ∈ (π.cellGraph (E.cell j₂)).vertexSet := hsub₂ ⟨hx₃K, hne23.symm⟩
      have hj12 : j₁ ≠ j₂ := fun h => hx₁_in (h ▸ hx₁_2)
      have hj13 : j₁ ≠ j₃ := fun h => hx₁_in (h ▸ hx₁_3)
      have hj23 : j₂ ≠ j₃ := fun h => hx₂_in (h ▸ hx₂_3)
      -- Claim (2): `{x₁, x₂, x₃} ∩ β(n+) ≠ ∅` for all `n ∈ N(Γ) ∩ Θ`.
      have hclaim2 : ∀ n ∈ π.Γ.N ∩ Θ, (({x₁, x₂, x₃} : Set α) ∩ π.borderPlus n).Nonempty := by
        intro n hn
        have hn_range : n ∈ Set.range E.node := by rw [E.range_node]; exact hn
        rcases hn_range with ⟨i, rfl⟩
        have hd12 : cyclicDist i j₁ ≠ cyclicDist i j₂ := by
          intro hEq
          have hi := i.2; have h1 := j₁.2; have h2 := j₂.2
          rw [cyclicDist_eq_ite i j₁, cyclicDist_eq_ite i j₂] at hEq
          apply hj12; ext; split_ifs at hEq <;> omega
        have hd13 : cyclicDist i j₁ ≠ cyclicDist i j₃ := by
          intro hEq
          have hi := i.2; have h1 := j₁.2; have h3 := j₃.2
          rw [cyclicDist_eq_ite i j₁, cyclicDist_eq_ite i j₃] at hEq
          apply hj13; ext; split_ifs at hEq <;> omega
        have hd23 : cyclicDist i j₂ ≠ cyclicDist i j₃ := by
          intro hEq
          have hi := i.2; have h2 := j₂.2; have h3 := j₃.2
          rw [cyclicDist_eq_ite i j₂, cyclicDist_eq_ite i j₃] at hEq
          apply hj23; ext; split_ifs at hEq <;> omega
        have hperm :
            (cyclicDist i j₁ < cyclicDist i j₂ ∧ cyclicDist i j₂ < cyclicDist i j₃) ∨
            (cyclicDist i j₃ < cyclicDist i j₂ ∧ cyclicDist i j₂ < cyclicDist i j₁) ∨
            (cyclicDist i j₂ < cyclicDist i j₁ ∧ cyclicDist i j₁ < cyclicDist i j₃) ∨
            (cyclicDist i j₃ < cyclicDist i j₁ ∧ cyclicDist i j₁ < cyclicDist i j₂) ∨
            (cyclicDist i j₁ < cyclicDist i j₃ ∧ cyclicDist i j₃ < cyclicDist i j₂) ∨
            (cyclicDist i j₂ < cyclicDist i j₃ ∧ cyclicDist i j₃ < cyclicDist i j₁) := by
          omega
        rcases hperm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨x₂, Or.inr (Or.inl rfl),
            mem_borderPlus_of_cyclicDist_lt π E i j₁ j₂ j₃ h1 h2 hx₂_1 hx₂_in hx₂_3⟩
        · exact ⟨x₂, Or.inr (Or.inl rfl),
            mem_borderPlus_of_cyclicDist_lt π E i j₃ j₂ j₁ h1 h2 hx₂_3 hx₂_in hx₂_1⟩
        · exact ⟨x₁, Or.inl rfl,
            mem_borderPlus_of_cyclicDist_lt π E i j₂ j₁ j₃ h1 h2 hx₁_2 hx₁_in hx₁_3⟩
        · exact ⟨x₁, Or.inl rfl,
            mem_borderPlus_of_cyclicDist_lt π E i j₃ j₁ j₂ h1 h2 hx₁_3 hx₁_in hx₁_2⟩
        · exact ⟨x₃, Or.inr (Or.inr rfl),
            mem_borderPlus_of_cyclicDist_lt π E i j₁ j₃ j₂ h1 h2 hx₃_1 hx₃_in hx₃_2⟩
        · exact ⟨x₃, Or.inr (Or.inr rfl),
            mem_borderPlus_of_cyclicDist_lt π E i j₂ j₃ j₁ h1 h2 hx₃_2 hx₃_in hx₃_1⟩
      have hX_sub : ({x₁, x₂, x₃} : Set α) ⊆ G.vertexSet := by
        rintro x (rfl | rfl | rfl)
        · exact hK.1 hx₁K
        · exact hK.1 hx₂K
        · exact hK.1 hx₃K
      have hX_card : 3 * ({x₁, x₂, x₃} : Set α).ncard ≤ 2 * p + 7 := by
        have hle3 : ({x₁, x₂, x₃} : Set α).ncard ≤ 3 := by
          have h1 := ncard_insert_le x₁ ({x₂, x₃} : Set α)
          have h2 := ncard_insert_le x₂ ({x₃} : Set α)
          rw [ncard_singleton] at h2
          omega
        omega
      exact theorem_6_6_proof h𝒯 π htrue.1 hwarp hred (by omega) hΘ
        hX_sub hX_card hclaim2

/-! ## 2. Cliques in General: (12.2) (Page 198) -/

/-- For a closed disc $\Delta \subseteq \Sigma$ with $\Gamma$-normal boundary, the attachments of
$\alpha(\Delta)$ in $G$ are contained in $\gamma(N(\Gamma) \cap \operatorname{bd}(\Delta))$, so
$|\operatorname{attachments}_G(\alpha(\Delta))| \le |\operatorname{bd}(\Delta) \cap N(\Gamma)|$. -/
private theorem ncard_attachments_areaGraph_le_normal_disc
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {Δ : Set π.S} (hΔ : IsClosedDisc Δ)
    (hnorm : π.Γ.IsNormal (discBd Δ)) :
    (attachments G (π.areaGraph Δ)).ncard ≤ (discBd Δ ∩ π.Γ.N).ncard := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have : ConnectedSpace π.S := π.connected
  let I₁ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Δ}
  let I₂ : Set (Set π.S) := {c ∈ π.Γ.C | ¬ c ⊆ Δ}
  have hcov : I₁ ∪ I₂ = π.Γ.C := by
    ext c
    simp only [I₁, I₂, mem_union, mem_sep_iff]
    exact ⟨fun h => h.elim And.left And.left,
      fun hc => by by_cases h : c ⊆ Δ <;> [exact Or.inl ⟨hc, h⟩; exact Or.inr ⟨hc, h⟩]⟩
  have hdisj : Disjoint I₁ I₂ := by
    rw [Set.disjoint_left]
    exact fun _ h₁ h₂ => h₂.2 h₁.2
  have hsep : G.IsSeparation (π.cellsUnion I₁) (π.cellsUnion I₂) :=
    π.isSeparation_cellsUnion hcov hdisj
  have hatt_sub_inter : attachments G (π.areaGraph Δ) ⊆
      (π.cellsUnion I₁ ∩ π.cellsUnion I₂).vertexSet :=
    attachments_subset_inter_of_isSeparation hsep
  have h21 := (theorem_2_1_proof π hcov hdisj).2
  obtain ⟨hdich, hno_bd, _⟩ := normal_disc_cell_dichotomy π.isSurface π.Γ hΔ hnorm
  have hsub_nv : attachments G (π.areaGraph Δ) ⊆ π.nodeVertex '' (discBd Δ ∩ π.Γ.N) := by
    intro v hv
    have hv_inter := hatt_sub_inter hv
    rw [h21] at hv_inter
    rcases hv_inter with hγ | hbs
    · rw [mem_iUnion₂] at hγ
      rcases hγ with ⟨c₁, hc₁, hγ⟩
      rw [mem_iUnion₂] at hγ
      rcases hγ with ⟨c₂, hc₂, hγ⟩
      rw [← π.gammaImage_inter, Portrayal.mem_gammaImage_iff] at hγ
      rcases hγ with ⟨n, ⟨hnc₁, hndom⟩, rfl⟩
      have hc₂_out : c₂ ⊆ Set.univ \ Δ :=
        (hdich c₂ hc₂.1).resolve_left fun h => hc₂.2 (h.trans sdiff_subset)
      have hcl_inter :=
        (closure_cell_inter_disc_of_subset_compl π.isSurface π.Γ hΔ hnorm hc₂.1 hc₂_out).2
      have hn_Δ : n ∈ Δ := (isClosed_of_isClosedDisc hΔ).closure_subset_iff.mpr hc₁.2 hnc₁.1.1
      have hn_bdΔ : n ∈ discBd Δ := by
        have : n ∈ closure c₂ ∩ Δ := ⟨hnc₁.2.1, hn_Δ⟩
        rw [hcl_inter] at this
        exact this.2
      exact ⟨n, ⟨hn_bdΔ, π.domγ_subset hndom⟩, rfl⟩
    · rw [mem_iUnion₂] at hbs
      rcases hbs with ⟨n, ⟨c₁, hc₁, hbd₁, _⟩, _⟩
      have hc₁_out : c₁ ⊆ Set.univ \ Δ := hno_bd c₁ hc₁.1 hbd₁
      rcases hbd₁ with ⟨x, hxc₁, _⟩
      exact ((hc₁_out hxc₁).2 (hc₁.2 hxc₁)).elim
  have hfin : (discBd Δ ∩ π.Γ.N).Finite := π.Γ.finite_N.inter_of_right _
  exact (ncard_le_ncard hsub_nv (hfin.image _)).trans (ncard_image_le hfin)

private theorem no_four_discs_in_portrayal
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ : ℕ}
    {p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G)
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 9 < θ) :
    ¬∃ Δ₀ Δ₁ Δ₂ Δ₃, (IsClosedDisc Δ₀ ∧ π.Γ.IsNormal (discBd Δ₀) ∧ (discBd Δ₀ ∩ π.Γ.N).ncard ≤ 3 ∧
      IsSmallWrt 𝒯 (π.areaGraph Δ₀)) ∧ (IsClosedDisc Δ₁ ∧ π.Γ.IsNormal (discBd Δ₁) ∧ (discBd Δ₁ ∩
      π.Γ.N).ncard ≤ 3 ∧ IsSmallWrt 𝒯 (π.areaGraph Δ₁)) ∧ (IsClosedDisc Δ₂ ∧ π.Γ.IsNormal (discBd
      Δ₂) ∧ (discBd Δ₂ ∩ π.Γ.N).ncard ≤ 3 ∧ IsSmallWrt 𝒯 (π.areaGraph Δ₂)) ∧ (IsClosedDisc Δ₃ ∧
      π.Γ.IsNormal (discBd Δ₃) ∧ (discBd Δ₃ ∩ π.Γ.N).ncard ≤ 3 ∧ IsSmallWrt 𝒯 (π.areaGraph Δ₃)) ∧
      ∀ c ∈ π.Γ.C, c ⊆ Δ₀ ∨ c ⊆ Δ₁ ∨ c ⊆ Δ₂ ∨ c ⊆ Δ₃ := by
  rintro ⟨Δ₀, Δ₁, Δ₂, Δ₃,
    ⟨hΔ₀, hnorm₀, hcard₀, hsmall₀⟩,
    ⟨hΔ₁, hnorm₁, hcard₁, hsmall₁⟩,
    ⟨_, _, _, ⟨B₂, hAB₂⟩⟩,
    ⟨_, _, _, ⟨B₃, hAB₃⟩⟩,
    hcov⟩
  have hatt₀ : (attachments G (π.areaGraph Δ₀)).ncard ≤ 3 :=
    (ncard_attachments_areaGraph_le_normal_disc π hΔ₀ hnorm₀).trans hcard₀
  have hatt₁ : (attachments G (π.areaGraph Δ₁)).ncard ≤ 3 :=
    (ncard_attachments_areaGraph_le_normal_disc π hΔ₁ hnorm₁).trans hcard₁
  have hatt_u : (attachments G (π.areaGraph Δ₀ ∪ π.areaGraph Δ₁)).ncard < θ := by
    have hsub : attachments G (π.areaGraph Δ₀ ∪ π.areaGraph Δ₁) ⊆
        attachments G (π.areaGraph Δ₀) ∪ attachments G (π.areaGraph Δ₁) := by
      rintro v ⟨hv₀ | hv₁, e, ⟨heG, he_not⟩, hinc⟩
      · exact Or.inl ⟨hv₀, e, ⟨heG, fun he₀ => he_not (Or.inl he₀)⟩, hinc⟩
      · exact Or.inr ⟨hv₁, e, ⟨heG, fun he₁ => he_not (Or.inr he₁)⟩, hinc⟩
    have hle := (ncard_le_ncard hsub (attachments_finite.union attachments_finite)).trans
      (ncard_union_le _ _)
    omega
  obtain ⟨B₀₁, hAB₀₁⟩ := hsmall₀.union h𝒯 hsmall₁ hatt_u
  let A₀₁ := π.areaGraph Δ₀ ∪ π.areaGraph Δ₁
  let A₂ := π.areaGraph Δ₂
  let A₃ := π.areaGraph Δ₃
  have hle_all : A₀₁ ∪ A₂ ∪ A₃ ≤ G :=
    union_le (union_le (h𝒯.isSeparation hAB₀₁).left_le (h𝒯.isSeparation hAB₂).left_le)
      (h𝒯.isSeparation hAB₃).left_le
  have hV_eq : (A₀₁ ∪ A₂ ∪ A₃).vertexSet = G.vertexSet := by
    refine Subset.antisymm hle_all.vertexSet_subset fun v hvG => ?_
    obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hvG
    rcases hcov c hc with hc₀ | hc₁ | hc₂ | hc₃
    · exact Or.inl (Or.inl (Or.inl (mem_biUnion ⟨⟨hc, hc₀⟩, hc⟩ hvc)))
    · exact Or.inl (Or.inl (Or.inr (mem_biUnion ⟨⟨hc, hc₁⟩, hc⟩ hvc)))
    · exact Or.inl (Or.inr (mem_biUnion ⟨⟨hc, hc₂⟩, hc⟩ hvc))
    · exact Or.inr (mem_biUnion ⟨⟨hc, hc₃⟩, hc⟩ hvc)
  have hE_eq : (A₀₁ ∪ A₂ ∪ A₃).edgeSet = G.edgeSet := by
    refine Subset.antisymm hle_all.edgeSet_subset fun e heG => ?_
    obtain ⟨c, hc, hec⟩ := π.p1_edge e heG
    rcases hcov c hc with hc₀ | hc₁ | hc₂ | hc₃
    · exact Or.inl (Or.inl (Or.inl (mem_biUnion ⟨⟨hc, hc₀⟩, hc⟩ hec)))
    · exact Or.inl (Or.inl (Or.inr (mem_biUnion ⟨⟨hc, hc₁⟩, hc⟩ hec)))
    · exact Or.inl (Or.inr (mem_biUnion ⟨⟨hc, hc₂⟩, hc⟩ hec))
    · exact Or.inr (mem_biUnion ⟨⟨hc, hc₃⟩, hc⟩ hec)
  exact h𝒯.axiom2 hAB₀₁ hAB₂ hAB₃
    (eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle_all le_rfl hV_eq hE_eq)

private theorem clique_vertices_in_cells_of_cuff
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {K : Set α}
    (hK : IsClique G K)
    (x : α)
    (hxK : x ∈ K)
    (hx_not_N : x ∉ π.nodeVertex '' π.Γ.N)
    (d : Set π.S)
    (hd : d ∈ π.Γ.C)
    (hxd : x ∈ (π.cellGraph d).vertexSet)
    (hcell_border : ∀ c ∈ π.Γ.C, x ∈ (π.cellGraph c).vertexSet → (c ∩ bd π.S).Nonempty ∧ ∃ n ∈
      tilde c, x ∈ π.borderSet n)
    (nd : π.S)
    (hx_nd : x ∈ π.borderSet nd)
    (Θ : Set π.S)
    (hΘ : Θ ∈ cuffs π.S)
    (hdΘ : (d ∩ Θ).Nonempty)
    (hnd_Θ : nd ∈ π.Γ.N ∩ Θ) :
    K ⊆ ⋃ c ∈ {c | c ∈ π.Γ.C ∧ (c ∩ Θ).Nonempty}, (π.cellGraph c).vertexSet := by
  intro y hyK
  by_cases hyx : y = x
  · subst hyx
    exact mem_iUnion₂.mpr ⟨d, ⟨hd, hdΘ⟩, hxd⟩
  · obtain ⟨_, e, hex, hey⟩ := hK.2 x hxK y hyK (Ne.symm hyx)
    obtain ⟨c, hc, hec⟩ := π.p1_edge e (G.edge_mem_of_inc hex)
    have hxc : x ∈ (π.cellGraph c).vertexSet :=
      (π.cellGraph c).vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le c hc) hec).mpr hex)
    have hyc : y ∈ (π.cellGraph c).vertexSet :=
      (π.cellGraph c).vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le c hc) hec).mpr hey)
    obtain ⟨hbd_c, nc, hnc_t, hx_nc⟩ := hcell_border c hc hxc
    obtain ⟨Θ', hΘ', hcΘ', htilde_c⟩ := π.Γ.exists_cuff_of_border_cell hc hbd_c
    have hnc_Θ' : nc ∈ π.Γ.N ∩ Θ' := htilde_c hnc_t
    have hΘ_eq : Θ' = Θ := by
      by_contra hne_Θ
      exact Set.disjoint_left.mp
        (π.p4_disjoint Θ hΘ Θ' hΘ' (Ne.symm hne_Θ) nd hnd_Θ nc hnc_Θ') hx_nd hx_nc
    exact mem_iUnion₂.mpr ⟨c, ⟨hc, hΘ_eq ▸ hcΘ'⟩, hyc⟩

/-- **Graph Minors XVII, (12.2)** (page 198):
"Let $\mathscr{T}$ be a tangle of order $>4p+9$ in a hypergraph $G$, and let
$\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a true, $(2p+7)$-redundant,
$\mathscr{T}$-central portrayal of $G$, with warp $\le p$. Then for every clique $K$ of $G$, either
(i) there is a disc $\Delta \subseteq \Sigma$ such that $\alpha(\Delta)$ is small,
$K \subseteq V(\alpha(\Delta))$, and $\operatorname{bd}(\Delta)$ is a $\Gamma$-normal $O$-arc with
$|\operatorname{bd}(\Delta) \cap N(\Gamma)| \le 3$, or
(ii) $K \subseteq V(\alpha(c))$ for some $c \in C(\Gamma)$."

In (i) we prove $K \subseteq V(\alpha(\Delta)) \cup \gamma(\operatorname{bd}(\Delta) \cap
N(\Gamma))$. The paper's proof gives $M \subseteq \Delta(C)$, and a node of
$\operatorname{bd}(\Delta)$ need not lie on a cell inside $\Delta$. This is what (12.4) uses, since
the cell made by (7.2) contains $\gamma(\operatorname{bd}(\Delta) \cap N(\Gamma))$. -/
theorem theorem_12_2_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 7))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 9 < θ)
    {K : Set α} (hK : IsClique G K) :
    (∃ Δ : Set π.S, IsClosedDisc Δ ∧ IsSmallWrt 𝒯 (π.areaGraph Δ) ∧
      K ⊆ (π.areaGraph Δ).vertexSet ∪ π.nodeVertex '' (discBd Δ ∩ π.Γ.N) ∧
      IsOArc (discBd Δ) ∧ π.Γ.IsNormal (discBd Δ) ∧
      (discBd Δ ∩ π.Γ.N).ncard ≤ 3) ∨
    (∃ c ∈ π.Γ.C, K ⊆ (π.cellGraph c).vertexSet) := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have : ConnectedSpace π.S := π.connected
  have hred3 : π.IsRedundant 𝒯 θ (2 * p + 3) := hred.mono (by omega)
  have hθ5 : 4 * p + 5 < θ := by omega
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof h𝒯 π htrue hred3 hwarp hθ5
  -- Claim (2): If there exists `x ∈ K` and a cell `c` with `x ∈ V(α(c)) - V(α(-c))`, then (ii)
  -- holds.
  by_cases hclaim2 : ∃ x ∈ K, ∃ c ∈ π.Γ.C,
      x ∈ (π.cellGraph c).vertexSet ∧ x ∉ π.otherVertices c
  · right
    rcases hclaim2 with ⟨x, hxK, c, hc, hxc, hx_not_other⟩
    refine ⟨c, hc, fun y hyK => ?_⟩
    by_cases hyx : y = x
    · exact hyx ▸ hxc
    · obtain ⟨_, e, hex, hey⟩ := hK.2 x hxK y hyK (Ne.symm hyx)
      obtain ⟨c', hc', hec'⟩ := π.p1_edge e (G.edge_mem_of_inc hex)
      have hxc' : x ∈ (π.cellGraph c').vertexSet :=
        (π.cellGraph c').vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le c' hc') hec').mpr hex)
      have hyc' : y ∈ (π.cellGraph c').vertexSet :=
        (π.cellGraph c').vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le c' hc') hec').mpr hey)
      have hcc' : c' = c := by
        by_contra hne
        exact hx_not_other ⟨c', hc', hne, hxc'⟩
      exact hcc' ▸ hyc'
  push Not at hclaim2
  -- Next, if there exists `x ∈ K` not in `π.nodeVertex '' π.Γ.N`, reduce to (12.1).
  by_cases hex_non_node : ∃ x ∈ K, x ∉ π.nodeVertex '' π.Γ.N
  · right
    rcases hex_non_node with ⟨x, hxK, hx_not_N⟩
    obtain ⟨d, hd, hxd⟩ := π.p1_vertex x (hK.1 hxK)
    have hcell_border : ∀ c ∈ π.Γ.C, x ∈ (π.cellGraph c).vertexSet →
        (c ∩ bd π.S).Nonempty ∧ ∃ n ∈ tilde c, x ∈ π.borderSet n := by
      intro c hc hxc
      obtain ⟨c', hc', hne, hxc'⟩ := hclaim2 x hxK c hc hxc
      have hbd : (c ∩ bd π.S).Nonempty := by
        by_contra hint
        obtain ⟨n, ⟨_, hn_dom⟩, hEq⟩ := π.p5 c hc hint x hxc ⟨c', hc', hne, hxc'⟩
        exact hx_not_N ⟨n, π.domγ_subset hn_dom, hEq⟩
      obtain ⟨n, hnt, hmem | ⟨hn_dom, hEq⟩⟩ := π.p6 c hc hbd x hxc ⟨c', hc', hne, hxc'⟩
      · exact ⟨hbd, n, hnt, hmem⟩
      · exact False.elim (hx_not_N ⟨n, π.domγ_subset hn_dom, hEq.symm⟩)
    obtain ⟨hbd_d, nd, hnd_t, hx_nd⟩ := hcell_border d hd hxd
    obtain ⟨Θ, hΘ, hdΘ, htilde_d⟩ := π.Γ.exists_cuff_of_border_cell hd hbd_d
    have hnd_Θ : nd ∈ π.Γ.N ∩ Θ := htilde_d hnd_t
    have hΘ_bd : Θ ⊆ bd π.S := by
      rcases hΘ with ⟨x₀, _, rfl⟩
      exact connectedComponentIn_subset (bd π.S) x₀
    have hK_sub_Θ : K ⊆ ⋃ c ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty}, (π.cellGraph c).vertexSet := by
      exact clique_vertices_in_cells_of_cuff (α := α) (β := β) (G := G) π (K := K) hK x hxK
        hx_not_N d hd hxd hcell_border nd hx_nd Θ hΘ hdΘ hnd_Θ
    obtain ⟨c, hc, _, hK_c⟩ :=
      theorem_12_1_proof h𝒯 π htrue hred hwarp hθ hΘ hK hK_sub_Θ
    exact ⟨c, hc, hK_c⟩
  · -- Claim (1): `K ⊆ π.nodeVertex '' π.Γ.N`.
    push Not at hex_non_node
    let M : Set π.S := {n ∈ π.Γ.N | π.nodeVertex n ∈ K}
    have hM_sub : M ⊆ π.Γ.N := fun _ h => h.1
    have hM_fin : M.Finite := π.Γ.finite_N.subset hM_sub
    have hK_eq_M : K = π.nodeVertex '' M := by
      ext x
      constructor
      · intro hxK
        obtain ⟨n, hnN, rfl⟩ := hex_non_node x hxK
        exact ⟨n, ⟨hnN, hxK⟩, rfl⟩
      · rintro ⟨n, ⟨_, hxK⟩, rfl⟩
        exact hxK
    have hinj_M : InjOn π.nodeVertex M :=
      π.nodeVertex_injOn.mono (fun _ h => hdom.symm ▸ h.1)
    have hadj_M : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ ≠ m₂ → ∃ c ∈ π.Γ.C, m₁ ∈ tilde c ∧ m₂ ∈ tilde c := by
      intro m₁ hm₁ m₂ hm₂ hne
      have hne_v : π.nodeVertex m₁ ≠ π.nodeVertex m₂ := hinj_M.ne hm₁ hm₂ hne
      obtain ⟨_, e, he₁, he₂⟩ := hK.2 (π.nodeVertex m₁) hm₁.2 (π.nodeVertex m₂) hm₂.2 hne_v
      obtain ⟨c, hc, hec⟩ := π.p1_edge e (G.edge_mem_of_inc he₁)
      have hv₁c : π.nodeVertex m₁ ∈ (π.cellGraph c).vertexSet :=
        (π.cellGraph c).vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le c hc) hec).mpr he₁)
      have hv₂c : π.nodeVertex m₂ ∈ (π.cellGraph c).vertexSet :=
        (π.cellGraph c).vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le c hc) hec).mpr he₂)
      have hm₁_tc : m₁ ∈ tilde c :=
        (nodeVertex_mem_cellGraph_iff h𝒯 π htrue hred3 hwarp hθ5 hc hm₁.1).mp hv₁c
      have hm₂_tc : m₂ ∈ tilde c :=
        (nodeVertex_mem_cellGraph_iff h𝒯 π htrue hred3 hwarp hθ5 hc hm₂.1).mp hv₂c
      exact ⟨c, hc, hm₁_tc, hm₂_tc⟩
    by_cases hex_cell : ∃ c ∈ π.Γ.C, M ⊆ tilde c
    · right
      rcases hex_cell with ⟨c, hc, hMc⟩
      refine ⟨c, hc, ?_⟩
      rw [hK_eq_M]
      rintro _ ⟨m, hm, rfl⟩
      exact π.p2 c hc m ⟨hMc hm, hdom.symm ▸ hm.1⟩
    have hM_ge3 : 3 ≤ M.ncard := by
      by_contra! hlt3
      apply hex_cell
      by_cases hM1 : M.ncard ≤ 1
      · by_cases hMne : M.Nonempty
        · obtain ⟨m, hm⟩ := hMne
          have hM_eq : M = {m} :=
            (eq_of_subset_of_ncard_le (singleton_subset_iff.mpr hm)
              (by rw [ncard_singleton]; omega) hM_fin).symm
          obtain ⟨c, hc, hvc⟩ := π.p1_vertex (π.nodeVertex m) (hK.1 hm.2)
          have hmt : m ∈ tilde c :=
            (nodeVertex_mem_cellGraph_iff h𝒯 π htrue hred3 hwarp hθ5 hc hm.1).mp hvc
          exact ⟨c, hc, hM_eq.symm ▸ singleton_subset_iff.mpr hmt⟩
        · rw [not_nonempty_iff_eq_empty] at hMne
          have hG_ne : G.vertexSet.Nonempty := by
            by_contra hemp
            rw [not_nonempty_iff_eq_empty] at hemp
            have hmem := IsTangle.discrete_mem h𝒯 (empty_subset G.vertexSet)
              (by rw [ncard_empty]; exact h𝒯.one_le)
            exact h𝒯.axiom3 hmem hemp.symm
          obtain ⟨v₀, hv₀⟩ := hG_ne
          obtain ⟨c, hc, _⟩ := π.p1_vertex v₀ hv₀
          exact ⟨c, hc, hMne.symm ▸ empty_subset _⟩
      · have hM2 : M.ncard = 2 := by omega
        obtain ⟨m₁, m₂, hne, hM_eq⟩ := ncard_eq_two.mp hM2
        have hm₁ : m₁ ∈ M := hM_eq ▸ mem_insert _ _
        have hm₂ : m₂ ∈ M := hM_eq ▸ mem_insert_of_mem _ (mem_singleton _)
        obtain ⟨c, hc, ht₁, ht₂⟩ := hadj_M m₁ hm₁ m₂ hm₂ hne
        refine ⟨c, hc, ?_⟩
        rw [hM_eq]
        rintro m (rfl | rfl) <;> assumption
    obtain ⟨h82_reg, h82_card, h82_node⟩ :=
      theorem_8_2_proof h𝒯 π htrue hred3 hwarp hθ5
    have h85_disc : ∀ F : Set π.S, IsOArc F → π.Γ.IsNormal F → (F ∩ π.Γ.N).ncard ≤ 3 →
        ∃ Δ : Set π.S, IsClosedDisc Δ ∧ discBd Δ = F ∧ IsSmallWrt 𝒯 (π.areaGraph Δ) := by
      intro F hO hnorm hcard
      obtain ⟨Δ, hΔ, hbd, hsmall, _⟩ :=
        theorem_8_5_proof h𝒯 π htrue hred3 hwarp hθ5 hO hnorm hcard
      exact ⟨Δ, hΔ, hbd, hsmall⟩
    have hno_four : ¬ ∃ Δ₀ Δ₁ Δ₂ Δ₃ : Set π.S,
        (IsClosedDisc Δ₀ ∧ π.Γ.IsNormal (discBd Δ₀) ∧ (discBd Δ₀ ∩ π.Γ.N).ncard ≤ 3 ∧
          IsSmallWrt 𝒯 (π.areaGraph Δ₀)) ∧
        (IsClosedDisc Δ₁ ∧ π.Γ.IsNormal (discBd Δ₁) ∧ (discBd Δ₁ ∩ π.Γ.N).ncard ≤ 3 ∧
          IsSmallWrt 𝒯 (π.areaGraph Δ₁)) ∧
        (IsClosedDisc Δ₂ ∧ π.Γ.IsNormal (discBd Δ₂) ∧ (discBd Δ₂ ∩ π.Γ.N).ncard ≤ 3 ∧
          IsSmallWrt 𝒯 (π.areaGraph Δ₂)) ∧
        (IsClosedDisc Δ₃ ∧ π.Γ.IsNormal (discBd Δ₃) ∧ (discBd Δ₃ ∩ π.Γ.N).ncard ≤ 3 ∧
          IsSmallWrt 𝒯 (π.areaGraph Δ₃)) ∧
        ∀ c ∈ π.Γ.C, c ⊆ Δ₀ ∨ c ⊆ Δ₁ ∨ c ⊆ Δ₂ ∨ c ⊆ Δ₃ := by
      exact no_four_discs_in_portrayal (α := α) (β := β) (G := G) (𝒯 := 𝒯) (θ := θ) (p := p) h𝒯 π
        hwarp hθ
    have hcellHyps : CellHyps π.Γ :=
      ⟨fun r hr => ⟨theorem_8_1_proof h𝒯 π htrue hred3 hwarp hθ5 hr, h82_reg r hr⟩, h82_card,
        h82_node⟩
    obtain ⟨Δ, hΔ, hO, hnorm, hcard, hsmall, hM_in⟩ :=
      clique_disc π.isSurface hcellHyps hM_sub hM_ge3 hadj_M (fun Δ => IsSmallWrt 𝒯
        (π.areaGraph Δ)) h85_disc
        (fun ⟨D, hD, hcov⟩ => hno_four ⟨D 0, D 1, D 2, D 3, hD 0, hD 1, hD 2, hD 3, fun c hc => by
          obtain ⟨k, hk⟩ := hcov c hc
          fin_cases k
          exacts [.inl hk, .inr (.inl hk), .inr (.inr (.inl hk)), .inr (.inr (.inr hk))]⟩)
    left
    refine ⟨Δ, hΔ, hsmall, ?_, hO, hnorm, hcard⟩
    rw [hK_eq_M]
    rintro _ ⟨m, hm, rfl⟩
    by_cases hmb : m ∈ discBd Δ
    · exact .inr ⟨m, ⟨hmb, hm.1⟩, rfl⟩
    · left
      obtain ⟨c, hc, hmc⟩ := h82_node m hm.1
      have hint : m ∈ discInt Δ := ⟨hM_in hm, hmb⟩
      have hman := π.isSurface.2.2
      obtain ⟨z, hzi, hzc⟩ := mem_closure_iff.mp hmc.1 _ (hΔ.isOpen_discInt hman) hint
      have hoff : Disjoint c (discBd Δ) := disjoint_left.mpr fun y hy hyb =>
        disjoint_left.mp (π.Γ.cell_disjoint_N hc) hy (hnorm ⟨hyb, π.Γ.cell_subset_U hc hy⟩)
      have hcΔ : c ⊆ Δ := by
        rcases disc_dichotomy hman hΔ (arcComponentsIn_isPathConnected
          hc).isConnected.isPreconnected hoff with h1 | h1
        · exact h1
        · exact absurd hzi.1 (disjoint_left.mp h1 hzc)
      exact mem_biUnion ⟨⟨hc, hcΔ⟩, hc⟩ (π.p2 c hc m ⟨hmc, hdom.symm ▸ hm.1⟩)

/-! ## 3. Adding an Edge Whose Ends Form a Clique: (12.3) (Page 199) -/

/-- If $G' \le G$ and $\mathcal{T}'$ is a tangle of order $\theta$ in $G'$, then the induced tangle
`inducedSubhypergraphTangle G G' 𝒯' θ` is a tangle of order $\theta$ in $G$.
Graph Minors XVII, Section 12 (page 199): "Then $\mathscr{T}$ is clearly a tangle in $G$; we call
it the *tangle induced by* $\mathscr{T}'$." -/
theorem isTangle_inducedSubhypergraphTangle {α : Type u} {β : Type v}
    {G G' : Hypergraph α β} {𝒯' : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (hle : G' ≤ G) (h𝒯' : IsTangle G' θ 𝒯') :
    IsTangle G θ (inducedSubhypergraphTangle G G' 𝒯' θ) :=
  GM10.isTangle_inducedTangleFromSubgraph hle h𝒯'

/-- Given a subhypergraph $H \le G$ and an edge $e \in E(G)$ with $\operatorname{ends}_G(e)
\subseteq V(H)$,
`addEdge G H e he hends` is the subhypergraph $(V(H), E(H) \cup \{e\})$ of $G$.
Graph Minors XVII, Section 12, (12.3) (page 199). -/
@[expose] def addEdge {α : Type u} {β : Type v} (G H : Hypergraph α β) (e : β)
    (he : e ∈ G.edgeSet) (hends : G.ends e ⊆ H.vertexSet) : Hypergraph α β where
  vertexSet := H.vertexSet
  edgeSet := H.edgeSet ∪ {e}
  Inc f v := H.Inc f v ∨ (f = e ∧ G.Inc e v)
  vertex_mem_of_inc := by
    rintro f v (h | ⟨_, h⟩)
    · exact H.vertex_mem_of_inc h
    · exact hends h
  edge_mem_of_inc := by
    rintro f v (h | ⟨rfl, _⟩)
    · exact Or.inl (H.edge_mem_of_inc h)
    · exact Or.inr (mem_singleton f)
  vertexSet_finite := H.vertexSet_finite
  edgeSet_finite := H.edgeSet_finite.union (finite_singleton e)

theorem addEdge_le {α : Type u} {β : Type v} {G H : Hypergraph α β} {e : β}
    (hH : H ≤ G) (he : e ∈ G.edgeSet) (hends : G.ends e ⊆ H.vertexSet) :
    addEdge G H e he hends ≤ G where
  vertexSet_subset := hH.vertexSet_subset
  edgeSet_subset := union_subset hH.edgeSet_subset (singleton_subset_iff.mpr he)
  ends_eq := by
    rintro f (hf | rfl)
    · ext v
      have hEq := congrArg (v ∈ ·) (hH.ends_eq f hf)
      exact ⟨fun hG => Or.inl (hEq.mp hG), fun h => h.elim hEq.mpr (fun ⟨rfl, hG⟩ => hG)⟩
    · ext v
      exact ⟨fun hG => Or.inr ⟨rfl, hG⟩, fun h => h.elim (fun hH_inc => by
        have hfH : f ∈ H.edgeSet := H.edge_mem_of_inc hH_inc
        have hEq := congrArg (v ∈ ·) (hH.ends_eq f hfH)
        exact hEq.mpr hH_inc) And.right⟩

/-- If a walk `w` in `K₂` is not a walk in a subgraph `K₁ ≤ K₂`, then `w` traverses an edge of `K₂`
that is not in `K₁`. -/
private theorem exists_adj_not_adj_of_not_walk {α : Type u} {K₁ K₂ : SimpleGraph α}
    {a b : α} (w : K₂.Walk a b)
    (hnot : ¬ ∃ w₁ : K₁.Walk a b, w₁.support = w.support) :
    ∃ v₁ ∈ w.support, ∃ v₂ ∈ w.support, K₂.Adj v₁ v₂ ∧ ¬ K₁.Adj v₁ v₂ := by
  induction w with
  | nil =>
    exfalso
    exact hnot ⟨.nil, rfl⟩
  | @cons x y z hadj tail ih =>
    by_cases hadj₁ : K₁.Adj x y
    · have hnot_tail : ¬ ∃ w₁ : K₁.Walk y z, w₁.support = tail.support := by
        rintro ⟨w₁, hsup⟩
        exact hnot ⟨.cons hadj₁ w₁, by simp [hsup]⟩
      obtain ⟨v₁, hv₁, v₂, hv₂, h2, h1⟩ := ih hnot_tail
      exact ⟨v₁, List.mem_cons_of_mem x hv₁, v₂, List.mem_cons_of_mem x hv₂, h2, h1⟩
    · exact ⟨x, SimpleGraph.Walk.start_mem_support _,
        y, List.mem_cons_of_mem x (SimpleGraph.Walk.start_mem_support _), hadj, hadj₁⟩

/-- In a linkage `P : Fin m → PathFromTo K X Y` of pairwise vertex-disjoint paths where
`X` is finite with `X.ncard = m`, every vertex in `(P i₀).walk.support ∩ X` equals `(P i₀).first`.
-/
private theorem eq_first_of_mem_support_of_linkage {α : Type u} {K : SimpleGraph α}
    {X Y : Set α} {m : ℕ} (hX_fin : X.Finite) (hX_card : X.ncard = m)
    (P : Fin m → PathFromTo K X Y)
    (hP_disj : Pairwise fun i j => Disjoint {z | z ∈ (P i).walk.support} {z | z ∈
      (P j).walk.support})
    {i₀ : Fin m} {v : α} (hv_sup : v ∈ (P i₀).walk.support) (hv_X : v ∈ X) :
    v = (P i₀).first := by
  have hinj : Function.Injective (fun i : Fin m => (P i).first) := by
    intro i j hij
    change (P i).first = (P j).first at hij
    by_contra hne
    have hmem_i : (P j).first ∈ (P i).walk.support :=
      hij ▸ SimpleGraph.Walk.start_mem_support (P i).walk
    exact Set.disjoint_left.mp (hP_disj hne)
      hmem_i (SimpleGraph.Walk.start_mem_support (P j).walk)
  have hsub : Set.range (fun i : Fin m => (P i).first) ⊆ X := by
    rintro _ ⟨i, rfl⟩; exact (P i).first_mem
  have hrange_card : (Set.range (fun i : Fin m => (P i).first)).ncard = m := by
    rw [ncard_range_of_injective hinj, Nat.card_fin]
  have hrange_eq : Set.range (fun i : Fin m => (P i).first) = X :=
    eq_of_subset_of_ncard_le hsub (by rw [hrange_card, hX_card]) hX_fin
  obtain ⟨j, hj⟩ : v ∈ Set.range (fun i : Fin m => (P i).first) := hrange_eq.symm ▸ hv_X
  have hji₀ : j = i₀ := by
    by_contra hne
    exact Set.disjoint_left.mp (hP_disj hne)
      (hj ▸ SimpleGraph.Walk.start_mem_support (P j).walk) hv_sup
  exact hj.symm.trans (congrArg (fun i => (P i).first) hji₀)

/-- Symmetric version for `Y`: every vertex in `(P i₀).walk.support ∩ Y` equals `(P i₀).last`. -/
private theorem eq_last_of_mem_support_of_linkage {α : Type u} {K : SimpleGraph α}
    {X Y : Set α} {m : ℕ} (hY_fin : Y.Finite) (hY_card : Y.ncard = m)
    (P : Fin m → PathFromTo K X Y)
    (hP_disj : Pairwise fun i j => Disjoint {z | z ∈ (P i).walk.support} {z | z ∈
      (P j).walk.support})
    {i₀ : Fin m} {v : α} (hv_sup : v ∈ (P i₀).walk.support) (hv_Y : v ∈ Y) :
    v = (P i₀).last := by
  have hinj : Function.Injective (fun i : Fin m => (P i).last) := by
    intro i j hij
    change (P i).last = (P j).last at hij
    by_contra hne
    have hmem_i : (P j).last ∈ (P i).walk.support :=
      hij ▸ SimpleGraph.Walk.end_mem_support (P i).walk
    exact Set.disjoint_left.mp (hP_disj hne)
      hmem_i (SimpleGraph.Walk.end_mem_support (P j).walk)
  have hsub : Set.range (fun i : Fin m => (P i).last) ⊆ Y := by
    rintro _ ⟨i, rfl⟩; exact (P i).last_mem
  have hrange_card : (Set.range (fun i : Fin m => (P i).last)).ncard = m := by
    rw [ncard_range_of_injective hinj, Nat.card_fin]
  have hrange_eq : Set.range (fun i : Fin m => (P i).last) = Y :=
    eq_of_subset_of_ncard_le hsub (by rw [hrange_card, hY_card]) hY_fin
  obtain ⟨j, hj⟩ : v ∈ Set.range (fun i : Fin m => (P i).last) := hrange_eq.symm ▸ hv_Y
  have hji₀ : j = i₀ := by
    by_contra hne
    exact Set.disjoint_left.mp (hP_disj hne)
      (hj ▸ SimpleGraph.Walk.end_mem_support (P j).walk) hv_sup
  exact hj.symm.trans (congrArg (fun i => (P i).last) hji₀)

private theorem cyclicDist_chain {k : ℕ} {a b c : Fin k} (h : cyclicDist a b
  ≤ cyclicDist a c) : cyclicDist a b + cyclicDist b c = cyclicDist a c := by
  have ha := a.2
  have hb := b.2
  have hc := c.2
  rw [cyclicDist_eq_ite a b, cyclicDist_eq_ite a c] at h
  rw [cyclicDist_eq_ite a b, cyclicDist_eq_ite b c, cyclicDist_eq_ite a c]
  split_ifs at h ⊢ <;> omega

private theorem cyclicDist_add_swap {k : ℕ} {a b : Fin k} (h : a ≠ b) : cyclicDist a b + cyclicDist
  b a = k := by
  have ha := a.2
  have hb := b.2
  have hne : a.1 ≠ b.1 := fun e => h (Fin.ext e)
  rw [cyclicDist_eq_ite a b, cyclicDist_eq_ite b a]
  split_ifs <;> omega

private theorem cyclicDist_succ {k : ℕ} (hk : 0 < k) (a t : Fin k) (hne : cyclicSucc hk t ≠ a) :
  cyclicDist a (cyclicSucc hk t) = cyclicDist a t + 1 := by
  have ha := a.2
  have ht := t.2
  have hne' : (cyclicSucc hk t).1 ≠ a.1 := fun e => hne (Fin.ext e)
  have hs : ((cyclicSucc hk t).1 = t.1 + 1 ∧ t.1 + 1 < k) ∨ ((cyclicSucc hk t).1 = 0 ∧ t.1 + 1 = k)
    := by
    by_cases h : t.1 + 1 < k
    · exact .inl ⟨Nat.mod_eq_of_lt h, h⟩
    · have h2 : t.1 + 1 = k := by omega
      refine .inr ⟨?_, h2⟩
      change (t.1 + 1) % k = 0
      rw [h2]
      exact Nat.mod_self k
  have hs2 := (cyclicSucc hk t).2
  rw [cyclicDist_eq_ite a t, cyclicDist_eq_ite a (cyclicSucc hk t)]
  generalize (cyclicSucc hk t).1 = u at *
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> split_ifs <;> omega

/-- Cyclic-order helper for Claim (1) in the proof of (12.3) (page 199): the two vertices `w₁`, `w₂`
lie on the two ends of the cell `E.cell j₀`, and each lies on an end `m₁`, `m₂` of another cell
`E.cell j`.
We measure positions on the cuff from `j₀`. If `i` comes before `m₂`, then (P7) for `j₀'`, `i`,
`m₂`, `j₀` puts `w₂` on `i`. If not, then `i` comes after `m₁`, and (P7) for `j₀`, `j₀'`, `m₁`, `i`
puts `w₁` on `i`. -/
private theorem borderPlus_nonempty_of_two_ends_in_other_cell
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    {j₀ j : Fin k} (hne_j : j ≠ j₀)
    {w₁ w₂ : α}
    (hw₁_j₀ : w₁ ∈ π.borderPlus (E.node j₀))
    (hw₁_not_next : w₁ ∉ π.borderPlus (E.node (cyclicSucc (Nat.lt_of_lt_of_le
      (by decide) E.two_le) j₀)))
    (hw₂_next : w₂ ∈ π.borderPlus (E.node (cyclicSucc (Nat.lt_of_lt_of_le
      (by decide) E.two_le) j₀)))
    (hw₂_not_j₀ : w₂ ∉ π.borderPlus (E.node j₀))
    (hw₁_c₀ : w₁ ∈ (π.cellGraph (E.cell j₀)).vertexSet)
    (hw₂_c₀ : w₂ ∈ (π.cellGraph (E.cell j₀)).vertexSet)
    (hw₁_c : w₁ ∈ (π.cellGraph (E.cell j)).vertexSet)
    (hw₂_c : w₂ ∈ (π.cellGraph (E.cell j)).vertexSet)
    (i : Fin k) :
    (({w₁, w₂} : Set α) ∩ π.borderPlus (E.node i)).Nonempty := by
  have hk0 : 0 < k := Nat.lt_of_lt_of_le (by decide) E.two_le
  have hcell_mem : ∀ r : Fin k, E.cell r ∈ π.Γ.C ∧ (E.cell r ∩ bd π.S).Nonempty := by
    intro r
    have hrange : E.cell r ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self r
    have hΘ_bd : Θ ⊆ bd π.S := by
      rcases E.cuff_mem with ⟨x₀, _, rfl⟩
      exact connectedComponentIn_subset (bd π.S) x₀
    exact ⟨hrange.1, hrange.2.mono (inter_subset_inter_right _ hΘ_bd)⟩
  have hne_cell : E.cell j ≠ E.cell j₀ := fun h => hne_j (E.injective_cell h)
  obtain ⟨n_m₁, hm₁_t, hw₁_m₁⟩ := π.p6 (E.cell j) (hcell_mem j).1 (hcell_mem j).2 w₁ hw₁_c
    ⟨E.cell j₀, (hcell_mem j₀).1, hne_cell.symm, hw₁_c₀⟩
  obtain ⟨n_m₂, hm₂_t, hw₂_m₂⟩ := π.p6 (E.cell j) (hcell_mem j).1 (hcell_mem j).2 w₂ hw₂_c
    ⟨E.cell j₀, (hcell_mem j₀).1, hne_cell.symm, hw₂_c₀⟩
  rw [E.cell_tilde j] at hm₁_t hm₂_t
  have hm₁_ex : ∃ m₁ : Fin k, (m₁ = j ∨ m₁ = cyclicSucc hk0 j) ∧ n_m₁ = E.node m₁ := by
    rcases hm₁_t with rfl | hm₁_t
    · exact ⟨j, Or.inl rfl, rfl⟩
    · exact ⟨cyclicSucc hk0 j, Or.inr rfl, mem_singleton_iff.mp hm₁_t⟩
  have hm₂_ex : ∃ m₂ : Fin k, (m₂ = j ∨ m₂ = cyclicSucc hk0 j) ∧ n_m₂ = E.node m₂ := by
    rcases hm₂_t with rfl | hm₂_t
    · exact ⟨j, Or.inl rfl, rfl⟩
    · exact ⟨cyclicSucc hk0 j, Or.inr rfl, mem_singleton_iff.mp hm₂_t⟩
  obtain ⟨m₁, hm₁_cases, rfl⟩ := hm₁_ex
  obtain ⟨m₂, hm₂_cases, rfl⟩ := hm₂_ex
  change w₁ ∈ π.borderPlus (E.node m₁) at hw₁_m₁
  change w₂ ∈ π.borderPlus (E.node m₂) at hw₂_m₂
  set j₀' := cyclicSucc hk0 j₀ with hj₀'
  have hj₀ne : j₀' ≠ j₀ := cyclicSucc_ne_self E.two_le j₀
  by_cases hi_j₀ : i = j₀
  · exact ⟨w₁, Or.inl rfl, hi_j₀ ▸ hw₁_j₀⟩
  by_cases hi_j₀' : i = j₀'
  · exact ⟨w₂, Or.inr rfl, hi_j₀' ▸ hw₂_next⟩
  by_cases hi_m₁ : i = m₁
  · exact ⟨w₁, Or.inl rfl, hi_m₁ ▸ hw₁_m₁⟩
  by_cases hi_m₂ : i = m₂
  · exact ⟨w₂, Or.inr rfl, hi_m₂ ▸ hw₂_m₂⟩
  have hm₁_ne_j₀' : m₁ ≠ j₀' := fun h => hw₁_not_next (h ▸ hw₁_m₁)
  have hm₂_ne_j₀ : m₂ ≠ j₀ := fun h => hw₂_not_j₀ (h ▸ hw₂_m₂)
  have hd1 : cyclicDist j₀ j₀' = 1 := by
    have h1 := cyclicDist_succ hk0 j₀ j₀ hj₀ne
    rw [cyclicDist_self] at h1
    exact h1
  have hinj : ∀ {a b : Fin k}, a ≠ j₀ → b ≠ j₀ → a ≠ b → cyclicDist j₀ a ≠ cyclicDist j₀ b
    := fun {a b} ha hb hab e => by
    have h1 := cyclicDist_add_swap ha.symm
    have h2 := cyclicDist_add_swap hb.symm
    have h3 : a.1 ≠ b.1 := fun e' => hab (Fin.ext e')
    have ha' : a.1 ≠ j₀.1 := fun e' => ha (Fin.ext e')
    have hb' : b.1 ≠ j₀.1 := fun e' => hb (Fin.ext e')
    have h4 := a.2
    have h5 := b.2
    have h6 := j₀.2
    rw [cyclicDist_eq_ite j₀ a, cyclicDist_eq_ite j₀ b] at e
    split_ifs at e <;> omega
  have hp_i : 1 < cyclicDist j₀ i := by
    have h1 := cyclicDist_pos_of_ne (Ne.symm hi_j₀)
    have h2 := hinj hi_j₀ hj₀ne hi_j₀'
    omega
  have hlt := cyclicDist_lt hk0 j₀ i
  have hltm := cyclicDist_lt hk0 j₀ m₂
  have hm₂_ne := hinj hi_j₀ hm₂_ne_j₀ hi_m₂
  by_cases hcmp : cyclicDist j₀ i < cyclicDist j₀ m₂
  · -- `w₂` lies on `i`, by (P7) for `j₀'`, `i`, `m₂`, `j₀`.
    refine ⟨w₂, Or.inr rfl, ?_⟩
    have hsum : cyclicDist j₀' i + cyclicDist i m₂ + cyclicDist m₂ j₀ ≤ k := by
      have h0 := cyclicDist_chain (a := j₀) (b := j₀') (c := i) (by omega)
      have h1 := cyclicDist_chain hcmp.le
      have h2 := cyclicDist_add_swap hm₂_ne_j₀.symm
      omega
    exact (π.p7_of_cyclicDist E hsum hw₂_next hw₂_m₂).resolve_right hw₂_not_j₀
  · -- `w₁` lies on `i`, by (P7) for `j₀`, `j₀'`, `m₁`, `i`.
    refine ⟨w₁, Or.inl rfl, ?_⟩
    have hgt : cyclicDist j₀ m₂ < cyclicDist j₀ i := by omega
    have hj₁ : j ≠ j₀ := hne_j
    have hm₂pos := cyclicDist_pos_of_ne (Ne.symm hm₂_ne_j₀)
    have hm₁_lt : cyclicDist j₀ m₁ < cyclicDist j₀ i ∧ m₁ ≠ j₀ := by
      rcases hm₁_cases with h1 | h1
      · rw [h1]
        refine ⟨?_, hne_j⟩
        rcases hm₂_cases with h2 | h2
        · rw [← h2]
          exact hgt
        · have h3 := cyclicDist_succ hk0 j₀ j (h2 ▸ hm₂_ne_j₀)
          rw [← h2] at h3
          omega
      · rcases hm₂_cases with h2 | h2
        · by_cases h3 : cyclicSucc hk0 j = j₀
          · exfalso
            have h4 : cyclicDist j₀ j + 1 = k := by
              have h5 := cyclicDist_add_swap hne_j.symm
              have h6 : cyclicDist j j₀ = 1 := by
                rw [← h3]
                have h7 := cyclicDist_succ hk0 j j (cyclicSucc_ne_self E.two_le j)
                rw [cyclicDist_self] at h7
                exact h7
              omega
            rw [h2] at hgt
            omega
          · have h4 := cyclicDist_succ hk0 j₀ j h3
            rw [← h1] at h4 h3
            rw [h2] at hgt
            refine ⟨?_, h3⟩
            have h5 := hinj hi_j₀ h3 hi_m₁
            omega
        · have e : m₂ = m₁ := h2.trans h1.symm
          exact ⟨e ▸ hgt, e ▸ hm₂_ne_j₀⟩
    obtain ⟨hlt₁, hm₁j⟩ := hm₁_lt
    have hp1 : cyclicDist j₀ j₀' ≤ cyclicDist j₀ m₁ := by
      have h1 := cyclicDist_pos_of_ne (Ne.symm hm₁j)
      omega
    have hsum : cyclicDist j₀ j₀' + cyclicDist j₀' m₁ + cyclicDist m₁ i ≤ k := by
      have h1 := cyclicDist_chain hp1
      have h2 := cyclicDist_chain hlt₁.le
      omega
    exact (π.p7_of_cyclicDist E hsum hw₁_j₀ hw₁_m₁).resolve_left hw₁_not_next

/-- The cell graphs of `π'` in (12.3): the edge `e` is added to the graph of the cell `c₀`, and
every other cell keeps its graph. -/
@[expose] noncomputable def addEdgeCell {α : Type u} {β : Type v} {G : Hypergraph α β} {e : β}
    (π : Portrayal (G.deleteEdges {e})) {c₀ : Set π.S} (he : e ∈ G.edgeSet)
    (hends : G.ends e ⊆ (π.cellGraph c₀).vertexSet) (c : Set π.S) : Hypergraph α β :=
  open Classical in if c = c₀ then addEdge G (π.cellGraph c₀) e he hends else π.cellGraph c

theorem addEdgeCell_vertexSet {α : Type u} {β : Type v} {G : Hypergraph α β} {e : β}
    (π : Portrayal (G.deleteEdges {e})) {c₀ : Set π.S} (he : e ∈ G.edgeSet)
    (hends : G.ends e ⊆ (π.cellGraph c₀).vertexSet) (c : Set π.S) :
    (addEdgeCell π he hends c).vertexSet = (π.cellGraph c).vertexSet := by
  dsimp only [addEdgeCell]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem deleteEdges_singleton_le {α : Type u} {β : Type v} (G : Hypergraph α β) (e : β) :
    G.deleteEdges {e} ≤ G :=
  ⟨subset_rfl, sdiff_subset, fun f hf => by
    ext v
    exact ⟨fun h => ⟨h, hf.2⟩, fun h => h.1⟩⟩

/-- The separation `(α(c), α(-c))` has order at most `max(3, 2p + 2)` when `π` has warp `≤ p`: by
(P5) for an internal cell, and by (P6) for a border cell. -/
theorem Portrayal.ncard_cell_inter_other_le {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {p : ℕ} (hwarp : π.warp ≤ p) {c : Set π.S} (hc : c ∈ π.Γ.C) :
    ((π.cellGraph c).vertexSet ∩ π.otherVertices c).ncard ≤ max 3 (2 * p + 2) := by
  by_cases hbd : (c ∩ bd π.S).Nonempty
  · obtain ⟨n₁, n₂, _, htilde, _, _, hn₁_mem, hn₂_mem⟩ := π.Γ.border_cell_exists_ends hc hbd
    have hsub_bp : (π.cellGraph c).vertexSet ∩ π.otherVertices c ⊆
        π.borderPlus n₁ ∪ π.borderPlus n₂ := by
      rintro v ⟨hvc, d, hd, hne, hvd⟩
      obtain ⟨n, hnt, hv_bp⟩ := π.p6 c hc hbd v hvc ⟨d, hd, hne, hvd⟩
      rcases (htilde ▸ hnt : n ∈ ({n₁, n₂} : Set π.S)) with rfl | rfl
      · exact Or.inl hv_bp
      · exact Or.inr hv_bp
    have hb₁ : (π.borderPlus n₁).ncard ≤ p + 1 :=
      (π.ncard_borderPlus_le hn₁_mem).trans
        (Nat.add_le_add_right ((π.ncard_borderSet_le_warp hn₁_mem).trans hwarp) 1)
    have hb₂ : (π.borderPlus n₂).ncard ≤ p + 1 :=
      (π.ncard_borderPlus_le hn₂_mem).trans
        (Nat.add_le_add_right ((π.ncard_borderSet_le_warp hn₂_mem).trans hwarp) 1)
    have hfin_u : (π.borderPlus n₁ ∪ π.borderPlus n₂).Finite :=
      (π.borderPlus_finite hn₁_mem).union (π.borderPlus_finite hn₂_mem)
    have hle := (ncard_le_ncard hsub_bp hfin_u).trans (ncard_union_le _ _)
    omega
  · have hsub_γ : (π.cellGraph c).vertexSet ∩ π.otherVertices c ⊆
        π.nodeVertex '' (tilde c ∩ π.domγ) := by
      rintro v ⟨hvc, d, hd, hne, hvd⟩
      exact π.p5 c hc hbd v hvc ⟨d, hd, hne, hvd⟩
    have hsub_t : tilde c ∩ π.domγ ⊆ tilde c := inter_subset_left
    have hfin_t : (tilde c).Finite := π.Γ.finite_tilde_cell hc
    have hcard_t : (tilde c).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hc
    have hle := (ncard_le_ncard hsub_γ ((hfin_t.subset hsub_t).image _)).trans
      ((ncard_image_le (hfin_t.subset hsub_t)).trans (ncard_le_ncard hsub_t hfin_t))
    omega

/-- The portrayal `π' = (Σ, Γ, α', β, γ)` of (12.3): the portrayal `π` of `G \ e` with the edge `e`
added to the cell `c₀`. It is a portrayal of `G`, since all ends of `e` lie in `V(α(c₀))`. -/
@[expose] noncomputable def addEdgePortrayal {α : Type u} {β : Type v} {G : Hypergraph α β} {e : β}
    (π : Portrayal (G.deleteEdges {e})) {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (he : e ∈ G.edgeSet)
    (hends : G.ends e ⊆ (π.cellGraph c₀).vertexSet) : Portrayal G :=
  { S := π.S
    top := π.top
    isSurface := π.isSurface
    connected := π.connected
    Γ := π.Γ
    cellGraph := addEdgeCell π he hends
    borderSet := π.borderSet
    domγ := π.domγ
    nodeVertex := π.nodeVertex
    cellGraph_le := fun c hc => by
      dsimp only [addEdgeCell]; split_ifs with h
      · exact addEdge_le ((π.cellGraph_le c₀ hc₀).trans (deleteEdges_singleton_le G e)) he hends
      · exact (π.cellGraph_le c hc).trans (deleteEdges_singleton_le G e)
    borderSet_subset := π.borderSet_subset
    domγ_subset := π.domγ_subset
    nodeVertex_mem := π.nodeVertex_mem
    nodeVertex_injOn := π.nodeVertex_injOn
    p1_vertex := fun v hv => by
      obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
      exact ⟨c, hc, (addEdgeCell_vertexSet π he hends c).symm ▸ hvc⟩
    p1_edge := fun f hf => by
      by_cases hfe : f = e
      · subst hfe
        refine ⟨c₀, hc₀, ?_⟩
        dsimp only [addEdgeCell]
        rw [ite_eq_left rfl]
        exact Or.inr (mem_singleton f)
      · obtain ⟨c, hc, hfc⟩ := π.p1_edge f ⟨hf, hfe⟩
        refine ⟨c, hc, ?_⟩
        dsimp only [addEdgeCell]; split_ifs with h
        · subst h; exact Or.inl hfc
        · exact hfc
    p1_disjoint := fun c₁ hc₁ c₂ hc₂ hne => by
      have hdisj₀ := π.p1_disjoint c₁ hc₁ c₂ hc₂ hne
      have he_not : ∀ c ∈ π.Γ.C, e ∉ (π.cellGraph c).edgeSet := fun c hc hec =>
        ((π.cellGraph_le c hc).edgeSet_subset hec).2 (mem_singleton e)
      dsimp only [addEdgeCell]
      split_ifs with h1 h2 h2
      · exact False.elim (hne (h1.trans h2.symm))
      · change Disjoint ((π.cellGraph c₀).edgeSet ∪ {e}) (π.cellGraph c₂).edgeSet
        rw [disjoint_union_left, disjoint_singleton_left]
        exact ⟨h1 ▸ hdisj₀, he_not c₂ hc₂⟩
      · change Disjoint (π.cellGraph c₁).edgeSet ((π.cellGraph c₀).edgeSet ∪ {e})
        rw [disjoint_union_right, disjoint_singleton_right]
        exact ⟨h2 ▸ hdisj₀, he_not c₁ hc₁⟩
      · exact hdisj₀
    p2 := fun c hc n hn => (addEdgeCell_vertexSet π he hends c).symm ▸ π.p2 c hc n hn
    p3_notMem := π.p3_notMem
    p3_subset := fun c hc hbd n hnt v hv => (addEdgeCell_vertexSet π he hends c).symm ▸ π.p3_subset
      c hc hbd n hnt hv
    p4_disjoint := π.p4_disjoint
    p4_notMem := π.p4_notMem
    p5 := fun c hc hint v hvc hex => by
      rcases hex with ⟨c', hc', hne, hvc'⟩
      exact π.p5 c hc hint v (addEdgeCell_vertexSet π he hends c ▸ hvc) ⟨c', hc', hne,
        addEdgeCell_vertexSet π he hends c' ▸ hvc'⟩
    p6 := fun c hc hbd v hvc hex => by
      rcases hex with ⟨c', hc', hne, hvc'⟩
      exact π.p6 c hc hbd v (addEdgeCell_vertexSet π he hends c ▸ hvc) ⟨c', hc', hne,
        addEdgeCell_vertexSet π he hends c' ▸ hvc'⟩
    p7 := π.p7 }

theorem addEdgePortrayal_central {α : Type u} {β : Type v} {G : Hypergraph α β} {e : β}
    (he : e ∈ G.edgeSet) {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle (G.deleteEdges {e}) θ 𝒯) (hθ : 2 * p + 8 < θ)
    (π : Portrayal (G.deleteEdges {e})) (hcentral : π.IsCentral 𝒯) (hwarp : π.warp ≤ p)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hends : G.ends e ⊆ (π.cellGraph c₀).vertexSet) :
    (addEdgePortrayal π hc₀ he hends).IsCentral (inducedSubhypergraphTangle G
      (G.deleteEdges {e}) 𝒯 θ) := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  intro c hc
  let A := (addEdgePortrayal π hc₀ he hends).cellGraph c
  let D := complSubhypergraph G A
  have hA_le : A ≤ G := (addEdgePortrayal π hc₀ he hends).cellGraph_le c hc
  have hsep_AD : G.IsSeparation A D := isSeparation_complSubhypergraph hA_le
  have hother_eq : (addEdgePortrayal π hc₀ he hends).otherVertices c = π.otherVertices c := by
    ext v
    simp only [Portrayal.otherVertices, mem_ofPred_eq]
    exact ⟨fun ⟨d, hd, hne, hvd⟩ => ⟨d, hd, hne, addEdgeCell_vertexSet π he hends d ▸ hvd⟩,
      fun ⟨d, hd, hne, hvd⟩ => ⟨d, hd, hne, (addEdgeCell_vertexSet π he hends d).symm ▸ hvd⟩⟩
  have hatt_sub : attachments G A ⊆ (π.cellGraph c).vertexSet ∩ π.otherVertices c := by
    have hsub := (addEdgePortrayal π hc₀ he hends).attachments_cellGraph_subset_otherVertices hc
    rw [hother_eq] at hsub
    exact fun v hv => ⟨(addEdgeCell_vertexSet π he hends c).subset (hsub hv).1, (hsub hv).2⟩
  have hcard_other := π.ncard_cell_inter_other_le hwarp hc
  have hord_AD : separationOrder A D < θ := by
    rw [separationOrder_complSubhypergraph]
    have hfin_inter : ((π.cellGraph c).vertexSet ∩ π.otherVertices c).Finite :=
      (π.cellGraph c).vertexSet_finite.inter_of_left _
    have hle := (ncard_le_ncard hatt_sub hfin_inter).trans hcard_other
    omega
  have hA_inter_G₀ : A ∩ (G.deleteEdges {e}) = π.cellGraph c := by
    have hle1 : A ∩ (G.deleteEdges {e}) ≤ (G.deleteEdges {e}) := inter_le_right hA_le
      (deleteEdges_singleton_le G e)
    have hle2 : π.cellGraph c ≤ (G.deleteEdges {e}) := π.cellGraph_le c hc
    apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle1 hle2
    · change (addEdgeCell π he hends c).vertexSet ∩ G.vertexSet = (π.cellGraph c).vertexSet
      rw [addEdgeCell_vertexSet π he hends c]
      exact inter_eq_self_of_subset_left hle2.vertexSet_subset
    · change (addEdgeCell π he hends c).edgeSet ∩ (G.deleteEdges {e}).edgeSet =
        (π.cellGraph c).edgeSet
      dsimp only [addEdgeCell]
      split_ifs with h
      · rw [h]
        ext f
        change (f ∈ (π.cellGraph c₀).edgeSet ∨ f = e) ∧ (f ∈ G.edgeSet ∧ f ≠ e) ↔
          f ∈ (π.cellGraph c₀).edgeSet
        exact ⟨fun ⟨h1, _, hne⟩ => h1.resolve_right hne,
          fun hf => ⟨Or.inl hf, (π.cellGraph_le c₀ hc₀).edgeSet_subset hf⟩⟩
      · exact inter_eq_self_of_subset_left hle2.edgeSet_subset
  have hsep_G₀ : (G.deleteEdges {e}).IsSeparation (π.cellGraph c) (D ∩ (G.deleteEdges {e})) := by
    rw [← hA_inter_G₀]
    have h1 : A ∩ (G.deleteEdges {e}) ≤ (G.deleteEdges {e}) := inter_le_right hsep_AD.left_le
      (deleteEdges_singleton_le G e)
    have h2 : D ∩ (G.deleteEdges {e}) ≤ (G.deleteEdges {e}) := inter_le_right hsep_AD.right_le
      (deleteEdges_singleton_le G e)
    rw [isSeparation_iff_of_le h1 h2]
    refine ⟨?_, ?_, ?_⟩
    · change (A.vertexSet ∩ (G.deleteEdges {e}).vertexSet) ∪ (D.vertexSet ∩
        (G.deleteEdges {e}).vertexSet) = (G.deleteEdges {e}).vertexSet
      rw [← union_inter_distrib_right, hsep_AD.vertexSet_union]
      exact Set.inter_self _
    · change (A.edgeSet ∩ (G.deleteEdges {e}).edgeSet) ∪ (D.edgeSet ∩ (G.deleteEdges {e}).edgeSet)
        = (G.deleteEdges {e}).edgeSet
      rw [← union_inter_distrib_right, hsep_AD.edgeSet_union,
        inter_eq_self_of_subset_right (deleteEdges_singleton_le G e).edgeSet_subset]
    · ext f
      change (f ∈ A.edgeSet ∧ f ∈ (G.deleteEdges {e}).edgeSet) ∧ (f ∈ D.edgeSet ∧ f ∈
        (G.deleteEdges {e}).edgeSet) ↔ False
      have hdisj_f : f ∉ (A ∩ D).edgeSet := hsep_AD.edgeSet_inter_eq ▸ notMem_empty f
      change ¬ (f ∈ A.edgeSet ∧ f ∈ D.edgeSet) at hdisj_f
      tauto
  have hord_G₀ : separationOrder (π.cellGraph c) (D ∩ (G.deleteEdges {e})) < θ := by
    rw [← hA_inter_G₀]
    have hsub : ((A ∩ (G.deleteEdges {e})) ∩ (D ∩ (G.deleteEdges {e}))).vertexSet ⊆
      (A ∩ D).vertexSet :=
      fun _ ⟨⟨hA, _⟩, ⟨hD, _⟩⟩ => ⟨hA, hD⟩
    exact (ncard_le_ncard hsub (A ∩ D).vertexSet_finite).trans_lt hord_AD
  have hmem_𝒯 : (π.cellGraph c, D ∩ (G.deleteEdges {e})) ∈ 𝒯 :=
    theorem_4_1_i h𝒯 (hcentral c hc) hsep_G₀ hord_G₀
  exact ⟨D, hsep_AD, hord_AD, by rwa [hA_inter_G₀]⟩

private theorem false_of_adjacent_cell_border_paths
    {α : Type u} {β : Type v} {G : Hypergraph α β} {e : β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle (G.deleteEdges {e}) θ 𝒯) (hθ : 2 * p + 8 < θ)
    (π : Portrayal (G.deleteEdges {e})) (hcentral : π.IsCentral 𝒯)
    (hred6 : π.IsRedundant 𝒯 θ 6) (hwarp : π.warp ≤ p)
    (hdisj : ∀ n ∈ π.Γ.N ∩ bd π.S, Disjoint (π.borderSet n) (π.nodeVertex '' π.domγ))
    {c c' Θ : Set π.S} (hc : c ∈ π.Γ.C) (hc' : c' ∈ π.Γ.C) (hne_c' : c' ≠ c)
    (hΘ : Θ ∈ cuffs π.S) (hcΘ : (c ∩ Θ).Nonempty)
    {n₁ n₂ : π.S} (hn₁ : n₁ ∈ tilde c) (hn₂ : n₂ ∈ tilde c) (hne12 : n₁ ≠ n₂)
    (hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S) (hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S)
    {u₁ u₂ : α} (hu₁_ne_u₂ : u₁ ≠ u₂)
    (hu₁_bp₁ : u₁ ∈ π.borderPlus n₁) (hu₂_bp₂ : u₂ ∈ π.borderPlus n₂)
    (hu₁_not_bp₂ : u₁ ∉ π.borderPlus n₂) (hu₂_not_bp₁ : u₂ ∉ π.borderPlus n₁)
    (hu₁_c : u₁ ∈ (π.cellGraph c).vertexSet) (hu₂_c : u₂ ∈ (π.cellGraph c).vertexSet)
    (hu₁_c' : u₁ ∈ (π.cellGraph c').vertexSet) (hu₂_c' : u₂ ∈ (π.cellGraph c').vertexSet)
    (hex_bs : u₁ ∈ π.borderSet n₁ ∨ u₂ ∈ π.borderSet n₂) : False := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hbd_c' : (c' ∩ bd π.S).Nonempty := by
    by_contra hint_c'
    rcases hex_bs with hu₁_bs | hu₂_bs
    · obtain ⟨m, ⟨_, hm_dom⟩, hm_eq⟩ :=
        π.p5 c' hc' hint_c' u₁ hu₁_c' ⟨c, hc, hne_c'.symm, hu₁_c⟩
      exact Set.disjoint_left.mp (hdisj n₁ hn₁_bd) hu₁_bs ⟨m, hm_dom, hm_eq⟩
    · obtain ⟨m, ⟨_, hm_dom⟩, hm_eq⟩ :=
        π.p5 c' hc' hint_c' u₂ hu₂_c' ⟨c, hc, hne_c'.symm, hu₂_c⟩
      exact Set.disjoint_left.mp (hdisj n₂ hn₂_bd) hu₂_bs ⟨m, hm_dom, hm_eq⟩
  obtain ⟨Θ', hΘ', hc'Θ', htilde_c'_Θ'⟩ := π.Γ.exists_cuff_of_border_cell hc' hbd_c'
  have hΘ'_bd : Θ' ⊆ bd π.S := by
    rcases hΘ' with ⟨y₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) y₀
  have htilde_c_Θ : tilde c ⊆ π.Γ.N ∩ Θ := (π.Γ.border_cell_subset_cuff hc hΘ hcΘ).2.2.2.1
  have hΘ'_eq_Θ : Θ' = Θ := by
    obtain ⟨n', hn'_t, hu₁_bp'⟩ := π.p6 c' hc' hbd_c' u₁ hu₁_c' ⟨c, hc, hne_c'.symm, hu₁_c⟩
    have hn'_Θ' : n' ∈ π.Γ.N ∩ Θ' := htilde_c'_Θ' hn'_t
    obtain ⟨Θ₀, hΘ₀, hn₁Θ₀, hn'Θ₀⟩ := π.cuff_eq_of_borderPlus_inter_nonempty
      hn₁_bd ⟨hn'_Θ'.1, hΘ'_bd hn'_Θ'.2⟩ hu₁_bp₁ hu₁_bp'
    have h1 : Θ₀ = Θ := cuffs_eq_of_nonempty_inter hΘ₀ hΘ ⟨n₁, hn₁Θ₀, (htilde_c_Θ hn₁).2⟩
    have h2 : Θ₀ = Θ' := cuffs_eq_of_nonempty_inter hΘ₀ hΘ' ⟨n', hn'Θ₀, hn'_Θ'.2⟩
    exact h2.symm.trans h1
  have hc'Θ : (c' ∩ Θ).Nonempty := hΘ'_eq_Θ ▸ hc'Θ'
  have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  have hc_range : c ∈ Set.range E.cell := by rw [E.range_cell]; exact ⟨hc, hcΘ⟩
  have hc'_range : c' ∈ Set.range E.cell := by rw [E.range_cell]; exact ⟨hc', hc'Θ⟩
  obtain ⟨j₀, hj₀⟩ := hc_range
  obtain ⟨j, hj⟩ := hc'_range
  subst hj₀ hj
  have hne_j : j ≠ j₀ := fun h => hne_c' (congrArg E.cell h)
  have hk0 : 0 < (π.Γ.N ∩ Θ).ncard := Nat.lt_of_lt_of_le (by decide) E.two_le
  have hn₁_ends : n₁ = E.node j₀ ∨ n₁ = E.node (cyclicSucc hk0 j₀) := by
    have h := hn₁
    rw [E.cell_tilde j₀] at h
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (mem_singleton_iff.mp h)
  have hn₂_ends : n₂ = E.node j₀ ∨ n₂ = E.node (cyclicSucc hk0 j₀) := by
    have h := hn₂
    rw [E.cell_tilde j₀] at h
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (mem_singleton_iff.mp h)
  have hclaim1 : ∀ n ∈ π.Γ.N ∩ Θ, (({u₁, u₂} : Set α) ∩ π.borderPlus n).Nonempty := by
    intro n hn
    have hn_range : n ∈ Set.range E.node := by rw [E.range_node]; exact hn
    rcases hn_range with ⟨i, rfl⟩
    rcases hn₁_ends with hn₁_eq | hn₁_eq <;> rcases hn₂_ends with hn₂_eq | hn₂_eq
    · exact False.elim (hne12 (hn₁_eq.trans hn₂_eq.symm))
    · rw [hn₁_eq] at hu₁_bp₁ hu₂_not_bp₁
      rw [hn₂_eq] at hu₂_bp₂ hu₁_not_bp₂
      exact borderPlus_nonempty_of_two_ends_in_other_cell π E hne_j
        hu₁_bp₁ hu₁_not_bp₂ hu₂_bp₂ hu₂_not_bp₁ hu₁_c hu₂_c hu₁_c' hu₂_c' i
    · rw [hn₁_eq] at hu₁_bp₁ hu₂_not_bp₁
      rw [hn₂_eq] at hu₂_bp₂ hu₁_not_bp₂
      rw [Set.pair_comm]
      exact borderPlus_nonempty_of_two_ends_in_other_cell π E hne_j
        hu₂_bp₂ hu₂_not_bp₁ hu₁_bp₁ hu₁_not_bp₂ hu₂_c hu₁_c hu₂_c' hu₁_c' i
    · exact False.elim (hne12 (hn₁_eq.trans hn₂_eq.symm))
  have hX_sub : ({u₁, u₂} : Set α) ⊆ (G.deleteEdges {e}).vertexSet := by
    rintro x (rfl | rfl)
    · exact (π.cellGraph_le (E.cell j₀) hc).vertexSet_subset hu₁_c
    · exact (π.cellGraph_le (E.cell j₀) hc).vertexSet_subset hu₂_c
  have hX_card : 3 * ({u₁, u₂} : Set α).ncard ≤ 6 := by
    rw [ncard_pair hu₁_ne_u₂]
  have hp_pos : 1 ≤ p :=
    (theorem_5_1_proof π hcentral (hred6.isZeroRedundant h𝒯) hΘ).trans
      ((π.warpAt_le_warp hΘ).trans hwarp)
  exact theorem_6_6_proof h𝒯 π hcentral hwarp hred6 (by omega) hΘ
    hX_sub hX_card hclaim1

private theorem exists_path_not_in_original_cell
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {e : β}
    (he : e ∈ G.edgeSet)
    (π : Portrayal (G.deleteEdges {e}))
    {c : Set π.S}
    (hc : c ∈ π.Γ.C)
    (hends : G.ends e ⊆ (π.cellGraph c).vertexSet) :
    let q₀ : ℕ := π.cellWarp c
    ∀ (n₁ : π.S),
    ∀ (n₂ : π.S),
    ((π.borderSet n₁).ncard ≤ π.cellWarp c ∧ (π.borderSet n₂).ncard ≤ π.cellWarp c ∧
      ((π.borderPlus n₁).ncard = π.cellWarp c + 1 → (π.borderPlus n₂).ncard = π.cellWarp c + 1 →
      Portrayal.LinkagePairs (π.cellGraph c).skeleton (π.borderPlus n₁) (π.borderPlus n₂)
      (π.cellWarp c + 1) (π.nodeVertex n₁) (π.nodeVertex n₂))) →
    ((π.borderPlus n₁).ncard = q₀ + 1) →
    ((π.borderPlus n₂).ncard = q₀ + 1) →
    ∀ (P : Fin (q₀ + 1) → PathFromTo ((addEdgePortrayal π hc he hends).cellGraph c).skeleton
      (π.borderPlus n₁) (π.borderPlus n₂)),
    (Pairwise fun i j => Disjoint {z | z ∈ (P i).walk.support} {z | z ∈ (P
      j).walk.support}) →
    (¬∃ i, (P i).first = π.nodeVertex n₁ ∧ (P i).last = π.nodeVertex n₂) →
    ∃ i₀ : Fin (q₀ + 1), ¬∃ w₀ : (π.cellGraph c).skeleton.Walk (P i₀).first (P i₀).last,
      w₀.support = (P i₀).walk.support := by
  intro q₀ n₁ n₂ hspec hb₁ hb₂ P hP hnot_pair
  by_contra! hall_walk
  choose w₀ hw₀_sup using hall_walk
  let P₀ : Fin (q₀ + 1) →
      PathFromTo (π.cellGraph c).skeleton (π.borderPlus n₁) (π.borderPlus n₂) := fun i =>
    { first := (P i).first
      last := (P i).last
      walk := w₀ i
      isPath := by
        rw [SimpleGraph.Walk.isPath_def, hw₀_sup i]
        exact (P i).isPath.support_nodup
      first_mem := (P i).first_mem
      last_mem := (P i).last_mem }
  have hP₀_disj : Pairwise fun i j =>
      Disjoint {z | z ∈ (P₀ i).walk.support} {z | z ∈ (P₀ j).walk.support} := by
    intro i j hij
    dsimp [P₀]
    rw [hw₀_sup i, hw₀_sup j]
    exact hP hij
  exact hnot_pair (hspec.2.2 hb₁ hb₂ P₀ hP₀_disj)

/-- The heart of (12.3): adding `e` to the cell `c` does not raise the warp of `c`. The paper's step
"Consequently `c` borders `Θ`" (page 199) uses that `β(n)` misses the image of `γ` for each border
node `n`, which is (9.7) when `π` is true. We take this as a condition, since (12.4) also uses this
result for a portrayal made by (7.2), which need not be true. -/
theorem addEdgePortrayal_cellWarp {α : Type u} {β : Type v} {G : Hypergraph α β} {e : β}
    (he : e ∈ G.edgeSet) (hK : IsClique (G.deleteEdges {e}) (G.ends e))
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle (G.deleteEdges {e}) θ 𝒯) (hθ : 2 * p + 8 < θ)
    (π : Portrayal (G.deleteEdges {e})) (hcentral : π.IsCentral 𝒯)
    (hred6 : π.IsRedundant 𝒯 θ 6) (hwarp : π.warp ≤ p)
    (hdisj : ∀ n ∈ π.Γ.N ∩ bd π.S, Disjoint (π.borderSet n) (π.nodeVertex '' π.domγ))
    {c : Set π.S} (hc : c ∈ π.Γ.C) (hends : G.ends e ⊆ (π.cellGraph c).vertexSet)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hcΘ : (c ∩ Θ).Nonempty) :
    (addEdgePortrayal π hc he hends).cellWarp c = π.cellWarp c := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
  have hsk_le : (π.cellGraph c).skeleton ≤ ((addEdgePortrayal π hc he hends).cellGraph c).skeleton
    := by
    intro u v ⟨hne, f, hfu, hfv⟩
    refine ⟨hne, f, ?_, ?_⟩ <;>
    · dsimp only [addEdgePortrayal, addEdgeCell]
      rw [ite_eq_left rfl]
      exact Or.inl ‹_›
  have hform : ∀ r, (addEdgePortrayal π hc he hends).CellWarpLE c r ↔ ∀ n₁ ∈ tilde c, ∀ n₂ ∈ tilde
    c, n₁ ≠ n₂ →
      (π.borderSet n₁).ncard ≤ r ∧ (π.borderSet n₂).ncard ≤ r ∧
      ((π.borderPlus n₁).ncard = r + 1 → (π.borderPlus n₂).ncard = r + 1 →
        Portrayal.LinkagePairs ((addEdgePortrayal π hc he hends).cellGraph c).skeleton
          (π.borderPlus n₁)
          (π.borderPlus n₂) (r + 1) (π.nodeVertex n₁) (π.nodeVertex n₂)) := fun _ => Iff.rfl
  have hle_iff : ∀ r : ℕ, (addEdgePortrayal π hc he hends).CellWarpLE c r → π.CellWarpLE c r := by
    intro r h
    rw [hform] at h
    intro n₁ hn₁ n₂ hn₂ hne
    obtain ⟨h1, h2, h3⟩ := h n₁ hn₁ n₂ hn₂ hne
    refine ⟨h1, h2, fun hb₁ hb₂ P hP => ?_⟩
    let P' : Fin (r + 1) →
        PathFromTo ((addEdgePortrayal π hc he hends).cellGraph c).skeleton
          ((addEdgePortrayal π hc he hends).borderPlus n₁) ((addEdgePortrayal π hc he
            hends).borderPlus n₂) := fun i =>
      { first := (P i).first
        last := (P i).last
        walk := (P i).walk.map (SimpleGraph.Hom.ofLE hsk_le)
        isPath := by
          rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_map]
          exact (P i).isPath.support_nodup.map (fun _ _ h => h)
        first_mem := (P i).first_mem
        last_mem := (P i).last_mem }
    have hP' : Pairwise fun i j =>
        Disjoint {z | z ∈ (P' i).walk.support} {z | z ∈ (P' j).walk.support} := by
      intro i j hij
      dsimp [P']
      rw [SimpleGraph.Walk.support_map, SimpleGraph.Walk.support_map,
        show (⇑(SimpleGraph.Hom.ofLE hsk_le) : α → α) = id from rfl]
      simp only [List.map_id]
      exact hP hij
    exact h3 hb₁ hb₂ P' hP'
  set q₀ := π.cellWarp c
  set q := π.warpAt Θ
  have hq₀_le_q : q₀ ≤ q := π.cellWarp_le_warpAt hc hcΘ
  obtain ⟨u₀, v₀, hne_uv₀, htilde_c, _, _, hu₀_mem, hv₀_mem⟩ :=
    π.Γ.border_cell_exists_ends hc hbd_c
  have hex_le : ∃ r, (addEdgePortrayal π hc he hends).CellWarpLE c r := by
    refine ⟨(π.borderSet u₀).ncard + (π.borderSet v₀).ncard + 1,
      (hform _).2 fun n₁ hn₁ n₂ hn₂ _ => ?_⟩
    have hn₁' : n₁ ∈ ({u₀, v₀} : Set π.S) := htilde_c ▸ hn₁
    have hn₂' : n₂ ∈ ({u₀, v₀} : Set π.S) := htilde_c ▸ hn₂
    have hb₁_le : (π.borderSet n₁).ncard ≤ (π.borderSet u₀).ncard + (π.borderSet v₀).ncard := by
      rcases hn₁' with rfl | rfl <;> omega
    have hb₂_le : (π.borderSet n₂).ncard ≤ (π.borderSet u₀).ncard + (π.borderSet v₀).ncard := by
      rcases hn₂' with rfl | rfl <;> omega
    refine ⟨by omega, by omega, fun hcard₁ _ => ?_⟩
    exfalso
    have hn₁_mem : n₁ ∈ π.Γ.N ∩ bd π.S := by rcases hn₁' with rfl | rfl <;> assumption
    have hbp_le := π.ncard_borderPlus_le hn₁_mem
    change (π.borderPlus n₁).ncard = _ at hcard₁
    omega
  have hwarpOrders : {r : ℕ | (addEdgePortrayal π hc he hends).CellWarpLE c r}.Nonempty := hex_le
  have hge : q₀ ≤ (addEdgePortrayal π hc he hends).cellWarp c :=
    Nat.sInf_le (hle_iff ((addEdgePortrayal π hc he hends).cellWarp c) (Nat.sInf_mem hwarpOrders))
  suffices hle_q₀ : (addEdgePortrayal π hc he hends).CellWarpLE c q₀ from
    le_antisymm (Nat.sInf_le hle_q₀) hge
  refine (hform _).2 ?_
  intro n₁ hn₁ n₂ hn₂ hne12
  have hspec := π.cellWarp_spec hc hbd_c n₁ hn₁ n₂ hn₂ hne12
  refine ⟨hspec.1, hspec.2.1, fun hb₁ hb₂ P hP => ?_⟩
  by_contra hnot_pair
  have hn₁' : n₁ ∈ ({u₀, v₀} : Set π.S) := htilde_c ▸ hn₁
  have hn₂' : n₂ ∈ ({u₀, v₀} : Set π.S) := htilde_c ▸ hn₂
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := by rcases hn₁' with rfl | rfl <;> assumption
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S := by rcases hn₂' with rfl | rfl <;> assumption
  -- Since `π.CellWarpLE c q₀` holds, some path `P i₀` is not a walk in `(π.cellGraph c).skeleton`
  have hex_not_walk : ∃ i₀ : Fin (q₀ + 1),
      ¬ ∃ w₀ : (π.cellGraph c).skeleton.Walk (P i₀).first (P i₀).last,
        w₀.support = (P i₀).walk.support := by
    exact exists_path_not_in_original_cell (α := α) (β := β) (G := G) (e := e) he π (c := c) hc
      hends  n₁ n₂ hspec hb₁ hb₂ P hP hnot_pair
  obtain ⟨i₀, hi₀_not⟩ := hex_not_walk
  obtain ⟨v₁, hv₁_sup, v₂, hv₂_sup, hadj', hnot_adj⟩ :=
    exists_adj_not_adj_of_not_walk (P i₀).walk hi₀_not
  have hv_ends : v₁ ≠ v₂ ∧ v₁ ∈ G.ends e ∧ v₂ ∈ G.ends e := by
    rcases hadj' with ⟨hne_v, f, hfv₁, hfv₂⟩
    have hno : ∀ {g : β} {v : α}, (π.cellGraph c).Inc g v → g ≠ e := fun h hg =>
      ((π.cellGraph_le c hc).edgeSet_subset ((π.cellGraph c).edge_mem_of_inc h)).2
        (mem_singleton_iff.2 hg)
    dsimp only [addEdgePortrayal, addEdgeCell] at hfv₁ hfv₂
    rw [ite_eq_left rfl] at hfv₁ hfv₂
    rcases hfv₁ with hfv₁ | ⟨hfe, hfv₁⟩
    · rcases hfv₂ with hfv₂ | ⟨hfe, _⟩
      · exact False.elim (hnot_adj ⟨hne_v, f, hfv₁, hfv₂⟩)
      · exact False.elim (hno hfv₁ hfe)
    · rcases hfv₂ with hfv₂ | ⟨_, hfv₂⟩
      · exact False.elim (hno hfv₂ hfe)
      · exact ⟨hne_v, hfe ▸ hfv₁, hfe ▸ hfv₂⟩
  obtain ⟨hne_v, hv₁_e, hv₂_e⟩ := hv_ends
  have hv₁_c : v₁ ∈ (π.cellGraph c).vertexSet := hends hv₁_e
  have hv₂_c : v₂ ∈ (π.cellGraph c).vertexSet := hends hv₂_e
  obtain ⟨_, f', hf'₁, hf'₂⟩ := hK.2 v₁ hv₁_e v₂ hv₂_e hne_v
  obtain ⟨c', hc', hf'c'⟩ := π.p1_edge f' ((G.deleteEdges {e}).edge_mem_of_inc hf'₁)
  have hv₁_c' : v₁ ∈ (π.cellGraph c').vertexSet :=
    (π.cellGraph c').vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le c' hc') hf'c').mpr hf'₁)
  have hv₂_c' : v₂ ∈ (π.cellGraph c').vertexSet :=
    (π.cellGraph c').vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le c' hc') hf'c').mpr hf'₂)
  have hne_c' : c' ≠ c := by
    intro h
    rw [h] at hf'c'
    exact hnot_adj ⟨hne_v, f',
      (inc_iff_of_le (π.cellGraph_le c hc) hf'c').mpr hf'₁,
      (inc_iff_of_le (π.cellGraph_le c hc) hf'c').mpr hf'₂⟩
  have htilde_pair : tilde c = {n₁, n₂} := by
    have hsub_pair : ({n₁, n₂} : Set π.S) ⊆ tilde c := by
      rintro x (rfl | rfl) <;> assumption
    exact (eq_of_subset_of_ncard_le hsub_pair
      (by rw [ncard_pair hne12, (π.Γ.border_cell c hc hbd_c).1])
      (π.Γ.finite_tilde_cell hc)).symm
  have hv₁_bp12 : v₁ ∈ π.borderPlus n₁ ∪ π.borderPlus n₂ := by
    obtain ⟨n, hnt, hbp⟩ := π.p6 c hc hbd_c v₁ hv₁_c ⟨c', hc', hne_c', hv₁_c'⟩
    rcases (htilde_pair ▸ hnt : n ∈ ({n₁, n₂} : Set π.S)) with rfl | rfl
    · exact Or.inl hbp
    · exact Or.inr hbp
  have hv₂_bp12 : v₂ ∈ π.borderPlus n₁ ∪ π.borderPlus n₂ := by
    obtain ⟨n, hnt, hbp⟩ := π.p6 c hc hbd_c v₂ hv₂_c ⟨c', hc', hne_c', hv₂_c'⟩
    rcases (htilde_pair ▸ hnt : n ∈ ({n₁, n₂} : Set π.S)) with rfl | rfl
    · exact Or.inl hbp
    · exact Or.inr hbp
  have hbp₁_fin : (π.borderPlus n₁).Finite := π.borderPlus_finite hn₁_bd
  have hbp₂_fin : (π.borderPlus n₂).Finite := π.borderPlus_finite hn₂_bd
  have hv₁_end : v₁ = (P i₀).first ∨ v₁ = (P i₀).last := by
    rcases hv₁_bp12 with h1 | h2
    · exact Or.inl (eq_first_of_mem_support_of_linkage hbp₁_fin hb₁ P hP hv₁_sup h1)
    · exact Or.inr (eq_last_of_mem_support_of_linkage hbp₂_fin hb₂ P hP hv₁_sup h2)
  have hv₂_end : v₂ = (P i₀).first ∨ v₂ = (P i₀).last := by
    rcases hv₂_bp12 with h1 | h2
    · exact Or.inl (eq_first_of_mem_support_of_linkage hbp₁_fin hb₁ P hP hv₂_sup h1)
    · exact Or.inr (eq_last_of_mem_support_of_linkage hbp₂_fin hb₂ P hP hv₂_sup h2)
  set u₁ := (P i₀).first
  set u₂ := (P i₀).last
  have hu₁_ne_u₂ : u₁ ≠ u₂ := by
    rcases hv₁_end with h1 | h1 <;> rcases hv₂_end with h2 | h2
    · exact False.elim (hne_v (h1.trans h2.symm))
    · exact h1 ▸ h2 ▸ hne_v
    · exact h1 ▸ h2 ▸ hne_v.symm
    · exact False.elim (hne_v (h1.trans h2.symm))
  have hu_pair : ({u₁, u₂} : Set α) = {v₁, v₂} := by
    rcases hv₁_end with h1 | h1 <;> rcases hv₂_end with h2 | h2
    · exact False.elim (hne_v (h1.trans h2.symm))
    · rw [h1, h2]
    · rw [h1, h2, Set.pair_comm]
    · exact False.elim (hne_v (h1.trans h2.symm))
  have hu₁_bp₁ : u₁ ∈ π.borderPlus n₁ := (P i₀).first_mem
  have hu₂_bp₂ : u₂ ∈ π.borderPlus n₂ := (P i₀).last_mem
  have hu₁_not_bp₂ : u₁ ∉ π.borderPlus n₂ := fun h =>
    hu₁_ne_u₂ (eq_last_of_mem_support_of_linkage hbp₂_fin hb₂ P hP
      (SimpleGraph.Walk.start_mem_support _) h)
  have hu₂_not_bp₁ : u₂ ∉ π.borderPlus n₁ := fun h =>
    hu₁_ne_u₂.symm (eq_first_of_mem_support_of_linkage hbp₁_fin hb₁ P hP
      (SimpleGraph.Walk.end_mem_support _) h)
  have hu₁_c : u₁ ∈ (π.cellGraph c).vertexSet := by
    have : u₁ ∈ ({v₁, v₂} : Set α) := hu_pair ▸ mem_insert _ _
    rcases this with rfl | rfl <;> assumption
  have hu₂_c : u₂ ∈ (π.cellGraph c).vertexSet := by
    have : u₂ ∈ ({v₁, v₂} : Set α) := hu_pair ▸ mem_insert_of_mem _ (mem_singleton _)
    rcases this with rfl | rfl <;> assumption
  have hu₁_c' : u₁ ∈ (π.cellGraph c').vertexSet := by
    have : u₁ ∈ ({v₁, v₂} : Set α) := hu_pair ▸ mem_insert _ _
    rcases this with rfl | rfl <;> assumption
  have hu₂_c' : u₂ ∈ (π.cellGraph c').vertexSet := by
    have : u₂ ∈ ({v₁, v₂} : Set α) := hu_pair ▸ mem_insert_of_mem _ (mem_singleton _)
    rcases this with rfl | rfl <;> assumption
  -- At least one of `u₁ ∈ π.borderSet n₁` or `u₂ ∈ π.borderSet n₂` holds
  have hex_bs : u₁ ∈ π.borderSet n₁ ∨ u₂ ∈ π.borderSet n₂ := by
    rcases hu₁_bp₁ with h1 | ⟨_, hEq1⟩
    · exact Or.inl h1
    · rcases hu₂_bp₂ with h2 | ⟨_, hEq2⟩
      · exact Or.inr h2
      · exact False.elim (hnot_pair ⟨i₀, hEq1, hEq2⟩)
  -- Deduce `c'` is a border cell bordering `Θ`
  exact false_of_adjacent_cell_border_paths (G := G) (e := e) h𝒯 hθ π hcentral hred6 hwarp hdisj
    hc hc' hne_c' hΘ hcΘ hn₁ hn₂ hne12 hn₁_bd hn₂_bd hu₁_ne_u₂ hu₁_bp₁ hu₂_bp₂
    hu₁_not_bp₂ hu₂_not_bp₁ hu₁_c hu₂_c hu₁_c' hu₂_c' hex_bs

theorem addEdgePortrayal_central_resembles
    {α : Type u} {β : Type v} {G : Hypergraph α β} {e : β} (he : e ∈ G.edgeSet)
    (hK : IsClique (G.deleteEdges {e}) (G.ends e))
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle (G.deleteEdges {e}) θ 𝒯) (hθ : 2 * p + 8 < θ)
    (π : Portrayal (G.deleteEdges {e})) (hcentral : π.IsCentral 𝒯)
    (hred : π.IsRedundant 𝒯 θ 6) (hwarp : π.warp ≤ p)
    (hdisj : ∀ n ∈ π.Γ.N ∩ bd π.S, Disjoint (π.borderSet n) (π.nodeVertex '' π.domγ))
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hends : G.ends e ⊆ (π.cellGraph c₀).vertexSet) :
    (addEdgePortrayal π hc₀ he hends).IsCentral (inducedSubhypergraphTangle G
      (G.deleteEdges {e}) 𝒯 θ) ∧
      (addEdgePortrayal π hc₀ he hends).Resembles π := by
  classical
  refine ⟨addEdgePortrayal_central he h𝒯 (by omega) π hcentral hwarp hc₀ hends,
    Homeomorph.refl π.S, fun Θ hΘ => ?_⟩
  refine Eq.trans ?_ (congrArg π.warpAt (image_id Θ).symm)
  have hcellWarp_eq : ∀ c ∈ π.Γ.C, (c ∩ Θ).Nonempty →
      (addEdgePortrayal π hc₀ he hends).cellWarp c = π.cellWarp c := by
    intro c hc hcΘ
    by_cases hcc₀ : c = c₀
    · subst hcc₀
      exact addEdgePortrayal_cellWarp he hK h𝒯 hθ π hcentral hred hwarp hdisj hc hends hΘ hcΘ
    · have hcellG_c : (addEdgePortrayal π hc₀ he hends).cellGraph c = π.cellGraph c
        := ite_eq_right hcc₀
      unfold Portrayal.cellWarp Portrayal.CellWarpLE
      rw [hcellG_c]
      rfl
  change sSup {r : ℕ | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ r = (addEdgePortrayal π hc₀ he
    hends).cellWarp c} =
    sSup {r : ℕ | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ r = π.cellWarp c}
  congr 1
  ext r
  exact ⟨fun ⟨c, hc, hcΘ, hr⟩ => ⟨c, hc, hcΘ, hr.trans (hcellWarp_eq c hc hcΘ)⟩,
    fun ⟨c, hc, hcΘ, hr⟩ => ⟨c, hc, hcΘ, hr.trans (hcellWarp_eq c hc hcΘ).symm⟩⟩

/-- **Graph Minors XVII, (12.3)** (page 199): "Let $e$ be an edge of a hypergraph $G$, and let $K$
be the set of ends of $e$. Let $K$ be a clique of $G \setminus e$. Let $\mathscr{T}$ be a tangle in
$G \setminus e$ of order $> 2p+8$, inducing a tangle $\mathscr{T}'$ in $G$. Let $\pi = (\Sigma,
\Gamma, \alpha, \beta, \gamma)$ be a 6-redundant, $\mathscr{T}$-central portrayal of $G \setminus
e$ with warp $\le p$. Let $c_0 \in C(\Gamma)$ with $K \subseteq V(\alpha(c_0))$. Define $\alpha'$
by $$\begin{aligned} \alpha'(c_0) &= (V(\alpha(c_0)), E(\alpha(c_0)) \cup \{e\}) \\ \alpha'(c) &=
\alpha(c) \qquad (c \in C(\Gamma) - \{c_0\}). \end{aligned}$$ Then $\pi' = (\Sigma, \Gamma,
\alpha', \beta, \gamma)$ is a $\mathscr{T}'$-central portrayal of $G$, resembling $\pi$." Here `π'`
is `addEdgePortrayal`.

The step "Consequently $c$ borders $\Theta$" of the paper's proof needs the conclusion of (9.7) (no
vertex of $\beta(n)$ is $\gamma$ of a node), which the paper does not cite there; (9.7) is proved
for true, $(2p+3)$-redundant portrayals with $\operatorname{ord}(\mathscr{T}) > 4p+5$. So here $\pi$
is assumed true and $\max(6, 2p+3)$-redundant with $\theta > \max(2p+8, 4p+5)$.
`addEdgePortrayal_central_resembles` has the printed hypotheses plus the conclusion of (9.7). -/
theorem theorem_12_3_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β} {e : β} (he : e ∈ G.edgeSet)
    (hK : IsClique (G.deleteEdges {e}) (G.ends e))
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle (G.deleteEdges {e}) θ 𝒯) (hθ : max (2 * p + 8) (4 * p + 5) < θ)
    (π : Portrayal (G.deleteEdges {e})) (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (max 6 (2 * p + 3))) (hwarp : π.warp ≤ p)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hends : G.ends e ⊆ (π.cellGraph c₀).vertexSet) :
    (addEdgePortrayal π hc₀ he hends).IsCentral (inducedSubhypergraphTangle G
      (G.deleteEdges {e}) 𝒯 θ) ∧
      (addEdgePortrayal π hc₀ he hends).Resembles π :=
  addEdgePortrayal_central_resembles he hK h𝒯 (by omega) π htrue.1 (hred.mono (by omega)) hwarp
    (fun n hn => (theorem_9_7_proof h𝒯 π htrue
      (hred.mono (by omega)) hwarp (by omega) hn).mono_right (image_mono π.domγ_subset)) hc₀ hends

end GraphMinor.GM17
