/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.VortexCells

/-!
# The axioms of the portrayal in XVII (13.1)

Fourth step of the proof of XVII (13.1), pages 203-204. We define `nv`, the vertex of a node, and
`bt`, the set `β(n)`. Then we prove (P2)-(P7) for the cells of `VortexCells`,
as statements on the index set `Idx`.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface GM09 GM14 GM16 Graph

universe u v

variable {α : Type u} [Nonempty α] {β : Type v} {S : Type} [TopologicalSpace S] [T2Space S] {G :
  Graph α β} {Seg : Set (Society α β)} {D : Society α β → Set S} {ν : α → S} {ρ : ℕ}
  {V : ∀ m : Maj Seg, VortexCut m.1 (D m.1) ν ρ}

/-- The vertex of a node. -/
noncomputable def nv (Seg : Set (Society α β)) (ν : α → S) (x : S) : α := Function.invFunOn ν
  (segregationVertices Seg) x

/-- The set `β(n)`: for the node of `t i` with `i` not first, the vertices shared by `X (i - 1)` and
`X i`, other than `t i`. -/
def bt (V : ∀ m : Maj Seg, VortexCut m.1 (D m.1) ν ρ) (x : S) : Set α :=
  {v | ∃ (m : Maj Seg) (i j : Fin (V m).k), x = ν ((V m).t i) ∧ j.1 + 1 = i.1 ∧ v ∈ V((V m).X j)
    ∧ v ∈ V((V m).X i) ∧ v ≠ (V m).t i}

omit [T2Space S] in
theorem nv_eq (harr : IsProperArrangement Seg D ν) {v : α} (hv : v ∈ segregationVertices Seg) : nv
  Seg ν (ν v) = v :=
  harr.1.injOn_pts.leftInvOn_invFunOn hv

variable (harr : IsProperArrangement Seg D ν)
include harr

omit [T2Space S] in
theorem nv_t (m : Maj Seg) (i : Fin (V m).k) : nv Seg ν (ν ((V m).t i)) = (V m).t i :=
  nv_eq harr (bar_sub_verts m.2.1 (t_mem_bar m i))

omit [Nonempty α] in
theorem node_unique {m m' : Maj Seg} {i : Fin (V m).k} {i' : Fin (V m').k} (h : ν ((V m).t i) = ν
  ((V m').t i')) : (⟨m, i⟩ : Σ m : Maj Seg, Fin (V m).k) = ⟨m', i'⟩ := by
  have h1 : m = m' := by
    by_contra hne
    have h2 := pt_mem_disc harr m.2.1 (t_mem_bar (V := V) m i)
    have h3 := pt_mem_disc harr m'.2.1 (t_mem_bar (V := V) m' i')
    rw [← h] at h3
    exact Set.disjoint_left.mp (disjoint_disc harr hne) h2 h3
  subst h1
  have h2 := harr.1.injOn_pts (bar_sub_verts m.2.1 (t_mem_bar m i)) (bar_sub_verts m.2.1
    (t_mem_bar m i')) h
  rw [(V m).dec.injective_t h2]

theorem nv_mem_gr (i : Idx V) {n : S} (hn : n ∈ Nd Seg ν ∩ Ds V i) : nv Seg ν n ∈
  (gr V i).vertexSet := by
  rcases i with a | ⟨m, a⟩
  · have h : n ∈ Nd Seg ν ∩ D a.1 := hn
    rw [Nd_inter_inl harr] at h
    obtain ⟨v, hv, rfl⟩ := h
    rw [nv_eq harr (bar_sub_verts a.2.1 hv)]
    exact a.1.bar_subset hv
  · have h : n ∈ Nd Seg ν ∩ (V m).L a := hn
    rw [Nd_inter_inr harr] at h
    rcases h with rfl | rfl
    · rw [nv_t harr]
      exact Or.inl ((V m).dec.mem_vertexSet a)
    · rw [nv_t harr]
      exact Or.inr rfl

omit [Nonempty α] in
/-- (P3), second part. -/
theorem bt_sub_gr {m : Maj Seg} {a : Fin (V m).k} {n : S} (hn : n ∈ Nd Seg ν ∩
  (V m).L a) : bt V n ⊆ (gr V (.inr ⟨m, a⟩)).vertexSet := by
  rw [Nd_inter_inr harr] at hn
  rintro v ⟨m', i, j, h1, h2, h3, h4, h5⟩
  have hle : (V m).k = (V m).k := rfl
  rcases hn with rfl | rfl
  · obtain ⟨rfl, hi⟩ := Sigma.mk.inj_iff.mp (node_unique harr h1)
    obtain rfl := eq_of_heq hi
    exact Or.inl h4
  · obtain ⟨rfl, hi⟩ := Sigma.mk.inj_iff.mp (node_unique harr h1)
    obtain rfl := eq_of_heq hi
    have h6 := (V m).hnx a
    have h7 := a.2
    by_cases hc : a.1 + 1 < (V m).k
    · rw [Nat.mod_eq_of_lt hc] at h6
      have : j = a := Fin.ext (by omega)
      subst this
      exact Or.inl h3
    · have : a.1 + 1 = (V m).k := by omega
      rw [this, Nat.mod_self] at h6
      omega

omit [T2Space S] in
/-- (P3), first part. -/
theorem nv_notMem_bt {n : S} (_ : n ∈ Nd Seg ν) : nv Seg ν n ∉ bt V n := by
  rintro ⟨m, i, j, h1, -, -, -, h5⟩
  apply h5
  rw [h1, nv_t harr]

omit [Nonempty α] [T2Space S] harr in
theorem bt_mem_graph {n : S} {v : α} (hv : v ∈ bt V n) : ∃ (m : Maj Seg) (i : Fin (V m).k), n = ν
  ((V m).t i) ∧ v ∈ V(m.1.G) := by
  obtain ⟨m, i, j, h1, -, -, h4, -⟩ := hv
  exact ⟨m, i, h1, ((V m).dec.le_G i).vertexSet_mono h4⟩

variable (hseg : IsGraphSegregation G Seg)
include hseg

omit [Nonempty α] in
/-- (P4), first part. -/
theorem bt_disjoint {m₁ m₂ : Maj Seg} (hm : m₁ ≠ m₂) {n₁ n₂ : S} (h₁ : n₁ ∈ D m₁.1)
  (h₂ : n₂ ∈ D m₂.1) : Disjoint (bt V n₁) (bt V n₂) := by
  refine Set.disjoint_left.mpr fun v hv hv' => ?_
  obtain ⟨m, i, rfl, hg⟩ := bt_mem_graph hv
  obtain ⟨m', i', rfl, hg'⟩ := bt_mem_graph hv'
  have e1 : m = m₁ := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_disc harr hne) (pt_mem_disc harr m.2.1 (t_mem_bar (V
      := V) m i)) h₁
  have e2 : m' = m₂ := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_disc harr hne) (pt_mem_disc harr m'.2.1 (t_mem_bar (V
      := V) m' i')) h₂
  subst e1 e2
  have hne : m.1 ≠ m'.1 := fun h => hm (Subtype.ext h)
  obtain ⟨h3, h4⟩ := hseg.vertex_inter_subset _ m.2.1 _ m'.2.1 hne ⟨hg, hg'⟩
  exact Set.disjoint_left.mp (disjoint_disc harr hm) (pt_mem_disc harr m.2.1 h3)
    (pt_mem_disc harr m'.2.1 h4)

/-- (P4), second part. -/
theorem nv_notMem_bt_of_off {m : Maj Seg} {n₁ n₂ : S} (h₁ : n₁ ∈ D m.1) (h₂ : n₂ ∈ Nd Seg ν)
  (hoff : n₂ ∉ discBd (V m).P) : nv Seg ν n₂ ∉ bt V n₁ := by
  intro hv
  obtain ⟨m', i, rfl, hg⟩ := bt_mem_graph hv
  have e1 : m' = m := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_disc harr hne) (pt_mem_disc harr m'.2.1 (t_mem_bar (V
      := V) m' i)) h₁
  subst e1
  obtain ⟨w, hw, rfl⟩ := h₂
  rw [nv_eq harr hw] at hg
  obtain ⟨j, rfl⟩ := exists_t_eq (V := V) (mem_bar_of_mem_graph hseg m'.2.1 hw hg)
  exact hoff (pt_mem_discBd_P m' j)

/-- (P5). -/
theorem p5_aux (a : Mnr Seg) {v : α} (hv : v ∈ (gr V (.inl a)).vertexSet) {j : Idx V}
  (hj : j ≠ .inl a) (hvj : v ∈ (gr V j).vertexSet) :
    ν v ∈ Nd Seg ν ∩ D a.1 ∧ nv Seg ν (ν v) = v := by
  have hne : soc V (.inl a) ≠ soc V j := by
    rcases j with b | ⟨m, b⟩
    · exact fun h => hj (congrArg Sum.inl (Subtype.ext h)).symm
    · exact soc_ne_of_mnr_maj a m
  have h := mem_bar_of_ne hseg hne hv hvj
  exact ⟨⟨pt_mem_Nd a.2.1 h, pt_mem_disc harr a.2.1 h⟩, nv_eq harr (bar_sub_verts a.2.1 h)⟩

/-- (P6). -/
theorem p6_aux {m : Maj Seg} {a : Fin (V m).k} {v : α} (hv : v ∈ (gr V
  (.inr ⟨m, a⟩)).vertexSet) {j : Idx V} (hj : j ≠ .inr ⟨m, a⟩) (hvj : v ∈ (gr V j).vertexSet) :
    ∃ n ∈ Nd Seg ν ∩ (V m).L a, v ∈ bt V n ∨ (n ∈ Nd Seg ν ∧ v = nv Seg ν n) := by
  have hA : ν ((V m).t a) ∈ Nd Seg ν ∩ (V m).L a := by
    rw [Nd_inter_inr harr]
    exact Or.inl rfl
  have hB : ν ((V m).t ((V m).nx a)) ∈ Nd Seg ν ∩ (V m).L a := by
    rw [Nd_inter_inr harr]
    exact Or.inr rfl
  by_cases h1 : v = (V m).t ((V m).nx a)
  · exact ⟨_, hB, Or.inr ⟨hB.1, by rw [nv_t harr, h1]⟩⟩
  by_cases h2 : v = (V m).t a
  · exact ⟨_, hA, Or.inr ⟨hA.1, by rw [nv_t harr, h2]⟩⟩
  have hva : v ∈ V((V m).X a) := by
    rcases hv with h | h
    · exact h
    · exact absurd h h1
  have key : ∃ e, e ≠ a ∧ v ∈ V((V m).X e) := by
    have outer : soc V (.inr ⟨m, a⟩) ≠ soc V j → ∃ e, e ≠ a ∧ v ∈ V((V m).X e) := fun hne => by
      obtain ⟨e, rfl⟩ := exists_t_eq (V := V) (mem_bar_of_ne hseg hne hv hvj)
      exact ⟨e, fun he => h2 (by rw [he]), (V m).dec.mem_vertexSet e⟩
    by_cases hso : soc V (.inr ⟨m, a⟩) = soc V j
    · rcases j with b | ⟨m', b⟩
      · exact absurd hso.symm (soc_ne_of_mnr_maj b m)
      · obtain rfl : m = m' := Subtype.ext hso
        have hab : b ≠ a := fun h => hj (h ▸ rfl)
        rcases hvj with h | h
        · exact ⟨b, hab, h⟩
        · have h' : v = (V m).t ((V m).nx b) := h
          exact ⟨(V m).nx b, fun he => h2 (by rw [h', he]), h' ▸ (V m).dec.mem_vertexSet _⟩
    · exact outer hso
  obtain ⟨e, hne, hve⟩ := key
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h0 : a.1 ≠ 0 := by
      have : e.1 < a.1 :=
        hlt
      omega
    let j₀ : Fin (V m).k := ⟨a.1 - 1, by omega⟩
    have hj₀ : v ∈ V((V m).X j₀) := (V m).mem_between (a := e) (c := a)
      (Fin.le_def.mpr (by have : e.1 < a.1 := hlt; simp only [j₀]; omega))
      (Fin.le_def.mpr (by simp only [j₀]; omega)) hve hva
    exact ⟨_, hA, Or.inl ⟨m, a, j₀, rfl, by simp only [j₀]; omega, hj₀, hva, h2⟩⟩
  · have hc : a.1 + 1 < (V m).k := by
      have : a.1 < e.1 := hlt
      have := e.2
      omega
    have hnxe : ((V m).nx a).1 = a.1 + 1 := by
      rw [(V m).hnx, Nat.mod_eq_of_lt hc]
    have hvn : v ∈ V((V m).X ((V m).nx a)) := (V m).mem_between (a := a) (c := e)
      (Fin.le_def.mpr (by omega)) (Fin.le_def.mpr (by have : a.1 < e.1 := hlt; omega)) hva hve
    exact ⟨_, hB, Or.inl ⟨m, (V m).nx a, a, rfl, hnxe.symm, hva, hvn, h1⟩⟩

omit hseg in
omit [Nonempty α] in
theorem ncard_bt_le (n : S) : (bt V n).ncard ≤ ρ := by
  by_cases he : (bt V n).Nonempty
  · obtain ⟨v₀, m, i, j, rfl, h2, -, -, -⟩ := he
    have hsub : bt V (ν ((V m).t i)) ⊆ V((V m).X j) ∩ V((V m).X i) := by
      rintro v ⟨m', i', j', h1, h3, h4, h5, -⟩
      obtain ⟨rfl, hi⟩ := Sigma.mk.inj_iff.mp (node_unique harr h1)
      obtain rfl := eq_of_heq hi
      have : j' = j := Fin.ext (by omega)
      subst this
      exact ⟨h4, h5⟩
    exact (Set.ncard_le_ncard hsub (((V m).finite_V j).subset inter_subset_left)).trans
      ((V m).small j i (Fin.lt_def.mpr (by omega)))
  · rw [not_nonempty_iff_eq_empty.mp he]
    simp

end GraphMinor.GM17
