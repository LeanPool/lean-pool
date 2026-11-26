/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10f
public import LeanPool.GraphMinor.GM20.Section9h

/-!
# Graph Minors XX, Section 10: the hull of a portrayal

We go on with the proof of (10.3). From a portrayal `π` with the properties that Graph Minors XVII
proves for true portrayals, we build the hypergraph `G'` with `V(G') = N(Γ) ∪ ⋃ β(n)` and with one
edge for each cell. It is a heart of `(G, ℒ)`, and `(Γ, β)` is a hull for it (`isHull`). The final
result `isShelled_of_portrayal` says that `(P, ℒ)` is shelled.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM18

universe u v

variable {α : Type u} {β : Type v}

/-- For a cuff `Θ`, each node `n` on `Θ` lies in `cTilde` for two different cells that meet `Θ`.
These are
the two cells of the cycle around `Θ` next to `n`. -/
theorem exists_two_cells {S : Type} [TopologicalSpace S] (hS : IsSurface S) (Γ : Painting S)
    {Θ : Set S} (hΘ : Θ ∈ cuffs S) {n : S} (hn : n ∈ Γ.N ∩ Θ) :
    ∃ c₁ ∈ Γ.C, ∃ c₂ ∈ Γ.C, c₁ ≠ c₂ ∧ n ∈ tilde c₁ ∧ n ∈ tilde c₂ ∧ (c₁ ∩ Θ).Nonempty ∧
      (c₂ ∩ Θ).Nonempty := by
  obtain ⟨-, -, harc⟩ := cuff_statement.{0} S hS
  obtain ⟨f⟩ := harc Θ hΘ
  obtain ⟨C⟩ := exists_cuffCycle Γ hΘ f
  obtain ⟨m, hm, rfl⟩ := C.exists_pos n hn
  have hk := C.two_le
  have hne : ∀ l, (C.cell l ∩ Θ).Nonempty := fun l ↦ by
    rw [C.cell_inter]
    exact (nonempty_Ioo.mpr (C.strictMono (Nat.lt_succ_self l))).image _
  have hl : m + C.k - 1 + 1 = m + C.k := by omega
  refine ⟨C.cell m, C.cell_mem m, C.cell (m + C.k - 1), C.cell_mem _,
    C.cell_ne m _ (by omega) (by omega), ?_, ?_, hne _, hne _⟩
  · rw [C.tilde_eq]
    exact Or.inl rfl
  · rw [C.tilde_eq, hl, C.T_add, cuffPoint_add]
    exact Or.inr rfl

/-- If `V` has at most three members and any two are joined by a path that has no other member of
`V`, then each grouping `K` with `V(K) = V` is realized in the subgraph `C` given by the paths for
the adjacent pairs of `K`. At most one component of `K` has two or more members, so a nonadjacent
pair has a member isolated in `K`, and no path meets that member. -/
theorem exists_realizing_subgraph {K₀ : SimpleGraph α} {V : Set α} (hfin : V.Finite)
    (h₃ : V.ncard ≤ 3)
    (hL : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → ∃ L : PathFromTo K₀ {x} {y},
      ∀ z ∈ L.walk.support, z ∈ V → z = x ∨ z = y)
    {K : (⊤ : SimpleGraph α).Subgraph} (hK : GM04.IsGrouping V K) (hverts : K.verts = V) :
    ∃ C : SimpleGraph α, C ≤ K₀ ∧ ∀ x ∈ V, ∀ y ∈ V, x ≠ y → (C.Reachable x y ↔ K.Adj x y) := by
  classical
  obtain ⟨-, htrans⟩ := GM04.isGrouping_iff.mp hK
  let good : α → α → α → α → Prop := fun x y u v ↦ K.Adj x y ∧ ∃ L : PathFromTo K₀ {x} {y},
    (∀ z ∈ L.walk.support, z ∈ V → z = x ∨ z = y) ∧ s(u, v) ∈ L.walk.edges
  let C : SimpleGraph α :=
    { Adj := fun u v ↦ ∃ x y, good x y u v
      symm := ⟨fun u v ⟨x, y, h, L, h₁, h₂⟩ ↦ ⟨x, y, h, L, h₁, Sym2.eq_swap ▸ h₂⟩⟩
      loopless := ⟨fun u ⟨_, _, _, L, _, h₂⟩ ↦ (L.walk.adj_of_mem_edges h₂).ne rfl⟩ }
  have hCle : C ≤ K₀ := fun u v ⟨_, _, _, L, _, h₂⟩ ↦ L.walk.adj_of_mem_edges h₂
  have hmemV : ∀ {x y}, K.Adj x y → x ∈ V ∧ y ∈ V := fun h ↦
    ⟨hverts ▸ K.edge_vert h, hverts ▸ K.edge_vert h.symm⟩
  have hiso : ∀ {u v}, u ∈ V → C.Adj u v → ∃ w, K.Adj u w := by
    rintro u v hu ⟨x, y, hxy, L, h₁, h₂⟩
    rcases h₁ u (L.walk.fst_mem_support_of_mem_edges h₂) hu with rfl | rfl
    · exact ⟨y, hxy⟩
    · exact ⟨x, hxy.symm⟩
  have hnotreach : ∀ {u v}, u ∈ V → u ≠ v → (¬ ∃ w, K.Adj u w) → ¬ C.Reachable u v := by
    rintro u v hu hne hno ⟨p⟩
    cases p with
    | nil => exact hne rfl
    | cons h _ => exact hno (hiso hu h)
  refine ⟨C, hCle, fun x hx y hy hxy ↦ ⟨fun hreach ↦ ?_, fun hadj ↦ ?_⟩⟩
  · by_contra hnadj
    have hxno : ∃ w, K.Adj x w := by
      by_contra h
      exact hnotreach hx hxy h hreach
    have hyno : ∃ w, K.Adj y w := by
      by_contra h
      exact hnotreach hy hxy.symm h hreach.symm
    obtain ⟨a, ha⟩ := hxno
    obtain ⟨b, hb⟩ := hyno
    have hax : a ≠ x := ha.ne.symm
    have hby : b ≠ y := hb.ne.symm
    have hay : a ≠ y := fun h ↦ hnadj (h ▸ ha)
    have hbx : b ≠ x := fun h ↦ hnadj (h ▸ hb.symm)
    have hab : a ≠ b := fun h ↦ hnadj (htrans x a y hxy ha (h ▸ hb.symm))
    have hsub : (({x, y, a, b} : Finset α) : Set α) ⊆ V := by
      intro z hz
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact (hmemV ha).2
      · exact (hmemV hb).2
    have hcard : ({x, y, a, b} : Finset α).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton] <;> simp [hxy, hab, hay.symm, hby.symm, hax.symm, hbx.symm]
    have hle := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, hcard] at hle
    omega
  · obtain ⟨L, hL'⟩ := hL x hx y hy hxy
    have hfirst : L.first = x := L.first_mem
    have hlast : L.last = y := L.last_mem
    have hC : ∀ e ∈ L.walk.edges, e ∈ C.edgeSet := by
      intro e he
      induction e with
      | _ u v => exact ⟨x, y, hadj, L, hL', he⟩
    have := (L.walk.transfer C hC).reachable
    rwa [hfirst, hlast] at this

end GraphMinor.GM20

namespace GraphMinor.GM17.Portrayal

open Set Topology GraphMinor.Surface GraphMinor.GM18 GraphMinor.GM20

universe u v

variable {α : Type u} {β : Type v}

/-- The graded surface `(Σ, ρ)` of a portrayal, with `ρ(Θ)` the warp of `π` at `Θ`. -/
noncomputable abbrev gradedOf {G : Hypergraph α β} (π : Portrayal G) : GradedSurface where
  S := π.S
  isSurface := π.isSurface
  connected := π.connected
  ρ := π.warpAt

/-- The painting of a portrayal, in the sense of Graph Minors XX, with the marches chosen freely. -/
noncomputable def paintingOf' {G : Hypergraph α β} (π : Portrayal G)
    (h₂ : ∀ c ∈ π.Γ.C, 2 ≤ (tilde c).ncard) : GM20.Painting π.S :=
  paintingOf π.Γ (fun c ↦ listOf (tilde c)) h₂ (fun _ _ ↦ nodup_listOf _)
    (fun _ hc ↦ by
      ext x
      exact mem_listOf (π.Γ.cell_disc _ hc).2.2.1)

variable {P : UnlabeledPatchwork α β} {π : Portrayal P.G.toHypergraph}

/-- Each cell `c` bordering the boundary has `cTilde ⊆ bd(Σ)`. -/
theorem tilde_subset_bd {c : Set π.S} (hc : c ∈ π.Γ.C) (hb : (c ∩ bd π.S).Nonempty) :
    tilde c ⊆ bd π.S := by
  intro n hn
  obtain ⟨-, -, -, h⟩ := π.Γ.border_cell c hc hb
  rw [← h] at hn
  obtain ⟨v, f, h₀, -⟩ := hn
  have := (f 0).2
  rw [h₀] at this
  exact this.2

/-- A cell meeting the boundary meets some cuff. -/
theorem exists_cuff_of_bd {x : π.S} (hx : x ∈ bd π.S) : ∃ Θ ∈ cuffs π.S, x ∈ Θ :=
  ⟨connectedComponentIn (bd π.S) x, ⟨x, hx, rfl⟩, mem_connectedComponentIn hx⟩

end GraphMinor.GM17.Portrayal
