/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section3
public import LeanPool.GraphMinor.GM14.DiscSlope
public import LeanPool.GraphMinor.GM09.Section8
public import LeanPool.GraphMinor.GM17.AngleOrder
public import LeanPool.GraphMinor.GM17.PaintDiscs
public import LeanPool.GraphMinor.GM17.CycleOrder

/-!
# The polygons and lunes of a segregation

This is the first step of the proof of XVII (13.1), page 202. We start from a segregation of a graph
with a proper arrangement in a closed surface. Each
society with more than three vertices is a vortex. It has a linear decomposition by XVI, and its
disc holds a polygon with one lune for each side
(`exists_vortexCut`, data in `VortexCut`).

The discs of the small societies and the lunes are the closed discs of a painting of the surface
with the polygons removed. Here we collect the facts on these
discs in the closed surface: they are indexed by `Idx`, the discs are `Ds`, and they meet only in
the points of the arrangement.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface GM09 GM14 GM16 Graph

universe u v

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]

/-- The data of one vortex: a linear decomposition, and a polygon with its lunes in the disc `E`. -/
structure VortexCut (s : Society α β) (E : Set S) (ν : α → S) (ρ : ℕ) where
  /-- The number of vertices of the society. -/
  k : ℕ
  four : 4 ≤ k
  /-- The next index. -/
  nx : Fin k → Fin k
  hnx : ∀ i, (nx i).1 = (i.1 + 1) % k
  /-- A clockwise enumeration of the society. -/
  t : Fin k → α
  /-- The linear decomposition. -/
  X : Fin k → Graph α β
  dec : s.IsLinearDecomposition t X
  small : ∀ i i', i < i' → (V(X i) ∩ V(X i')).ncard ≤ ρ
  /-- The polygon. -/
  P : Set S
  /-- The lunes. -/
  L : Fin k → Set S
  /-- The sides of the polygon. -/
  F : Fin k → Set S
  disc_P : IsClosedDisc P
  P_sub : P ⊆ E
  bd_P : discBd P = ⋃ i, F i
  disc_L : ∀ i, IsClosedDisc (L i)
  L_sub : ∀ i, L i ⊆ E
  L_inter : ∀ i, L i ∩ P = F i
  F_sub : ∀ i, F i ⊆ discBd (L i)
  F_line : ∀ i, IsLineWithEnds (F i) (ν (t i)) (ν (t (nx i)))
  lune_inter : ∀ i j, i ≠ j → L i ∩ L j ⊆ range fun i => ν (t i)
  node_mem : ∀ i j, ν (t j) ∈ L i ↔ j = i ∨ j = nx i

theorem IsLineWithEnds.left_mem {T : Type*} [TopologicalSpace T] {L : Set T} {u v : T}
  (h : IsLineWithEnds L u v) : u ∈ L := by
  obtain ⟨f, h0, -⟩ := h
  exact h0 ▸ (f 0).2

theorem IsLineWithEnds.right_mem {T : Type*} [TopologicalSpace T] {L : Set T} {u v : T}
  (h : IsLineWithEnds L u v) : v ∈ L := by
  obtain ⟨f, -, h1⟩ := h
  exact h1 ▸ (f 1).2

section

variable [T2Space S] {G : Graph α β} {Seg : Set (Society α β)} {D : Society α β → Set S} {ν : α
  → S} {ρ : ℕ}

/-- A vortex of a proper arrangement has a linear decomposition, and a polygon with lunes in its
disc. -/
theorem exists_vortexCut (hS : IsClosedSurface S) (harr : IsProperArrangement Seg D ν) {s : Society
  α β} (hs : s ∈ Seg)
    (h3 : 3 < s.Ω.bar.ncard) (hv : IsRhoVortex s ρ) : Nonempty (VortexCut s (D s) ν ρ) := by
  have hne : s.Ω.bar.Nonempty := by
    rw [← Set.ncard_pos s.Ω.finite_bar]
    omega
  obtain ⟨t, ht, hr, hcw⟩ := s.Ω.exists_clockwise_enumeration hne
  have hk0 : 0 < s.Ω.bar.ncard := by omega
  obtain ⟨X, hX, hsm⟩ := exists_isLinearDecomposition_of_isRhoVortex (by omega) hv ht hr hcw
  have hdisc := (harr.1.isClosedDisc s hs).1
  obtain ⟨-, φ₀, hφ⟩ := harr.1.natural_order s hs
  have heq : subBd (D s) = discBd (D s) := IsClosedDisc.subBd_eq_discBd hS hdisc
  have hinj : InjOn ν s.Ω.bar := harr.1.injOn_pts.mono (subset_biUnion_of_mem (u
    := fun s : Society α β => s.Ω.bar) hs)
  obtain ⟨θ, hθ, hl, hval⟩ := exists_angles hk0 hcw hinj hφ
  let nx : Fin s.Ω.bar.ncard → Fin s.Ω.bar.ncard := fun i => ⟨(i.1 + 1) % s.Ω.bar.ncard, Nat.mod_lt
    _ hk0⟩
  let φ : Circle ≃ₜ discBd (D s) := φ₀.trans (Homeomorph.setCongr heq)
  obtain ⟨P, L, F, h1, h2, h3', h4, h5, h6, h7⟩ := exists_polygon_in_disc hdisc φ
    (by omega) θ hθ hl nx (fun _ => rfl) (fun i => ν (t i)) (fun i => hval i)
  exact ⟨{ k := s.Ω.bar.ncard
           four := by omega
           nx := nx
           hnx := fun _ => rfl
           t := t
           X := X
           dec := hX
           small := hsm
           P := P
           L := L
           F := F
           disc_P := h1
           P_sub := h2
           bd_P := h3'
           disc_L := fun i => (h5 i).1
           L_sub := fun i => (h5 i).2.1
           L_inter := fun i => (h5 i).2.2.1
           F_sub := fun i => (h5 i).2.2.2.1
           F_line := fun i => (h5 i).2.2.2.2
           lune_inter := h6
           node_mem := h7 }⟩

/-- The vortices of `Seg`. -/
abbrev Maj (Seg : Set (Society α β)) := ↥{s ∈ Seg | 3 < s.Ω.bar.ncard}

/-- The small societies of `Seg`. -/
abbrev Mnr (Seg : Set (Society α β)) := ↥{s ∈ Seg | ¬ 3 < s.Ω.bar.ncard}

variable (V : ∀ m : Maj Seg, VortexCut m.1 (D m.1) ν ρ)

/-- The index set of the discs of the painting: the small societies, and the lunes. -/
abbrev Idx := Mnr Seg ⊕ Σ m : Maj Seg, Fin (V m).k

/-- The society that a disc belongs to. -/
def soc : Idx V → Society α β
  | .inl s => s.1
  | .inr x => x.1.1

/-- The discs of the painting. -/
def Ds : Idx V → Set S
  | .inl s => D s.1
  | .inr x => (V x.1).L x.2

/-- The vertices of the arrangement, as points of the surface. -/
def Nd (Seg : Set (Society α β)) (ν : α → S) : Set S := ν '' segregationVertices Seg

omit [T2Space S] in
theorem soc_mem (i : Idx V) : soc V i ∈ Seg := by
  rcases i with s | x
  · exact s.2.1
  · exact x.1.2.1

omit [T2Space S] in
theorem Ds_sub (i : Idx V) : Ds V i ⊆ D (soc V i) := by
  rcases i with s | x
  · exact subset_rfl
  · exact (V x.1).L_sub x.2

theorem bar_sub_verts {s : Society α β} (hs : s ∈ Seg) : s.Ω.bar ⊆ segregationVertices Seg
  := subset_biUnion_of_mem (u := fun s : Society α β => s.Ω.bar) hs

variable {V}
variable (harr : IsProperArrangement Seg D ν)
include harr

/-- If the point of a vertex of the arrangement lies in the disc of `s`, then the vertex belongs to
`s`. -/
theorem mem_bar_of_mem_disc {s : Society α β} (hs : s ∈ Seg) {v : α} (hv : v ∈ segregationVertices
  Seg) (h : ν v ∈ D s) : v ∈ s.Ω.bar := by
  obtain ⟨s', hs', hv'⟩ : ∃ s' ∈ Seg, v ∈ s'.Ω.bar := by simpa [segregationVertices] using hv
  by_cases he : s' = s
  · exact he ▸ hv'
  have hp : ν v ∈ subBd (D s') := (harr.1.isClosedDisc s' hs').2 v hv'
  have hmem : ν v ∈ D s' := by
    have := hp.1
    rwa [(harr.1.isClosedDisc s' hs').1.isClosed.closure_eq] at this
  obtain ⟨w, hw, hwe⟩ := harr.1.inter_discs s hs s' hs' (Ne.symm he) ⟨h, hmem⟩
  exact (harr.1.injOn_pts (bar_sub_verts hs hw.1) hv hwe) ▸ hw.1

theorem pt_mem_disc {s : Society α β} (hs : s ∈ Seg) {v : α} (hv : v ∈ s.Ω.bar) : ν v ∈ D s := by
  have hp : ν v ∈ subBd (D s) := (harr.1.isClosedDisc s hs).2 v hv
  have := hp.1
  rwa [(harr.1.isClosedDisc s hs).1.isClosed.closure_eq] at this

omit [TopologicalSpace S] [T2Space S] harr in
theorem soc_ne_of_mnr_maj (a : Mnr Seg) (m : Maj Seg) : a.1 ≠ m.1 := fun h => a.2.2 (h ▸ m.2.2)

omit harr in
omit [T2Space S] in
theorem t_mem_bar (m : Maj Seg) (j : Fin (V m).k) : (V m).t j ∈ m.1.Ω.bar := by
  rw [← (V m).dec.range_t]
  exact mem_range_self j

omit harr in
omit [T2Space S] in
theorem exists_t_eq {m : Maj Seg} {v : α} (hv : v ∈ m.1.Ω.bar) : ∃ j, (V m).t j = v := by
  rw [← (V m).dec.range_t] at hv
  exact hv

omit [TopologicalSpace S] [T2Space S] harr in
theorem pt_mem_Nd {s : Society α β} (hs : s ∈ Seg) {v : α} (hv : v ∈ s.Ω.bar) : ν v ∈ Nd Seg ν :=
  mem_image_of_mem _ (bar_sub_verts hs hv)

omit [T2Space S] in
theorem inter_sub_Nd {i j : Idx V} (hij : i ≠ j) : Ds V i ∩ Ds V j ⊆ Nd Seg ν := by
  by_cases hs : soc V i = soc V j
  · rcases i with a | ⟨m, a⟩ <;> rcases j with b | ⟨m', b⟩
    · exact absurd (congrArg Sum.inl (Subtype.ext hs)) hij
    · exact absurd hs (soc_ne_of_mnr_maj a m')
    · exact absurd hs.symm (soc_ne_of_mnr_maj b m)
    · obtain rfl : m = m' := Subtype.ext hs
      have hab : a ≠ b := fun h => hij (h ▸ rfl)
      rintro x hx
      obtain ⟨e, rfl⟩ := (V m).lune_inter a b hab hx
      exact pt_mem_Nd m.2.1 (t_mem_bar m e)
  · rintro x ⟨hx, hx'⟩
    obtain ⟨w, hw, rfl⟩ := harr.1.inter_discs _ (soc_mem V i) _ (soc_mem V j) hs ⟨Ds_sub V i hx,
      Ds_sub V j hx'⟩
    exact pt_mem_Nd (soc_mem V i) hw.1

theorem Nd_inter_inl (a : Mnr Seg) : Nd Seg ν ∩ D a.1 = ν '' a.1.Ω.bar := by
  ext x
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, h⟩
    exact ⟨v, mem_bar_of_mem_disc harr a.2.1 hv h, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨pt_mem_Nd a.2.1 hv, pt_mem_disc harr a.2.1 hv⟩

theorem Nd_inter_inr (m : Maj Seg) (i : Fin (V m).k) :
    Nd Seg ν ∩ (V m).L i = {ν ((V m).t i), ν ((V m).t ((V m).nx i))} := by
  ext x
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, h⟩
    obtain ⟨j, rfl⟩ := exists_t_eq (V := V) (mem_bar_of_mem_disc harr m.2.1 hv ((V m).L_sub i h))
    rcases ((V m).node_mem i j).mp h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨pt_mem_Nd m.2.1 (t_mem_bar m _), ((V m).node_mem i i).mpr (Or.inl rfl)⟩
    · exact ⟨pt_mem_Nd m.2.1 (t_mem_bar m _), ((V m).node_mem i _).mpr (Or.inr rfl)⟩

omit [T2Space S] in
theorem Ds_disc (i : Idx V) : IsClosedDisc (Ds V i) := by
  rcases i with a | ⟨m, a⟩
  · exact (harr.1.isClosedDisc _ a.2.1).1
  · exact (V m).disc_L a

theorem Nd_sub_discBd (hS : IsClosedSurface S) (i : Idx V) : Nd Seg ν ∩ Ds V i ⊆ discBd (Ds V i)
  := by
  rcases i with a | ⟨m, a⟩
  · change Nd Seg ν ∩ D a.1 ⊆ discBd (D a.1)
    rw [Nd_inter_inl harr]
    rintro _ ⟨v, hv, rfl⟩
    rw [← IsClosedDisc.subBd_eq_discBd hS (harr.1.isClosedDisc _ a.2.1).1]
    exact (harr.1.isClosedDisc _ a.2.1).2 v hv
  · change Nd Seg ν ∩ (V m).L a ⊆ discBd ((V m).L a)
    rw [Nd_inter_inr harr]
    rintro x (rfl | rfl)
    · exact (V m).F_sub a ((V m).F_line a).left_mem
    · exact (V m).F_sub a ((V m).F_line a).right_mem

theorem Nd_sub_Ds : Nd Seg ν ⊆ ⋃ i, Ds V i := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨s, hs, hv'⟩ : ∃ s ∈ Seg, v ∈ s.Ω.bar := by simpa [segregationVertices] using hv
  by_cases h3 : 3 < s.Ω.bar.ncard
  · let m : Maj Seg := ⟨s, hs, h3⟩
    obtain ⟨j, rfl⟩ := exists_t_eq (V := V) (m := m) hv'
    exact mem_iUnion.2 ⟨.inr ⟨m, j⟩, ((V m).node_mem j j).mpr (Or.inl rfl)⟩
  · exact mem_iUnion.2 ⟨.inl ⟨s, hs, h3⟩, pt_mem_disc harr hs hv'⟩

omit [T2Space S] harr in
theorem pt_mem_discBd_P (m : Maj Seg) (j : Fin (V m).k) : ν ((V m).t j) ∈ discBd (V m).P := by
  rw [(V m).bd_P]
  exact mem_iUnion.2 ⟨j, ((V m).F_line j).left_mem⟩

omit [T2Space S] in
theorem disjoint_disc {m m' : Maj Seg} (h : m ≠ m') : Disjoint (D m.1) (D m'.1) :=
  harr.2 m.2.1 m'.2.1 (fun he => h (Subtype.ext he)) m.2.2 m'.2.2

omit [T2Space S] in
theorem disjoint_P {m m' : Maj Seg} (h : m ≠ m') : Disjoint (V m).P (V m').P :=
  (disjoint_disc harr h).mono (V m).P_sub (V m').P_sub

omit [T2Space S] in
/-- A small disc meets the disc of a vortex only in points of that vortex. -/
theorem mnr_inter_maj (a : Mnr Seg) (m : Maj Seg) : D a.1 ∩ D m.1 ⊆ ν '' m.1.Ω.bar := by
  rintro x hx
  obtain ⟨w, hw, rfl⟩ := harr.1.inter_discs _ a.2.1 _ m.2.1 (soc_ne_of_mnr_maj a m) hx
  exact ⟨w, hw.2, rfl⟩

/-- The surface with the polygons removed. -/
def Cut (V : ∀ m : Maj Seg, VortexCut m.1 (D m.1) ν ρ) : Set S := (⋃ m, discInt (V m).P)ᶜ

omit [T2Space S] in
theorem Ds_sub_Cut (i : Idx V) : Ds V i ⊆ Cut V := by
  intro z hz hu
  obtain ⟨m, hzP, hzn⟩ := mem_iUnion.1 hu
  rcases i with a | ⟨m', a⟩
  · obtain ⟨v, hv, rfl⟩ := mnr_inter_maj harr a m ⟨hz, (V m).P_sub hzP⟩
    obtain ⟨j, rfl⟩ := exists_t_eq (V := V) hv
    exact hzn (pt_mem_discBd_P m j)
  · by_cases hm : m' = m
    · subst hm
      have : z ∈ (V m').F a := by
        rw [← (V m').L_inter a]
        exact ⟨hz, hzP⟩
      exact hzn (by rw [(V m').bd_P]; exact mem_iUnion.2 ⟨a, this⟩)
    · exact Set.disjoint_left.mp (disjoint_disc harr hm) ((V m').L_sub a hz) ((V m).P_sub hzP)

omit [T2Space S] in
/-- A small disc meets the boundary of the cut surface only in points of the arrangement. -/
theorem mnr_inter_bd (a : Mnr Seg) : D a.1 ∩ ⋃ m, discBd (V m).P ⊆ Nd Seg ν := by
  rintro x ⟨hx, hx'⟩
  obtain ⟨m, hm⟩ := mem_iUnion.1 hx'
  obtain ⟨v, hv, rfl⟩ := mnr_inter_maj harr a m ⟨hx, (V m).P_sub (discBd_subset _ hm)⟩
  exact pt_mem_Nd m.2.1 hv

omit [T2Space S] in
/-- A lune meets the boundary of the cut surface in its side. -/
theorem lune_inter_bd (m : Maj Seg) (i : Fin (V m).k) : (V m).L i ∩ ⋃ m', discBd (V m').P =
  (V m).F i := by
  ext x
  constructor
  · rintro ⟨hx, hx'⟩
    obtain ⟨m', hm⟩ := mem_iUnion.1 hx'
    by_cases he : m = m'
    · subst he
      rw [← (V m).L_inter i]
      exact ⟨hx, discBd_subset _ hm⟩
    · exact absurd ((V m').P_sub (discBd_subset _ hm)) (Set.disjoint_left.mp
      (disjoint_disc harr he) ((V m).L_sub i hx))
  · intro hx
    refine ⟨?_, mem_iUnion.2 ⟨m, ?_⟩⟩
    · rw [← (V m).L_inter i] at hx
      exact hx.1
    · rw [(V m).bd_P]
      exact mem_iUnion.2 ⟨i, hx⟩

end

end GraphMinor.GM17
