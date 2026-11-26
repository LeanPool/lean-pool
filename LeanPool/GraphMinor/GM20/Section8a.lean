/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section9a
public import LeanPool.GraphMinor.GM20.Cited
public import LeanPool.GraphMinor.GM20.Draw6
public import LeanPool.GraphMinor.Surface.InvarianceOfDomain
public import LeanPool.GraphMinor.Surface.TopologyStatements
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.Convex
import LeanPool.GraphMinor.Surface.Fan

/-!
# Graph Minors XX, Section 8: making the discs narrow

A cell of size 2 of a painting of Graph Minors XX is a disc, and an edge of size 2 of a painting of
Graph Minors XIX is a line. The paper says "it is easy to convert from one version to the other;
make
the discs narrow and the lines thick". Here we pick in each cell of size 2 a line with the same two
ends.
For a border cell it is the part of the closure in the boundary. For an internal cell it is a chord
of the
disc. Replacing the cells of size 2 by these lines gives a painting in the sense of Graph Minors XIX
with
the same nodes.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- Basic facts on a line with ends `a` and `b`. -/
theorem line_facts [T2Space S] {L : Set S} {a b : S} (h : IsLineWithEnds L a b) :
    a ≠ b ∧ IsPathConnected (L \ {a, b}) ∧ closure (L \ {a, b}) = L ∧ lineEnds L = {a, b} := by
  have hab : a ≠ b := by
    obtain ⟨f, rfl, rfl⟩ := h
    intro he
    have := f.injective (Subtype.ext he)
    exact zero_ne_one this
  obtain ⟨f, ha, hb⟩ := id h
  have hcomp : IsCompact L := isCompact_iff_compactSpace.mpr f.compactSpace
  refine ⟨hab, h.isPathConnected_interior,
    Subset.antisymm (closure_minimal sdiff_subset hcomp.isClosed)
      h.subset_closure_interior, ?_⟩
  · ext u
    constructor
    · rintro ⟨v, g', h₀, -⟩
      let φ : unitInterval ≃ₜ unitInterval := g'.trans f.symm
      have hφ : Continuous fun s ↦ (φ s).1 := continuous_subtype_val.comp φ.continuous
      have hinj : Function.Injective fun s ↦ (φ s).1 := fun s s' h ↦ φ.injective (Subtype.ext h)
      have hu : u = (f (φ 0)).1 := by simp [φ, h₀]
      rcases Continuous.strictMono_of_inj hφ hinj with hm | hm
      · have h₁ : φ 0 = 0 := by
          apply Subtype.ext
          apply le_antisymm _ (φ 0).2.1
          have h₂ := hm.monotone (show (0 : unitInterval) ≤ φ.symm 0 from (φ.symm 0).2.1)
          simpa using h₂
        left
        rw [hu, h₁, ha]
      · have h₁ : φ 0 = 1 := by
          apply Subtype.ext
          apply le_antisymm (φ 0).2.2
          have h₂ := hm.antitone (show (0 : unitInterval) ≤ φ.symm 1 from (φ.symm 1).2.1)
          simpa using h₂
        exact Or.inr (by rw [mem_singleton_iff, hu, h₁, hb])
    · rintro (rfl | rfl)
      · exact ⟨b, h⟩
      · exact ⟨a, GM11.IsLineWithEnds.symm h⟩

/-- A chord of a closed disc between two points of its boundary. -/
theorem exists_chord [T2Space S] {D : Set S} (hD : IsClosedDisc D) {a b : S} (ha : a ∈ discBd D)
    (hb : b ∈ discBd D) (hab : a ≠ b) :
    ∃ L, IsLineWithEnds L a b ∧ L ⊆ D ∧ L \ {a, b} ⊆ D \ discBd D := by
  obtain ⟨L, hL, hLD, hbd⟩ := Surface.exists_chord hD ha hb hab
  refine ⟨L, hL, hLD, fun x hx => ⟨hLD hx.1, fun hxb => hx.2 ?_⟩⟩
  exact hbd ▸ ⟨hx.1, hxb⟩

/-- `L` gives for each cell of size 2 a line in its closure with the same two ends. For a border
cell this
is the part of the closure in the boundary. For an internal cell it is a chord of the disc. -/
def IsChordData (Γ : Painting S) (L : Set S → Set S) : Prop :=
  ∀ c ∈ Γ.C, (tilde c).ncard = 2 → ∃ a b, IsLineWithEnds (L c) a b ∧ tilde c = {a, b} ∧
    L c ⊆ closure c ∧
    ((¬ Painting.IsBorder c ∧ L c \ {a, b} ⊆ closure c \ discBd (closure c)) ∨
      (Painting.IsBorder c ∧ L c = closure c ∩ bd S))

theorem exists_chordData [T2Space S] (Γ : Painting S) : ∃ L, IsChordData Γ L := by
  classical
  have key : ∀ c, ∃ Lc : Set S, c ∈ Γ.C → (tilde c).ncard = 2 → ∃ a b, IsLineWithEnds Lc a b ∧
      tilde c = {a, b} ∧ Lc ⊆ closure c ∧
      ((¬ Painting.IsBorder c ∧ Lc \ {a, b} ⊆ closure c \ discBd (closure c)) ∨
        (Painting.IsBorder c ∧ Lc = closure c ∩ bd S)) := by
    intro c
    by_cases hc : c ∈ Γ.C ∧ (tilde c).ncard = 2
    · obtain ⟨hc, h₂⟩ := hc
      obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.mp h₂
      by_cases hb : Painting.IsBorder c
      · obtain ⟨-, ⟨f⟩, h₄⟩ := Γ.border_cell c hc hb
        refine ⟨closure c ∩ bd S, fun _ _ ↦ ?_⟩
        have hend : IsLineWithEnds (closure c ∩ bd S) (f 0).1 (f 1).1 := ⟨f, rfl, rfl⟩
        have h₅ := (line_facts hend).2.2.2
        rw [h₄, hset] at h₅
        exact ⟨(f 0).1, (f 1).1, hend, by rw [hset, h₅], inter_subset_left,
          Or.inr ⟨hb, rfl⟩⟩
      · have ha' : a ∈ discBd (closure c) := Γ.tilde_subset c hc (by rw [hset]; exact Or.inl rfl)
        have hb' : b ∈ discBd (closure c) := Γ.tilde_subset c hc (by rw [hset]; exact Or.inr rfl)
        obtain ⟨Lc, h₃, h₄, h₅⟩ := exists_chord (Γ.cell_disc c hc) ha' hb' hab
        exact ⟨Lc, fun _ _ ↦ ⟨a, b, h₃, hset, h₄, Or.inl ⟨hb, h₅⟩⟩⟩
    · exact ⟨∅, fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ hc⟩
  choose L hL using key
  exact ⟨L, hL⟩

namespace Thin

open Classical in
/-- The part of the cell `c` that remains. -/
noncomputable def τ (L : Set S → Set S) (c : Set S) : Set S :=
  if (tilde c).ncard = 2 then L c \ tilde c else c

open Classical in
/-- The closure of `τ L c`. -/
noncomputable def W (L : Set S → Set S) (c : Set S) : Set S :=
  if (tilde c).ncard = 2 then L c else closure c

variable [T2Space S] {Γ : Painting S} {L : Set S → Set S} {c : Set S}

omit [T2Space S] in
theorem closure_diff (hc : c ∈ Γ.C) : closure c \ Γ.N = c := by
  ext x
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra h₃
    exact h₂ (tilde_subset_N Γ hc ⟨h₁, h₃⟩)
  · intro hx
    exact ⟨subset_closure hx, (hc.2.1 hx).2⟩

omit [T2Space S] in
theorem closure_subset_U (hc : c ∈ Γ.C) : closure c ⊆ Γ.U :=
  closure_minimal (hc.2.1.trans sdiff_subset) Γ.isClosed_U

omit [T2Space S] in
theorem τ_subset (hL : IsChordData Γ L) (hc : c ∈ Γ.C) : τ L c ⊆ c := by
  unfold τ
  split_ifs with h
  · obtain ⟨a, b, -, -, h₃, -⟩ := hL c hc h
    rintro x ⟨hx, hxn⟩
    by_contra h₄
    exact hxn ⟨h₃ hx, h₄⟩
  · exact subset_rfl

omit [T2Space S] in
theorem W_subset (hL : IsChordData Γ L) (hc : c ∈ Γ.C) : W L c ⊆ closure c := by
  unfold W
  split_ifs with h
  · obtain ⟨a, b, -, -, h₃, -⟩ := hL c hc h
    exact h₃
  · exact subset_rfl

theorem closure_τ (hL : IsChordData Γ L) (hc : c ∈ Γ.C) : closure (τ L c) = W L c := by
  unfold τ W
  split_ifs with h
  · obtain ⟨a, b, h₁, h₂, -, -⟩ := hL c hc h
    rw [h₂]
    exact (line_facts h₁).2.2.1
  · rfl

theorem tilde_τ (hL : IsChordData Γ L) (hc : c ∈ Γ.C) : tilde (τ L c) = tilde c := by
  unfold τ
  split_ifs with h
  · obtain ⟨a, b, h₁, h₂, -, -⟩ := hL c hc h
    obtain ⟨h₃, -, h₄, -⟩ := line_facts h₁
    rw [h₂]
    unfold tilde
    rw [h₄]
    ext x
    constructor
    · rintro ⟨h₅, h₆⟩
      by_contra h₇
      exact h₆ ⟨h₅, h₇⟩
    · intro h₅
      exact ⟨by
        rcases h₅ with rfl | rfl
        · exact (Draw.mem_of_line h₁).1
        · exact (Draw.mem_of_line h₁).2, fun h₆ ↦ h₆.2 h₅⟩
  · rfl

theorem isPathConnected_τ (hL : IsChordData Γ L) (hc : c ∈ Γ.C) : IsPathConnected (τ L c) := by
  unfold τ
  split_ifs with h
  · obtain ⟨a, b, h₁, h₂, -, -⟩ := hL c hc h
    rw [h₂]
    exact (line_facts h₁).2.1
  · exact hc.2.2.1

theorem W_diff (hL : IsChordData Γ L) (hc : c ∈ Γ.C) : W L c \ Γ.N = τ L c := by
  ext x
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₃ : x ∈ c := by
      rw [← closure_diff hc]
      exact ⟨W_subset hL hc h₁, h₂⟩
    unfold W at h₁
    unfold τ
    split_ifs at h₁ ⊢ with h
    · exact ⟨h₁, fun h₄ ↦ h₄.2 h₃⟩
    · exact h₃
  · intro hx
    refine ⟨?_, (hc.2.1 (τ_subset hL hc hx)).2⟩
    rw [← closure_τ hL hc]
    exact subset_closure hx

/-- The new set `U`. -/
noncomputable def U' (Γ : Painting S) (L : Set S → Set S) : Set S := Γ.N ∪ ⋃ c ∈ Γ.C, W L c

theorem isClosed_W (hL : IsChordData Γ L) (hc : c ∈ Γ.C) : IsClosed (W L c) := by
  rw [← closure_τ hL hc]
  exact isClosed_closure

omit [T2Space S] in
theorem U'_subset (hL : IsChordData Γ L) : U' Γ L ⊆ Γ.U := by
  rintro x (hx | hx)
  · exact Γ.N_subset hx
  · simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨c, hc, hx⟩ := hx
    exact closure_subset_U hc (W_subset hL hc hx)

theorem mem_U'_diff {x : S} (hL : IsChordData Γ L) (hx : x ∈ U' Γ L \ Γ.N) :
    ∃ c ∈ Γ.C, x ∈ τ L c := by
  obtain ⟨hx | hx, hn⟩ := hx
  · exact absurd hx hn
  · simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨c, hc, hx⟩ := hx
    exact ⟨c, hc, by rw [← W_diff hL hc]; exact ⟨hx, hn⟩⟩

theorem τ_subset_U' (hL : IsChordData Γ L) (hc : c ∈ Γ.C) : τ L c ⊆ U' Γ L \ Γ.N := by
  intro x hx
  have h₁ := hx
  rw [← W_diff hL hc] at h₁
  exact ⟨Or.inr (mem_biUnion hc h₁.1), h₁.2⟩

theorem τ_mem (hL : IsChordData Γ L) (hc : c ∈ Γ.C) : τ L c ∈ arcComponentsIn (U' Γ L \ Γ.N) := by
  have hp := isPathConnected_τ hL hc
  refine ⟨hp.nonempty, τ_subset_U' hL hc, hp, ?_⟩
  intro D hD hDp hsub
  have hne := hp.nonempty
  have hDc : D ⊆ c := by
    have h₁ : c ∪ D = c := by
      refine hc.2.2.2 _ ?_ (hc.2.2.1.union hDp ?_) subset_union_left
      · rintro x (hx | hx)
        · exact hc.2.1 hx
        · exact ⟨U'_subset hL (hD hx).1, (hD hx).2⟩
      · obtain ⟨x, hx⟩ := hne
        exact ⟨x, τ_subset hL hc hx, hsub hx⟩
    exact subset_union_right.trans h₁.subset
  refine subset_antisymm ?_ hsub
  intro x hx
  obtain ⟨c', hc', hxc'⟩ := mem_U'_diff hL (hD hx)
  have h₂ : c = c' := arcComponent_eq hc hc' (hDc hx) (τ_subset hL hc' hxc')
  rw [h₂]
  exact hxc'

theorem arcComponents_eq (hL : IsChordData Γ L) :
    arcComponentsIn (U' Γ L \ Γ.N) = τ L '' Γ.C := by
  ext e
  constructor
  · intro he
    obtain ⟨x, hx⟩ := he.1
    obtain ⟨c, hc, hxc⟩ := mem_U'_diff hL (he.2.1 hx)
    exact ⟨c, hc, arcComponent_eq (τ_mem hL hc) he hxc hx⟩
  · rintro ⟨c, hc, rfl⟩
    exact τ_mem hL hc

theorem τ_injOn (hL : IsChordData Γ L) : InjOn (τ L) Γ.C := by
  intro c hc c' hc' h
  obtain ⟨x, hx⟩ := (isPathConnected_τ hL hc).nonempty
  exact arcComponent_eq hc hc' (τ_subset hL hc hx) (τ_subset hL hc' (h ▸ hx))

omit [T2Space S] in
/-- The cells of the new painting are in the cell `c`, and for a border cell equal to the part in
the
boundary. -/
theorem inter_bd (hL : IsChordData Γ L) (hc : c ∈ Γ.C) : c ∩ bd S = τ L c ∩ bd S := by
  apply subset_antisymm _ (inter_subset_inter_left _ (τ_subset hL hc))
  rintro x ⟨hx, hb⟩
  refine ⟨?_, hb⟩
  have hb' : Painting.IsBorder c := ⟨x, hx, hb⟩
  have h₂ := (Γ.border_cell c hc hb').1
  unfold τ
  rw [ite_eq_left h₂]
  obtain ⟨a, b, -, h₄, -, h₅⟩ := hL c hc h₂
  rcases h₅ with h₅ | ⟨-, h₅⟩
  · exact absurd hb' h₅.1
  · rw [h₅]
    exact ⟨⟨subset_closure hx, hb⟩, fun h₆ ↦ h₆.2 hx⟩

omit [T2Space S] in
theorem τ_subset_bd (hL : IsChordData Γ L) (hc : c ∈ Γ.C) (hb : (τ L c ∩ bd S).Nonempty) :
    τ L c ⊆ bd S ∧ (tilde c).ncard = 2 := by
  have hb' : Painting.IsBorder c := by
    obtain ⟨x, hx, hxb⟩ := hb
    exact ⟨x, τ_subset hL hc hx, hxb⟩
  have h₂ := (Γ.border_cell c hc hb').1
  refine ⟨?_, h₂⟩
  unfold τ
  rw [ite_eq_left h₂]
  obtain ⟨a, b, -, h₄, -, h₅⟩ := hL c hc h₂
  rcases h₅ with h₅ | ⟨-, h₅⟩
  · exact absurd hb' h₅.1
  · rw [h₅]
    exact fun x hx ↦ hx.1.2

/-- The cell of `Γ` that gives an edge of the new painting. -/
noncomputable def back (Γ : Painting S) (L : Set S → Set S) (e : Set S) : Set S :=
  Function.invFunOn (τ L) Γ.C e

theorem back_τ (hL : IsChordData Γ L) (hc : c ∈ Γ.C) : back Γ L (τ L c) = c :=
  (τ_injOn hL).leftInvOn_invFunOn hc

/-- The painting of Graph Minors XIX that we get from `Γ` by making the discs narrow. -/
noncomputable def painting (Γ : Painting S) (L : Set S → Set S) (hL : IsChordData Γ L) :
    GM19.Painting S where
  U := U' Γ L
  V := Γ.N
  γ e := Γ.γ (back Γ L e)
  isClosed_U := by
    have h₁ : IsClosed (⋃ c ∈ Γ.C, W L c) :=
      Set.Finite.isClosed_biUnion Γ.finite_cells fun c hc ↦ isClosed_W hL hc
    exact Γ.finite_N.isClosed.union h₁
  V_subset := subset_union_left
  finite_V := Γ.finite_N
  bd_subset := by
    intro x hx
    by_cases hn : x ∈ Γ.N
    · exact Or.inl hn
    · have hc : pathComponentIn (Γ.U \ Γ.N) x ∈ Γ.C :=
        mem_arcComponentsIn_pathComponentIn ⟨Γ.bd_subset hx, hn⟩
      have hxc : x ∈ pathComponentIn (Γ.U \ Γ.N) x := mem_pathComponentIn_self ⟨Γ.bd_subset hx, hn⟩
      have h₁ : x ∈ τ L (pathComponentIn (Γ.U \ Γ.N) x) := by
        have h₂ := inter_bd hL hc
        have h₃ : x ∈ pathComponentIn (Γ.U \ Γ.N) x ∩ bd S := ⟨hxc, hx⟩
        rw [h₂] at h₃
        exact h₃.1
      exact (τ_subset_U' hL hc h₁).1
  finite_edges := by
    rw [arcComponents_eq hL]
    exact Γ.finite_cells.image _
  edge_shape := by
    intro e he
    rw [arcComponents_eq hL] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [tilde_τ hL hc, closure_τ hL hc]
    have hf := (Γ.cell_size c hc).1
    by_cases h : (tilde c).ncard = 2
    · left
      obtain ⟨a, b, h₁, h₂, -, -⟩ := hL c hc h
      refine ⟨h, hf, ?_, ?_⟩
      · simp only [W, ite_eq_left h]
        obtain ⟨g, -, -⟩ := h₁
        exact ⟨g⟩
      · simp only [W, ite_eq_left h]
        rw [h₂]
        exact (line_facts h₁).2.2.2
    · right
      have h₃ := (Γ.cell_size c hc).2.resolve_left h
      refine ⟨h₃, hf, ?_, ?_⟩
      · simp only [W, ite_eq_right h]
        exact Γ.cell_disc c hc
      · simp only [W, ite_eq_right h]
        exact Γ.tilde_subset c hc
  γ_nodup := by
    intro e he
    rw [arcComponents_eq hL] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [back_τ hL hc]
    exact Γ.γ_nodup c hc
  γ_set := by
    intro e he
    rw [arcComponents_eq hL] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [back_τ hL hc, tilde_τ hL hc]
    exact Γ.γ_set c hc
  border_edge := by
    intro e he hb
    rw [arcComponents_eq hL] at he
    obtain ⟨c, hc, rfl⟩ := he
    obtain ⟨h₁, h₂⟩ := τ_subset_bd hL hc hb
    rw [tilde_τ hL hc]
    exact ⟨h₂, h₁⟩

@[simp] theorem painting_E (hL : IsChordData Γ L) : (painting Γ L hL).E = τ L '' Γ.C :=
  arcComponents_eq hL

theorem painting_skAdj (hL : IsChordData Γ L) : (painting Γ L hL).skAdj = Γ.sk := by
  ext x y
  change (x ≠ y ∧ x ∈ Γ.N ∧ y ∈ Γ.N ∧ ∃ e ∈ (painting Γ L hL).E, x ∈ tilde e ∧ y ∈ tilde e) ↔
    (x ≠ y ∧ x ∈ Γ.N ∧ y ∈ Γ.N ∧ ∃ c ∈ Γ.C, x ∈ tilde c ∧ y ∈ tilde c)
  rw [painting_E]
  constructor
  · rintro ⟨h₁, h₂, h₃, _, ⟨c, hc, rfl⟩, h₄, h₅⟩
    rw [tilde_τ hL hc] at h₄ h₅
    exact ⟨h₁, h₂, h₃, c, hc, h₄, h₅⟩
  · rintro ⟨h₁, h₂, h₃, c, hc, h₄, h₅⟩
    exact ⟨h₁, h₂, h₃, _, ⟨c, hc, rfl⟩, by rwa [tilde_τ hL hc], by rwa [tilde_τ hL hc]⟩

end Thin

end GraphMinor.GM20
