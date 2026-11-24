/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Theorem61
public import LeanPool.GraphMinor.GM11.Theorem65

/-!
# Theorems (6.6) and (4.1) of Graph Minors XI

`theorem_6_6` is Graph Minors XI, (6.6), pages 92–93, with the correction for loops at `θ = 2` of
`theorem_6_5`. See the correction to (6.6) in `corrections/GM11.md`. We state it for any two
drawings with a common radial drawing, which covers the paper's dual drawings. The paper's "In
particular" is about respectful tangles: `theorem_6_6_exists`.

`theorem_4_1` is Graph Minors XI, (4.1), page 78.

The common tools are that a slope is determined by a pretangle (`derived_unique`) and that the
induced pretangle
depends only on the discs of short circuits (`induced_congr`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

section Congr

variable {Γ : PaintingOrDrawing S} {Γ' : Drawing S} {θ : ℕ} {ins ins' : Drawing S → Set S}

/-- The pretangle induced from a slope depends only on the discs of the short circuits. -/
theorem induced_congr (h : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ
  → ins C = ins' C) :
    inducedPretangle Γ Γ' θ ins = inducedPretangle Γ Γ' θ ins' := by
  have key : ∀ {i j : Drawing S → Set S}, (∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ'
    → C.length < 2 * θ →
      i C = j C) → ∀ p, p ∈ inducedPretangle Γ Γ' θ i → p ∈ inducedPretangle Γ Γ' θ j := by
    rintro i j hij p ⟨hs, ho, hc, hcap⟩
    refine ⟨hs, ho, hc, fun r hr => ?_⟩
    obtain ⟨C, hC, hCs, hl, hin⟩ := hcap r hr
    refine ⟨C, hC, hCs, hl, ?_⟩
    rwa [← hij C hC (hCs.trans (Drawing.span_isSubdrawing Γ' _ _)) hl]
  exact Set.ext fun p => ⟨key h p, key (fun C a b c => (h C a b c).symm) p⟩

variable {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}

/-- A pretangle determines the discs of its derived slope. -/
theorem derived_unique [ConnectedSpace S] (hS : IsClosedSurface S) (hT : IsPretangle Γ.toHypergraph
  θ T)
    (hrad : Γ.U ∩ Γ'.U = Γ.V) (hd : IsDerivedSlope Γ Γ' θ T ins) (hd' : IsDerivedSlope Γ Γ' θ T
      ins')
    (C : Drawing S) (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ') (hl : C.length < 2 * θ) : ins C
      = ins' C := by
  obtain ⟨d, b, m⟩ := hd C hC hCs hl
  obtain ⟨d', b', m'⟩ := hd' C hC hCs hl
  by_contra hne
  have hbd : discBd (ins C) = discBd (ins' C) := by
    rw [← IsClosedDisc.frontier_eq_discBd hS d, ← IsClosedDisc.frontier_eq_discBd hS d',
      ← subBd_eq_frontier,
      ← subBd_eq_frontier, b, b']
  have hcov := cover_of_discBd_eq hS d d' hbd hne
  have hfr : frontier (ins C) ⊆ Γ'.U := by
    rw [← subBd_eq_frontier, b]
    exact hCs.U_subset
  have hfr' : frontier (ins' C) ⊆ Γ'.U := by
    rw [← subBd_eq_frontier, b']
    exact hCs.U_subset
  exact not_cover hT hrad (IsClosedDisc.isCompact d).isClosed (IsClosedDisc.isCompact d').isClosed
    (IsClosedDisc.isCompact d).isClosed hfr hfr' hfr m m' m (by rw [hcov, univ_union])

end Congr

/-- A tangle is a pretangle. -/
theorem IsTangle.isPretangle {α β : Type*} {G : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (h : GM10.IsTangle G θ T) : IsPretangle G θ T :=
  ⟨h.one_le, h.isSeparation, h.order_lt, h.axiom1, h.axiom2⟩

variable [ConnectedSpace S] {Γ Γs Γ' : Drawing S} {θ : ℕ}

/-- A respectful tangle in a drawing `Γ` with radial drawing `Γ'`, and the even slope derived from
it. -/
private theorem transfer (hS : IsClosedSurface S) (hE : Γ.E.Nonempty) (hEs : Γs.E.Nonempty)
    (hrad : (PaintingOrDrawing.drawing Γ).IsRadialDrawing Γ') (hrads :
      (PaintingOrDrawing.drawing Γs).IsRadialDrawing Γ')
    (hloop : θ ≠ 2 ∨ ∀ e ∈ Γs.E, ∃ x y, x ≠ y ∧ closure e ∩ Γs.V = {x, y})
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hresp : (PaintingOrDrawing.drawing Γ).IsRespectful θ T) {ins : Drawing S → Set S}
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) Γ' θ T ins) :
    GM10.IsTangle Γs.toHypergraph θ (inducedPretangle (PaintingOrDrawing.drawing Γs) Γ' θ ins) ∧
      (PaintingOrDrawing.drawing Γs).IsRespectful θ (inducedPretangle
        (PaintingOrDrawing.drawing Γs) Γ' θ ins) ∧
      IsDerivedSlope (PaintingOrDrawing.drawing Γs) Γ' θ (inducedPretangle
        (PaintingOrDrawing.drawing Γs) Γ' θ ins) ins := by
  have hp := IsTangle.isPretangle hT
  have hsl := isSlope_of_derived (Γ := PaintingOrDrawing.drawing Γ) hS hp hrad.2.1.1 hd
  have hev := (theorem_6_5_proof hS hE hp hresp hrad hd).1 hT
  obtain ⟨h₁, h₂, h₃⟩ := theorem_6_1_proof (Γ := PaintingOrDrawing.drawing Γs) hS hEs hrads
    hT.one_le hsl
  exact ⟨(theorem_6_5_proof hS hEs h₁ h₂ hrads h₃).2 hloop hev, h₂, h₃⟩

/-- The set of respectful tangles of order `θ` in a drawing. -/
abbrev RespectfulTangle (Γ : Drawing S) (θ : ℕ) : Type u :=
  {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)) //
    GM10.IsTangle Γ.toHypergraph θ T ∧ (PaintingOrDrawing.drawing Γ).IsRespectful θ T}

/-- **Graph Minors XI, (6.6)** (pages 92–93), for drawings with a common radial drawing, with the
correction for loops at `θ = 2`: there is a bijection between respectful tangles, and the two sides
of it have the same derived slopes. -/
theorem theorem_6_6_proof (hS : IsClosedSurface S) (hE : Γ.E.Nonempty) (hEs : Γs.E.Nonempty)
    (hrad : (PaintingOrDrawing.drawing Γ).IsRadialDrawing Γ') (hrads :
      (PaintingOrDrawing.drawing Γs).IsRadialDrawing Γ')
    (hloop : θ ≠ 2 ∨ (∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y}) ∧
      ∀ e ∈ Γs.E, ∃ x y, x ≠ y ∧ closure e ∩ Γs.V = {x, y}) :
    ∃ φ : RespectfulTangle Γ θ ≃ RespectfulTangle Γs θ, ∀ (T : RespectfulTangle Γ θ)
      (ins : Drawing S → Set S),
      IsDerivedSlope (PaintingOrDrawing.drawing Γ) Γ' θ T.1 ins ↔
        IsDerivedSlope (PaintingOrDrawing.drawing Γs) Γ' θ (φ T).1 ins := by
  classical
  have hl₁ : θ ≠ 2 ∨ ∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y} := hloop.imp id (·.1)
  have hl₂ : θ ≠ 2 ∨ ∀ e ∈ Γs.E, ∃ x y, x ≠ y ∧ closure e ∩ Γs.V = {x, y} := hloop.imp id (·.2)
  have hex : ∀ T : RespectfulTangle Γ θ, ∃ ins, IsDerivedSlope (PaintingOrDrawing.drawing Γ) Γ' θ
    T.1 ins :=
    fun T => exists_derivedSlope hS T.2.2 hrad.2.1
  have hexs : ∀ T : RespectfulTangle Γs θ, ∃ ins, IsDerivedSlope (PaintingOrDrawing.drawing Γs) Γ'
    θ T.1 ins :=
    fun T => exists_derivedSlope hS T.2.2 hrads.2.1
  choose i hi using hex
  choose j hj using hexs
  have hind : ∀ {G : Drawing S} (hEG : G.E.Nonempty) (_ : (PaintingOrDrawing.drawing
    G).IsRadialDrawing Γ')
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))), GM10.IsTangle G.toHypergraph θ T →
      (PaintingOrDrawing.drawing G).IsRespectful θ T → ∀ ins, IsDerivedSlope
        (PaintingOrDrawing.drawing G) Γ' θ T ins →
      T = inducedPretangle (PaintingOrDrawing.drawing G) Γ' θ ins := fun {G} hEG hr T ht hre ins hd
        =>
    (theorem_6_3_proof S hS inferInstance (PaintingOrDrawing.drawing G) Γ' θ T ins hr.1 hEG
      (IsTangle.isPretangle ht) hre hr hd).2
  let f : RespectfulTangle Γ θ → RespectfulTangle Γs θ := fun T =>
    ⟨_, (transfer hS hE hEs hrad hrads hl₂ T.2.1 T.2.2 (hi T)).1, (transfer hS hE hEs hrad hrads
      hl₂ T.2.1 T.2.2 (hi T)).2.1⟩
  let g : RespectfulTangle Γs θ → RespectfulTangle Γ θ := fun T =>
    ⟨_, (transfer hS hEs hE hrads hrad hl₁ T.2.1 T.2.2 (hj T)).1, (transfer hS hEs hE hrads hrad
      hl₁ T.2.1 T.2.2 (hj T)).2.1⟩
  have hfd : ∀ T, IsDerivedSlope (PaintingOrDrawing.drawing Γs) Γ' θ (f T).1 (i T) := fun T =>
    (transfer hS hE hEs hrad hrads hl₂ T.2.1 T.2.2 (hi T)).2.2
  have hgd : ∀ T, IsDerivedSlope (PaintingOrDrawing.drawing Γ) Γ' θ (g T).1 (j T) := fun T =>
    (transfer hS hEs hE hrads hrad hl₁ T.2.1 T.2.2 (hj T)).2.2
  have hu : ∀ T, ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ → j (f T) C
    = i T C := fun T =>
    derived_unique (Γ := PaintingOrDrawing.drawing Γs) hS (IsTangle.isPretangle
      (f T).2.1) hrads.2.1.1 (hj (f T)) (hfd T)
  have hv : ∀ T, ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ → i (g T) C
    = j T C := fun T =>
    derived_unique (Γ := PaintingOrDrawing.drawing Γ) hS (IsTangle.isPretangle
      (g T).2.1) hrad.2.1.1 (hi (g T)) (hgd T)
  let φ : RespectfulTangle Γ θ ≃ RespectfulTangle Γs θ :=
    { toFun := f
      invFun := g
      left_inv := fun T => Subtype.ext ((induced_congr (hu T)).trans
        (hind hE hrad T.1 T.2.1 T.2.2 (i T) (hi T)).symm)
      right_inv := fun T => Subtype.ext ((induced_congr (hv T)).trans
        (hind hEs hrads T.1 T.2.1 T.2.2 (j T) (hj T)).symm) }
  refine ⟨φ, fun T ins => ⟨fun hd => ?_, fun hd => ?_⟩⟩
  · have hsl := isSlope_of_derived (Γ := PaintingOrDrawing.drawing Γ) hS
      (IsTangle.isPretangle T.2.1) hrad.2.1.1 hd
    have he : (φ T).1 = inducedPretangle (PaintingOrDrawing.drawing Γs) Γ' θ ins :=
      induced_congr (derived_unique (Γ := PaintingOrDrawing.drawing Γ) hS
        (IsTangle.isPretangle T.2.1) hrad.2.1.1 (hi T) hd)
    rw [he]
    exact isDerivedSlope_induced hS hEs hrads hsl
  · have hsl := isSlope_of_derived (Γ := PaintingOrDrawing.drawing Γs) hS (IsTangle.isPretangle
      (φ T).2.1) hrads.2.1.1 hd
    have he : T.1 = inducedPretangle (PaintingOrDrawing.drawing Γ) Γ' θ ins :=
      (hind hE hrad T.1 T.2.1 T.2.2 (i T) (hi T)).trans
        (induced_congr (derived_unique (Γ := PaintingOrDrawing.drawing Γs) hS (IsTangle.isPretangle
          (φ T).2.1) hrads.2.1.1 (hfd T) hd))
    rw [he]
    exact isDerivedSlope_induced hS hE hrad hsl

/-- **Graph Minors XI, (6.6)** (page 93), the last sentence, for respectful tangles. -/
theorem theorem_6_6_exists (hS : IsClosedSurface S) (hE : Γ.E.Nonempty) (hEs : Γs.E.Nonempty)
    (hrad : (PaintingOrDrawing.drawing Γ).IsRadialDrawing Γ') (hrads :
      (PaintingOrDrawing.drawing Γs).IsRadialDrawing Γ')
    (hloop : θ ≠ 2 ∨ (∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y}) ∧
      ∀ e ∈ Γs.E, ∃ x y, x ≠ y ∧ closure e ∩ Γs.V = {x, y}) :
    Nonempty (RespectfulTangle Γ θ) ↔ Nonempty (RespectfulTangle Γs θ) := by
  obtain ⟨φ, -⟩ := theorem_6_6_proof hS hE hEs hrad hrads hloop
  exact ⟨fun ⟨T⟩ => ⟨φ T⟩, fun ⟨T⟩ => ⟨φ.symm T⟩⟩

/-- **Graph Minors XI, (4.1)** (page 78): a `θ`-representative 2-cell painting or drawing in a
connected surface other than
the sphere has a unique respectful tangle of order `θ`. -/
theorem theorem_4_1_proof {Γ : PaintingOrDrawing S} (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
  (hθ : 1 ≤ θ)
    (hT2 : Γ.IsTwoCell) (hrep : Γ.IsRepresentative θ) :
    ∃! T, GM10.IsTangle Γ.toHypergraph θ T ∧ Γ.IsRespectful θ T := by
  classical
  have hE : Γ.E.Nonempty := edge_nonempty_any hS hns hT2
  obtain ⟨Γ', hrad⟩ := exists_radialDrawing hS hT2
  have hb := bipartite_of_preRadial hrad.2.1
  have hbdS : ∀ F : Set S, Disjoint F (bd S) := fun F => disjoint_left.mpr fun x _ hx => hx
    (hS.2.2 x)
  -- Each short circuit of `Γ'` bounds a disc, since `Γ` is `θ`-representative.
  have hex : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ →
      ∃ Δ, IsClosedDisc Δ ∧ subBd Δ = C.U := by
    intro C hC hCs hl
    have hN : Γ.IsNormal C.U := fun x hx =>
      hrad.2.1.1.subset ⟨hx.2, hCs.U_subset hx.1⟩
    have hsub : C.U ∩ Γ.V ⊆ Γ.V ∩ C.V := by
      rintro x ⟨hxC, hxV⟩
      refine ⟨hxV, ?_⟩
      by_contra hn
      obtain ⟨e, he, hxe⟩ := C.exists_edge_of_mem hxC hn
      exact ((hCs.2 he).2.1 hxe).2 (hrad.2.1.2.1 hxV)
    have hk : (C.U ∩ Γ.V).ncard < θ := by
      have h₁ := two_mul_ncard_le_length Γ.V hb hC hCs
      have h₂ := ncard_le_ncard hsub (C.finite_V.subset inter_subset_right)
      omega
    have hF := IsCircuit.isOArc_U hC
    obtain ⟨Δ, -, hΔ, hbΔ⟩ := (epstein S univ C.U (IsClosedSurface.isSurface hS) inferInstance hF
      (subset_univ _)
      (hbdS _)).1 (hrep.2 C.U hF hN hk)
    exact ⟨Δ, hΔ, by rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hΔ, hbΔ]⟩
  let ins : Drawing S → Set S := fun C => if h : C.IsCircuit ∧ C.IsSubdrawing Γ'
    ∧ C.length < 2 * θ then
    (hex C h.1 h.2.1 h.2.2).choose else ∅
  have hins : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ →
      IsClosedDisc (ins C) ∧ subBd (ins C) = C.U := fun C hC hCs hl => by
    have h : C.IsCircuit ∧ C.IsSubdrawing Γ' ∧ C.length < 2 * θ := ⟨hC, hCs, hl⟩
    simp only [ins, h, and_self, dite_true]
    exact (hex C hC hCs hl).choose_spec
  have hbd : ∀ {Δ : Set S}, IsClosedDisc Δ → discBd Δ = subBd Δ := fun hΔ => by
    rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hΔ]
  have hsl : IsSlope Γ' (2 * θ) ins := by
    refine isSlope_of_mono hS (by omega) hins ?_ fun h => absurd h hns
    intro C₁ C₂ h₁ s₁ l₁ h₂ s₂ l₂ hsub
    obtain ⟨d₁, b₁⟩ := hins C₁ h₁ s₁ l₁
    obtain ⟨d₂, -⟩ := hins C₂ h₂ s₂ l₂
    exact disc_subset_of_bd hS hns d₁ d₂ (by rw [hbd d₁, b₁]; exact hsub)
  obtain ⟨h₁, h₂, h₃⟩ := theorem_6_1_proof hS hE hrad hθ hsl
  refine ⟨_, ⟨(theorem_6_4_proof hS hns hT2 h₁ h₂).2, h₂⟩, fun T hT => ?_⟩
  obtain ⟨ins', hd⟩ := exists_derivedSlope hS hT.2 hrad.2.1
  have hTi := (theorem_6_3_proof S hS inferInstance Γ Γ' θ T ins' hrad.1 hE
    (IsTangle.isPretangle hT.1) hT.2 hrad hd).2
  refine hTi.trans (induced_congr fun C hC hCs hl => ?_)
  obtain ⟨d, b, -⟩ := hd C hC hCs hl
  obtain ⟨d', b'⟩ := hins C hC hCs hl
  exact eq_of_discBd_eq (IsClosedSurface.isSurface hS) hns d d' (by rw [hbd d, hbd d', b, b'])

end GraphMinor.GM11
