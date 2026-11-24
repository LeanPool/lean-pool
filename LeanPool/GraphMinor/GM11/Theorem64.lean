/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingFlat
public import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Theorem (6.4) of Graph Minors XI

Graph Minors XI, (6.4), page 90. Claims (1) and (2) of the proof are in `Section64.lean` and
`Section64b.lean`.

`edge_nonempty` is the first line of the proof: "Since $\Gamma$ is 2-cell and $\Sigma$ is not a
sphere, it follows that
$E(\Gamma) \ne \emptyset$."

For the last sentence, the paper shows that `U(K_e)` includes no non-null-homotopic `O`-arc when `e`
has few ends.
We use (2) in place of that: if `(Γ \ e, K_e) ∈ 𝒯`, then (1) and (2) give a non-null-homotopic
`O`-arc in
`U(K_e) - U(Γ \ e) ⊆ e`, and an edge includes no `O`-arc.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A finite set in a `T₁` space is flat, since each path in it is constant. -/
theorem flat_of_finite [T1Space S] {Z : Set S} (hZ : Z.Finite) : Flat Z := by
  have hconst : ∀ {a b : S} (p : Path a b), (∀ u, p u ∈ Z) → ∀ u, p u = a := fun {a b} p hp u => by
    by_contra hu
    obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp (isPreconnected_range p.continuous) {a}
      (Z \ {a})
      isClosed_singleton (hZ.subset sdiff_subset).isClosed (fun x hx => by
        obtain ⟨v, rfl⟩ := hx
        by_cases h : p v = a
        · exact Or.inl h
        · exact Or.inr ⟨hp v, h⟩) ⟨a, ⟨0, by simp⟩, rfl⟩ ⟨p u, ⟨u, rfl⟩, hp u, hu⟩
    exact hz₂.2 hz₁
  intro a b p q hp hq
  have : p = q := Path.ext (funext fun u => (hconst p hp u).trans (hconst q hq u).symm)
  rw [this]

variable [T2Space S] [ConnectedSpace S]

/-- An edge of a drawing includes no `O`-arc. -/
theorem not_oArc_subset_edge {Γ : Drawing S} {e F : Set S} (he : e ∈ Γ.E) (hF : IsOArc F)
  (hFe : F ⊆ e) : False := by
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  have hc := hγ.cont e he
  have hFc : IsCompact F := isCompact_of_isOArc hF
  have hP : IsCompact (γ e ⁻¹' F) := (hFc.isClosed.preimage hc).isCompact
  obtain ⟨x, hx⟩ := (infinite_of_isOArc hF).nonempty
  obtain ⟨t, ht, rfl⟩ : x ∈ γ e '' Ioo 0 1 := (hγ.image e he).symm ▸ hFe hx
  have hne : (γ e ⁻¹' F).Nonempty := ⟨t, hx⟩
  obtain ⟨a, ha, hale⟩ := hP.exists_isLeast hne
  obtain ⟨b, hb, hble⟩ := hP.exists_isGreatest hne
  have hIoo : ∀ u, u ∈ γ e ⁻¹' F → u ∈ Ioo (0 : I) 1 := fun u hu => by
    constructor
    · refine lt_of_le_of_ne (unitInterval.nonneg u) fun h => ?_
      exact edge_notMem_V he (hFe hu) (h ▸ hγ.zero e he)
    · refine lt_of_le_of_ne (unitInterval.le_one u) fun h => ?_
      exact edge_notMem_V he (hFe hu) (h.symm ▸ hγ.one e he)
  have hab : a.1 ≤ b.1 := hale hb
  have hne' : a.1 ≠ b.1 := fun h => by
    have hsub : F ⊆ {γ e a} := fun y hy => by
      obtain ⟨u, -, rfl⟩ : y ∈ γ e '' Ioo 0 1 := (hγ.image e he).symm ▸ hFe hy
      have h₁ : a.1 ≤ u.1 := hale hy
      have h₂ : u.1 ≤ b.1 := hble hy
      have : u = a := Subtype.ext (by linarith)
      rw [this]
      rfl
    exact (infinite_of_isOArc hF) ((finite_singleton _).subset hsub)
  let m : I → I := fun u => ⟨a.1 + u.1 * (b.1 - a.1), by
    have := u.2.1; have := a.2.1; nlinarith, by
    have := u.2.2; have := b.2.2; nlinarith⟩
  have hm : Continuous m := Continuous.subtype_mk (by fun_prop) _
  have hmI : ∀ u, m u ∈ Ioo (0 : I) 1 := fun u => by
    have ha₀ := hIoo a ha
    have hb₀ := hIoo b hb
    have h₁ : a.1 ≤ (m u).1 := by
      have := u.2.1
      simp only [m]
      nlinarith
    have h₂ : (m u).1 ≤ b.1 := by
      have := u.2.2
      simp only [m]
      nlinarith
    exact ⟨lt_of_lt_of_le ha₀.1 h₁, lt_of_le_of_lt h₂ hb₀.2⟩
  have hinj : Function.Injective (fun u => γ e (m u)) := fun u v h => by
    have h₁ := hγ.inj e he (hmI u) (hmI v) h
    have h₂ : a.1 + u.1 * (b.1 - a.1) = a.1 + v.1 * (b.1 - a.1) := congrArg Subtype.val h₁
    have h₃ : b.1 - a.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne')
    exact Subtype.ext (mul_right_cancel₀ h₃ (add_left_cancel h₂))
  refine not_oArc_subset_arc (hc.comp hm) hinj hF fun y hy => ?_
  obtain ⟨u, -, rfl⟩ : y ∈ γ e '' Ioo 0 1 := (hγ.image e he).symm ▸ hFe hy
  have h₁ : a.1 ≤ u.1 := hale hy
  have h₂ : u.1 ≤ b.1 := hble hy
  have hd : 0 < b.1 - a.1 := sub_pos.mpr (lt_of_le_of_ne hab hne')
  refine ⟨⟨(u.1 - a.1) / (b.1 - a.1), div_nonneg (by linarith) hd.le,
    (div_le_one hd).mpr (by linarith)⟩, ?_⟩
  have : m ⟨(u.1 - a.1) / (b.1 - a.1), div_nonneg (by linarith) hd.le, (div_le_one hd).mpr
    (by linarith)⟩ = u :=
    Subtype.ext (by
      simp only [m]
      field_simp
      ring)
  exact congrArg (γ e) this

/-- The first line of the proof of (6.4) (page 90). -/
theorem edge_nonempty (hS : IsClosedSurface S) (hns : ¬ IsSphere S) {Γ : Drawing S}
    (hT2 : (PaintingOrDrawing.drawing Γ).IsTwoCell) : Γ.E.Nonempty := by
  classical
  by_contra hE
  have hE' : Γ.E = ∅ := not_nonempty_iff_eq_empty.mp hE
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hUV : Γ.U = Γ.V := by
    rw [Γ.U_eq, hE']
    simp
  obtain ⟨z, -, hz⟩ := exists_notMem_U (Γ := Γ) hS isOpen_univ univ_nonempty
  obtain ⟨r, hr, hzr⟩ := exists_region_of_notMem hz
  have hr' : Γ.Vᶜ ⊆ r := by
    have hcn : IsPreconnected (univ \ Γ.V) := isPreconnected_sdiff_finite hS isOpen_univ
      isPreconnected_univ Γ.finite_V
    have : Γ.Vᶜ = univ \ Γ.V := by simp [compl_eq_univ_sdiff]
    rw [this]
    exact subset_region hr hcn (disjoint_left.mpr fun x hx h => hx.2 (hUV ▸ h)) ⟨mem_univ _,
      hUV ▸ hz⟩ hzr
  obtain ⟨Sep, hSep, hdisj⟩ := Γ.finite_V.t2_separation
  have hgood : ∀ s ∈ Γ.V, ∃ E : Set S, IsOpen E ∧ s ∈ E ∧ E ⊆ Sep s ∧ IsSimplyConnectedSet E
    := fun s _ => by
    obtain ⟨D, D', hD, hD'o, hsD', hD'D, hDO, hb⟩ := exists_closedDisc_nbhd hS (hSep s).2 (hSep s).1
    have hD' : D' = D \ discBd D := by
      rw [← hb]
      ext x
      constructor
      · exact fun h => ⟨hD'D h, fun h' => h'.2 h⟩
      · rintro ⟨h₁, h₂⟩
        by_contra h
        exact h₂ ⟨h₁, h⟩
    exact ⟨D', hD'o, hsD', hD'D.trans hDO, IsOpenDisc.isSimplyConnectedSet
      (hD' ▸ isOpenDisc_interior hS hD)⟩
  choose! E hEo hsE hESep hEs using hgood
  let O : {s // s ∈ Γ.V} → Set S := fun s => E s.1
  have hfl : Flat (⋃ s, O s) := by
    refine flat_iUnion_cover (flat_of_finite Γ.finite_V) O Subtype.val (fun s => hEo s.1 s.2)
      (fun s => hsE s.1 s.2)
      (fun s => (hEs s.1 s.2).1) (fun s => IsSimplyConnectedSet.flat (hEs s.1 s.2)) fun i j y hy
        hy' => ?_
    obtain rfl : i = j := Subtype.ext (by
      by_contra hne
      exact disjoint_left.mp (hdisj i.2 j.2 hne) (hESep _ i.2 hy) (hESep _ j.2 hy'))
    have hj := (hEs i.1 i.2).1.joinedIn _ (hsE i.1 i.2) y hy
    refine ⟨Cl.mk hj.somePath, (Cl.mk hj.somePath).symm, ⟨_, hj.somePath_mem, rfl⟩,
      Arw.symm ⟨_, hj.somePath_mem, rfl⟩, ?_⟩
    rw [cl_trans_symm]
    exact arw_refl i.2
  have hcpt : CompactSpace S := hS.1
  have hCc : IsCompact (⋃ s, O s)ᶜ := (isOpen_iUnion fun s : {s // s ∈ Γ.V}
    => hEo s.1 s.2).isClosed_compl.isCompact
  have hCr : (⋃ s, O s)ᶜ ⊆ r := fun x hx => hr' fun hxV => hx (mem_iUnion.mpr ⟨⟨x, hxV⟩, hsE x hxV⟩)
  obtain ⟨Δ, hΔ, -, hCΔ⟩ := exists_closedDisc_of_isCompact (hT2.2 r hr) hCc hCr
  exact not_flat_compl_disc hS hns hΔ (fun x hx => by
    by_contra h
    exact hx (hCΔ h)) hfl

variable {Γ : PaintingOrDrawing S} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}

/-- An `O`-arc in an edge of a painting or drawing is null-homotopic. For a drawing there is no such
`O`-arc, and a cell
has a closed disc as its closure. -/
theorem null_of_subset_edge {e F : Set S} (he : e ∈ Γ.E) (hF : IsOArc F)
  (hFe : F ⊆ e) : IsNullHomotopicOArc F := by
  cases Γ with
  | painting Γ =>
    exact isNullHomotopicOArcIn_of_subset_disc hF (subset_univ _) (Cell.isClosedDisc_closure he)
      (hFe.trans subset_closure)
  | drawing Γ => exact (not_oArc_subset_edge he hF hFe).elim

/-- The first line of the proof of (6.4) (page 90), for a painting or drawing. A painting with no
cell has the same
regions as the drawing of its vertices. -/
theorem edge_nonempty_any (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
  (hT2 : Γ.IsTwoCell) : Γ.E.Nonempty := by
  cases Γ with
  | drawing Γ => exact edge_nonempty hS hns hT2
  | painting Γ =>
    by_contra hE
    have hE' : Γ.E = ∅ := not_nonempty_iff_eq_empty.mp hE
    have hUV : Γ.U = Γ.V := by
      refine subset_antisymm (fun x hx => ?_) Γ.V_subset_U
      rcases Cell.mem_V_or_cell Γ hx with h | ⟨e, he, -⟩
      · exact h
      · rw [hE'] at he
        exact he.elim
    let D : Drawing S := pointsDrawing Γ.finite_V
    have hDU : D.U = Γ.U := by rw [hUV]; simp [D, pointsDrawing]
    have hDE : D.E = ∅ := by
      refine eq_empty_of_forall_notMem ?_
      rintro C ⟨⟨x, hx⟩, hsub, -⟩
      have := hsub hx
      exact this.2 this.1
    have hR : D.R = Γ.R := by
      change componentsIn (univ \ D.U) = componentsIn (univ \ Γ.U)
      rw [hDU]
    have := edge_nonempty hS hns (Γ := D) ⟨hT2.1, fun r hr => hT2.2 r (show r ∈ Γ.R from hR ▸ hr)⟩
    rw [hDE] at this
    exact this.ne_empty rfl

omit [T2Space S] in
/-- **Graph Minors XI, (6.4)** (page 90). -/
theorem theorem_6_4_proof (hS : IsClosedSurface S) (hns : ¬ IsSphere S) (hT2 : Γ.IsTwoCell)
    (hT : IsPretangle Γ.toHypergraph θ T) (hresp : Γ.IsRespectful θ T) :
    (∀ A B : Hypergraph S (Set S), Γ.toHypergraph.IsSeparation A B → separationOrder A B < θ →
      ((A, B) ∈ T ↔ ∀ F : Set S, F ⊆ PaintingOrDrawing.underlying A → IsOArc F
        → IsNullHomotopicOArc F) ∧
      ((A, B) ∈ T ↔ ∃ F : Set S, IsOArc F ∧
        F ⊆ PaintingOrDrawing.underlying B \ PaintingOrDrawing.underlying A
          ∧ ¬ IsNullHomotopicOArc F)) ∧
      GM10.IsTangle Γ.toHypergraph θ T := by
  have ht2 : T2Space S := hS.2.1
  have hE : Γ.E.Nonempty := edge_nonempty_any hS hns hT2
  obtain ⟨Γ', hrad⟩ := exists_radialDrawing hS hT2
  obtain ⟨ins, hd⟩ := exists_derivedSlope hS hresp hrad.2.1
  have h₁ : ∀ {A B : Hypergraph S (Set S)}, Γ.toHypergraph.IsSeparation A B
    → separationOrder A B < θ → (A, B) ∈ T →
      ∀ F : Set S, F ⊆ PaintingOrDrawing.underlying A → IsOArc F → IsNullHomotopicOArc F :=
    fun hsep hord hm F hFA hF => no_oArc_of_mem hS hns hE hT2 hT hresp hrad hd hsep hord hm hF hFA
  have h₂ : ∀ {A B : Hypergraph S (Set S)}, Γ.toHypergraph.IsSeparation A B
    → separationOrder A B < θ →
      (∀ F : Set S, F ⊆ PaintingOrDrawing.underlying A → IsOArc F → IsNullHomotopicOArc F) →
      ∃ F : Set S, IsOArc F ∧ F ⊆ PaintingOrDrawing.underlying B \ PaintingOrDrawing.underlying A ∧
        ¬ IsNullHomotopicOArc F :=
    fun hsep hord hA => exists_oArc_of_null_any hS hns hE hrad hT.one_le hd hsep hord hA
  have h₃ : ∀ {A B : Hypergraph S (Set S)}, Γ.toHypergraph.IsSeparation A B
    → separationOrder A B < θ →
      (∃ F : Set S, IsOArc F ∧ F ⊆ PaintingOrDrawing.underlying B \ PaintingOrDrawing.underlying A ∧
        ¬ IsNullHomotopicOArc F) → (A, B) ∈ T := fun hsep hord ⟨F, hF, hFB, hn⟩ => by
    refine (hT.axiom1 hsep hord).resolve_right fun hm => hn ?_
    exact h₁ hsep.symm (by rwa [GM10.separationOrder_comm]) hm F (hFB.trans sdiff_subset) hF
  refine ⟨fun A B hsep hord => ⟨⟨h₁ hsep hord, fun h => h₃ hsep hord (h₂ hsep hord h)⟩,
    ⟨fun h => h₂ hsep hord (h₁ hsep hord h), h₃ hsep hord⟩⟩, ?_⟩
  refine (GM10.theorem_2_7_proof hT.one_le hT.isSeparation hT.order_lt hT.axiom1 hT.axiom2).mpr fun
    e he hsize => ?_
  have hs := GM10.isSeparation_edgeHypergraph_deleteEdges he
  have ho : separationOrder (GM10.edgeHypergraph Γ.toHypergraph e) (Γ.toHypergraph.deleteEdges {e})
    < θ := by
    rwa [GM10.separationOrder_edgeHypergraph_deleteEdges]
  refine (hT.axiom1 hs ho).resolve_right fun hm => ?_
  obtain ⟨F, hF, hFs, hnn⟩ := h₂ hs.symm (by rwa [GM10.separationOrder_comm]) (h₁ hs.symm
    (by rwa [GM10.separationOrder_comm]) hm)
  refine hnn (null_of_subset_edge (Γ.toHypergraph_edgeSet ▸ he) hF fun x hx => ?_)
  obtain ⟨hxK, hxn⟩ := hFs hx
  rcases hxK with hx' | ⟨f, hf, hxf⟩
  · exact (hxn (Or.inl (Γ.toHypergraph.vertex_mem_of_inc hx'))).elim
  · obtain rfl : f = e := hf
    exact hxf

end GraphMinor.GM11
