/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15i
public import LeanPool.GraphMinor.GM19.Section11g
public import LeanPool.GraphMinor.GM19.Section5i
public import LeanPool.GraphMinor.GM19.FragmentForm
public import LeanPool.GraphMinor.GM19.FreeFrame

/-!
# Graph Minors XIX, (15.2): bites and the border edges

Step (4) of the proof of (15.2) says that no short circuit through a pole holds many of the ends of
the images of the border edges. We need to grow a bite so that it
holds a given border edge, as the paper does when it writes `l(β(e), s₁) ≤ ½|E(F)| + 2`. A border
edge lies in a bite of length at most six (`exists_bite_of_edge`), and two bites that share a
point of the cuff lie in one bite (`IsSideSetting.exists_bite_superset`).

The paper shows that no `β(e)` lies in `ins(F)`, and then says that `N(r*) ∩ ins(F) = V(Φ) ∩
ins(F)`. An end of `β(e)` may still lie on `F`. So we work with an edge that has an end in `ins(F)`,
and not with an edge that lies in
`ins(F)`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β} {D : TangleDatum cap χ}

/-- A connected set in an `O`-arc that meets a line of the `O`-arc but misses its ends lies in the
line. -/
theorem subset_line_of_isPreconnected {T : Type} [TopologicalSpace T] [T2Space T] {c L J : Set T}
  {a b : T} (hc : IsOArc c) (hl : IsLineWithEnds L a b) (hLc : L ⊆ c) (hJ : IsPreconnected J)
    (hJc : J ⊆ c) (ha : a ∉ J) (hb : b ∉ J) {y : T} (hy : y ∈ J) (hyL : y ∈ L) : J ⊆ L := by
  classical
  obtain ⟨f, h0, hpi, himg⟩ := exists_angle_of_line hc hl hLc
  have hp := Real.pi_pos
  by_contra hn
  obtain ⟨z, hzJ, hzL⟩ := not_subset.mp hn
  have hC₁ : IsClosed L := himg ▸ (isCompact_Icc.image (continuous_cuffAngle f)).isClosed
  have hC₂ : IsClosed (cuffPoint f '' Icc Real.pi (2 * Real.pi)) := (isCompact_Icc.image
    (continuous_cuffAngle f)).isClosed
  have hcov : J ⊆ L ∪ cuffPoint f '' Icc Real.pi (2 * Real.pi) := fun w hw => by
    obtain ⟨t, ht, rfl⟩ := exists_cuffAngle_eq f 0 (hJc hw)
    by_cases h : t ≤ Real.pi
    · exact .inl (himg ▸ ⟨t, ⟨ht.1, h⟩, rfl⟩)
    · exact .inr ⟨t, ⟨(not_le.1 h).le, by linarith [ht.2]⟩, rfl⟩
  have hzC : z ∈ cuffPoint f '' Icc Real.pi (2 * Real.pi) := (hcov hzJ).resolve_left hzL
  obtain ⟨w, hwJ, hw₁, hw₂⟩ := isPreconnected_closed_iff.mp hJ _ _ hC₁ hC₂ hcov ⟨y, hy, hyL⟩ ⟨z,
    hzJ, hzC⟩
  rw [← himg] at hw₁
  obtain ⟨t₁, ht₁, rfl⟩ := hw₁
  obtain ⟨t₂, ht₂, he⟩ := hw₂
  by_cases h2 : t₂ = 2 * Real.pi
  · have : cuffPoint f t₂ = a := by
      rw [← h0, h2]
      have := cuffAngle_add_two_pi f 0
      rwa [zero_add] at this
    exact ha (by rw [← this, he]; exact hwJ)
  · have ht₂' : t₂ ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
      ⟨by linarith [ht₂.1], by simpa only [zero_add] using lt_of_le_of_ne ht₂.2 h2⟩
    have e := cuffAngle_injOn f ht₂' ⟨ht₁.1, by linarith [ht₁.2]⟩ he
    have : t₁ = Real.pi := le_antisymm ht₁.2 (by linarith [ht₂.1])
    exact hb (by rw [← hpi, ← this]; exact hwJ)

namespace TangleDatum

omit [T2Space S] [T2Space Shat] in
/-- A short bite that holds two border edges bounds their border distance. -/
theorem borderEdgeDist_le_of_bite {r : Shat} {c₁ c₂ : Set S} {C : Drawing Shat}
  (hC : D.IsBiteAt r C) (h₁ : cap.emb '' c₁ ⊆ D.ins C) (h₂ : cap.emb '' c₂ ⊆ D.ins C) :
    D.borderEdgeDist r c₁ c₂ ≤ C.E.ncard / 2 := by
  classical
  have : ConnectedSpace Shat := cap.connected
  unfold borderEdgeDist
  rw [dite_eq_left ⟨C, hC, h₁, h₂⟩]
  have e := D.ncard_E_eq_hat hC.is_circuit
  exact Nat.sInf_le ⟨C, hC, h₁, h₂, by omega⟩

omit [T2Space S] [T2Space Shat] in
/-- The pole in the disc of a cuff is the one whose region is that disc. -/
theorem pole_eq_of_mem_cuffDisc {r r' : Shat} (hr : r ∈ D.rad.poles) {Θ : Set S}
  (hΘ : Θ ∈ cuffs S) (hreg : D.rad.regionOf r = cap.cuffDisc Θ) (hr' : r' ∈ D.rad.poles)
    (hd : r' ∈ cap.cuffDisc Θ) : r' = r := by
  obtain ⟨Θ', hΘ', hreg', hd'⟩ := D.rad.pole_cases hr'
  have e : Θ' = Θ := by
    by_contra hne
    exact disjoint_left.mp (cap.cuffDisc_disjoint Θ' hΘ' Θ hΘ hne) (subset_closure hd')
      (subset_closure hd)
  subst e
  have hm := D.rad.regionOf_mem hr.1
  have hm' := D.rad.regionOf_mem hr'.1
  obtain ⟨w, -, huniq⟩ := D.rad.isPreRadial.2.2.1 _ hm.1
  rw [hreg'] at hm'
  rw [hreg] at huniq hm
  exact (huniq r' ⟨hm'.2, hr'.1.1⟩).trans (huniq r ⟨hm.2, hr.1.1⟩).symm

end TangleDatum

namespace TangleDatum.IsSideSetting

variable {side Θ : Set S} {r : Shat} {N : ℕ} (X : D.IsSideSetting side Θ r N)
include X

/-- A bite can be replaced by one no longer, with a bigger inside and no vertex in the outer arc of
the cuff. -/
theorem exists_tight_bite (hS : IsSurface S) {F : Drawing Shat} (hb : D.IsBiteAt r F)
  (hc : F.E.ncard ≤ 2 * N) :
    ∃ F', D.IsBiteAt r F' ∧ F'.E.ncard ≤ F.E.ncard ∧ D.ins F ⊆ D.ins F'
      ∧ ∃ v₁ v₂ Β L A A' Di Do, D.IsBiteShape r Θ F' v₁ v₂ Β L A A' Di Do ∧ Disjoint F'.V A' := by
  induction hk : F.E.ncard using Nat.strong_induction_on generalizing F with
  | _ k ih =>
    obtain ⟨v₁, v₂, Β, L, A, A', Di, Do, hs⟩ := X.shape hS hb hc
    by_cases hdis : Disjoint F.V A'
    · exact ⟨F, hb, hk.le, Subset.rfl, v₁, v₂, Β, L, A, A', Di, Do, hs, hdis⟩
    obtain ⟨x, hxV, hxA⟩ := not_disjoint_iff.mp hdis
    obtain ⟨F', hF', hlt, hsub, hr⟩ := X.exists_shorter hS hs hxV hxA
    have hb' : D.IsBiteAt r F' := ⟨hb.pole_mem, hF', by have := hb.card_lt; omega, hr⟩
    obtain ⟨F'', h₁, h₂, h₃, h₄⟩ := ih F'.E.ncard (hk ▸ hlt) hb' (by omega) rfl
    exact ⟨F'', h₁, by omega, hsub.trans h₃, h₄⟩

omit X in
omit [T2Space S] in
omit [T2Space Shat] in
/-- A point of a circuit of `Γ*` that lies on another circuit of `Γ*` gives a common vertex other
than `r`, if it is not `r`. -/
theorem exists_common_vertex {F G : Drawing Shat} (hF : F.IsCircuitOf D.rad.G)
  (hG : G.IsCircuitOf D.rad.G) {z : Shat} (hzF : z ∈ F.U) (hzG : z ∈ G.U) (hzr : z ≠ r) :
    ∃ x ∈ F.V, x ∈ G.V ∧ x ≠ r := by
  classical
  by_cases hzV : z ∈ D.rad.G.V
  · exact ⟨z, mem_V_of_mem_U_sub hF.1 hzF hzV, mem_V_of_mem_U_sub hG.1 hzG hzV, hzr⟩
  obtain ⟨e, he, hze⟩ := D.rad.G.exists_edge_of_mem (hF.1.U_subset hzF) hzV
  have hmem : ∀ C : Drawing Shat, C.IsSubdrawing D.rad.G → z ∈ C.U → e ∈ C.E := fun C hC hzC => by
    obtain ⟨f, hf, hzf⟩ := C.exists_edge_of_mem hzC (fun h => hzV (hC.1 h))
    exact (D.rad.G.edge_eq_of_mem (hC.2 hf) he hzf hze) ▸ hf
  have heF := hmem F hF.1 hzF
  have heG := hmem G hG.1 hzG
  obtain ⟨v, hvh, w, hwh, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e he
  have hends : ∀ C : Drawing Shat, e ∈ C.E → ∀ x, x ∈ closure e ∩ D.rad.G.V → x ∈ C.V
    := fun C hC' x hx => by
    by_contra hxC
    have : x ∈ closure e \ C.V := ⟨hx.1, hxC⟩
    rw [C.closure_diff_V hC'] at this
    exact (he.2.1 this).2 hx.2
  have hv : v ∈ closure e ∩ D.rad.G.V := hcap ▸ .inl rfl
  have hw : w ∈ closure e ∩ D.rad.G.V := hcap ▸ .inr rfl
  by_cases hvr : v = r
  · have hwr : w ≠ r := fun h => hwh.2 (h ▸ hvr ▸ hvh)
    exact ⟨w, hends F heF w hw, hends G heG w hw, hwr⟩
  · exact ⟨v, hends F heF v hv, hends G heG v hv, hvr⟩

omit [T2Space S] in
/-- Two bites at `r`, one with a vertex other than `r` inside the other, lie in one bite. If they
have a second common vertex we use `no_two_common_vertices`. If not, the first bite without `r` is
connected and misses the
second bite, so it lies inside the second bite. -/
theorem exists_bite_superset_of_vertex {F G : Drawing Shat}
  (hF : D.IsBiteAt r F) (hG : D.IsBiteAt r G) (hc : F.E.ncard + G.E.ncard ≤ 2 * N) {p : Shat}
    (hpF : p ∈ F.V) (hpr : p ≠ r) (hpG : p ∈ D.ins G) :
    ∃ C, D.IsBiteAt r C ∧ C.E.ncard ≤ F.E.ncard + G.E.ncard ∧ D.ins F ⊆ D.ins C ∧ D.ins G ⊆ D.ins C
      := by
  classical
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have : ConnectedSpace Shat := cap.connected
  have hrep : 1 ≤ D.rep := by have := X.rep_gt; omega
  by_cases hx : ∃ x ∈ F.V, x ∈ G.V ∧ x ≠ r
  · obtain ⟨x, hxF, hxG, hxr⟩ := hx
    obtain ⟨C, hC, hcard, i₁, i₂, hV⟩ := no_two_common_vertices X.rep_gt hF.is_circuit
      hG.is_circuit hc hxr hxF hxG hF.rstar_mem hG.rstar_mem
    have e₁ := IsCircuit.ncard_V hC.2
    have e₂ := IsCircuit.ncard_V hF.is_circuit.2
    have e₃ := IsCircuit.ncard_V hG.is_circuit.2
    have h₃ := ncard_le_ncard hV (F.finite_V.union G.finite_V)
    have h₄ := ncard_union_le F.V G.V
    have hrF := D.U_subset_ins hF.is_circuit hF.card_lt (F.V_subset_U hF.rstar_mem)
    exact ⟨C, X.bite_of_ins hC hcard (i₁ hrF), by omega, i₁, i₂⟩
  push Not at hx
  have hi := D.ins_spec hG.is_circuit hG.card_lt
  have hconn : IsPreconnected (F.U \ {r}) := (Surface.isPathConnected_oArc_diff
    (IsCircuit.isOArc_U hF.is_circuit.2) (F.V_subset_U hF.rstar_mem)).isConnected.isPreconnected
  have hdis : Disjoint (F.U \ {r}) (discBd (D.ins G)) := by
    rw [hi.2.2.2.1]
    refine disjoint_left.mpr fun z hz hzG => ?_
    obtain ⟨x, h₁, h₂, h₃⟩ := exists_common_vertex hF.is_circuit hG.is_circuit hz.1 hzG hz.2
    exact h₃ (hx x h₁ h₂)
  have hsub : F.U ⊆ D.ins G := by
    rcases hi.2.2.1.side hman hconn hdis with h | h
    · intro z hz
      by_cases hzr : z = r
      · exact hzr ▸ D.U_subset_ins hG.is_circuit hG.card_lt (G.V_subset_U hG.rstar_mem)
      · exact discInt_subset _ (h ⟨hz, hzr⟩)
    · exact absurd hpG (disjoint_left.mp h ⟨F.V_subset_U hpF, hpr⟩)
  have hmono := (D.isSlope hrep).monotone _ _ hF.is_circuit.2 hF.is_circuit.1 hF.card_lt
    hG.is_circuit.2 hG.is_circuit.1 hG.card_lt hsub
  exact ⟨G, hG, by omega, hmono, Subset.rfl⟩

omit X [T2Space S] in
/-- What a tight bite meets on the cuff is its arc. -/
theorem _root_.GraphMinor.GM19.TangleDatum.IsBiteShape.isPreconnected_cuff_inter_ins
 {F : Drawing Shat} {v₁ v₂ Β L A A' Di Do} (h : D.IsBiteShape r Θ F v₁ v₂ Β L A
    A' Di Do) (hdis : Disjoint F.V A') :
    IsPreconnected (cap.emb '' Θ ∩ D.ins F) := by
  classical
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have : ConnectedSpace Shat := cap.connected
  have hi := D.ins_spec h.circuit h.lt
  have hsubI : ∀ x ∈ D.biteArc r F, x ∈ cap.emb '' Θ ∧ x ∈ D.ins F := fun x hx => by
    obtain ⟨I, hI, hxI⟩ := hx
    have := hI.1 hxI
    exact ⟨closure_region_sdiff h.cuff h.reg ▸ this.2, this.1⟩
  have hfr : IsOpen (discInt (D.ins F)) := hi.2.2.1.isOpen_discInt hman
  have heq : cap.emb '' Θ ∩ D.ins F = D.biteArc r F := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => hsubI x hx
    obtain ⟨⟨y, hy, rfl⟩, hxi⟩ := hx
    by_contra hn
    have hA' : cap.emb y ∈ A' := by
      by_contra hA'
      exact hn (by
        rw [h.biteArc_eq]
        by_cases he : cap.emb y ∈ ({cap.emb v₁, cap.emb v₂} : Set Shat)
        · exact .inr he
        · rcases h.cover ⟨mem_image_of_mem _ hy, he⟩ with h' | h'
          · exact .inl h'
          · exact absurd h' hA')
    have hnotU : cap.emb y ∉ F.U := fun hU => by
      obtain ⟨-, hyF, -⟩ := D.rad.bd_point h.circuit.1 (cuff_subset_bd ⟨Θ, h.cuff⟩ hy) hU
      exact disjoint_left.mp hdis hyF hA'
    have hint : cap.emb y ∈ discInt (D.ins F) := ⟨hxi, by rwa [hi.2.2.2.1]⟩
    have hyD : cap.emb y ∈ closure (discInt Do) := by
      rw [closure_discInt h.do_]
      exact Surface.discBd_subset _ (h.bd_o ▸ Or.inl hA')
    obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp hyD _ hfr hint
    exact disjoint_left.mp h.out_ins hw₂ (discInt_subset _ hw₁)
  rw [heq, ← image_preimage_eq_of_subset (f := cap.emb) (s := D.biteArc r F) fun x hx
    => image_subset_range _ _ (hsubI x hx).1]
  exact (cap.isEmbedding.isInducing.isPreconnected_image).mpr (h.isPreconnected_biteArc)

/-- **Two bites at `r` that share a point of the cuff lie in one bite.** We may take the first
tight, so it meets the cuff in a connected set. Either an end of that set lies in the second bite,
or the second bite has a vertex in that set. -/
theorem exists_bite_superset (hS : IsSurface S) {F G : Drawing Shat} (hF : D.IsBiteAt r F)
  (hG : D.IsBiteAt r G) (hc : F.E.ncard + G.E.ncard ≤ 2 * N) {z : Shat} (hzΘ : z ∈ cap.emb '' Θ)
    (hzF : z ∈ D.ins F) (hzG : z ∈ D.ins G) :
    ∃ C, D.IsBiteAt r C ∧ C.E.ncard ≤ F.E.ncard + G.E.ncard ∧ D.ins F ⊆ D.ins C ∧ D.ins G ⊆ D.ins C
      := by
  classical
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨F', hF', hle, hsub, v₁, v₂, Β, L, A, A', Di, Do, hs, hdis⟩ := X.exists_tight_bite hS hF
    (by omega)
  have hcon := hs.isPreconnected_cuff_inter_ins hdis
  have hrr : ∀ {y : S}, cap.emb y ≠ r := fun {y} he => by
    have hrd : r ∈ cap.cuffDisc Θ := X.reg ▸ (D.rad.regionOf_mem X.pole.1).2
    exact cap.notMem_range X.cuff hrd ⟨y, he⟩
  have hv₁U : cap.emb v₁ ∈ F'.U := hs.Β_F (hs.meet ▸ mem_insert _ _ : cap.emb v₁ ∈ Β ∩ cap.emb ''
    Θ).1
  obtain ⟨-, hv₁F, -⟩ := D.rad.bd_point hs.circuit.1 (cuff_subset_bd ⟨Θ, hs.cuff⟩ hs.v₁_cuff) hv₁U
  have fin : ∀ {C}, D.IsBiteAt r C → C.E.ncard ≤ F'.E.ncard + G.E.ncard → D.ins F' ⊆ D.ins C
    → D.ins G ⊆ D.ins C →
      ∃ C, D.IsBiteAt r C ∧ C.E.ncard ≤ F.E.ncard + G.E.ncard ∧
        D.ins F ⊆ D.ins C ∧ D.ins G ⊆ D.ins C := by
    intro C h₁ h₂ h₃ h₄
    exact ⟨C, h₁, by omega, hsub.trans h₃, h₄⟩
  by_cases hv : cap.emb v₁ ∈ D.ins G
  · obtain ⟨C, h₁, h₂, h₃, h₄⟩ := X.exists_bite_superset_of_vertex hF' hG (by omega) hv₁F hrr hv
    exact fin h₁ h₂ h₃ h₄
  have hi := D.ins_spec hG.is_circuit hG.card_lt
  have hne : ∃ w, w ∈ cap.emb '' Θ ∩ D.ins F' ∧ w ∈ G.U := by
    by_contra hn
    push Not at hn
    have hd : Disjoint (cap.emb '' Θ ∩ D.ins F') (discBd (D.ins G)) := by
      rw [hi.2.2.2.1]
      exact disjoint_left.mpr hn
    rcases hi.2.2.1.side hman hcon hd with h | h
    · exact hv (discInt_subset _ (h ⟨mem_image_of_mem _ hs.v₁_cuff,
        D.U_subset_ins hs.circuit hs.lt hv₁U⟩))
    · exact disjoint_left.mp h ⟨hzΘ, hsub hzF⟩ hzG
  obtain ⟨w, ⟨⟨y, hy, rfl⟩, hwF⟩, hwG⟩ := hne
  obtain ⟨-, hyG, -⟩ := D.rad.bd_point hG.is_circuit.1 (cuff_subset_bd ⟨Θ, X.cuff⟩ hy) hwG
  obtain ⟨C, h₁, h₂, h₃, h₄⟩ := X.exists_bite_superset_of_vertex hG hF' (by omega) hyG hrr hwF
  exact fin h₁ (by omega) h₄ h₃

end TangleDatum.IsSideSetting

namespace TangleDatum

variable {P₀ : ColouredPainting χ} {n : ℕ} {b : Set S → Set S}

/-- The set `N(r*)` of step (4) of the proof of (15.2): the ends of the images of the edges of `Γ₀`
on a cuff. -/
def cuffEnds (P₀ : ColouredPainting χ) (b : Set S → Set S) (Θ : Set S) : Set S
  := {y | ∃ e ∈ P₀.Γ.E, e ⊆ Θ ∧ y ∈ tilde (b e)}

/-- An edge of `Γ₀` on a cuff has its image on a side of that cuff. -/
theorem exists_side_of_cuffEnds (hS : IsSurface S) (hb : D.IsEdgeMap P₀ n b) {Θ : Set S}
  (hΘ : Θ ∈ cuffs S) {e : Set S} (he : e ∈ P₀.Γ.E) (heΘ : e ⊆ Θ) :
    ∃ s ∈ χ.Φ.sides, s ⊆ Θ ∧ e ⊆ s ∧ b e ⊆ s ∧ (s ∉ χ.Φ.longSides → b e = s) := by
  obtain ⟨x, hx⟩ : e.Nonempty := he.1
  obtain ⟨s, hs, hes, hbs, -⟩ := hb.border he ⟨x, hx, cuff_subset_bd ⟨Θ, hΘ⟩ (heΘ hx)⟩
  obtain ⟨Θ', hΘ', hsΘ', -⟩ := χ.Φ.side_on_cuff hS hs
  obtain rfl : Θ' = Θ := cuffs_eq_of_mem hΘ' hΘ (hsΘ' (hes hx)) (heΘ hx)
  refine ⟨s, hs, hsΘ', hes, hbs, fun hl => ?_⟩
  have hss : s ∈ χ.Φ.shortSides := ⟨hs, fun h => hl ⟨hs, h⟩⟩
  obtain rfl := eq_short_of_subset P₀.fits he hss hes
  exact hb.short e hss

/-- **Step (4) of the proof of (15.2).** No short circuit of `Γ*` through or around the pole of a
cuff holds more than half its length of `N(r*)`. -/
theorem no_circuit_holds_cuffEnds (hS : IsSurface S) (hb : D.IsEdgeMap P₀ n b) (hn : 3 ≤ n)
  (hnr : n < D.rep) (hfree : ∀ C, ¬ D.IsFreeCircuit n C)
    (hfar : ∀ r₁ ∈ D.rad.poles, ∀ r₂ ∈ D.rad.poles, r₁ ≠ r₂ → n < D.vDist r₁ r₂) {r : Shat}
      (hr : r ∈ D.rad.poles) {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hreg : D.rad.regionOf r
        = cap.cuffDisc Θ)
    {F₀ : Drawing Shat} (hF₀ : F₀.IsCircuitOf D.rad.G) (hsm : F₀.E.ncard + 12 ≤ n)
      (hri : r ∈ D.ins F₀) (hlt : F₀.E.ncard < 2 * ((cap.emb '' cuffEnds P₀ b Θ) ∩ D.ins F₀).ncard)
        : False := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hbd : IsClosed (bd S) := (cuff_statement S hS).1
  have h3 := D.P.fits.internally_three_connected
  have hinj := cap.isEmbedding.injective
  have hNfin : (cuffEnds P₀ b Θ).Finite := by
    refine (P₀.Γ.finite_edges.biUnion (t := fun e => tilde (b e)) fun e he => D.P.Γ.finite_V.subset
      (D.P.Γ.tilde_subset_V (hb.mem e he))).subset ?_
    rintro y ⟨e, he, -, hy⟩
    exact mem_biUnion he hy
  have hΘo : IsOArc Θ := (cuff_statement S hS).2.2 Θ hΘ
  have hΘcl : IsClosed Θ := hΘo.isCompact.isClosed
  have hfree' : ∀ F : Drawing Shat, F.IsCircuitOf D.rad.G → F.E.ncard ≤ 2 * n → F.E.ncard < 2 *
    ((cap.emb '' cuffEnds P₀ b Θ) ∩ D.ins F).ncard → (cap.emb '' cuffEnds P₀ b Θ) ∩ D.ins F ⊆
      cap.emb '' χ.Φ.V → False := fun F hF hc hl hsub =>
    hfree F ⟨hF, hc, Or.inr (lt_of_lt_of_le hl (by
      have := ncard_le_ncard (s := (cap.emb '' cuffEnds P₀ b Θ) ∩ D.ins F) (t :=
        (cap.emb '' χ.Φ.V) ∩ D.ins F) (fun x hx => ⟨hsub hx, hx.2⟩) (χ.Φ.finite_V.image _
          |>.inter_of_left _)
      omega))⟩
  by_cases hlong : ∃ side ∈ χ.Φ.longSides, side ⊆ Θ
  swap
  · refine hfree' F₀ hF₀ (by omega) hlt ?_
    rintro _ ⟨⟨y, ⟨e, he, heΘ, hy⟩, rfl⟩, -⟩
    obtain ⟨s, hs, hsΘ, -, -, hshort⟩ := exists_side_of_cuffEnds hS hb hΘ he heΘ
    rw [hshort fun hl => hlong ⟨s, hl, hsΘ⟩] at hy
    exact mem_image_of_mem _ (χ.Φ.tilde_subset hbd hs hy)
  obtain ⟨side₀, hside₀, hs₀Θ⟩ := hlong
  have X : D.IsSideSetting side₀ Θ r n := ⟨h3, hside₀, hs₀Θ, hΘ, hr, hreg, hnr, hfar, hfree⟩
  have hri' := X.pole_mem hF₀ (by omega) hri
  obtain ⟨F, hbF, hle, hsub, v₁, v₂, Β, L, A, A', Di, Do, hs, hdis⟩ :=
    X.exists_tight_bite hS (⟨hr, hF₀, by omega, hri'⟩ : D.IsBiteAt r F₀) (by omega)
  have hmono : ((cap.emb '' cuffEnds P₀ b Θ) ∩ D.ins F₀).ncard ≤ ((cap.emb '' cuffEnds P₀ b Θ) ∩
    D.ins F).ncard :=
    ncard_le_ncard (fun x hx => ⟨hx.1, hsub hx.2⟩) ((hNfin.image _).inter_of_left _)
  have hF4 : 4 ≤ F.E.ncard := by
    have hp : ({cap.emb v₁, cap.emb v₂} : Set Shat) ⊆ F.V ∩ D.P.Γ.hatV cap := by
      have key : ∀ {v}, cap.emb v ∈ Β → v ∈ Θ → v ∈ D.P.Γ.V → cap.emb v ∈ F.V ∩ D.P.Γ.hatV cap
        := fun {v} h₁ h₂ h₃ =>
        ⟨(D.rad.bd_point hs.circuit.1 (cuff_subset_bd ⟨Θ, hΘ⟩ h₂) (hs.Β_F h₁)).2.1,
          mem_image_of_mem _ h₃⟩
      rintro x (rfl | hx)
      · exact key (hs.meet ▸ mem_insert _ _ : cap.emb v₁ ∈ Β ∩ cap.emb '' Θ).1 hs.v₁_cuff hs.v₁_mem
      · rw [mem_singleton_iff.mp hx]
        exact key (hs.meet ▸ mem_insert_of_mem _ rfl : cap.emb v₂ ∈ Β ∩ cap.emb '' Θ).1 hs.v₂_cuff
          hs.v₂_mem
    have := ncard_le_ncard hp (F.finite_V.subset inter_subset_left)
    rw [ncard_pair fun he => hs.ne (hinj he)] at this
    have e := D.ncard_E_eq_hat hs.circuit
    omega
  have hsmF : F.E.ncard + 12 ≤ n := by omega
  have grow : ∀ t ∈ D.P.Γ.E, t ⊆ Θ → ∀ B, D.IsBiteAt r B → B.E.ncard + 6 ≤ 2 * n
    → ∀ z ∈ closure t, cap.emb z ∈ D.ins B → ∃ C, D.IsBiteAt r C ∧ C.E.ncard ≤ B.E.ncard + 6
      ∧ D.ins B ⊆ D.ins C ∧ cap.emb '' t ⊆ D.ins C := by
    intro t ht htΘ B hB hBn z hz hzB
    obtain ⟨G, hG, hG6, hGt⟩ := exists_bite_of_edge hn (by omega) hfree hside₀ hs₀Θ hΘ hr hreg
      ht htΘ
    have hzG : cap.emb z ∈ D.ins G := by
      have hG' := (D.ins_spec hG.is_circuit hG.card_lt).2.2.1.isClosed
      refine closure_minimal hGt hG' ?_
      rw [(cap.isClosedEmbedding hS).closure_image_eq t]
      exact mem_image_of_mem _ hz
    have hzΘ : cap.emb z ∈ cap.emb '' Θ := by
      refine mem_image_of_mem _ ?_
      exact closure_minimal htΘ hΘcl hz
    obtain ⟨C, h₁, h₂, h₃, h₄⟩ := X.exists_bite_superset hS hB hG (by omega) hzΘ hzB hzG
    exact ⟨C, h₁, by omega, h₃, hGt.trans h₄⟩
  have hcΘ : IsOArc (cap.emb '' Θ) := cap.cuffDisc_bd Θ hΘ ▸ (cap.cuffDisc_closedDisc Θ
    hΘ).isOArc_discBd
  by_cases hY : (cap.emb '' cuffEnds P₀ b Θ) ∩ D.ins F ⊆ cap.emb '' χ.Φ.V
  · exact hfree' F hs.circuit (by omega) (by omega) hY
  obtain ⟨_, ⟨⟨y, ⟨e, he, heΘ, hy⟩, rfl⟩, hyi⟩, hyΦ⟩ := not_subset.mp hY
  obtain ⟨s, hs', hsΘ, hes, hbs, hshort⟩ := exists_side_of_cuffEnds hS hb hΘ he heΘ
  have hsl : s ∈ χ.Φ.longSides := by
    by_contra hl
    rw [hshort hl] at hy
    exact hyΦ (mem_image_of_mem _ (χ.Φ.tilde_subset hbd hs' hy))
  obtain ⟨m, f, g, c, r', u₀, u₁, u₀', u₁', hM⟩ := hb.side s hsl
  obtain ⟨x, hx⟩ : e.Nonempty := he.1
  have hcE : c = Θ := cuffs_eq_of_mem hM.cuff hΘ (hM.side_cuff (hes hx)) (hsΘ (hes hx))
  rw [hcE] at hM
  have hrE : r' = r := pole_eq_of_mem_cuffDisc hr hΘ hreg hM.pole hM.pole_disc
  rw [hrE] at hM
  obtain ⟨i, rfl⟩ := hM.all₀ e he hes
  have hgi := hM.map i
  obtain ⟨F₁, hF₁, hF₁c, hF₁i, hF₁g⟩ := grow _ (hb.mem _ he) (hbs.trans hsΘ) F hbF
    (by omega) y hy.1 hyi
  have hcorner : ∀ v ∈ tilde s, cap.emb v ∉ D.ins F := by
    intro v hv hvi
    have hvV := χ.Φ.tilde_subset hbd hs' hv
    obtain ⟨t, ht, hvt⟩ := χ.Φ.exists_short_side hS hvV
    obtain ⟨Θ', hΘ', htΘ', -⟩ := χ.Φ.side_on_cuff hS ht.1
    have hcl' : IsClosed Θ' := ((cuff_statement S hS).2.2 Θ' hΘ').isCompact.isClosed
    obtain rfl : Θ' = Θ := cuffs_eq_of_mem hΘ' hΘ (closure_minimal htΘ' hcl' hvt.1)
      (closure_minimal hsΘ hΘcl hv.1)
    obtain ⟨F₂, hF₂, hF₂c, hF₂i, hF₂t⟩ := grow t (D.P.fits.short_sides ht) htΘ' F₁ hF₁
      (by omega) v hvt.1 (hF₁i hvi)
    have h₁ := D.borderEdgeDist_le_of_bite hF₂ (hF₁g.trans hF₂i) hF₂t
    have h₂ := hM.far_short i t ht htΘ'
    rw [← hgi] at h₂
    omega
  obtain ⟨v, hv⟩ : (tilde s).Nonempty := by
    have h2 := (χ.Φ.side_shape s hs').1
    exact nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨w, -, htil, hline⟩ := χ.Φ.exists_line hs' hv
  have hwt : w ∈ tilde s := htil ▸ mem_insert_of_mem _ rfl
  have hJ : cap.emb '' Θ ∩ D.ins F ⊆ cap.emb '' closure s :=
    subset_line_of_isPreconnected hcΘ (hline.map_of_embedding cap.isEmbedding) (image_mono
      (closure_minimal hsΘ hΘcl))
      (hs.isPreconnected_cuff_inter_ins hdis) inter_subset_left (fun h => hcorner v hv h.2)
        (fun h => hcorner w hwt h.2)
      ⟨mem_image_of_mem _ (closure_minimal (hbs.trans hsΘ) hΘcl hy.1), hyi⟩ (mem_image_of_mem _
        (closure_mono hbs hy.1))
  have hsubN : (cap.emb '' cuffEnds P₀ b Θ) ∩ D.ins F ⊆ cap.emb '' tilde (b (f i)) := by
    rintro _ ⟨⟨y', ⟨e', he', he'Θ, hy'⟩, rfl⟩, hy'i⟩
    obtain ⟨s', hs'', hs'Θ, hes', hbs', -⟩ := exists_side_of_cuffEnds hS hb hΘ he' he'Θ
    have hy's : y' ∈ s := by
      obtain ⟨z, hz, hze⟩ := hJ ⟨mem_image_of_mem _ (closure_minimal (hbs'.trans hs'Θ) hΘcl hy'.1),
        hy'i⟩
      obtain rfl := hinj hze
      by_contra hn'
      exact hcorner z ⟨hz, hn'⟩ hy'i
    have hy'V : y' ∉ χ.Φ.V := (hs'.2.1 hy's).2
    have hy's' : y' ∈ s' := by
      by_contra hn'
      exact hy'V (χ.Φ.tilde_subset hbd hs'' ⟨closure_mono hbs' hy'.1, hn'⟩)
    obtain rfl : s' = s := GM11.arcComponent_eq hs'' hs' hy's' hy's
    obtain ⟨j, rfl⟩ := hM.all₀ e' he' hes'
    by_cases hij : i = j
    · rw [hij]
      exact mem_image_of_mem _ hy'
    exfalso
    obtain ⟨F₂, hF₂, hF₂c, hF₂i, hF₂t⟩ := grow _ (hb.mem _ he') (hbs'.trans hsΘ) F₁ hF₁
      (by omega) y' hy'.1 (hF₁i hy'i)
    rcases lt_or_gt_of_ne hij with hlt' | hlt'
    · have h₁ := D.borderEdgeDist_le_of_bite hF₂ (hF₁g.trans hF₂i) hF₂t
      have h₂ := hM.far i j hlt'
      rw [← hM.map i, ← hM.map j] at h₂
      omega
    · have h₁ := D.borderEdgeDist_le_of_bite hF₂ hF₂t (hF₁g.trans hF₂i)
      have h₂ := hM.far j i hlt'
      rw [← hM.map i, ← hM.map j] at h₂
      omega
  have h2 : (tilde (b (f i))).ncard = 2 := by
    obtain ⟨z, hz⟩ : (b (f i)).Nonempty := (hb.mem _ he).1
    exact (D.P.Γ.border_edge _ (hb.mem _ he) ⟨z, hz, (hs'.2.1 (hbs hz)).1⟩).1
  have hcard : ((cap.emb '' cuffEnds P₀ b Θ) ∩ D.ins F).ncard ≤ 2 := by
    have := ncard_le_ncard hsubN ((D.P.Γ.finite_V.subset (D.P.Γ.tilde_subset_V
      (hb.mem _ he))).image _)
    rw [ncard_image_of_injective _ hinj, h2] at this
    exact this
  omega

end TangleDatum

end GraphMinor.GM19
