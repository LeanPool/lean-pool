/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Epstein
public import LeanPool.GraphMinor.GM11.PathClasses
public import LeanPool.GraphMinor.GM11.Solid
public import LeanPool.GraphMinor.GM11.EdgeSides
public import LeanPool.GraphMinor.GM11.RadialAccess
public import LeanPool.GraphMinor.GM11.PaintingCells
public import LeanPool.GraphMinor.Surface.OpenDisc
public import LeanPool.GraphMinor.Surface.SphereDisc
import LeanPool.GraphMinor.Surface.Disc
import Mathlib.Analysis.Convex.Contractible

/-!
# Flat sets in an open disc

This file proves the part of Graph Minors VII, (11.5)--(11.10), that Graph Minors XI uses: a closed
flat
set that is arc-wise connected and locally arc-wise connected lies in an open set which is a disc,
or else
the surface is a sphere. We follow the paper:

- `flat_iUnion` is (11.5): the set has an open flat neighbourhood.
- `flat_union_disc` is the case of (11.3) that the proof of (11.8) uses, where the disc has all of
  its boundary in
  the open set. Here the paper's limit of curves is not needed.
- `exists_maximal_flat` is the first step of the proof of (11.8), by Zorn's lemma.
- `exists_open_around` is (11.9), and with `open_disc` it gives the conclusion.

"Flat" here is relative to an open set `W`, in place of the whole surface, so that the proof also
gives
(7.5) of Graph Minors XI. So the homotopies live in the subtype `W`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

section Abstract

variable {T : Type u} [TopologicalSpace T]

/-- **(11.5)** of Graph Minors VII (page 251). Let `N z` be path-connected neighbourhoods of the
points `z` of
a flat set `X`. If `N z`, `N z'` meet, then they lie in one flat set, in which `X` is
path-connected. Then
the union of the sets `N z` is flat. -/
theorem flat_iUnion {X : Set T} (hX : Flat X) (N : T → Set T) (hNo : ∀ z ∈ X, IsOpen (N z))
    (hNm : ∀ z ∈ X, z ∈ N z) (hNc : ∀ z ∈ X, IsPathConnected (N z))
    (hpair : ∀ z ∈ X, ∀ z' ∈ X, (N z ∩ N z').Nonempty → ∃ D : Set T, Flat D ∧ N z ∪ N z' ⊆ D ∧
      ∀ a ∈ X ∩ D, ∀ b ∈ X ∩ D, JoinedIn (X ∩ D) a b) :
    Flat (⋃ z ∈ X, N z) := by
  -- A path between two points of `N z`, in `N z`.
  have harw : ∀ z ∈ X, ∀ a ∈ N z, ∀ b ∈ N z, ∃ f : Cl a b, Arw (N z) f := fun z hz a ha b hb => by
    have hj := (hNc z hz).joinedIn a ha b hb
    exact ⟨Cl.mk hj.somePath, hj.somePath, fun u => hj.somePath_mem u, rfl⟩
  have hjoin : ∀ z ∈ X, ∀ z' ∈ X, (N z ∩ N z').Nonempty → ∃ (D : Set T) (w : Cl z z'), Flat D ∧
      N z ∪ N z' ⊆ D ∧ Arw (X ∩ D) w := fun z hz z' hz' hne => by
    obtain ⟨D, hD, hsub, hj⟩ := hpair z hz z' hz' hne
    have hj' := hj z ⟨hz, hsub (Or.inl (hNm z hz))⟩ z' ⟨hz', hsub (Or.inr (hNm z' hz'))⟩
    exact ⟨D, Cl.mk hj'.somePath, hD, hsub, hj'.somePath, fun u => hj'.somePath_mem u, rfl⟩
  -- The main claim: a path in the union, seen from its first point, is homotopic to a path in `X`.
  have key : ∀ (a b : T) (p : Path a b), (∀ u, p u ∈ ⋃ z ∈ X, N z) → ∀ (z₀ : T)
    (α : Cl z₀ a), z₀ ∈ X →
      a ∈ N z₀ → Arw (N z₀) α → ∃ z ∈ X, b ∈ N z ∧ ∃ (β : Cl b z) (θ : Cl z₀ z), Arw (N z) β
        ∧ Arw X θ ∧
        α.trans ((Cl.mk p).trans β) = θ := by
    intro a b p hp z₀ α hz₀ ha hα
    let Q : ∀ c : T, Cl a c → Prop := fun c f => ∃ z ∈ X, c ∈ N z ∧ ∃ (β : Cl c z) (θ : Cl z₀ z),
      Arw (N z) β ∧ Arw X θ ∧ α.trans (f.trans β) = θ
    refine cl_induction (𝒞 := {O | ∃ z ∈ X, O = N z}) ?_ p (fun u => ?_) Q ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hNo z hz
    · have := hp u
      simp only [mem_iUnion, exists_prop] at this
      obtain ⟨z, hz, hu⟩ := this
      exact ⟨N z, ⟨z, hz, rfl⟩, hu⟩
    · refine ⟨z₀, hz₀, ha, α.symm, Cl.rf z₀, hα.symm, arw_refl hz₀, ?_⟩
      rw [cl_refl_trans, cl_trans_symm]
    · rintro c d f r _ ⟨z', hz', rfl⟩ hr ⟨z, hz, hc, β, θ, hβ, hθ, e⟩
      have hc' : c ∈ N z' := by simpa using hr 0
      have hd' : d ∈ N z' := by simpa using hr 1
      obtain ⟨D, w, hD, hsub, hw⟩ := hjoin z hz z' hz' ⟨c, hc, hc'⟩
      obtain ⟨β', hβ'⟩ := harw z' hz' d hd' z' (hNm z' hz')
      refine ⟨z', hz', hd', β', θ.trans w, hβ', hθ.trans (hw.mono inter_subset_left), ?_⟩
      have h₁ : (Cl.mk r).trans β' = β.trans w := hD.eq
        ((Arw.of_path r hr).trans hβ' |>.mono subset_union_right |>.mono hsub)
        ((hβ.mono subset_union_left |>.mono hsub).trans (hw.mono inter_subset_right))
      have e₂ : α.trans ((f.trans (Cl.mk r)).trans β') = (α.trans (f.trans β)).trans w := by
        simp only [cl_assoc, h₁]
      rw [e₂, e]
  intro a b p q hp hq
  have ha : a ∈ ⋃ z ∈ X, N z := by simpa using hp 0
  simp only [mem_iUnion, exists_prop] at ha
  obtain ⟨z₀, hz₀, ha⟩ := ha
  obtain ⟨α, hα⟩ := harw z₀ hz₀ z₀ (hNm z₀ hz₀) a ha
  obtain ⟨z, hz, hb, β, θ, hβ, hθ, e⟩ := key a b p hp z₀ α hz₀ ha hα
  obtain ⟨z', hz', hb', β', θ', hβ', hθ', e'⟩ := key a b q hq z₀ α hz₀ ha hα
  obtain ⟨D, w, hD, hsub, hw⟩ := hjoin z hz z' hz' ⟨b, hb, hb'⟩
  have h₁ : β' = β.trans w := hD.eq (hβ'.mono (subset_union_right.trans hsub))
    ((hβ.mono (subset_union_left.trans hsub)).trans (hw.mono inter_subset_right))
  have h₂ : θ' = θ.trans w := hX.eq hθ' (hθ.trans (hw.mono inter_subset_left))
  refine Path.Homotopic.Quotient.eq.mp (cl_cancel α (β.trans w) ?_)
  have e₃ : ∀ k : Cl a b, α.trans (k.trans (β.trans w)) = (α.trans (k.trans β)).trans w := fun k
    => by
    simp only [cl_assoc]
  rw [e₃, e, ← h₂, ← e', h₁]

/-- A path from a point of `D` to a set `F`, where `D` is closed and `D \ F` is open, stays in `D`
until it first
reaches `F`. -/
theorem exists_arw_to {Y D F : Set T} (hDc : IsClosed D) (hDo : IsOpen (D \ F)) (hFc : IsClosed F)
    (hFD : F ⊆ D) {a f : T} (haD : a ∈ D) (hf : f ∈ F) (p : Path a f) (hp : ∀ u, p u ∈ Y) :
    ∃ x ∈ F, ∃ g : Cl a x, Arw (Y ∩ D) g := by
  by_cases haF : a ∈ F
  · exact ⟨a, haF, Cl.rf a, arw_refl ⟨by simpa using hp 0, haD⟩⟩
  have hcp : IsCompact (p ⁻¹' F) := (hFc.preimage p.continuous).isCompact
  obtain ⟨t, ht, hle⟩ := hcp.exists_isLeast ⟨1, by simpa using hf⟩
  have hpre : IsPreconnected (Ico (0 : I) t) := ordConnected_Ico.isPreconnected
  have hin : Ico (0 : I) t ⊆ p ⁻¹' (D \ F) := by
    have hsub : Ico (0 : I) t ⊆ p ⁻¹' (D \ F) ∪ p ⁻¹' Dᶜ := by
      intro u hu
      by_cases huD : p u ∈ D
      · exact Or.inl ⟨huD, fun h => absurd (hle h) (not_le.mpr hu.2)⟩
      · exact Or.inr huD
    have h0 : (0 : I) ∈ Ico (0 : I) t := ⟨le_rfl, lt_of_le_of_ne (unitInterval.nonneg t) fun e => by
      apply haF
      have : p t ∈ F := ht
      rwa [← e, p.source] at this⟩
    refine hpre.subset_left_of_subset_union (hDo.preimage p.continuous)
      (hDc.isOpen_compl.preimage p.continuous) ?_ hsub ⟨0, h0, ?_⟩
    · exact disjoint_left.mpr fun x hx hx' => hx' hx.1
    · simpa using (⟨haD, haF⟩ : a ∈ D \ F)
  refine ⟨p t, ht, Cl.mk (p.subpath 0 t |>.cast p.source.symm rfl), _, fun u => ?_, rfl⟩
  have : (p.subpath 0 t) u ∈ p '' uIcc 0 t := by
    rw [← Path.range_subpath]
    exact mem_range_self u
  obtain ⟨v, hv, hv'⟩ := this
  rw [uIcc_of_le (show (0 : I) ≤ t from unitInterval.nonneg t)] at hv
  simp only [Path.cast_coe]
  rw [← hv']
  refine ⟨hp v, ?_⟩
  rcases eq_or_lt_of_le hv.2 with e | hlt
  · rw [e]
    exact hFD ht
  · exact (hin ⟨hv.1, hlt⟩).1

/-- **A case of (11.3)** of Graph Minors VII (page 249). Let `Y` be open, flat and path-connected.
Let `D` be a closed
flat path-connected set with `D \ F` open, where `F ⊆ Y ∩ D` is closed and path-connected. Then `Y ∪
D` is flat. -/
theorem flat_union_disc {Y D F : Set T} (hYo : IsOpen Y) (hYc : IsPathConnected Y) (hYf : Flat Y)
    (hDf : Flat D) (hDc : IsClosed D) (hDp : IsPathConnected D) (hDo : IsOpen (D \ F))
      (hFc : IsClosed F)
    (hFp : IsPathConnected F) (hFY : F ⊆ Y) (hFD : F ⊆ D) : Flat (Y ∪ D) := by
  obtain ⟨f₀, hf₀⟩ := hFp.nonempty
  -- Each point of `Y ∩ D` is joined to `F` in `Y ∩ D`.
  have hto : ∀ a ∈ Y ∩ D, ∃ x ∈ F, ∃ g : Cl a x, Arw (Y ∩ D) g := fun a ha => by
    have hj := hYc.joinedIn a ha.1 f₀ (hFY hf₀)
    exact exists_arw_to hDc hDo hFc hFD ha.2 hf₀ hj.somePath hj.somePath_mem
  -- A class of `D` with ends in `Y` has a path in `Y`.
  have hflatten : ∀ (a b : T) (f : Cl a b), a ∈ Y → b ∈ Y → Arw D f → Arw Y f := by
    intro a b f ha hb hf
    obtain ⟨x, hx, g, hg⟩ := hto a ⟨ha, hf.left_mem⟩
    obtain ⟨y, hy, h, hh⟩ := hto b ⟨hb, hf.right_mem⟩
    have hj := hFp.joinedIn x hx y hy
    have hη : Arw F (Cl.mk hj.somePath) := ⟨_, hj.somePath_mem, rfl⟩
    have e : f = g.trans ((Cl.mk hj.somePath).trans h.symm) := hDf.eq hf
      ((hg.mono inter_subset_right).trans ((hη.mono hFD).trans (hh.mono inter_subset_right).symm))
    rw [e]
    exact (hg.mono inter_subset_left).trans ((hη.mono hFY).trans (hh.mono inter_subset_left).symm)
  -- A path of `Y ∪ D` with ends in `Y` is homotopic to a path in `Y`.
  have hpush : ∀ (a b : T) (p : Path a b), a ∈ Y → b ∈ Y → (∀ u, p u ∈ Y ∪ D) → Arw Y (Cl.mk p)
    := by
    intro a b p ha hb hp
    let Q : ∀ c : T, Cl a c → Prop := fun c f => Arw Y f ∨
      ∃ (e : T) (g : Cl a e) (r : Cl e c), e ∈ Y ∧ Arw Y g ∧ Arw D r ∧ f = g.trans r
    have hQ : Q b (Cl.mk p) := by
      refine cl_induction (𝒞 := {Y, D \ F}) ?_ p (fun u => ?_) Q (Or.inl (arw_refl ha)) ?_
      · rintro O (h | h)
        · rw [h]
          exact hYo
        · rw [h]
          exact hDo
      · by_cases hu : p u ∈ F
        · exact ⟨Y, Or.inl rfl, hFY hu⟩
        · rcases hp u with h | h
          · exact ⟨Y, Or.inl rfl, h⟩
          · exact ⟨D \ F, Or.inr rfl, h, hu⟩
      · rintro c d f r O (h | h) hr hc
        · rw [h] at hr
          have hcY : c ∈ Y := by simpa using hr 0
          left
          rcases hc with hc | ⟨e, g, t, he, hg, ht, rfl⟩
          · exact hc.trans (Arw.of_path r hr)
          · exact (hg.trans (hflatten e c t he hcY ht)).trans (Arw.of_path r hr)
        · rw [h] at hr
          have hr' : Arw D (Cl.mk r) := (Arw.of_path r hr).mono sdiff_subset
          right
          rcases hc with hc | ⟨e, g, t, he, hg, ht, rfl⟩
          · exact ⟨c, f, Cl.mk r, hc.right_mem, hc, hr', rfl⟩
          · exact ⟨e, g, t.trans (Cl.mk r), he, hg, ht.trans hr', cl_assoc _ _ _⟩
    rcases hQ with h | ⟨e, g, r, he, hg, hr, h⟩
    · exact h
    · rw [h]
      exact hg.trans (hflatten e b r he hb hr)
  -- Each point of `Y ∪ D` is joined to `Y`.
  have hbase : ∀ x ∈ Y ∪ D, ∃ y ∈ Y, ∃ ρ : Cl y x, Arw (Y ∪ D) ρ := by
    rintro x (hx | hx)
    · exact ⟨x, hx, Cl.rf x, arw_refl (Or.inl hx)⟩
    · have hj := hDp.joinedIn f₀ (hFD hf₀) x hx
      exact ⟨f₀, hFY hf₀, Cl.mk hj.somePath, _, fun u => Or.inr (hj.somePath_mem u), rfl⟩
  intro a b p q hp hq
  obtain ⟨a', ha', ρ, hρ⟩ := hbase a (by simpa using hp 0)
  obtain ⟨b', hb', ρ', hρ'⟩ := hbase b (by simpa using hp 1)
  have hpush' : ∀ f : Cl a' b', Arw (Y ∪ D) f → Arw Y f := by
    rintro _ ⟨r, hr, rfl⟩
    exact hpush _ _ r ha' hb' hr
  refine Path.Homotopic.Quotient.eq.mp (cl_cancel ρ ρ'.symm (hYf.eq (hpush' _ ?_) (hpush' _ ?_)))
  · exact hρ.trans ((Arw.of_path p hp).trans hρ'.symm)
  · exact hρ.trans ((Arw.of_path q hq).trans hρ'.symm)

/-- **The first step of the proof of (11.8)** of Graph Minors VII (page 253): by Zorn's lemma, there
is a maximal
open flat path-connected set that contains a given one. -/
theorem exists_maximal_flat {Y₀ : Set T} (hY₀o : IsOpen Y₀) (hY₀c : IsPathConnected Y₀)
  (hY₀f : Flat Y₀) :
    ∃ Y, Y₀ ⊆ Y ∧ IsOpen Y ∧ IsPathConnected Y ∧ Flat Y ∧
      ∀ Y', Y ⊆ Y' → IsOpen Y' → IsPathConnected Y' → Flat Y' → Y' ⊆ Y := by
  let 𝓕 : Set (Set T) := {Y | Y₀ ⊆ Y ∧ IsOpen Y ∧ IsPathConnected Y ∧ Flat Y}
  obtain ⟨x₀, hx₀⟩ := hY₀c.nonempty
  have hchain : ∀ c ⊆ 𝓕, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ 𝓕, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hch hne
    obtain ⟨Y₁, hY₁⟩ := hne
    refine ⟨⋃₀ c, ⟨(hc hY₁).1.trans (subset_sUnion_of_mem hY₁), isOpen_sUnion fun s hs =>
      (hc hs).2.1,
      ?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    · refine ⟨x₀, ⟨Y₁, hY₁, (hc hY₁).1 hx₀⟩, ?_⟩
      rintro y ⟨s, hs, hy⟩
      exact ((hc hs).2.2.1.joinedIn x₀ ((hc hs).1 hx₀) y hy).mono (subset_sUnion_of_mem hs)
    · intro a b p q hp hq
      have hK : IsCompact (range p ∪ range q) := (isCompact_range p.continuous).union
        (isCompact_range q.continuous)
      have hsub : range p ∪ range q ⊆ ⋃ s : c, s.1 := by
        rw [← sUnion_eq_iUnion]
        rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
        · exact hp u
        · exact hq u
      have : Nonempty c := ⟨⟨Y₁, hY₁⟩⟩
      obtain ⟨s, hs⟩ := hK.elim_directed_cover _ (fun s : c => (hc s.2).2.1) hsub
        (directedOn_iff_directed.mp hch.directedOn)
      exact (hc s.2).2.2.2 p q (fun u => hs (Or.inl ⟨u, rfl⟩)) fun u => hs (Or.inr ⟨u, rfl⟩)
  obtain ⟨Y, -, hY⟩ := zorn_subset_nonempty 𝓕 hchain Y₀ ⟨subset_rfl, hY₀o, hY₀c, hY₀f⟩
  refine ⟨Y, hY.prop.1, hY.prop.2.1, hY.prop.2.2.1, hY.prop.2.2.2, fun Y' h₁ h₂ h₃ h₄ => ?_⟩
  exact hY.le_of_ge ⟨hY.prop.1.trans h₁, h₂, h₃, h₄⟩ h₁

end Abstract

variable {S : Type u} [TopologicalSpace S]

/-- A subset of `W` that is simply-connected is flat in `W`. -/
theorem flat_of_simplyConnected {W K : Set S} (hK : IsSimplyConnectedSet K) (hKW : K ⊆ W) :
    Flat (Subtype.val ⁻¹' K : Set W) := fun _ _ p q hp hq =>
  homotopic_of_mem hK hKW p q (by simpa using hp 0) (by simpa using hp 1) hp hq

/-- A set in `W` is path-connected in `W` if it is path-connected in the surface. -/
theorem isPathConnected_preimage {W K : Set S} (hK : IsPathConnected K) (hKW : K ⊆ W) :
    IsPathConnected (Subtype.val ⁻¹' K : Set W) := by
  rw [IsInducing.subtypeVal.isPathConnected_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hKW]
  exact hK

/-- **(11.5)** of Graph Minors VII (page 251), in a closed surface: a closed flat path-connected set
`X`
that is locally arc-wise connected has an open flat path-connected neighbourhood in `W`. -/
theorem exists_open_flat (hS : IsClosedSurface S) {W X : Set S} (hW : IsOpen W)
  (hXW : X ⊆ W)
    (hXc : IsClosed X) (hXl : IsLocallyArcConnected X) (hXp : IsPathConnected X)
    (hXf : Flat (Subtype.val ⁻¹' X : Set W)) :
    ∃ Y₀ : Set W, Subtype.val ⁻¹' X ⊆ Y₀ ∧ IsOpen Y₀ ∧ IsPathConnected Y₀ ∧ Flat Y₀ := by
  classical
  have hT : T2Space S := hS.2.1
  have hC : CompactSpace S := hS.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  -- The cover: open sets that miss `X`, and open subsets of discs in `W` where `X` is
  -- path-connected.
  let Good : Set S → Prop := fun O => IsOpen O ∧ (O ⊆ Xᶜ ∨ ∃ D, IsClosedDisc D ∧ O ⊆ D ∧ D ⊆ W ∧
    ∀ a ∈ X ∩ O, ∀ b ∈ X ∩ O, JoinedIn (X ∩ O) a b)
  have hcover : (univ : Set S) ⊆ ⋃ O : {O // Good O}, O.1 := by
    intro z _
    by_cases hz : z ∈ X
    · obtain ⟨D, D', hD, hD'o, hzD', hD'D, hDW, -⟩ := exists_closedDisc_nbhd hS hW (hXW hz)
      obtain ⟨A, hA, hzA, hAo, hAc⟩ := hXl z hz D' hD'o hzD'
      refine mem_iUnion.mpr ⟨⟨A, hAo, Or.inr ⟨D, hD, hA.trans hD'D, hDW, fun a ha b hb => ?_⟩⟩, hzA⟩
      by_cases hab : a = b
      · subst hab
        exact JoinedIn.refl ha
      · obtain ⟨L, hL, hl⟩ := hAc a ha b hb hab
        obtain ⟨f, h0, h1⟩ := hl
        exact (show JoinedIn L a b from ⟨⟨⟨fun t => (f t).1, by fun_prop⟩, h0, h1⟩,
          fun t => (f t).2⟩).mono hL
    · exact mem_iUnion.mpr ⟨⟨Xᶜ, hXc.isOpen_compl, Or.inl subset_rfl⟩, hz⟩
  obtain ⟨R, hR, hN⟩ := exists_small_rel (fun O : {O // Good O} => O.1) (fun O => O.2.1) hcover
  -- The neighbourhoods.
  have hnb : ∀ z : S, ∃ V : Set S, z ∈ X → (IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧ IsPathConnected V ∧
      ∀ a ∈ V, ∀ b ∈ V, R a b) := by
    intro z
    by_cases hz : z ∈ X
    · obtain ⟨N, hNo, hNz, hNr⟩ := hN z
      obtain ⟨V, hV, hVo, hzV, hVc⟩ := locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp hlc
        z (N ∩ W)
        ((hNo.inter hW).mem_nhds ⟨hNz, hXW hz⟩)
      exact ⟨V, fun _ => ⟨hVo, hzV, hV.trans inter_subset_right,
        isPathConnected_of_isOpen hS hVo hVc.isPreconnected ⟨z, hzV⟩,
        fun a ha b hb => hNr a (hV ha).1 b (hV hb).1⟩⟩
    · exact ⟨∅, fun h => (hz h).elim⟩
  choose V hV using hnb
  let N : W → Set W := fun z => Subtype.val ⁻¹' V z.1
  have hNf := flat_iUnion hXf N (fun z hz => (hV z.1 hz).1.preimage continuous_subtype_val)
    (fun z hz => (hV z.1 hz).2.1) (fun z hz => isPathConnected_preimage (hV z.1 hz).2.2.2.1
      (hV z.1 hz).2.2.1)
    (fun z hz z' hz' hne => ?_)
  · refine ⟨⋃ z ∈ (Subtype.val ⁻¹' X : Set W), N z, fun z hz => ?_, ?_, ?_, hNf⟩
    · exact mem_biUnion hz (hV z.1 hz).2.1
    · exact isOpen_biUnion fun z hz => (hV z.1 hz).1.preimage continuous_subtype_val
    · obtain ⟨x₀, hx₀, hj⟩ := isPathConnected_preimage hXp hXW
      have hsub : ∀ z ∈ (Subtype.val ⁻¹' X : Set W), N z ⊆ ⋃ z ∈ (Subtype.val ⁻¹' X : Set W), N z :=
        fun z hz => subset_biUnion_of_mem (u := N) hz
      have hmem : ∀ z ∈ (Subtype.val ⁻¹' X : Set W), z ∈ N z := fun z hz => (hV z.1 hz).2.1
      refine ⟨x₀, hsub x₀ hx₀ (hmem x₀ hx₀), fun y hy => ?_⟩
      simp only [mem_iUnion, exists_prop] at hy
      obtain ⟨z, hz, hy⟩ := hy
      have h₁ : JoinedIn (⋃ z ∈ (Subtype.val ⁻¹' X : Set W), N z) x₀ z :=
        (hj hz).mono fun w hw => hsub w hw (hmem w hw)
      have h₂ : JoinedIn (N z) z y :=
        (isPathConnected_preimage (hV z.1 hz).2.2.2.1 (hV z.1 hz).2.2.1).joinedIn z (hmem z hz) y hy
      exact h₁.trans (h₂.mono (hsub z hz))
  · obtain ⟨u, hu, hu'⟩ := hne
    obtain ⟨⟨O, hOo, hO⟩, hOr⟩ := hR u.1
    have hin : ∀ y ∈ N z, y.1 ∈ O := fun y hy => hOr _ ((hV z.1 hz).2.2.2.2 _ hu _ hy)
    have hin' : ∀ y ∈ N z', y.1 ∈ O := fun y hy => hOr _ ((hV z'.1 hz').2.2.2.2 _ hu' _ hy)
    rcases hO with hO | ⟨D, hD, hOD, hDW, hj⟩
    · exact (hO (hin z (hV z.1 hz).2.1) hz).elim
    · refine ⟨Subtype.val ⁻¹' O, (flat_of_simplyConnected (IsClosedDisc.isSimplyConnectedSet hD)
        hDW).mono
        (preimage_mono hOD), ?_, fun a ha b hb => ?_⟩
      · rintro y (hy | hy)
        · exact hin y hy
        · exact hin' y hy
      · have := hj a.1 ha b.1 hb
        have e : (Subtype.val '' ((Subtype.val ⁻¹' X : Set W) ∩ Subtype.val ⁻¹' O)) = X ∩ O := by
          rw [← preimage_inter, Subtype.image_preimage_coe, inter_eq_right.mpr
            (inter_subset_left.trans hXW)]
        exact (IsInducing.subtypeVal.joinedIn_image ha hb).mp (by rwa [e])

/-- **(11.9)** of Graph Minors VII (page 253), in a closed surface and inside an open set `W`, with
the conclusion
that (11.10) draws from it. Graph Minors XI (7.2) gives a disc in `W` bounded by an `O`-arc
null-homotopic in `W`. -/
theorem exists_open_around [ConnectedSpace S] (hS : IsClosedSurface S) {W X : Set S}
    (hW : IsOpen W) (hXW : X ⊆ W) (hXc : IsClosed X) (hXl : IsLocallyArcConnected X)
      (hXp : IsPathConnected X)
    (hXf : Flat (Subtype.val ⁻¹' X : Set W)) :
    ∃ Y, X ⊆ Y ∧ Y ⊆ W ∧ ((IsSphere S ∧ Y = univ) ∨ IsOpenDisc Y) := by
  have hT : T2Space S := hS.2.1
  obtain ⟨Y₀, hsub, h₁, h₂, h₃⟩ := exists_open_flat hS hW hXW hXc hXl hXp hXf
  obtain ⟨Y, hY₀, hYo, hYc, hYf, hmax⟩ := exists_maximal_flat h₁ h₂ h₃
  have hopen : IsOpen (Subtype.val '' Y) := hW.isOpenEmbedding_subtypeVal.isOpenMap _ hYo
  refine ⟨Subtype.val '' Y, fun x hx => ⟨⟨x, hXW hx⟩, hY₀ (hsub hx), rfl⟩, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hbody : ∀ F : Set S, F ⊆ Subtype.val '' Y → IsOArc F →
      ∃ Δ : Set S, Δ ⊆ Subtype.val '' Y ∧ IsClosedDisc Δ ∧ discBd Δ = F := by
    intro F hFY hF
    have hFW : F ⊆ W := by
      rintro x hx
      obtain ⟨y, -, rfl⟩ := hFY hx
      exact y.2
    obtain ⟨ψ⟩ := id hF
    let φ : C(Circle, S) := ⟨fun x => (ψ x).1, continuous_subtype_val.comp ψ.continuous⟩
    have hmem : ∀ t, φ (arcParam 1 t) ∈ W := fun t => hFW (ψ _).2
    let a : W := ⟨φ (arcParam 1 0), hmem 0⟩
    let γ : Path a a := ⟨⟨fun t => ⟨φ (arcParam 1 t), hmem t⟩, by fun_prop⟩, rfl,
      Subtype.ext (by simp [a])⟩
    have hγ : ∀ u, γ u ∈ Y := fun u => by
      obtain ⟨y, hy, e⟩ := hFY (ψ (arcParam 1 u)).2
      have : γ u = y := Subtype.ext e.symm
      rwa [this]
    have hh : γ.Homotopic (Path.refl a) := hYf _ _ (hγ) (fun _ => by simpa using hγ 0)
    have hnull : IsNullHomotopicOArcIn W F := ⟨ψ, a.1, a.2, closedCurvesHomotopicIn_of_path 1 φ
      (ContinuousMap.const _ a.1) γ (Path.refl a) (fun _ => rfl) (fun _ => rfl) hh⟩
    have hbd : Disjoint F (bd S) := disjoint_left.mpr fun x _ hx => hx (hS.2.2 x)
    obtain ⟨Δ, hΔW, hΔ, hb⟩ := (epstein S W F (IsClosedSurface.isSurface hS) inferInstance hF hFW
      hbd).1 hnull
    have hcφ : Continuous fun t : I => φ (arcParam 1 t) := by fun_prop
    have hrange : range (fun t : I => φ (arcParam 1 t)) = F := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact (ψ _).2
      · intro hx
        obtain ⟨w, hw⟩ := ψ.surjective ⟨x, hx⟩
        obtain ⟨t, rfl⟩ := arcParam_surjective 1 w
        exact ⟨t, congrArg Subtype.val hw⟩
    have hFc : IsClosed F := hrange ▸ (isCompact_range hcφ).isClosed
    have hpc : PathConnectedSpace I :=
      have : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
      inferInstance
    have hpF : IsPathConnected F := hrange ▸ isPathConnected_range hcφ
    let D : Set W := Subtype.val ⁻¹' Δ
    let G : Set W := Subtype.val ⁻¹' F
    have hDG : D \ G = Subtype.val ⁻¹' (Δ \ F) := rfl
    have hDo : IsOpen (D \ G) := by
      rw [hDG, ← hb]
      exact (isOpenDisc_interior hS hΔ).1.preimage continuous_subtype_val
    have hFΔ : F ⊆ Δ := by
      rw [← hb]
      exact discBd_subset Δ
    have hGY : G ⊆ Y := fun x hx => by
      obtain ⟨y, hy, e⟩ := hFY hx
      have : x = y := Subtype.ext e.symm
      rwa [this]
    have hGD : G ⊆ D := fun x hx => hFΔ hx
    have hDp : IsPathConnected D := isPathConnected_preimage (IsClosedDisc.isSimplyConnectedSet
      hΔ).1 hΔW
    have hGp : IsPathConnected G := isPathConnected_preimage hpF hFW
    have hflat : Flat (Y ∪ D) := flat_union_disc hYo hYc hYf
      (flat_of_simplyConnected (IsClosedDisc.isSimplyConnectedSet hΔ) hΔW)
      ((IsClosedDisc.isCompact hΔ).isClosed.preimage continuous_subtype_val) hDp hDo
        (hFc.preimage continuous_subtype_val)
      hGp hGY hGD
    have hopen' : IsOpen (Y ∪ D) := by
      have e : Y ∪ D = Y ∪ (D \ G) := by
        ext x
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · by_cases hx : x ∈ G
            · exact Or.inl (hGY hx)
            · exact Or.inr ⟨h, hx⟩
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr h.1
      rw [e]
      exact hYo.union hDo
    obtain ⟨g, hg⟩ := hGp.nonempty
    have hpc : IsPathConnected (Y ∪ D) := hYc.union hDp ⟨g, hGY hg, hGD hg⟩
    have hsubD := hmax _ subset_union_left hopen' hpc hflat
    refine ⟨Δ, fun x hx => ⟨⟨x, hΔW hx⟩, hsubD (Or.inr hx), rfl⟩, hΔ, hb⟩
  exact open_disc S _ hS inferInstance (hYc.isConnected.image _
    continuous_subtype_val.continuousOn) hopen hbody

end GraphMinor.GM11
