/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12f

/-!
# Graph Minors XIX, Section 12: tools for (12.4)

The proof of (12.4) walks along short circuits, and measures atoms with them. This file holds these
steps: a short
circuit bounds the metric (`dist_le_of_circuit`), two vertices of a circuit are joined along it by
at most half of it
(`exists_walk_on_circuit`), a walk from outside a short circuit to inside it meets it
(`exists_walk_to_circuit`), and
the zone of a connected hub is connected (`isPreconnected_nearZone`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {H : Drawing Shat} {k : ℕ}

/-- A short circuit bounds the metric between two atoms that meet its inside. -/
theorem dist_le_of_circuit (D : TangleDatum cap χ) (hrep : 1 ≤ D.rep) {F : Drawing Shat}
  (hF : Drawing.IsCircuitOf F D.rad.G)
    (hlt : F.E.ncard < 2 * D.rep) {a b : Set Shat} (ha : (a ∩ D.ins F).Nonempty) (hb :
      (b ∩ D.ins F).Nonempty) :
    2 * D.dist a b ≤ F.E.ncard := by
  obtain ⟨X, hX, hl, hi, -⟩ := exists_restraint_of_circuit D hrep hF hlt
  obtain ⟨T, hTX, hTl⟩ := exists_walk_of_restraint D hrep hX
  have := D.dist_le T (a := a) (b := b) (ha.mono (inter_subset_inter_right _ (hTX ▸ hi)))
    (hb.mono (inter_subset_inter_right _ (hTX ▸ hi)))
  omega

/-- A path of `G` gives a walk of `G` as long as the path. -/
theorem _root_.GraphMinor.GM19.Drawing.IsPathOf.exists_walk {T : Type} [TopologicalSpace T]
  [T2Space T] {P G : Drawing T}
    {u v : T} (hP : Drawing.IsPathOf P G u v) : ∃ W : GraphWalk G.toGraph u v, W.length = P.E.ncard
      := by
  obtain ⟨W, hW, -, hE⟩ := hP.2
  obtain ⟨W', -, he⟩ := hP.1.exists_walk_up W
  refine ⟨W', ?_⟩
  have h₁ := ncard_walk_E P hW
  rw [walkDrawing_E, ← hE] at h₁
  have h₂ : W'.length = W.length := by rw [← edges_length, ← edges_length, he]
  omega

/-- Two vertices of a circuit are joined along it by a walk of at most half its length. -/
theorem exists_walk_on_circuit {T : Type} [TopologicalSpace T] [T2Space T] {F G : Drawing T}
    (hF : Drawing.IsCircuitOf F G) {a b : T} (ha : a ∈ F.V) (hb : b ∈ F.V) :
    ∃ W : GraphWalk G.toGraph a b, 2 * W.length ≤ F.E.ncard ∧ ∀ x ∈ W.support, x ∈ F.V := by
  classical
  by_cases hab : a = b
  · subst hab
    exact ⟨.nil (hF.1.1 ha), by change 2 * 0 ≤ _; omega, by simpa [GraphWalk.support] using ha⟩
  obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, -, hdisj, hsup⟩ := hF.2.exists_two_paths ha hb hab
  have hcount : P.E.ncard + Q.E.ncard = F.E.ncard := by
    have hE := Drawing.sup_E hPs hQs
    rw [hsup] at hE
    rw [hE, ncard_union_eq hdisj (F.finite_edges.subset hPs.2) (F.finite_edges.subset hQs.2)]
  have key : ∀ {P : Drawing T}, P.IsPathBetween a b → P.IsSubdrawing F →
      ∃ W : GraphWalk G.toGraph a b, W.length = P.E.ncard ∧ ∀ x ∈ W.support, x ∈ F.V := by
    intro P hP hPs
    obtain ⟨W, hW, hV, hE⟩ := hP
    obtain ⟨W', hs, he⟩ := (hPs.trans hF.1).exists_walk_up W
    refine ⟨W', ?_, fun x hx ↦ hPs.1 ?_⟩
    · have h₁ := ncard_walk_E P hW
      rw [walkDrawing_E, ← hE] at h₁
      have h₂ : W'.length = W.length := by rw [← edges_length, ← edges_length, he]
      omega
    · rw [hV]
      rw [hs] at hx
      exact hx
  obtain ⟨W₁, h₁, h₁'⟩ := key hP hPs
  obtain ⟨W₂, h₂, h₂'⟩ := key hQ hQs
  by_cases hle : P.E.ncard ≤ Q.E.ncard
  · exact ⟨W₁, by omega, h₁'⟩
  · exact ⟨W₂, by omega, h₂'⟩

omit [T2Space S] in
/-- A walk from outside the interior of a short circuit to its interior reaches a vertex of the
circuit. -/
theorem exists_walk_to_circuit (D : TangleDatum cap χ) (hrep : 1 ≤ D.rep) {F : Drawing Shat}
    (hF : Drawing.IsCircuitOf F D.rad.G) (hlt : F.E.ncard < 2 * D.rep) {c y : Shat}
      (W : GraphWalk D.rad.G.toGraph c y)
    (hc : c ∉ D.ins F \ F.U) (hy : y ∈ D.ins F \ F.U) :
    ∃ h ∈ F.V, ∃ W' : GraphWalk D.rad.G.toGraph c h, W'.length ≤ W.length := by
  have : ConnectedSpace Shat := cap.connected
  have hsl := D.isSlope hrep
  have hl : F.length < 2 * D.rep := hlt
  obtain ⟨hcl, hfr, hU⟩ := ins_facts_of_length hsl hF.2 hF.1 hl
  induction W with
  | nil h => exact absurd hy hc
  | @cons c u y g hg r ih =>
    by_cases hcU : c ∈ F.U
    · exact ⟨c, mem_V_of_mem_U hF.1 hcU hg.2.1, .nil hg.2.1, Nat.zero_le _⟩
    have hcA : c ∉ D.ins F := fun h ↦ hc ⟨h, hcU⟩
    by_cases hu : u ∈ D.ins F \ F.U
    · exfalso
      have hg₁ : c ∈ closure g ∩ D.rad.G.V := by
        rw [hg.2.2.2]
        exact .inl rfl
      have hg₂ : u ∈ closure g ∩ D.rad.G.V := by
        rw [hg.2.2.2]
        exact .inr rfl
      rcases edge_subset_or_disjoint_of_length hsl hF.2 hF.1 hl hg.1 with h | h
      · exact hcA (closure_minimal h hcl hg₁.1)
      · have hint : u ∈ interior (D.ins F) := by
          by_contra hn
          exact hu.2 (hfr ▸ ⟨subset_closure hu.1, hn⟩)
        obtain ⟨x, hx₁, hx₂⟩ := mem_closure_iff.mp hg₂.1 _ isOpen_interior hint
        exact disjoint_left.mp h hx₂ (interior_subset hx₁)
    · obtain ⟨h, hh, W', hW'⟩ := ih hu hy
      exact ⟨h, hh, .cons hg W', by simpa using hW'⟩

omit [T2Space Shat] in
/-- The zone of a connected hub is connected. -/
theorem isPreconnected_nearZone (hH : H.IsSubdrawing D.rad.G) (hc : IsPreconnected H.U)
  (hne : H.V.Nonempty) :
    IsPreconnected (nearZone D H k) := by
  classical
  have hS := χ.isSurface
  -- the set of a vertex of `Γ*`
  have hzH : H.U ⊆ nearZone D H k := subset_nearZone hH
  have hatomN : ∀ {j : ℕ} {x : Shat}, D.IsNear H j x → (x ∈ D.P.Γ.hatV cap → j ≤ k + 1) → j ≤ k + 2
    →
      D.rad.atomOf x ⊆ nearZone D H k := by
    intro j x hN h₁ h₂
    by_cases hx : x ∈ D.P.Γ.hatV cap
    · obtain ⟨v, hv, rfl⟩ := hx
      rw [D.atomOf_emb hv]
      rintro _ rfl
      exact .inl ⟨mem_image_of_mem _ hv, hN.mono (h₁ (mem_image_of_mem _ hv))⟩
    · have hw : x ∈ D.rad.Rstar := ⟨hN.mem_V, hx⟩
      rw [atomOf_Rstar D hw]
      exact fun y hy ↦ .inr (mem_iUnion₂.mpr ⟨x, ⟨hw, hN.mono h₂⟩, hy⟩)
  have hatomc : ∀ {x : Shat}, x ∈ D.rad.G.V → IsPreconnected (D.rad.atomOf x) := by
    intro x hxG
    by_cases hx : x ∈ D.P.Γ.hatV cap
    · obtain ⟨v, hv, rfl⟩ := hx
      rw [D.atomOf_emb hv]
      exact isPreconnected_singleton
    · rw [atomOf_Rstar D ⟨hxG, hx⟩]
      exact isPreconnected_connectedComponentIn
  have key : ∀ {x h : Shat} (W : GraphWalk D.rad.G.toGraph x h), h ∈ H.V → W.length ≤ k + 2 →
      (x ∈ D.P.Γ.hatV cap → W.length ≤ k + 1) →
      ∃ T ⊆ nearZone D H k, D.rad.atomOf x ⊆ T ∧ h ∈ T ∧ IsPreconnected T := by
    intro x h W
    induction W with
    | nil hG =>
      intro hh hl hl'
      refine ⟨D.rad.atomOf _, hatomN (j := 0) (isNear_self hH hh) (fun _ ↦ by omega) (by omega),
        subset_rfl,
        D.mem_atomOf hG, hatomc hG⟩
    | @cons x u h g hg r ih =>
      intro hh hl hl'
      rw [GraphWalk.length_cons] at hl
      have hgu : u ∈ closure g ∩ D.rad.G.V := by
        rw [hg.2.2.2]
        exact .inr rfl
      have hgx : x ∈ closure g ∩ D.rad.G.V := by
        rw [hg.2.2.2]
        exact .inl rfl
      by_cases hx : x ∈ D.P.Γ.hatV cap
      · have hu : u ∈ D.rad.Rstar := other_end_mem_Rstar D hg.1 hg.2.2.2 hx
        rw [GraphWalk.length_cons] at hl'
        obtain ⟨T, hT, hat, hhT, hTc⟩ := ih hh (by omega) (fun h ↦ absurd h hu.2)
        rw [atomOf_Rstar D hu] at hat
        have hclosure : x ∈ closure (D.rad.regionOf u) :=
          closure_mono (edge_subset_regionOf D hu hg.1 hgu.1) hgx.1
        have hS' : IsPreconnected (insert x (D.rad.regionOf u)) :=
          isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
            (insert_subset hclosure subset_closure)
        have hxz : x ∈ nearZone D H k := .inl ⟨hx, h, hh, .cons hg r, by
          rw [GraphWalk.length_cons]
          exact hl' hx⟩
        have huT := hat (D.rad.regionOf_mem hu).2
        refine ⟨T ∪ insert x (D.rad.regionOf u), union_subset hT (insert_subset hxz
          (hat.trans hT)), ?_, .inl hhT,
          hTc.union u huT (.inr (D.rad.regionOf_mem hu).2) hS'⟩
        obtain ⟨v, hv, rfl⟩ := hx
        rw [D.atomOf_emb hv]
        rintro _ rfl
        exact .inr (.inl rfl)
      · have hw : x ∈ D.rad.Rstar := ⟨hg.2.1, hx⟩
        have hu : u ∈ D.P.Γ.hatV cap := by
          obtain ⟨a, ha, t, ht, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 g hg.1
          have : a ∈ closure g ∩ D.rad.G.V := by
            rw [hcap]
            exact .inl rfl
          rw [hg.2.2.2] at this
          rcases this with rfl | rfl
          · exact absurd ha hx
          · exact ha
        obtain ⟨T, hT, hat, hhT, hTc⟩ := ih hh (by omega) (fun _ ↦ by omega)
        have huT : u ∈ T := by
          apply hat
          exact D.mem_atomOf hgu.2
        have hclosure : u ∈ closure (D.rad.regionOf x) :=
          closure_mono (edge_subset_regionOf D hw hg.1 hgx.1) hgu.1
        have hS' : IsPreconnected (insert u (D.rad.regionOf x)) :=
          isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
            (insert_subset hclosure subset_closure)
        have hxz : D.rad.regionOf x ⊆ nearZone D H k := fun y hy ↦
          .inr (mem_iUnion₂.mpr ⟨x, ⟨hw, h, hh, .cons hg r, by
            rw [GraphWalk.length_cons]
            exact hl⟩, hy⟩)
        refine ⟨T ∪ insert u (D.rad.regionOf x), union_subset hT (insert_subset (hT huT) hxz),
          ?_, .inl hhT,
          hTc.union u huT (.inl rfl) hS'⟩
        rw [atomOf_Rstar D hw]
        exact fun y hy ↦ .inr (.inr hy)
  obtain ⟨h₀, hh₀⟩ := hne
  have hh₀U := H.V_subset_U hh₀
  have hfinal : ∀ {x h : Shat} (W : GraphWalk D.rad.G.toGraph x h), h ∈ H.V → W.length ≤ k + 2 →
      (x ∈ D.P.Γ.hatV cap → W.length ≤ k + 1) → ∀ y ∈ D.rad.atomOf x,
      ∃ t ⊆ nearZone D H k, h₀ ∈ t ∧ y ∈ t ∧ IsPreconnected t := by
    intro x h W hh h₁ h₂ y hy
    obtain ⟨T, hT, hat, hhT, hTc⟩ := key W hh h₁ h₂
    exact ⟨T ∪ H.U, union_subset hT hzH, .inr hh₀U, .inl (hat hy),
      hTc.union h hhT (H.V_subset_U hh) hc⟩
  refine isPreconnected_of_forall h₀ fun y hy ↦ ?_
  rcases hy with ⟨hyV, h, hh, W, hW⟩ | hy
  · exact hfinal W hh (by omega) (fun _ ↦ hW) y (D.mem_atomOf (IsNear.mem_V ⟨h, hh, W, hW⟩))
  · obtain ⟨w, ⟨hw, h, hh, W, hWl⟩, hyw⟩ := mem_iUnion₂.mp hy
    exact hfinal W hh hWl (fun h' ↦ absurd h' hw.2) y (by rw [atomOf_Rstar D hw]; exact hyw)

end TangleDatum

end GraphMinor.GM19
