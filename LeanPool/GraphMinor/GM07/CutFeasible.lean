/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.MoveOff
public import LeanPool.GraphMinor.GM07.Matched
public import LeanPool.GraphMinor.GM07.CutDraw
public import LeanPool.GraphMinor.GM07.Section4
import LeanPool.GraphMinor.GM07.Section6
import LeanPool.GraphMinor.GM19.Section6a

/-!
# Feasibility across a cut

The step of (7.5), page 241. We move `H` off `ē`, take its preimage `H'` in `Σ_e`, and add the two
ends `a'` and `b'` of the cut as isolated
vertices. A homeomorphism of `Σ_e` fixing the boundary fixes the new cuff pointwise, so it comes
down to a homeomorphism of `Σ` that fixes
`ē`. A forest in `φ_e⁻¹(G \ e)` misses `e`, so it comes down to a forest in `G`.
-/

public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

section Cut

variable {S S_e : Type u} [TopologicalSpace S] [TopologicalSpace S_e] [T2Space S] [CompactSpace
  S_e] [T2Space S_e]
  {G : Drawing S} {e : Set S} {a b c : ℕ} {φ : S_e → S} {G_e : Drawing S_e}

omit [T2Space S] [CompactSpace S_e] [T2Space S_e] in
/-- A homeomorphism of `Σ_e` fixing the boundary comes down to `Σ`. -/
theorem IsCutAlongEdge.exists_descent (hCut : IsCutAlongEdge G e a b c S_e φ G_e) (α' : S_e ≃ₜ S_e)
  (hfix : ∀ x ∈ bd S_e, α' x = x) :
    ∃ α : S ≃ₜ S, ∀ x, φ (α' x) = α (φ x) := by
  classical
  have hq := hCut.quotientMap
  have hsurj := hq.surjective
  have hbd : ∀ x, φ x ∈ e → x ∈ bd S_e := fun x hx => by
    rw [hCut.bd_eq]
    exact .inr (subset_closure hx)
  have hdown : ∀ β : S_e ≃ₜ S_e, (∀ x ∈ bd S_e, β x = x) → ∃ d : S → S, Continuous d ∧ ∀ x, d (φ x)
    = φ (β x) := fun β hβ => by
    have hfib : ∀ x y, φ x = φ y → φ (β x) = φ (β y) := fun x y he => by
      rcases hCut.inj x y he with rfl | hx
      · rfl
      · rw [hβ x (hbd x hx), hβ y (hbd y (he ▸ hx)), he]
    let d : S → S := fun y => φ (β (surjInv hsurj y))
    have hd : ∀ x, d (φ x) = φ (β x) := fun x => hfib _ _ (surjInv_eq hsurj (φ x))
    refine ⟨d, hq.continuous_iff.mpr ?_, hd⟩
    have : d ∘ φ = φ ∘ β := funext hd
    rw [this]
    exact hq.continuous.comp β.continuous
  obtain ⟨d₁, hd₁, h₁⟩ := hdown α' hfix
  obtain ⟨d₂, hd₂, h₂⟩ := hdown α'.symm fun x hx => by
    rw [Homeomorph.symm_apply_eq, hfix x hx]
  refine ⟨⟨⟨d₁, d₂, fun y => ?_, fun y => ?_⟩, hd₁, hd₂⟩, fun x => (h₁ x).symm⟩
  · obtain ⟨x, rfl⟩ := hsurj y
    rw [h₁, h₂, Homeomorph.symm_apply_apply]
  · obtain ⟨x, rfl⟩ := hsurj y
    rw [h₂, h₁, Homeomorph.apply_symm_apply]

omit [T2Space S] [CompactSpace S_e] [T2Space S_e] in
theorem IsCutAlongEdge.injOn_off (hCut : IsCutAlongEdge G e a b c S_e φ G_e) {K : Set S}
  (hK : Disjoint K e) : InjOn φ (φ ⁻¹' K) := fun x hx y _ he =>
  (hCut.inj x y he).resolve_right fun h => disjoint_left.mp hK hx h

omit [T2Space S_e] in
/-- Each edge of `G_e` is the preimage of an edge of `G` other than `e`. -/
theorem IsCutAlongEdge.exists_edge (hCut : IsCutAlongEdge G e a b c S_e φ G_e) {f₁ : Set S_e}
  (hf₁ : f₁ ∈ G_e.E) :
    φ '' f₁ ∈ G.E ∧ Disjoint (φ '' f₁) e ∧ f₁ = φ ⁻¹' (φ '' f₁) := by
  have hs := hCut.quotientMap.surjective
  have hc := hCut.quotientMap.continuous
  set D := G.deleteEdge e with hD
  have hDU : D.U = G.U \ e := deleteEdge_U G hCut.mem_E
  have hDV : D.V = G.V := deleteEdge_V G e
  have hi : InjOn φ (φ ⁻¹' D.U) := hCut.injOn_off (by rw [hDU]; exact disjoint_sdiff_left)
  have hE : arcComponentsIn (φ ⁻¹' (D.U \ D.V)) = preimage φ '' D.E := arcComponentsIn_preimage hc
    hs D.isClosed_U hi sdiff_subset
  have heq : G_e.U \ G_e.V = φ ⁻¹' (D.U \ D.V) := by
    rw [hCut.preimage_U, hCut.preimage_V, hDU, hDV]
    rfl
  have hf₂ : f₁ ∈ arcComponentsIn (φ ⁻¹' (D.U \ D.V)) := heq ▸ hf₁
  rw [hE] at hf₂
  obtain ⟨C, hC, rfl⟩ := hf₂
  have hCE : C ∈ G.E \ {e} := deleteEdge_E G e ▸ hC
  rw [image_preimage_eq C hs]
  refine ⟨hCE.1, ?_, rfl⟩
  have : C ⊆ D.U := subset_closure.trans (D.closure_subset_U hC)
  rw [hDU] at this
  exact disjoint_left.mpr fun x hx hxe => (this hx).2 hxe

/-- The image in `G` of a subgraph of `G_e`. -/
@[expose] noncomputable def cutImage (G : Drawing S) (φ : S_e → S) (H₁ : Drawing S_e) : Drawing S :=
  G.span (φ '' H₁.V) (image φ '' H₁.E)

omit [T2Space S_e] in
/-- A subgraph of a graph that lies over `G` matches its image. -/
theorem matched_cutImage_of {H₁ G_e : Drawing S_e} (hc : Continuous φ) (hinj : InjOn φ G_e.U)
  (hVe : G_e.V = φ ⁻¹' G.V)
    (hEe : ∀ f₁ ∈ G_e.E, φ '' f₁ ∈ G.E) (hsub : H₁.IsSubdrawing G_e) :
    IsMatched H₁ (cutImage G φ H₁) φ ∅ := by
  have hcl : ∀ f₁ : Set S_e, closure (φ '' f₁) = φ '' closure f₁ := fun f₁ =>
    (image_closure_subset_closure_image hc).antisymm' (closure_minimal (image_mono subset_closure)
      (isClosed_closure.isCompact.image hc).isClosed)
  have hUs := hsub.U_subset
  have hE : image φ '' H₁.E ∩ G.E = image φ '' H₁.E := inter_eq_left.mpr (by
    rintro _ ⟨f₁, hf₁, rfl⟩
    exact hEe _ (hsub.2 hf₁))
  have hVs : φ '' H₁.V ∩ G.V = φ '' H₁.V := inter_eq_left.mpr (by
    rintro _ ⟨x, hx, rfl⟩
    have : x ∈ G_e.V := hsub.1 hx
    rw [hVe] at this
    exact this)
  have hV : (cutImage G φ H₁).V = φ '' H₁.V := by
    change G.spanV _ _ = _
    rw [Drawing.spanV, hE, hVs]
    refine union_eq_left.mpr (iUnion₂_subset ?_)
    rintro _ ⟨f₁, hf₁, rfl⟩ x ⟨hx, hxV⟩
    rw [hcl] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    by_contra hn
    have h1 : y ∈ closure f₁ \ H₁.V := ⟨hy, hn⟩
    rw [H₁.closure_diff_V hf₁] at h1
    have h2 := (hsub.2 hf₁).2.1 h1
    apply h2.2
    rw [hVe]
    exact hxV
  have hU : (cutImage G φ H₁).U = φ '' H₁.U := by
    change G.spanU _ _ = _
    rw [Drawing.spanU]
    have : G.spanV (φ '' H₁.V) (image φ '' H₁.E) = φ '' H₁.V := hV
    rw [this, hE, H₁.U_eq, image_union, image_iUnion₂]
    congr 1
    ext x
    simp only [mem_iUnion, exists_prop, mem_image, ← hcl]
    constructor
    · rintro ⟨_, ⟨f₁, hf₁, rfl⟩, hx⟩
      exact ⟨f₁, hf₁, hx⟩
    · rintro ⟨f₁, hf₁, hx⟩
      exact ⟨_, ⟨f₁, hf₁, rfl⟩, hx⟩
  refine ⟨hc, hinj.mono hUs, empty_subset _, fun _ _ => disjoint_empty _, by rw [hU,
    sdiff_empty], by rw [hV, sdiff_empty], ?_⟩
  rw [cutImage, Drawing.span_E, hE]

omit [T2Space S_e] in
theorem IsCutAlongEdge.matched_cutImage (hCut : IsCutAlongEdge G e a b c S_e φ G_e) {H₁ : Drawing
  S_e} (hsub : H₁.IsSubdrawing G_e) :
    IsMatched H₁ (cutImage G φ H₁) φ ∅ :=
  matched_cutImage_of hCut.quotientMap.continuous (fun x hx y _ he =>
    (hCut.inj x y he).resolve_right (by
    have := hx
    rw [hCut.preimage_U] at this
    exact this.2)) hCut.preimage_V (fun f₁ hf₁ => (hCut.exists_edge hf₁).1) hsub

/-- `H₀` off `ē`, in `Σ_e`, with the two ends of the cut added. -/
noncomputable def cutLift (H₀ : Drawing S) (u v : S) (hB : Disjoint
  ({u, v} : Set S) H₀.U) (hc : Continuous φ) (hs : Surjective φ)
    (hi : InjOn φ (φ ⁻¹' (addIsolated H₀ {u, v} (by simp) hB).U)) : Drawing S_e :=
  pullDrawing (addIsolated H₀ {u, v} (by simp) hB) hc hs hi

omit [T2Space S_e] in
theorem IsCutAlongEdge.matched_cutLift (hCut : IsCutAlongEdge G e a b c S_e φ G_e) {H₀ : Drawing S}
  {u v : S} {u' v' : S_e} (hu : φ u' = u) (hv : φ v' = v)
    (huniq : ∀ x, φ x = u ∨ φ x = v → x = u' ∨ x = v') (hB : Disjoint ({u, v} : Set S) H₀.U)
    (hi : InjOn φ (φ ⁻¹' (addIsolated H₀ {u, v} (by simp) hB).U)) :
    IsMatched (cutLift H₀ u v hB hCut.quotientMap.continuous hCut.quotientMap.surjective hi) H₀ φ
      {u', v'} := by
  classical
  have hc := hCut.quotientMap.continuous
  have hs := hCut.quotientMap.surjective
  set H' := cutLift H₀ u v hB hc hs hi with hH'
  have hUd : H'.U = φ ⁻¹' (H₀.U ∪ {u, v}) := rfl
  have hVd : H'.V = φ ⁻¹' (H₀.V ∪ {u, v}) := rfl
  have hoff : ∀ x, x ∈ H₀.U → x ≠ u ∧ x ≠ v := fun x hx => by
    constructor
    · rintro rfl
      exact disjoint_left.mp hB (by simp) hx
    · rintro rfl
      exact disjoint_left.mp hB (by simp) hx
  have hEd : H'.E = preimage φ '' H₀.E := by
    have h : H'.U \ H'.V = φ ⁻¹' (H₀.U \ H₀.V) := by
      rw [hUd, hVd]
      ext x
      simp only [mem_sdiff, mem_preimage, mem_union, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · rintro ⟨h1 | h1 | h1, h2, h3⟩
        · exact ⟨h1, h2⟩
        · exact absurd h1 h3.1
        · exact absurd h1 h3.2
      · rintro ⟨h1, h2⟩
        exact ⟨.inl h1, h2, (hoff _ h1).1, (hoff _ h1).2⟩
    change arcComponentsIn (H'.U \ H'.V) = _
    rw [h]
    exact arcComponentsIn_preimage hc hs H₀.isClosed_U (hi.mono (preimage_mono subset_union_left))
      sdiff_subset
  have himg : ∀ {P : Set S}, P ⊆ H₀.U → φ '' (φ ⁻¹' (P ∪ {u, v}) \ {u', v'}) = P := fun {P} hP => by
    ext y
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      rcases hx1 with h1 | h1
      · exact h1
      · exact absurd (huniq x (by simpa using h1)) (by simpa using hx2)
    · intro hy
      obtain ⟨x, rfl⟩ := hs y
      refine ⟨x, ⟨.inl hy, ?_⟩, rfl⟩
      rintro (rfl | rfl)
      · exact (hoff _ (hP hy)).1 hu
      · exact (hoff _ (hP hy)).2 hv
  refine ⟨hc, hi, ?_, ?_, himg subset_rfl, himg H₀.V_subset_U, ?_⟩
  · rintro x (rfl | rfl)
    · exact .inr (by simp [hu])
    · exact .inr (by simp [hv])
  · intro f hf
    rw [hEd] at hf
    obtain ⟨C, hC, rfl⟩ := hf
    have hiC : InjOn φ (φ ⁻¹' closure C) := hi.mono (preimage_mono ((H₀.closure_subset_U hC).trans
      subset_union_left))
    rw [closure_preimage_of_injOn hc hs hiC, disjoint_left]
    rintro x hx (rfl | rfl)
    · exact (hoff _ (H₀.closure_subset_U hC hx)).1 hu
    · exact (hoff _ (H₀.closure_subset_U hC hx)).2 hv
  · rw [hEd, image_image]
    have : (fun C => φ '' (φ ⁻¹' C)) = id := funext fun C => image_preimage_eq C hs
    change H₀.E = (fun C => φ '' (φ ⁻¹' C)) '' H₀.E
    rw [this, image_id]

end Cut

private theorem lifted_forest_has_cut_boundary_vertices
    {S : Type u}
    {S_e : Type u}
    [TopologicalSpace S]
    [TopologicalSpace S_e]
    (G : Drawing S)
    (e : Set S)
    (φ : S_e → S)
    (G_e : Drawing S_e)
    (u : S)
    (v : S)
    (hucap : u ∈ closure e ∩ G.V)
    (hvcap : v ∈ closure e ∩ G.V)
    (H₀ : Drawing S)
    (hH₀bd : H₀.V ∩ bd S = G.V ∩ bd S)
    (H' : Drawing S_e)
    (hVd : ∀ (x : S_e), x ∈ H'.V ↔ φ x ∈ H₀.V ∨ φ x = u ∨ φ x = v)
    (hbde : ∀ (x : S_e), x ∈ bd S_e ↔ φ x ∈ bd S ∨ φ x ∈ closure e)
    (hGVe : ∀ (x : S_e), x ∈ G_e.V ↔ φ x ∈ G.V)
    (huU : ∀ (x : S_e), φ x ∈ closure e → φ x ∉ H₀.U)
    (hcapE : ∀ (x : S_e), φ x ∈ closure e → φ x ∈ G.V → φ x = u ∨ φ x = v) :
    G_e.V ∩ bd S_e = H'.V ∩ bd S_e := by
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [hGVe] at h1
    rw [hVd]
    rcases (hbde x).mp h2 with h3 | h3
    · have : φ x ∈ H₀.V ∩ bd S := by
        rw [hH₀bd]
        exact ⟨h1, h3⟩
      exact .inl this.1
    · exact .inr (hcapE x h3 h1)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [hGVe]
    rcases (hVd x).mp h1 with h3 | h3 | h3
    · rcases (hbde x).mp h2 with h4 | h4
      · have : φ x ∈ G.V ∩ bd S := by
          rw [← hH₀bd]
          exact ⟨h3, h4⟩
        exact this.1
      · exact absurd (H₀.V_subset_U h3) (huU x h4)
    · rw [h3]
      exact hucap.2
    · rw [h3]
      exact hvcap.2

private theorem cut_boundary_vertex_count
    {S : Type u}
    {S_e : Type u}
    [TopologicalSpace S]
    [TopologicalSpace S_e]
    (a : ℕ)
    (b : ℕ)
    (G : Drawing S)
    (e : Set S)
    (φ : S_e → S)
    (G_e : Drawing S_e)
    (hCut : IsCutAlongEdge G e a b 1 S_e φ G_e)
    (u : S)
    (v : S)
    (heV : ∀ x ∈ e, x ∉ G.V)
    (u' : S_e)
    (v' : S_e)
    (huniq : ∀ (x : S_e), φ x = u ∨ φ x = v → x = u' ∨ x = v')
    (hne' : u' ≠ v')
    (hbde : ∀ (x : S_e), x ∈ bd S_e ↔ φ x ∈ bd S ∨ φ x ∈ closure e)
    (hGVe : ∀ (x : S_e), x ∈ G_e.V ↔ φ x ∈ G.V)
    (hcapE : ∀ (x : S_e), φ x ∈ closure e → φ x ∈ G.V → φ x = u ∨ φ x = v) :
    (G_e.V ∩ bd S_e).ncard ≤ (G.V ∩ bd S).ncard + 2 := by
  have hfinG : (G.V ∩ bd S).Finite := G.finite_V.subset inter_subset_left
  have hsub : G_e.V ∩ bd S_e ⊆ ((G_e.V ∩ bd S_e) \ {u', v'}) ∪ {u', v'} := fun x hx => by
    by_cases h : x ∈ ({u', v'} : Set S_e)
    · exact .inr h
    · exact .inl ⟨hx, h⟩
  have hmaps : MapsTo φ ((G_e.V ∩ bd S_e) \ {u', v'}) (G.V ∩ bd S) := fun x hx => by
    have h1 := (hGVe x).mp hx.1.1
    refine ⟨h1, ?_⟩
    rcases (hbde x).mp hx.1.2 with h2 | h2
    · exact h2
    · exact absurd (huniq x (hcapE x h2 h1)) hx.2
  have hinj : InjOn φ ((G_e.V ∩ bd S_e) \ {u', v'}) := fun x hx y hy hxy => by
    refine (hCut.inj x y hxy).resolve_right fun h1 => ?_
    exact heV _ h1 (hmaps hx).1
  have hfin : ((G_e.V ∩ bd S_e) \ {u', v'}).Finite := Set.Finite.of_injOn hmaps hinj hfinG
  calc (G_e.V ∩ bd S_e).ncard ≤ (((G_e.V ∩ bd S_e) \ {u', v'}) ∪ {u', v'}).ncard
    := ncard_le_ncard hsub (hfin.union (by simp))
    _ ≤ ((G_e.V ∩ bd S_e) \ {u', v'}).ncard + ({u', v'} : Set S_e).ncard := ncard_union_le _ _
    _ ≤ (G.V ∩ bd S).ncard + 2 := by
      refine Nat.add_le_add (ncard_le_ncard_of_injOn φ hmaps hinj hfinG) ?_
      rw [ncard_pair hne']

private theorem few_small_cuffs_after_cut
    {S : Type u}
    {S_e : Type u}
    [TopologicalSpace S]
    [TopologicalSpace S_e]
    (a : ℕ)
    (b : ℕ)
    (G : Drawing S)
    (e : Set S)
    (φ : S_e → S)
    (G_e : Drawing S_e)
    (hCut : IsCutAlongEdge G e a b 1 S_e φ G_e)
    (hSe : IsSurface S_e)
    (u : S)
    (v : S)
    (hucap : u ∈ closure e ∩ G.V)
    (hvcap : v ∈ closure e ∩ G.V)
    (H₀ : Drawing S)
    (u' : S_e)
    (hu : φ u' = u)
    (v' : S_e)
    (hv : φ v' = v)
    (huniq : ∀ (x : S_e), φ x = u ∨ φ x = v → x = u' ∨ x = v')
    (hne' : u' ≠ v')
    (H' : Drawing S_e)
    (hmat : IsMatched H' H₀ φ {u', v'})
    (hGVe : ∀ (x : S_e), x ∈ G_e.V ↔ φ x ∈ G.V) :
    {C | C ∈ cuffs S_e ∧ (G_e.V ∩ C).ncard ≤ 1}.ncard ≤ 1 := by
  have hcuffs : (cuffs S_e).ncard = 2 := ncard_cuffs_of_homeomorph_surfaceModel hCut.homeo_model
  have hfin : (cuffs S_e).Finite := (cuff_statement.{u} S_e hSe).2.1
  have hnew := hCut.newCuff
  have hsub : {C ∈ cuffs S_e | (G_e.V ∩ C).ncard ≤ 1} ⊆ cuffs S_e \ {φ ⁻¹' closure e} := by
    rintro C ⟨hC, hle⟩
    refine ⟨hC, fun hCe => ?_⟩
    rw [mem_singleton_iff] at hCe
    subst hCe
    have hp : ({u', v'} : Set S_e) ⊆ G_e.V ∩ φ ⁻¹' closure e := by
      rintro x (rfl | rfl)
      · exact ⟨(hGVe _).mpr (by rw [hu]; exact hucap.2), by rw [mem_preimage, hu]; exact hucap.1⟩
      · exact ⟨(hGVe _).mpr (by rw [hv]; exact hvcap.2), by rw [mem_preimage, hv]; exact hvcap.1⟩
    have := ncard_le_ncard hp (G_e.finite_V.subset inter_subset_left)
    rw [ncard_pair hne'] at this
    omega
  have h1 := ncard_le_ncard hsub (hfin.sdiff)
  rw [ncard_sdiff_singleton_of_mem hnew] at h1
  omega

/-- **The step of (7.5), page 241.** Given a cut edge `e` with `α(G_e) ≥ ⌊28kv/3⌋`, moving `H` off
`ē` and adding the two ends of the cut gives a forest `H'`
in `Σ_e` such that `|V(G_e) ∩ bd(Σ_e)| ≤ 2k - 2g`, where `g` counts the cuffs of `Σ_e` with at most
one vertex, and `H'` being `G_e`-feasible makes `H`
`G`-feasible. The paper applies (6.1) here, but its hypothesis `≤ 2k - 2c` fails, since the cut adds
two vertices. What holds, and what the proof of (6.1) uses,
is the bound here. See the correction to the proof of (7.5) in `corrections/GM07.md`. -/
theorem oneCuffCutEdgeFeasibilityStep {S S_e : Type u} [TopologicalSpace S] [TopologicalSpace S_e]
  [T1Space S]
    (hS : IsSurface S) (a b : ℕ) (hm : Nonempty
      (S ≃ₜ SurfaceModel a b 1))
    (k : ℕ) (G H : Drawing S) (e : Set S) (φ : S_e → S) (G_e : Drawing S_e)
    (hcard : (G.V ∩ bd S).ncard + 4 ≤ 2 * k)
    (hH : IsSurfaceForest H) (hbdeq : G.V ∩ bd S = H.V ∩ bd S)
    (hCut : IsCutAlongEdge G e a b 1 S_e φ G_e)
    (hα : (28 * k * vModel a b 2 k) / 3 ≤ alpha G_e) :
    ∃ H' : Drawing S_e,
      IsSurfaceForest H' ∧ G_e.V ∩ bd S_e = H'.V ∩ bd S_e ∧
      (G_e.V ∩ bd S_e).ncard ≤ 2 * k - 2 * {C ∈ cuffs S_e | (G_e.V ∩ C).ncard ≤ 1}.ncard ∧
      9 * k * vSurface S_e k < alpha G_e ∧
      (IsGFeasible G_e H' → IsGFeasible G H) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  have hSe := hCut.isSurface
  have ht2e : T2Space S_e := hSe.2.1
  have hce : CompactSpace S_e := hSe.1
  have hConn : ConnectedSpace S := connectedSpace_of_model hm
  have hc := hCut.quotientMap.continuous
  have hs := hCut.quotientMap.surjective
  have hneS : Nonempty S := inferInstance
  have hneSe : Nonempty S_e := by
    obtain ⟨x⟩ := hneS
    obtain ⟨y, -⟩ := hs x
    exact ⟨y⟩
  have he := hCut.mem_E
  have hd := hCut.disjoint_bd
  have hl := hCut.not_loop
  obtain ⟨u, v, huv, hcap, hL⟩ : ∃ u v : S, u ≠ v ∧ closure e ∩ G.V = {u, v} ∧ IsLineWithEnds
    (closure e) u v := by
    rcases G.edge_cond e he with h1 | ⟨u, hcap, -⟩
    · exact h1
    · rw [GraphMinor.GM19.tilde_eq_inter_V G he, hcap] at hl
      simp at hl
  have hucap : u ∈ closure e ∩ G.V := by rw [hcap]; simp
  have hvcap : v ∈ closure e ∩ G.V := by rw [hcap]; simp
  have heV : ∀ x ∈ e, x ∉ G.V := fun x hx => (he.2.1 hx).2
  obtain ⟨hmo⟩ := id hm
  have hM : IsSurface (SurfaceModel a b 1) := (modelCriterion.1 a b 1).1
  obtain ⟨β, hβfix, hβoff⟩ := exists_move_off_line hS hM hmo hH hL hd
  set H₀ := mapDrawingHomeo β H with hH₀def
  have hH₀ : IsSurfaceForest H₀ := hH.map_homeo β
  have hoff : Disjoint H₀.U (closure e) := hβoff
  have hH₀bd : H₀.V ∩ bd S = G.V ∩ bd S := by
    rw [hbdeq]
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hb⟩
      have hyx : y = β y := by
        apply β.injective
        rw [hβfix _ hb]
      rw [← hyx] at hb ⊢
      exact ⟨hy, hb⟩
    · rintro ⟨hx, hb⟩
      exact ⟨⟨x, hx, hβfix x hb⟩, hb⟩
  obtain ⟨u', hu⟩ := hs u
  obtain ⟨v', hv⟩ := hs v
  have huniq : ∀ x, φ x = u ∨ φ x = v → x = u' ∨ x = v' := by
    rintro x (h | h)
    · exact .inl ((hCut.inj x u' (h.trans hu.symm)).resolve_right fun h1 => heV _ h1 (h ▸ hucap.2))
    · exact .inr ((hCut.inj x v' (h.trans hv.symm)).resolve_right fun h1 => heV _ h1 (h ▸ hvcap.2))
  have hne' : u' ≠ v' := fun h => huv (by rw [← hu, ← hv, h])
  have hB : Disjoint ({u, v} : Set S) H₀.U := by
    rw [disjoint_left]
    rintro x (rfl | rfl) hx
    · exact disjoint_left.mp hoff hx hucap.1
    · exact disjoint_left.mp hoff hx hvcap.1
  have hi : InjOn φ (φ ⁻¹' (addIsolated H₀ {u, v} (by simp) hB).U) := by
    refine hCut.injOn_off ?_
    rw [disjoint_left]
    rintro x (hx | rfl | rfl) hxe
    · exact disjoint_left.mp hoff hx (subset_closure hxe)
    · exact heV _ hxe hucap.2
    · exact heV _ hxe hvcap.2
  set H' := cutLift H₀ u v hB hc hs hi with hH'
  have hmat : IsMatched H' H₀ φ {u', v'} := hCut.matched_cutLift hu hv huniq hB hi
  have hUd : ∀ x, x ∈ H'.U ↔ φ x ∈ H₀.U ∨ φ x = u ∨ φ x = v := fun x => Iff.rfl
  have hVd : ∀ x, x ∈ H'.V ↔ φ x ∈ H₀.V ∨ φ x = u ∨ φ x = v := fun x => Iff.rfl
  have hbde : ∀ x, x ∈ bd S_e ↔ φ x ∈ bd S ∨ φ x ∈ closure e := fun x => by
    rw [hCut.bd_eq]
    rfl
  have hGVe : ∀ x, x ∈ G_e.V ↔ φ x ∈ G.V := fun x => by
    rw [hCut.preimage_V]
    rfl
  have hbdoff : ∀ x, x ∈ closure e → x ∉ bd S := fun x h1 h2 => by
    have : x ∈ closure e ∩ bd S := ⟨h1, h2⟩
    rw [hd] at this
    exact this
  have huU : ∀ x, φ x ∈ closure e → φ x ∉ H₀.U := fun x h1 h2 => disjoint_left.mp hoff h2 h1
  have hcapE : ∀ x, φ x ∈ closure e → φ x ∈ G.V → φ x = u ∨ φ x = v := fun x h1 h2 => by
    have : φ x ∈ closure e ∩ G.V := ⟨h1, h2⟩
    rw [hcap] at this
    simpa using this
  have hbdE : G_e.V ∩ bd S_e = H'.V ∩ bd S_e := by
    exact lifted_forest_has_cut_boundary_vertices (S := S) (S_e := S_e) G e φ G_e u v hucap hvcap
      H₀ hH₀bd H' hVd hbde hGVe huU hcapE
  have hproper : H'.IsProper := by
    rintro x ⟨hb, hU⟩
    rw [hVd]
    rcases (hUd x).mp hU with h1 | h1
    · rcases (hbde x).mp hb with h2 | h2
      · exact .inl (hH₀.1 ⟨h2, h1⟩)
      · exact absurd h1 (huU x h2)
    · exact .inr h1
  have hforest : IsSurfaceForest H' := ⟨hproper, hmat.isGraphForest_iff.mpr hH₀.2⟩
  -- The count on the boundary.
  have hZ : (G_e.V ∩ bd S_e).ncard ≤ (G.V ∩ bd S).ncard + 2 := by
    exact cut_boundary_vertex_count (S := S) (S_e := S_e) a b G e φ G_e hCut u v heV u' v' huniq
      hne' hbde hGVe hcapE
  have hg : {C ∈ cuffs S_e | (G_e.V ∩ C).ncard ≤ 1}.ncard ≤ 1 := by
    exact few_small_cuffs_after_cut (S := S) (S_e := S_e) a b G e φ G_e hCut hSe u v hucap hvcap
      H₀ u' hu v' hv huniq hne' H' hmat hGVe
  have hvm : 2 * k ≤ vModel a b 2 k := by
    unfold vModel
    omega
  have hk : 2 ≤ k := by omega
  have halpha : 9 * k * vSurface S_e k < alpha G_e := by
    have h1 : vSurface S_e k ≤ vModel a b 2 k := vSurface_le_vModel hCut.homeo_model k
    set w := vModel a b 2 k
    have h2 : 9 * k * vSurface S_e k ≤ 9 * k * w := Nat.mul_le_mul_left _ h1
    have h3' : 9 * k * w + 1 ≤ 28 * k * w / 3 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      nlinarith
    omega
  refine ⟨H', hforest, hbdE, by omega, halpha, ?_⟩
  -- Feasibility comes down.
  rintro ⟨H₁, hH₁, ⟨α', hα'fix, hhom⟩, hsub⟩
  obtain ⟨α, hcomm⟩ := hCut.exists_descent α' hα'fix
  have hαfix : ∀ x ∈ bd S, α x = x := fun x hx => by
    obtain ⟨y, rfl⟩ := hs x
    rw [← hcomm, hα'fix y ((hbde y).mpr (.inl hx))]
  set H₂ := cutImage G φ H₁ with hH₂
  have m₂ : IsMatched H₁ H₂ φ ∅ := hCut.matched_cutImage hsub
  have hBfix : α' '' {u', v'} = {u', v'} := by
    rw [image_pair, hα'fix u' ((hbde _).mpr (.inr (hu ▸ hucap.1))),
      hα'fix v' ((hbde _).mpr (.inr (hv ▸ hvcap.1)))]
  have m₁ : IsMatched (mapDrawingHomeo α' H') (mapDrawingHomeo α H₀) φ {u', v'}
    := hBfix ▸ hmat.map α' α hcomm
  have hbdhom : (mapDrawingHomeo α' H').V ∩ bd S_e = H₁.V ∩ bd S_e := hhom.2.2.2.2.1
  have hp₂ : H₂.IsProper := by
    rintro x ⟨hb, hU⟩
    rw [← m₂.image_U, sdiff_empty] at hU
    obtain ⟨y, hy, rfl⟩ := hU
    rw [← m₂.image_V, sdiff_empty]
    exact ⟨y, hH₁.1 ⟨(hbde y).mpr (.inl hb), hy⟩, rfl⟩
  have hlift : ∀ s ∈ (mapDrawingHomeo α H₀).V ∩ bd S, ∃ x, φ x = s ∧ x ∈
    (mapDrawingHomeo α' H').V \ {u', v'} ∧ x ∈ bd S_e ∧ x ∈ H₁.V \ ∅ := by
    rintro _ ⟨⟨y, hy, rfl⟩, hb⟩
    have hyb : y = α y := by
      apply α.injective
      rw [hαfix _ hb]
    rw [← hyb] at hb ⊢
    obtain ⟨x, rfl⟩ := hs y
    have hxb : x ∈ bd S_e := (hbde x).mpr (.inl hb)
    have hxV : x ∈ (mapDrawingHomeo α' H').V := ⟨x, (hVd x).mpr (.inl hy), hα'fix x hxb⟩
    have hx₁ : x ∈ H₁.V ∩ bd S_e := by
      rw [← hbdhom]
      exact ⟨hxV, hxb⟩
    refine ⟨x, rfl, ⟨hxV, ?_⟩, hxb, hx₁.1, not_false⟩
    rintro (rfl | rfl)
    · exact huU _ (hu ▸ hucap.1) (H₀.V_subset_U hy)
    · exact huU _ (hv ▸ hvcap.1) (H₀.V_subset_U hy)
  have hV : (mapDrawingHomeo α H₀).V ∩ bd S = H₂.V ∩ bd S := by
    ext s
    constructor
    · intro h1
      obtain ⟨x, rfl, -, -, hx, -⟩ := hlift s h1
      refine ⟨?_, h1.2⟩
      rw [← m₂.image_V, sdiff_empty]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨h1, hb⟩
      rw [← m₂.image_V, sdiff_empty] at h1
      obtain ⟨x, hx, rfl⟩ := h1
      have hxb : x ∈ bd S_e := (hbde x).mpr (.inl hb)
      have h2 : x ∈ (mapDrawingHomeo α' H').V ∩ bd S_e := by
        rw [hbdhom]
        exact ⟨hx, hxb⟩
      obtain ⟨z, hz, hzx⟩ := h2.1
      have hzeq : z = x := by
        apply α'.injective
        rw [hzx, hα'fix x hxb]
      subst hzeq
      refine ⟨⟨φ z, ?_, hαfix _ hb⟩, hb⟩
      rcases (hVd z).mp hz with h3 | h3 | h3
      · exact h3
      · exact absurd hb (hbdoff _ (h3 ▸ hucap.1))
      · exact absurd hb (hbdoff _ (h3 ▸ hvcap.1))
  have hfin := m₁.forestsHomotopic m₂ hhom (hH₀.map_homeo α).1 hp₂ hV hlift
  refine ⟨H₂, ⟨hp₂, m₂.isGraphForest_iff.mp hH₁.2⟩, ⟨β.trans α, fun x hx => ?_, ?_⟩,
    Drawing.span_isSubdrawing _ _ _⟩
  · simp [Homeomorph.trans_apply, hβfix x hx, hαfix x hx]
  · rw [← mapDrawingHomeo_trans]
    exact hfin

end GraphMinor.GM07
