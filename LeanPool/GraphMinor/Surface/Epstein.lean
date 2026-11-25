/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutRetract

/-!
# Null-homotopic `O`-arcs bound discs

We prove `EpsteinStatement`. The hard part says that a null-homotopic `O`-arc `F` in a set `Z` of a
surface bounds a closed disc
inside `Z`.

We cut the surface along `F`. Words of the pieces with values in a finite group show that `F`
separates and that one piece is a disc
(`CutNull.lean`). Say that this disc does not lie in `Z`. Then a null-homotopy misses a point of the
disc, so we can push it out of
the disc, and we get a null-homotopy of the cuff of the other piece, inside this other piece. So the
other piece is a disc too. If it
also does not lie in `Z`, then we can push out of it as well, and we get a null-homotopy of the
identity map of the circle, which
is impossible.

Epstein's Theorem 1.7 gives the ambient result using covering spaces. Robertson and Seymour's
Graph Minors XI (7.2) gives the relative disc containment proved here.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u

section two

variable {S Y : Type u} [TopologicalSpace S] [TopologicalSpace Y] [T2Space S] [T2Space Y]
  [CompactSpace Y]

/-- The two pieces of a surface that was cut along a separating `O`-arc. -/
structure TwoSides (ψ : Y → S) (F : Set S) (W₁ W₂ X X' : Set Y) : Prop where
  hψ : IsCutting ψ F
  c₁ : IsClopen W₁
  c₂ : IsClopen W₂
  hU : W₁ ∪ W₂ = univ
  hd : Disjoint W₁ W₂
  hX : X ⊆ W₁
  hX' : X' ⊆ W₂
  hun : X ∪ X' = ψ ⁻¹' F
  b : BijOn ψ X F
  b' : BijOn ψ X' F
  hbd : X ⊆ bd Y
  hbd' : X' ⊆ bd Y

variable {ψ : Y → S} {F : Set S} {W₁ W₂ X X' : Set Y}

omit [T2Space S] [T2Space Y] [CompactSpace Y] in
theorem TwoSides.symm (T : TwoSides ψ F W₁ W₂ X X') : TwoSides ψ F W₂ W₁ X' X :=
  ⟨T.hψ, T.c₂, T.c₁, by rw [union_comm, T.hU], T.hd.symm, T.hX', T.hX, by rw [union_comm, T.hun],
    T.b', T.b, T.hbd', T.hbd⟩

omit [T2Space S] [T2Space Y] [CompactSpace Y] in
theorem TwoSides.mem_of_mem (T : TwoSides ψ F W₁ W₂ X X') {y : Y} (hy : y ∈ W₁)
  (hF : ψ y ∈ F) : y ∈ X := by
  have h : y ∈ X ∪ X' := by
    rw [T.hun]
    exact hF
  exact h.resolve_right fun h' => disjoint_left.mp T.hd hy (T.hX' h')

omit [T2Space S] [T2Space Y] [CompactSpace Y] in
theorem TwoSides.inj (T : TwoSides ψ F W₁ W₂ X X') : Function.Injective fun y : W₁ => ψ y.1 := by
  intro a b he
  simp only at he
  by_cases h : ψ a.1 ∈ F
  · exact Subtype.ext (T.b.injOn (T.mem_of_mem a.2 h) (T.mem_of_mem b.2 (he ▸ h)) he)
  · exact Subtype.ext (T.hψ.2.2.1 h (show ψ b.1 ∈ Fᶜ from he ▸ h) he)

omit [T2Space S] [T2Space Y] [CompactSpace Y] in
theorem TwoSides.mem_cross (T : TwoSides ψ F W₁ W₂ X X') {a b : Y} (ha : a ∈ W₁) (hb : b ∈ W₂)
  (he : ψ a = ψ b) : a ∈ X := by
  have hne : a ≠ b := fun h => disjoint_left.mp T.hd ha (h ▸ hb)
  refine T.mem_of_mem ha ?_
  by_contra h
  exact hne (T.hψ.2.2.1 h (show ψ b ∈ Fᶜ from he ▸ h) he)

omit [T2Space Y] in
/-- If one piece is a disc, then its image is a closed disc bounded by `F`. -/
theorem TwoSides.disc (T : TwoSides ψ F W₁ W₂ X X') (hO : IsOArc F) (e : W₁ ≃ₜ ClosedUnitDisc) :
    IsClosedDisc (ψ '' W₁) ∧ discBd (ψ '' W₁) = F ∧ ∀ x : W₁, x ∈ bd W₁ ↔ ψ x.1 ∈ F := by
  have hcW : CompactSpace W₁ := isCompact_iff_compactSpace.mp T.c₁.1.isCompact
  have cψ := T.hψ.1
  let j : W₁ → ψ '' W₁ := fun y => ⟨ψ y.1, mem_image_of_mem _ y.2⟩
  have cj : Continuous j := Continuous.subtype_mk (cψ.comp continuous_subtype_val) _
  have bj : Function.Bijective j := by
    refine ⟨fun a b he => T.inj (congrArg Subtype.val he), ?_⟩
    rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  let e₂ : W₁ ≃ₜ ψ '' W₁ := cj.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j bj)
  have hD : IsClosedDisc (ψ '' W₁) := ⟨e.symm.trans e₂⟩
  have himg := image_bd_homeomorph e₂
  have hto : ∀ x : W₁, x ∈ bd W₁ → ψ x.1 ∈ discBd (ψ '' W₁) := fun x hx =>
    ⟨e₂ x, himg ▸ mem_image_of_mem _ hx, rfl⟩
  have hsub : F ⊆ discBd (ψ '' W₁) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := T.b.surjOn hx
    exact hto ⟨y, T.hX hy⟩ ((mem_bd_sub T.c₁.2).mpr (T.hbd hy))
  obtain ⟨φ⟩ := hD.isOArc_discBd
  have hF := oarc_eq φ hO hsub
  refine ⟨hD, hF.symm, fun x => ⟨fun hx => hF ▸ hto x hx, fun hx => ?_⟩⟩
  exact (mem_bd_sub T.c₁.2).mpr (T.hbd (T.mem_of_mem x.2 hx))

omit [T2Space Y] in
/-- If one piece is a disc, a null-homotopy that misses a point of the disc moves to the other
piece. -/
theorem TwoSides.move (T : TwoSides ψ F W₁ W₂ X X') (hO : IsOArc F) (e : W₁ ≃ₜ ClosedUnitDisc)
  (φ : Circle ≃ₜ F)
    {H : C(Circle × unitInterval, S)} {c₀ : S} (h0 : ∀ x, H (x, 0) = (φ x).1) (h1 : ∀ x, H (x, 1)
      = c₀) {z : W₁} (hz : ∀ p, H p ≠ ψ z.1)
    (hzF : ψ z.1 ∉ F) {C : Set W₂} (φC : Circle ≃ₜ C) (hC : ∀ x : C, ψ x.1.1 ∈ F) (hne :
      (Nonempty W₂)) :
    ∃ (H' : C(Circle × unitInterval, W₂)) (c : W₂), (∀ x, H' (x, 0) = (φC x).1) ∧ (∀ x, H' (x, 1)
      = c) ∧ ∀ p, ψ (H' p).1 ∈ F ∨ ∃ q, ψ (H' p).1 = H q := by
  have hcW : CompactSpace W₁ := isCompact_iff_compactSpace.mp T.c₁.1.isCompact
  have hcW' : CompactSpace W₂ := isCompact_iff_compactSpace.mp T.c₂.1.isCompact
  obtain ⟨hD, hbdF, hb⟩ := T.disc hO e
  obtain ⟨d⟩ := isClosedDisc_closedBall.1
  have hzb : z ∉ bd W₁ := fun h => hzF ((hb z).mp h)
  obtain ⟨R, cR, hR, hfix⟩ := exists_ret (e.trans d) hzb
  have hzn : Nonempty W₁ := ⟨z⟩
  have c₁ : Continuous fun y : W₁ => ψ y.1 := T.hψ.1.comp continuous_subtype_val
  have c₂ : Continuous fun y : W₂ => ψ y.1 := T.hψ.1.comp continuous_subtype_val
  have hu : range (fun y : W₁ => ψ y.1) ∪ range (fun y : W₂ => ψ y.1) = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨y, rfl⟩ := T.hψ.2.1 x
    have : y ∈ W₁ ∪ W₂ := T.hU ▸ mem_univ y
    rcases this with h | h
    · exact .inl ⟨⟨y, h⟩, rfl⟩
    · exact .inr ⟨⟨y, h⟩, rfl⟩
  have hB : ∀ x ∈ bd W₁, ψ x.1 ∈ range fun y : W₂ => ψ y.1 := fun x hx => by
    obtain ⟨y, hy, he⟩ := T.b'.surjOn ((hb x).mp hx)
    exact ⟨⟨y, T.hX' hy⟩, he⟩
  have hB' : ∀ (x : W₁) (y : W₂), ψ x.1 = ψ y.1 → x ∈ bd W₁ := fun x y he =>
    (mem_bd_sub T.c₁.2).mpr (T.hbd (T.mem_cross x.2 y.2 he))
  obtain ⟨g, g1, g2, g3⟩ := retract_two c₁ c₂ T.inj T.symm.inj hu hB hB' cR hR hfix
  have cG := g3 H H.continuous hz
  have cθ : Continuous fun x => φ.symm ⟨ψ (φC x).1.1, hC _⟩ :=
    φ.symm.continuous.comp (Continuous.subtype_mk
      (T.hψ.1.comp (continuous_subtype_val.comp (continuous_subtype_val.comp φC.continuous))) _)
  refine ⟨⟨fun p => g (H (φ.symm ⟨ψ (φC p.1).1.1, hC _⟩, p.2)), ?_⟩, g c₀, fun x => ?_,
    fun x => ?_, fun p => ?_⟩
  · exact cG.comp (Continuous.prodMk (cθ.comp continuous_fst) continuous_snd)
  · change g (H (φ.symm ⟨ψ (φC x).1.1, hC _⟩, 0)) = _
    rw [h0, φ.apply_symm_apply]
    exact g1 _
  · change g (H (φ.symm ⟨ψ (φC x).1.1, hC _⟩, 1)) = _
    rw [h1]
  · obtain ⟨x, t⟩ := p
    change ψ (g (H (φ.symm ⟨ψ (φC x).1.1, hC _⟩, t))).1 ∈ F ∨ ∃ q, ψ (g (H (φ.symm ⟨ψ
      (φC x).1.1, hC _⟩, t))).1 = H q
    obtain ⟨q, hq⟩ : ∃ q, q = (φ.symm ⟨ψ (φC x).1.1, hC _⟩, t) := ⟨_, rfl⟩
    rw [← hq]
    by_cases h : H q ∈ range fun y : W₂ => ψ y.1
    · obtain ⟨y, hy⟩ := h
      right
      refine ⟨q, ?_⟩
      rw [← hy, g1]
    · left
      obtain ⟨y, hy, he⟩ := g2 _ h (hz q)
      show ψ (g (H q)).1 ∈ F
      have := (hb y).mp hy
      simp only at he
      rwa [he] at this

/-- If one piece is a disc, then `F` bounds a disc in `Z`. -/
theorem TwoSides.of_disc (_hS : IsSurface Y) (T : TwoSides ψ F W₁ W₂ X X') (hO : IsOArc F)
  (hOX' : IsOArc X') (e : W₁ ≃ₜ ClosedUnitDisc) (φ : Circle ≃ₜ F)
    {Z : Set S} (hFZ : F ⊆ Z) {H : C(Circle × unitInterval, S)} {c₀ : S} (h0 : ∀ x, H (x, 0) =
      (φ x).1) (h1 : ∀ x, H (x, 1) = c₀) (hHZ : ∀ p, H p ∈ Z)
    {a b c : ℕ} (e₂ : W₂ ≃ₜ SurfaceModel a b c) : ∃ Δ, Δ ⊆ Z ∧ IsClosedDisc Δ ∧ discBd Δ = F := by
  obtain ⟨hD, hbdF, hb⟩ := T.disc hO e
  by_cases h₁ : ψ '' W₁ ⊆ Z
  · exact ⟨_, h₁, hD, hbdF⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, hzZ⟩ := not_subset.mp h₁
  have hne' : X'.Nonempty := by
    obtain ⟨e'⟩ := id hOX'
    exact ⟨_, (e' 1).2⟩
  obtain ⟨C, hC, hsub⟩ := exists_cuff_sub T.c₂.2 hOX'.isPreconnected hne' T.hX' T.hbd'
  obtain ⟨i, hi, φC, g, hg, hs⟩ := exists_one_hole e₂ hC
  have eX' := oarc_eq (hatC φC) hOX' (by
    intro x hx
    exact hsub hx)
  have hCF : ∀ x : C, ψ x.1.1 ∈ F := fun x => T.b'.mapsTo (by
    rw [eX']
    exact mem_image_of_mem _ x.2)
  obtain ⟨H', c', h0', h1', hH'⟩ := T.move hO e φ h0 h1 (z := ⟨y, hy⟩) (fun p he => hzZ
    (he ▸ hHZ p)) (fun h => hzZ (hFZ h)) φC hCF
    ⟨(φC 1).1⟩
  by_cases hd : a = 0 ∧ b = 0 ∧ c = 1
  · obtain ⟨rfl, rfl, rfl⟩ := hd
    obtain ⟨d⟩ := nonempty_disc_homeo
    obtain ⟨hD₂, hbdF₂, hb₂⟩ := T.symm.disc hO (e₂.trans d)
    by_cases h₂ : ψ '' W₂ ⊆ Z
    · exact ⟨_, h₂, hD₂, hbdF₂⟩
    exfalso
    obtain ⟨_, ⟨y₂, hy₂, rfl⟩, hzZ₂⟩ := not_subset.mp h₂
    obtain ⟨d'⟩ := isClosedDisc_closedBall.1
    obtain ⟨R, cR, hR, hfix⟩ := exists_ret (t := (⟨y₂, hy₂⟩ : W₂)) ((e₂.trans d).trans d') fun h
      => hzZ₂ (hFZ ((hb₂ _).mp h))
    have hmem : ∀ x : W₂, x ∈ bd W₂ → x ∈ C := fun x hx => by
      have h3 : x.1 ∈ X' := T.symm.mem_of_mem x.2 ((hb₂ x).mp hx)
      rw [eX'] at h3
      obtain ⟨x', hx', he⟩ := h3
      rwa [← Subtype.ext he]
    have hav : ∀ p, H' p ≠ ⟨y₂, hy₂⟩ := fun p he => by
      have h3 := hH' p
      rw [he] at h3
      rcases h3 with h3 | ⟨q, h3⟩
      · exact hzZ₂ (hFZ h3)
      · exact hzZ₂ (h3 ▸ hHZ q)
    have cR' : Continuous fun p => R (H' p) := cR.comp_continuous H'.continuous hav
    let G : C(Circle × unitInterval, Circle) := ⟨fun p => φC.symm ⟨R (H' p), hmem _ (hR _ (hav p))⟩,
      φC.symm.continuous.comp (Continuous.subtype_mk cR' _)⟩
    have hC' : ∀ x, (φC x).1 ∈ bd W₂ := fun x => (hb₂ _).mpr (hCF _)
    refine circle_not_null G (c := G (1, 1)) (fun x => ?_) fun x => ?_
    · change φC.symm ⟨R (H' (x, 0)), _⟩ = x
      rw [φC.symm_apply_eq]
      apply Subtype.ext
      change R (H' (x, 0)) = _
      rw [h0', hfix _ (hC' x)]
    · change φC.symm ⟨R (H' (x, 1)), _⟩ = φC.symm ⟨R (H' (1, 1)), _⟩
      congr 2
      rw [h1', h1']
  · exfalso
    obtain ⟨hN, hL⟩ := erase_facts c i
    have hne : 0 < a ∨ 0 < b ∨ (List.range' 0 c).erase i ≠ [] := by
      by_contra h
      push Not at h
      have hl := length_erase_range hi
      rw [h.2.2] at hl
      simp only [List.length_nil] at hl
      exact hd ⟨by omega, by omega, by omega⟩
    exact not_null_C hi hN hL hne hg hs ⟨φC, H', c', h0', h1'⟩ (by
      refine ContinuousOn.comp_continuous continuousOn_id ?_ (fun _ => mem_univ _) |>.continuousOn
      exact continuous_subtype_val.comp (φC.continuous.comp continuous_ee))
      (by simp only [ee_one]) fun u _ => (φC (ee u)).2

end two

/-- A null-homotopic `O`-arc in a set `Z` of a surface, off the boundary, bounds a closed disc in
`Z`. -/
theorem epstein_first {S : Type u} [TopologicalSpace S] [ConnectedSpace S] {Z F : Set S}
  (hS : IsSurface S) (hO : IsOArc F) (hFZ : F ⊆ Z)
    (hd : Disjoint F (bd S)) (hnull : IsNullHomotopicOArcIn Z F) : ∃ Δ, Δ ⊆ Z ∧ IsClosedDisc Δ
      ∧ discBd Δ = F := by
  have hcS : CompactSpace S := hS.1
  have ht2 : T2Space S := hS.2.1
  obtain ⟨φF, c₀, hc₀, H, hHZ, h0, h1⟩ := hnull
  have hNS : NullIn F := ⟨φF, H, c₀, h0, h1⟩
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, hcase, Z₁, Z₂, u, c, X₁, Y₁, X₂, Y₂, h7, h8, hi, hun, huc, hfu,
    hfc⟩ := exists_cut_loop hS hO hd
  have hcY : CompactSpace Y := hY.1
  have hdcuff := cuff_statement.{u} Y hY
  rcases hcase with ⟨X, X', hdX, hunX, hOX, hOX', b1, b2⟩ | hQ
  · have ne₁ : X.Nonempty := by
      obtain ⟨e⟩ := id hOX
      exact ⟨_, (e 1).2⟩
    have ne₂ : X'.Nonempty := by
      obtain ⟨e⟩ := id hOX'
      exact ⟨_, (e 1).2⟩
    obtain ⟨x, hx⟩ := ne₁
    obtain ⟨y, hy⟩ := ne₂
    have hXb : X ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hunX ▸ Or.inl hz)
    have hXb' : X' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hunX ▸ Or.inr hz)
    rcases cut_comps hψ hY hOX.isPreconnected hOX'.isPreconnected hunX hx hy with hYc | ⟨W₁, W₂,
      hne', hsc, hX₁, hX₂, hW₁, hW₂, hU, hdW, hc₁, hc₂⟩
    · exfalso
      obtain ⟨a, b, c, ⟨e⟩⟩ := classification.{u} Y hY hYc
      have hC : connectedComponentIn (bd Y) x ∈ cuffs Y := ⟨_, hXb hx, rfl⟩
      have hC' : connectedComponentIn (bd Y) y ∈ cuffs Y := ⟨_, hXb' hy, rfl⟩
      obtain ⟨φ₀⟩ := hdcuff.2.2 _ hC
      obtain ⟨φ₀'⟩ := hdcuff.2.2 _ hC'
      have eX := oarc_eq φ₀ hOX (hOX.isPreconnected.subset_connectedComponentIn hx hXb)
      have eX' := oarc_eq φ₀' hOX' (hOX'.isPreconnected.subset_connectedComponentIn hy hXb')
      have hCC : connectedComponentIn (bd Y) x ≠ connectedComponentIn (bd Y) y := by
        intro he
        rw [← eX, ← eX'] at he
        exact Set.disjoint_left.mp hdX hx (he ▸ hx)
      obtain ⟨i, hi', j, hj, hij, φ, φ', g, hg, hs, hs'⟩ := exists_two_holes e hC hC' hCC
      obtain ⟨hN, hLf⟩ := erase_erase_facts c i j
      rw [eX, eX'] at hunX
      rw [eX] at b1
      rw [eX'] at b2
      have hdis := cuffs_disjoint hC hC' hCC
      obtain ⟨σ, g', hp, hs₂⟩ := loop_two_aux hY hψ hC' (hdcuff.2.2 _ hC).isCompact.isClosed
        (hdcuff.2.2 _ hC').isCompact.isClosed hdis hunX b1 b2 φ φ'
        hij hi' hj hLf hg hs hs'
      refine not_null_E hij hi' hj hN hLf hp hs₂ hNS ?_ (by simp only [ee_one]) fun u _
        => b1.mapsTo (φ (ee u)).2
      exact (hψ.1.comp (continuous_subtype_val.comp (φ.continuous.comp continuous_ee))).continuousOn
    · have T : TwoSides ψ F W₁ W₂ X X' := ⟨hψ, hW₁, hW₂, hU, hdW, hX₁, hX₂, hunX, b1, b2, hXb, hXb'⟩
      obtain ⟨a₁, b₁, c₁, ⟨e₁⟩⟩ := classification.{u} W₁ (isSurface_sub hY hW₁) hc₁
      obtain ⟨a₂, b₂, c₂, ⟨e₂⟩⟩ := classification.{u} W₂ (isSurface_sub hY hW₂) hc₂
      obtain ⟨d⟩ := nonempty_disc_homeo
      by_cases h1' : a₁ = 0 ∧ b₁ = 0 ∧ c₁ = 1
      · obtain ⟨rfl, rfl, rfl⟩ := h1'
        exact T.of_disc hY hO hOX' (e₁.trans d) φF hFZ h0 h1 hHZ e₂
      by_cases h2' : a₂ = 0 ∧ b₂ = 0 ∧ c₂ = 1
      · obtain ⟨rfl, rfl, rfl⟩ := h2'
        exact T.symm.of_disc hY hO hOX (e₂.trans d) φF hFZ h0 h1 hHZ e₁
      exfalso
      obtain ⟨i, j, σ, f, ρ, q, hi', hj, hf, hq, hs, cρ, hcl, hρ⟩ := loop_comps_aux hY hψ hunX b1
        b2 hOX hOX' hW₁ hW₂ hdW hU e₁ e₂ hX₁ hX₂ hXb hXb'
      obtain ⟨hN₁, hL₁⟩ := erase_facts c₁ i
      obtain ⟨hN₂, hL₂⟩ := erase_facts c₂ j
      have hne₁ : 0 < a₁ ∨ 0 < b₁ ∨ (List.range' 0 c₁).erase i ≠ [] := by
        by_contra h
        push Not at h
        have hl := length_erase_range hi'
        rw [h.2.2] at hl
        simp only [List.length_nil] at hl
        exact h1' ⟨by omega, by omega, by omega⟩
      have hne₂ : 0 < a₂ ∨ 0 < b₂ ∨ (List.range' 0 c₂).erase j ≠ [] := by
        by_contra h
        push Not at h
        have hl := length_erase_range hj
        rw [h.2.2] at hl
        simp only [List.length_nil] at hl
        exact h2' ⟨by omega, by omega, by omega⟩
      exact not_null_B (F := F) (ρ := fun u => ψ (ρ u)) hi' hj hN₁ hN₂ hL₁ hL₂ hne₁ hne₂ hf hq hs
        hNS (hψ.1.comp_continuousOn cρ)
        (congrArg ψ hcl) fun u hu => b1.mapsTo (hρ u hu)
  · exfalso
    have ne₀ : (ψ ⁻¹' F).Nonempty := by
      obtain ⟨e⟩ := id hQ
      exact ⟨_, (e 1).2⟩
    have hYc := connected_of_cut hψ hY hQ.isPreconnected rfl ne₀
    obtain ⟨a, b, c', ⟨e⟩⟩ := classification.{u} Y hY hYc
    obtain ⟨x, hx⟩ := ne₀
    have hQb := hψ.2.2.2.2
    have hC : connectedComponentIn (bd Y) x ∈ cuffs Y := ⟨_, hQb hx, rfl⟩
    obtain ⟨φ₀⟩ := hdcuff.2.2 _ hC
    have eQ := oarc_eq φ₀ hQ (hQ.isPreconnected.subset_connectedComponentIn hx hQb)
    obtain ⟨i, hi', φ, g, hg, hs⟩ := exists_one_hole e hC
    obtain ⟨hN, hLf⟩ := erase_facts c' i
    obtain ⟨a₀, ξ, η, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := h7.paths h8 hi huc hfu hfc hψ.1
    rw [hun] at c5 c6
    have L : ArcLift ψ F a₀ ξ η := ⟨c1, c2, c3, c4, c5, fun y y' he hne' => by
      by_cases hy : ψ y ∈ F
      · exact c6 y y' he hne' hy
      · exact absurd (hψ.2.2.1 hy (show ψ y' ∈ Fᶜ from he ▸ hy) he) hne'⟩
    have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have hξ : ∀ t ∈ Icc (0 : ℝ) 1, ξ t ∈ connectedComponentIn (bd Y) x := fun t ht => by
      rw [← eQ]
      change ψ (ξ t) ∈ F
      rw [c3 t ht, ← c5]
      exact mem_image_of_mem _ ht
    have hη : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ connectedComponentIn (bd Y) x := fun t ht => by
      rw [← eQ]
      change ψ (η t) ∈ F
      rw [c4 t ht, ← c5]
      exact mem_image_of_mem _ ht
    rcases c9 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have injξ : InjOn ξ (Ico 0 1) := fun p hp q hq he => c7 hp hq (by
        rw [← c3 p (Ico_subset_Icc_self hp), ← c3 q (Ico_subset_Icc_self hq), he])
      have him := loop_image φ c1 hξ injξ e1.symm
      obtain ⟨v, hv, hve⟩ := him.symm.subset (hη 0 m0)
      have ha : a₀ v = a₀ 0 := by rw [← c3 v hv, hve, c4 0 m0]
      rcases eq_or_lt_of_le hv.2 with rfl | hv1
      · exact c8 0 m0 (e1.symm.trans hve)
      · have := c7 ⟨hv.1, hv1⟩ ⟨le_rfl, zero_lt_one⟩ ha
        subst this
        exact c8 0 m0 hve
    · obtain ⟨g', a', hp, hs₂, h3, h4, h5⟩ := loop_one_aux hY L hψ.1 hψ.2.1 hC φ hi' hLf hg hs hξ
        hη (conc_inj c3 c4 c7 c8 e1 e2) e1 e2
      exact not_null_D hi' hN hLf hp hs₂ hNS h5 h4 h3

/-- Disc bounding inside the subset of a null-homotopy, as in Robertson and Seymour's
Graph Minors XI (7.2). Their XI (7.1) quotes Epstein's ambient result, Theorem 1.7 of
*Curves on 2-manifolds and isotopies*, Acta Math. 115 (1966) 83–107. -/
theorem epstein : EpsteinStatement.{u} := by
  intro S _ Z F hS hconn hO hFZ hd
  refine ⟨epstein_first hS hO hFZ hd, ?_, ?_⟩
  · rintro ⟨Δ, h1, h2, h3⟩
    exact isNullHomotopicOArcIn_of_subset_disc hO h1 h2 h3
  · intro Δ₁ Δ₂ h1 h2 e1 e2 hns
    exact eq_of_discBd_eq hS hns h1 h2 (e1.trans e2.symm)

end GraphMinor.Surface
