/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# Euler genus after adding a handle

The boundary of the closed cylinder is its two end circles (`bd_cylinder`). Adding a handle removes
two open discs from a closed connected surface `S` and glues a cylinder `S₂` to what is left, `S₁`.
As for a crosscap, we show that `S₁` is a surface, that the closures of the two discs are closed
discs, and that `S₁` has model `Σ(a, b, 2)` when `S` has model `Σ(a, b, 0)`.

To see `S'` we do not cut along both ends of the cylinder. We take a collar of one cuff of `S₁`, and
we stretch this collar so that it covers the collar and the whole cylinder. This is a map from `S₁`
onto `S'` that only glues the two cuffs of `S₁` together (`handle_cut`), and the words of
`CutLoop.lean` then show that `S'` has model `Σ(a + 1, b, 0)` or `Σ(a, b + 2, 0)` (`handle_model`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u

local notation "𝕀" => unitInterval

/-- The end circle of the closed cylinder at height `r`. -/
def cylEnd (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (w : Circle) : ClosedCylinder
  := ⟨(r, w), hr, mem_univ _⟩

theorem isEmbedding_cylEnd (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) : IsEmbedding (cylEnd r hr) := by
  have h1 : Continuous (cylEnd r hr) := by
    unfold cylEnd
    fun_prop
  have h2 : Function.LeftInverse (fun p : ClosedCylinder => p.1.2) (cylEnd r hr) := fun _ => rfl
  exact h2.isEmbedding (by fun_prop) h1

/-- A rotation of the closed cylinder. -/
noncomputable def cylRot (u : Circle) : ClosedCylinder ≃ₜ ClosedCylinder :=
  Homeomorph.subtype ((Homeomorph.refl ℝ).prodCongr (Homeomorph.mulLeft u)) (fun p
    => by simp [ClosedCylinder])

theorem cylinder_interior {p : ClosedCylinder} (h1 : 1 < p.1.1) (h2 : p.1.1 < 2) : IsInteriorPoint
  p := by
  revert h1 h2
  obtain ⟨⟨r, u⟩, hr, -⟩ := p
  intro (h1 : 1 < r) (h2 : r < 2)
  set d : ℝ := 2 * r - 3 with hd
  let w : ℂ := ⟨d / 2, -(d / 2)⟩
  have hw : nn w < 1 := by
    simp only [nn, w]
    rw [abs_neg]
    rcases abs_cases (d / 2) with h3 | h3 <;> linarith
  have hz : ‖mu w‖ < 1 := by rwa [norm_mu]
  have hmem : ((0 : ℕ), mu w) ∈ Dsk (sW cylW) := by
    refine ⟨?_, hz.le⟩
    rw [sW_zero]
    simp [cylW]
  have hz' : ‖((0 : ℕ), mu w).2‖ < 1 := hz
  have h3 : IsInteriorPoint ((fun a : ℕ × ℂ => cylG a.2) (0, mu w)) := isInteriorPoint_of_lt (W
    := sW cylW) (finW_sW cylW) presents_cyl hmem hz'
  replace h3 : IsInteriorPoint (cylG (mu w)) := h3
  have h4 : cylG (mu w) = ⟨(r, 1), hr, mem_univ _⟩ := by
    apply Subtype.ext
    apply Prod.ext
    · rw [cylG_fst hz.le]
      simp only [cylR, nu_mu, w]
      linarith
    · rw [cylG_snd]
      simp only [cylS, nu_mu, w]
      have : ee ((d / 2 + -(d / 2)) / 2) = 1 := by
        rw [show (d / 2 + -(d / 2)) / 2 = (0 : ℝ) by ring]
        simp [ee]
      exact this
  have h5 : cylRot u ⟨(r, 1), hr, mem_univ _⟩ = ⟨(r, u), hr, mem_univ _⟩ := by
    exact Subtype.ext (Prod.ext rfl (mul_one u))
  rw [h4] at h3
  rw [← h5]
  exact (isInteriorPoint_homeomorph_iff (cylRot u) _).mpr h3

/-- A component of the boundary from a splitting of the boundary into two closed sets. -/
theorem cuff_of_split {Y : Type u} [TopologicalSpace Y] {A B : Set Y} (hA : IsClosed A)
  (hB : IsClosed B) (hd : Disjoint A B) (hu : A ∪ B = bd Y) (hc : IsConnected A) :
    A ∈ cuffs Y := by
  obtain ⟨x, hx⟩ := hc.1
  have hAb : A ⊆ bd Y := hu ▸ subset_union_left
  refine ⟨x, hAb hx, ?_⟩
  apply subset_antisymm
  · have h1 : IsPreconnected (connectedComponentIn (bd Y) x) := isPreconnected_connectedComponentIn
    have h2 : connectedComponentIn (bd Y) x ⊆ A ∪ B := hu ▸ connectedComponentIn_subset _ _
    have hdis : Disjoint B A := hd.symm
    rcases isPreconnected_closed_iff.mp h1 with h3
    by_contra hn
    obtain ⟨z, hz, hzA⟩ := not_subset.mp hn
    have hzB : z ∈ B := (h2 hz).resolve_left hzA
    obtain ⟨y, -, hy1, hy2⟩ := h3 A B hA hB h2 ⟨x, mem_connectedComponentIn
      (hAb hx), hx⟩ ⟨z, hz, hzB⟩
    exact Set.disjoint_left.mp hd hy1 hy2
  · exact hc.2.subset_connectedComponentIn hx hAb

/-- The boundary of the closed cylinder is the union of its two end circles. -/
theorem bd_cylinder : bd ↥ClosedCylinder = range (cylEnd 1 (by norm_num)) ∪ range (cylEnd 2
  (by norm_num)) := by
  set A₁ := range (cylEnd 1 (by norm_num)) with hA₁
  set A₂ := range (cylEnd 2 (by norm_num)) with hA₂
  have memA₁ : ∀ p : ClosedCylinder, p.1.1 = 1 → p ∈ A₁ := fun p hp => ⟨p.1.2, Subtype.ext
    (Prod.ext hp.symm rfl)⟩
  have memA₂ : ∀ p : ClosedCylinder, p.1.1 = 2 → p ∈ A₂ := fun p hp => ⟨p.1.2, Subtype.ext
    (Prod.ext hp.symm rfl)⟩
  have hsub : bd ↥ClosedCylinder ⊆ A₁ ∪ A₂ := fun p hp => by
    have h1 := p.2.1.1
    have h2 := p.2.1.2
    rcases h1.lt_or_eq with h3 | h3
    · rcases h2.lt_or_eq with h4 | h4
      · exact absurd (cylinder_interior h3 h4) hp
      · exact .inr (memA₂ p h4)
    · exact .inl (memA₁ p h3.symm)
  obtain ⟨m⟩ := nonempty_cyl_homeo
  obtain ⟨ht, f, hf⟩ := presents_ew 0 0 2
  have h2 := ncard_cuffs (presents_comp hf m)
  obtain ⟨C₁, C₂, hne, hC⟩ := Set.ncard_eq_two.mp h2
  have hcase : ∀ C ∈ cuffs ↥ClosedCylinder, C = A₁ ∨ C = A₂ := by
    have hS : IsSurface ↥ClosedCylinder := isSurface_of_homeo m (isSurface_model 0 0 2).1
    intro C hC'
    have hO := (cuff_statement.{0} _ hS).2.2 C hC'
    have hCb : C ⊆ bd ↥ClosedCylinder := by
      obtain ⟨x, -, rfl⟩ := hC'
      exact connectedComponentIn_subset _ _
    have o1 : IsOpen {p : ClosedCylinder | p.1.1 < 3 / 2} := isOpen_lt
      (by fun_prop) continuous_const
    have o2 : IsOpen {p : ClosedCylinder | 3 / 2 < p.1.1} := isOpen_lt continuous_const
      (by fun_prop)
    have hcov : C ⊆ {p : ClosedCylinder | p.1.1 < 3 / 2} ∪ {p : ClosedCylinder | 3 / 2 < p.1.1}
      := fun p hp => by
      rcases hsub (hCb hp) with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · refine .inl ?_
        change (1 : ℝ) < 3 / 2
        norm_num
      · refine .inr ?_
        change (3 / 2 : ℝ) < 2
        norm_num
    rcases hO.isPreconnected.subset_or_subset o1 o2 (Set.disjoint_left.mpr fun p
      (h3 : p.1.1 < 3 / 2) (h4 : 3 / 2 < p.1.1) => absurd h3 (not_lt.mpr h4.le)) hcov with h3 | h3
    · left
      exact oarc_eq (isEmbedding_cylEnd 1 (by norm_num)).toHomeomorph hO fun p hp => by
        rcases hsub (hCb hp) with h5 | ⟨w, rfl⟩
        · exact h5
        · exact absurd (h3 hp) (by change ¬ ((2 : ℝ) < 3 / 2); norm_num)
    · right
      exact oarc_eq (isEmbedding_cylEnd 2 (by norm_num)).toHomeomorph hO fun p hp => by
        rcases hsub (hCb hp) with ⟨w, rfl⟩ | h5
        · exact absurd (h3 hp) (by change ¬ ((3 / 2 : ℝ) < 1); norm_num)
        · exact h5
  have m1 : C₁ ∈ cuffs ↥ClosedCylinder := by rw [hC]; simp
  have m2 : C₂ ∈ cuffs ↥ClosedCylinder := by rw [hC]; simp
  have sub : ∀ C ∈ cuffs ↥ClosedCylinder, C ⊆ bd ↥ClosedCylinder := by
    rintro _ ⟨x, -, rfl⟩
    exact connectedComponentIn_subset _ _
  apply subset_antisymm hsub
  rcases hcase C₁ m1 with h3 | h3 <;> rcases hcase C₂ m2 with h4 | h4
  · exact absurd (h3.trans h4.symm) hne
  · exact union_subset (h3 ▸ sub C₁ m1) (h4 ▸ sub C₂ m2)
  · exact union_subset (h4 ▸ sub C₂ m2) (h3 ▸ sub C₁ m1)
  · exact absurd (h3.trans h4.symm) hne

variable {S : Type u} [TopologicalSpace S]

/-- The complement of an open disc with a frontier as in `closure_disc` is a surface. -/
theorem compl_surface [ConnectedSpace S] (hS : IsSurface S) (hb : bd S = ∅) {Λ : Set S}
  (hΛ : IsOpen Λ) (hF : IsOArc (closure Λ \ Λ))
    (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ) : IsSurface ↥Λᶜ := by
  have hcS := hS.1
  have ht2 := hS.2.1
  have hsub : Λ ⊆ closure Λ := subset_closure
  have hXc : IsClosed Λᶜ := hΛ.isClosed_compl
  refine ⟨isCompact_iff_compactSpace.mp hXc.isCompact, inferInstance, fun x => ?_⟩
  by_cases hx : x.1 ∈ closure Λ
  · refine (side_manifold hS (T := Λᶜ) (Z := closure Λ) (C := closure Λ \ Λ) (D
      := ∅) hXc isClosed_closure ?_ hF (by rw [hb]; exact disjoint_empty _)
      (fun z hz => hz.2) isClosed_empty ?_ (disjoint_empty _) ?_ ?_ (x := x.1) ⟨hx, x.2⟩).1
    · rw [eq_univ_iff_forall]
      intro z
      by_cases hz : z ∈ Λ
      · exact .inr (hsub hz)
      · exact .inl hz
    · rw [union_empty, inter_comm]
      rfl
    · intro z hz
      have : Λᶜ \ closure Λ = (closure Λ)ᶜ := by
        ext w
        exact ⟨fun h => h.2, fun h => ⟨fun h' => h (hsub h'), h⟩⟩
      rw [this]
      exact hout z hz
    · intro z hz
      have : closure Λ \ Λᶜ = Λ := by
        ext w
        exact ⟨fun h => not_not.mp h.2, fun h => ⟨hsub h, not_not.mpr h⟩⟩
      rw [this]
      exact hz.1
  · have hop : IsOpen (closure Λ)ᶜ := isClosed_closure.isOpen_compl
    have hs : (closure Λ)ᶜ ⊆ Λᶜ := compl_subset_compl.mpr hsub
    exact isManifoldPoint_of_isOpenEmbedding (isOpenEmbedding_inclusion hs hop) (x := ⟨x.1,
      hx⟩) (isManifoldPoint_sub hop (hS.2.2 x.1))

/-- The two `O`-arcs of the boundary of the complement of two open discs are the two frontiers. -/
theorem two_frontiers {Λ₁ Λ₂ : Set S} {X : Set S} (hX : X = (Λ₁ ∪ Λ₂)ᶜ) (hd : Disjoint (closure Λ₁)
  (closure Λ₂)) (h1 : (closure Λ₁ \ Λ₁).Nonempty) (h2 : (closure Λ₂ \ Λ₂).Nonempty)
    (hb : ∀ x : ↥X, x ∈ bd ↥X ↔ x.1 ∈ closure (Λ₁ ∪ Λ₂)) (hΛ₁ : IsOpen Λ₁)
      (hΛ₂ : IsOpen Λ₂) {P₁ P₂ : Set ↥X} (hP₁ : IsPreconnected P₁) (hP₂ : IsPreconnected P₂)
    (hu : P₁ ∪ P₂ = bd ↥X) :
    (Subtype.val '' P₁ = closure Λ₁ \ Λ₁ ∧ Subtype.val '' P₂ = closure Λ₂ \ Λ₂) ∨
      (Subtype.val '' P₁ = closure Λ₂ \ Λ₂ ∧ Subtype.val '' P₂ = closure Λ₁ \ Λ₁) := by
  have hF₁c : IsClosed (closure Λ₁ \ Λ₁) := isClosed_closure.sdiff hΛ₁
  have hF₂c : IsClosed (closure Λ₂ \ Λ₂) := isClosed_closure.sdiff hΛ₂
  have hdF : Disjoint (closure Λ₁ \ Λ₁) (closure Λ₂ \ Λ₂) := hd.mono sdiff_subset sdiff_subset
  have hvb : Subtype.val '' bd ↥X = (closure Λ₁ \ Λ₁) ∪ (closure Λ₂ \ Λ₂) := by
    subst hX
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h3 := (hb y).mp hy
      rw [closure_union] at h3
      have h4 := y.2
      simp only [mem_compl_iff, mem_union, not_or] at h4
      rcases h3 with h3 | h3
      · exact .inl ⟨h3, h4.1⟩
      · exact .inr ⟨h3, h4.2⟩
    · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
      · refine ⟨⟨x, fun h => h.elim h4 fun h' => Set.disjoint_left.mp hd h3 (subset_closure h')⟩,
          (hb _).mpr ?_, rfl⟩
        exact closure_mono subset_union_left h3
      · refine ⟨⟨x, fun h => h.elim (fun h' => Set.disjoint_left.mp hd (subset_closure h') h3) h4⟩,
          (hb _).mpr ?_, rfl⟩
        exact closure_mono subset_union_right h3
  have hside : ∀ P : Set ↥X, IsPreconnected P → P ⊆ bd ↥X → Subtype.val '' P ⊆ closure Λ₁ \ Λ₁
    ∨ Subtype.val '' P ⊆ closure Λ₂ \ Λ₂ := by
    intro P hP hPb
    have h3 := hP.image _ continuous_subtype_val.continuousOn
    have h4 : Subtype.val '' P ⊆ (closure Λ₁ \ Λ₁) ∪ (closure Λ₂ \ Λ₂) := hvb ▸ image_mono hPb
    by_contra hn
    push Not at hn
    obtain ⟨n1, n2⟩ := hn
    obtain ⟨a, ha, ha'⟩ := not_subset.mp n1
    obtain ⟨c, hc, hc'⟩ := not_subset.mp n2
    obtain ⟨z, -, hz1, hz2⟩ := isPreconnected_closed_iff.mp h3 _ _ hF₁c hF₂c h4 ⟨c, hc,
      (h4 hc).resolve_right hc'⟩ ⟨a, ha, (h4 ha).resolve_left ha'⟩
    exact Set.disjoint_left.mp hdF hz1 hz2
  have hu' : Subtype.val '' P₁ ∪ Subtype.val '' P₂ = (closure Λ₁ \ Λ₁) ∪ (closure Λ₂ \ Λ₂) := by
    rw [← image_union, hu, hvb]
  have h1b : P₁ ⊆ bd ↥X := hu ▸ subset_union_left
  have h2b : P₂ ⊆ bd ↥X := hu ▸ subset_union_right
  have key : ∀ {A B F G : Set S}, Disjoint F G → A ∪ B = F ∪ G → A ⊆ F → B ⊆ G → A = F ∧ B = G := by
    intro A B F G hdis hun hA hB
    refine ⟨subset_antisymm hA fun z hz => ?_, subset_antisymm hB fun z hz => ?_⟩
    · rcases (hun ▸ (.inl hz : z ∈ F ∪ G) : z ∈ A ∪ B) with h | h
      · exact h
      · exact absurd (hB h) (Set.disjoint_left.mp hdis hz)
    · rcases (hun ▸ (.inr hz : z ∈ F ∪ G) : z ∈ A ∪ B) with h | h
      · exact absurd hz (Set.disjoint_left.mp hdis (hA h))
      · exact h
  rcases hside P₁ hP₁ h1b with h3 | h3 <;> rcases hside P₂ hP₂ h2b with h4 | h4
  · exfalso
    obtain ⟨z, hz⟩ := h2
    have h5 : z ∈ closure Λ₁ \ Λ₁ := by
      rcases (hu' ▸ (.inr hz) : z ∈ Subtype.val '' P₁ ∪ Subtype.val '' P₂) with h | h
      · exact h3 h
      · exact h4 h
    exact Set.disjoint_left.mp hdF h5 hz
  · exact .inl (key hdF hu' h3 h4)
  · refine .inr ?_
    rw [union_comm] at hu'
    have := key hdF hu' h4 h3
    exact ⟨this.2, this.1⟩
  · exfalso
    obtain ⟨z, hz⟩ := h1
    have h5 : z ∈ closure Λ₂ \ Λ₂ := by
      rcases (hu' ▸ (.inl hz) : z ∈ Subtype.val '' P₁ ∪ Subtype.val '' P₂) with h | h
      · exact h3 h
      · exact h4 h
    exact Set.disjoint_left.mp hdF hz h5

/-- If a closed connected surface has model `Σ(a, b, 0)`, then the surface left by removing two open
discs has a model `Σ(a', b', 2)` with `2 a' + b' = 2 a + b`. -/
theorem handle_hole_model [ConnectedSpace S] (hS : IsSurface S) (hb : bd S = ∅) {Λ₁ Λ₂ : Set S}
  (hΛ₁ : IsOpenDisc Λ₁) (hΛ₂ : IsOpenDisc Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂)) (hX : IsSurface ↥(Λ₁ ∪ Λ₂)ᶜ) {P₁ P₂ : Set ↥(Λ₁ ∪
      Λ₂)ᶜ} (hP₁ : IsOArc P₁) (hP₂ : IsOArc P₂)
    (hu : P₁ ∪ P₂ = bd ↥(Λ₁ ∪ Λ₂)ᶜ) (hdP : Disjoint P₁ P₂) (hv₁ : Subtype.val '' P₁
      = closure Λ₁ \ Λ₁) (hv₂ : Subtype.val '' P₂ = closure Λ₂ \ Λ₂)
    {a b : ℕ} (e : S ≃ₜ SurfaceModel a b 0) :
    ∃ a₁ b₁, Nonempty (↥(Λ₁ ∪ Λ₂)ᶜ ≃ₜ SurfaceModel a₁ b₁ 2) ∧ 2 * a₁ + b₁ = 2 * a + b := by
  classical
  have ht2 := hS.2.1
  have hcS := hS.1
  have hcX : CompactSpace ↥(Λ₁ ∪ Λ₂)ᶜ := hX.1
  have ht2X : T2Space ↥(Λ₁ ∪ Λ₂)ᶜ := hX.2.1
  have hXc : IsClosed (Λ₁ ∪ Λ₂)ᶜ := (hΛ₁.1.union hΛ₂.1).isClosed_compl
  have hint : ∀ x : S, IsInteriorPoint x := fun x => by
    by_contra h
    have h3 : x ∈ bd S := h
    rw [hb] at h3
    exact h3
  have hbX : ∀ x : ↥(Λ₁ ∪ Λ₂)ᶜ, x ∈ bd ↥(Λ₁ ∪ Λ₂)ᶜ ↔ x.1 ∈ closure (Λ₁ ∪ Λ₂) := fun x => by
    have := bd_subset_iff hint x
    rwa [compl_compl] at this
  have hF₁ : IsOArc (closure Λ₁ \ Λ₁) := hv₁ ▸ isOArc_image IsEmbedding.subtypeVal hP₁
  have hF₂ : IsOArc (closure Λ₂ \ Λ₂) := hv₂ ▸ isOArc_image IsEmbedding.subtypeVal hP₂
  have hP₁b : P₁ ⊆ bd ↥(Λ₁ ∪ Λ₂)ᶜ := hu ▸ subset_union_left
  have hP₂b : P₂ ⊆ bd ↥(Λ₁ ∪ Λ₂)ᶜ := hu ▸ subset_union_right
  have houter : ∀ k : ↥(Λ₁ ∪ Λ₂)ᶜ, k.1 ∈ closure (Subtype.val '' (bd ↥(Λ₁ ∪ Λ₂)ᶜ)ᶜ) := fun k =>
    image_closure_subset_closure_image continuous_subtype_val ⟨k, mem_closure_compl_bd
      (hX.2.2 k), rfl⟩
  have hsm : Subtype.val '' (bd ↥(Λ₁ ∪ Λ₂)ᶜ)ᶜ ⊆ (closure (Λ₁ ∪ Λ₂))ᶜ := by
    rintro _ ⟨w, hw, rfl⟩
    exact fun h5 => hw ((hbX w).mpr h5)
  have hout₁ : ∀ x ∈ closure Λ₁ \ Λ₁, x ∈ closure (closure Λ₁)ᶜ := by
    rw [← hv₁]
    rintro _ ⟨k, -, rfl⟩
    exact closure_mono (hsm.trans (compl_subset_compl.mpr (closure_mono subset_union_left)))
      (houter k)
  have hout₂ : ∀ x ∈ closure Λ₂ \ Λ₂, x ∈ closure (closure Λ₂)ᶜ := by
    rw [← hv₂]
    rintro _ ⟨k, -, rfl⟩
    exact closure_mono (hsm.trans (compl_subset_compl.mpr (closure_mono subset_union_right)))
      (houter k)
  obtain ⟨hG₁, hG₁b⟩ := closure_disc hS hΛ₁ (by rw [hb]; exact disjoint_empty _) hF₁ hout₁
  obtain ⟨hG₂, hG₂b⟩ := closure_disc hS hΛ₂ (by rw [hb]; exact disjoint_empty _) hF₂ hout₂
  have hmeet₁ : closure Λ₁ ∩ (Λ₁ ∪ Λ₂)ᶜ = closure Λ₁ \ Λ₁ := by
    ext z
    exact ⟨fun h => ⟨h.1, fun h' => h.2 (.inl h')⟩, fun h => ⟨h.1,
      fun h' => h'.elim h.2 fun h'' => Set.disjoint_left.mp hd h.1 (subset_closure h'')⟩⟩
  have hmeet₂ : closure Λ₂ ∩ (Λ₁ ∪ Λ₂)ᶜ = closure Λ₂ \ Λ₂ := by
    ext z
    exact ⟨fun h => ⟨h.1, fun h' => h.2 (.inr h')⟩, fun h => ⟨h.1,
      fun h' => h'.elim (fun h'' => Set.disjoint_left.mp hd (subset_closure h'') h.1) h.2⟩⟩
  obtain ⟨φ₁⟩ := id hF₁
  obtain ⟨φ₂⟩ := id hF₂
  have hcov₁ : Λ₁ᶜ ∪ closure Λ₁ = univ := by
    rw [eq_univ_iff_forall]
    intro z
    by_cases hz : z ∈ Λ₁
    · exact .inr (subset_closure hz)
    · exact .inl hz
  have hconn : ConnectedSpace ↥(Λ₁ ∪ Λ₂)ᶜ := by
    have hmem : (φ₁ 1).1 ∈ closure Λ₁ ∩ (Λ₁ ∪ Λ₂)ᶜ := by
      rw [hmeet₁]
      exact (φ₁ 1).2
    refine connected_compl hXc ⟨(φ₁ 1).1, hmem.2⟩ (𝓖 := {closure Λ₁,
      closure Λ₂}) (by simp) ?_ ?_ ?_ ?_ ?_
    · rintro G (rfl | rfl) <;> exact isClosed_closure
    · rintro G (rfl | rfl)
      · rw [hmeet₁]
        exact hF₁.isPreconnected
      · rw [hmeet₂]
        exact hF₂.isPreconnected
    · rintro G (rfl | rfl)
      · rw [hmeet₁]
        exact ⟨_, (φ₁ 1).2⟩
      · rw [hmeet₂]
        exact ⟨_, (φ₂ 1).2⟩
    · rintro G (rfl | rfl) G' (rfl | rfl) hne
      · exact absurd rfl hne
      · exact hd
      · exact hd.symm
      · exact absurd rfl hne
    · rw [eq_univ_iff_forall]
      intro z
      by_cases h1 : z ∈ Λ₁
      · exact .inr ⟨_, .inl rfl, subset_closure h1⟩
      · by_cases h2 : z ∈ Λ₂
        · exact .inr ⟨_, .inr rfl, subset_closure h2⟩
        · exact .inl fun h => h.elim h1 h2
  obtain ⟨a₁, b₁, c₁, ⟨e₃⟩⟩ := classification.{u} _ hX hconn
  have hQ : IsSurface ↥Λ₁ᶜ := compl_surface hS hb hΛ₁.1 hF₁ hout₁
  have hcQ : CompactSpace ↥Λ₁ᶜ := hQ.1
  have hQc : IsClosed Λ₁ᶜ := hΛ₁.1.isClosed_compl
  have hXQ : (Λ₁ ∪ Λ₂)ᶜ ⊆ Λ₁ᶜ := compl_subset_compl.mpr subset_union_left
  let ι : ↥(Λ₁ ∪ Λ₂)ᶜ → ↥Λ₁ᶜ := inclusion hXQ
  have hι : IsClosedEmbedding ι := (continuous_inclusion hXQ).isClosedEmbedding
    (inclusion_injective hXQ)
  have hvalQ := hQc.isClosedEmbedding_subtypeVal
  have hG₂Q : closure Λ₂ ⊆ range (Subtype.val : ↥Λ₁ᶜ → S) := fun z hz => by
    rw [Subtype.range_coe]
    exact fun h => Set.disjoint_left.mp hd (subset_closure h) hz
  have hne : Nonempty ↥Λ₁ᶜ := ⟨⟨(φ₁ 1).1, (φ₁ 1).2.2⟩⟩
  obtain ⟨hΔ, hΔb⟩ := isClosedDisc_preimage hvalQ hG₂ hG₂Q
  have hkey : ∀ z : ↥Λ₁ᶜ, z.1 ∈ closure Λ₂ \ Λ₂ ↔ z ∈ ι '' P₂ := fun z => by
    rw [← hv₂]
    constructor
    · rintro ⟨p, hp, he⟩
      exact ⟨p, hp, Subtype.ext he⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
  have hran : range ι ∪ Subtype.val ⁻¹' closure Λ₂ = univ := by
    rw [eq_univ_iff_forall]
    intro z
    by_cases h1 : z.1 ∈ Λ₂
    · exact .inr (subset_closure h1)
    · exact .inl ⟨⟨z.1, fun h => h.elim z.2 h1⟩, rfl⟩
  have hmeet : range ι ∩ Subtype.val ⁻¹' closure Λ₂ = ι '' P₂ := by
    ext z
    rw [← hkey]
    constructor
    · rintro ⟨⟨x, rfl⟩, h⟩
      exact ⟨h, fun h' => x.2 (.inr h')⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨⟨z.1, fun h => h.elim z.2 h2⟩, rfl⟩, h1⟩
  have hbd₂ : discBd (Subtype.val ⁻¹' closure Λ₂ : Set ↥Λ₁ᶜ) = ι '' P₂ := by
    rw [hΔb, hG₂b]
    ext z
    exact hkey z
  have hcP₂ : P₂ ∈ cuffs ↥(Λ₁ ∪ Λ₂)ᶜ := by
    exact cuff_of_split hP₂.isCompact.isClosed hP₁.isCompact.isClosed hdP.symm
      ((union_comm _ _).trans hu) hP₂.isConnected'
  obtain ⟨h0, ⟨e₄⟩⟩ := paste_model hX hcP₂ hQ hι hΔ hran hmeet hbd₂ e₃
  have hbQ : ∀ x : ↥Λ₁ᶜ, x ∈ bd ↥Λ₁ᶜ ↔ x.1 ∈ closure Λ₁ := fun x => by
    have := bd_subset_iff hint x
    rwa [compl_compl] at this
  have himg : Subtype.val '' bd ↥Λ₁ᶜ = closure Λ₁ \ Λ₁ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hbQ y).mp hy, y.2⟩
    · rintro ⟨h3, h4⟩
      exact ⟨⟨x, h4⟩, (hbQ _).mpr h3, rfl⟩
  have hObQ : IsOArc (bd ↥Λ₁ᶜ) := isOArc_of_image hvalQ.isEmbedding (himg ▸ hF₁)
  have hran' : range (Subtype.val : ↥Λ₁ᶜ → S) ∪ closure Λ₁ = univ := by
    rw [Subtype.range_coe]
    exact hcov₁
  have hmeet' : range (Subtype.val : ↥Λ₁ᶜ → S) ∩ closure Λ₁ = Subtype.val '' bd ↥Λ₁ᶜ := by
    rw [Subtype.range_coe, himg, inter_comm]
    rfl
  obtain ⟨h0', ⟨e₅⟩⟩ := paste_model hQ (isCuff_of_oArc hObQ) hS hvalQ hG₁ hran' hmeet'
    (hG₁b.trans himg.symm) e₄
  obtain ⟨c0, ce, -⟩ := (modelCriterion.2 a₁ b₁ (c₁ - 1 - 1) a b 0).mp ⟨e₅.symm.trans e⟩
  obtain rfl : c₁ = 2 := by omega
  exact ⟨a₁, b₁, ⟨e₃⟩, ce⟩

/-- The lower half of the unit interval, stretched and turned over. -/
noncomputable def loI (t : 𝕀) : 𝕀 := projIcc 0 1 zero_le_one (1 - 2 * (t : ℝ))

/-- The upper half of the unit interval, stretched. -/
noncomputable def hiI (t : 𝕀) : 𝕀 := projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)

theorem loI_coe {t : 𝕀} (h : (t : ℝ) ≤ 1 / 2) : (loI t : ℝ) = 1 - 2 * t := by
  have hm : 1 - 2 * (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [t.2.1]⟩
  rw [loI, projIcc_of_mem _ hm]

theorem hiI_coe {t : 𝕀} (h : 1 / 2 ≤ (t : ℝ)) : (hiI t : ℝ) = 2 * t - 1 := by
  have hm : 2 * (t : ℝ) - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [t.2.2]⟩
  rw [hiI, projIcc_of_mem _ hm]

private theorem cut_handle_boundary_preimage
    {Y : Type u}
    {T : Type u}
    [TopologicalSpace Y]
    {ι : Y → T}
    (hιi : Function.Injective ι)
    {c : Circle × 𝕀 → T}
    (hci : Function.Injective c)
    {J₁ : Set Y}
    {J₂ : Set Y}
    (φ₁ : Circle ≃ₜ ↑J₁)
    (h1 : ι '' J₂ = range fun w => c (w, 1))
    (b : Circle × 𝕀 → Y)
    (hb0 : ∀ (w : Circle), b (w, 0) = ↑(φ₁ w))
    (τ : Circle × 𝕀 → T)
    (hτlo : ∀ {p : Circle × 𝕀}, (p.2 : ℝ) ≤ 1 / 2 → τ p = c (p.1, loI p.2))
    (hτhi : ∀ {p : Circle × 𝕀}, 1 / 2 ≤ (p.2 : ℝ) → τ p = ι (b (p.1, hiI p.2)))
    (ψ : Y → T)
    (hψb : ∀ (p : Circle × 𝕀), ψ (b p) = τ p)
    (hψn : ∀ {z : Y}, z ∉ range b → ψ z = ι z)
    (hJ₂b : ∀ z ∈ J₂, z ∉ range b)
    (hψ0 : ∀ (w : Circle), ψ ↑(φ₁ w) = c (w, 1))
    (hc1 : ∀ (w : Circle), c (w, 1) ∈ ι '' J₂) :
    J₁ ∪ J₂ = ψ ⁻¹' ι '' J₂ := by
  apply subset_antisymm
  · rintro y (hy | hy)
    · obtain ⟨w, he⟩ := φ₁.surjective ⟨y, hy⟩
      have h2 : y = (φ₁ w).1 := by rw [he]
      rw [mem_preimage, h2, hψ0]
      exact hc1 w
    · rw [mem_preimage, hψn (hJ₂b y hy)]
      exact ⟨y, hy, rfl⟩
  · intro y hy
    by_cases h : y ∈ range b
    · obtain ⟨⟨w, t⟩, rfl⟩ := h
      rw [mem_preimage, hψb] at hy
      by_cases ht : (t : ℝ) ≤ 1 / 2
      · rw [hτlo ht] at hy
        rw [h1] at hy
        obtain ⟨w', he⟩ := hy
        have h3 := Prod.ext_iff.mp (hci he)
        have h4 : (loI t : ℝ) = 1 := by
          have h7 : (1 : 𝕀) = loI t := h3.2
          rw [← h7]
          rfl
        have h5 := loI_coe ht
        have h6 : t = 0 := Subtype.ext (by rw [Icc.coe_zero]; linarith)
        subst h6
        rw [hb0]
        exact .inl (φ₁ w).2
      · rw [hτhi (le_of_lt (not_le.mp ht))] at hy
        obtain ⟨y', hy', he⟩ := hy
        exact absurd ⟨_, rfl⟩ (hJ₂b _ (hιi he ▸ hy'))
    · rw [mem_preimage, hψn h] at hy
      obtain ⟨y', hy', he⟩ := hy
      exact .inr (hιi he ▸ hy')

/-- A map that stretches a collar of the cuff `J₁` of `Y` over the collar and a cylinder `c`, which
is glued to `ι Y` by its end at `0` along `ι J₁` and by its end at `1` along `ι J₂`. So this map
only glues `J₁` to `J₂`. -/
theorem handle_cut {Y T : Type u} [TopologicalSpace Y] [TopologicalSpace T]
  (hY : IsSurface Y) {ι : Y → T} (hι : Continuous ι) (hιi : Function.Injective ι)
    {c : Circle × 𝕀 → T} (hc : Continuous c) (hci : Function.Injective c) {J₁ J₂ : Set Y}
      (φ₁ : Circle ≃ₜ J₁) (hJ₁ : IsCuff J₁) (hJ₂ : IsClosed J₂) (hd : Disjoint J₁ J₂)
    (hbd : J₁ ∪ J₂ ⊆ bd Y) (h0 : ∀ w, ι (φ₁ w).1 = c (w, 0)) (h1 : ι '' J₂ = range fun w => c
      (w, 1))
    (hm : ∀ y p, ι y = c p → ((p.2 : ℝ) = 0 ∧ y ∈ J₁) ∨ ((p.2 : ℝ) = 1 ∧ y ∈ J₂))
      (hcov : ∀ x, x ∈ range ι ∨ x ∈ range c) :
    ∃ ψ : Y → T, IsCutting ψ (ι '' J₂) ∧ BijOn ψ J₁ (ι '' J₂) ∧ BijOn ψ J₂ (ι '' J₂) ∧ J₁ ∪ J₂
      = ψ ⁻¹' (ι '' J₂) := by
  classical
  have hcY : CompactSpace Y := hY.1
  have ht2Y : T2Space Y := hY.2.1
  obtain ⟨b, hb, hbi, hbr, hb0, hbo⟩ := exists_collar hY hJ₁ φ₁ hJ₂.isOpen_compl (fun z hz
    => Set.disjoint_left.mp hd hz)
  obtain ⟨f', hf', hl⟩ := exists_inv_of_compactOn (isCompact_univ (X := Circle × 𝕀))
    hb.continuousOn hbi.injOn
  have hinv : ∀ p, f' (b p) = p := fun p => hl (mem_univ p)
  let τ : Circle × 𝕀 → T := fun p => if (p.2 : ℝ) ≤ 1 / 2 then c (p.1, loI p.2) else ι (b
    (p.1, hiI p.2))
  have hzero : ∀ p : Circle × 𝕀, (p.2 : ℝ) = 0 → p = (p.1, 0) := fun p hp => Prod.ext rfl
    (Subtype.ext hp)
  have hhalf : ∀ w, ι (b (w, 0)) = c (w, 0) := fun w => by rw [hb0, h0]
  have hτ : Continuous τ := by
    refine Continuous.if_le ?_ ?_ (by fun_prop) continuous_const ?_
    · exact hc.comp (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
    · exact hι.comp (hb.comp (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop))))
    · intro p hp
      have e1 : loI p.2 = 0 := Subtype.ext (by rw [loI_coe hp.le, hp]; norm_num)
      have e2 : hiI p.2 = 0 := Subtype.ext (by rw [hiI_coe hp.ge, hp]; norm_num)
      rw [e1, e2, hhalf]
  have hτlo : ∀ {p : Circle × 𝕀}, (p.2 : ℝ) ≤ 1 / 2 → τ p = c (p.1, loI p.2) := fun h
    => ite_eq_left h
  have hτhi : ∀ {p : Circle × 𝕀}, 1 / 2 ≤ (p.2 : ℝ) → τ p = ι (b (p.1, hiI p.2)) := fun {p} h => by
    by_cases h' : (p.2 : ℝ) ≤ 1 / 2
    · have hp : (p.2 : ℝ) = 1 / 2 := le_antisymm h' h
      have e1 : loI p.2 = 0 := Subtype.ext (by rw [loI_coe h', hp]; norm_num)
      have e2 : hiI p.2 = 0 := Subtype.ext (by rw [hiI_coe h, hp]; norm_num)
      rw [hτlo h', e1, e2, hhalf]
    · exact ite_eq_right h'
  let ψ : Y → T := fun z => if z ∈ range b then τ (f' z) else ι z
  have hψb : ∀ p, ψ (b p) = τ p := fun p => by
    simp only [ψ, mem_range_self, ite_true, hinv]
  have hψn : ∀ {z}, z ∉ range b → ψ z = ι z := fun h => ite_eq_right h
  have hJ₂b : ∀ z ∈ J₂, z ∉ range b := fun z hz h => hbr h hz
  have hone : hiI 1 = 1 := Subtype.ext (by rw [hiI_coe (by simp; norm_num)]; norm_num)
  have hψc : Continuous ψ := by
    have cR : IsClosed (range b) := (isCompact_range hb).isClosed
    have cB : IsClosed (range b \ b '' {x | x.2 = 1})ᶜ := hbo.isClosed_compl
    have on1 : ContinuousOn ψ (range b) := by
      have h2 : ContinuousOn f' (range b) := by simpa using hf'
      refine (hτ.comp_continuousOn h2).congr fun z hz => ?_
      exact ite_eq_left hz
    have on2 : ContinuousOn ψ (range b \ b '' {x | x.2 = 1})ᶜ := by
      refine hι.continuousOn.congr fun z hz => ?_
      by_cases h : z ∈ range b
      · have h3 : z ∈ b '' {x | x.2 = 1} := by
          by_contra h4
          exact hz ⟨h, h4⟩
        obtain ⟨⟨w, t⟩, ht, rfl⟩ := h3
        obtain rfl : t = 1 := ht
        rw [hψb, hτhi (by simp; norm_num), hone]
      · exact hψn h
    have h3 := on1.union_of_isClosed on2 cR cB
    have h4 : range b ∪ (range b \ b '' {x | x.2 = 1})ᶜ = univ := by
      rw [eq_univ_iff_forall]
      intro z
      by_cases h : z ∈ range b
      · exact .inl h
      · exact .inr fun h' => h h'.1
    rw [h4] at h3
    exact continuousOn_univ.mp h3
  have hψ0 : ∀ w, ψ (φ₁ w).1 = c (w, 1) := fun w => by
    rw [← hb0, hψb, hτlo (by simp)]
    have : loI 0 = 1 := Subtype.ext (by rw [loI_coe (by simp)]; norm_num)
    simp only [this]
  have hc1 : ∀ w, c (w, 1) ∈ ι '' J₂ := fun w => by
    rw [h1]
    exact ⟨w, rfl⟩
  have hc1i : ∀ {w w'}, c (w, 1) = c (w', 1) → w = w' := fun h => (Prod.ext_iff.mp (hci h)).1
  have hpre : J₁ ∪ J₂ = ψ ⁻¹' (ι '' J₂) := by
    exact cut_handle_boundary_preimage (Y := Y) (T := T) (ι := ι) hιi (c := c) hci (J₁ := J₁) (J₂
      := J₂) φ₁ h1 b hb0 τ hτlo hτhi ψ hψb hψn hJ₂b hψ0 hc1
  have hCval : ∀ w (t : 𝕀), 0 < (t : ℝ) → (t : ℝ) < 1 / 2 → ∀ z, ψ (b (w, t)) = ι z → False := by
    intro w t h2 h3 z he
    rw [hψb, hτlo h3.le] at he
    have h4 := loI_coe h3.le
    rcases hm z _ he.symm with ⟨h5, -⟩ | ⟨h5, -⟩
    · simp only at h5
      linarith
    · simp only at h5
      linarith
  have hkind : ∀ z, z ∉ ψ ⁻¹' (ι '' J₂) → z ∉ range b ∨ (∃ w t, z = b (w, t) ∧ 1 / 2 ≤ (t : ℝ))
    ∨ ∃ w t, z = b (w, t) ∧ 0 < (t : ℝ) ∧ (t : ℝ) < 1 / 2 := by
    intro z hz
    by_cases h : z ∈ range b
    · obtain ⟨⟨w, t⟩, rfl⟩ := h
      by_cases h2 : 1 / 2 ≤ (t : ℝ)
      · exact .inr (.inl ⟨w, t, rfl, h2⟩)
      · refine .inr (.inr ⟨w, t, rfl, lt_of_le_of_ne t.2.1 fun h3 => hz ?_, not_le.mp h2⟩)
        have h4 : t = 0 := Subtype.ext h3.symm
        subst h4
        rw [← hpre, hb0]
        exact .inl (φ₁ w).2
    · exact .inl h
  have hinj : InjOn ψ (ψ ⁻¹' (ι '' J₂))ᶜ := by
    intro y hy y' hy' he
    rcases hkind y hy with h2 | ⟨w, t, rfl, h2⟩ | ⟨w, t, rfl, h2, h3⟩
      <;> rcases hkind y' hy' with h4 | ⟨w', t', rfl, h4⟩ | ⟨w', t', rfl, h4, h5⟩
    · rw [hψn h2, hψn h4] at he
      exact hιi he
    · rw [hψn h2, hψb, hτhi h4] at he
      exact absurd ⟨_, (hιi he).symm⟩ h2
    · rw [hψn h2] at he
      exact (hCval w' t' h4 h5 y he.symm).elim
    · rw [hψn h4, hψb, hτhi h2] at he
      exact absurd ⟨_, hιi he⟩ h4
    · rw [hψb, hψb, hτhi h2, hτhi h4] at he
      have h6 := Prod.ext_iff.mp (hbi (hιi he))
      have h7 : (hiI t : ℝ) = hiI t' := congrArg Subtype.val h6.2
      rw [hiI_coe h2, hiI_coe h4] at h7
      have h8 : t = t' := Subtype.ext (by linarith)
      rw [show w = w' from h6.1, h8]
    · rw [hψb (w, t), hτhi h2] at he
      exact (hCval w' t' h4 h5 _ he.symm).elim
    · rw [hψn h4] at he
      exact (hCval w t h2 h3 y' he).elim
    · rw [hψb (w', t'), hτhi h4] at he
      exact (hCval w t h2 h3 _ he).elim
    · rw [hψb, hψb, hτlo h3.le, hτlo h5.le] at he
      have h6 := Prod.ext_iff.mp (hci he)
      have h7 : (loI t : ℝ) = loI t' := congrArg Subtype.val h6.2
      rw [loI_coe h3.le, loI_coe h5.le] at h7
      have h8 : t = t' := Subtype.ext (by linarith)
      rw [show w = w' from h6.1, h8]
  have hsurj : Function.Surjective ψ := by
    intro x
    rcases hcov x with ⟨y, rfl⟩ | ⟨⟨w, s⟩, rfl⟩
    · by_cases h : y ∈ range b
      · obtain ⟨⟨w, s⟩, rfl⟩ := h
        have hmem : (1 + (s : ℝ)) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [s.2.1], by linarith [s.2.2]⟩
        have h2 : 1 / 2 ≤ (1 + (s : ℝ)) / 2 := by linarith [s.2.1]
        refine ⟨b (w, ⟨_, hmem⟩), ?_⟩
        rw [hψb, hτhi h2]
        have : hiI ⟨_, hmem⟩ = s := Subtype.ext (by rw [hiI_coe h2]; ring)
        simp only [this]
      · exact ⟨y, hψn h⟩
    · have hmem : (1 - (s : ℝ)) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [s.2.2], by linarith [s.2.1]⟩
      have h2 : (1 - (s : ℝ)) / 2 ≤ 1 / 2 := by linarith [s.2.1]
      refine ⟨b (w, ⟨_, hmem⟩), ?_⟩
      rw [hψb, hτlo h2]
      have : loI ⟨_, hmem⟩ = s := Subtype.ext (by rw [loI_coe h2]; ring)
      simp only [this]
  have hcount : ∀ x ∈ ι '' J₂, (ψ ⁻¹' {x}).ncard = 2 := by
    rintro _ ⟨j, hj, rfl⟩
    have h2 : ι j ∈ range fun w => c (w, 1) := h1 ▸ ⟨j, hj, rfl⟩
    obtain ⟨w, hw⟩ := h2
    have hw' : c (w, 1) = ι j := hw
    have e : ψ ⁻¹' {ι j} = {j, (φ₁ w).1} := by
      ext y
      simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
      constructor
      · intro he
        have h3 : y ∈ J₁ ∪ J₂ := by
          rw [hpre]
          exact ⟨j, hj, he.symm⟩
        rcases h3 with h3 | h3
        · right
          obtain ⟨w', hw''⟩ := φ₁.surjective ⟨y, h3⟩
          have h4 : y = (φ₁ w').1 := by rw [hw'']
          rw [h4, hψ0, ← hw'] at he
          rw [h4, hc1i he]
        · left
          rw [hψn (hJ₂b y h3)] at he
          exact hιi he
      · rintro (rfl | rfl)
        · exact hψn (hJ₂b y hj)
        · rw [hψ0, hw']
    rw [e, ncard_pair]
    exact fun h => Set.disjoint_left.mp hd (φ₁ w).2 (h ▸ hj)
  refine ⟨ψ, ⟨hψc, hsurj, hinj, hcount, fun y hy => hbd (hpre ▸ hy)⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    hpre⟩
  · intro y hy
    have : y ∈ ψ ⁻¹' (ι '' J₂) := hpre ▸ .inl hy
    exact this
  · intro y hy y' hy' he
    obtain ⟨w, hw⟩ := φ₁.surjective ⟨y, hy⟩
    obtain ⟨w', hw'⟩ := φ₁.surjective ⟨y', hy'⟩
    have h2 : y = (φ₁ w).1 := by rw [hw]
    have h3 : y' = (φ₁ w').1 := by rw [hw']
    rw [h2, h3, hψ0, hψ0] at he
    rw [h2, h3, hc1i he]
  · rintro x hx
    rw [h1] at hx
    obtain ⟨w, rfl⟩ := hx
    exact ⟨(φ₁ w).1, (φ₁ w).2, hψ0 w⟩
  · intro y hy
    have : y ∈ ψ ⁻¹' (ι '' J₂) := hpre ▸ .inr hy
    exact this
  · intro y hy y' hy' he
    rw [hψn (hJ₂b y hy), hψn (hJ₂b y' hy')] at he
    exact hιi he
  · rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, hj, hψn (hJ₂b j hj)⟩

end GraphMinor.Surface
