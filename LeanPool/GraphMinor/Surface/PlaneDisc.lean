/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Schoenflies

/-!
# Closed discs in the plane

This file collects what the disc statements need from the Schoenflies theorem, in `ℂ`.

* `isClosedDisc_closedInner`: the closed domain of an `O`-arc `G` is a closed disc with boundary
  `G`.
* `eq_closedInner_of_discBd`: it is the only closed disc with this boundary. The disc minus its
  boundary is open by invariance of domain, so it is a full side of `G`, and only the inner side is
  bounded.
* `componentsIn_image`, `componentsIn_union_eq_pair`: tools for the components of a set.
* `IsCut.components`: the components of a closed domain minus a cross-cut, and of an `O`-arc minus
  two points.
* `exists_other_arc`: an arc in an `O`-arc has a complementary arc with the same ends.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

local notation "𝕀" => unitInterval

universe u v

/-- A map with a continuous inverse on its image is a homeomorphism onto the image. -/
theorem exists_homeomorph_image {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    {Δ : Set S} {f : S → T} {f' : T → S} (hf : ContinuousOn f Δ) (hf' : ContinuousOn f' (f '' Δ))
    (hl : LeftInvOn f' f Δ) : ∃ e : Δ ≃ₜ f '' Δ, ∀ x, (e x).1 = f x.1 := by
  have hmem : ∀ y : f '' Δ, f' y.1 ∈ Δ := by
    rintro ⟨_, x, hx, rfl⟩
    change f' (f x) ∈ Δ
    rw [hl hx]
    exact hx
  refine ⟨⟨⟨fun x => ⟨f x.1, mem_image_of_mem f x.2⟩, fun y => ⟨f' y.1, hmem y⟩, fun x => ?_,
    ?_⟩, ?_, ?_⟩, fun _ => rfl⟩
  · exact Subtype.ext (hl x.2)
  · rintro ⟨_, x, hx, rfl⟩
    refine Subtype.ext ?_
    change f (f' (f x)) = f x
    rw [hl hx]
  · exact Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.mp hf) _
  · exact Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.mp hf') _

/-- The image of a closed disc under a map with a continuous inverse. -/
theorem IsClosedDisc.image {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    {Δ : Set S} (hΔ : IsClosedDisc Δ) {f : S → T} {f' : T → S} (hf : ContinuousOn f Δ)
    (hf' : ContinuousOn f' (f '' Δ)) (hl : LeftInvOn f' f Δ) :
    IsClosedDisc (f '' Δ) ∧ discBd (f '' Δ) = f '' discBd Δ := by
  obtain ⟨e, he⟩ := exists_homeomorph_image hf hf' hl
  obtain ⟨φ⟩ := hΔ
  refine ⟨⟨φ.trans e⟩, ?_⟩
  rw [disc_boundary.{v} (f '' Δ) (φ.trans e), disc_boundary.{u} Δ φ, image_image]
  exact image_congr fun x _ => he (φ x)

/-- The image of an `O`-arc under a map with a continuous inverse. -/
theorem IsOArc.image {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    {F : Set S} (hF : IsOArc F) {f : S → T} {f' : T → S} (hf : ContinuousOn f F)
    (hf' : ContinuousOn f' (f '' F)) (hl : LeftInvOn f' f F) : IsOArc (f '' F) := by
  obtain ⟨e, -⟩ := exists_homeomorph_image hf hf' hl
  obtain ⟨φ⟩ := hF
  exact ⟨φ.trans e⟩

/-- Under a continuous map with a continuous inverse, components go to components. -/
theorem image_connectedComponentIn {S : Type u} {T : Type v} [TopologicalSpace S]
    [TopologicalSpace T] {X : Set S} {f : S → T} {f' : T → S} (hf : ContinuousOn f X)
    (hf' : ContinuousOn f' (f '' X)) (hl : LeftInvOn f' f X) {x : S} (hx : x ∈ X) :
    f '' connectedComponentIn X x = connectedComponentIn (f '' X) (f x) := by
  have hsub : connectedComponentIn X x ⊆ X := connectedComponentIn_subset X x
  have hsub' : connectedComponentIn (f '' X) (f x) ⊆ f '' X := connectedComponentIn_subset _ _
  have hxm : x ∈ connectedComponentIn X x := mem_connectedComponentIn hx
  have hfm : f x ∈ f '' X := mem_image_of_mem f hx
  have hym : f x ∈ connectedComponentIn (f '' X) (f x) := mem_connectedComponentIn hfm
  have h1 : f '' connectedComponentIn X x ⊆ connectedComponentIn (f '' X) (f x) :=
    IsPreconnected.subset_connectedComponentIn
      (isPreconnected_connectedComponentIn.image f (hf.mono hsub)) (mem_image_of_mem f hxm)
      (image_mono hsub)
  have h2 : f' '' connectedComponentIn (f '' X) (f x) ⊆ connectedComponentIn X x := by
    refine IsPreconnected.subset_connectedComponentIn
      (isPreconnected_connectedComponentIn.image f' (hf'.mono hsub')) ⟨f x, hym, hl hx⟩ ?_
    refine (image_mono hsub').trans ?_
    rw [hl.image_image]
  refine Subset.antisymm h1 fun y hy => ?_
  obtain ⟨z, hz, rfl⟩ := hsub' hy
  exact ⟨z, by simpa [hl hz] using h2 (mem_image_of_mem f' hy), rfl⟩

/-- Components of an image. -/
theorem componentsIn_image {S : Type u} {T : Type v} [TopologicalSpace S]
    [TopologicalSpace T] {X : Set S} {f : S → T} {f' : T → S} (hf : ContinuousOn f X)
    (hf' : ContinuousOn f' (f '' X)) (hl : LeftInvOn f' f X) :
    componentsIn (f '' X) = (fun C => f '' C) '' componentsIn X := by
  ext C
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, image_connectedComponentIn hf hf' hl hx⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, mem_image_of_mem f hx, (image_connectedComponentIn hf hf' hl hx).symm⟩

/-- A preconnected subset of the union of two separated sets lies in one of them. -/
theorem IsPreconnected.subset_or_of_separated {T : Type u} [TopologicalSpace T] {A B C : Set T}
    (hC : IsPreconnected C) (hsub : C ⊆ A ∪ B) (h1 : Disjoint (closure A) B)
    (h2 : Disjoint A (closure B)) : C ⊆ A ∨ C ⊆ B := by
  by_contra hn
  push Not at hn
  obtain ⟨hA, hB⟩ := hn
  obtain ⟨y, hyC, hyA⟩ := not_subset.mp hA
  obtain ⟨x, hxC, hxB⟩ := not_subset.mp hB
  have hxA : x ∈ A := (hsub hxC).resolve_right hxB
  have hyB : y ∈ B := (hsub hyC).resolve_left hyA
  obtain ⟨z, hzC, hz1, hz2⟩ := hC (closure B)ᶜ (closure A)ᶜ isClosed_closure.isOpen_compl
    isClosed_closure.isOpen_compl (fun z hz => by
      rcases hsub hz with h | h
      · exact Or.inl (Set.disjoint_left.mp h2 h)
      · exact Or.inr (Set.disjoint_right.mp h1 h))
    ⟨x, hxC, Set.disjoint_left.mp h2 hxA⟩ ⟨y, hyC, Set.disjoint_right.mp h1 hyB⟩
  rcases hsub hzC with h | h
  · exact hz2 (subset_closure h)
  · exact hz1 (subset_closure h)

/-- The components of the union of two separated connected sets. -/
theorem componentsIn_union_eq_pair {T : Type u} [TopologicalSpace T] {A B : Set T}
  (hA : IsPreconnected A)
    (hB : IsPreconnected B) (hA' : A.Nonempty) (hB' : B.Nonempty) (h1 : Disjoint (closure A) B)
    (h2 : Disjoint A (closure B)) : componentsIn (A ∪ B) = {A, B} := by
  have hdisj : Disjoint A B := h1.mono_left subset_closure
  have key : ∀ {A' B' : Set T}, IsPreconnected A' → Disjoint (closure A') B' →
      Disjoint A' (closure B') → A' ∪ B' = A ∪ B → ∀ x ∈ A',
      connectedComponentIn (A ∪ B) x = A' := by
    intro A' B' hA1 h3 h4 hu x hx
    have hxm : x ∈ A ∪ B := hu ▸ Or.inl hx
    refine Subset.antisymm ?_ (hA1.subset_connectedComponentIn hx (hu ▸ subset_union_left))
    have hC := isPreconnected_connectedComponentIn (F := A ∪ B) (x := x)
    have hs : connectedComponentIn (A ∪ B) x ⊆ A' ∪ B' := hu ▸ connectedComponentIn_subset _ _
    rcases IsPreconnected.subset_or_of_separated hC hs h3 h4 with h | h
    · exact h
    · exact absurd (h (mem_connectedComponentIn hxm))
        (Set.disjoint_left.mp (h3.mono_left subset_closure) hx)
  have hA2 := key hA h1 h2 rfl
  have hB2 := key hB (by rw [disjoint_comm]; exact h2) (by rw [disjoint_comm]; exact h1)
    (union_comm _ _)
  ext C
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl (hA2 x hx)
    · exact Or.inr (hB2 x hx)
  · rintro (rfl | rfl)
    · obtain ⟨x, hx⟩ := hA'
      exact ⟨x, Or.inl hx, hA2 x hx⟩
    · obtain ⟨x, hx⟩ := hB'
      exact ⟨x, Or.inr hx, hB2 x hx⟩

/-- `exists_homeomorph_closedInner` in terms of functions on the plane. -/
theorem exists_bdMatch_closedInner {F F' : Set ℂ} (hF : Nonempty (Circle ≃ₜ F))
    (hF' : Nonempty (Circle ≃ₜ F')) {h₀ k₀ : ℂ → ℂ} (m : BdMatch F F' h₀ k₀) :
    ∃ ψ χ : ℂ → ℂ, BdMatch (closedInner F) (closedInner F') ψ χ ∧ EqOn ψ h₀ F := by
  obtain ⟨Ψ, hΨ⟩ := exists_homeomorph_closedInner hF hF' m
  obtain ⟨ψ, χ, m', hv⟩ := exists_bdMatch Ψ
  have hsub : F ⊆ closedInner F := subset_union_right
  refine ⟨ψ, χ, m', fun z hz => ?_⟩
  rw [hv ⟨z, hsub hz⟩]
  exact hΨ ⟨z, hsub hz⟩ hz

theorem BdMatch.image_eq {F F' : Set ℂ} {h k : ℂ → ℂ} (m : BdMatch F F' h k) : h '' F = F' := by
  refine Subset.antisymm (image_subset_iff.mpr m.1) fun w hw => ?_
  exact ⟨k w, m.2.1 hw, m.2.2.2.1 hw⟩

theorem BdMatch.leftInvOn {F F' : Set ℂ} {h k : ℂ → ℂ} (m : BdMatch F F' h k) : LeftInvOn k h F :=
  m.2.2.1

/-- The closed disc of `ℂ`. -/
theorem isClosedDisc_closedBall : IsClosedDisc (closedBall (0 : ℂ) 1) ∧
    discBd (closedBall (0 : ℂ) 1) = sphere 0 1 := by
  have h0 : IsClosedDisc ClosedUnitDisc := ⟨Homeomorph.refl _⟩
  have hb : discBd ClosedUnitDisc = UnitCircle := by
    rw [discBd, bd_closedUnitDisc]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hx' : x ∈ ClosedUnitDisc := sphere_subset_closedBall hx
      exact ⟨⟨x, hx'⟩, hx, rfl⟩
  have himg : ∀ {r : ℝ}, complexPlane.symm '' closedBall 0 r = closedBall 0 r := by
    intro r
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
      exact mem_closedBall_zero_iff.mp hx
    · intro hz
      refine ⟨complexPlane z, ?_, complexPlane.symm_apply_apply z⟩
      rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
      exact mem_closedBall_zero_iff.mp hz
  have himg' : complexPlane.symm '' UnitCircle = sphere 0 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
      exact mem_sphere_zero_iff_norm.mp hx
    · intro hz
      refine ⟨complexPlane z, ?_, complexPlane.symm_apply_apply z⟩
      rw [UnitCircle, mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
      exact mem_sphere_zero_iff_norm.mp hz
  have := h0.image (f := complexPlane.symm) (f' := complexPlane)
    complexPlane.symm.continuous.continuousOn complexPlane.continuous.continuousOn
    fun x _ => complexPlane.apply_symm_apply x
  rw [hb, himg', ClosedUnitDisc, himg] at this
  exact this

/-- The closed domain of an `O`-arc of `ℂ` is a closed disc with that boundary. This is the form of
the Schoenflies theorem that the disc statements use. -/
theorem isClosedDisc_closedInner {G : Set ℂ} (hG : Nonempty (Circle ≃ₜ G)) :
    IsClosedDisc (closedInner G) ∧ discBd (closedInner G) = G := by
  obtain ⟨φ₀⟩ := oArc_sphere
  obtain ⟨φ⟩ := id hG
  obtain ⟨h₀, k₀, m, -⟩ := exists_bdMatch (φ₀.symm.trans φ)
  obtain ⟨ψ, χ, m', he⟩ := exists_bdMatch_closedInner ⟨φ₀⟩ hG m
  rw [closedInner_sphere] at m'
  have himg := m'.image_eq
  obtain ⟨h1, h2⟩ := isClosedDisc_closedBall.1.image m'.2.2.2.2.1
    (by rw [himg]; exact m'.2.2.2.2.2) m'.leftInvOn
  rw [himg, isClosedDisc_closedBall.2, he.image_eq, m.image_eq] at h2
  rw [himg] at h1
  exact ⟨h1, h2⟩

/-- The sides of a curve: a nonempty connected open set `W` that misses `G`, and with `W ∪ G`
closed,
is a side of `G`. -/
theorem subset_of_side {T : Type u} [TopologicalSpace T] {C W G : Set T} (hC : IsPreconnected C)
  (hW : IsOpen W)
    (hcl : IsClosed (W ∪ G)) (hCG : Disjoint C G) (hne : (C ∩ W).Nonempty) : C ⊆ W := by
  have hsub : C ⊆ W ∪ (W ∪ G)ᶜ := fun z hz => by
    by_cases h : z ∈ W
    · exact Or.inl h
    · exact Or.inr fun h' => h'.elim h (Set.disjoint_left.mp hCG hz)
  exact hC.subset_left_of_subset_union hW hcl.isOpen_compl
    (Set.disjoint_left.mpr fun z h h' => h' (Or.inl h)) hsub hne

/-- A closed disc of `ℂ` with boundary `G` is the closed domain of `G`. -/
theorem eq_closedInner_of_discBd {Δ G : Set ℂ} (hG : Nonempty (Circle ≃ₜ G)) (hΔ : IsClosedDisc Δ)
    (hb : discBd Δ = G) : Δ = closedInner G := by
  obtain ⟨φ⟩ := hG
  have J := isJordanParts φ
  obtain ⟨h, g, hh, hg, hhm, hgm, hgh, hhg, hbdh⟩ := hΔ.exists_chart
  have hginj : InjOn g (closedBall 0 1) := (show LeftInvOn h g (closedBall 0 1) from hhg).injOn
  have hgs : g '' sphere 0 1 = G := by
    rw [← hbdh, hgh.image_image' ?_, hb]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  let W := g '' ball 0 1
  have hsplit : ball (0 : ℂ) 1 ∪ sphere 0 1 = closedBall 0 1 := ball_union_sphere
  have hW : IsOpen W := isOpen_image_of_injOn isOpen_ball
    (hg.mono ball_subset_closedBall) (hginj.mono ball_subset_closedBall)
  have hΔeq : g '' closedBall 0 1 = Δ := by
    refine Subset.antisymm (image_subset_iff.mpr hgm) fun x hx => ?_
    exact ⟨h x, hhm hx, hgh hx⟩
  have hun : W ∪ G = Δ := by
    rw [← hgs, ← image_union, hsplit, hΔeq]
  have hcomp : IsCompact Δ := by
    rw [← hΔeq]
    exact (isCompact_closedBall 0 1).image_of_continuousOn hg
  have hcl : IsClosed (W ∪ G) := hun ▸ hcomp.isClosed
  have hdis : Disjoint W G := by
    rw [← hgs]
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have := hginj (sphere_subset_closedBall hy) (ball_subset_closedBall hx) he
    subst this
    exact (mem_ball_zero_iff.mp hx).ne (mem_sphere_zero_iff_norm.mp hy)
  have hWc : IsPreconnected W :=
    (convex_ball (0 : ℂ) 1).isPreconnected.image g (hg.mono ball_subset_closedBall)
  have hWne : W.Nonempty := ⟨g 0, 0, by simp, rfl⟩
  have hsub : W ⊆ inner G ∪ outer G := by
    rw [J.union_eq]
    exact fun z hz hzG => Set.disjoint_left.mp hdis hz hzG
  have hWin : W ⊆ inner G := by
    rcases (isPreconnected_iff_subset_of_disjoint.mp hWc) _ _ J.isOpen_inner J.isOpen_outer hsub
      (by rw [J.disjoint.inter_eq]; simp) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨z, hz⟩ := hWne
      have h2 := subset_of_side J.isConnected_outer.isPreconnected hW hcl
        (Set.disjoint_left.mpr fun z hz hzG => J.outer_subset_compl hz hzG) ⟨z, h1 hz, hz⟩
      exact J.not_isBounded_outer ((hcomp.isBounded.subset (hun ▸ subset_union_left)).subset h2)
  obtain ⟨z, hz⟩ := hWne
  have h2 := subset_of_side J.isConnected_inner.isPreconnected hW hcl
    (Set.disjoint_left.mpr fun z hz hzG => J.inner_subset_compl hz hzG) ⟨z, hWin hz, hz⟩
  rw [← hun, Subset.antisymm hWin h2]
  rfl

theorem outer_sphere : outer (sphere (0 : ℂ) 1) = (closedBall 0 1)ᶜ := by
  obtain ⟨φ⟩ := oArc_sphere
  have J := isJordanParts φ
  ext z
  have h1 : z ∈ inner (sphere (0 : ℂ) 1) ↔ ‖z‖ < 1 := by
    rw [inner_sphere, mem_ball_zero_iff]
  constructor
  · intro hz hz'
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz') with h | h
    · exact Set.disjoint_left.mp J.disjoint (h1.mpr h) hz
    · exact J.outer_subset_compl hz (mem_sphere_zero_iff_norm.mpr h)
  · intro hz
    have : z ∈ (sphere (0 : ℂ) 1)ᶜ := fun h => hz (sphere_subset_closedBall h)
    rw [← J.union_eq] at this
    exact this.resolve_left fun h => hz (ball_subset_closedBall (inner_sphere ▸ h))

/-- A curve in the closed unit disc has its closed domain in the disc. -/
theorem closedInner_subset_closedBall {G : Set ℂ} (hG : Nonempty (Circle ≃ₜ G))
    (hsub : G ⊆ closedBall 0 1) : closedInner G ⊆ closedBall 0 1 := by
  obtain ⟨φ⟩ := hG
  obtain ⟨φ₀⟩ := oArc_sphere
  have J := isJordanParts φ
  have J₀ := isJordanParts φ₀
  have hconn : IsPreconnected (closedBall (0 : ℂ) 1)ᶜ := by
    rw [← outer_sphere]
    exact J₀.isConnected_outer.isPreconnected
  have hdis : (closedBall (0 : ℂ) 1)ᶜ ⊆ inner G ∪ outer G := by
    rw [J.union_eq]
    exact fun z hz hzG => hz (hsub hzG)
  have hout : (closedBall (0 : ℂ) 1)ᶜ ⊆ outer G := by
    rcases (isPreconnected_iff_subset_of_disjoint.mp hconn) _ _ J.isOpen_inner J.isOpen_outer hdis
      (by rw [J.disjoint.inter_eq]; simp) with h | h
    · refine absurd (J.isBounded_inner.subset h) ?_
      rw [← outer_sphere]
      exact J₀.not_isBounded_outer
    · exact h
  rintro z (hz | hz)
  · by_contra hn
    exact Set.disjoint_left.mp J.disjoint hz (hout hn)
  · exact hsub hz

/-- A point on the outer side of a curve in the closed unit disc is joined to the unit circle
inside the disc, off the curve. -/
private theorem exists_sphere_mem_component {G : Set ℂ} (φ : Circle ≃ₜ G) {x : ℂ}
    (hx : x ∈ outer G) (hx1 : ‖x‖ ≤ 1) :
    ∃ y ∈ sphere (0 : ℂ) 1, y ∈ connectedComponentIn (closedBall 0 1 \ G) x := by
  have J := isJordanParts φ
  have hpath : IsPathConnected (outer G) :=
    (J.isOpen_outer.isConnected_iff_isPathConnected).mp J.isConnected_outer
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ outer G, 1 < ‖w‖ := by
    by_contra hn
    push Not at hn
    exact J.not_isBounded_outer ((isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset
      fun z hz => mem_closedBall_zero_iff.mpr (hn z hz))
  obtain ⟨p, hp⟩ := hpath.joinedIn x hx w hw
  have hT : IsCompact {t : 𝕀 | 1 ≤ ‖p t‖} :=
    (isClosed_le continuous_const p.continuous.norm).isCompact
  obtain ⟨t, ht, hmin⟩ := hT.exists_isLeast ⟨1, by simpa using hw1.le⟩
  have hle : ∀ s ≤ t, ‖p s‖ ≤ 1 := by
    have hcl : IsClosed {s : 𝕀 | ‖p s‖ ≤ 1} := isClosed_le p.continuous.norm continuous_const
    have hlt : Iio t ⊆ {s : 𝕀 | ‖p s‖ ≤ 1} := fun s hs => by
      by_contra hn
      have h1 : 1 ≤ ‖p s‖ := le_of_lt (not_le.mp hn)
      exact absurd (hmin h1) (not_le.mpr hs)
    intro s hs
    rcases eq_or_ne t 0 with h0 | h0
    · have hs0 : s = 0 := le_antisymm (h0 ▸ hs) (show (0 : 𝕀) ≤ s from unitInterval.nonneg')
      subst hs0
      simpa using hx1
    · have hne : (Iio t).Nonempty := ⟨0, bot_lt_iff_ne_bot.mpr h0⟩
      have hc := closure_minimal hlt hcl
      rw [closure_Iio' hne] at hc
      exact hc hs
  refine ⟨p t, mem_sphere_zero_iff_norm.mpr (le_antisymm (hle t le_rfl) ht), ?_⟩
  have hsub' : p '' Iic t ⊆ closedBall 0 1 \ G := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨mem_closedBall_zero_iff.mpr (hle s hs), J.outer_subset_compl (hp s)⟩
  exact (isPreconnected_Iic.image p p.continuous.continuousOn).subset_connectedComponentIn
    ⟨0, (show (0 : 𝕀) ≤ t from unitInterval.nonneg'), by simp⟩ hsub' ⟨t, le_rfl, rfl⟩

/-- The components of the closed unit disc minus a curve. -/
theorem components_closedBall_sdiff {G : Set ℂ} (hG : Nonempty (Circle ≃ₜ G))
    (hsub : G ⊆ closedBall 0 1) :
    inner G ∈ componentsIn (closedBall 0 1 \ G) ∧ Disjoint (inner G) (sphere 0 1) ∧
      ∀ C ∈ componentsIn (closedBall 0 1 \ G), Disjoint C (sphere 0 1) → C = inner G := by
  obtain ⟨φ⟩ := id hG
  have J := isJordanParts φ
  have hin : inner G ⊆ closedBall 0 1 \ G := fun z hz =>
    ⟨closedInner_subset_closedBall hG hsub (Or.inl hz), J.inner_subset_compl hz⟩
  have hcomp : ∀ x ∈ inner G, connectedComponentIn (closedBall 0 1 \ G) x = inner G := by
    intro x hx
    refine Subset.antisymm ?_ (J.isConnected_inner.isPreconnected.subset_connectedComponentIn hx
      hin)
    refine J.subset_inner isPreconnected_connectedComponentIn ?_
      ⟨x, mem_connectedComponentIn (hin hx), hx⟩
    exact Set.disjoint_left.mpr fun z hz => (connectedComponentIn_subset _ _ hz).2
  obtain ⟨x₀, hx₀⟩ := J.isConnected_inner.nonempty
  refine ⟨⟨x₀, hin hx₀, hcomp x₀ hx₀⟩, ?_, ?_⟩
  · refine Set.disjoint_left.mpr fun z hz hzs => ?_
    have hint : inner G ⊆ interior (closedBall (0 : ℂ) 1) :=
      interior_maximal (fun w hw => (hin hw).1) J.isOpen_inner
    rw [interior_closedBall _ one_ne_zero] at hint
    exact (mem_ball_zero_iff.mp (hint hz)).ne (mem_sphere_zero_iff_norm.mp hzs)
  · rintro _ ⟨x, hx, rfl⟩ hdis
    have hsplit : x ∈ inner G ∨ x ∈ outer G := by
      have : x ∈ Gᶜ := hx.2
      rwa [← J.union_eq] at this
    rcases hsplit with h | h
    · exact hcomp x h
    · obtain ⟨y, hy, hyc⟩ := exists_sphere_mem_component φ h (mem_closedBall_zero_iff.mp hx.1)
      exact absurd hy (Set.disjoint_left.mp hdis hyc)

theorem exists_mid : ∃ t : 𝕀, 0 < t ∧ t < 1 := by
  refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, ?_, ?_⟩
  · exact Subtype.mk_lt_mk.mpr (by norm_num)
  · exact Subtype.mk_lt_mk.mpr (by norm_num)

theorem mem_Ioo_iff_ne {t : 𝕀} : t ∈ Ioo (0 : 𝕀) 1 ↔ t ≠ 0 ∧ t ≠ 1 := by
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨h0.ne', h1.ne⟩
  · rintro ⟨h0, h1⟩
    exact ⟨bot_lt_iff_ne_bot.mpr h0, lt_top_iff_ne_top.mpr h1⟩

/-- An arc minus its ends. -/
theorem IsArcMap.range_sdiff {a : 𝕀 → ℂ} (ha : IsArcMap a) :
    range a \ {a 0, a 1} = a '' Ioo 0 1 := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, hz⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact ⟨t, mem_Ioo_iff_ne.mpr ⟨fun h => hz.1 (by rw [h]), fun h => hz.2 (by rw [h])⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨h0, h1⟩ := mem_Ioo_iff_ne.mp ht
    refine ⟨⟨t, rfl⟩, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h => h0 (ha.2 h), fun h => h1 (ha.2 h)⟩

private theorem disjoint_closure_open_arc {a b : 𝕀 → ℂ} (ha : IsArcMap a)
    (hm : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    Disjoint (closure (a '' Ioo 0 1)) (b '' Ioo 0 1) := by
  have hcl : closure (a '' Ioo 0 1) ⊆ range a :=
    closure_minimal (image_subset_range _ _) (isCompact_range ha.1).isClosed
  refine Set.disjoint_left.mpr fun z hz => ?_
  obtain ⟨s, rfl⟩ := hcl hz
  rintro ⟨t, ht, he⟩
  obtain ⟨h0, h1⟩ := mem_Ioo_iff_ne.mp ht
  rcases hm s t he.symm with h | h
  · exact h0 h.2
  · exact h1 h.2

private theorem swap_meet {a b : 𝕀 → ℂ}
    (hm : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∀ s t, b s = a t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := fun s t h =>
  (hm t s h.symm).imp And.symm And.symm

/-- An arc inside an arc with the same ends is the whole arc. -/
theorem range_eq_of_subset {a c : 𝕀 → ℂ} (ha : IsArcMap a) (hc : IsArcMap c)
    (hsub : range c ⊆ range a) (h0 : c 0 = a 0) (h1 : c 1 = a 1) : range c = range a := by
  refine Subset.antisymm hsub ?_
  obtain ⟨ι, hι, hιc⟩ := ha.exists_inv
  have hcont : Continuous fun t => ι (c t) :=
    hιc.comp_continuous hc.1 fun t => hsub ⟨t, rfl⟩
  rintro _ ⟨s, rfl⟩
  obtain ⟨t, ht⟩ := mem_range_of_exists_le_of_exists_ge hcont
    ⟨0, by
      change ι (c 0) ≤ s
      rw [h0, hι]
      exact unitInterval.nonneg'⟩
    ⟨1, by
      change s ≤ ι (c 1)
      rw [h1, hι]
      exact unitInterval.le_one'⟩
  obtain ⟨r, hr⟩ := hsub ⟨t, rfl⟩
  refine ⟨t, ?_⟩
  rw [← hr, ← ht]
  change a r = a (ι (c t))
  rw [← hr, hι]

/-- An arc in an `O`-arc has a complementary arc with the same ends. -/
theorem exists_other_arc {F : Set ℂ} (φ : Circle ≃ₜ F) {c : 𝕀 → ℂ} (hc : IsArcMap c)
    (hsub : range c ⊆ F) : ∃ d : 𝕀 → ℂ, IsArcMap d ∧ d 0 = c 0 ∧ d 1 = c 1 ∧ range c ∪ range d = F ∧
      ∀ s t, c s = d t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
  have hne : c 0 ≠ c 1 := fun h => zero_ne_one (hc.2 h)
  obtain ⟨a, b, ha, hb, ha0, ha1, hb0, hb1, hu, hm⟩ :=
    exists_two_arcs φ (hsub ⟨0, rfl⟩) (hsub ⟨1, rfl⟩) hne
  have key : ∀ a b : 𝕀 → ℂ, IsArcMap a → IsArcMap b → a 0 = c 0 → a 1 = c 1 → b 0 = c 0 →
      b 1 = c 1 → range a ∪ range b = F →
      (∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) → c '' Ioo 0 1 ⊆ a '' Ioo 0 1 →
      ∃ d : 𝕀 → ℂ, IsArcMap d ∧ d 0 = c 0 ∧ d 1 = c 1 ∧ range c ∪ range d = F ∧
        ∀ s t, c s = d t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro a b ha hb ha0 ha1 hb0 hb1 hu hm hs
    have hsub' : range c ⊆ range a := by
      rintro _ ⟨t, rfl⟩
      by_cases h0 : t = 0
      · exact ⟨0, by rw [h0, ha0]⟩
      · by_cases h1 : t = 1
        · exact ⟨1, by rw [h1, ha1]⟩
        · exact image_subset_range _ _ (hs ⟨t, mem_Ioo_iff_ne.mpr ⟨h0, h1⟩, rfl⟩)
    have hr := range_eq_of_subset ha hc hsub' ha0.symm ha1.symm
    refine ⟨b, hb, hb0, hb1, by rw [hr, hu], fun s t he => ?_⟩
    obtain ⟨r, hr'⟩ := hsub' ⟨s, rfl⟩
    rw [← hr'] at he
    rcases hm r t he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨hc.2 ?_, h2⟩
      rw [← hr', h1, ha0]
    · right
      refine ⟨hc.2 ?_, h2⟩
      rw [← hr', h1, ha1]
  have hsplit : c '' Ioo 0 1 ⊆ a '' Ioo 0 1 ∪ b '' Ioo 0 1 := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨h0, h1⟩ := mem_Ioo_iff_ne.mp ht
    have hF : c t ∈ F := hsub ⟨t, rfl⟩
    have hend : ∀ {d : 𝕀 → ℂ}, d 0 = c 0 → d 1 = c 1 → ∀ s, d s = c t → s ∈ Ioo (0 : 𝕀) 1 := by
      intro d h2 h3 s hs
      refine mem_Ioo_iff_ne.mpr ⟨fun h => h0 (hc.2 ?_), fun h => h1 (hc.2 ?_)⟩
      · rw [← hs, h, h2]
      · rw [← hs, h, h3]
    rw [← hu] at hF
    rcases hF with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact Or.inl ⟨s, hend ha0 ha1 s hs, hs⟩
    · exact Or.inr ⟨s, hend hb0 hb1 s hs, hs⟩
  rcases IsPreconnected.subset_or_of_separated (isPreconnected_Ioo.image c hc.1.continuousOn) hsplit
    (disjoint_closure_open_arc ha hm)
    (by rw [disjoint_comm]; exact disjoint_closure_open_arc hb (swap_meet hm)) with h | h
  · exact key a b ha hb ha0 ha1 hb0 hb1 hu hm h
  · exact key b a hb ha hb0 hb1 ha0 ha1 (by rw [union_comm, hu]) (swap_meet hm) h

/-- A closed domain minus its boundary. -/
theorem closedInner_sdiff {G : Set ℂ} (hG : Nonempty (Circle ≃ₜ G)) :
    closedInner G \ G = inner G := by
  obtain ⟨φ⟩ := hG
  have J := isJordanParts φ
  ext z
  constructor
  · rintro ⟨h | h, h'⟩
    · exact h
    · exact absurd h h'
  · exact fun h => ⟨Or.inl h, J.inner_subset_compl h⟩

/-- The components of a closed domain minus a cross-cut, and of the curve minus the two ends of
the cut. -/
theorem IsCut.components {F : Set ℂ} {a b e : 𝕀 → ℂ} (c : IsCut F a b e) (J : IsJordanParts F) :
    closedInner F \ range e =
        (closedInner (side a e) \ range e) ∪ (closedInner (side b e) \ range e) ∧
      componentsIn (closedInner F \ range e) =
        {closedInner (side a e) \ range e, closedInner (side b e) \ range e} ∧
      F \ {e 0, e 1} = (range a \ {e 0, e 1}) ∪ (range b \ {e 0, e 1}) ∧
      componentsIn (F \ {e 0, e 1}) = {range a \ {e 0, e 1}, range b \ {e 0, e 1}} ∧
      range a \ {e 0, e 1} ≠ range b \ {e 0, e 1} := by
  obtain ⟨f1, -, -, f4, -, -⟩ := c.closedInner_facts J
  have hu1 : closedInner F \ range e =
      (closedInner (side a e) \ range e) ∪ (closedInner (side b e) \ range e) := by
    rw [← f1, union_sdiff_distrib]
  have hu2 : F \ {e 0, e 1} = (range a \ {e 0, e 1}) ∪ (range b \ {e 0, e 1}) := by
    rw [← c.union, union_sdiff_distrib]
  have hpart : ∀ {d : 𝕀 → ℂ}, Nonempty (Circle ≃ₜ side d e) →
      IsPreconnected (closedInner (side d e) \ range e) ∧
      (closedInner (side d e) \ range e).Nonempty ∧ IsClosed (closedInner (side d e)) := by
    rintro d ⟨φ⟩
    have J₁ := isJordanParts φ
    have hsub : inner (side d e) ⊆ closedInner (side d e) \ range e := fun z hz =>
      ⟨Or.inl hz, fun h => J₁.inner_subset_compl hz (Or.inr h)⟩
    refine ⟨J₁.isConnected_inner.isPreconnected.subset_closure hsub ?_,
      J₁.isConnected_inner.nonempty.mono hsub, J₁.isCompact_closure_inner.isClosed⟩
    rw [J₁.closure_inner]
    exact sdiff_subset
  obtain ⟨p1, n1, c1⟩ := hpart (d := a) c.oArc_side
  obtain ⟨p2, n2, c2⟩ := hpart (d := b) c.symm.oArc_side
  have hab : Disjoint (closure (closedInner (side a e) \ range e))
      (closedInner (side b e) \ range e) := by
    refine Set.disjoint_left.mpr fun z hz hz' => hz'.2 (f4 ⟨?_, hz'.1⟩)
    exact closure_minimal sdiff_subset c1 hz
  have hba : Disjoint (closedInner (side a e) \ range e)
      (closure (closedInner (side b e) \ range e)) := by
    refine Set.disjoint_left.mpr fun z hz hz' => hz.2 (f4 ⟨hz.1, ?_⟩)
    exact closure_minimal sdiff_subset c2 hz'
  have ea : range a \ {e 0, e 1} = a '' Ioo 0 1 := by
    rw [← c.a_zero, ← c.a_one, c.arc_a.range_sdiff]
  have eb : range b \ {e 0, e 1} = b '' Ioo 0 1 := by
    rw [← c.b_zero, ← c.b_one, c.arc_b.range_sdiff]
  obtain ⟨t₀, ht₀, ht₁⟩ := exists_mid
  have hA : (a '' Ioo 0 1).Nonempty := ⟨_, t₀, ⟨ht₀, ht₁⟩, rfl⟩
  have hB : (b '' Ioo 0 1).Nonempty := ⟨_, t₀, ⟨ht₀, ht₁⟩, rfl⟩
  have hd1 := disjoint_closure_open_arc c.arc_a c.meet
  have hd2 := disjoint_closure_open_arc c.arc_b (swap_meet c.meet)
  refine ⟨hu1, ?_, hu2, ?_, ?_⟩
  · rw [hu1]
    exact componentsIn_union_eq_pair p1 p2 n1 n2 hab hba
  · rw [hu2, ea, eb]
    exact componentsIn_union_eq_pair (isPreconnected_Ioo.image a c.arc_a.1.continuousOn)
      (isPreconnected_Ioo.image b c.arc_b.1.continuousOn) hA hB hd1
      (by rw [disjoint_comm]; exact hd2)
  · rw [ea, eb]
    intro h
    obtain ⟨z, hz⟩ := hA
    exact Set.disjoint_left.mp hd1 (subset_closure hz) (h ▸ hz)

/-- In the complex plane a closed disc has frontier equal to its
intrinsic boundary. -/
theorem complex_disc_frontier {D : Set ℂ} (hD : IsClosedDisc D) :
    frontier D = discBd D := by
  obtain ⟨φ⟩ := hD.isOArc_discBd
  have J := isJordanParts φ
  have heq : closedInner (discBd D) = (outer (discBd D))ᶜ := by
    ext z
    change (z ∈ inner (discBd D) ∨ z ∈ discBd D) ↔ z ∉ outer (discBd D)
    constructor
    · rintro (hz | hz)
      · exact J.disjoint.notMem_of_mem_left hz
      · exact fun h => h.1 hz
    · intro hz
      by_cases hb : z ∈ discBd D
      · exact Or.inr hb
      · have hmem : z ∈ inner (discBd D) ∪ outer (discBd D) :=
          J.union_eq.symm ▸ hb
        exact Or.inl (hmem.resolve_right hz)
  conv_lhs => rw [eq_closedInner_of_discBd ⟨φ⟩ hD rfl, heq, frontier_compl, J.frontier_outer]

/-- In the Euclidean plane the frontier and intrinsic disc boundary
also agree. -/
theorem plane_disc_frontier {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    frontier D = discBd D := by
  let e : EuclideanPlane ≃ₜ ℂ := complexPlane.symm.toHomeomorph
  obtain ⟨hDc, hb⟩ := hD.image (f := e) (f' := e.symm)
    e.continuous.continuousOn e.symm.continuous.continuousOn
    (fun _ _ => e.symm_apply_apply _)
  apply e.injective.image_injective
  rw [e.image_frontier, complex_disc_frontier hDc, hb]

/-- Every point of the Euclidean plane is a surface interior point. -/
theorem isInteriorPoint_euclideanPlane (x : EuclideanPlane) : IsInteriorPoint x := by
  let U : Set EuclideanPlane := (fun y : EuclideanPlane => y + x) '' OpenUnitDisc
  have hHomeo := (Homeomorph.addRight x).image OpenUnitDisc
  have hOpen_ball : IsOpen OpenUnitDisc := Metric.isOpen_ball
  have hOpen_U : IsOpen U := (Homeomorph.addRight x).isOpenMap OpenUnitDisc hOpen_ball
  have hxU : x ∈ U := ⟨0, by simp [OpenUnitDisc], by simp⟩
  exact ⟨U, hOpen_U, hxU, ⟨hHomeo.symm⟩⟩

protected theorem subBd_eq_frontier {S : Type*} [TopologicalSpace S] (A : Set S) :
    subBd A = frontier A := by
  rw [subBd, ← compl_eq_univ_sdiff, frontier_eq_closure_inter_closure]

theorem subBd_eq_discBd_complex {Δ : Set ℂ} (hΔ : IsClosedDisc Δ) :
    subBd Δ = discBd Δ :=
  (Surface.subBd_eq_frontier Δ).trans (complex_disc_frontier hΔ)

theorem subBd_eq_discBd_euclideanPlane {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    subBd D = discBd D :=
  (Surface.subBd_eq_frontier D).trans (plane_disc_frontier hD)

end GraphMinor.Surface
