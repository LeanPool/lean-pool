/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.ThinPainting
public import LeanPool.GraphMinor.GM11.RadialAccess
public import LeanPool.GraphMinor.GM11.Corners
public import LeanPool.GraphMinor.GM20.Section8a
public import LeanPool.GraphMinor.GM11.PlaneFacts

/-!
# The perimeter of a region has no repeated vertices

Graph Minors XIX, Section 6 (page 341) and Section 8 (page 346), use that the perimeter of a region
of
an internally 3-connected painting has no repeated vertices. We prove the form that the rest of the
paper needs: a region has at most one corner at a vertex. If it had two, an `O`-arc inside the
region
would pass through the vertex from one corner to the other. Such an `O`-arc bounds a disc that
misses
the drawing, apart from the vertex. But near the vertex the disc lies in a single corner, and the
two
ends of the `O`-arc at the vertex lie in different corners.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface unitInterval Metric

section Arcs

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- The part of a parametrized line up to a given time. -/
theorem line_piece {L : Set T} (f : I ≃ₜ L) {τ : I} (hτ : 0 < τ) :
    IsLineWithEnds ((fun t : I ↦ (f t).1) '' Iic τ) (f 0).1 (f τ).1 := by
  let p : ℝ → T := fun t ↦ (f (projIcc 0 1 zero_le_one t)).1
  have hp : Continuous p := continuous_subtype_val.comp (f.continuous.comp continuous_projIcc)
  have hp' : ∀ t : I, p t = (f t).1 := fun t ↦ by simp [p]
  have hτ0 : (0 : ℝ) < τ := hτ
  have hinj : InjOn p (Icc 0 (τ : ℝ)) := fun a ha b hb hab ↦ by
    have ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1, ha.2.trans τ.2.2⟩
    have hb' : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1, hb.2.trans τ.2.2⟩
    have := f.injective (Subtype.ext hab)
    have h₂ := congrArg Subtype.val this
    rwa [projIcc_of_mem _ ha', projIcc_of_mem _ hb'] at h₂
  have hl := GM11.isLine_of_injOn hp hτ0 hinj
  have hp0 : p 0 = (f 0).1 := by simpa using hp' 0
  have hpτ : p τ = (f τ).1 := hp' τ
  rw [hp0, hpτ] at hl
  have hset : p '' Icc 0 (τ : ℝ) = (fun t : I ↦ (f t).1) '' Iic τ := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans τ.2.2⟩
      refine ⟨⟨t, ht'⟩, ht.2, ?_⟩
      simp only [p]
      rw [projIcc_of_mem _ ht']
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ⟨t.2.1, ht⟩, hp' t⟩
  rwa [hset] at hl

/-- The part of a line up to a given point. -/
theorem IsLineWithEnds.exists_sub {L : Set T} {u v c : T} (h : IsLineWithEnds L u v) (hc : c ∈ L)
    (hne : c ≠ u) : ∃ L', IsLineWithEnds L' u c ∧ L' ⊆ L := by
  obtain ⟨f, h0, -⟩ := h
  obtain ⟨τ, hτ⟩ := f.surjective ⟨c, hc⟩
  have hτ0 : 0 < τ := by
    refine lt_of_le_of_ne bot_le fun h ↦ hne ?_
    have h₁ : c = (f τ).1 := by rw [hτ]
    rw [h₁, ← h, ← h0]
  have hl := line_piece f hτ0
  rw [h0, hτ] at hl
  refine ⟨_, hl, ?_⟩
  rintro _ ⟨t, -, rfl⟩
  exact (f _).2

/-- A short part of a line, near its first end. -/
theorem IsLineWithEnds.exists_short {L : Set T} {u v : T} (h : IsLineWithEnds L u v) {W : Set T}
    (hW : IsOpen W) (hu : u ∈ W) :
    ∃ L' a, IsLineWithEnds L' u a ∧ L' ⊆ L ∧ L' ⊆ W ∧ a ≠ u := by
  obtain ⟨f, h0, h1⟩ := h
  have hc : Continuous fun t : I ↦ (f t).1 := continuous_subtype_val.comp f.continuous
  have hO : IsOpen ((fun t : I ↦ (f t).1) ⁻¹' W) := hW.preimage hc
  have h0' : (0 : I) ∈ (fun t : I ↦ (f t).1) ⁻¹' W := by
    change (f 0).1 ∈ W
    rwa [h0]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO 0 h0'
  let τ : I := ⟨min (ε / 2) 1, le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hτ0 : (0 : ℝ) < τ := lt_min (half_pos hε) one_pos
  have hτ0' : 0 < τ := hτ0
  have hτne : (f τ).1 ≠ u := by
    rw [← h0]
    intro he
    have := f.injective (Subtype.ext he)
    have h₂ := congrArg Subtype.val this
    simp only [Icc.coe_zero] at h₂
    exact hτ0.ne' h₂
  have hl := line_piece f hτ0'
  rw [h0] at hl
  refine ⟨_, _, hl, ?_, ?_, hτne⟩
  · rintro _ ⟨t, -, rfl⟩
    exact (f _).2
  · rintro _ ⟨t, ht, rfl⟩
    refine hball ?_
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    have ht' : (t : ℝ) ≤ τ := ht
    have : (τ : ℝ) ≤ ε / 2 := min_le_left _ _
    simp only [Icc.coe_zero, sub_zero]
    rw [abs_of_nonneg t.2.1]
    linarith

omit [T2Space T] in
/-- A path from a closed set `A` to a disjoint closed set `B` has a part that meets `A` and `B` only
at its ends. -/
theorem exists_bridge {p : I → T} (hp : Continuous p) {A B : Set T} (hA : IsClosed A)
  (hB : IsClosed B)
    (hAB : ∀ t, p t ∈ A → p t ∉ B) (h0 : p 0 ∈ A) (h1 : p 1 ∈ B) :
    ∃ s t : I, s < t ∧ p s ∈ A ∧ p t ∈ B ∧ ∀ u, s < u → u < t → p u ∉ A ∧ p u ∉ B := by
  have hcB : IsCompact (p ⁻¹' B) := (hB.preimage hp).isCompact
  obtain ⟨t, ht, htm⟩ := hcB.exists_isLeast ⟨1, h1⟩ |>.imp fun t h ↦ h
  have hcA : IsCompact (p ⁻¹' A ∩ Iic t) := ((hA.preimage hp).inter isClosed_Iic).isCompact
  obtain ⟨s, hs, hsm⟩ := hcA.exists_isGreatest ⟨0, h0, (bot_le : (0 : I) ≤ t)⟩ |>.imp fun t h ↦ h
  have hst : s < t := by
    refine lt_of_le_of_ne hs.2 fun h ↦ hAB s hs.1 (h ▸ ht)
  refine ⟨s, t, hst, hs.1, ht, fun u hsu hut ↦ ⟨fun hu ↦ ?_, fun hu ↦ ?_⟩⟩
  · exact absurd (hsm ⟨hu, hut.le⟩) (not_le.mpr hsu)
  · exact absurd (htm hu) (not_le.mpr hut)

omit [T2Space T] in
/-- Near a boundary point, a closed disc without that point is connected. -/
theorem exists_lens {Δ W : Set T} (hΔ : IsClosedDisc Δ) {v : T} (hv : v ∈ discBd Δ) (hW : IsOpen W)
    (hvW : v ∈ W) : ∃ O, IsOpen O ∧ v ∈ O ∧ O ⊆ W ∧ IsPreconnected ((Δ ∩ O) \ {v}) := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  have hvΔ : v ∈ Δ := discBd_subset _ hv
  have hp : h v ∈ sphere (0 : ℂ) 1 := by
    rw [← c.bd]
    exact mem_image_of_mem _ hv
  have hpB : h v ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hp
  have hgp : g (h v) = v := c.gh hvΔ
  obtain ⟨Y, hY, hYe⟩ := continuousOn_iff'.mp c.gc W hW
  have hpY : h v ∈ Y := by
    have : h v ∈ g ⁻¹' W ∩ closedBall 0 1 := ⟨by change g _ ∈ W; rwa [hgp], hpB⟩
    rw [hYe] at this
    exact this.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hY _ hpY
  obtain ⟨O', hO', hOe⟩ := continuousOn_iff'.mp c.hc _ (isOpen_ball (x := h v) (ε := ε))
  have hvO' : v ∈ O' := by
    have : v ∈ h ⁻¹' ball (h v) ε ∩ Δ := ⟨mem_ball_self hε, hvΔ⟩
    rw [hOe] at this
    exact this.1
  let A : Set ℂ := (ball (h v) ε ∩ closedBall 0 1) \ {h v}
  have hAc : Convex ℝ A := by
    intro x hx y hy a b ha hb hab
    refine ⟨(convex_ball _ _).inter (convex_closedBall _ _) hx.1 hy.1 ha hb hab, fun he ↦ ?_⟩
    have he' : a • x + b • y = h v := he
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by linarith
      subst this
      exact hy.2 (by simpa using he')
    rcases hb.eq_or_lt with rfl | hb'
    · have : a = 1 := by linarith
      subst this
      exact hx.2 (by simpa using he')
    by_cases hxy : x = y
    · subst hxy
      refine hx.2 ?_
      rw [← add_smul, hab, one_smul] at he'
      exact he'
    · have := strictConvex_closedBall ℝ (0 : ℂ) 1 hx.1.2 hy.1.2 hxy ha' hb' hab
      rw [interior_closedBall _ one_ne_zero, he'] at this
      exact (mem_ball.mp this).ne (by simpa using hp)
  have hAg : ContinuousOn g A := c.gc.mono fun _ hx ↦ hx.1.2
  have hset : (Δ ∩ (O' ∩ W)) \ {v} = g '' A := by
    ext x
    constructor
    · rintro ⟨⟨hxΔ, hxO, -⟩, hxv⟩
      have hx' : x ∈ h ⁻¹' ball (h v) ε ∩ Δ := by
        rw [hOe]
        exact ⟨hxO, hxΔ⟩
      refine ⟨h x, ⟨⟨hx'.1, c.hm hxΔ⟩, fun he ↦ hxv ?_⟩, c.gh hxΔ⟩
      have := congrArg g he
      rwa [c.gh hxΔ, hgp] at this
    · rintro ⟨y, hy, rfl⟩
      have hyΔ := c.gm hy.1.2
      have hhy : h (g y) = y := c.hg hy.1.2
      refine ⟨⟨hyΔ, ?_, ?_⟩, fun he ↦ hy.2 ?_⟩
      · have : g y ∈ h ⁻¹' ball (h v) ε ∩ Δ :=
          ⟨show h (g y) ∈ ball (h v) ε by rw [hhy]; exact hy.1.1, hyΔ⟩
        rw [hOe] at this
        exact this.1
      · have : y ∈ g ⁻¹' W ∩ closedBall 0 1 := by
          rw [hYe]
          exact ⟨hball hy.1.1, hy.1.2⟩
        exact this.1
      · have he' : g y = v := he
        change y = h v
        rw [← hhy, he']
  refine ⟨O' ∩ W, hO'.inter hW, ⟨hvO', hvW⟩, inter_subset_right, ?_⟩
  rw [hset]
  exact hAc.isPreconnected.image g hAg

end Arcs

section Corner

open GM11

variable {T : Type} [TopologicalSpace T]

/-- `GM11.exists_sectors`, which also says that the sectors cover what lies off the drawing near the
vertex. -/
theorem exists_sectors' (hS : IsClosedSurface T) (D : Drawing T) {γ : Set T → I → T}
    (hγ : EdgePar D γ) {v : T} (hv : v ∈ D.V) (h2 : 2 ≤ Nat.card (halfEdges D γ v)) :
    ∃ next ρ P W Q τ, IsSectors D γ v next ρ P W Q τ ∧ (W \ D.U ⊆ ⋃ k, P k) ∧ ∀ k, P k ⊆ Q k := by
  have hB : DiscBoundaryStatement.{0} := disc_boundary
  have hI : DiscIArcStatement.{0} := disc_iArc
  have : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hS
  have : T2Space T := hS.2.1
  obtain ⟨next, P, W, Q, hW, hvW, hinj, hne, hreach, hconn, hdis, hcl, hcov, hsid, hQ, hQQ, hoff,
    hbdU, τ, hτ, hτl, hτr⟩ := exists_rotation_sectors hS D hγ hv h2
  have hex : ∀ k, ∃ r ∈ D.R, P k ⊆ r := by
    intro k
    obtain ⟨x, hx⟩ : (P k).Nonempty := by
      by_contra h
      have h0 := not_nonempty_iff_eq_empty.mp h
      have := hcl k
      rw [h0] at this
      simp at this
    obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp (hdis k) hx)
    exact ⟨r, hr, subset_region hr (hconn k) (hdis k) hx hxr⟩
  choose ρ hρ hsub using hex
  have hin : ∀ {r x}, r ∈ D.R → x ∈ r → ∀ k, x ∈ P k → r = ρ k := fun hr hx k hk ↦
    region_eq_of_mem hr (hρ k) hx (hsub k hk)
  refine ⟨next, ρ, P, W, Q, τ, ⟨⟨hinj, hreach, hρ, fun k ↦ closure_mono (hsub k) (hcl k), ?_, ?_,
    ?_, ?_⟩, hne, hW, hvW, hsub, hcov, fun k ↦ (hQ k).2.2.1, fun k ↦ (hQ k).1, fun k ↦ (hQ k).2.1,
    fun k ↦ (hQ k).2.2.2, hQQ, hoff, hbdU, hτ, hτl, hτr⟩, hcov, fun k ↦ (hQ k).2.2.1⟩
  · intro r hr hvr
    obtain ⟨x, hxW, hxr⟩ := mem_closure_iff.mp hvr W hW hvW
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov ⟨hxW, region_subset hr hxr⟩)
    exact ⟨k, hin hr hxr k hk⟩
  · intro k
    obtain ⟨q, hq, O, -, -, -, h₁, -⟩ := hsid k
    exact edge_subset_closure_of_incident hS (next k).2.1 (hρ k)
      ⟨q, hq, closure_mono (hsub k) h₁⟩
  · intro k
    obtain ⟨q, hq, O, -, -, -, -, h₂⟩ := hsid k
    exact edge_subset_closure_of_incident hS (next k).2.1 (hρ _)
      ⟨q, hq, closure_mono (hsub _) h₂⟩
  · intro k r hr hsubr
    obtain ⟨q, hq, O, hO, hqO, hOs, -, -⟩ := hsid k
    obtain ⟨x, hxO, hxr⟩ := mem_closure_iff.mp (hsubr hq) O hO hqO
    rcases hOs ⟨hxO, region_subset hr hxr⟩ with h | h
    · exact Or.inl (hin hr hxr _ h)
    · exact Or.inr (hin hr hxr _ h)

/-- A line from `v` into a sector, close to `v`. -/
theorem exists_line_in_sector [T2Space T] {D : Drawing T} {γ : Set T → I
  → T} {v : T} {next} {ρ P Q τ}
    {W : Set T} (h : IsSectors D γ v next ρ P W Q τ) (k) :
    ∃ L a, IsLineWithEnds L v a ∧ L ⊆ W ∧ a ≠ v ∧ L \ {v} ⊆ P k ∧ L ⊆ Q k := by
  have hQ := h.disc k
  have hvbd := h.bd k
  obtain ⟨b, hb, hbv⟩ : ∃ b ∈ discBd (Q k), b ≠ v := by
    obtain ⟨F⟩ := hQ.isOArc_discBd
    by_contra hall
    push Not at hall
    have hsing : ∀ x y : Circle, F x = F y := fun x y ↦
      Subtype.ext ((hall _ (F x).2).trans (hall _ (F y).2).symm)
    have := F.injective (hsing 1 (-1))
    have h₂ := congrArg (fun z : Circle ↦ (z : ℂ)) this
    norm_num at h₂
  obtain ⟨L₀, hL₀, hsub, hint⟩ := GM20.exists_chord hQ hvbd hb hbv.symm
  obtain ⟨L, a, hL, hLL, hLW, hav⟩ := IsLineWithEnds.exists_short hL₀
    (h.isOpen.inter (isOpen_compl_singleton (x := b))) ⟨h.mem, hbv.symm⟩
  refine ⟨L, a, hL, fun x hx ↦ (hLW hx).1, hav, fun x hx ↦ ?_, hLL.trans hsub⟩
  have hx₁ := hint ⟨hLL hx.1, fun hc ↦ by
    rcases hc with hc | hc
    · exact hx.2 hc
    · exact (hLW hx.1).2 hc⟩
  exact h.inside k ⟨⟨(hLW hx.1).1, hx₁.1⟩, hx₁.2⟩

/-- **Only one corner.** Suppose that each `O`-arc through `v` that otherwise lies in the region
`ρ k` bounds a disc that misses the drawing except at `v`. Then the region has only the corner `k`
at
`v`. -/
theorem corner_unique (hS : IsClosedSurface T) {D : Drawing T} {γ : Set T → I → T} {v : T}
    (hv : v ∈ D.V) {next}
    {ρ P Q τ} {W : Set T} (h : IsSectors D γ v next ρ P W Q τ) (hcov : W \ D.U ⊆ ⋃ k, P k)
    (hPQ : ∀ k, P k ⊆ Q k) {k j} (hkj : ρ k = ρ j)
    (hpinch : ∀ F : Set T, IsOArc F → v ∈ F → v ∈ closure (F \ {v}) → F \ {v} ⊆ ρ k →
      ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ∩ D.U ⊆ {v}) : k = j := by
  classical
  by_contra hne
  have : T2Space T := hS.2.1
  have hlp := IsClosedSurface.locPathConnected hS
  have hrR := h.corners.region k
  obtain ⟨A₀, a, hA₀, hA₀W, hav, hA₀P, hA₀Q⟩ := exists_line_in_sector h k
  obtain ⟨B₀, b, hB₀, hB₀W, hbv, hB₀P, hB₀Q⟩ := exists_line_in_sector h j
  have hPU : ∀ i, Disjoint (P i) D.U := fun i ↦
    (h.sub i).trans (region_subset (h.corners.region i)) |> fun hs ↦
      disjoint_left.mpr fun x hx hxU ↦ hs hx hxU
  have hAB : A₀ ∩ B₀ = {v} := by
    ext x
    constructor
    · rintro ⟨hxA, hxB⟩
      by_contra hxv
      exact disjoint_left.mp (hPU k) (hA₀P ⟨hxA, hxv⟩) (h.inter k j hne ⟨hA₀Q hxA, hB₀Q hxB⟩)
    · rintro rfl
      obtain ⟨f, h0, -⟩ := id hA₀
      obtain ⟨g, g0, -⟩ := id hB₀
      exact ⟨h0 ▸ (f 0).2, g0 ▸ (g 0).2⟩
  have haA : a ∈ A₀ := by
    obtain ⟨f, -, h1⟩ := hA₀
    exact h1 ▸ (f 1).2
  have hbB : b ∈ B₀ := by
    obtain ⟨f, -, h1⟩ := hB₀
    exact h1 ▸ (f 1).2
  have har : a ∈ ρ k := h.sub k (hA₀P ⟨haA, hav⟩)
  have hbr : b ∈ ρ k := hkj ▸ h.sub j (hB₀P ⟨hbB, hbv⟩)
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hS
  have hrO : IsOpen (ρ k) := region_isOpen hrR
  have hrC : IsConnected (ρ k) := by
    obtain ⟨x₀, hx₀, hr₀⟩ := (mem_R_iff D).mp hrR
    rw [hr₀]
    exact isConnected_connectedComponentIn_iff.mpr ⟨trivial, hx₀⟩
  have hrP : IsPathConnected (ρ k) := hrO.isConnected_iff_isPathConnected.mp hrC
  have hvr : v ∉ ρ k := fun hc ↦ region_subset hrR hc (D.V_subset_U hv)
  obtain ⟨p, hp⟩ := hrP.joinedIn a har b hbr
  have hA₀c : IsClosed A₀ := by
    obtain ⟨f, -, -⟩ := id hA₀
    have : A₀ = range fun t : I ↦ (f t).1 := by
      ext x
      exact ⟨fun hx ↦ ⟨f.symm ⟨x, hx⟩, by simp⟩, by rintro ⟨t, rfl⟩; exact (f t).2⟩
    rw [this]
    exact (isCompact_range (continuous_subtype_val.comp f.continuous)).isClosed
  have hB₀c : IsClosed B₀ := by
    obtain ⟨f, -, -⟩ := id hB₀
    have : B₀ = range fun t : I ↦ (f t).1 := by
      ext x
      exact ⟨fun hx ↦ ⟨f.symm ⟨x, hx⟩, by simp⟩, by rintro ⟨t, rfl⟩; exact (f t).2⟩
    rw [this]
    exact (isCompact_range (continuous_subtype_val.comp f.continuous)).isClosed
  obtain ⟨s, t, hst, hsA, htB, hmid⟩ := exists_bridge p.continuous hA₀c hB₀c
    (fun u hu hu' ↦ by
      have : p u ∈ A₀ ∩ B₀ := ⟨hu, hu'⟩
      rw [hAB] at this
      exact hvr (this ▸ hp u))
    (by rw [p.source]; exact haA) (by rw [p.target]; exact hbB)
  let m : I → I := fun u ↦ ⟨s + u * (t - s), by
    constructor
    · nlinarith [s.2.1, u.2.1, (show (s : ℝ) < t from hst)]
    · nlinarith [t.2.2, u.2.2, (show (s : ℝ) < t from hst)]⟩
  have hmc : Continuous m := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hm0 : m 0 = s := Subtype.ext (by simp [m])
  have hm1 : m 1 = t := Subtype.ext (by simp [m])
  have hstR : (s : ℝ) < t := hst
  have hqc : Continuous (p ∘ m) := p.continuous.comp hmc
  have hq01 : (p ∘ m) 0 ≠ (p ∘ m) 1 := by
    simp only [Function.comp, hm0, hm1]
    intro he
    have : p s ∈ A₀ ∩ B₀ := ⟨hsA, he ▸ htB⟩
    rw [hAB] at this
    exact hvr (this ▸ hp s)
  obtain ⟨e, hec, hei, he0, he1, her⟩ := exists_arc_of_path hqc hq01
  simp only [Function.comp, hm0, hm1] at he0 he1
  have hM : IsLineWithEnds (range e) (p s) (p t) := by
    have hcont : Continuous fun x : ℝ ↦ e (projIcc 0 1 zero_le_one x) := hec.comp continuous_projIcc
    have hl := GM11.isLine_of_injOn hcont (zero_lt_one' ℝ) (fun x hx y hy hxy ↦ by
      have := hei hxy
      have h₂ := congrArg Subtype.val this
      rwa [projIcc_of_mem _ hx, projIcc_of_mem _ hy] at h₂)
    have hset : (fun x : ℝ ↦ e (projIcc 0 1 zero_le_one x)) '' Icc 0 1 = range e := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact mem_range_self _
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, by simp⟩
    rw [hset] at hl
    simpa [he0, he1] using hl
  have hMm : ∀ x ∈ range e, x = p s ∨ x = p t ∨ (x ∉ A₀ ∧ x ∉ B₀) := by
    intro x hx
    obtain ⟨u, rfl⟩ := her hx
    simp only [Function.comp]
    rcases u.2.1.eq_or_lt with h0 | h0
    · left
      have : u = 0 := Subtype.ext h0.symm
      rw [this, hm0]
    rcases u.2.2.eq_or_lt with h1 | h1
    · right
      left
      have : u = 1 := Subtype.ext h1
      rw [this, hm1]
    right
    right
    refine hmid _ ?_ ?_
    · change (s : ℝ) < s + u * (t - s)
      nlinarith
    · change (s : ℝ) + u * (t - s) < t
      nlinarith
  have hMr : range e ⊆ ρ k := by
    intro x hx
    obtain ⟨u, rfl⟩ := her hx
    exact hp _
  have hsv : p s ≠ v := fun he ↦ hvr (he ▸ hp s)
  have htv : p t ≠ v := fun he ↦ hvr (he ▸ hp t)
  obtain ⟨A, hA, hAA⟩ := IsLineWithEnds.exists_sub hA₀ hsA hsv
  obtain ⟨B, hB, hBB⟩ := IsLineWithEnds.exists_sub hB₀ htB htv
  have hps : p s ∉ B₀ := fun hc ↦ by
    have : p s ∈ A₀ ∩ B₀ := ⟨hsA, hc⟩
    rw [hAB] at this
    exact hsv this
  have hpt : p t ∉ A₀ := fun hc ↦ by
    have : p t ∈ A₀ ∩ B₀ := ⟨hc, htB⟩
    rw [hAB] at this
    exact htv this
  have hcsA : p s ∈ A := by
    obtain ⟨f, -, h1⟩ := id hA
    exact h1 ▸ (f 1).2
  have hctB : p t ∈ B := by
    obtain ⟨f, -, h1⟩ := id hB
    exact h1 ▸ (f 1).2
  have hsM : p s ∈ range e := ⟨0, he0⟩
  have htM : p t ∈ range e := ⟨1, he1⟩
  have hX : IsLineWithEnds (A ∪ range e) v (p t) := by
    refine GM11.IsLineWithEnds.union (GM11.IsLineWithEnds.symm hA) hM ?_
    ext x
    constructor
    · rintro ⟨hxA, hxM⟩
      rcases hMm x hxM with h | h | h
      · exact h
      · exact absurd (h ▸ hAA hxA) hpt
      · exact absurd (hAA hxA) h.1
    · rintro rfl
      exact ⟨hcsA, hsM⟩
  have hF : IsOArc ((A ∪ range e) ∪ B) := by
    refine GM11.isOArc_union hX hB ?_
    rintro x ⟨hxX | hxM, hxB⟩
    · have : x ∈ A₀ ∩ B₀ := ⟨hAA hxX, hBB hxB⟩
      rw [hAB] at this
      exact Or.inl this
    · rcases hMm x hxM with h | h | h
      · exact absurd (h ▸ hBB hxB) hps
      · exact Or.inr h
      · exact absurd (hBB hxB) h.2
  have hvA : v ∈ A := by
    obtain ⟨f, h0, -⟩ := id hA
    exact h0 ▸ (f 0).2
  have hvB : v ∈ B := by
    obtain ⟨f, h0, -⟩ := id hB
    exact h0 ▸ (f 0).2
  obtain ⟨Δ, hΔ, hΔF, hΔU⟩ := hpinch _ hF (Or.inl (Or.inl hvA))
    (closure_mono (sdiff_subset_sdiff_left (fun x hx ↦ Or.inl (Or.inl hx)))
      (GM11.IsLineWithEnds.mem_closure_sdiff hA)) (by
    rintro x ⟨(hx | hx) | hx, hxv⟩
    · exact h.sub k (hA₀P ⟨hAA hx, hxv⟩)
    · exact hMr hx
    · exact hkj ▸ h.sub j (hB₀P ⟨hBB hx, hxv⟩))
  have hFΔ : (A ∪ range e) ∪ B ⊆ Δ := hΔF ▸ Surface.discBd_subset Δ
  obtain ⟨O, hO, hvO, hOW, hCon⟩ := exists_lens hΔ (by rw [hΔF]; exact Or.inl (Or.inl hvA)) h.isOpen
    h.mem
  obtain ⟨x₁, hx₁O, hx₁⟩ := mem_closure_iff.mp (GM11.IsLineWithEnds.mem_closure_sdiff hA) O hO hvO
  obtain ⟨x₂, hx₂O, hx₂⟩ := mem_closure_iff.mp (GM11.IsLineWithEnds.mem_closure_sdiff hB) O hO hvO
  have hfin : Finite (halfEdges D γ v) := (finite_halfEdges D γ v).to_subtype
  have hCU : ∀ y ∈ (Δ ∩ O) \ {v}, y ∉ D.U := fun y hy hyU ↦ hy.2 (hΔU ⟨hy.1.1, hyU⟩)
  have hcover : (Δ ∩ O) \ {v} ⊆ Q k ∪ ⋃ i : {i // i ≠ k}, Q i.1 := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov ⟨hOW hy.1.2, hCU y hy⟩)
    by_cases hik : i = k
    · exact Or.inl (hik ▸ hPQ i hi)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hik⟩, hPQ i hi⟩)
  have hQ' : IsClosed (⋃ i : {i // i ≠ k}, Q i.1) :=
    isClosed_iUnion_of_finite fun i : {i // i ≠ k} ↦ (h.disc i.1).isClosed
  obtain ⟨y, hy, hyk, hyi⟩ := isPreconnected_closed_iff.mp hCon _ _ (h.disc k).isClosed
    hQ' hcover
    ⟨x₁, ⟨⟨hFΔ (Or.inl (Or.inl hx₁.1)), hx₁O⟩, hx₁.2⟩, hPQ k (hA₀P ⟨hAA hx₁.1, hx₁.2⟩)⟩
    ⟨x₂, ⟨⟨hFΔ (Or.inr hx₂.1), hx₂O⟩, hx₂.2⟩, mem_iUnion.mpr ⟨⟨j, Ne.symm hne⟩,
      hPQ j (hB₀P ⟨hBB hx₂.1, hx₂.2⟩)⟩⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hyi
  exact hCU y hy (h.inter k i.1 (Ne.symm i.2) ⟨hyk, hi⟩)

end Corner

section Hat

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]

omit [T2Space S] in
theorem IsCappedSurface.isClosedSurface (cap : IsCappedSurface S Shat) : IsClosedSurface Shat := by
  have hsurf := cap.isSurface
  refine ⟨hsurf.1, hsurf.2.1, fun x ↦ ?_⟩
  by_contra hx
  have : x ∈ bd Shat := hx
  rw [cap.bd_empty] at this
  exact this

omit [T2Space S] in
theorem IsCappedSurface.isClosedEmbedding (hS : IsSurface S) (cap : IsCappedSurface S Shat) :
    IsClosedEmbedding cap.emb := by
  have hsurf := cap.isSurface
  have : CompactSpace S := hS.1
  have : T2Space Shat := hsurf.2.1
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap cap.isEmbedding.continuous
    cap.isEmbedding.injective cap.isEmbedding.continuous.isClosedMap

omit [T2Space S] in
theorem IsCappedSurface.notMem_range (cap : IsCappedSurface S Shat) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
    {x : Shat} (hx : x ∈ cap.cuffDisc Θ) : x ∉ range cap.emb := fun hr ↦ by
  have : x ∈ (range cap.emb)ᶜ := by
    rw [cap.compl_eq]
    exact mem_iUnion₂.2 ⟨Θ, hΘ, hx⟩
  exact this hr

omit [T2Space S] in
/-- A region of `Γ` in `Σ̂` either lies in `Σ`, or is the inside of a pasted disc. -/
theorem hatRegion_cases (hS : IsSurface S) (cap : IsCappedSurface S Shat)
  (Γ : Painting S) {r : Set Shat}
    (hr : r ∈ Γ.hatRegions cap) : r ⊆ range cap.emb ∨ ∃ Θ ∈ cuffs S, r = cap.cuffDisc Θ := by
  have hsurf := cap.isSurface
  have : T2Space Shat := hsurf.2.1
  have hman : ∀ x : Shat, IsManifoldPoint x := hsurf.2.2
  by_cases hex : ∃ Θ ∈ cuffs S, (r ∩ cap.cuffDisc Θ).Nonempty
  · right
    obtain ⟨Θ, hΘ, x, hxr, hxΘ⟩ := hex
    refine ⟨Θ, hΘ, ?_⟩
    obtain ⟨y, hy, rfl⟩ := hr
    rw [connectedComponentIn_eq hxr]
    have hx : x ∈ (Γ.hatU cap)ᶜ := connectedComponentIn_subset _ _ hxr
    set r := connectedComponentIn (Γ.hatU cap)ᶜ x with hrdef
    have hrpre : IsPreconnected r := isPreconnected_connectedComponentIn
    have hrU : r ⊆ (Γ.hatU cap)ᶜ := connectedComponentIn_subset _ _
    have hcapopen : IsOpen (cap.cuffDisc Θ) := by
      rw [cap.cuffDisc_eq_discInt hS hΘ]
      exact (cap.cuffDisc_closedDisc Θ hΘ).isOpen_discInt hman
    have hcapU : cap.cuffDisc Θ ⊆ (Γ.hatU cap)ᶜ := fun w hw ⟨y, _, hy⟩ ↦
      cap.notMem_range hΘ hw ⟨y, hy⟩
    have hconn : IsPreconnected (cap.cuffDisc Θ) := by
      rw [cap.cuffDisc_eq_discInt hS hΘ]
      exact (cap.cuffDisc_closedDisc Θ hΘ).isPreconnected_discInt
    have h₁ : cap.cuffDisc Θ ⊆ r := hconn.subset_connectedComponentIn hxΘ hcapU
    have h₂ : r ⊆ cap.cuffDisc Θ := by
      refine hrpre.subset_left_of_subset_union hcapopen
        (isClosed_closure (s := cap.cuffDisc Θ)).isOpen_compl ?_ (fun w hw ↦ ?_)
        ⟨x, mem_connectedComponentIn hx, hxΘ⟩
      · exact disjoint_left.2 fun w hw hn ↦ hn (subset_closure hw)
      · by_cases hwc : w ∈ cap.cuffDisc Θ
        · exact Or.inl hwc
        · refine Or.inr fun hcl ↦ ?_
          rw [cap.closure_cuffDisc hS hΘ] at hcl
          rcases hcl with h | ⟨y, hy, rfl⟩
          · exact hwc h
          · have hyb : y ∈ bd S := by
              obtain ⟨z, hz, rfl⟩ := hΘ
              exact connectedComponentIn_subset _ _ hy
            exact hrU hw (mem_image_of_mem _ (Γ.bd_subset hyb))
    exact Subset.antisymm h₂ h₁
  · left
    intro x hxr
    by_contra hn
    have hmem : x ∈ ⋃ Θ ∈ cuffs S, cap.cuffDisc Θ := by
      rw [← cap.compl_eq]
      exact hn
    obtain ⟨Θ, hΘ, hxΘ⟩ := mem_iUnion₂.1 hmem
    exact hex ⟨Θ, hΘ, x, hxr, hxΘ⟩

/-- If a drawing has no loops, and an `O`-arc through `v` meets the drawing only at `v`, and a disc
bounded by the `O`-arc has only the vertex `v`, then the disc meets the drawing only at `v`. An
edge that meets the disc elsewhere stays inside, so both ends lie in the disc, and they are
different. -/
theorem disc_misses {T : Type} [TopologicalSpace T] [T2Space T] (hman : ∀ x : T, IsManifoldPoint x)
    {D : Drawing T} (hloop : ∀ e ∈ D.E, ∃ u w, u ≠ w ∧ closure e ∩ D.V = {u, w})
    {Δ : Set T} (hΔ : IsClosedDisc Δ) {v : T} (hvV : v ∈ D.V) (hbd : discBd Δ ∩ D.U ⊆ {v})
    (hV : Δ ∩ D.V ⊆ {v}) :
    Δ ∩ D.U ⊆ {v} := by
  rintro y ⟨hyΔ, hyU⟩
  by_cases hyV : y ∈ D.V
  · exact hV ⟨hyΔ, hyV⟩
  by_cases hyF : y ∈ discBd Δ
  · exact hbd ⟨hyF, hyU⟩
  exfalso
  obtain ⟨e, he, hye⟩ := GM19.exists_arcComp_superset (F := D.U \ D.V) (isPathConnected_singleton y)
    (singleton_subset_iff.2 ⟨hyU, hyV⟩)
  have hye' : y ∈ e := hye rfl
  have hint : IsOpen (discInt Δ) := hΔ.isOpen_discInt hman
  have hyint : y ∈ discInt Δ := ⟨hyΔ, hyF⟩
  have hec : e ⊆ D.U \ D.V := he.2.1
  have hsub : e ⊆ discInt Δ := by
    have hdis : ∀ x ∈ e, x ∉ discBd Δ := fun x hx hxF ↦ by
      have hxv : x = v := hbd ⟨hxF, (hec hx).1⟩
      exact (hec hx).2 (hxv ▸ hvV)
    refine he.2.2.1.isConnected.isPreconnected.subset_left_of_subset_union hint
      (hΔ.isClosed.isOpen_compl) ?_ (fun x hx ↦ ?_) ⟨y, hye', hyint⟩
    · exact disjoint_left.2 fun x hx hn ↦ hn hx.1
    · by_cases hxΔ : x ∈ Δ
      · exact Or.inl ⟨hxΔ, hdis x hx⟩
      · exact Or.inr hxΔ
  obtain ⟨u, w, huw, hset⟩ := hloop e he
  have hcl : closure e ⊆ Δ := closure_minimal (hsub.trans fun x hx ↦ hx.1) hΔ.isClosed
  have hu : u ∈ closure e ∩ D.V := by rw [hset]; exact Or.inl rfl
  have hw : w ∈ closure e ∩ D.V := by rw [hset]; exact Or.inr rfl
  have h₁ : u = v := hV ⟨hcl hu.1, hu.2⟩
  have h₂ : w = v := hV ⟨hcl hw.1, hw.2⟩
  exact huw (h₁.trans h₂.symm)

theorem arcComponentsIn_image' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {ι : X → Y}
    (hι : IsEmbedding ι) {F c : Set X} (hc : c ∈ arcComponentsIn F) :
    ι '' c ∈ arcComponentsIn (ι '' F) := by
  refine ⟨hc.1.image _, image_mono hc.2.1, hc.2.2.1.image hι.continuous, fun D hDF hD hsub ↦ ?_⟩
  have hDr : ι '' (ι ⁻¹' D) = D := image_preimage_eq_of_subset (hDF.trans (image_subset_range _ _))
  have hpc : IsPathConnected (ι ⁻¹' D) := by
    rw [hι.isInducing.isPathConnected_iff, hDr]
    exact hD
  have hsub' : ι ⁻¹' D ⊆ F := fun x hx ↦ by
    obtain ⟨y, hy, hyx⟩ := hDF hx
    exact hι.injective hyx ▸ hy
  have := hc.2.2.2 (ι ⁻¹' D) hsub' hpc (by
    intro x hx
    exact hsub (mem_image_of_mem _ hx))
  rw [← hDr, this]

/-- The sets that come from `sk(Γ)` drawn in `Σ̂`. -/
structure IsSkHat (cap : IsCappedSurface S Shat) (Γ : Painting S) (D : Drawing Shat) : Prop where
  hU : D.U = cap.emb '' Γ.skU
  hV : D.V = cap.emb '' Γ.V

theorem exists_isSkHat (hS : IsSurface S) (cap : IsCappedSurface S Shat) (Γ : Painting S) :
    ∃ D, IsSkHat cap Γ D := by
  obtain ⟨D₀, hD₀U, hD₀V⟩ := Γ.exists_skDrawing
  obtain ⟨D, hDU, hDV⟩ := exists_drawing_image D₀ (cap.isClosedEmbedding hS)
  rw [hD₀U] at hDU
  rw [hD₀V] at hDV
  exact ⟨D, hDU, hDV⟩

omit [T2Space S] in
theorem IsSkHat.edge_iff (_hS : IsSurface S) {cap : IsCappedSurface S Shat} {Γ : Painting S}
    {D : Drawing Shat} (h : IsSkHat cap Γ D) {C : Set Shat} :
    C ∈ D.E ↔ ∃ e ∈ arcComponentsIn (Γ.skU \ Γ.V), cap.emb '' e = C := by
  have hset : D.U \ D.V = cap.emb '' (Γ.skU \ Γ.V) := by
    rw [h.hU, h.hV, image_sdiff cap.isEmbedding.injective]
  constructor
  · intro hC
    have hC' : C ∈ arcComponentsIn (cap.emb '' (Γ.skU \ Γ.V)) := hset ▸ hC
    obtain ⟨c, hc, rfl⟩ := arcComponentsIn_image cap.isEmbedding hC'
    exact ⟨c, hc, rfl⟩
  · rintro ⟨e, he, rfl⟩
    change _ ∈ arcComponentsIn (D.U \ D.V)
    rw [hset]
    exact arcComponentsIn_image' cap.isEmbedding he

omit [T2Space S] in
/-- A region of `Γ` in `Σ̂` is a region of `sk(Γ)`. If a component of the complement of `sk(Γ)` went
beyond the region it would enter the inside of a disc of an edge of size 3. The frontier of that
inside lies in `sk(Γ)`, so the component would lie in it, which it does not. -/
theorem IsSkHat.hatRegion_mem_R {cap : IsCappedSurface S Shat} {Γ : Painting S}
    {D : Drawing Shat} (h : IsSkHat cap Γ D) (_hS : IsSurface S) {r : Set Shat}
    (hr : r ∈ Γ.hatRegions cap) : r ∈ D.R := by
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hsub : D.U ⊆ Γ.hatU cap := by
    rw [h.hU]
    exact image_mono Γ.skU_subset
  obtain ⟨x, hx, rfl⟩ := hr
  have hxD : x ∈ univ \ D.U := ⟨trivial, fun hc ↦ hx (hsub hc)⟩
  refine ⟨x, hxD, Subset.antisymm ?_ ?_⟩
  rotate_left
  · refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx) ?_
    exact (connectedComponentIn_subset _ _).trans fun y hy ↦ ⟨trivial, fun hc ↦ hy (hsub hc)⟩
  · refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxD) fun y hy ↦ ?_
    have hyD : y ∈ univ \ D.U := connectedComponentIn_subset _ _ hy
    by_contra hyU
    have hyU' : y ∈ Γ.hatU cap := not_not.mp hyU
    obtain ⟨z, hzU, rfl⟩ := hyU'
    have hzsk : z ∉ Γ.skU := fun hc ↦ hyD.2 (by rw [h.hU]; exact mem_image_of_mem _ hc)
    have hzV : z ∉ Γ.V := fun hc ↦ hzsk (Or.inl (Or.inl hc))
    obtain ⟨c, hc, hzc⟩ := exists_arcComp_superset (F := Γ.U \ Γ.V)
      (isPathConnected_singleton z) (singleton_subset_iff.2 ⟨hzU, hzV⟩)
    have hzc' : z ∈ c := hzc rfl
    have h3 : (tilde c).ncard = 3 := by
      rcases Γ.size_cases hc with h2 | h3
      · exact absurd (Or.inl (Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h2⟩, hzc'⟩))) hzsk
      · exact h3
    obtain ⟨hdisc, -⟩ := Γ.isDisc_of_three hc h3
    obtain ⟨hC, hCbd⟩ := isClosedDisc_image hdisc cap.isEmbedding
    have hopen := hC.isOpen_discInt hman
    have hbdU : discBd (cap.emb '' closure c) ⊆ D.U := by
      rw [hCbd, h.hU]
      exact image_mono fun w hw ↦ Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h3⟩, hw⟩)
    have hyB : cap.emb z ∈ discInt (cap.emb '' closure c) :=
      ⟨mem_image_of_mem _ (subset_closure hzc'), fun hc' ↦ hyD.2 (hbdU hc')⟩
    have hin : connectedComponentIn (univ \ D.U) x ⊆ discInt (cap.emb '' closure c) := by
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hopen
        hC.isClosed.isOpen_compl ?_ (fun w hw ↦ ?_) ⟨_, hy, hyB⟩
      · exact disjoint_left.2 fun w hw hn ↦ hn hw.1
      · by_cases hwC : w ∈ cap.emb '' closure c
        · exact Or.inl ⟨hwC, fun hb ↦ (connectedComponentIn_subset _ _ hw).2 (hbdU hb)⟩
        · exact Or.inr hwC
    obtain ⟨⟨u, hu, hue⟩, -⟩ := hin (mem_connectedComponentIn hxD)
    exact hx ⟨u, Γ.closure_subset_U hc hu, hue⟩

/-- `sk(Γ)` has no loops. -/
theorem IsSkHat.no_loops (hS : IsSurface S) {cap : IsCappedSurface S Shat} {Γ : Painting S}
    {D : Drawing Shat} (h : IsSkHat cap Γ D) :
    ∀ e ∈ D.E, ∃ u w, u ≠ w ∧ closure e ∩ D.V = {u, w} := by
  intro C hC
  obtain ⟨e, he, rfl⟩ := (h.edge_iff hS).mp hC
  obtain ⟨u, w, huw, ht, htV, -⟩ := Γ.sk_line he
  refine ⟨cap.emb u, cap.emb w, cap.isEmbedding.injective.ne huw, ?_⟩
  have hset : closure e ∩ Γ.V = {u, w} := by
    rw [← ht]
    ext x
    constructor
    · rintro ⟨hx, hxV⟩
      exact ⟨hx, fun hxe ↦ (he.2.1 hxe).2 hxV⟩
    · exact fun hx ↦ ⟨hx.1, htV hx⟩
  rw [(cap.isClosedEmbedding hS).closure_image_eq, h.hV, ← image_inter cap.isEmbedding.injective,
    hset, image_pair]

/-- Inside a closed disc whose boundary holds all of the drawing in the disc, an `O`-arc through a
boundary
point `v` and otherwise in the open disc bounds a disc that meets the drawing only at `v`. -/
theorem pinch_of_cell {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T) {D : Drawing T}
    {C F : Set T} (hC : IsClosedDisc C) (hF : IsOArc F) {v : T} (hsub : F ⊆ C)
    (hint : F \ {v} ⊆ discInt C) (hU : C ∩ D.U ⊆ discBd C) :
    ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ∩ D.U ⊆ {v} := by
  have : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  obtain ⟨Δ, ⟨hΔC, hΔ, hbd, -⟩, -⟩ := disc_oArc.{0} C F hC hsub hF
  refine ⟨Δ, hΔ, hbd, ?_⟩
  rintro y ⟨hyΔ, hyU⟩
  by_contra hyv
  have hyb := hU ⟨hΔC hyΔ, hyU⟩
  have hyF : y ∉ F := fun h ↦ (hint ⟨h, hyv⟩).2 hyb
  have hyint : y ∈ discInt Δ := ⟨hyΔ, by rwa [hbd]⟩
  have hin : y ∈ interior C := mem_interior.mpr ⟨discInt Δ, fun x hx ↦ hΔC hx.1,
    hΔ.isOpen_discInt hman, hyint⟩
  rw [← GM11.IsClosedDisc.frontier_eq_discBd hT hC] at hyb
  exact hyb.2 hin

/-- An `O`-arc through a vertex `v` that otherwise lies in a region of an internally 3-connected
painting bounds a disc that meets `sk(Γ)` only at `v`. In `Σ` this comes from the definition of
internal 3-connectivity, since the `O`-arc meets `V(Γ)` and `bd(Σ)` only at `v`. In a pasted disc it
comes from the disc. -/
theorem pinch (hS : IsSurface S) {cap : IsCappedSurface S Shat} {Γ : Painting S} {D : Drawing Shat}
    (h : IsSkHat cap Γ D) (h3 : Γ.IsInternallyThreeConnected) {r : Set Shat}
    (hr : r ∈ Γ.hatRegions cap) {v₀ : S} (hv₀ : v₀ ∈ Γ.V) {F : Set Shat} (hF : IsOArc F)
    (_hvF : cap.emb v₀ ∈ F) (hcl : cap.emb v₀ ∈ closure (F \ {cap.emb v₀}))
    (hsub : F \ {cap.emb v₀} ⊆ r) :
    ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ∩ D.U ⊆ {cap.emb v₀} := by
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hrU : r ⊆ (Γ.hatU cap)ᶜ := by
    obtain ⟨x, hx, rfl⟩ := hr
    exact connectedComponentIn_subset _ _
  rcases hatRegion_cases hS cap Γ hr with hrr | ⟨Θ, hΘ, rfl⟩
  · have hFr : F ⊆ range cap.emb := fun x hx ↦ by
      by_cases hxv : x = cap.emb v₀
      · exact ⟨v₀, hxv.symm⟩
      · exact hrr (hsub ⟨hx, hxv⟩)
    have hFe : cap.emb '' (cap.emb ⁻¹' F) = F := image_preimage_eq_of_subset hFr
    set F₀ := cap.emb ⁻¹' F with hF₀
    have hO : IsOArc F₀ := by
      obtain ⟨φ⟩ := hF
      rw [← hFe] at φ
      exact ⟨φ.trans (cap.isEmbedding.homeomorphImage F₀).symm⟩
    have hF₀U : F₀ ∩ Γ.U ⊆ {v₀} := by
      rintro x ⟨hxF, hxU⟩
      by_contra hxv
      exact hrU (hsub ⟨hxF, fun he ↦ hxv (cap.isEmbedding.injective he)⟩)
        (mem_image_of_mem _ hxU)
    have hbdU : F₀ ∩ bd S ⊆ {v₀} := fun x hx ↦ hF₀U ⟨hx.1, Γ.bd_subset hx.2⟩
    have hVU : F₀ ∩ Γ.V ⊆ {v₀} := fun x hx ↦ hF₀U ⟨hx.1, Γ.V_subset hx.2⟩
    have hc₁ : (F₀ ∩ Γ.V).ncard ≤ 1 := by
      simpa using ncard_le_ncard hVU (finite_singleton v₀)
    have hc₂ : (F₀ ∩ bd S).ncard ≤ 1 := by
      simpa using ncard_le_ncard hbdU (finite_singleton v₀)
    obtain ⟨Δ₀, hΔ₀, hbd, hV⟩ := h3.2 F₀ hO (fun x hx ↦ by
      have := hF₀U hx
      rw [mem_singleton_iff.mp this]
      exact hv₀) ((finite_singleton v₀).subset hbdU) (by omega)
    obtain ⟨hΔ, hbdΔ⟩ := isClosedDisc_image hΔ₀ cap.isEmbedding
    refine ⟨cap.emb '' Δ₀, hΔ, by rw [hbdΔ, hbd, hFe], ?_⟩
    refine disc_misses hman (h.no_loops hS) hΔ (by rw [h.hV]; exact mem_image_of_mem _ hv₀) ?_ ?_
    · rintro _ ⟨hy, hyU⟩
      rw [hbdΔ, hbd] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [h.hU] at hyU
      obtain ⟨z, hz, hzx⟩ := hyU
      obtain rfl := cap.isEmbedding.injective hzx
      exact congrArg _ (hF₀U ⟨hx, Γ.skU_subset hz⟩)
    · rintro _ ⟨⟨x, hx, rfl⟩, hyV⟩
      rw [h.hV] at hyV
      obtain ⟨z, hz, hzx⟩ := hyV
      obtain rfl := cap.isEmbedding.injective hzx
      exact congrArg _ (hVU ⟨hV ⟨hx, hz⟩, hz⟩)
  · have hC := cap.cuffDisc_closedDisc Θ hΘ
    have hint : F \ {cap.emb v₀} ⊆ discInt (closure (cap.cuffDisc Θ)) := by
      rw [← cap.cuffDisc_eq_discInt hS hΘ]
      exact hsub
    refine pinch_of_cell hT hC hF (fun x hx ↦ ?_) hint ?_
    · by_cases hxv : x = cap.emb v₀
      · rw [hxv]
        exact closure_mono hsub hcl
      · exact subset_closure (hsub ⟨hx, hxv⟩)
    · rintro y ⟨hyC, hyU⟩
      rw [cap.cuffDisc_bd Θ hΘ]
      rw [cap.closure_cuffDisc hS hΘ] at hyC
      rcases hyC with hy | hy
      · rw [h.hU] at hyU
        obtain ⟨z, -, rfl⟩ := hyU
        exact absurd (mem_range_self z) (cap.notMem_range hΘ hy)
      · exact hy

/-- The two edges of `sk(Γ)` at a vertex in the frontier of a region: there are at most two. -/
theorem sk_frontier_pair (hS : IsSurface S) {cap : IsCappedSurface S Shat} {Γ : Painting S}
    (h3 : Γ.IsInternallyThreeConnected) {r : Set Shat} (hr : r ∈ Γ.hatRegions cap) {v₀ : S}
    (hv₀ : v₀ ∈ Γ.V) : ∃ f₁ f₂ : Set S, ∀ f ∈ arcComponentsIn (Γ.skU \ Γ.V), v₀ ∈ tilde f →
      cap.emb '' f ⊆ frontier r → f = f₁ ∨ f = f₂ := by
  classical
  obtain ⟨D, hD⟩ := exists_isSkHat hS cap Γ
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  have : Nonempty Shat := ⟨cap.emb v₀⟩
  by_cases hex : ∃ f ∈ arcComponentsIn (Γ.skU \ Γ.V), v₀ ∈ tilde f ∧ cap.emb '' f ⊆ frontier r
  swap
  · exact ⟨∅, ∅, fun f hf hv hfr ↦ absurd ⟨f, hf, hv, hfr⟩ hex⟩
  obtain ⟨f₀, hf₀, hvf₀, hfr₀⟩ := hex
  have hvD : cap.emb v₀ ∈ D.V := by
    rw [hD.hV]
    exact mem_image_of_mem _ hv₀
  obtain ⟨γ, hγ⟩ := GM11.exists_edgePar D
  have hhalf : ∀ f ∈ arcComponentsIn (Γ.skU \ Γ.V), v₀ ∈ tilde f →
      ∃ x ∈ GM11.halfEdges D γ (cap.emb v₀), x.1 = cap.emb '' f := by
    intro f hf hv
    have hE : cap.emb '' f ∈ D.E := (hD.edge_iff hS).mpr ⟨f, hf, rfl⟩
    have hcl : cap.emb v₀ ∈ closure (cap.emb '' f) :=
      image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ hv.1)
    obtain ⟨b, hb⟩ := GM11.exists_end_eq hγ hE hvD hcl
    exact ⟨(cap.emb '' f, b), ⟨hE, hb⟩, rfl⟩
  have hinj : ∀ f : Set S, cap.emb ⁻¹' (cap.emb '' f) = f := fun f ↦
    preimage_image_eq _ cap.isEmbedding.injective
  have hfin : Finite (GM11.halfEdges D γ (cap.emb v₀)) :=
    (GM11.finite_halfEdges D γ _).to_subtype
  by_cases h2 : 2 ≤ Nat.card (GM11.halfEdges D γ (cap.emb v₀))
  · obtain ⟨next, ρ, P, W, Q, τ, hsec, hcov, hPQ⟩ := exists_sectors' hT D hγ hvD h2
    have hrD : r ∈ D.R := hD.hatRegion_mem_R hS hr
    have hsurj : Function.Surjective next := Finite.injective_iff_surjective.mp hsec.corners.inj
    have hcl : ∀ f : Set S, cap.emb '' f ⊆ frontier r → cap.emb '' f ⊆ closure r :=
      fun f hf ↦ hf.trans frontier_subset_closure
    obtain ⟨x₀, hx₀, hx₀e⟩ := hhalf f₀ hf₀ hvf₀
    obtain ⟨k₀, hk₀⟩ := hsurj ⟨x₀, hx₀⟩
    obtain ⟨i, hi⟩ : ∃ i, ρ i = r := by
      have hs : (next k₀).1.1 ⊆ closure r := by
        rw [hk₀]
        change x₀.1 ⊆ _
        rw [hx₀e]
        exact hcl _ hfr₀
      rcases hsec.corners.sides k₀ r hrD hs with h | h
      · exact ⟨k₀, h.symm⟩
      · exact ⟨_, h.symm⟩
    have huniq : ∀ j, ρ j = r → j = i := fun j hj ↦ by
      refine (corner_unique hT hvD hsec hcov hPQ (hi.trans hj.symm) fun F hF hvF hclF hsub ↦
        ?_).symm
      rw [hi] at hsub
      exact pinch hS hD h3 hr hv₀ hF hvF hclF hsub
    refine ⟨cap.emb ⁻¹' i.1.1, cap.emb ⁻¹' (next i).1.1, fun f hf hv hfr ↦ ?_⟩
    obtain ⟨x, hx, hxe⟩ := hhalf f hf hv
    obtain ⟨k, hk⟩ := hsurj ⟨x, hx⟩
    have hs : (next k).1.1 ⊆ closure r := by
      rw [hk]
      change x.1 ⊆ _
      rw [hxe]
      exact hcl _ hfr
    rcases hsec.corners.sides k r hrD hs with h | h
    · right
      obtain rfl := huniq k h.symm
      rw [hk]
      change f = cap.emb ⁻¹' x.1
      rw [hxe, hinj]
    · left
      have := huniq _ h.symm
      rw [← this, hk]
      change f = cap.emb ⁻¹' x.1
      rw [hxe, hinj]
  · have hsub : Subsingleton (GM11.halfEdges D γ (cap.emb v₀)) := by
      rw [← Finite.card_le_one_iff_subsingleton]
      omega
    obtain ⟨x₀, hx₀, hx₀e⟩ := hhalf f₀ hf₀ hvf₀
    refine ⟨f₀, f₀, fun f hf hv _ ↦ Or.inl ?_⟩
    obtain ⟨x, hx, hxe⟩ := hhalf f hf hv
    have := congrArg Subtype.val (hsub.elim ⟨x, hx⟩ ⟨x₀, hx₀⟩)
    have he : cap.emb '' f = cap.emb '' f₀ := by
      rw [← hxe, ← hx₀e]
      exact congrArg Prod.fst this
    rw [← hinj f, he, hinj]

end Hat

end GraphMinor.GM19
