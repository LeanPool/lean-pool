/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.FlatCover
public import LeanPool.GraphMinor.Surface.ArcDisc

/-!
# Adding cells to a flat set

A set is flat if paths in it with the same ends are homotopic. Graph Minors XI shows that the
regions of a drawing, with a small
open set around each vertex of a small set, form a flat set, when the short circuits of its radial
drawing are null-homotopic.
The skeleton of a painting has more regions than the painting has: each disc edge adds a cell. We
have no radial circuits around
these cells. So we add the cells afterwards.

Let `Z` be a flat open set and let `c` be a cell. If two points of `Z` in `c` are always joined by a
path in `Z` and a path in `c`
of the same class, then `Z ∪ c` is flat (`flat_union_of_common`). To arrange this we shrink the sets
around the vertices, so that
each looks like a corner of the cell (`IsCone`). The result used later is `exists_flat_with_cells`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

variable {T : Type} [TopologicalSpace T]

/-- Two flat open sets, the second one path-connected, have a flat union if paths in the two sets
agree between common points. -/
theorem flat_union_of_common {Z c : Set T} (hZo : IsOpen Z) (hco : IsOpen c) (hZ : Flat Z)
  (hc : Flat c) (hcp : IsPathConnected c)
    (hpair : ∀ x ∈ Z ∩ c, ∀ y ∈ Z ∩ c, ∃ f : Cl x y, Arw Z f ∧ Arw c f) : Flat (Z ∪ c) := by
  classical
  have hclose : ∀ {a x y : T} {g₁ : Cl a x} {g₂ : Cl x y}, x ∈ Z ∩ c → y ∈ Z ∩ c → Arw Z g₁
    → Arw c g₂ → Arw Z (g₁.trans g₂) := by
    intro a x y g₁ g₂ hx hy h₁ h₂
    obtain ⟨f, hfZ, hfc⟩ := hpair x hx y hy
    rw [hc.eq h₂ hfc]
    exact h₁.trans hfZ
  have key : ∀ (a e : T) (p : Path a e), (∀ u, p u ∈ Z ∪ c) → a ∈ Z → e ∈ Z → Arw Z (Cl.mk p) := by
    intro a e p hp ha he
    let Q : ∀ d : T, Cl a d → Prop := fun d g => (d ∈ Z ∧ Arw Z g) ∨
      (d ∈ c ∧ ∃ x, x ∈ Z ∩ c ∧ ∃ (g₁ : Cl a x) (g₂ : Cl x d), Arw Z g₁ ∧ Arw c g₂ ∧ g
        = g₁.trans g₂)
    have hQ : Q e (Cl.mk p) := by
      refine cl_induction (𝒞 := {Z, c}) ?_ p ?_ Q (.inl ⟨ha, arw_refl ha⟩) ?_
      · rintro O (rfl | rfl)
        · exact hZo
        · exact hco
      · intro u
        rcases hp u with h | h
        · exact ⟨Z, .inl rfl, h⟩
        · exact ⟨c, .inr rfl, h⟩
      · rintro y d g r O (rfl | rfl) hr h
        · have hyO : y ∈ O := by simpa using hr 0
          have hdO : d ∈ O := by simpa using hr 1
          rcases h with ⟨-, hg⟩ | ⟨hyc, x, hx, g₁, g₂, h₁, h₂, rfl⟩
          · exact .inl ⟨hdO, hg.trans (Arw.of_path r hr)⟩
          · exact .inl ⟨hdO, (hclose hx ⟨hyO, hyc⟩ h₁ h₂).trans (Arw.of_path r hr)⟩
        · have hyO : y ∈ O := by simpa using hr 0
          have hdO : d ∈ O := by simpa using hr 1
          rcases h with ⟨hyZ, hg⟩ | ⟨-, x, hx, g₁, g₂, h₁, h₂, rfl⟩
          · exact .inr ⟨hdO, y, ⟨hyZ, hyO⟩, g, Cl.mk r, hg, Arw.of_path r hr, rfl⟩
          · refine .inr ⟨hdO, x, hx, g₁, g₂.trans (Cl.mk r), h₁, h₂.trans (Arw.of_path r hr), ?_⟩
            rw [cl_assoc]
    rcases hQ with ⟨-, h⟩ | ⟨hec, x, hx, g₁, g₂, h₁, h₂, h⟩
    · exact h
    · rw [h]
      exact hclose hx ⟨he, hec⟩ h₁ h₂
  intro a b p q hp hq
  by_cases hne : (Z ∩ c).Nonempty
  · obtain ⟨w, hw⟩ := hne
    have hstart : ∀ x ∈ Z ∪ c, ∃ (z : T) (α : Cl z x), z ∈ Z ∧ Arw (Z ∪ c) α := fun x hx => by
      by_cases hxZ : x ∈ Z
      · exact ⟨x, Cl.rf x, hxZ, arw_refl (.inl hxZ)⟩
      · have hj := hcp.joinedIn w hw.2 x (hx.resolve_left hxZ)
        exact ⟨w, Cl.mk hj.somePath, hw.1, hj.somePath, fun u => .inr (hj.somePath_mem u), rfl⟩
    obtain ⟨z₀, α, hz₀, hα⟩ := hstart a (by simpa using hp 0)
    obtain ⟨z₁, β, hz₁, hβ⟩ := hstart b (by simpa using hp 1)
    have hk : ∀ f : Cl z₀ z₁, Arw (Z ∪ c) f → Arw Z f := by
      rintro _ ⟨r, hr, rfl⟩
      exact key _ _ r hr hz₀ hz₁
    have e : α.trans ((Cl.mk p).trans β.symm) = α.trans ((Cl.mk q).trans β.symm) :=
      hZ.eq (hk _ (hα.trans ((Arw.of_path p hp).trans hβ.symm))) (hk _ (hα.trans
        ((Arw.of_path q hq).trans hβ.symm)))
    exact Path.Homotopic.Quotient.eq.mp (cl_cancel α β.symm e)
  · have hd : Z ∩ c ⊆ ∅ := fun x hx => hne ⟨x, hx⟩
    have hdisj : Disjoint Z c := disjoint_iff_inter_eq_empty.mpr (subset_empty_iff.mp hd)
    have hr : ∀ r : Path a b, (∀ u, r u ∈ Z ∪ c) → (a ∈ Z → ∀ u, r u ∈ Z) ∧ (a ∈ c → ∀ u, r u ∈ c)
      := fun r hr => by
      have hpre : IsPreconnected (range r) := isPreconnected_range r.continuous
      have hsub : range r ⊆ Z ∪ c := by
        rintro _ ⟨u, rfl⟩
        exact hr u
      have h0 : a ∈ range r := ⟨0, by simp⟩
      refine ⟨fun ha u => ?_, fun ha u => ?_⟩
      · exact hpre.subset_left_of_subset_union hZo hco hdisj hsub ⟨a, h0, ha⟩ ⟨u, rfl⟩
      · exact hpre.subset_right_of_subset_union hZo hco hdisj hsub ⟨a, h0, ha⟩ ⟨u, rfl⟩
    rcases (by simpa using hp 0 : a ∈ Z ∪ c) with ha | ha
    · exact hZ p q ((hr p hp).1 ha) ((hr q hq).1 ha)
    · exact hc p q ((hr p hp).2 ha) ((hr q hq).2 ha)

/-- A finite disjoint family of cells can be added to a flat open set. -/
theorem flat_union_finite {ι : Type*} {I : Set ι} (hI : I.Finite) {Z : Set T} (c : ι → Set T)
  (hZo : IsOpen Z) (hZ : Flat Z)
    (hco : ∀ i ∈ I, IsOpen (c i)) (hc : ∀ i ∈ I, Flat (c i)) (hcp : ∀ i ∈ I, IsPathConnected (c i))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (c i) (c j))
    (hpair : ∀ i ∈ I, ∀ x ∈ Z ∩ c i, ∀ y ∈ Z ∩ c i, ∃ f : Cl x y, Arw Z f ∧ Arw (c i) f) : Flat
      (Z ∪ ⋃ i ∈ I, c i) := by
  classical
  induction I, hI using Set.Finite.induction_on with
  | empty => simpa using hZ
  | @insert a I ha hI ih =>
    have hI' := ih (fun i hi => hco i (.inr hi)) (fun i hi => hc i (.inr hi)) (fun i hi => hcp i
      (.inr hi))
      (fun i hi j hj => hdisj i (.inr hi) j (.inr hj)) (fun i hi => hpair i (.inr hi))
    have e : Z ∪ ⋃ i ∈ insert a I, c i = (Z ∪ ⋃ i ∈ I, c i) ∪ c a := by
      rw [biUnion_insert]
      ext x
      simp only [mem_union]
      tauto
    rw [e]
    have hmeet : ∀ x ∈ (Z ∪ ⋃ i ∈ I, c i) ∩ c a, x ∈ Z := fun x hx => by
      rcases hx.1 with h | h
      · exact h
      · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp h
        have hne : a ≠ i := fun h' => ha (h' ▸ hi)
        exact absurd hxi (disjoint_left.mp (hdisj a (.inl rfl) i (.inr hi) hne) hx.2)
    refine flat_union_of_common (hZo.union (isOpen_biUnion fun i hi => hco i (.inr hi))) (hco a
      (.inl rfl)) hI' (hc a (.inl rfl))
      (hcp a (.inl rfl)) fun x hx y hy => ?_
    obtain ⟨f, h₁, h₂⟩ := hpair a (.inl rfl) x ⟨hmeet x hx, hx.2⟩ y ⟨hmeet y hy, hy.2⟩
    exact ⟨f, h₁.mono subset_union_left, h₂⟩

/-- The set `N` looks like a corner of the disc `Δ` at the point `s`. -/
structure IsCone (Δ : Set T) (s : T) (N : Set T) : Prop where
  to_point : ∀ x ∈ N ∩ Δ, ∃ f : Cl s x, Arw (N ∩ Δ) f
  in_cell : ∀ x ∈ (N ∩ Δ) ∩ discInt Δ, ∀ y ∈ (N ∩ Δ) ∩ discInt Δ, ∃ f : Cl x y, Arw
    ((N ∩ Δ) ∩ discInt Δ) f

theorem IsCone.congr {Δ N N' : Set T} {s : T} (h : IsCone Δ s N) (e : N ∩ Δ
  = N' ∩ Δ) : IsCone Δ s N' := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · simp only [← e] at hx ⊢
    exact h.to_point x hx
  · simp only [← e] at hx hy ⊢
    exact h.in_cell x hx y hy

/-- Each point on the boundary of a closed disc has small neighbourhoods that are corners of the
disc. -/
theorem exists_cone {Δ W : Set T} {s : T} (hΔ : IsClosedDisc Δ) (hs : s ∈ discBd Δ) (hW : IsOpen W)
  (hsW : s ∈ W) :
    ∃ N, IsOpen N ∧ s ∈ N ∧ N ⊆ W ∧ IsCone Δ s N := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  have hsΔ : s ∈ Δ := Surface.discBd_subset _ hs
  have hp : h s ∈ sphere (0 : ℂ) 1 := by
    rw [← c.bd]
    exact mem_image_of_mem _ hs
  have hpB : h s ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hp
  have hgp : g (h s) = s := c.gh hsΔ
  obtain ⟨Y, hY, hYe⟩ := continuousOn_iff'.mp c.gc W hW
  have hpY : h s ∈ Y := by
    have : h s ∈ g ⁻¹' W ∩ closedBall 0 1 := ⟨by change g _ ∈ W; rwa [hgp], hpB⟩
    rw [hYe] at this
    exact this.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hY _ hpY
  obtain ⟨O', hO', hOe⟩ := continuousOn_iff'.mp c.hc _ (isOpen_ball (x := h s) (ε := ε))
  have hN : ∀ x, x ∈ (O' ∩ W) ∩ Δ ↔ x ∈ Δ ∧ h x ∈ ball (h s) ε := fun x => by
    constructor
    · rintro ⟨⟨h₁, -⟩, h₃⟩
      have : x ∈ O' ∩ Δ := ⟨h₁, h₃⟩
      rw [← hOe] at this
      exact ⟨h₃, this.1⟩
    · rintro ⟨h₁, h₂⟩
      have h₃ : x ∈ h ⁻¹' ball (h s) ε ∩ Δ := ⟨h₂, h₁⟩
      rw [hOe] at h₃
      have h₄ : h x ∈ Y ∩ closedBall 0 1 := ⟨hball h₂, c.hm h₁⟩
      rw [← hYe] at h₄
      have h₅ : g (h x) ∈ W := h₄.1
      rw [c.gh h₁] at h₅
      exact ⟨⟨h₃.1, h₅⟩, h₁⟩
  have hpath : ∀ K : Set ℂ, K ⊆ closedBall 0 1 → Convex ℝ K → ∀ u ∈ K, ∀ v ∈ K, ∃ p : Path (g u)
    (g v), ∀ t, p t ∈ g '' K := by
    intro K hK hconv u hu v hv
    have hj := (hconv.isPathConnected ⟨u, hu⟩).joinedIn u hu v hv
    refine ⟨⟨⟨fun t => g (hj.somePath t), c.gc.comp_continuous hj.somePath.continuous fun t => hK
      (hj.somePath_mem t)⟩, by simp, by simp⟩, fun t => ?_⟩
    exact ⟨_, hj.somePath_mem t, rfl⟩
  have himg : ∀ K : Set ℂ, K ⊆ closedBall 0 1 → K ⊆ ball (h s) ε → g '' K ⊆ (O' ∩ W) ∩ Δ := by
    rintro K hK hb _ ⟨z, hz, rfl⟩
    refine (hN _).mpr ⟨c.gm (hK hz), ?_⟩
    rw [c.hg (hK hz)]
    exact hb hz
  refine ⟨O' ∩ W, hO'.inter hW, ⟨?_, hsW⟩, inter_subset_right, ?_, ?_⟩
  · have : s ∈ h ⁻¹' ball (h s) ε ∩ Δ := ⟨mem_ball_self hε, hsΔ⟩
    rw [hOe] at this
    exact this.1
  · intro x hx
    obtain ⟨hxΔ, hxb⟩ := (hN x).mp hx
    obtain ⟨p, hp'⟩ := hpath (closedBall 0 1 ∩ ball (h s) ε) inter_subset_left
      ((convex_closedBall _ _).inter (convex_ball _ _)) _
      ⟨hpB, mem_ball_self hε⟩ _ ⟨c.hm hxΔ, hxb⟩
    refine ⟨_, p.cast hgp.symm (c.gh hxΔ).symm, fun t => ?_, rfl⟩
    exact himg _ inter_subset_left inter_subset_right (hp' t)
  · intro x hx y hy
    have hk : ∀ w ∈ ((O' ∩ W) ∩ Δ) ∩ discInt Δ, h w ∈ ball (0 : ℂ) 1 ∩ ball (h s) ε := fun w hw
      => by
      obtain ⟨hwΔ, hwb⟩ := (hN w).mp hw.1
      have h₂ := hw.2
      rw [c.discInt_eq] at h₂
      obtain ⟨z, hz, rfl⟩ := h₂
      refine ⟨?_, hwb⟩
      rwa [c.hg (ball_subset_closedBall hz)]
    have hsub : ball (0 : ℂ) 1 ∩ ball (h s) ε ⊆ closedBall 0 1 := inter_subset_left.trans
      ball_subset_closedBall
    obtain ⟨p, hp'⟩ := hpath _ hsub ((convex_ball _ _).inter (convex_ball _ _)) _ (hk x hx) _
      (hk y hy)
    refine ⟨_, p.cast (c.gh hx.1.2).symm (c.gh hy.1.2).symm, fun t => ?_, rfl⟩
    refine ⟨himg _ hsub inter_subset_right (hp' t), ?_⟩
    change p t ∈ discInt Δ
    rw [c.discInt_eq]
    obtain ⟨z, hz, hzt⟩ := hp' t
    exact ⟨z, hz.1, hzt⟩

/-- Points of `Z` in a cell have a common class, if `Z` meets the cell only in corners and two
corners are joined by a class in
`Z` and in the closed cell. -/
theorem cell_pair {Z Δ : Set T} {S₀ : Set T} {D : T → Set T} (hΔ : IsClosedDisc Δ)
  (hcp : IsPathConnected (discInt Δ))
    (hDZ : ∀ s ∈ S₀, D s ⊆ Z) (hcone : ∀ s ∈ S₀, s ∈ Δ → IsCone Δ s (D s))
      (hmeet : ∀ x ∈ Z ∩ discInt Δ, ∃ s ∈ S₀, s ∈ Δ ∧ x ∈ D s)
    (hg : ∀ a ∈ S₀, ∀ b ∈ S₀, a ∈ Δ → b ∈ Δ → a ≠ b → ∃ g : Cl a b, Arw Z g ∧ Arw Δ g) :
    ∀ x ∈ Z ∩ discInt Δ, ∀ y ∈ Z ∩ discInt Δ, ∃ f : Cl x y, Arw Z f ∧ Arw (discInt Δ) f := by
  intro x hx y hy
  have hfl : Flat Δ := IsSimplyConnectedSet.flat (IsClosedDisc.isSimplyConnectedSet hΔ)
  have hI : discInt Δ ⊆ Δ := sdiff_subset
  obtain ⟨a, ha, haΔ, hxa⟩ := hmeet x hx
  obtain ⟨b, hb, hbΔ, hyb⟩ := hmeet y hy
  by_cases hab : a = b
  · subst hab
    obtain ⟨f, hf⟩ := (hcone a ha haΔ).in_cell x ⟨⟨hxa, hI hx.2⟩, hx.2⟩ y ⟨⟨hyb, hI hy.2⟩, hy.2⟩
    exact ⟨f, hf.mono fun z hz => hDZ a ha hz.1.1, hf.mono fun z hz => hz.2⟩
  · obtain ⟨g, hgZ, hgΔ⟩ := hg a ha b hb haΔ hbΔ hab
    obtain ⟨f₁, hf₁⟩ := (hcone a ha haΔ).to_point x ⟨hxa, hI hx.2⟩
    obtain ⟨f₂, hf₂⟩ := (hcone b hb hbΔ).to_point y ⟨hyb, hI hy.2⟩
    have hj := hcp.joinedIn x hx.2 y hy.2
    have hc : Arw (discInt Δ) (Cl.mk hj.somePath) := Arw.of_path _ hj.somePath_mem
    refine ⟨Cl.mk hj.somePath, ?_, hc⟩
    have e : Cl.mk hj.somePath = f₁.symm.trans (g.trans f₂) :=
      hfl.eq (hc.mono hI) ((hf₁.mono inter_subset_right).symm.trans (hgΔ.trans
        (hf₂.mono inter_subset_right)))
    rw [e]
    exact (hf₁.mono fun z hz => hDZ a ha hz.1).symm.trans (hgZ.trans (hf₂.mono fun z hz
      => hDZ b hb hz.1))

/-- **Adding cells to a flat set.** Let `R` be an open set that misses the cells of a finite family,
and let `S₀` be a set of corners.
Suppose `R`, with a small open set around each point of `S₀`, is flat. Suppose that two corners of a
cell are joined by a class that
has a path in `R` and a path in the closed cell. Then after we shrink the small open sets, the cells
can be added. -/
theorem exists_flat_with_cells (hT : IsClosedSurface T) {𝒟 : Set (Set T)} (h𝒟 : 𝒟.Finite)
  (hd : ∀ Δ ∈ 𝒟, IsClosedDisc Δ) {V₀ : Set T}
    (hV₀ : V₀.Finite) (hmeet : ∀ Δ ∈ 𝒟, ∀ Δ' ∈ 𝒟, Δ ≠ Δ' → Δ ∩ Δ' ⊆ V₀)
    (hint : ∀ Δ ∈ 𝒟, ∀ Δ' ∈ 𝒟, Δ ≠ Δ' → Disjoint (discInt Δ) (discInt Δ')) {S₀ : Set T}
    (hbd : ∀ Δ ∈ 𝒟, ∀ s ∈ S₀, s ∈ Δ → s ∈ discBd Δ) {R : Set T} (hR : IsOpen R)
      (hRc : ∀ Δ ∈ 𝒟, Disjoint R (discInt Δ))
    {D : T → Set T} (hDo : ∀ s ∈ S₀, IsOpen (D s)) (hsD : ∀ s ∈ S₀, s ∈ D s) (hfl : Flat
      (R ∪ ⋃ s ∈ S₀, D s))
    (hg : ∀ Δ ∈ 𝒟, ∀ a ∈ S₀, ∀ b ∈ S₀, a ∈ Δ → b ∈ Δ → a ≠ b → ∃ g : Cl a b, Arw (R ∪ {a, b}) g
      ∧ Arw Δ g) :
    ∃ D' : T → Set T, (∀ s ∈ S₀, IsOpen (D' s)) ∧ (∀ s ∈ S₀, s ∈ D' s) ∧
      Flat ((R ∪ ⋃ s ∈ S₀, D' s) ∪ ⋃ Δ ∈ 𝒟, discInt Δ) := by
  classical
  have : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have hcl : ∀ Δ ∈ 𝒟, IsClosed Δ := fun Δ hΔ => (IsClosedDisc.isCompact (hd Δ hΔ)).isClosed
  let G : T → Set T := fun s => D s \ ((V₀ \ {s}) ∪ ⋃ Δ ∈ {Δ ∈ 𝒟 | s ∉ Δ}, Δ)
  have hGo : ∀ s ∈ S₀, IsOpen (G s) := fun s hs => (hDo s hs).sdiff
    ((hV₀.subset sdiff_subset).isClosed.union ((h𝒟.subset (sep_subset _ _)).isClosed_biUnion fun Δ
      hΔ => hcl Δ hΔ.1))
  have hsG : ∀ s ∈ S₀, s ∈ G s := fun s hs => ⟨hsD s hs, by
    rintro (h | h)
    · exact h.2 rfl
    · obtain ⟨Δ, hΔ, hsΔ⟩ := mem_iUnion₂.mp h
      exact hΔ.2 hsΔ⟩
  have hN : ∀ Δ ∈ 𝒟, ∀ s ∈ S₀, s ∈ Δ → ∃ N, IsOpen N ∧ s ∈ N ∧ N ⊆ G s ∧ IsCone Δ s N
    := fun Δ hΔ s hs hsΔ =>
    exists_cone (hd Δ hΔ) (hbd Δ hΔ s hs hsΔ) (hGo s hs) (hsG s hs)
  choose! N hNo hsN hNG hNc using hN
  let D' : T → Set T := fun s => G s \ ⋃ Δ ∈ {Δ ∈ 𝒟 | s ∈ Δ}, (Δ \ N Δ s)
  have hD'o : ∀ s ∈ S₀, IsOpen (D' s) := fun s hs => (hGo s hs).sdiff
    ((h𝒟.subset (sep_subset _ _)).isClosed_biUnion fun Δ hΔ => (hcl Δ hΔ.1).sdiff
      (hNo Δ hΔ.1 s hs hΔ.2))
  have hsD' : ∀ s ∈ S₀, s ∈ D' s := fun s hs => ⟨hsG s hs, fun h => by
    obtain ⟨Δ, hΔ, hsΔ⟩ := mem_iUnion₂.mp h
    exact hsΔ.2 (hsN Δ hΔ.1 s hs hΔ.2)⟩
  have hD'D : ∀ s ∈ S₀, D' s ⊆ D s := fun s _ x hx => hx.1.1
  have hcone : ∀ s ∈ S₀, ∀ Δ ∈ 𝒟, s ∈ Δ → IsCone Δ s (D' s) := fun s hs Δ hΔ hsΔ => by
    refine (hNc Δ hΔ s hs hsΔ).congr (Subset.antisymm ?_ ?_)
    · rintro x ⟨hxN, hxΔ⟩
      refine ⟨⟨hNG Δ hΔ s hs hsΔ hxN, fun h => ?_⟩, hxΔ⟩
      obtain ⟨Δ', hΔ', hxΔ'⟩ := mem_iUnion₂.mp h
      by_cases he : Δ = Δ'
      · subst he
        exact hxΔ'.2 hxN
      · have hxV : x ∈ V₀ := hmeet Δ hΔ Δ' hΔ'.1 he ⟨hxΔ, hxΔ'.1⟩
        have hxs : x = s := by
          by_contra hne
          exact (hNG Δ hΔ s hs hsΔ hxN).2 (.inl ⟨hxV, hne⟩)
        subst hxs
        exact hxΔ'.2 (hsN Δ' hΔ'.1 x hs hΔ'.2)
    · rintro x ⟨hx, hxΔ⟩
      refine ⟨?_, hxΔ⟩
      by_contra hn
      exact hx.2 (mem_iUnion₂.mpr ⟨Δ, ⟨hΔ, hsΔ⟩, hxΔ, hn⟩)
  have hZo : IsOpen (R ∪ ⋃ s ∈ S₀, D' s) := hR.union (isOpen_biUnion hD'o)
  have hZ : Flat (R ∪ ⋃ s ∈ S₀, D' s) := hfl.mono (union_subset_union_right _
    (biUnion_mono Subset.rfl hD'D))
  have hsub : ∀ s ∈ S₀, D' s ⊆ R ∪ ⋃ s ∈ S₀, D' s := fun s hs x hx => .inr
    (mem_iUnion₂.mpr ⟨s, hs, hx⟩)
  refine ⟨D', hD'o, hsD', flat_union_finite h𝒟 discInt hZo hZ (fun Δ hΔ =>
    (hd Δ hΔ).isOpen_discInt hman)
    (fun Δ hΔ => (IsSimplyConnectedSet.flat (IsClosedDisc.isSimplyConnectedSet
      (hd Δ hΔ))).mono sdiff_subset)
    (fun Δ hΔ => ?_) hint fun Δ hΔ => ?_⟩
  · obtain ⟨h, g, c⟩ := (hd Δ hΔ).exists_isChart
    rw [c.discInt_eq]
    exact ((convex_ball (0 : ℂ) 1).isPathConnected ⟨0, by simp⟩).image'
      (c.gc.mono ball_subset_closedBall)
  · refine cell_pair (D := D') (S₀ := S₀) (hd Δ hΔ) ?_ hsub (fun s hs hsΔ
    => hcone s hs Δ hΔ hsΔ) ?_ ?_
    · obtain ⟨h, g, c⟩ := (hd Δ hΔ).exists_isChart
      rw [c.discInt_eq]
      exact ((convex_ball (0 : ℂ) 1).isPathConnected ⟨0, by simp⟩).image'
        (c.gc.mono ball_subset_closedBall)
    · rintro x ⟨hxZ | hxZ, hxc⟩
      · exact absurd hxc (disjoint_left.mp (hRc Δ hΔ) hxZ)
      · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hxZ
        refine ⟨s, hs, ?_, hxs⟩
        by_contra hsΔ
        exact hxs.1.2 (.inr (mem_iUnion₂.mpr ⟨Δ, ⟨hΔ, hsΔ⟩, hxc.1⟩))
    · intro a ha b hb haΔ hbΔ hab
      obtain ⟨g, hgR, hgΔ⟩ := hg Δ hΔ a ha b hb haΔ hbΔ hab
      refine ⟨g, hgR.mono ?_, hgΔ⟩
      rintro x (hx | rfl | rfl)
      · exact .inl hx
      · exact hsub _ ha (hsD' _ ha)
      · exact hsub _ hb (hsD' _ hb)

end GraphMinor.GM19
