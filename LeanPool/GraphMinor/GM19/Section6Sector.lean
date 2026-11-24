/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Reroute
public import LeanPool.GraphMinor.GM19.Perimeter

/-!
# Paths that leave a vertex into a region

Let `v` be a vertex of a drawing `D` in a closed surface, and `ρ` a region of `D` that is an open
disc,
such that each `O`-arc through `v` that otherwise lies in `ρ` bounds a disc that misses `D` except
at
`v`. Then `ρ` has only one corner at `v` (`corner_unique`), and two paths from `v` to one point, off
`v`
inside `ρ`, are homotopic (`sector_homotopic`). This says that `ρ ∪ {v}` is simply connected, which
is
the fact the paper's proof of (6.7), page 342, starts from.

The proof takes the start of each path, inside the closed disc `Q` of the one sector of `ρ` at `v`.
Two
points near `v` in the open disc join inside the sector (`exists_sector_nhd`). What is left of the
paths lies in `ρ`, an open disc.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 Metric

local notation "𝕀" => unitInterval

variable {T : Type} [TopologicalSpace T]

/-- Near a boundary point of a closed disc, two points of the open disc are joined in the open disc.
-/
theorem exists_sector_nhd {Q W : Set T} (hQ : IsClosedDisc Q) {v : T} (hv : v ∈ discBd Q)
    (hW : IsOpen W) (hvW : v ∈ W) : ∃ O, IsOpen O ∧ v ∈ O ∧ O ⊆ W ∧
      ∀ a ∈ O ∩ discInt Q, ∀ b ∈ O ∩ discInt Q, ∃ p : Path a b, range p ⊆ O ∩ discInt Q := by
  obtain ⟨h, g, c⟩ := hQ.exists_isChart
  have hvQ : v ∈ Q := Surface.discBd_subset _ hv
  have hp : h v ∈ sphere (0 : ℂ) 1 := by
    rw [← c.bd]
    exact mem_image_of_mem _ hv
  have hpB : h v ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hp
  have hgp : g (h v) = v := c.gh hvQ
  obtain ⟨Y, hY, hYe⟩ := continuousOn_iff'.mp c.gc W hW
  have hpY : h v ∈ Y := by
    have : h v ∈ g ⁻¹' W ∩ closedBall 0 1 := ⟨by change g _ ∈ W; rwa [hgp], hpB⟩
    rw [hYe] at this
    exact this.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hY _ hpY
  obtain ⟨O', hO', hOe⟩ := continuousOn_iff'.mp c.hc _ (isOpen_ball (x := h v) (ε := ε))
  have hvO' : v ∈ O' := by
    have : v ∈ h ⁻¹' ball (h v) ε ∩ Q := ⟨mem_ball_self hε, hvQ⟩
    rw [hOe] at this
    exact this.1
  let A : Set ℂ := ball (h v) ε ∩ ball 0 1
  have hAc : Convex ℝ A := (convex_ball _ _).inter (convex_ball _ _)
  have hAb : A ⊆ closedBall 0 1 := fun _ hx => ball_subset_closedBall hx.2
  have hin : ∀ a ∈ (O' ∩ W) ∩ discInt Q, h a ∈ A := by
    rintro a ⟨⟨haO, -⟩, haQ, hab⟩
    have h₁ : a ∈ h ⁻¹' ball (h v) ε ∩ Q := by
      rw [hOe]
      exact ⟨haO, haQ⟩
    refine ⟨h₁.1, ?_⟩
    have h₂ := c.hm haQ
    rw [mem_closedBall, ← not_lt] at h₂
    rw [mem_ball]
    refine lt_of_le_of_ne (not_lt.mp h₂) fun h₃ => hab ?_
    have h₄ : h a ∈ h '' discBd Q := by
      rw [c.bd]
      exact h₃
    obtain ⟨z, hz, hza⟩ := h₄
    have := congrArg g hza
    rw [c.gh (Surface.discBd_subset _ hz), c.gh haQ] at this
    exact this ▸ hz
  have hout : ∀ y ∈ A, g y ∈ (O' ∩ W) ∩ discInt Q := by
    intro y hy
    have hyb := hAb hy
    have hyQ := c.gm hyb
    have hhy : h (g y) = y := c.hg hyb
    refine ⟨⟨?_, ?_⟩, hyQ, fun hb => ?_⟩
    · have : g y ∈ h ⁻¹' ball (h v) ε ∩ Q := ⟨show h (g y) ∈ ball (h v) ε by rw [hhy]; exact hy.1,
      hyQ⟩
      rw [hOe] at this
      exact this.1
    · have : y ∈ g ⁻¹' W ∩ closedBall 0 1 := by
        rw [hYe]
        exact ⟨hball hy.1, hyb⟩
      exact this.1
    · have : h (g y) ∈ h '' discBd Q := mem_image_of_mem _ hb
      rw [c.bd, hhy] at this
      have h₁ := hy.2
      rw [mem_ball] at h₁
      rw [mem_sphere] at this
      exact h₁.ne this
  refine ⟨O' ∩ W, hO'.inter hW, ⟨hvO', hvW⟩, inter_subset_right, fun a ha b hb => ?_⟩
  have hja := hin a ha
  have hjb := hin b hb
  have hJ : JoinedIn A (h a) (h b) := (hAc.isPathConnected ⟨_, hja⟩).joinedIn _ hja _ hjb
  have hσ : ∀ t, hJ.somePath t ∈ closedBall (0 : ℂ) 1 := fun t => hAb (hJ.somePath_mem t)
  refine ⟨⟨⟨fun t => g (hJ.somePath t), c.gc.comp_continuous hJ.somePath.continuous hσ⟩, ?_, ?_⟩,
    ?_⟩
  · simpa using c.gh ha.2.1
  · simpa using c.gh hb.2.1
  · rintro _ ⟨t, rfl⟩
    exact hout _ (hJ.somePath_mem t)

/-- A continuous map from the interval stays in an open set for a while. -/
theorem exists_time {f : 𝕀 → T} (hf : Continuous f) {O : Set T} (hO : IsOpen O) (h0 : f 0 ∈ O) :
    ∃ t₀ : 𝕀, 0 < t₀ ∧ ∀ s ≤ t₀, f s ∈ O := by
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp (hO.preimage hf) 0 h0
  have hpos : 0 < min 1 (ε / 2) := lt_min one_pos (by positivity)
  refine ⟨⟨min 1 (ε / 2), hpos.le, min_le_left _ _⟩, hpos, fun s hs => hb ?_⟩
  have hs' : s.1 ≤ ε / 2 := le_trans hs (min_le_right _ _)
  rw [mem_ball, Subtype.dist_eq]
  have h₁ := s.2.1
  change dist s.1 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h₁]
  linarith

theorem path_split_aux (f : C(𝕀, T)) {u v : T} (h0 : f 0 = u) (h1 : f 1 = v) (t : 𝕀) :
    ∃ (g₁ : Path u (f t)) (g₂ : Path (f t) v), (⟨f, h0, h1⟩ : Path u v).Homotopic (g₁.trans g₂) ∧
      (∀ s, ∃ s' ≤ t, g₁ s = f s' ∧ (0 < s → 0 < t → 0 < s')) ∧
      (∀ s, ∃ s', t ≤ s' ∧ g₂ s = f s' ∧ (s < 1 → t < 1 → s' < 1)) := by
  subst h0 h1
  refine ⟨subP f 0 t, subP f t 1, ?_, fun s => ⟨seg 0 t s, ?_, rfl, ?_⟩, fun s => ⟨seg t 1 s, ?_,
    rfl, ?_⟩⟩
  · have e : (⟨f, rfl, rfl⟩ : Path (f 0) (f 1)) = subP f 0 1 := by
      ext x
      change f x = f (seg 0 1 x)
      congr 1
      ext
      simp [seg]
    rw [e]
    exact subP_trans f 0 t 1
  · change ((1 - s.1) * (0 : 𝕀).1 + s.1 * t.1) ≤ t.1
    have := s.2.2
    have := t.2.1
    simp only [Icc.coe_zero, mul_zero, zero_add]
    nlinarith
  · intro h₁ h₂
    change 0 < ((1 - s.1) * (0 : 𝕀).1 + s.1 * t.1)
    have h₁' : 0 < s.1 := h₁
    have h₂' : 0 < t.1 := h₂
    simp only [Icc.coe_zero, mul_zero, zero_add]
    positivity
  · change t.1 ≤ ((1 - s.1) * t.1 + s.1 * (1 : 𝕀).1)
    have := s.2.1
    have := t.2.2
    simp only [Icc.coe_one, mul_one]
    nlinarith
  · intro h₁ h₂
    change ((1 - s.1) * t.1 + s.1 * (1 : 𝕀).1) < 1
    have h₁' : s.1 < 1 := h₁
    have h₂' : t.1 < 1 := h₂
    simp only [Icc.coe_one, mul_one]
    nlinarith

/-- A path is the product of its parts before and after a time. -/
theorem path_split {u v : T} (g : Path u v) (t : 𝕀) :
    ∃ (g₁ : Path u (g t)) (g₂ : Path (g t) v), g.Homotopic (g₁.trans g₂) ∧
      (∀ s, ∃ s' ≤ t, g₁ s = g s' ∧ (0 < s → 0 < t → 0 < s')) ∧
      (∀ s, ∃ s', t ≤ s' ∧ g₂ s = g s' ∧ (s < 1 → t < 1 → s' < 1)) :=
  path_split_aux g.toContinuousMap g.source g.target t

theorem trans_mem_of_pos {a b c : T} {p : Path a b} {q : Path b c} {ρ : Set T}
    (hp : ∀ t, 0 < t → p t ∈ ρ) (hq : ∀ t, q t ∈ ρ) : ∀ t, 0 < t → p.trans q t ∈ ρ := by
  intro t ht
  rw [Path.trans_apply]
  split_ifs with h
  · refine hp _ ?_
    have ht' : 0 < t.1 := ht
    change 0 < 2 * t.1
    positivity
  · exact hq _

/-- Two paths in an open disc with the same ends are homotopic. -/
theorem paths_homotopic_in_open {Λ : Set T} (hΛ : IsOpenDisc Λ) {a b : T} (p q : Path a b)
    (hp : range p ⊆ Λ) (hq : range q ⊆ Λ) : p.Homotopic q := by
  obtain ⟨-, ⟨e⟩⟩ := id hΛ
  have hc : ContractibleSpace OpenUnitDisc :=
    (convex_ball (0 : EuclideanPlane) 1).contractibleSpace ⟨0, by simp⟩
  have hc' : ContractibleSpace Λ := e.symm.contractibleSpace
  have ha : a ∈ Λ := hp ⟨0, by simp⟩
  have hb : b ∈ Λ := hp ⟨1, by simp⟩
  let p' : Path (⟨a, ha⟩ : Λ) ⟨b, hb⟩ := ⟨⟨fun t => ⟨p t, hp ⟨t, rfl⟩⟩, by fun_prop⟩, by simp, by
    simp⟩
  let q' : Path (⟨a, ha⟩ : Λ) ⟨b, hb⟩ := ⟨⟨fun t => ⟨q t, hq ⟨t, rfl⟩⟩, by fun_prop⟩, by simp, by
    simp⟩
  have h : p'.Homotopic q' := SimplyConnectedSpace.paths_homotopic _ _
  have h2 := h.map ⟨Subtype.val, continuous_subtype_val⟩
  have e1 : p'.map continuous_subtype_val = p := by
    ext t
    rfl
  have e2 : q'.map continuous_subtype_val = q := by
    ext t
    rfl
  have e3 := h2
  simp only [ContinuousMap.coe_mk] at e3
  rwa [e1, e2] at e3

/-- **Two paths into a region from a vertex.** See the module docstring. -/
theorem sector_homotopic (hT : IsClosedSurface T) (D : Drawing T) {γ : Set T → 𝕀
  → T}
    (hγ : EdgePar D γ) {v : T} (hv : v ∈ D.V) (h2 : 2 ≤ Nat.card (halfEdges D γ v)) {ρ : Set T}
    (hρ : ρ ∈ D.R) (hρd : IsOpenDisc ρ)
    (hpinch : ∀ F : Set T, IsOArc F → v ∈ F → v ∈ closure (F \ {v}) → F \ {v} ⊆ ρ →
      ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ∩ D.U ⊆ {v}) {x : T} (α β : Path v x)
    (hα : ∀ t, 0 < t → α t ∈ ρ) (hβ : ∀ t, 0 < t → β t ∈ ρ) : α.Homotopic β := by
  classical
  have : T2Space T := hT.2.1
  obtain ⟨next, ρs, P, W, Q, τ, hsec, hcov, hPQ⟩ := exists_sectors' hT D hγ hv h2
  have hvρ : v ∈ closure ρ := by
    rw [_root_.mem_closure_iff]
    intro O hO hvO
    obtain ⟨t, ht, hs⟩ := exists_time α.continuous hO (by simpa using hvO)
    exact ⟨α t, hs t le_rfl, hα t ht⟩
  obtain ⟨k, hk⟩ := hsec.corners.all ρ hρ hvρ
  have huniq : ∀ j, ρs j = ρ → j = k := fun j hj =>
    (corner_unique hT hv hsec hcov hPQ (hk.symm.trans hj.symm) (fun F hF hvF hcl hsub =>
      hpinch F hF hvF hcl (hk ▸ hsub))).symm
  have hρU : Disjoint ρ D.U := disjoint_left.mpr fun y hy => region_subset hρ hy
  have hWρ : W ∩ ρ ⊆ P k := by
    rintro y ⟨hyW, hyρ⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov ⟨hyW, disjoint_left.mp hρU hyρ⟩)
    have hjρ : ρs j = ρ := region_eq_of_mem (hsec.corners.region j) hρ (hsec.sub j hj) hyρ
    rwa [huniq j hjρ] at hj
  obtain ⟨O, hO, hvO, hOW, hOp⟩ := exists_sector_nhd (hsec.disc k) (hsec.bd k) hsec.isOpen hsec.mem
  have hin : ∀ y ∈ O, y ∈ ρ → y ∈ O ∩ discInt (Q k) := fun y hyO hyρ =>
    ⟨hyO, hPQ k (hWρ ⟨hOW hyO, hyρ⟩), fun hb =>
      disjoint_left.mp hρU hyρ (hsec.bdU k ⟨hOW hyO, hb⟩)⟩
  have hsecρ : O ∩ discInt (Q k) ⊆ ρ := by
    rintro y ⟨hyO, hyQ⟩
    have := hsec.sub k (hsec.inside k ⟨⟨hOW hyO, hyQ.1⟩, hyQ.2⟩)
    rwa [← hk] at this
  obtain ⟨t₀, ht₀, hsα⟩ := exists_time α.continuous hO (by simpa using hvO)
  obtain ⟨t₁, ht₁, hsβ⟩ := exists_time β.continuous hO (by simpa using hvO)
  obtain ⟨α₁, α₂, hα₀, hα₁, hα₂⟩ := path_split α t₀
  obtain ⟨β₁, β₂, hβ₀, hβ₁, hβ₂⟩ := path_split β t₁
  obtain ⟨δ, hδ⟩ := hOp _ (hin _ (hsα t₀ le_rfl) (hα _ ht₀)) _ (hin _ (hsβ t₁ le_rfl) (hβ _ ht₁))
  have hvQ : v ∈ Q k := Surface.discBd_subset _ (hsec.bd k)
  have hrng : ∀ {y : 𝕀 → T} {t : 𝕀}, y 0 = v → (∀ s ≤ t, y s ∈ O) → (∀ s, 0 < s → y s ∈ ρ) →
      ∀ s ≤ t, y s ∈ Q k := by
    intro y t h0 hO' hρ' s hs
    by_cases h : s = 0
    · rwa [h, h0]
    · exact (hin _ (hO' s hs) (hρ' s (unitInterval.pos_iff_ne_zero.mpr h))).2.1
  have h₁ : (α₁.trans δ).Homotopic β₁ := by
    refine paths_homotopic_in_disc (hsec.disc k) _ _ ?_ ?_
    · rw [Path.trans_range]
      refine union_subset ?_ (fun y hy => (hδ hy).2.1)
      rintro _ ⟨s, rfl⟩
      obtain ⟨s', hs', he, -⟩ := hα₁ s
      rw [he]
      exact hrng α.source hsα hα s' hs'
    · rintro _ ⟨s, rfl⟩
      obtain ⟨s', hs', he, -⟩ := hβ₁ s
      rw [he]
      exact hrng β.source hsβ hβ s' hs'
  have h₂ : α₂.Homotopic (δ.trans β₂) := by
    refine paths_homotopic_in_open hρd _ _ ?_ ?_
    · rintro _ ⟨s, rfl⟩
      obtain ⟨s', hs', he, -⟩ := hα₂ s
      rw [he]
      exact hα _ (lt_of_lt_of_le ht₀ hs')
    · rw [Path.trans_range]
      refine union_subset (fun y hy => hsecρ (hδ hy)) ?_
      rintro _ ⟨s, rfl⟩
      obtain ⟨s', hs', he, -⟩ := hβ₂ s
      rw [he]
      exact hβ _ (lt_of_lt_of_le ht₁ hs')
  exact hα₀.trans (((Path.Homotopic.refl α₁).hcomp h₂).trans
    ((Path.Homotopic.trans_assoc α₁ δ β₂).symm.trans ((h₁.hcomp (Path.Homotopic.refl β₂)).trans
      hβ₀.symm)))

end GraphMinor.GM19
