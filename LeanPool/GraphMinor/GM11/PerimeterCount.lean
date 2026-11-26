/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PerimeterWalk
public import LeanPool.GraphMinor.GM11.Cylinder

/-!
# How often a perimeter walk uses an edge

`perimeterCount Γ X e` is the number of sides of `e` outside `X`, for an edge `e` on the frontier of
`X`, and
`0` for other edges. Each perimeter walk of `X` uses `e` at least that often (`count_le_edgeCount`),
and
`exists_perimeterWalk` gives a perimeter walk that uses it exactly that often. So `l(X)` is the sum
of these
numbers (`perimeterWalkLength_eq`). Graph Minors XI, Section 8 (page 96), says this as "its length
equals
the length of the perimeter of $\Sigma - X$".
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

section Runs

variable {Γ : Drawing S} {φ : ℝ → S}

theorem runs_start {u v : S} {W : GraphWalk Γ.toGraph u v} {a b : ℝ} (h : RunsAlongOn Γ φ a b W) :
    φ a = u := by
  cases W with
  | nil hv => exact h.2
  | cons hlink rest =>
    obtain ⟨c, -, hu, -⟩ := h
    exact hu

theorem runs_le {u v : S} (W : GraphWalk Γ.toGraph u v) :
    ∀ {a b : ℝ}, RunsAlongOn Γ φ a b W → a ≤ b := by
  induction W with
  | nil hv =>
    rintro a b ⟨rfl, -⟩
    exact le_rfl
  | @cons x y w e hlink rest ih =>
    rintro a b ⟨c, hac, -, -, -, hrest⟩
    exact hac.le.trans (ih hrest)

/-- A point of a walk that is not a vertex lies in an edge of the walk. -/
theorem runs_mem {u v : S} (W : GraphWalk Γ.toGraph u v) :
    ∀ {a b : ℝ}, RunsAlongOn Γ φ a b W → ∀ t ∈ Icc a b, φ t ∉ Γ.V → ∃ e ∈ W.edges, φ t ∈ e := by
  induction W with
  | nil hv =>
    rintro a b ⟨rfl, hu⟩ t ⟨h₁, h₂⟩ ht
    obtain rfl : t = a := le_antisymm h₂ h₁
    exact (ht (hu ▸ hv)).elim
  | @cons x y w e hlink rest ih =>
    rintro a b ⟨c, hac, hu, -, him, hrest⟩ t ht hV
    rcases lt_or_ge t c with htc | htc
    · rcases eq_or_lt_of_le ht.1 with rfl | hat
      · exact (hV (hu ▸ hlink.2.1)).elim
      · exact ⟨e, List.mem_cons_self, him ▸ mem_image_of_mem φ ⟨hat, htc⟩⟩
    · obtain ⟨e', he', hm⟩ := ih hrest t ⟨htc, ht.2⟩ hV
      exact ⟨e', List.mem_cons_of_mem _ he', hm⟩

open Classical in
/-- If a walk uses an edge at most once, it passes each point of the edge at most once. -/
theorem runs_unique {u v : S} (W : GraphWalk Γ.toGraph u v) {e : Set S} (he : e ∈ Γ.E) :
    ∀ {a b : ℝ}, RunsAlongOn Γ φ a b W → edgeCount W.edges e ≤ 1 → ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      φ s ∈ e → φ s = φ t → s = t := by
  have hoffV : ∀ {t}, φ t ∈ e → φ t ∉ Γ.V := fun h => (he.2.1 h).2
  induction W with
  | nil hv =>
    rintro a b ⟨rfl, -⟩ - s ⟨h₁, h₂⟩ t ⟨h₃, h₄⟩ - -
    exact (le_antisymm h₂ h₁).trans (le_antisymm h₄ h₃).symm
  | @cons x y w e' hlink rest ih =>
    rintro a b ⟨c, hac, hu, hi, him, hrest⟩ hc s hs t ht hse hst
    have hte : φ t ∈ e := hst ▸ hse
    have hrestV := runs_start hrest
    have he' : e' ∈ Γ.E := hlink.1
    have hin : ∀ r ∈ Icc a b, φ r ∈ e → r < c → r ∈ Ioo a c ∧ e = e' := by
      intro r hr hre hrc
      have har : a < r := by
        rcases eq_or_lt_of_le hr.1 with rfl | h
        · exact (hoffV hre (hu ▸ hlink.2.1)).elim
        · exact h
      have hm : r ∈ Ioo a c := ⟨har, hrc⟩
      exact ⟨hm, Γ.edge_eq_of_mem he he' hre (him ▸ mem_image_of_mem φ hm)⟩
    by_cases hee : e = e'
    · subst hee
      have hc0 : edgeCount rest.edges e = 0 := by
        have : edgeCount (e :: rest.edges) e = edgeCount rest.edges e + 1 := List.count_cons_self
        change edgeCount (e :: rest.edges) e ≤ 1 at hc
        omega
      have hnot : e ∉ rest.edges := fun h => by
        have : 0 < edgeCount rest.edges e := List.count_pos_iff.mpr h
        omega
      have hlt : ∀ r ∈ Icc a b, φ r ∈ e → r < c := by
        intro r hr hre
        by_contra hrc
        obtain ⟨e₂, he₂, hm⟩ := runs_mem rest hrest r ⟨not_lt.mp hrc, hr.2⟩ (hoffV hre)
        have he₂E : e₂ ∈ Γ.E := mem_E_of_mem_edges rest he₂
        exact hnot (Γ.edge_eq_of_mem he he₂E hre hm ▸ he₂)
      exact hi (hin s hs hse (hlt s hs hse)).1 (hin t ht hte (hlt t ht hte)).1 hst
    · have hge : ∀ r ∈ Icc a b, φ r ∈ e → r ∈ Icc c b := by
        intro r hr hre
        refine ⟨?_, hr.2⟩
        by_contra hrc
        exact hee (hin r hr hre (not_le.mp hrc)).2
      have hc' : edgeCount rest.edges e ≤ 1 := by
        have : edgeCount (e' :: rest.edges) e = edgeCount rest.edges e :=
          List.count_cons_of_ne (Ne.symm hee)
        change edgeCount (e' :: rest.edges) e ≤ 1 at hc
        omega
      exact ih hrest hc' s (hge s hs hse) t (hge t ht hte) hse hst

end Runs

/-- A collar of a closed set `X`, near a point `y` of an edge inside `X` with both sides of the edge
outside
`X`, cannot have just one point of its bottom at `y`. -/
theorem no_single_pass [T2Space S] (hS : IsClosedSurface S) {Γ : Drawing S}
    {X e : Set S} (he : e ∈ Γ.E) (heX : e ⊆ X) (h : C(Circle × I, S))
    (hoff : ∀ p : Circle × I, 0 < p.2 → h p ∉ X) (hbot : ∀ z, h (z, 0) ∈ X)
    (hop : IsOpen (X ∪ h '' {p | p.2 < 1})) {y : S} (hye : y ∈ e) (hyi : y ∈ interior (Xᶜ ∪ e))
    {z₀ : Circle} (hz₀ : h (z₀, 0) = y) (huniq : ∀ z, h (z, 0) = y → z = z₀) : False := by
  have hK : CompactSpace S := hS.1
  obtain ⟨W, A₁, A₂, Δ₁, Δ₂, hW, hyW, hWU, -, -, -, d₁, d₂, c₁, c₂, hΔ₁, hΔ₂, s₁, s₂, hcov, hmeet⟩
    :=
    exists_edge_sides_split hS Γ he hye
  have hyX : y ∈ X := heX hye
  let G₀ : Set S := W ∩ interior (Xᶜ ∪ e) ∩ (X ∪ h '' {p | p.2 < 1})
  have hG₀ : IsOpen G₀ := (hW.inter isOpen_interior).inter hop
  have hyG₀ : y ∈ G₀ := ⟨⟨hyW, hyi⟩, Or.inl hyX⟩
  have hO : IsOpen (h ⁻¹' G₀) := hG₀.preimage h.continuous
  have hmem₀ : ((z₀, 0) : Circle × I) ∈ h ⁻¹' G₀ := by
    change h (z₀, 0) ∈ G₀
    rw [hz₀]
    exact hyG₀
  obtain ⟨u, v, hu, hv, hzu, h0v, huv⟩ := isOpen_prod_iff.mp hO z₀ 0 hmem₀
  -- A connected open arc around `z₀`.
  obtain ⟨J, hJo, hzJ, hJu, hJc⟩ : ∃ J : Set Circle, IsOpen J ∧ z₀ ∈ J ∧ J ⊆ u ∧ IsPreconnected J
    := by
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, Circle.exp θ = z₀ := ⟨_, Circle.exp_arg z₀⟩
    have hop' : IsOpen (Circle.exp ⁻¹' u) := hu.preimage Circle.exp.continuous
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hop' θ (by simpa [hθ] using hzu)
    rw [Real.ball_eq_Ioo] at hball
    refine ⟨Circle.exp '' Ioo (θ - ε) (θ + ε), isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo,
      ⟨θ, ⟨by linarith, by linarith⟩, hθ⟩, ?_, isPreconnected_Ioo.image _
        Circle.exp.continuous.continuousOn⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hball ht
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hv 0 h0v
  let δ' : I := ⟨min (δ / 2) 1, by positivity, min_le_right _ _⟩
  have hδ' : (0 : I) < δ' := by
    change (0 : ℝ) < min (δ / 2) 1
    positivity
  have hvsub : Iio δ' ⊆ v := by
    intro t ht
    refine hball ?_
    have ht' : t.1 < min (δ / 2) 1 := ht
    rw [Metric.mem_ball, Subtype.dist_eq, Icc.coe_zero, Real.dist_eq, sub_zero, abs_of_nonneg t.2.1]
    linarith [min_le_left (δ / 2) (1 : ℝ)]
  let B : Set (Circle × I) := J ×ˢ Iio δ'
  have hBo : IsOpen B := hJo.prod isOpen_Iio
  have hBG : ∀ p ∈ B, h p ∈ G₀ := fun p hp => huv ⟨hJu hp.1, hvsub hp.2⟩
  have hCc : IsClosed (h '' Bᶜ) := (hBo.isClosed_compl.isCompact.image h.continuous).isClosed
  have hyC : y ∉ h '' Bᶜ := by
    rintro ⟨⟨z, t⟩, hp, hpe⟩
    have ht0 : t = 0 := by
      by_contra ht
      exact hoff (z, t) (unitInterval.pos_iff_ne_zero.mpr ht) (hpe ▸ hyX)
    subst ht0
    obtain rfl := huniq z hpe
    exact hp ⟨hzJ, hδ'⟩
  let T : Set S := h '' (J ×ˢ Ioo 0 δ')
  have hTc : IsPreconnected T :=
    (hJc.prod isPreconnected_Ioo).image _ h.continuous.continuousOn
  have hTW : T ⊆ W := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hBG p ⟨hp.1, hp.2.2⟩).1.1
  have hTX : ∀ x ∈ T, x ∉ X := by
    rintro _ ⟨p, hp, rfl⟩
    exact hoff p hp.2.1
  have hTU : ∀ x ∈ T, x ∉ Γ.U := fun x hx hxU => hTX x hx (heX (hWU ⟨hTW hx, hxU⟩))
  -- Each point near `y` off `X` is in `T`.
  let G : Set S := G₀ ∩ (h '' Bᶜ)ᶜ
  have hGo : IsOpen G := hG₀.inter hCc.isOpen_compl
  have hyG : y ∈ G := ⟨hyG₀, hyC⟩
  have hsub : ∀ a ∈ G, a ∉ Γ.U → a ∈ T := by
    rintro a ⟨⟨⟨-, hai⟩, hah⟩, haC⟩ haU
    have hae : a ∉ e := fun h' => haU ((he.2.1 h').1)
    have haX : a ∉ X := by
      rcases interior_subset hai with h' | h'
      · exact h'
      · exact (hae h').elim
    obtain ⟨p, -, rfl⟩ := hah.resolve_left haX
    have hpB : p ∈ B := by
      by_contra hp
      exact haC ⟨p, hp, rfl⟩
    have hp0 : 0 < p.2 := by
      by_contra hp
      have ht : p.2 = 0 := le_antisymm (not_lt.mp hp) (unitInterval.nonneg _)
      have hpz : p = (p.1, 0) := Prod.ext rfl ht
      exact haX (hpz ▸ hbot p.1)
    exact ⟨p, ⟨hpB.1, hp0, hpB.2⟩, rfl⟩
  have key : ∀ {Δ₃ A₄ Δ₄ : Set S}, T ⊆ Δ₃ → A₄ ⊆ Δ₄ → Disjoint A₄ Γ.U → y ∈ closure A₄ →
      Δ₃ ∩ Δ₄ ⊆ Γ.U → False := by
    intro Δ₃ A₄ Δ₄ h₁ h₂ h₃ h₄ h₅
    obtain ⟨a, haG, haA⟩ := mem_closure_iff.mp h₄ G hGo hyG
    have haU := disjoint_left.mp h₃ haA
    exact haU (h₅ ⟨h₁ (hsub a haG haU), h₂ haA⟩)
  have hTcov : T ⊆ Δ₁ ∪ Δ₂ := fun x hx => hcov (hTW hx)
  have hsplit : T ⊆ Δ₁ ∨ T ⊆ Δ₂ := by
    by_contra hnot
    push Not at hnot
    obtain ⟨hn₁, hn₂⟩ := hnot
    obtain ⟨a, ha, ha₁⟩ := not_subset.mp hn₁
    obtain ⟨b, hb, hb₂⟩ := not_subset.mp hn₂
    obtain ⟨x, hxT, hx₁, hx₂⟩ := isPreconnected_closed_iff.mp hTc Δ₁ Δ₂ hΔ₁ hΔ₂ hTcov
      ⟨b, hb, (hTcov hb).resolve_right hb₂⟩ ⟨a, ha, (hTcov ha).resolve_left ha₁⟩
    exact hTU x hxT (hmeet ⟨hx₁, hx₂⟩)
  rcases hsplit with hs | hs
  · exact key hs s₂ d₂ (c₂ ⟨hye, hyW⟩) hmeet
  · exact key hs s₁ d₁ (c₁ ⟨hye, hyW⟩) (by rwa [inter_comm])

open Classical in
/-- The number of sides of `e` outside `X`, if `e` meets the frontier of `X`, and otherwise `0`. -/
noncomputable def perimeterCount (X e : Set S) : ℕ :=
  if (e ∩ frontier X).Nonempty then (if IsTwoSided Xᶜ e then 2 else 1) else 0

/-- Each point of the circle is `Circle.exp (2πt)` for some `t` in `[0, 1)`. -/
theorem exists_collar_time (z : Circle) : ∃ t : ℝ, t ∈ Ico (0 : ℝ) 1 ∧ z = Circle.exp
  (2 * Real.pi * t) := by
  obtain ⟨i, hi, u, hu, hz⟩ := exists_circle_param one_pos z
  obtain rfl : i = 0 := by omega
  refine ⟨u.1, ⟨u.2.1, hu⟩, ?_⟩
  simpa using hz

variable [T2Space S] [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- **Each perimeter walk uses `e` at least `perimeterCount X e` times.** -/
theorem count_le_edgeCount (hS : IsClosedSurface S) {Γ : Drawing S} {X : Set S} (hXc : IsClosed X)
    (hXn : IsGammaNice Γ X) {u : S} {W : GraphWalk Γ.toGraph u u} (hW : IsPerimeterWalk Γ X W)
    {e : Set S} (he : e ∈ Γ.E) : perimeterCount X e ≤ edgeCount W.edges e := by
  classical
  obtain ⟨h, -, hoff, hrng, hop, hcase⟩ := hW
  rw [subBd_eq_frontier] at hrng
  by_cases hef : (e ∩ frontier X).Nonempty
  swap
  · simp [perimeterCount, hef]
  obtain ⟨y₀, hy₀, hy₀f⟩ := hef
  have hef : (e ∩ frontier X).Nonempty := ⟨y₀, hy₀, hy₀f⟩
  have heF : e ⊆ frontier X := edge_subset_frontier hS hXc hXn he hy₀ hy₀f
  have hbot : ∀ z, h (z, 0) ∈ X := fun z => hXc.frontier_subset (hrng ▸ mem_range_self z)
  rcases hcase with ⟨h0, hu⟩ | ⟨-, hrun⟩
  · exfalso
    obtain ⟨z, hz⟩ := hrng.superset hy₀f
    have hzu : y₀ = u := hz.symm.trans (hu z)
    have huV : u ∈ Γ.V := by
      cases W with
      | nil hv => exact hv
      | cons hl rest => exact hl.2.1
    exact (he.2.1 hy₀).2 (hzu ▸ huV)
  have htime : ∀ y ∈ e, ∃ z, ∃ t ∈ Ico (0 : ℝ) 1, collarCurve h t = y ∧ h (z, 0) = y ∧
      z = Circle.exp (2 * Real.pi * t) := by
    intro y hy
    obtain ⟨z, hz⟩ := hrng.superset (heF hy)
    obtain ⟨t, ht, rfl⟩ := exists_collar_time z
    exact ⟨_, t, ht, hz, hz, rfl⟩
  have hpos : 0 < edgeCount W.edges e := by
    obtain ⟨z, t, ht, hty, -⟩ := htime y₀ hy₀
    obtain ⟨e', he', hm⟩ := runs_mem W hrun t ⟨ht.1, ht.2.le⟩ (by
      rw [hty]
      exact (he.2.1 hy₀).2)
    have heq : e = e' := Γ.edge_eq_of_mem he (mem_E_of_mem_edges W he') (hty ▸ hy₀) hm
    exact List.count_pos_iff.mpr (heq ▸ he')
  by_cases hts : IsTwoSided Xᶜ e
  swap
  · simp only [perimeterCount, hef, hts, ite_true, ite_false]
    exact hpos
  simp only [perimeterCount, hef, hts, ite_true]
  by_contra hlt
  have hle : edgeCount W.edges e ≤ 1 := by omega
  obtain ⟨y, hye, hyi⟩ := hts
  obtain ⟨z₀, t₀, ht₀, hty₀, hz₀, rfl⟩ := htime y hye
  refine no_single_pass hS he (heF.trans hXc.frontier_subset) h hoff hbot hop hye hyi hz₀ fun z hz
    => ?_
  obtain ⟨t, ht, rfl⟩ := exists_collar_time z
  have heqt : t = t₀ := runs_unique W he hrun hle t ⟨ht.1, ht.2.le⟩ t₀ ⟨ht₀.1, ht₀.2.le⟩
    (by
      change h (_, 0) ∈ e
      rw [hz]
      exact hye)
    (by
      change h (_, 0) = h (_, 0)
      rw [hz, hz₀])
  rw [heqt]

omit [T2Space S] [ConnectedSpace S] in
/-- The length of a walk is the sum of the number of times it uses each edge. -/
theorem length_eq_sum {Γ : Drawing S} {u v : S} (W : GraphWalk Γ.toGraph u v) :
    W.length = ∑ e ∈ Γ.finite_edges.toFinset, edgeCount W.edges e := by
  classical
  have hsub : W.edges.toFinset ⊆ Γ.finite_edges.toFinset := fun e he =>
    Γ.finite_edges.mem_toFinset.mpr (mem_E_of_mem_edges W (List.mem_toFinset.mp he))
  have h₀ : ∀ e ∈ Γ.finite_edges.toFinset, e ∉ W.edges.toFinset → edgeCount W.edges e = 0 :=
    fun e _ he => edgeCount_eq_zero fun h => he (List.mem_toFinset.mpr h)
  rw [← Finset.sum_subset hsub h₀]
  exact (List.sum_toFinset_count_eq_length W.edges).symm

/-- The sum over the edges of `Γ` of `perimeterCount X e`. -/
noncomputable def perimeterSum (Γ : Drawing S) (X : Set S) : ℕ :=
  ∑ e ∈ Γ.finite_edges.toFinset, perimeterCount X e

/-- **A shortest perimeter walk.** The walk has length `l(X)`, and it uses each edge exactly
`perimeterCount X e` times. -/
theorem exists_minimal_perimeterWalk (hS : IsClosedSurface S)
    {Γ : Drawing S} {X : Set S} (hXc : IsClosed X)
    (hXn : IsGammaNice Γ X) (hXs : IsSimplyConnectedSet X) (hne : X.Nonempty) (hu : X ≠ univ) :
    ∃ (u : S) (W : GraphWalk Γ.toGraph u u), IsPerimeterWalk Γ X W ∧
      W.length = perimeterWalkLength Γ X ∧ W.length = perimeterSum Γ X ∧
      ∀ e ∈ Γ.E, edgeCount W.edges e = perimeterCount X e := by
  obtain ⟨u, W, hW, hc⟩ := exists_perimeterWalk hS hXc hXn hXs hne hu
  have hc' : ∀ e ∈ Γ.E, edgeCount W.edges e = perimeterCount X e := hc
  have hsum : W.length = perimeterSum Γ X := by
    rw [length_eq_sum]
    exact Finset.sum_congr rfl fun e he => hc' e (Γ.finite_edges.mem_toFinset.mp he)
  refine ⟨u, W, hW, ?_, hsum, hc'⟩
  apply le_antisymm
  · refine le_csInf ⟨_, u, W, hW, rfl⟩ ?_
    rintro _ ⟨v, W', hW', rfl⟩
    rw [hsum, length_eq_sum, perimeterSum]
    exact Finset.sum_le_sum fun e he => count_le_edgeCount hS hXc hXn hW'
      (Γ.finite_edges.mem_toFinset.mp he)
  · exact Nat.sInf_le ⟨u, W, hW, rfl⟩

/-- The formula for `l(X)`. -/
theorem perimeterWalkLength_eq (hS : IsClosedSurface S)
    {Γ : Drawing S} {X : Set S} (hXc : IsClosed X)
    (hXn : IsGammaNice Γ X) (hXs : IsSimplyConnectedSet X) (hne : X.Nonempty) (hu : X ≠ univ) :
    perimeterWalkLength Γ X = perimeterSum Γ X := by
  obtain ⟨u', W, -, h₁, h₂, -⟩ := exists_minimal_perimeterWalk hS hXc hXn hXs hne hu
  exact h₁.symm.trans h₂

end GraphMinor.GM11
