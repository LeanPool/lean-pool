/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section11
public import LeanPool.GraphMinor.GM07.Section11f
public import LeanPool.GraphMinor.GM11.LocalCone
public import LeanPool.GraphMinor.GM11.GlueFaces
public import LeanPool.GraphMinor.GM19.Conditional
import LeanPool.GraphMinor.GM19.Section6a
import LeanPool.GraphMinor.Surface.Epstein

/-!
# Existence of `α(G)` Candidates (`GM19.GM07AlphaExistsStatement`)

This file proves the remark in Graph Minors VII, Section 5 (page 230) on the existence of a
solid, connected, `G`-normal, non-near-planar subset `X ⊆ S` (`IsAlphaCandidate G X`) on any
connected surface without boundary (`bd S = ∅`) that is not a 2-sphere (`¬ IsSphere S`),
unconditionally concluding `GM19.GM07AlphaExistsStatement`.

## Main results
- `exists_goodOpen`: Every point `z : S` on a closed surface `S` has an open neighborhood `O`
  contained in a closed disc `D` such that any two points `x, y ∈ O \ G.U` are joined by a path in
  `D` and a homotopic path in `(G.U \ G.V)ᶜ`.
- `exists_homotopic_normal_path`: Every path in `S` with endpoints outside `G.U` is homotopic with
  fixed endpoints to a `G`-normal path in `(G.U \ G.V)ᶜ`.
- `exists_homotopic_normal_curve`: Every closed curve `φ : C(Circle, S)` on a closed connected
  surface `S` is homotopic in `S` to a `G`-normal closed curve `ψ : C(Circle, S)`.
- `gm07_alpha_exists_core`: Unconditional proof of `GM19.GM07AlphaExistsStatement`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology Metric Filter unitInterval
open GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- An open set `O` is *good* for a drawing `G` if `O` is contained in a closed disc `D` and any
two points `x, y ∈ O \ G.U` are joined by a path `p` in `D` and a homotopic path `q` in
`(G.U \ G.V)ᶜ`. -/
def GoodOpen (G : Drawing S) (O : Set S) : Prop :=
  IsOpen O ∧ ∃ D : Set S, IsClosedDisc D ∧ O ⊆ D ∧
    ∀ x ∈ O \ G.U, ∀ y ∈ O \ G.U,
      ∃ (p q : Path x y), (∀ u, p u ∈ D) ∧ (∀ u, q u ∈ (G.U \ G.V)ᶜ) ∧ p.Homotopic q

theorem goodOpen_of_joinedIn (G : Drawing S) {O D : Set S} (hO : IsOpen O) (hD : IsClosedDisc D)
    (hOD : O ⊆ D)
    (hjoin : ∀ x ∈ O \ G.U, ∀ y ∈ O \ G.U, JoinedIn (D ∩ (G.U \ G.V)ᶜ) x y) :
    GoodOpen G O := by
  refine ⟨hO, D, hD, hOD, fun x hx y hy => ?_⟩
  obtain ⟨p, hp⟩ := hjoin x hx y hy
  exact ⟨p, p, fun u => (hp u).1, fun u => (hp u).2, Path.Homotopic.refl p⟩

/-- In a locally path-connected space, any two points in a preconnected subset `A` of an open set
`U` are joined by a path in `U`. -/
theorem joinedIn_of_isOpen_of_isPreconnected [LocallyPathConnectedSpace S]
    {U A : Set S} (hU : IsOpen U) (hA : IsPreconnected A) (hAU : A ⊆ U)
    {x y : S} (hx : x ∈ A) (hy : y ∈ A) :
    JoinedIn U x y := by
  have hsub := hA.subset_connectedComponentIn hx hAU
  have hpc : IsPathConnected (connectedComponentIn U x) :=
    (hU.connectedComponentIn).isConnected_iff_isPathConnected.mp
      ⟨⟨x, mem_connectedComponentIn (hAU hx)⟩, isPreconnected_connectedComponentIn⟩
  exact (hpc.joinedIn x (mem_connectedComponentIn (hAU hx)) y (hsub hy)).mono
    (connectedComponentIn_subset U x)

/-- Case 1: Every point `z ∉ G.U` has a good open neighborhood. -/
theorem exists_goodOpen_of_notMem_U (hS : IsClosedSurface S) (G : Drawing S) {z : S}
    (hz : z ∉ G.U) :
    ∃ O : Set S, z ∈ O ∧ GoodOpen G O := by
  have : T2Space S := hS.2.1
  obtain ⟨D, D', hD, hD', hzD', hD'D, hDU, -⟩ :=
    exists_closedDisc_nbhd hS G.isClosed_U.isOpen_compl hz
  refine ⟨D', hzD', goodOpen_of_joinedIn G hD' hD hD'D fun x hx y hy => ?_⟩
  refine (hD.isPathConnected.joinedIn x (hD'D hx.1) y (hD'D hy.1)).mono fun w hw => ?_
  exact ⟨hw, fun h => hDU hw h.1⟩

/-- Case 2a: A polar chart at a vertex `z ∈ G.V` gives a good open neighborhood. -/
theorem exists_goodOpen_of_isPolar [T2Space S] {G : Drawing S} {z : S} (hzV : z ∈ G.V)
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar G z Φ) :
    ∃ O : Set S, z ∈ O ∧ GoodOpen G O := by
  have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hemb : IsEmbedding Φ := (Φ.continuous.isClosedEmbedding hp.inj).isEmbedding
  have hD : IsClosedDisc (range Φ) := ⟨hemb.toHomeomorph⟩
  refine ⟨interior (range Φ), hp.nhd,
    goodOpen_of_joinedIn G isOpen_interior hD interior_subset fun x hx y hy => ?_⟩
  have hray_join : ∀ w ∈ interior (range Φ) \ G.U,
      JoinedIn (range Φ ∩ (G.U \ G.V)ᶜ) z w := by
    intro w ⟨hw_int, hwU⟩
    obtain ⟨u, rfl⟩ := interior_subset hw_int
    have huc : u ≠ polarCentre := by
      rintro rfl
      exact hwU (hp.centre.symm ▸ G.V_subset_U hzV)
    have hcont : Continuous fun t : I => Φ (discScale t u) :=
      (Φ.continuous.comp continuous_discScale).comp (Continuous.prodMk continuous_id
        continuous_const)
    refine ⟨⟨⟨fun t => Φ (discScale t u), hcont⟩, by simp [discScale_zero, hp.centre],
      by simp [discScale_one]⟩, fun t => ⟨mem_range_self _, ?_⟩⟩
    change Φ (discScale t u) ∈ (G.U \ G.V)ᶜ
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with h0 | h0
    · have ht0 : t = 0 := Subtype.ext h0.symm
      rw [ht0, discScale_zero, hp.centre]
      exact fun h => h.2 hzV
    · obtain ⟨a, ha, h1, h2⟩ := hp.ray u huc t h0
      intro hU_diff
      rcases ha with (⟨v, hv, rfl⟩ | he) | hr
      · exact hwU (h1.symm ▸ G.V_subset_U hv)
      · exact hwU (he.2.1 h1).1
      · exact region_subset hr h2 hU_diff.1
  exact (hray_join x hx).symm.trans (hray_join y hy)

/-- Case 2: Every vertex `z ∈ G.V` has a good open neighborhood. -/
theorem exists_goodOpen_of_mem_V (hS : IsClosedSurface S) (G : Drawing S) {z : S}
    (hzV : z ∈ G.V) :
    ∃ O : Set S, z ∈ O ∧ GoodOpen G O := by
  classical
  have : T2Space S := hS.2.1
  have : Nonempty S := ⟨z⟩
  have : LocallyPathConnectedSpace S := IsClosedSurface.locallyPathConnectedSpace hS
  obtain ⟨γ, hγ⟩ := exists_edgePar G
  by_cases h2 : 2 ≤ Nat.card (halfEdges G γ z)
  · obtain ⟨Φ, hΦ⟩ := exists_isPolar_of_sectors hS hγ hzV h2
    exact exists_goodOpen_of_isPolar hzV hΦ
  · have hfinH : Finite (halfEdges G γ z) := (finite_halfEdges G γ z).to_subtype
    have hss : Subsingleton (halfEdges G γ z) :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    rcases isEmpty_or_nonempty (halfEdges G γ z) with h0 | ⟨⟨⟨e, b⟩, he, hb⟩⟩
    · have hno : ∀ g ∈ G.E, z ∉ closure g := by
        intro g hg hzg
        obtain ⟨b, hb⟩ := exists_end_eq hγ hg hzV hzg
        exact h0.false ⟨(g, b), hg, hb⟩
      let T : Set S := (G.V \ {z}) ∪ ⋃ g ∈ G.E, closure g
      have hT : IsClosed T := (G.finite_V.subset sdiff_subset).isClosed.union
        (G.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure)
      have hzT : z ∉ T := by
        rintro (h | h)
        · exact h.2 rfl
        · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp h
          exact hno g hg hzg
      obtain ⟨D, D', hD, hD', hzD', hD'D, hDT, -⟩ :=
        exists_closedDisc_nbhd hS hT.isOpen_compl hzT
      refine ⟨D', hzD', goodOpen_of_joinedIn G hD' hD hD'D fun x hx y hy => ?_⟩
      refine (hD.isPathConnected.joinedIn x (hD'D hx.1) y (hD'D hy.1)).mono fun w hw => ⟨hw, ?_⟩
      rintro ⟨hwU, hwV⟩
      obtain ⟨g, hg, hwg⟩ := G.exists_edge_of_mem hwU hwV
      exact hDT hw (Or.inr (mem_iUnion₂.mpr ⟨g, hg, subset_closure hwg⟩))
    · have hleaf : ∀ f ∈ G.E, f ≠ e → z ∉ closure f := by
        intro f hf hfe hzf
        obtain ⟨b', hb'⟩ := exists_end_eq hγ hf hzV hzf
        have := congrArg (fun k : halfEdges G γ z => k.1.1)
          (hss.elim ⟨(f, b'), hf, hb'⟩ ⟨(e, b), he, hb⟩)
        exact hfe this
      have hzcl : z ∈ closure e := by
        have := end_mem_closure hγ he b
        rwa [hb] at this
      have hnot_loop : ∃ u : S, u ≠ z ∧ closure e ∩ G.V = {u, z} ∧ IsLineWithEnds (closure e) u z
        := by
        rcases G.edge_cond e he with ⟨u, v, huv, hcap, hl⟩ | ⟨u, hu, -⟩
        · have hz_uv : z = u ∨ z = v := by
            have : z ∈ closure e ∩ G.V := ⟨hzcl, hzV⟩
            rwa [hcap, mem_insert_iff, mem_singleton_iff] at this
          rcases hz_uv with rfl | rfl
          · exact ⟨v, huv.symm, by rw [pair_comm]; exact hcap, hl.symm⟩
          · exact ⟨u, huv, hcap, hl⟩
        · exfalso
          have hend : ∀ c, γ e (endOf c) = z := by
            intro c
            have h₁ : γ e (endOf c) ∈ closure e ∩ G.V := by
              refine ⟨end_mem_closure hγ he c, ?_⟩
              cases c
              · exact hγ.zero e he
              · exact hγ.one e he
            have h₂ : z ∈ closure e ∩ G.V := ⟨hzcl, hzV⟩
            rw [hu] at h₁ h₂
            exact h₁.trans h₂.symm
          have := congrArg (fun k : halfEdges G γ z => k.1.2)
            (hss.elim ⟨(e, true), he, hend true⟩ ⟨(e, false), he, hend false⟩)
          simp at this
      obtain ⟨u, huz, hcap, hL⟩ := hnot_loop
      obtain ⟨D, D', hD, hD', hzD', hD'D, -, -⟩ :=
        exists_closedDisc_nbhd hS isOpen_univ (mem_univ z)
      obtain ⟨Z, hZ, hzZ, hZ_conn⟩ :=
        exists_leaf_nbhd hS G he huz hcap hL hleaf hD' hzD'
      refine ⟨Z ∩ D', ⟨hzZ, hzD'⟩,
        goodOpen_of_joinedIn G (hZ.inter hD') hD (inter_subset_right.trans hD'D)
          fun x hx y hy => ?_⟩
      obtain ⟨A, hA_conn, hA_disj, hxA, hyA, hAD'⟩ :=
        hZ_conn x hx.1.1 hx.2 y hy.1.1 hy.2
      have hAU : A ⊆ D' \ G.U := fun w hw => ⟨hAD' hw, disjoint_left.mp hA_disj hw⟩
      have hj := joinedIn_of_isOpen_of_isPreconnected (hD'.sdiff G.isClosed_U) hA_conn hAU hxA hyA
      exact hj.mono fun w ⟨hwD', hwU⟩ => ⟨hD'D hwD', fun h => hwU h.1⟩

theorem pathsHomotopic_of_mem_disc {D : Set S} (hD : IsClosedDisc D) {a b : S}
    (p q : Path a b) (hp : ∀ u, p u ∈ D) (hq : ∀ u, q u ∈ D) :
    p.Homotopic q := by
  have ha : a ∈ D := by simpa using hp 0
  have hb : b ∈ D := by simpa using hp 1
  exact (hD.isSimplyConnectedSet.pathsHomotopic
    (pathCod p ha hb hp) (pathCod q ha hb hq)).map
    (f := (⟨Subtype.val, continuous_subtype_val⟩ : C(D, S)))

theorem path_trans_mem {A : Set S} {a b c : S} {p : Path a b} {q : Path b c}
    (hp : ∀ u, p u ∈ A) (hq : ∀ u, q u ∈ A) (u : I) : (p.trans q) u ∈ A := by
  have : (p.trans q) u ∈ range p ∪ range q := Path.trans_range p q ▸ mem_range_self u
  rcases this with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact hv ▸ hp v
  · exact hv ▸ hq v

theorem path_symm_mem {A : Set S} {a b : S} {p : Path a b}
    (hp : ∀ u, p u ∈ A) (u : I) : p.symm u ∈ A := by
  rw [Path.symm_apply]
  exact hp _

theorem path_homotopic_symm {a b : S} {p q : Path a b} (h : p.Homotopic q) :
    p.symm.Homotopic q.symm := by
  obtain ⟨H⟩ := h
  exact ⟨H.symm₂⟩

theorem IsEdgeChart.lower_pathConnected {G : Drawing S} {γ : I → S} {t₀ a b : I}
    {M : ℂ → S} (c : IsEdgeChart G γ t₀ M a b) :
    IsPathConnected (M '' IsEdgeChart.lower) := by
  have hzl : (⟨0, -1 / 2⟩ : ℂ) ∈ IsEdgeChart.lower := by
    refine ⟨?_, by norm_num⟩
    rw [mem_closedBall, dist_zero_right]
    have : ‖(⟨0, -1 / 2⟩ : ℂ)‖ = 1 / 2 := by
      rw [Complex.norm_def, Complex.normSq_mk]
      rw [show (0 : ℝ) * 0 + -1 / 2 * (-1 / 2) = (1 / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by norm_num)
    linarith
  refine ⟨M ⟨0, -1 / 2⟩, ⟨_, hzl, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨p, hp⟩ := (IsEdgeChart.convex_lower.isPathConnected ⟨_, hzl⟩).joinedIn _ hzl w hw
  exact ⟨{ toFun := fun u => M (p u)
           continuous_toFun := c.cont.comp_continuous p.continuous fun u => (hp u).1
           source' := by simp
           target' := by simp }, fun u => ⟨p u, hp u, rfl⟩⟩

theorem IsEdgeChart.upper_pathConnected {G : Drawing S} {γ : I → S} {t₀ a b : I}
    {M : ℂ → S} (c : IsEdgeChart G γ t₀ M a b) :
    IsPathConnected (M '' IsEdgeChart.upper) := by
  have hzu : (⟨0, 1 / 2⟩ : ℂ) ∈ IsEdgeChart.upper := by
    refine ⟨?_, by norm_num⟩
    rw [mem_closedBall, dist_zero_right]
    have : ‖(⟨0, 1 / 2⟩ : ℂ)‖ = 1 / 2 := by
      rw [Complex.norm_def, Complex.normSq_mk]
      rw [show (0 : ℝ) * 0 + 1 / 2 * (1 / 2) = (1 / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by norm_num)
    linarith
  refine ⟨M ⟨0, 1 / 2⟩, ⟨_, hzu, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨p, hp⟩ := (IsEdgeChart.convex_upper.isPathConnected ⟨_, hzu⟩).joinedIn _ hzu w hw
  exact ⟨{ toFun := fun u => M (p u)
           continuous_toFun := c.cont.comp_continuous p.continuous fun u => (hp u).1
           source' := by simp
           target' := by simp }, fun u => ⟨p u, hp u, rfl⟩⟩

/-- Case 3: Every point `z ∈ e` (`e ∈ G.E`) has a good open neighborhood. -/
theorem exists_goodOpen_of_mem_edge (hS : IsClosedSurface S) (G : Drawing S) {e : Set S}
    (he : e ∈ G.E) {z : S} (hz : z ∈ e) :
    ∃ O : Set S, z ∈ O ∧ GoodOpen G O := by
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨γ, hγ, hγ0, hγ1, hinj, hγe⟩ := exists_edge_param G he
  let T : Set I := {t : I | ∃ O : Set S, γ t ∈ O ∧ GoodOpen G O}
  have h0T : (0 : I) ∈ T := exists_goodOpen_of_mem_V hS G hγ0
  have h1T : (1 : I) ∈ T := exists_goodOpen_of_mem_V hS G hγ1
  have hT_open : IsOpen T := by
    rw [isOpen_iff_forall_mem_open]
    rintro t ⟨O, htO, hGO⟩
    exact ⟨γ ⁻¹' O, fun s hs => ⟨O, hs, hGO⟩, hGO.1.preimage hγ, htO⟩
  have hT_closed : IsClosed T := by
    rw [← closure_subset_iff_isClosed]
    intro t₀ ht₀_cl
    rcases eq_or_lt_of_le (unitInterval.nonneg t₀) with h0 | h0
    · exact (Subtype.ext h0.symm : t₀ = 0) ▸ h0T
    rcases eq_or_lt_of_le (unitInterval.le_one t₀) with h1 | h1
    · exact (Subtype.ext h1 : t₀ = 1) ▸ h1T
    have ht₀ : t₀ ∈ Ioo (0 : I) 1 := ⟨h0, h1⟩
    obtain ⟨M, a, b, g₁, g₂, _, g₄, g₅, _, g₇, g₈, g₉, g₁₀, g₁₁⟩ :=
      exists_edge_chart hS G he hγ hγ0 hγ1 hinj hγe ht₀ ht₀.1 ht₀.2
    have c : IsEdgeChart G γ t₀ M a b := ⟨g₁, g₂, g₄, g₅, g₇, g₈, g₉, g₁₀, g₁₁⟩
    let O : Set S := M '' ball 0 1
    have hO_open : IsOpen O := by
      change IsOpen (M '' ball 0 1)
      rw [← c.discInt_eq]
      exact c.isClosedDisc.isOpen_discInt hman
    have ht₀_O : γ t₀ ∈ O := ⟨0, by simp, c.zero⟩
    have hOD : O ⊆ c.disc := image_mono ball_subset_closedBall
    obtain ⟨t₁, ⟨ht₁_ab, ⟨O₁, ht₁_O₁, hO₁_open, D₁, hD₁, hO₁D₁, hO₁_join⟩⟩⟩ :=
      mem_closure_iff.mp ht₀_cl (Ioo a b) isOpen_Ioo ⟨c.left, c.right⟩
    have hγt₁_ball : γ t₁ ∈ M '' {z | z ∈ ball (0 : ℂ) 1 ∧ z.im = 0} := by
      rw [c.ball_eq]
      exact ⟨t₁, ht₁_ab, rfl⟩
    obtain ⟨z₁, ⟨hz₁_ball, hz₁_im⟩, hMz₁⟩ := hγt₁_ball
    have hγt₁_O : γ t₁ ∈ O₁ ∩ O := ⟨ht₁_O₁, z₁, hz₁_ball, hMz₁⟩
    obtain ⟨E, E', hE, hE', hγt₁_E', hE'E, hE_sub, -⟩ :=
      exists_closedDisc_nbhd hS (hO₁_open.inter hO_open) hγt₁_O
    have hcont_z₁ : ContinuousAt M z₁ :=
      c.cont.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hz₁_ball) ball_subset_closedBall)
    have hnhds : M ⁻¹' E' ∩ ball (0 : ℂ) 1 ∈ 𝓝 z₁ :=
      Filter.inter_mem (hcont_z₁.preimage_mem_nhds (hE'.mem_nhds (hMz₁.symm ▸ hγt₁_E')))
        (isOpen_ball.mem_nhds hz₁_ball)
    obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp hnhds
    let w_low : ℂ := z₁ - ((δ / 2 : ℝ) : ℂ) * Complex.I
    let w_up : ℂ := z₁ + ((δ / 2 : ℝ) : ℂ) * Complex.I
    have hw_low_mem : w_low ∈ ball z₁ δ := by
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ_pos)]
      linarith
    have hw_up_mem : w_up ∈ ball z₁ δ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ_pos)]
      linarith
    have hw_low_in : w_low ∈ IsEdgeChart.lower := by
      refine ⟨ball_subset_closedBall (hδ_ball hw_low_mem).2, ?_⟩
      simp [w_low, hz₁_im]
      linarith
    have hw_up_in : w_up ∈ IsEdgeChart.upper := by
      refine ⟨ball_subset_closedBall (hδ_ball hw_up_mem).2, ?_⟩
      simp [w_up, hz₁_im]
      linarith
    let x_L : S := M w_low
    let x_U : S := M w_up
    have hx_L_L : x_L ∈ M '' IsEdgeChart.lower := ⟨w_low, hw_low_in, rfl⟩
    have hx_U_U : x_U ∈ M '' IsEdgeChart.upper := ⟨w_up, hw_up_in, rfl⟩
    have hx_L_E' : x_L ∈ E' := (hδ_ball hw_low_mem).1
    have hx_U_E' : x_U ∈ E' := (hδ_ball hw_up_mem).1
    have hx_L_notU : x_L ∉ G.U := disjoint_left.mp c.lower_disjoint hx_L_L
    have hx_U_notU : x_U ∉ G.U := disjoint_left.mp c.upper_disjoint hx_U_U
    obtain ⟨p₁, q₀, hp₁D₁, hq₀G, hp₁q₀⟩ :=
      hO₁_join x_L ⟨(hE_sub (hE'E hx_L_E')).1, hx_L_notU⟩
        x_U ⟨(hE_sub (hE'E hx_U_E')).1, hx_U_notU⟩
    obtain ⟨p₀, hp₀E⟩ := hE.isPathConnected.joinedIn x_L (hE'E hx_L_E') x_U (hE'E hx_U_E')
    have hp₀D : ∀ u, p₀ u ∈ c.disc := fun u => hOD (hE_sub (hp₀E u)).2
    have hp₀D₁ : ∀ u, p₀ u ∈ D₁ := fun u => hO₁D₁ (hE_sub (hp₀E u)).1
    have hp₀q₀ : p₀.Homotopic q₀ :=
      (pathsHomotopic_of_mem_disc hD₁ p₀ p₁ hp₀D₁ hp₁D₁).trans hp₁q₀
    have hL_sub : M '' IsEdgeChart.lower ⊆ c.disc ∩ (G.U \ G.V)ᶜ := by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw.1, rfl⟩, fun h => disjoint_left.mp c.lower_disjoint ⟨w, hw, rfl⟩ h.1⟩
    have hU_sub : M '' IsEdgeChart.upper ⊆ c.disc ∩ (G.U \ G.V)ᶜ := by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw.1, rfl⟩, fun h => disjoint_left.mp c.upper_disjoint ⟨w, hw, rfl⟩ h.1⟩
    have h_side : ∀ w ∈ O \ G.U, w ∈ M '' IsEdgeChart.lower ∨ w ∈ M '' IsEdgeChart.upper := by
      rintro _ ⟨⟨z, hz, rfl⟩, hnU⟩
      rcases IsEdgeChart.cases_of_closedBall (ball_subset_closedBall hz) with h | h | h
      · exact Or.inl ⟨z, h, rfl⟩
      · exact absurd ((c.mem_U z (ball_subset_closedBall hz)).mpr h) hnU
      · exact Or.inr ⟨z, h, rfl⟩
    refine ⟨O, ht₀_O, hO_open, c.disc, c.isClosedDisc, hOD, fun x hx y hy => ?_⟩
    rcases h_side x hx with hxL | hxU <;> rcases h_side y hy with hyL | hyU
    · obtain ⟨p, hp⟩ := ((IsEdgeChart.lower_pathConnected c).joinedIn x hxL y hyL).mono hL_sub
      exact ⟨p, p, fun u => (hp u).1, fun u => (hp u).2, Path.Homotopic.refl p⟩
    · obtain ⟨α, hα⟩ := ((IsEdgeChart.lower_pathConnected c).joinedIn x hxL x_L hx_L_L).mono hL_sub
      obtain ⟨β, hβ⟩ := ((IsEdgeChart.upper_pathConnected c).joinedIn x_U hx_U_U y hyU).mono hU_sub
      refine ⟨α.trans (p₀.trans β), α.trans (q₀.trans β),
        path_trans_mem (fun u => (hα u).1) (path_trans_mem hp₀D fun u => (hβ u).1),
        path_trans_mem (fun u => (hα u).2) (path_trans_mem hq₀G fun u => (hβ u).2),
        (Path.Homotopic.refl α).hcomp (hp₀q₀.hcomp (Path.Homotopic.refl β))⟩
    · obtain ⟨α, hα⟩ := ((IsEdgeChart.upper_pathConnected c).joinedIn x hxU x_U hx_U_U).mono hU_sub
      obtain ⟨β, hβ⟩ := ((IsEdgeChart.lower_pathConnected c).joinedIn x_L hx_L_L y hyL).mono hL_sub
      refine ⟨α.trans (p₀.symm.trans β), α.trans (q₀.symm.trans β),
        path_trans_mem (fun u => (hα u).1) (path_trans_mem (path_symm_mem hp₀D) fun u => (hβ u).1),
        path_trans_mem (fun u => (hα u).2) (path_trans_mem (path_symm_mem hq₀G) fun u => (hβ u).2),
        (Path.Homotopic.refl α).hcomp ((path_homotopic_symm hp₀q₀).hcomp (Path.Homotopic.refl β))⟩
    · obtain ⟨p, hp⟩ := ((IsEdgeChart.upper_pathConnected c).joinedIn x hxU y hyU).mono hU_sub
      exact ⟨p, p, fun u => (hp u).1, fun u => (hp u).2, Path.Homotopic.refl p⟩
  have hT_univ : T = univ := IsClopen.eq_univ ⟨hT_closed, hT_open⟩ ⟨0, h0T⟩
  obtain ⟨t, -, rfl⟩ : z ∈ γ '' Ioo 0 1 := hγe.symm ▸ hz
  have htT : t ∈ T := hT_univ.symm ▸ mem_univ t
  exact htT

/-- Every point `z : S` on a closed surface `S` has a good open neighborhood for `G`. -/
theorem exists_goodOpen (hS : IsClosedSurface S) (G : Drawing S) (z : S) :
    ∃ O : Set S, z ∈ O ∧ GoodOpen G O := by
  by_cases hzV : z ∈ G.V
  · exact exists_goodOpen_of_mem_V hS G hzV
  · by_cases hzU : z ∈ G.U
    · obtain ⟨e, he, hze⟩ := G.exists_edge_of_mem hzU hzV
      exact exists_goodOpen_of_mem_edge hS G he hze
    · exact exists_goodOpen_of_notMem_U hS G hzU

/-- Every path `p : Path a b` in `S` with endpoints `a, b ∉ G.U` is homotopic with fixed endpoints
to a path `q : Path a b` in `(G.U \ G.V)ᶜ`. -/
theorem exists_homotopic_normal_path (hS : IsClosedSurface S) (G : Drawing S) {a b : S}
    (p : Path a b) (ha : a ∉ G.U) (hb : b ∉ G.U) :
    ∃ q : Path a b, p.Homotopic q ∧ ∀ u, q u ∈ (G.U \ G.V)ᶜ := by
  have : T2Space S := hS.2.1
  let good : Set I → Prop := fun W => IsOpen W ∧ ∃ U : Set S, GoodOpen G U ∧ ∀ t ∈ W, p t ∈ U
  have hcover : (univ : Set I) ⊆ ⋃ W : {W : Set I // good W}, W.1 := by
    intro t _
    obtain ⟨U, htU, hGU⟩ := exists_goodOpen hS G (p t)
    exact mem_iUnion.mpr ⟨⟨p ⁻¹' U, hGU.1.preimage p.continuous, U, hGU, fun _ hw => hw⟩, htU⟩
  obtain ⟨t, ht0, htmono, ⟨n₀, hn₀⟩, htW⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun W : {W : Set I // good W} => W.2.1) hcover
  have key : ∀ n (U : Set S), GoodOpen G U → p (t n) ∈ U →
      ∃ (x : S) (α : Path (p (t n)) x) (q : Path (p 0) x),
        x ∈ U \ G.U ∧ (∀ u, α u ∈ U) ∧ (∀ u, q u ∈ (G.U \ G.V)ᶜ) ∧
        (p.subpath 0 (t n)).Homotopic (q.trans α.symm) := by
    intro n
    induction n with
    | zero =>
      intro U _ hpU
      rw [ht0] at hpU ⊢
      have hp0 : p 0 ∉ G.U := by rw [p.source]; exact ha
      refine ⟨p 0, Path.refl (p 0), Path.refl (p 0), ⟨hpU, hp0⟩,
        fun _ => hpU, fun _ h => hp0 h.1, ?_⟩
      rw [Path.subpath_self]
      exact (Path.Homotopic.refl_trans (Path.refl (p 0))).symm
    | succ n ih =>
      intro U' hU' hp_U'
      obtain ⟨⟨W, _, U_n, hUn, hW_Un⟩, hsub⟩ := htW n
      have hle : t n ≤ t (n + 1) := htmono (Nat.le_succ n)
      have hp_Un : ∀ w ∈ Icc (t n) (t (n + 1)), p w ∈ U_n := fun w hw => hW_Un w (hsub hw)
      obtain ⟨x_n, α_n, q_n, hx_n, hα_n, hq_n, hhom_n⟩ :=
        ih U_n hUn (hp_Un (t n) ⟨le_rfl, hle⟩)
      obtain ⟨hUn_open, D_n, hD_n, hUn_Dn, hUn_join⟩ := hUn
      have hp_inter : p (t (n + 1)) ∈ U_n ∩ U' := ⟨hp_Un (t (n + 1)) ⟨hle, le_rfl⟩, hp_U'⟩
      obtain ⟨E, E', hE, hE', hp_E', hE'E, hE_sub, -⟩ :=
        exists_closedDisc_nbhd hS (hUn_open.inter hU'.1) hp_inter
      obtain ⟨x', hx'_E', hx'_notU⟩ :=
        exists_notMem_U (Γ := G) hS hE' ⟨p (t (n + 1)), hp_E'⟩
      obtain ⟨α', hα'E⟩ := hE.isPathConnected.joinedIn (p (t (n + 1))) (hE'E hp_E') x' (hE'E hx'_E')
      have hx'_Un : x' ∈ U_n \ G.U := ⟨(hE_sub (hE'E hx'_E')).1, hx'_notU⟩
      obtain ⟨r, s, hrD, hsG, hrs⟩ := hUn_join x_n hx_n x' hx'_Un
      have hpiece : ∀ u, (p.subpath (t n) (t (n + 1))) u ∈ D_n := by
        intro u
        have : (p.subpath (t n) (t (n + 1))) u ∈ p '' uIcc (t n) (t (n + 1)) := by
          rw [← Path.range_subpath]
          exact mem_range_self u
        obtain ⟨v, hv, hv'⟩ := this
        rw [uIcc_of_le hle] at hv
        rw [← hv']
        exact hUn_Dn (hp_Un v hv)
      have h_disc_hom : (α_n.symm.trans (p.subpath (t n) (t (n + 1)))).Homotopic (r.trans α'.symm)
        :=
        pathsHomotopic_of_mem_disc hD_n _ _
          (path_trans_mem (path_symm_mem fun u => hUn_Dn (hα_n u)) hpiece)
          (path_trans_mem hrD (path_symm_mem fun u => hUn_Dn (hE_sub (hα'E u)).1))
      have h_step_hom : (p.subpath 0 (t (n + 1))).Homotopic ((q_n.trans s).trans α'.symm) := by
        refine (Path.Homotopic.subpath_trans_subpath p 0 (t n) (t (n + 1))).symm.trans ?_
        refine (hhom_n.hcomp (Path.Homotopic.refl _)).trans ?_
        refine (Path.Homotopic.trans_assoc q_n α_n.symm _).trans ?_
        refine ((Path.Homotopic.refl q_n).hcomp (h_disc_hom.trans (hrs.hcomp
          (Path.Homotopic.refl α'.symm)))).trans ?_
        exact (Path.Homotopic.trans_assoc q_n s α'.symm).symm
      exact ⟨x', α', q_n.trans s, ⟨(hE_sub (hE'E hx'_E')).2, hx'_notU⟩,
        fun u => (hE_sub (hα'E u)).2, path_trans_mem hq_n hsG, h_step_hom⟩
  obtain ⟨D_b, D'_b, hD_b, hD'_b, hb_D', hD'D_b, hDb_U, -⟩ :=
    exists_closedDisc_nbhd hS G.isClosed_U.isOpen_compl hb
  have hGood_b : GoodOpen G D'_b := by
    refine goodOpen_of_joinedIn G hD'_b hD_b hD'D_b fun x hx y hy => ?_
    refine (hD_b.isPathConnected.joinedIn x (hD'D_b hx.1) y (hD'D_b hy.1)).mono fun w hw => ?_
    exact ⟨hw, fun h => hDb_U hw h.1⟩
  have htn₀ : t n₀ = 1 := hn₀ n₀ le_rfl
  have hp_tn₀ : p (t n₀) = b := by rw [htn₀, p.target]
  obtain ⟨x, α, q, _, hα_D', hqG, hhom⟩ := key n₀ D'_b hGood_b (hp_tn₀.symm ▸ hb_D')
  have hα_G : ∀ u, α.symm u ∈ (G.U \ G.V)ᶜ := fun u => by
    rw [Path.symm_apply]
    exact fun h => hDb_U (hD'D_b (hα_D' _)) h.1
  let q_final : Path a b := (q.trans α.symm).cast p.source.symm hp_tn₀.symm
  refine ⟨q_final, ?_, fun u => ?_⟩
  · have hsub01 : (p.subpath 0 (t n₀)).cast p.source.symm hp_tn₀.symm = p := by
      ext u
      change (p.subpath 0 (t n₀)) u = p u
      rw [htn₀, Path.subpath_zero_one]
      rfl
    rw [← hsub01]
    exact Path.Homotopic.pathCast hhom p.source.symm hp_tn₀.symm
  · change (q.trans α.symm) u ∈ (G.U \ G.V)ᶜ
    exact path_trans_mem hqG hα_G u

/-- Every closed curve `φ : C(Circle, S)` on a closed connected surface `S` is homotopic in `S` to
a `G`-normal closed curve `ψ : C(Circle, S)` (`range ψ ⊆ (G.U \ G.V)ᶜ`). -/
theorem exists_homotopic_normal_curve [ConnectedSpace S] (hS : IsClosedSurface S) (G : Drawing S)
    (φ : C(Circle, S)) :
    ∃ ψ : C(Circle, S), range ψ ⊆ (G.U \ G.V)ᶜ ∧ ClosedCurvesHomotopicIn univ φ ψ := by
  have : T2Space S := hS.2.1
  have : LocallyPathConnectedSpace S := IsClosedSurface.locallyPathConnectedSpace hS
  have : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨x₀, -, hx₀_notU⟩ :=
    exists_notMem_U (Γ := G) hS isOpen_univ ⟨φ 1, mem_univ _⟩
  obtain ⟨α⟩ := PathConnectedSpace.joined (φ 1) x₀
  let p₀ : Path (φ 1) (φ 1) :=
    { toFun := fun t => φ (arcParam 1 t)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  let p₁ : Path (φ 1) (φ 1) := p₀.trans (α.trans α.symm)
  have hp₀_p₁ : p₀.Homotopic p₁ :=
    (Path.Homotopic.trans_refl p₀).symm.trans
      ((Path.Homotopic.refl p₀).hcomp (Path.Homotopic.trans_symm α).symm)
  let f₁ : C(I, S) := ⟨fun t => p₁ t, p₁.continuous⟩
  have hf₁ : f₁ 0 = f₁ 1 := by simp [f₁]
  let φ₁ : C(Circle, S) := loopLift 1 f₁ hf₁
  let g_u : C(S, (univ : Set S)) := ⟨fun x => ⟨x, mem_univ x⟩, by fun_prop⟩
  have hhom₁ : ClosedCurvesHomotopicIn univ φ φ₁ :=
    closedCurvesHomotopicIn_of_path 1 φ φ₁ (p₀.map g_u.continuous) (p₁.map g_u.continuous)
      (fun _ => rfl)
      (fun t => (loopLift_apply 1 f₁ hf₁ t).symm)
      (hp₀_p₁.map g_u)
  have hx₀_range : x₀ ∈ range p₁ := by
    change x₀ ∈ range (p₀.trans (α.trans α.symm))
    rw [Path.trans_range, Path.trans_range]
    exact Or.inr (Or.inl ⟨1, α.target⟩)
  obtain ⟨t₁, ht₁⟩ := hx₀_range
  let z₁ : Circle := arcParam 1 t₁
  have hφ₁_z₁ : φ₁ z₁ ∉ G.U := by
    change loopLift 1 f₁ hf₁ (arcParam 1 t₁) ∉ G.U
    rw [loopLift_apply]
    change p₁ t₁ ∉ G.U
    rw [ht₁]
    exact hx₀_notU
  let p₂ : Path (φ₁ z₁) (φ₁ z₁) :=
    { toFun := fun t => φ₁ (arcParam z₁ t)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  obtain ⟨q, hp₂_q, hq_G⟩ := exists_homotopic_normal_path hS G p₂ hφ₁_z₁ hφ₁_z₁
  let f₂ : C(I, S) := ⟨fun t => q t, q.continuous⟩
  have hf₂ : f₂ 0 = f₂ 1 := by simp [f₂]
  let ψ : C(Circle, S) := loopLift z₁ f₂ hf₂
  have hhom₂ : ClosedCurvesHomotopicIn univ φ₁ ψ :=
    closedCurvesHomotopicIn_of_path z₁ φ₁ ψ (p₂.map g_u.continuous) (q.map g_u.continuous)
      (fun _ => rfl)
      (fun t => (loopLift_apply z₁ f₂ hf₂ t).symm)
      (hp₂_q.map g_u)
  refine ⟨ψ, ?_, GraphMinor.Surface.ClosedCurvesHomotopicIn.trans hhom₁ hhom₂⟩
  rintro _ ⟨w, rfl⟩
  obtain ⟨t, rfl⟩ := arcParam_surjective z₁ w
  change loopLift z₁ f₂ hf₂ (arcParam z₁ t) ∈ (G.U \ G.V)ᶜ
  rw [loopLift_apply]
  exact hq_G t

/-- Every `O`-arc in a Hausdorff space is solid (`IsSolid`). -/
theorem IsOArc.isSolid [T2Space S] {F : Set S} (hF : IsOArc F) : IsSolid F := by
  obtain ⟨φ⟩ := hF
  let f : I → S := fun t => (φ (arcParam 1 t)).1
  have hf : Continuous f := continuous_subtype_val.comp (φ.continuous.comp (arcParam 1).continuous)
  have hrange : F = range f := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := arcParam_surjective 1 (φ.symm ⟨x, hx⟩)
      exact ⟨t, by simp [f, ht]⟩
    · rintro ⟨t, rfl⟩
      exact (φ (arcParam 1 t)).2
  rw [hrange]
  exact ⟨isLocallyArcConnected_of_locJoin fun x hx => locJoin_range hf hx,
    (isCompact_range hf).isClosed⟩

/-- Unconditional proof of `GM19.GM07AlphaExistsStatement` (Graph Minors VII, Section 5, page 230).
-/
theorem gm07_alpha_exists_core : GraphMinor.GM19.GM07AlphaExistsStatement.{u} := by
  intro S _ _ hS hconn hbd hsph G
  have : T2Space S := hS.2.1
  have hS_closed : IsClosedSurface S := isClosedSurface_of_bd_eq_empty hS hbd
  obtain ⟨F₀, hF₀_oarc, hF₀_not_null⟩ :=
    GraphMinor.GM19.exists_not_nullHomotopic hS hbd hsph
  obtain ⟨e₀⟩ := hF₀_oarc
  let φ₀ : C(Circle, S) := ⟨fun z => (e₀ z).1, continuous_subtype_val.comp e₀.continuous⟩
  have hφ₀_not_null : ¬ ClosedCurveIsNullHomotopicIn univ φ₀ := fun h => hF₀_not_null ⟨e₀, h⟩
  obtain ⟨ψ, hψ_norm, hhom⟩ := exists_homotopic_normal_curve hS_closed G φ₀
  have hψ_not_null : ¬ ClosedCurveIsNullHomotopicIn univ ψ := fun h =>
    hφ₀_not_null (null_of_homotopic subset_rfl hhom h)
  obtain ⟨F, hF_oarc, hF_sub, hF_not_null⟩ := theorem_11_2_proof hS ψ hψ_not_null
  have hF_ne : F.Nonempty := by
    obtain ⟨φF⟩ := hF_oarc
    exact ⟨(φF 1).1, (φF 1).2⟩
  refine ⟨F, IsOArc.isSolid hF_oarc,
    ⟨hF_ne, IsArcConnected.isPreconnected (IsOArc.isArcConnected hF_oarc)⟩,
    fun x ⟨hxF, hxU⟩ => by_contra fun hxV => hψ_norm (hF_sub hxF) ⟨hxU, hxV⟩, ?_⟩
  rintro (⟨Δ, hΔ, hFΔ⟩ | ⟨C, ⟨x, hx, rfl⟩, _⟩)
  · exact hF_not_null
      (isNullHomotopicOArcIn_of_subset_disc hF_oarc (subset_univ Δ) hΔ hFΔ)
  · rw [hbd] at hx
    exact hx

end GraphMinor.GM07
