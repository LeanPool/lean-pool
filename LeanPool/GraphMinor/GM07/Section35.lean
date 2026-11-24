/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.GrowForest
public import LeanPool.GraphMinor.GM07.Section2

/-!
# Graph Minors VII, (3.5)

(3.5) (page 221) says that each homoplasty class of forests holds a forest that meets a given
matching `G` in a finite set. The paper leaves
the proof to the reader. Our route: take the discs around the components of the forest `H₀`, and the
matching `G₁` in their boundaries. In each disc,
join the points of `bd(Σ)` by a tree that meets `G` in finitely many points. The new forest and `H₀`
are both surrounded by `G₁`, so by
(3.4), claim (2), they are homotopic.

To join two points in a disc we leave each along a line that misses `G` (`exists_start`), and then
use `finReach_of_connected`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

variable {S T : Type} [TopologicalSpace S] [TopologicalSpace T]

/-- A connected set that misses the frontier of a closed set and meets the set lies in it. -/
theorem subset_of_preconnected_frontier {A B : Set T} (hA : IsPreconnected A) (hB : IsClosed B)
  (hd : Disjoint A (frontier B))
    (hne : (A ∩ B).Nonempty) : A ⊆ B := by
  by_contra hn
  obtain ⟨z, hz, hzB⟩ := not_subset.mp hn
  have hcov : A ⊆ B ∪ closure Bᶜ := fun w _ => by
    by_cases h : w ∈ B
    · exact .inl h
    · exact .inr (subset_closure h)
  obtain ⟨w, hw, h1⟩ := isPreconnected_closed_iff.mp hA _ _ hB isClosed_closure hcov hne ⟨z, hz,
    subset_closure hzB⟩
  refine disjoint_left.mp hd hw ?_
  rw [frontier_eq_closure_inter_closure, hB.closure_eq]
  exact h1

/-- A line from a point of `bd(Σ)` into a disc which misses a drawing `G`, when `G` also misses the
point. -/
theorem exists_start_off {j : S → T} (hj : IsEmbedding j) {D Z : Set S} {y : S}
  (hD : IsClosedDisc D) (hy : y ∈ discBd D) (hZ : IsClosed Z)
    (hyZ : y ∉ Z) : ∃ w K₀, w ∈ discInt D ∧ w ∉ Z ∧ JoinedIn K₀ (j y) (j w) ∧ K₀ ⊆ {j y} ∪ j ''
      (discInt D \ Z) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hpS : h y ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hy
  have hyD : y ∈ D := GM11.discBd_subset _ hy
  set p := h y with hp
  have hgp : g p = y := c.gh hyD
  have hpn : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hpS
  obtain ⟨W₁, hW₁, hW₁eq⟩ := continuousOn_iff'.mp c.gc Zᶜ hZ.isOpen_compl
  have hpW : p ∈ W₁ := by
    have : p ∈ g ⁻¹' Zᶜ ∩ closedBall 0 1 :=
      ⟨by rw [mem_preimage, hgp]; exact hyZ, sphere_subset_closedBall hpS⟩
    rw [hW₁eq] at this
    exact this.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW₁ p hpW
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ 1 / 2 := min_le_right _ _
  let w' : ℂ := ((1 - δ : ℝ) : ℂ) * p
  let Q : Set ℂ := segment ℝ w' p
  have hform : ∀ z ∈ Q, ∃ r : ℝ, 0 ≤ r ∧ r ≤ δ ∧ z = ((1 - r : ℝ) : ℂ) * p := fun z hz => by
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    refine ⟨a * δ, mul_nonneg ha hδ.le, ?_, ?_⟩
    · have : a ≤ 1 := by linarith
      nlinarith
    · simp only [w', Complex.real_smul]
      have hb' : b = 1 - a := by linarith
      subst hb'
      push_cast
      ring
  have hnorm : ∀ r : ℝ, 0 ≤ r → r ≤ δ → ‖((1 - r : ℝ) : ℂ) * p‖ = 1 - r := fun r h0 h1 => by
    rw [norm_mul, hpn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hQball : Q ⊆ closedBall 0 1 := fun z hz => by
    obtain ⟨r, h0, h1, rfl⟩ := hform z hz
    rw [mem_closedBall_zero_iff, hnorm r h0 h1]
    linarith
  have hQZ : ∀ z ∈ Q, g z ∉ Z := fun z hz => by
    obtain ⟨r, h0, h1, e⟩ := hform z hz
    have hd : dist z p < ε := by
      rw [e, dist_eq_norm]
      have h2 : ((1 - r : ℝ) : ℂ) * p - p = ((-r : ℝ) : ℂ) * p := by
        push_cast
        ring
      rw [h2, norm_mul, hpn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg h0]
      linarith
    have h3 : z ∈ W₁ ∩ closedBall 0 1 := ⟨hball hd, hQball hz⟩
    rw [← hW₁eq] at h3
    exact h3.1
  have hQint : ∀ z ∈ Q, z ≠ p → g z ∈ discInt D := fun z hz hne => by
    obtain ⟨r, h0, h1, e⟩ := hform z hz
    refine ⟨c.gm (hQball hz), fun hb => ?_⟩
    have h2 : h (g z) ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hb
    rw [c.hg (hQball hz), mem_sphere_zero_iff_norm, e, hnorm r h0 h1] at h2
    have : r = 0 := by linarith
    apply hne
    rw [e, this]
    simp
  have hw'p : w' ≠ p := fun e => by
    have h1 := congrArg norm e
    rw [show w' = ((1 - δ : ℝ) : ℂ) * p from rfl, hnorm δ hδ.le le_rfl, hpn] at h1
    linarith
  have hmem : w' ∈ Q := left_mem_segment ℝ w' p
  have hjg : JoinedIn Q w' p := ((convex_segment w' p).isPathConnected ⟨w', hmem⟩).joinedIn _ hmem
    _ (right_mem_segment ℝ w' p)
  have hj2 : JoinedIn (j '' (g '' Q)) (j (g w')) (j (g p)) :=
    (hjg.map (c.gc.mono hQball)).map hj.continuous.continuousOn
  rw [hgp] at hj2
  refine ⟨g w', _, hQint w' hmem hw'p, hQZ w' hmem, hj2.symm, ?_⟩
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  by_cases hzp : z = p
  · rw [hzp, hgp]
    exact .inl rfl
  · exact .inr ⟨g z, ⟨hQint z hz hzp, hQZ z hz⟩, rfl⟩

/-- A line that runs next to the edge of a matching `G` at its end `y`, and otherwise misses `G` and
`bd(Σ)`, until it reaches the given open set `O`. -/
theorem exists_start_on (hS : IsSurface S) {j : S → T} {K : Set T} (hT : IsClosedSurface T)
  (hj : IsClosedEmbedding j) (hK : IsClosed K) (hu : range j ∪ K = univ)
    (hi : range j ∩ K = j '' bd S) {G : Drawing S} (hG : IsMatching G) {y : S} (hyb : y ∈ bd S)
      (hyG : y ∈ G.U) {D O : Set S} (hO : IsOpen O) (hyO : y ∈ O)
    (hOD : O \ bd S ⊆ discInt D) : ∃ w K₀, w ∈ discInt D ∧ w ∉ G.U ∧ JoinedIn K₀ (j y) (j w)
      ∧ K₀ ⊆ {j y} ∪ j '' (discInt D \ G.U) := by
  classical
  have ht2 : T2Space T := hT.2.1
  have ht2S : T2Space S := hS.2.1
  have hbc : IsClosed (bd S) := (cuff_statement.{0} S hS).1
  have hprop : ∀ x ∈ G.U, x ∈ bd S → x ∈ G.V := fun x h1 h2 => hG.1 ⟨h2, h1⟩
  have hyV : y ∈ G.V := hprop y hyG hyb
  -- The edge at `y`.
  have hval := hG.2.2 y hyV
  obtain ⟨e, he, hye, hte⟩ : ∃ e ∈ G.E, y ∈ closure e ∧ (tilde e).ncard = 2 := by
    unfold vertexValency at hval
    have hpos : {e ∈ G.E | G.VertexIncident y e ∧ (tilde e).ncard = 2}.Nonempty := by
      by_contra hn
      rw [not_nonempty_iff_eq_empty.mp hn, ncard_empty] at hval
      omega
    obtain ⟨e, he, ⟨-, -, h3⟩, h4⟩ := hpos
    exact ⟨e, he, h3, h4⟩
  have htilde := tilde_eq_closure_inter_V G he
  obtain ⟨y', hne, hcap, hL⟩ : ∃ y', y ≠ y' ∧ closure e ∩ G.V = {y, y'} ∧ IsLineWithEnds
    (closure e) y y' := by
    rcases G.edge_cond e he with ⟨u, v, huv, hcap, hl⟩ | ⟨u, hcap, -⟩
    · have : y ∈ ({u, v} : Set S) := hcap ▸ ⟨hye, hyV⟩
      rcases this with rfl | h1
      · exact ⟨v, huv, hcap, hl⟩
      · rw [mem_singleton_iff.mp h1] at *
        exact ⟨u, huv.symm, by rw [hcap, pair_comm], hl.symm⟩
    · rw [htilde, hcap] at hte
      simp at hte
  have hl' := hL.map_of_embedding hj.isEmbedding
  have hne' : j y ≠ j y' := fun e' => hne (hj.injective e')
  let Zl : Set T := j '' ((G.U \ e) ∪ bd S)
  have hZl : IsClosed Zl := hj.isClosedMap _ ((isClosed_U_sdiff_edge G he).union hbc)
  have heV : ∀ x ∈ e, x ∈ G.U ∧ x ∉ G.V := fun x hx => he.2.1 hx
  have heb : ∀ x ∈ e, x ∉ bd S := fun x hx hb => (heV x hx).2 (hprop x (heV x hx).1 hb)
  have hLZ : (j '' closure e) ∩ Zl ⊆ {j y, j y'} := by
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨x', hx', e'⟩⟩
    obtain rfl := hj.injective e'
    by_cases hxe : x' ∈ e
    · rcases hx' with h1 | h1
      · exact (h1.2 hxe).elim
      · exact (heb _ hxe h1).elim
    · have : x' ∈ tilde e := ⟨hx, hxe⟩
      rw [htilde, hcap] at this
      rcases this with rfl | h1
      · exact .inl rfl
      · exact .inr (congrArg j h1)
  obtain ⟨Dl, A, B, -, hLD, hDZ, -, -, -, hDeq, hAc, -, hAne, -, hAL, -, hLA, -, ⟨pth, -, hpin⟩, -⟩
    := exists_edge_lens hT hl' hne' hZl hLZ
  have hAD : A ⊆ Dl := fun z hz => hDeq ▸ .inl (.inl hz)
  have hAZ : Disjoint A Zl := disjoint_left.mpr fun z h1 h2 => by
    have h3 := hDZ ⟨hAD h1, h2⟩
    have h4 : z ∈ j '' closure e := by
      rcases h3 with rfl | h3
      · exact hl'.left_mem
      · exact (mem_singleton_iff.mp h3) ▸ hl'.right_mem
    exact disjoint_left.mp hAL h1 h4
  have hfr : frontier (range j) = j '' bd S := cap_frontier hT hj hK hu hi
  have hAr : A ⊆ range j := by
    refine subset_of_preconnected_frontier hAc hj.isClosed_range ?_ ?_
    · rw [hfr]
      exact hAZ.mono_right (image_mono subset_union_right)
    · obtain ⟨x₀, hx₀⟩ : e.Nonempty := he.2.2.1.nonempty
      have h1 : j x₀ ∈ interior (range j) := by
        have h2 : j x₀ ∉ frontier (range j) := by
          rw [hfr]
          rintro ⟨x, hx, e'⟩
          rw [hj.injective e'] at hx
          exact heb x₀ hx₀ hx
        by_contra h3
        exact h2 ⟨subset_closure ⟨x₀, rfl⟩, h3⟩
      have h2 : j x₀ ∈ closure A := hLA ⟨x₀, subset_closure hx₀, rfl⟩
      obtain ⟨z, hz, hzA⟩ := mem_closure_iff.mp h2 _ isOpen_interior h1
      exact ⟨z, hzA, interior_subset hz⟩
  obtain ⟨W', hW', hWO⟩ := hj.isInducing.isOpen_iff.mp hO
  have hp0 : pth 0 ∈ W' := by
    rw [pth.source]
    exact (hWO.symm ▸ hyO : y ∈ j ⁻¹' W')
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hW'.preimage pth.continuous) 0 hp0
  let τ : ℝ := min (ε / 2) (1 / 2)
  have hτ : 0 < τ := lt_min (by linarith) (by norm_num)
  have hτ1 : τ ≤ ε / 2 := min_le_left _ _
  have hτ2 : τ ≤ 1 / 2 := min_le_right _ _
  have hIcc : ∀ t ∈ Icc 0 τ, t ∈ Icc (0 : ℝ) 1 := fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  have hgood : ∀ t (ht : t ∈ Icc 0 τ), 0 < t → ∃ x ∈ discInt D \ G.U, pth ⟨t, hIcc t ht⟩ = j x
    := fun t ht h0 => by
    have hA : pth ⟨t, hIcc t ht⟩ ∈ A := hpin _ h0 (show (t : ℝ) < 1 by linarith [ht.2])
    obtain ⟨x, hx⟩ := hAr hA
    have hxO : x ∈ O := by
      rw [← hWO, mem_preimage, hx]
      refine hball ?_
      rw [mem_ball, Subtype.dist_eq]
      simp only [Set.Icc.coe_zero, Real.dist_eq, sub_zero]
      rw [abs_of_nonneg ht.1]
      linarith [ht.2]
    have hxb : x ∉ bd S := fun h => disjoint_left.mp hAZ hA ⟨x, .inr h, hx⟩
    have hxG : x ∉ G.U := fun h => by
      by_cases hxe : x ∈ e
      · exact disjoint_left.mp hAL hA ⟨x, subset_closure hxe, hx⟩
      · exact disjoint_left.mp hAZ hA ⟨x, .inl ⟨h, hxe⟩, hx⟩
    exact ⟨x, ⟨hOD ⟨hxO, hxb⟩, hxG⟩, hx.symm⟩
  have hτm : τ ∈ Icc 0 τ := ⟨hτ.le, le_rfl⟩
  obtain ⟨w, hw, hwe⟩ := hgood τ hτm hτ
  have hmem0 : (0 : ℝ) ∈ Icc 0 τ := ⟨le_rfl, hτ.le⟩
  have hJ : JoinedIn (Icc 0 τ) (0 : ℝ) τ := ((convex_Icc 0 τ).isPathConnected ⟨0, hmem0⟩).joinedIn
    _ hmem0 _ hτm
  have hJ2 := hJ.map pth.continuous_extend.continuousOn
  have hext : ∀ t (ht : t ∈ Icc 0 τ), pth.extend t = pth ⟨t, hIcc t ht⟩ := fun t ht
    => pth.extend_apply (hIcc t ht)
  rw [hext τ hτm, hwe, pth.extend_zero] at hJ2
  refine ⟨w, _, hw.1, hw.2, hJ2, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  rcases ht.1.eq_or_lt with h0 | h0
  · rw [← h0, pth.extend_zero]
    exact .inl rfl
  · obtain ⟨x, hx, e'⟩ := hgood t ht h0
    rw [hext t ht, e']
    exact .inr ⟨x, hx, rfl⟩

/-- A drawing is an arc near each of its points that are not vertices. -/
theorem drawing_local_arc [T2Space S] {j : S → T} (hj : IsClosedEmbedding j)
  (G : Drawing S) {x : S} (hxU : x ∈ G.U) (hxV : x ∉ G.V) :
    ∃ (a : unitInterval → T) (W : Set T), IsArcMap a ∧ IsOpen W ∧ j x ∈ W ∧ j x ∈ a '' Ioo 0 1
      ∧ range a ⊆ j '' G.U ∧ j '' G.U ∩ W ⊆ range a := by
  obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem hxU hxV
  obtain ⟨γ, hγc, h0, h1, hinj, himg⟩ := exists_edge_param G he
  obtain ⟨t, ht, rfl⟩ := (himg ▸ hxe : x ∈ γ '' Ioo 0 1)
  have ht0 : (0 : ℝ) < t := ht.1
  have ht1 : (t : ℝ) < 1 := ht.2
  let φ : unitInterval → unitInterval := fun u =>
    ⟨(t.1 + u.1) / 2, by have := u.2.1; linarith, by have := u.2.2; linarith⟩
  have hφc : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hφ0 : ∀ u, 0 < φ u := fun u => by
    have h2 : 0 ≤ u.1 := u.2.1
    change (0 : ℝ) < (t.1 + u.1) / 2
    linarith
  have hφ1 : ∀ u, φ u < 1 := fun u => by
    have h2 : u.1 ≤ 1 := u.2.2
    change (t.1 + u.1) / 2 < (1 : ℝ)
    linarith
  have hφi : ∀ u, φ u ∈ Ioo (0 : unitInterval) 1 := fun u => ⟨hφ0 u, hφ1 u⟩
  have hφt : φ t = t := Subtype.ext (by simp only [φ]; ring)
  let a : unitInterval → T := fun u => j (γ (φ u))
  have ha : IsArcMap a := ⟨hj.continuous.comp (hγc.comp hφc), fun u v h => by
    have h2 := hinj (hφi u) (hφi v) (hj.injective h)
    have h3 : (t.1 + u.1) / 2 = (t.1 + v.1) / 2 := congrArg Subtype.val h2
    exact Subtype.ext (by linarith)⟩
  have hγe : ∀ u ∈ Ioo (0 : unitInterval) 1, γ u ∈ e := fun u hu => himg ▸ mem_image_of_mem γ hu
  let c₁ : unitInterval := ⟨t.1 / 2, by linarith, by linarith⟩
  let c₂ : unitInterval := ⟨(t.1 + 1) / 2, by linarith, by linarith⟩
  let Y₀ : Set S := (G.U \ e) ∪ γ '' Iic c₁ ∪ γ '' Ici c₂
  have hY₀ : IsClosed Y₀ := ((isClosed_U_sdiff_edge G he).union (isClosed_Iic.isCompact.image
    hγc).isClosed).union (isClosed_Ici.isCompact.image hγc).isClosed
  have hnot : ∀ r : unitInterval, γ r = γ t → r = t := fun r e' => by
    by_cases h2 : r ∈ Ioo (0 : unitInterval) 1
    · exact hinj h2 ht e'
    · exfalso
      have h3 : r = 0 ∨ r = 1 := by
        by_contra hn
        push Not at hn
        exact h2 ⟨unitInterval.pos_iff_ne_zero.mpr hn.1, unitInterval.lt_one_iff_ne_one.mpr hn.2⟩
      rcases h3 with rfl | rfl
      · exact hxV (e' ▸ h0)
      · exact hxV (e' ▸ h1)
  have hxY : γ t ∉ Y₀ := by
    rintro ((h2 | ⟨r, hr, e'⟩) | ⟨r, hr, e'⟩)
    · exact h2.2 hxe
    · rw [hnot r e'] at hr
      have : t.1 ≤ t.1 / 2 := hr
      linarith
    · rw [hnot r e'] at hr
      have : (t.1 + 1) / 2 ≤ t.1 := hr
      linarith
  refine ⟨a, (j '' Y₀)ᶜ, ha, (hj.isClosedMap _ hY₀).isOpen_compl, fun ⟨x', hx',
    e'⟩ => hxY (hj.injective e' ▸ hx'), ⟨t, ht, by simp only [a, hφt]⟩, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact ⟨_, (he.2.1 (hγe _ (hφi u))).1, rfl⟩
  · rintro _ ⟨⟨x', hx', rfl⟩, hW⟩
    have hx'Y : x' ∉ Y₀ := fun h => hW ⟨x', h, rfl⟩
    have hx'e : x' ∈ e := by
      by_contra h
      exact hx'Y (.inl (.inl ⟨hx', h⟩))
    obtain ⟨r, hr, rfl⟩ := (himg ▸ hx'e : x' ∈ γ '' Ioo 0 1)
    have h3 : c₁ < r := by
      by_contra h
      exact hx'Y (.inl (.inr ⟨r, not_lt.mp h, rfl⟩))
    have h4 : r < c₂ := by
      by_contra h
      exact hx'Y (.inr ⟨r, not_lt.mp h, rfl⟩)
    have h3' : t.1 / 2 < r.1 := h3
    have h4' : r.1 < (t.1 + 1) / 2 := h4
    refine ⟨⟨2 * r.1 - t.1, by linarith, by linarith⟩, ?_⟩
    have : φ ⟨2 * r.1 - t.1, by linarith, by linarith⟩ = r := Subtype.ext (by simp only [φ]; ring)
    simp only [a, this]

/-- **Joining two points of a disc.** Two points of `bd(Σ)` in the boundary of a disc, whose inside
misses `bd(Σ)`, are joined by a line through the
inside of the disc that meets the matching `G` in a finite set. -/
theorem exists_line_in_disc (hS : IsSurface S) {G : Drawing S} (hG : IsMatching G) {D : Set S}
  (hD : IsClosedDisc D) (hDb : Disjoint (discInt D) (bd S)) {y y' : S}
    (hne : y ≠ y') (hy : y ∈ bd S) (hy' : y' ∈ bd S) (hyD : y ∈ discBd D) (hyD' : y' ∈ discBd D)
      (hO : ∃ O, IsOpen O ∧ y ∈ O ∧ O \ bd S ⊆ discInt D)
    (hO' : ∃ O, IsOpen O ∧ y' ∈ O ∧ O \ bd S ⊆ discInt D) :
    ∃ P, IsLineWithEnds P y y' ∧ P ⊆ D ∧ P \ {y, y'} ⊆ discInt D ∧ (P ∩ G.U).Finite := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hN : Nonempty S := ⟨y⟩
  obtain ⟨T, tT, j, K, hT, hj, hK, hu, hi, -⟩ := exists_capAll S hS
  have ht2T : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have hstart : ∀ {x : S}, x ∈ bd S → x ∈ discBd D → (∃ O, IsOpen O ∧ x ∈ O ∧ O \ bd S ⊆ discInt D)
    →
      ∃ w K₀, w ∈ discInt D ∧ w ∉ G.U ∧ JoinedIn K₀ (j x) (j w) ∧ K₀ ⊆ {j x} ∪ j ''
        (discInt D \ G.U) := fun {x} hx hxD ⟨O, h1, h2, h3⟩ => by
    by_cases hxG : x ∈ G.U
    · exact exists_start_on hS hT hj hK hu hi hG hx hxG h1 h2 h3
    · exact exists_start_off hj.isEmbedding hD hxD G.isClosed_U hxG
  obtain ⟨w, K₁, hw, hwG, hJ₁, hK₁⟩ := hstart hy hyD hO
  obtain ⟨w', K₂, hw', hwG', hJ₂, hK₂⟩ := hstart hy' hyD' hO'
  let O' : Set T := j '' discInt D
  let Z' : Set T := j '' G.U
  have hdisc := hD.image_injOn hj.continuous.continuousOn hj.injective.injOn
  have hO'eq : O' = discInt (j '' D) := by
    change j '' (D \ discBd D) = j '' D \ discBd (j '' D)
    rw [hdisc.2, image_sdiff hj.injective]
  have hO'o : IsOpen O' := hO'eq ▸ hdisc.1.isOpen_discInt hman
  have hO'c : IsPreconnected O' := hD.isPreconnected_discInt.image j hj.continuous.continuousOn
  have hZ' : IsClosed Z' := hj.isClosedMap _ G.isClosed_U
  have hmemO : ∀ {x}, x ∈ discInt D → x ∉ G.U → j x ∈ O' \ Z' := fun {x} h1 h2 =>
    ⟨⟨x, h1, rfl⟩, fun ⟨x', h3, e⟩ => h2 (hj.injective e ▸ h3)⟩
  have hreach : FinReach O' Z' (j w) (j w') := finReach_of_connected hT hO'o hO'c hZ' (fun z hz
    => by
    obtain ⟨⟨x, hx, rfl⟩, ⟨x', hx', e⟩⟩ := hz
    obtain rfl := hj.injective e
    have hxV : x' ∉ G.V := fun h => disjoint_left.mp hDb hx (hG.2.1 h)
    exact drawing_local_arc hj G hx' hxV) (hmemO hw hwG) (hmemO hw' hwG')
  obtain ⟨K₃, h3O, h3Z, hJ₃⟩ := hreach
  have hJ : JoinedIn (K₁ ∪ K₃ ∪ K₂) (j y) (j y') :=
    ((hJ₁.mono (subset_union_left.trans subset_union_left)).trans (hJ₃.mono
      (subset_union_right.trans subset_union_left))).trans
      (hJ₂.symm.mono subset_union_right)
  have hne' : j y ≠ j y' := fun e => hne (hj.injective e)
  obtain ⟨L, hLs, hLl⟩ := ((joinedIn_iff_eq_or_exists_isLineWithEnds hJ.source_mem
    hJ.target_mem).mp hJ).resolve_left hne'
  have hKr : K₁ ∪ K₃ ∪ K₂ ⊆ range j := by
    rintro z ((hz | hz) | hz)
    · rcases hK₁ hz with rfl | ⟨x, -, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · obtain ⟨x, -, rfl⟩ := h3O hz
      exact ⟨_, rfl⟩
    · rcases hK₂ hz with rfl | ⟨x, -, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  obtain ⟨u', v', e1, e2, hl⟩ := hLl.pull hj.isEmbedding (hLs.trans hKr)
  obtain rfl := hj.injective e1
  obtain rfl := hj.injective e2
  have hinner : ∀ x ∈ j ⁻¹' L, x ≠ u' → x ≠ v' → x ∈ discInt D := fun x hx h1 h2 => by
    rcases hLs hx with (h3 | h3) | h3
    · rcases hK₁ h3 with h4 | ⟨x', h4, e⟩
      · exact (h1 (hj.injective h4)).elim
      · exact hj.injective e ▸ h4.1
    · obtain ⟨x', h4, e⟩ := h3O h3
      exact hj.injective e ▸ h4
    · rcases hK₂ h3 with h4 | ⟨x', h4, e⟩
      · exact (h2 (hj.injective h4)).elim
      · exact hj.injective e ▸ h4.1
  refine ⟨j ⁻¹' L, hl, fun x hx => ?_, fun x hx => hinner x hx.1 (fun e => hx.2 (.inl e)) (fun e
    => hx.2 (.inr e)), ?_⟩
  · by_cases h1 : x = u'
    · exact h1 ▸ GM11.discBd_subset _ hyD
    by_cases h2 : x = v'
    · exact h2 ▸ GM11.discBd_subset _ hyD'
    exact (hinner x hx h1 h2).1
  · have hfin : (({j u', j v'} : Set T) ∪ (K₃ ∩ Z')).Finite := (by simp :
      ({j u', j v'} : Set T).Finite).union h3Z
    refine Finite.of_finite_image (hfin.subset ?_) hj.injective.injOn
    rintro _ ⟨x, ⟨hx, hxG⟩, rfl⟩
    by_cases h1 : x = u'
    · exact .inl (.inl (congrArg j h1))
    by_cases h2 : x = v'
    · exact .inl (.inr (congrArg j h2))
    rcases hLs hx with (h3 | h3) | h3
    · rcases hK₁ h3 with h4 | ⟨x', h4, e⟩
      · exact (h1 (hj.injective h4)).elim
      · exact (h4.2 (hj.injective e ▸ hxG)).elim
    · exact .inr ⟨h3, x, hxG, rfl⟩
    · rcases hK₂ h3 with h4 | ⟨x', h4, e⟩
      · exact (h2 (hj.injective h4)).elim
      · exact (h4.2 (hj.injective e ▸ hxG)).elim

/-- **Graph Minors VII, (3.5) (page 221).** For a matching `G` and a forest `H₀`, some forest
homoplastic to `H₀` meets `G` in a finite set. The paper leaves the
proof to the reader. The route is in the module docstring. -/
theorem exists_finite_forest (hS : IsSurface S) {G H₀ : Drawing S} (hG : IsMatching G)
  (hH : IsSurfaceForest H₀) :
    ∃ H : Drawing S, IsSurfaceForest H ∧ ForestsHomoplastic H₀ H ∧ (G.U ∩ H.U).Finite := by
  classical
  have ht2 : T2Space S := hS.2.1
  rcases isEmpty_or_nonempty S with hE | hN
  · refine ⟨H₀, hH, ⟨Homeomorph.refl S, fun _ _ => rfl, ?_⟩, ?_⟩
    · rw [mapDrawingHomeo_refl]
      exact ⟨hH.1, hH.1, hH.2, hH.2, rfl, fun s => (hE.false s).elim⟩
    · refine (finite_empty (α := S)).subset fun x _ => (hE.false x).elim
  have : Inhabited S := ⟨hN.some⟩
  let Y : Set S := H₀.V ∩ bd S
  have hYf : Y.Finite := H₀.finite_V.subset inter_subset_left
  have hYb : Y ⊆ bd S := inter_subset_right
  obtain ⟨f, ε, hm, hd⟩ := exists_marks hS hYb hYf
  obtain ⟨c, -, -, G₁, -, -, -, hG₀, hdisc, hdj, hdb, hall⟩ := exists_thick_matching hS hH rfl hm hd
  have hsame : ∀ {u v z}, u ∈ Y → v ∈ Y → z ∈ c u → z ∈ c v → c u = c v := fun {u v z} hu hv h1 h2
    => by
    by_contra hn
    exact disjoint_left.mp (hdj u hu v hv hn) h1 h2
  have hyc : ∀ y ∈ Y, y ∈ c y := fun y hy => GM11.discBd_subset _ (hdisc y hy).2.1
  let 𝒟 : Set (Set S) := c '' Y
  have hrep : ∀ D ∈ 𝒟, ∃ r ∈ Y, c r = D := fun D ⟨r, hr, e⟩ => ⟨r, hr, e⟩
  choose! rep hrepY hrepc using hrep
  let R : Set S := rep '' 𝒟
  have hRf : R.Finite := (hYf.image c).image rep
  have hRY : R ⊆ Y := by
    rintro _ ⟨D, hD, rfl⟩
    exact hrepY D hD
  let Q : Set S := ⋃ y ∈ Y, discInt (c y)
  have hYQ : Disjoint Y Q := disjoint_left.mpr fun z hz hzQ => by
    obtain ⟨y, hy, h1⟩ := mem_iUnion₂.mp hzQ
    exact disjoint_left.mp (hdb y hy) h1 hz.2
  obtain ⟨V, 𝓛, hgrow, hYV, hreach⟩ := exists_grown (Z := G.U) (Q := Q) (𝒟 := 𝒟) hRf hYf hRY hYQ
    (fun y hy hyR => by
    have hD : c y ∈ 𝒟 := ⟨y, hy, rfl⟩
    let r := rep (c y)
    have hrY : r ∈ Y := hrepY _ hD
    have hrc : c r = c y := hrepc _ hD
    have hne : y ≠ r := fun e => hyR (e ▸ ⟨_, hD, rfl⟩)
    have h1 := hdisc y hy
    have h2 := hdisc r hrY
    rw [hrc] at h2
    obtain ⟨P, hl, hPD, hPQ, hPZ⟩ := exists_line_in_disc hS hG h1.1 (hdb y hy) hne (hYb hy)
      (hYb hrY) h1.2.1 h2.2.1 h1.2.2 h2.2.2
    exact ⟨r, ⟨_, hD, rfl⟩, P, c y, hD, hl, hPD, fun z hz => mem_iUnion₂.mpr ⟨y, hy, hPQ hz⟩, hPZ⟩)
  have hline : ∀ A ∈ 𝓛, ∃ a b, IsLineWithEnds A a b ∧ a ≠ b ∧ A ∩ V = {a, b} := hgrow.line
  choose! ea eb hla hne hVA using hline
  obtain ⟨H, hHU, hHV, hHE⟩ := GM12.exists_drawing_of_finite_lines hgrow.finV hgrow.finL id ea eb
    hla hne hVA
    fun A hA A' hA' h => hgrow.meet A hA A' hA' h
  have hUeq : H.U = grownU V 𝓛 := by
    rw [hHU, grownU, sUnion_eq_biUnion]
    rfl
  have hUsub : H.U ⊆ Y ∪ Q := by
    rw [hUeq]
    rintro z (hz | ⟨A, hA, hz⟩)
    · exact hgrow.subV hz
    · exact hgrow.subL A hA hz
  have hQb : ∀ z ∈ Q, z ∉ bd S := fun z hz hb => by
    obtain ⟨y, hy, h1⟩ := mem_iUnion₂.mp hz
    exact disjoint_left.mp (hdb y hy) h1 hb
  have hHYeq : H.V ∩ bd S = Y := by
    rw [hHV]
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      rcases hgrow.subV h1 with h3 | h3
      · exact h3
      · exact (hQb z h3 h2).elim
    · exact fun h => ⟨hYV h, hYb h⟩
  have hHf : IsSurfaceForest H := by
    refine ⟨fun z hz => ?_, isGraphForest_of_noOArc fun F hF hsub => hgrow.noO F hF (hUeq ▸ hsub)⟩
    rw [hHV]
    rcases hUsub hz.2 with h1 | h1
    · exact hYV h1
    · exact (hQb z h1 hz.1).elim
  have hAclo : ∀ A ∈ 𝓛, closure (A \ {ea A, eb A}) = A := fun A hA =>
    subset_antisymm (closure_minimal sdiff_subset (hla A hA).isCompact.isClosed)
      (hla A hA).subset_closure_diff
  -- Lines stay in one disc.
  have hAdisc : ∀ A ∈ 𝓛, ∀ y ∈ Y, ∀ u ∈ A, u ∈ c y → A ⊆ c y := fun A hA y hy u hu huy => by
    obtain ⟨_, ⟨y', hy', rfl⟩, hA'⟩ := hgrow.disc A hA
    rw [hsame hy hy' huy (hA' hu)]
    exact hA'
  have hadjc : ∀ y ∈ Y, ∀ u v, GrownAdj V 𝓛 u v → u ∈ c y → v ∈ c y := fun y hy u v ⟨A, hA, hc⟩ hu
    => by
    have hu' : u ∈ A := (hc ▸ (Or.inl rfl) : u ∈ A ∩ V).1
    have hv' : v ∈ A := (hc ▸ (Or.inr rfl) : v ∈ A ∩ V).1
    exact hAdisc A hA y hy u hu' hu hv'
  have hreachc : ∀ y ∈ Y, ∀ {u v}, Relation.ReflTransGen (GrownAdj V 𝓛) u v → u ∈ c y → v ∈ c y
    := fun y hy {u v} h hu => by
    induction h with
    | refl => exact hu
    | tail _ h2 ih => exact hadjc y hy _ _ h2 ih
  have hadjW : ∀ u v, GrownAdj V 𝓛 u v → Nonempty (GraphWalk H.toGraph u v) := fun u v ⟨A, hA, hc⟩
    => by
    have hu : u ∈ V := (hc ▸ (Or.inl rfl) : u ∈ A ∩ V).2
    have hv : v ∈ V := (hc ▸ (Or.inr rfl) : v ∈ A ∩ V).2
    have hu' : u ∈ H.V := hHV ▸ hu
    have hv' : v ∈ H.V := hHV ▸ hv
    have hE : A \ {ea A, eb A} ∈ H.E := hHE ▸ ⟨A, hA, rfl⟩
    have hlink : H.toGraph.IsLink (A \ {ea A, eb A}) u v :=
      ⟨hE, hu', hv', by rw [hAclo A hA, hHV]; exact hc⟩
    exact ⟨.cons hlink (.nil hv')⟩
  have hreachW : ∀ {u v}, Relation.ReflTransGen (GrownAdj V 𝓛) u v → u ∈ V → Nonempty
    (GraphWalk H.toGraph u v) := fun {u v} h hu => by
    induction h with
    | refl =>
      have hu' : u ∈ H.V := hHV ▸ hu
      exact ⟨.nil hu'⟩
    | tail _ h2 ih =>
      obtain ⟨W⟩ := ih
      obtain ⟨W'⟩ := hadjW _ _ h2
      exact ⟨W.append W'⟩
  have hRuniq : ∀ r ∈ R, ∀ r' ∈ R, c r = c r' → r = r' := by
    rintro _ ⟨D, hD, rfl⟩ _ ⟨D', hD', rfl⟩ e
    rw [hrepc D hD, hrepc D' hD'] at e
    rw [e]
  have hRY' : ∀ r ∈ R, r ∈ Y := fun r hr => hRY hr
  have hG₁H : MatchingStrictlySurroundsForest G₁ H := by
    refine hall H hHYeq (fun u hu v hv huv => ?_) (fun e he u hu y hy huc huy => ?_)
      (fun y hy z hz hzb => ?_)
    · obtain ⟨r, hr, h1⟩ := hreach u (hYV hu)
      obtain ⟨r', hr', h2⟩ := hreach v (hYV hv)
      have h3 : r ∈ c u := hreachc u hu h1 (hyc u hu)
      have h4 : r' ∈ c v := hreachc v hv h2 (hyc v hv)
      have h5 : c r = c r' := (hsame (hRY' r hr) hu (hyc r (hRY' r hr)) h3).trans
        (huv.trans (hsame (hRY' r' hr') hv (hyc r' (hRY' r' hr')) h4).symm)
      have h6 := hRuniq r hr r' hr' h5
      rw [← h6] at h2
      obtain ⟨W₁⟩ := hreachW h1 (hYV hu)
      obtain ⟨W₂⟩ := hreachW h2 (hYV hv)
      exact ⟨W₁.append W₂.reverse⟩
    · rw [hHE] at he
      obtain ⟨A, hA, rfl⟩ := he
      simp only [id] at huc ⊢
      rw [hAclo A hA] at huc ⊢
      exact hAdisc A hA y hy u huc huy
    · rcases hUsub hz with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨y', hy', h2⟩ := mem_iUnion₂.mp h1
        have h3 := hsame hy hy' (GM11.discBd_subset _ hzb) h2.1
        exact h2.2 (h3 ▸ hzb)
  have hhom : ForestsHomotopic H₀ H := theorem_3_4_claim_2 hS ⟨hH, rfl⟩ ⟨hHf, hHYeq⟩ hG₀ hG₁H
  refine ⟨H, hHf, ⟨Homeomorph.refl S, fun _ _ => rfl, by rw [mapDrawingHomeo_refl]; exact hhom⟩, ?_⟩
  rw [inter_comm, hUeq]
  exact hgrow.finZ

/-- Graph Minors VII, (3.5) (page 221), as the statement used in Sections 3, 7, and 9. -/
theorem forestMatchingFiniteIntersection.{u} : ForestMatchingFiniteIntersectionStatement.{u} := by
  intro S _ hS G H₀ hG hH
  obtain ⟨S₀, tS₀, ⟨β⟩⟩ := exists_homeo_type_zero hS
  have hS₀ : IsSurface S₀ := isSurface_of_homeo β hS
  obtain ⟨H', hH'_forest, hH'_homo, hH'_fin⟩ :=
    exists_finite_forest hS₀ (hG.map_homeo β) (IsSurfaceForest.map_homeo β hH)
  refine ⟨mapDrawingHomeo β.symm H', IsSurfaceForest.map_homeo β.symm hH'_forest,
    hH'_homo.conj_homeo β, ?_⟩
  have hinter : G.U ∩ (mapDrawingHomeo β.symm H').U =
      β.symm '' ((mapDrawingHomeo β G).U ∩ H'.U) := by
    rw [image_inter β.symm.injective]
    change G.U ∩ β.symm '' H'.U = β.symm '' (β '' G.U) ∩ β.symm '' H'.U
    congr 1
    ext z
    simp
  rw [hinter]
  exact hH'_fin.image β.symm

section Section3Main

universe u

variable {S' : Type u} [TopologicalSpace S']

/-- Graph Minors VII, (3.4), Claim (1) (page 220):
"(1) *Every $Y$-forest is surrounded by some $X$-matching.*" -/
theorem theorem_3_4_claim_1
    (hS : IsSurface S') {Y : Set S'} (hY : Y ⊆ bd S') (hYfin : Y.Finite) :
    ∃ X : Set S', X ⊆ bd S' ∧ X.Finite ∧ X.ncard = 2 * Y.ncard ∧
      ∀ H : Drawing S', IsYForest Y H →
        ∃ G : Drawing S', IsXMatching X G ∧ MatchingStrictlySurroundsForest G H :=
  forestSurroundingMatching S' hS hY hYfin

/-- Graph Minors VII, (3.4) (page 220):
"(3.4) *For any surface $\Sigma$ and finite $Y \subseteq bd(\Sigma)$, there are only finitely many
homoplasty classes of $Y$-forests.*" -/
theorem theorem_3_4_proof
    (hS : IsSurface S') {Y : Set S'} (hY : Y ⊆ bd S') (hYfin : Y.Finite) :
    ∃ 𝓗 : Set (Drawing S'), 𝓗.Finite ∧
      (∀ H₀ ∈ 𝓗, IsYForest Y H₀) ∧
      ∀ H : Drawing S', IsYForest Y H → ∃ H₀ ∈ 𝓗, ForestsHomoplastic H₀ H := by
  obtain ⟨X, hX_bd, hX_fin, _, hX_surr⟩ := theorem_3_4_claim_1 hS hY hYfin
  obtain ⟨𝓜, h𝓜_fin, h𝓜_match, h𝓜_cov⟩ := theorem_3_3_proof hS hX_bd hX_fin
  let good (G₀ : Drawing S') : Prop :=
    ∃ H₀ : Drawing S', IsYForest Y H₀ ∧
      ∃ G : Drawing S', IsXMatching X G ∧ MatchingStrictlySurroundsForest G H₀ ∧
        AreCongruentMatchings G₀ G
  set 𝓜' : Set (Drawing S') := {G₀ ∈ 𝓜 | good G₀}
  have h𝓜'_fin : 𝓜'.Finite := h𝓜_fin.subset (sep_subset 𝓜 good)
  have h_rep : ∀ G₀ ∈ 𝓜', ∃ H₀ : Drawing S', IsYForest Y H₀ ∧
      ∃ G : Drawing S', IsXMatching X G ∧ MatchingStrictlySurroundsForest G H₀ ∧
        AreCongruentMatchings G₀ G := fun _ h => h.2
  choose! rep hrep_Y hrep_G using h_rep
  refine ⟨rep '' 𝓜', h𝓜'_fin.image rep, ?_, ?_⟩
  · rintro _ ⟨G₀, hG₀, rfl⟩
    exact hrep_Y G₀ hG₀
  · intro H hH
    obtain ⟨G, hG_match, hG_surr⟩ := hX_surr H hH
    obtain ⟨G₀, hG₀_mem, hG₀_congr⟩ := h𝓜_cov G hG_match
    have hG₀_good : G₀ ∈ 𝓜' := ⟨hG₀_mem, ⟨H, hH, G, hG_match, hG_surr, hG₀_congr⟩⟩
    obtain ⟨G_rep, _, hG_rep_surr, ⟨α₁, hα₁_U, hα₁_bd⟩⟩ := hrep_G G₀ hG₀_good
    rcases hG₀_congr with ⟨α₂, hα₂_U, hα₂_bd⟩
    have hcongr : AreCongruentMatchings G_rep G := by
      refine ⟨α₁.symm.trans α₂, ?_, fun x hx => ?_⟩
      · calc
          (α₁.symm.trans α₂) '' G_rep.U = α₂ '' (α₁.symm '' (α₁ '' G₀.U)) := by
            rw [← hα₁_U]; ext y; simp [Homeomorph.trans_apply]
          _ = α₂ '' G₀.U := by congr 1; exact α₁.symm_image_image G₀.U
          _ = G.U := hα₂_U
      · have hx1 : α₁.symm x = x := (α₁.symm_apply_eq).mpr (hα₁_bd x hx).symm
        simp [Homeomorph.trans_apply, hx1, hα₂_bd x hx]
    exact ⟨rep G₀, mem_image_of_mem rep hG₀_good,
      theorem_3_4_claim_3 hS hY (hrep_Y G₀ hG₀_good) hH hG_rep_surr hG_surr hcongr⟩

/-- Graph Minors VII, (3.5) (page 221):
"(3.5) *For every matching $G$ in $\Sigma$ and every homoplasty class $\mathscr{B}$ there exists
$H \in \mathscr{B}$ with $U(G) \cap U(H)$ finite.*" -/
theorem theorem_3_5_proof
    (hS : IsSurface S') (G H₀ : Drawing S') (hG : IsMatching G) (hH₀ : IsSurfaceForest H₀) :
    ∃ H : Drawing S', IsSurfaceForest H ∧ ForestsHomoplastic H₀ H ∧ (G.U ∩ H.U).Finite :=
  forestMatchingFiniteIntersection S' hS G H₀ hG hH₀

/-- Theorem (3.6) for a fixed pair of finite subsets `X, Y ⊆ bd S'`. -/
theorem theorem_3_6_fixed_XY
    (hS : IsSurface S') {X Y : Set S'} (hX : X ⊆ bd S') (hXfin : X.Finite)
    (hY : Y ⊆ bd S') (hYfin : Y.Finite) :
    ∃ w : ℕ, ∀ (G H : Drawing S'), IsXMatching X G → IsYForest Y H →
      ∃ H' : Drawing S', IsSurfaceForest H' ∧ ForestsHomoplastic H H' ∧
        (G.U ∩ H'.U).Finite ∧ (G.U ∩ H'.U).ncard ≤ w := by
  classical
  obtain ⟨𝓜, h𝓜_fin, h𝓜_match, h𝓜_cov⟩ := theorem_3_3_proof hS hX hXfin
  obtain ⟨𝓗, h𝓗_fin, h𝓗_forest, h𝓗_cov⟩ := theorem_3_4_proof hS hY hYfin
  have h_pair : ∀ (G₀ : Drawing S'), G₀ ∈ 𝓜 → ∀ (H₀ : Drawing S'), H₀ ∈ 𝓗 →
      ∃ H₁ : Drawing S', IsSurfaceForest H₁ ∧ ForestsHomoplastic H₀ H₁ ∧
        (G₀.U ∩ H₁.U).Finite :=
    fun G₀ hG₀ H₀ hH₀ => theorem_3_5_proof hS G₀ H₀ (h𝓜_match G₀ hG₀).1 (h𝓗_forest H₀ hH₀).1
  choose! repH hrep_forest hrep_homo hrep_fin using h_pair
  let pairBound (p : Drawing S' × Drawing S') : ℕ := (p.1.U ∩ (repH p.1 p.2).U).ncard
  let B : Set ℕ := pairBound '' (𝓜 ×ˢ 𝓗)
  have hB_fin : B.Finite := (h𝓜_fin.prod h𝓗_fin).image pairBound
  let w : ℕ := hB_fin.toFinset.sup id
  refine ⟨w, fun G H hG hH => ?_⟩
  obtain ⟨G₀, hG₀_mem, ⟨α, hα_U, hα_bd⟩⟩ := h𝓜_cov G hG
  obtain ⟨H₀, hH₀_mem, hH₀_homo⟩ := h𝓗_cov H hH
  let H₁ := repH G₀ H₀
  have hH₁_forest : IsSurfaceForest H₁ := hrep_forest G₀ hG₀_mem H₀ hH₀_mem
  have hH₁_homo : ForestsHomoplastic H₀ H₁ := hrep_homo G₀ hG₀_mem H₀ hH₀_mem
  have hH₁_fin : (G₀.U ∩ H₁.U).Finite := hrep_fin G₀ hG₀_mem H₀ hH₀_mem
  have hH₁_le : (G₀.U ∩ H₁.U).ncard ≤ w := by
    have h_mem : pairBound (G₀, H₀) ∈ hB_fin.toFinset :=
      hB_fin.mem_toFinset.mpr ⟨(G₀, H₀), ⟨hG₀_mem, hH₀_mem⟩, rfl⟩
    exact Finset.le_sup (f := id) h_mem
  let H' := mapDrawingHomeo α H₁
  have h_inter : G.U ∩ H'.U = α '' (G₀.U ∩ H₁.U) := by
    rw [← hα_U]
    exact (image_inter α.injective).symm
  refine ⟨H', IsSurfaceForest.map_homeo α hH₁_forest,
    hH₀_homo.symm.trans (hH₁_homo.map_right α hα_bd),
    h_inter ▸ hH₁_fin.image α, ?_⟩
  rw [h_inter, ncard_image_of_injective _ α.injective]
  exact hH₁_le

/-- Existence of a bound `w` satisfying `IsW36Bound S' k n w`. -/
theorem exists_isW36Bound
    (hS : IsSurface S') (k n : ℕ) :
    ∃ w : ℕ, IsW36Bound S' k n w := by
  classical
  obtain ⟨Z_canon, hZ_bd, hZ_fin, hZ_move⟩ := exists_canon_bd_homeo hS (2 * n + k)
  let P := 𝒫 Z_canon ×ˢ 𝒫 Z_canon
  have hP_fin : P.Finite := hZ_fin.powerset.prod hZ_fin.powerset
  have h_sub : ∀ p ∈ P, ∃ w_p : ℕ,
      ∀ (G H : Drawing S'), IsXMatching p.1 G → IsYForest p.2 H →
        ∃ H' : Drawing S', IsSurfaceForest H' ∧ ForestsHomoplastic H H' ∧
          (G.U ∩ H'.U).Finite ∧ (G.U ∩ H'.U).ncard ≤ w_p := by
    rintro ⟨X₀, Y₀⟩ ⟨hX₀, hY₀⟩
    exact theorem_3_6_fixed_XY hS
      (hX₀.trans hZ_bd) (hZ_fin.subset hX₀)
      (hY₀.trans hZ_bd) (hZ_fin.subset hY₀)
  choose! w_sub hw_sub using h_sub
  let B : Set ℕ := w_sub '' P
  have hB_fin : B.Finite := hP_fin.image w_sub
  let w : ℕ := hB_fin.toFinset.sup id
  refine ⟨w, fun G H hG hGcard hH hHcard => ?_⟩
  let X := G.V
  let Y := H.V ∩ bd S'
  have hX : X ⊆ bd S' := hG.2.1
  have hY : Y ⊆ bd S' := inter_subset_right
  have hX_fin : X.Finite := G.finite_V
  have hY_fin : Y.Finite := H.finite_V.subset inter_subset_left
  have hXY_bd : X ∪ Y ⊆ bd S' := union_subset hX hY
  have hXY_fin : (X ∪ Y).Finite := hX_fin.union hY_fin
  have hXY_card : (X ∪ Y).ncard ≤ 2 * n + k :=
    (ncard_union_le X Y).trans (add_le_add hGcard hHcard)
  obtain ⟨β, hβ_XY⟩ := hZ_move (X ∪ Y) hXY_bd hXY_fin hXY_card
  let X₀ := β '' X
  let Y₀ := β '' Y
  have hX₀_Z : X₀ ⊆ Z_canon := (image_mono subset_union_left).trans hβ_XY
  have hY₀_Z : Y₀ ⊆ Z_canon := (image_mono subset_union_right).trans hβ_XY
  have hp_mem : (X₀, Y₀) ∈ P := ⟨hX₀_Z, hY₀_Z⟩
  have hGX : IsXMatching X G := ⟨hG, rfl⟩
  have hHY : IsYForest Y H := ⟨hH, rfl⟩
  obtain ⟨H₁', hH₁'_forest, hH₁'_homo, hH₁'_fin, hH₁'_le⟩ :=
    hw_sub (X₀, Y₀) hp_mem (mapDrawingHomeo β G) (mapDrawingHomeo β H)
      (hGX.map_homeo β) (hHY.map_homeo β)
  let H' := mapDrawingHomeo β.symm H₁'
  have h_inter : G.U ∩ H'.U = β.symm '' ((mapDrawingHomeo β G).U ∩ H₁'.U) := by
    rw [image_inter β.symm.injective]
    change G.U ∩ β.symm '' H₁'.U = β.symm '' (β '' G.U) ∩ β.symm '' H₁'.U
    congr 1
    ext z
    simp
  have hw_le : w_sub (X₀, Y₀) ≤ w := by
    have h_in : w_sub (X₀, Y₀) ∈ hB_fin.toFinset :=
      hB_fin.mem_toFinset.mpr ⟨(X₀, Y₀), hp_mem, rfl⟩
    exact Finset.le_sup (f := id) h_in
  refine ⟨H', IsSurfaceForest.map_homeo β.symm hH₁'_forest,
    hH₁'_homo.conj_homeo β,
    h_inter ▸ hH₁'_fin.image β.symm, ?_⟩
  rw [h_inter, ncard_image_of_injective _ β.symm.injective]
  exact hH₁'_le.trans hw_le

/-- Graph Minors VII, (3.6) (page 221):
"(3.6) *For every surface $\Sigma$ and all integers $k, n \ge 0$ there is an integer
$w(\Sigma, k, n)$ such that for every matching $G$ in $\Sigma$ with $|V(G)| \le 2n$ and every
forest $H$ in $\Sigma$ with $|V(H) \cap bd(\Sigma)| \le k$, there is a forest $H'$ homoplastic to
$H$ with $|U(G) \cap U(H')| \le w(\Sigma, k, n)$.*" -/
theorem theorem_3_6_proof
    (hS : IsSurface S') (k n : ℕ) :
    IsW36Bound S' k n (wSurface S' k n) := by
  have hne : {w : ℕ | IsW36Bound S' k n w}.Nonempty := exists_isW36Bound hS k n
  exact Nat.sInf_mem hne

end Section3Main

end GraphMinor.GM07
