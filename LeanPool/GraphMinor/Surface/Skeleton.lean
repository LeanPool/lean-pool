/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# A skeleton of a closed surface

Starting from a given graph in a connected closed surface, `exists_skeleton` adds round curves of
charts, moved a
little so that they meet the graph in a finite way, until the closed discs that they bound cover the
surface. The new
curves form a set `G` that stays connected when one point is removed. No connecting arcs are needed:
`G` has a point
inside and a point outside each new disc, so the new curve must meet `G` twice.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

local notation "𝕀" => unitInterval

variable {S : Type u} [TopologicalSpace S]

/-- An arc has no interior in a surface. -/
theorem not_image_ball_subset_arc [T2Space S] {γ : 𝕀 → S} (hγ : IsArcMap γ) {w : ℂ} {ρ : ℝ}
  (hρ : 0 < ρ)
    {g : ℂ → S} (hgc : ContinuousOn g (ball w ρ)) (hgi : InjOn g (ball w ρ)) : ¬ g '' ball w ρ ⊆
      range γ := by
  intro hsub
  obtain ⟨k, hk1, hk2⟩ := exists_inv_of_compactOn isCompact_univ hγ.1.continuousOn hγ.2.injOn
  rw [image_univ] at hk1
  have hcirc : IsOArc (univ : Set Circle) := ⟨(Homeomorph.Set.univ Circle).symm⟩
  let g' : ℂ → Circle := fun z => Circle.exp (k (g z))
  refine not_image_ball_subset_oArc hcirc (w := w) hρ (g := g') ?_ ?_ (subset_univ _)
  · have h1 : ContinuousOn (fun z => k (g z)) (ball w ρ) := hk1.comp hgc fun z hz
    => hsub ⟨z, hz, rfl⟩
    exact Circle.exp.continuous.comp_continuousOn (continuous_subtype_val.comp_continuousOn h1)
  · intro z hz z' hz' he
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
    have hpi := Real.pi_gt_three
    have b0 := (k (g z)).2.1
    have b1 := (k (g z)).2.2
    have b2 := (k (g z')).2.1
    have b3 := (k (g z')).2.2
    have hm0 : m = 0 := by
      by_contra hne
      have h6 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hne
      have h7 : |(m : ℝ) * (2 * Real.pi)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul, abs_of_pos (show 0 < 2 * Real.pi by positivity)] at h7
      nlinarith
    subst hm0
    have h8 : k (g z) = k (g z') := Subtype.ext (by simpa using hm)
    obtain ⟨s, hs⟩ := hsub ⟨z, hz, rfl⟩
    obtain ⟨s', hs'⟩ := hsub ⟨z', hz', rfl⟩
    rw [← hs, ← hs', hk2 (mem_univ s), hk2 (mem_univ s')] at h8
    refine hgi hz hz' ?_
    rw [← hs, ← hs', h8]

/-- A nonempty open set of a surface has a point off finitely many arcs. -/
theorem exists_off_arcs [T2Space S] (_hman : ∀ x : S, IsManifoldPoint x) {U : Set S} {h : S
  → ℂ} {g : ℂ → S} {R : ℝ}
    (c : BallChart R U h g) (L : List (𝕀 → S)) (hL : ∀ γ ∈ L, IsArcMap γ) :
    ∀ W : Set ℂ, IsOpen W → W ⊆ ball 0 R → W.Nonempty → ∃ w ∈ W, ∀ γ ∈ L, g w ∉ range γ := by
  induction L with
  | nil =>
    rintro W - - ⟨w, hw⟩
    exact ⟨w, hw, by simp⟩
  | cons γ L ih =>
    intro W hW hsub hne
    have hγ : IsArcMap γ := hL γ (by simp)
    obtain ⟨w, hw⟩ := hne
    obtain ⟨ρ, hρ, hb⟩ := Metric.isOpen_iff.mp hW w hw
    have hn := not_image_ball_subset_arc hγ hρ (g := g) (c.gc.mono (hb.trans hsub))
      (c.hg.injOn.mono (hb.trans hsub))
    obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := not_subset.mp hn
    have hopen : IsOpen (W ∩ g ⁻¹' (range γ)ᶜ) :=
      (c.gc.mono hsub).isOpen_inter_preimage hW (isCompact_range hγ.1).isClosed.isOpen_compl
    obtain ⟨w', hw', hoff⟩ := ih (fun γ' hγ' => hL γ' (by simp [hγ'])) _ hopen
      (inter_subset_left.trans hsub)
      ⟨z, hb hz, hz'⟩
    refine ⟨w', hw'.1, fun γ' hγ' => ?_⟩
    rcases List.mem_cons.mp hγ' with rfl | h'
    · exact hw'.2
    · exact hoff γ' h'

/-- A curve around the ball of radius `2` of a chart, which meets finitely many given arcs in a
finite way. -/
theorem exists_tame_curve' [CompactSpace S] [T2Space S] (hman : ∀ x : S, IsManifoldPoint x)
    {U : Set S} {h : S → ℂ} {g : ℂ → S} (c : BallChart 3 U h g) (G : List (𝕀 → S))
      (hG : ∀ γ ∈ G, IsArcMap γ) :
    ∃ P E : Set S, IsOArc P ∧ FinConn (P \ ⋃ γ ∈ G, range γ) ∧ IsClosedDisc E ∧ discBd E = P ∧
      g '' closedBall 0 2 ⊆ E ∧ E ⊆ U ∧ Disjoint P (g '' closedBall 0 2) := by
  let Ω₀ : Set ℂ := {z | 2 < ‖z‖ ∧ ‖z‖ < 3}
  have hΩ₀ : IsOpen Ω₀ := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hΩ₀b : Ω₀ ⊆ ball 0 3 := fun z hz => mem_ball_zero_iff.mpr hz.2
  have hne : Ω₀.Nonempty := ⟨((5 / 2 : ℝ) : ℂ), by
    simp only [Ω₀, mem_ofPred_eq, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num)]
    norm_num⟩
  obtain ⟨w, hwΩ, hw⟩ := exists_off_arcs hman c G hG Ω₀ hΩ₀ hΩ₀b hne
  have hcl : IsClosed (⋃ γ ∈ G, range γ) := by
    refine G.finite_toSet.isClosed_biUnion fun γ hγ => (isCompact_range (hG γ hγ).1).isClosed
  have hopen : IsOpen (Ω₀ ∩ g ⁻¹' (⋃ γ ∈ G, range γ)ᶜ) :=
    (c.gc.mono hΩ₀b).isOpen_inter_preimage hΩ₀ hcl.isOpen_compl
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen w ⟨hwΩ, by simpa using hw⟩
  let u : Circle := Circle.exp (Complex.arg w)
  have huw : (u : ℂ) * (‖w‖ : ℝ) = w := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rw [Circle.coe_exp, mul_comm]
    exact this
  have hcan : ∀ z : ℂ, (u : ℂ) * (((u⁻¹ : Circle) : ℂ) * z) = z := fun z => by
    rw [← mul_assoc, ← Circle.coe_mul]
    simp
  have hmulcl : ∀ {t : ℝ} {z : ℂ}, z ∈ closedBall (0 : ℂ) t →
      ((u⁻¹ : Circle) : ℂ) * z ∈ closedBall (0 : ℂ) t :=
    fun hz => by simpa [norm_mul] using hz
  have hmulcl' : ∀ {t : ℝ} {z : ℂ}, z ∈ closedBall (0 : ℂ) t → (u : ℂ) * z ∈ closedBall (0 : ℂ) t :=
    fun hz => by simpa [norm_mul] using hz
  have himg : (fun z => g ((u : ℂ) * z)) '' closedBall 0 2 = g '' closedBall 0 2 := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, hmulcl' hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, hmulcl hz, by simp only [hcan]⟩
  obtain ⟨P, E, h1, h2, h3, h4, h5, h6, h7⟩ := exists_tame_curve hman (c.rotate u) G hG (r := ‖w‖)
    (ρ := ρ)
    hwΩ.1 hwΩ.2 hρ (fun z hz γ hγ => by
      have h8 : (u : ℂ) * z ∈ ball w ρ := by
        rw [mem_ball, ← huw, dist_eq_norm, ← mul_sub, norm_mul, Circle.norm_coe, one_mul, ←
          dist_eq_norm]
        exact hz
      have h9 := (hball h8).2
      simp only [mem_preimage, mem_compl_iff, mem_iUnion, not_exists] at h9
      exact h9 γ hγ)
  rw [himg] at h5 h7
  exact ⟨P, E, h1, h2, h3, h4, h5, h6, h7⟩

theorem IsGraph.exists_list {V : Set S} {E : Set (Set S)} (h : IsGraph V E) :
    ∃ L : List (𝕀 → S), (∀ γ ∈ L, IsArcMap γ) ∧ (⋃ γ ∈ L, range γ) = ⋃₀ E := by
  classical
  have key : ∀ e ∈ E, ∃ a : 𝕀 → S, IsArcMap a ∧ range a = e := fun e he => by
    obtain ⟨u, v, -, hl, -⟩ := h.edge e he
    obtain ⟨a, ha, hr, -, -⟩ := hl.exists_arc
    exact ⟨a, ha, hr⟩
  by_cases hE : E.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty] at hE
    exact ⟨[], by simp, by simp [hE]⟩
  obtain ⟨e0, he0⟩ := hE
  have : Nonempty (𝕀 → S) := ⟨(key e0 he0).choose⟩
  choose! A hA hr using key
  refine ⟨h.fine.toFinset.toList.map A, ?_, ?_⟩
  · intro γ hγ
    simp only [List.mem_map, Finset.mem_toList, Finite.mem_toFinset] at hγ
    obtain ⟨e, he, rfl⟩ := hγ
    exact hA e he
  · ext x
    simp only [List.mem_map, Finset.mem_toList, Finite.mem_toFinset, mem_iUnion, exists_prop,
      mem_sUnion]
    constructor
    · rintro ⟨γ, ⟨e, he, rfl⟩, hx⟩
      exact ⟨e, he, hr e he ▸ hx⟩
    · rintro ⟨e, he, hx⟩
      exact ⟨A e, ⟨e, he, rfl⟩, (hr e he).symm ▸ hx⟩

/-- A finite cover by chart discs which contain at most one point of each given pair. -/
theorem exists_charts (hT : IsClosedSurface S) {Pairs : Set (S × S)} (hP : Pairs.Finite)
  (hne : ∀ p ∈ Pairs, p.1 ≠ p.2) :
    ∃ I : Set (S), I.Finite ∧ ∃ U : S → Set S, ∃ h : S → S → ℂ, ∃ g : S → ℂ → S,
      (∀ i ∈ I, BallChart 3 (U i) (h i) (g i)) ∧ (∀ i ∈ I, ∀ p ∈ Pairs, ¬ (p.1 ∈ U i ∧ p.2 ∈ U i)) ∧
      (⋃ i ∈ I, g i '' ball 0 1) = univ := by
  classical
  obtain ⟨hc, ht, hint⟩ := id hT
  have key : ∀ x : S, ∃ U : Set S, ∃ h : S → ℂ, ∃ g : ℂ → S, BallChart 3 U h g ∧ g 0 = x ∧
      ∀ p ∈ Pairs, ¬ (p.1 ∈ U ∧ p.2 ∈ U) := by
    intro x
    let W : Set S := ⋂ p ∈ Pairs, (if x = p.1 then {p.2}ᶜ else {p.1}ᶜ)
    have hW : IsOpen W := hP.isOpen_biInter fun p _ => by
      split_ifs <;> exact isOpen_compl_singleton
    have hxW : x ∈ W := by
      simp only [W, mem_iInter]
      intro p hp
      split_ifs with he
      · exact fun h' => hne p hp (he.symm.trans h')
      · exact he
    obtain ⟨U, h, g, c, hU, h0⟩ := (hint x).exists_ballChart hW hxW (R := 3) (by norm_num)
    refine ⟨U, h, g, c, h0, fun p hp hin => ?_⟩
    have h1 := hU hin.1
    have h2 := hU hin.2
    simp only [W, mem_iInter] at h1 h2
    have h3 := h1 p hp
    have h4 := h2 p hp
    split_ifs at h3 h4 with he
    · exact h4 rfl
    · exact h3 rfl
  choose U h g c hg0 hpair using key
  have hopen : ∀ x, IsOpen (g x '' ball 0 1) := fun x =>
    (c x).isOpen_image isOpen_ball (ball_subset_ball (by norm_num))
  have hcov : (univ : Set S) ⊆ ⋃ x, g x '' ball 0 1 := fun x _ =>
    mem_iUnion.mpr ⟨x, 0, by simp, hg0 x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
  refine ⟨t, t.finite_toSet, U, h, g, fun i _ => c i, fun i _ => hpair i, ?_⟩
  refine eq_univ_of_univ_subset (ht.trans fun x hx => ?_)
  simpa using hx

/-- A new curve around a point of `G` that leaves a point of `G` outside its disc meets `G` twice.
-/
theorem exists_two_meets [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {G B : Set S}
  (hG : TwoConn G)
    (hB : IsClosedDisc B) {x y : S} (hx : x ∈ G) (hy : y ∈ G) (hxB : x ∈ discInt B) (hyB : y ∉ B) :
    ∃ a b, a ∈ G ∩ discBd B ∧ b ∈ G ∩ discBd B ∧ a ≠ b := by
  by_contra hcon
  push Not at hcon
  have hP := hB.isOArc_discBd
  obtain ⟨c, hcP, hc⟩ : ∃ c ∈ discBd B, ∀ z ∈ G ∩ discBd B, z = c := by
    by_cases h3 : (G ∩ discBd B).Nonempty
    · obtain ⟨c, hc⟩ := h3
      exact ⟨c, hc.2, fun z hz => hcon z c hz hc⟩
    · obtain ⟨c, hc, -⟩ := hP.exists_ne x
      exact ⟨c, hc, fun z hz => absurd ⟨z, hz⟩ h3⟩
  have hdisj : Disjoint (G \ {c}) (discBd B) := by
    rw [Set.disjoint_left]
    exact fun z hz hz' => hz.2 (hc z ⟨hz.1, hz'⟩)
  have hxc : x ≠ c := fun he => hxB.2 (he ▸ hcP)
  have hyc : y ≠ c := fun he => hyB (discBd_subset B (he ▸ hcP))
  rcases hB.side hman (hG c) hdisj with h1 | h1
  · exact hyB (h1 ⟨hy, hyc⟩).1
  · exact Set.disjoint_left.mp h1 ⟨hx, hxc⟩ hxB.1

/-- Curves of charts added to a graph, until each point lies inside one of their discs. -/
theorem exists_skeleton_aux (hT : IsClosedSurface S) [ConnectedSpace S] {Pairs : Set
  (S × S)} {u w : S}
    (huw : (u, w) ∈ Pairs) {I : Set S} (hI : I.Finite) {U : S → Set S} {h : S → S → ℂ} {g : S → ℂ
      → S}
    (c : ∀ i ∈ I, BallChart 3 (U i) (h i) (g i)) (hp : ∀ i ∈ I, ∀ p ∈ Pairs, ¬ (p.1 ∈ U i
      ∧ p.2 ∈ U i))
    (hcov : (⋃ i ∈ I, g i '' ball 0 1) = univ) (Z : Set S) (n : ℕ) :
    ∀ (V : Set S) (E : Set (Set S)) (G : Set S) (𝓑 : Set (Set S)) (R : Set S), IsGraph V E
      → V ⊆ ⋃₀ E →
      gr V E = G ∪ Z → TwoConn G → IsClosed G → u ∈ G → w ∈ G → 𝓑.Finite →
      (∀ B ∈ 𝓑, IsClosedDisc B ∧ discBd B ⊆ G ∧ ∀ p ∈ Pairs, ¬ (p.1 ∈ B ∧ p.2 ∈ B)) →
      R ⊆ I → (∀ i ∈ I \ R, ∃ B ∈ 𝓑, g i '' ball 0 1 ⊆ discInt B) → R.ncard = n →
      ∃ (V' : Set S) (E' : Set (Set S)) (G' : Set S) (𝓑' : Set (Set S)), V ⊆ V' ∧ G ⊆ G'
        ∧ IsGraph V' E' ∧ V' ⊆ ⋃₀ E' ∧ gr V' E' = G' ∪ Z ∧ TwoConn G' ∧ IsClosed G' ∧
        𝓑'.Finite ∧ (∀ B ∈ 𝓑', IsClosedDisc B ∧ discBd B ⊆ G' ∧ ∀ p ∈ Pairs, ¬ (p.1 ∈ B ∧ p.2 ∈ B))
          ∧
        ∀ x, ∃ B ∈ 𝓑', x ∈ discInt B := by
  obtain ⟨hcpt, ht2, hint⟩ := id hT
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hint x).isManifoldPoint
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V E G 𝓑 R hg hno hgr hG hGc hu hw h𝓑 hB hRI hdone hn
  by_cases hall : ∀ i ∈ R, Disjoint (g i '' ball 0 1) G
  · refine ⟨V, E, G, 𝓑, subset_rfl, subset_rfl, hg, hno, hgr, hG, hGc, h𝓑, hB, ?_⟩
    have hin : ∀ x ∈ G, ∃ B ∈ 𝓑, x ∈ discInt B := fun x hx => by
      obtain ⟨i, hi, hxi⟩ : ∃ i ∈ I, x ∈ g i '' ball 0 1 := by
        have : x ∈ ⋃ i ∈ I, g i '' ball 0 1 := hcov ▸ mem_univ x
        simpa using this
      by_cases hiR : i ∈ R
      · exact absurd hx (Set.disjoint_left.mp (hall i hiR) hxi)
      · obtain ⟨B, hb, hs⟩ := hdone i ⟨hi, hiR⟩
        exact ⟨B, hb, hs hxi⟩
    set Q : Set S := G ∪ ⋃₀ 𝓑 with hQ
    have hQc : IsClosed Q := hGc.union (h𝓑.isClosed_sUnion fun B hb => (hB B hb).1.isClosed)
    have hQint : Q ⊆ interior Q := by
      have hsub : ∀ B ∈ 𝓑, discInt B ⊆ interior Q := fun B hb => interior_maximal
        ((discInt_subset B).trans fun z hz => .inr ⟨B, hb, hz⟩) ((hB B hb).1.isOpen_discInt hman)
      rintro x (hx | ⟨B, hb, hxB⟩)
      · obtain ⟨B, hb, hxB⟩ := hin x hx
        exact hsub B hb hxB
      · by_cases h1 : x ∈ discBd B
        · obtain ⟨B', hb', hxB'⟩ := hin x ((hB B hb).2.1 h1)
          exact hsub B' hb' hxB'
        · exact hsub B hb ⟨hxB, h1⟩
    have hQo : IsOpen Q := by
      rw [← subset_interior_iff_isOpen]
      exact hQint
    have hQu : Q = univ := IsClopen.eq_univ ⟨hQc, hQo⟩ ⟨u, .inl hu⟩
    intro x
    have hxQ : x ∈ Q := hQu ▸ mem_univ x
    rcases hxQ with hx | ⟨B, hb, hxB⟩
    · exact hin x hx
    · by_cases h1 : x ∈ discBd B
      · exact hin x ((hB B hb).2.1 h1)
      · exact ⟨B, hb, hxB, h1⟩
  push Not at hall
  obtain ⟨i, hiR, hnd⟩ := hall
  obtain ⟨x, hxi, hxG⟩ := Set.not_disjoint_iff.mp hnd
  have hi : i ∈ I := hRI hiR
  have hci := c i hi
  obtain ⟨L, hL, hLu⟩ := hg.exists_list
  obtain ⟨P, D, hPO, hPt, hD, hDb, hDg, hDU, hPd⟩ := exists_tame_curve' hman hci L hL
  have hgrE : gr V E = ⋃₀ E := union_eq_right.mpr hno
  rw [hLu, ← hgrE] at hPt
  obtain ⟨V1, E1, hV1, hg1, hgr1, hno1⟩ := hg.add_curve hPO hPt
  have hsubD : g i '' ball 0 1 ⊆ discInt D := by
    rintro _ ⟨z, hz, rfl⟩
    have hz2 : g i z ∈ g i '' closedBall 0 2 := ⟨z, ball_subset_closedBall (ball_subset_ball
      (by norm_num) hz), rfl⟩
    exact ⟨hDg hz2, fun h3 => Set.disjoint_left.mp hPd (hDb ▸ h3) hz2⟩
  have hxD : x ∈ discInt D := hsubD hxi
  obtain ⟨y, hyG, hyD⟩ : ∃ y ∈ G, y ∉ D := by
    by_cases h3 : u ∈ D
    · refine ⟨w, hw, fun h4 => hp i hi _ huw ⟨hDU h3, hDU h4⟩⟩
    · exact ⟨u, hu, h3⟩
  obtain ⟨a, b, ha, hb, hab⟩ := exists_two_meets hman hG hD hxG hyG hxD hyD
  have hG' : TwoConn (G ∪ P) := hG.union hPO.twoConn (x := a) (y := b) ⟨ha.1, hDb ▸ ha.2⟩ ⟨hb.1,
    hDb ▸ hb.2⟩ hab
  have hlt : (R \ {i}).ncard < n := by
    rw [← hn]
    exact ncard_sdiff_singleton_lt_of_mem hiR (hI.subset hRI)
  obtain ⟨V', E', G', 𝓑', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := ih _ hlt V1 E1 (G ∪ P)
    (insert D 𝓑) (R \ {i})
    hg1 (hno1 hno) (by rw [hgr1, hgr, union_right_comm]) hG' (hGc.union hPO.isCompact.isClosed)
      (.inl hu) (.inl hw)
    (h𝓑.insert _) (by
      rintro B (rfl | hb')
      · refine ⟨hD, hDb ▸ subset_union_right, fun p hpp hin => hp i hi p hpp ⟨hDU hin.1, hDU hin.2⟩⟩
      · exact ⟨(hB B hb').1, (hB B hb').2.1.trans subset_union_left, (hB B hb').2.2⟩)
    (sdiff_subset.trans hRI) (fun j hj => by
      by_cases hji : j = i
      · exact ⟨D, .inl rfl, hji ▸ hsubD⟩
      · have hjR : j ∉ R := fun h' => hj.2 ⟨h', hji⟩
        obtain ⟨B, hb', hs⟩ := hdone j ⟨hj.1, hjR⟩
        exact ⟨B, .inr hb', hs⟩) rfl
  exact ⟨V', E', G', 𝓑', hV1.trans h1, subset_union_left.trans h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The skeleton: curves of charts added to a graph, such that each point lies inside one of their
discs, and
each disc has at most one point of each given pair. -/
theorem exists_skeleton (hT : IsClosedSurface S) [ConnectedSpace S] {V₀ : Set S} {E₀ : Set (Set S)}
    (hg : IsGraph V₀ E₀) (hno : V₀ ⊆ ⋃₀ E₀) {G₀ Z : Set S} (hgr : gr V₀ E₀ = G₀ ∪ Z)
      (hG₀ : TwoConn G₀)
    (hGc : IsClosed G₀) {Pairs : Set (S × S)} (hP : Pairs.Finite) (hne : ∀ p ∈ Pairs, p.1 ≠ p.2) {u
      w : S}
    (huw : (u, w) ∈ Pairs) (hu : u ∈ G₀) (hw : w ∈ G₀) :
    ∃ (V : Set S) (E : Set (Set S)) (G : Set S) (𝓑 : Set (Set S)), V₀ ⊆ V ∧ G₀ ⊆ G ∧ IsGraph V E
      ∧ V ⊆ ⋃₀ E ∧ gr V E = G ∪ Z ∧ TwoConn G ∧ IsClosed G ∧
      𝓑.Finite ∧ (∀ B ∈ 𝓑, IsClosedDisc B ∧ discBd B ⊆ G ∧ ∀ p ∈ Pairs, ¬ (p.1 ∈ B ∧ p.2 ∈ B)) ∧
      ∀ x, ∃ B ∈ 𝓑, x ∈ discInt B := by
  obtain ⟨I, hI, U, h, g, c, hp, hcov⟩ := exists_charts hT hP hne
  exact exists_skeleton_aux hT huw hI c hp hcov Z _ V₀ E₀ G₀ ∅ I hg hno hgr hG₀ hGc hu hw
    finite_empty (by simp)
    subset_rfl (by simp) rfl

end GraphMinor.Surface
