/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section11f

/-!
# Graph Minors VII, (11.10) Boundary-Surface Case (`bd S ≠ ∅`): Boundary Chart Merging

This file completes the proof of `SolidFlatBoundarySurfacePlanarStatement`
(`GraphMinor/GM07/Open.lean`),
formalizing the boundary-surface case ($\operatorname{bd}(\Sigma) \ne \emptyset$) of Graph Minors
VII,
(11.10) (page 253).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology Metric Filter OnePoint GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Plane Domain Lemmas for `B_half` and `psiShift` -/

/-- The half-ball domain `B_half := {z ∈ ball 0 3 | z.re ≤ capH52 z.im}` in `ℂ`. -/
def bHalf : Set ℂ := {z : ℂ | z ∈ ball 0 3 ∧ z.re ≤ capH52 z.im}

/-- The open interior part `B_int := {z ∈ ball 0 3 | z.re < capH52 z.im}` of `bHalf`. -/
def bInt : Set ℂ := {z : ℂ | z ∈ ball 0 3 ∧ z.re < capH52 z.im}

theorem isOpen_bInt : IsOpen bInt :=
  isOpen_ball.inter (isOpen_lt Complex.continuous_re (continuous_capH52.comp Complex.continuous_im))

theorem bInt_subset_bHalf : bInt ⊆ bHalf := fun _ hz => ⟨hz.1, hz.2.le⟩

/-- Every point on `sphere (0 : ℂ) (5 / 2)` satisfies `capH52 z.im = |z.re|` and lies in `bHalf`. -/
theorem capH52_of_mem_sphere {z : ℂ} (hz : z ∈ sphere (0 : ℂ) (5 / 2)) :
    capH52 z.im = |z.re| ∧ z ∈ bHalf := by
  have hnorm : ‖z‖ = 5 / 2 := mem_sphere_zero_iff_norm.mp hz
  have hsq : z.re ^ 2 + z.im ^ 2 = (5 / 2) ^ 2 := by
    have h1 : Complex.normSq z = (5 / 2) ^ 2 := by rw [← Complex.sq_norm, hnorm]
    rw [Complex.normSq_apply] at h1
    nlinarith
  have hcap : capH52 z.im = |z.re| := by
    unfold capH52
    have h1 : (5 / 2) ^ 2 - z.im ^ 2 = z.re ^ 2 := by linarith
    rw [h1, max_eq_right (sq_nonneg _), Real.sqrt_sq_eq_abs]
  refine ⟨hcap, mem_ball_zero_iff.mpr (by linarith), ?_⟩
  rw [hcap]
  exact le_abs_self z.re

/-- On `sphere (0 : ℂ) (5 / 2)`, `z.re = capH52 z.im ↔ 0 ≤ z.re`. -/
theorem re_eq_capH52_iff_nonneg {z : ℂ} (hz : z ∈ sphere (0 : ℂ) (5 / 2)) :
    z.re = capH52 z.im ↔ 0 ≤ z.re := by
  rw [(capH52_of_mem_sphere hz).1]
  exact ⟨fun h => h ▸ abs_nonneg z.re, fun h => (abs_of_nonneg h).symm⟩

/-- Every point of `{z : ℂ | ‖z‖ = 5 / 2 ∧ 0 ≤ z.re}` is `(5 / 2 : ℂ) * (Circle.exp (-τ) *
Circle.exp (s * (2 * τ)))`
for some `s ∈ 𝕀`, whenever `Real.pi / 2 ≤ τ`. -/
theorem right_semicircle_subset_arc {τ : ℝ} (hτ : Real.pi / 2 ≤ τ) (hτ_pos : 0 < τ)
    {z : ℂ} (hz : ‖z‖ = 5 / 2) (hre : 0 ≤ z.re) :
    ∃ s : 𝕀, (5 / 2 : ℂ) * ↑(Circle.exp (-τ) * Circle.exp (s.1 * (2 * τ))) = z := by
  obtain ⟨harg_ge, harg_le⟩ := abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hre)
  let s_val : ℝ := (Complex.arg z + τ) / (2 * τ)
  have hs0 : 0 ≤ s_val := div_nonneg (by linarith) (by positivity)
  have hs1 : s_val ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  refine ⟨⟨s_val, hs0, hs1⟩, ?_⟩
  rw [← Circle.exp_add]
  have hangle : -τ + s_val * (2 * τ) = Complex.arg z := by
    dsimp [s_val]
    field_simp
    ring
  rw [hangle, Circle.coe_exp]
  have hmul := Complex.norm_mul_exp_arg_mul_I z
  rw [hz] at hmul
  simpa [mul_comm] using hmul

/-- If an `O`-arc `Q ⊆ bHalf` in `ℂ` satisfies `closedInner Q ⊆ ball 0 3`, then
`closedInner Q ⊆ bHalf`. -/
theorem closedInner_subset_bHalf {Q : Set ℂ} (hQ : IsOArc Q) (hQb : Q ⊆ bHalf)
    (hsub3 : closedInner Q ⊆ ball 0 3) :
    closedInner Q ⊆ bHalf := by
  obtain ⟨φ⟩ := id hQ
  have J := isJordanParts φ
  intro z₀ hz₀
  refine ⟨hsub3 hz₀, ?_⟩
  rcases hz₀ with hz₀_in | hz₀_Q
  · by_contra hgt
    push Not at hgt
    let γ : ℝ → ℂ := fun s => z₀ + (s : ℂ)
    have hγc : Continuous γ := by fun_prop
    have hγ_conn : IsPreconnected (γ '' Icc 0 6) :=
      isPreconnected_Icc.image γ hγc.continuousOn
    have hγ_disj : Disjoint (γ '' Icc 0 6) Q := by
      rw [Set.disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ hmemQ
      have hle := (hQb hmemQ).2
      have hre : (γ s).re = z₀.re + s := by simp [γ]
      have him : (γ s).im = z₀.im := by simp [γ]
      rw [hre, him] at hle
      linarith [hs.1]
    have hcov : γ '' Icc 0 6 ⊆ Surface.inner Q ∪ (closedInner Q)ᶜ := by
      intro w hw
      by_cases hw_in : w ∈ Surface.inner Q
      · exact Or.inl hw_in
      · exact Or.inr fun hcl => hcl.elim hw_in (Set.disjoint_left.mp hγ_disj hw)
    have hdisj_open : Disjoint (Surface.inner Q) (closedInner Q)ᶜ :=
      Set.disjoint_left.mpr fun w hw hnot => hnot (Or.inl hw)
    rcases hγ_conn.subset_or_subset J.isOpen_inner J.isCompact_closure_inner.isClosed.isOpen_compl
      hdisj_open hcov with hsub_in | hsub_out
    · have h6_in : γ 6 ∈ ball (0 : ℂ) 3 :=
        hsub3 (Or.inl (hsub_in ⟨6, ⟨by norm_num, by norm_num⟩, rfl⟩))
      have hz₀_in3 : ‖z₀‖ < 3 := mem_ball_zero_iff.mp (hsub3 (Or.inl hz₀_in))
      have h6_norm : ‖γ 6‖ < 3 := mem_ball_zero_iff.mp h6_in
      have htri := norm_sub_norm_le (6 : ℂ) (-z₀)
      have h6_eq : (6 : ℂ) - (-z₀) = γ 6 := by simp [γ]; ring
      rw [h6_eq, norm_neg] at htri
      have hnorm6 : ‖(6 : ℂ)‖ = 6 := by norm_num
      linarith
    · have h0_out := hsub_out ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩
      have hγ0 : γ 0 = z₀ := by simp [γ]
      rw [hγ0] at h0_out
      exact h0_out (Or.inl hz₀_in)
  · exact (hQb hz₀_Q).2

/-- If `Q = A ∪ B` is an `O`-arc in `ℂ` with `closedBall 0 2 ⊆ Surface.inner Q`,
`{z : ℂ | ‖z‖ = 5 / 2 ∧ 0 ≤ z.re} ⊆ A ⊆ sphere 0 (5 / 2)`, and `B ⊆ {z : ℂ | z.re < 0}`, then
`{z : ℂ | ‖z‖ ≤ 5 / 2 ∧ 0 ≤ z.re} ⊆ closedInner Q`. -/
theorem right_halfDisc_subset_closedInner {Q A B : Set ℂ} (hQ : IsOArc Q) (hQ_eq : Q = A ∪ B)
    (hin2 : closedBall (0 : ℂ) 2 ⊆ Surface.inner Q)
    (hA_semi : {z : ℂ | ‖z‖ = 5 / 2 ∧ 0 ≤ z.re} ⊆ A)
    (hA_sph : A ⊆ sphere 0 (5 / 2))
    (hB_neg : ∀ z ∈ B, z.re < 0) :
    {z : ℂ | ‖z‖ ≤ 5 / 2 ∧ 0 ≤ z.re} ⊆ closedInner Q := by
  obtain ⟨φ⟩ := id hQ
  have J := isJordanParts φ
  rintro z₀ ⟨hz₀_norm, hz₀_re⟩
  rcases eq_or_lt_of_le hz₀_norm with heq | hlt
  · exact Or.inr (hQ_eq ▸ Or.inl (hA_semi ⟨heq, hz₀_re⟩))
  · let γ : ℝ → ℂ := fun s => (s : ℂ) * z₀
    have hγc : Continuous γ := by fun_prop
    have hγ_conn : IsPreconnected (γ '' Icc 0 1) :=
      isPreconnected_Icc.image γ hγc.continuousOn
    have hγ_disj : Disjoint (γ '' Icc 0 1) Q := by
      rw [Set.disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ hmemQ
      rw [hQ_eq] at hmemQ
      rcases hmemQ with hmemA | hmemB
      · have hnorm_s : ‖γ s‖ = 5 / 2 := mem_sphere_zero_iff_norm.mp (hA_sph hmemA)
        have hnorm_le : ‖γ s‖ < 5 / 2 := by
          simp only [γ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
          nlinarith [hs.1, hs.2, norm_nonneg z₀]
        exact hnorm_le.ne hnorm_s
      · have hneg := hB_neg (γ s) hmemB
        have hnonneg : 0 ≤ (γ s).re := by
          simp only [γ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          exact mul_nonneg hs.1 hz₀_re
        linarith
    have hcov : γ '' Icc 0 1 ⊆ Surface.inner Q ∪ (closedInner Q)ᶜ := by
      intro w hw
      by_cases hw_in : w ∈ Surface.inner Q
      · exact Or.inl hw_in
      · exact Or.inr fun hcl => hcl.elim hw_in (Set.disjoint_left.mp hγ_disj hw)
    have hdisj_open : Disjoint (Surface.inner Q) (closedInner Q)ᶜ :=
      Set.disjoint_left.mpr fun w hw hnot => hnot (Or.inl hw)
    rcases hγ_conn.subset_or_subset J.isOpen_inner J.isCompact_closure_inner.isClosed.isOpen_compl
      hdisj_open hcov with hsub_in | hsub_out
    · have h1_in := hsub_in ⟨1, ⟨by norm_num, by norm_num⟩, rfl⟩
      have hγ1 : γ 1 = z₀ := by simp [γ]
      rw [hγ1] at h1_in
      exact Or.inl h1_in
    · exfalso
      have h0_out := hsub_out ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩
      have hγ0 : γ 0 = 0 := by simp [γ]
      rw [hγ0] at h0_out
      exact h0_out (Or.inl (hin2 (mem_closedBall_zero_iff.mpr (by norm_num))))

/-! ## 2. Taming One Arc When the Other Arc Misses `G` -/

/-- If `a` and `b` form two arcs of an `O`-arc and `range a` is disjoint from `G₀ = ⋃ g ∈ G, range
g`,
we can tame `b` alone within `thickening ε (range b)` while keeping `a` fixed. -/
theorem exists_tame_single_arc {Y : Type u} [MetricSpace Y] (G : List (𝕀 → Y))
    (hG : ∀ g ∈ G, IsArcMap g) {a b : 𝕀 → Y} (ha : IsArcMap a) (hb : IsArcMap b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hm : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hdisj_a : Disjoint (range a) (⋃ g ∈ G, range g)) {ε : ℝ} (hε : 0 < ε) :
    ∃ b' : 𝕀 → Y, IsArcMap b' ∧ b' 0 = a 0 ∧ b' 1 = a 1 ∧
      (∀ s t, a s = b' t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) ∧
      range b' ⊆ thickening ε (range b) ∧
      FinConn ((range a ∪ range b') \ ⋃ g ∈ G, range g) := by
  classical
  set G₀ : Set Y := ⋃ g ∈ G, range g with hG₀
  have hp : ∀ g ∈ G, a 0 ∉ range g := fun g hg hmem =>
    Set.disjoint_left.mp hdisj_a ⟨0, rfl⟩ (mem_iUnion₂.mpr ⟨g, hg, hmem⟩)
  have hq : ∀ g ∈ G, a 1 ∉ range g := fun g hg hmem =>
    Set.disjoint_left.mp hdisj_a ⟨1, rfl⟩ (mem_iUnion₂.mpr ⟨g, hg, hmem⟩)
  have hcut : ∃ L : List (𝕀 → Y), (∀ g ∈ L, IsArcMap g) ∧ (⋃ g ∈ L, range g) = G₀ ∧
      ∀ g ∈ L, ∀ x ∈ range g, ∀ y ∈ range g, dist x y < ε := by
    clear_value G₀
    subst hG₀
    clear hdisj_a hp hq
    induction G with
    | nil =>
      exact ⟨[], by simp, by simp, by simp⟩
    | cons g G ih =>
      obtain ⟨L₁, h1', h2', h3'⟩ := (hG g (.head _)).exists_small hε
      obtain ⟨L₂, h1'', h2'', h3''⟩ := ih (fun g' hg' => hG g' (.tail _ hg'))
      refine ⟨L₁ ++ L₂, ?_, ?_, ?_⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h | h
        · exact h1' g' h
        · exact h1'' g' h
      · ext x
        simp only [mem_iUnion, List.mem_append, exists_prop, List.mem_cons]
        have e1 := Set.ext_iff.mp h2' x
        have e2 := Set.ext_iff.mp h2'' x
        simp only [mem_iUnion, exists_prop] at e1 e2
        constructor
        · rintro ⟨g', hg' | hg', hx⟩
          · exact ⟨g, .inl rfl, e1.mp ⟨g', hg', hx⟩⟩
          · obtain ⟨g'', h5, h6⟩ := e2.mp ⟨g', hg', hx⟩
            exact ⟨g'', .inr h5, h6⟩
        · rintro ⟨g', rfl | hg', hx⟩
          · obtain ⟨g'', h5, h6⟩ := e1.mpr hx
            exact ⟨g'', .inl h5, h6⟩
          · obtain ⟨g'', h5, h6⟩ := e2.mpr ⟨g', hg', hx⟩
            exact ⟨g'', .inr h5, h6⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h | h
        · exact h3' g' h
        · exact h3'' g' h
  obtain ⟨L, hL1, hL2, hL3⟩ := hcut
  have hLG : ∀ g ∈ L, range g ⊆ G₀ := fun g hg => by
    rw [← hL2]
    exact subset_biUnion_of_mem (s := {g | g ∈ L}) (u := fun g : 𝕀 → Y => range g) hg
  let Lb := L.filter fun g => (range g ∩ range b).Nonempty
  have hLb : ∀ g ∈ Lb, g ∈ L ∧ (range g ∩ range b).Nonempty := fun g hg => by
    simpa [Lb] using hg
  have hmissG : ∀ g ∈ L, a 0 ∉ range g ∧ a 1 ∉ range g := fun g hg => by
    constructor
    · intro hx
      obtain ⟨g', h5, h6⟩ := mem_iUnion₂.mp (hLG g hg hx)
      exact hp g' h5 h6
    · intro hx
      obtain ⟨g', h5, h6⟩ := mem_iUnion₂.mp (hLG g hg hx)
      exact hq g' h5 h6
  obtain ⟨b', hb', hb0, hb1, hb2, hb3⟩ := exists_erase Lb (fun g hg => hL1 g (hLb g hg).1) hb
    (fun g hg => h0 ▸ (hmissG g (hLb g hg).1).1) (fun g hg => h1 ▸ (hmissG g (hLb g hg).1).2)
  refine ⟨b', hb', hb0.trans h0, hb1.trans h1, ?_, ?_, ?_⟩
  · intro s t he
    have hmem : b' t ∈ range b ∪ ⋃ g ∈ Lb, range g := hb2 ⟨t, rfl⟩
    rcases hmem with ⟨t', ht'⟩ | hmemL
    · rcases hm s t' (he.trans ht'.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, hb'.2 (by rw [← he, hb0, h0])⟩
      · exact Or.inr ⟨rfl, hb'.2 (by rw [← he, hb1, h1])⟩
    · exfalso
      obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hmemL
      exact Set.disjoint_left.mp hdisj_a ⟨s, he⟩ (hLG g (hLb g hg).1 hxg)
  · intro x hx
    rcases hb2 hx with hxb | hxL
    · exact self_subset_thickening hε _ hxb
    · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hxL
      obtain ⟨y, hyg, hyb⟩ := (hLb g hg).2
      exact mem_thickening_iff.mpr ⟨y, hyb, hL3 g (hLb g hg).1 x hxg y hyg⟩
  · have ha_sdiff : range a \ G₀ = range a := sdiff_eq_left.mpr hdisj_a
    have hb_sdiff : range b' \ G₀ = range b' \ ⋃ g ∈ Lb, range g := by
      ext x
      constructor
      · rintro ⟨h4, h5⟩
        refine ⟨h4, fun h6 => h5 ?_⟩
        obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h6
        exact hLG g (hLb g hg).1 hxg
      · rintro ⟨h4, h5⟩
        refine ⟨h4, fun h6 => ?_⟩
        rw [← hL2] at h6
        obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h6
        rcases hb2 h4 with h7 | h7
        · have hne : (range g ∩ range b).Nonempty := ⟨x, hxg, h7⟩
          exact h5 (mem_iUnion₂.mpr ⟨g, by simp [Lb, hg, hne], hxg⟩)
        · exact h5 h7
    rw [union_sdiff_distrib, ha_sdiff, hb_sdiff]
    exact (finConn_of_isPreconnected (isPreconnected_range ha.1)).union hb3

/-! ## 3. Boundary Half-Charts and Boundary Disc Merging -/

/-- Coordinates on a boundary collar neighborhood `U ⊆ S`, mapping `bHalf = {z ∈ ball 0 3 | z.re ≤
capH52 z.im}`
homeomorphically onto `U`, with `g z ∈ bd S ↔ z.re = capH52 z.im`. -/
structure BoundaryHalfChart (U : Set S) (h : S → ℂ) (g : ℂ → S) : Prop where
  hc : ContinuousOn h U
  gc : Continuous g
  hm : MapsTo h U bHalf
  gm : MapsTo g bHalf U
  gh : LeftInvOn g h U
  hg : LeftInvOn h g bHalf
  bd_iff : ∀ z ∈ bHalf, g z ∈ bd S ↔ z.re = capH52 z.im

namespace BoundaryHalfChart

variable {U : Set S} {h : S → ℂ} {g : ℂ → S}

theorem isOpen_image_bInt (c : BoundaryHalfChart U h g) (hS : IsSurface S) {V : Set ℂ}
    (hV : IsOpen V) (hsub : V ⊆ bInt) : IsOpen (g '' V) :=
  isOpen_image_of_manifold hV c.gc.continuousOn (c.hg.injOn.mono (hsub.trans bInt_subset_bHalf))
    fun _ _ => hS.2.2 _

theorem image_disc (c : BoundaryHalfChart U h g) {Z : Set ℂ} (hZ : IsClosedDisc Z)
    (hsub : Z ⊆ bHalf) :
    IsClosedDisc (g '' Z) ∧ discBd (g '' Z) = g '' discBd Z :=
  hZ.image (c.gc.continuousOn.mono hsub)
    (c.hc.mono (image_subset_iff.mpr fun _ hz => c.gm (hsub hz))) (c.hg.mono hsub)

end BoundaryHalfChart

/-- Cosine is negative on `(π/2, 3π/2)`. -/
theorem cos_neg_of_mem_Ioo_pi_div_two_three_pi_div_two {θ : ℝ}
    (h1 : Real.pi / 2 < θ) (h2 : θ < 3 * Real.pi / 2) : Real.cos θ < 0 := by
  have hpi := Real.pi_pos
  rcases le_or_gt θ Real.pi with hle | hgt
  · exact Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith)
  · have hsym : Real.cos (2 * Real.pi - θ) = Real.cos θ := by
      have : 2 * Real.pi - θ = -θ + 2 * Real.pi := by ring
      rw [this, Real.cos_add_two_pi, Real.cos_neg]
    rw [← hsym]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)

private theorem scaled_collar_arcs
    {τ r : ℝ} (hτ_gt : Real.pi / 2 < τ) (hτ_lt2 : τ < 2) (hrpos : 0 < r)
    (a₀ b₀ : 𝕀 → Circle)
    (ha₀ : ∀ s, a₀ s = Circle.exp (-τ) * Circle.exp (s.1 * (2 * τ)))
    (hb₀ : ∀ s, b₀ s = Circle.exp (-τ) *
      Circle.exp (2 * Real.pi - s.1 * (2 * Real.pi - 2 * τ))) :
    let κ : Circle → ℂ := fun w => (r : ℂ) * w
    (∀ w : Circle, (w : ℂ) ≠ -1 → κ w ∈ Complex.slitPlane) ∧
      (∀ s, (a₀ s : ℂ) ≠ -1) ∧ (∀ s, (κ (b₀ s)).re < 0) := by
  intro κ
  have hpi_gt3 : 3 < Real.pi := Real.pi_gt_three
  have hslit : ∀ w : Circle, (w : ℂ) ≠ -1 → κ w ∈ Complex.slitPlane := fun w hw => by
    have h1 := circle_mem_slitPlane hw
    rw [Complex.mem_slitPlane_iff] at h1 ⊢
    simp only [κ, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, add_zero]
    rcases h1 with h1 | h1
    · exact .inl (mul_pos hrpos h1)
    · exact .inr (mul_ne_zero hrpos.ne' h1)
  have ha₀ne : ∀ s, (a₀ s : ℂ) ≠ -1 := fun s he => by
    have h1 : a₀ s = Circle.exp Real.pi := Circle.ext (by simpa using he)
    rw [ha₀, ← Circle.exp_add] at h1
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
    have hs0 := s.2.1
    have hs1 := s.2.2
    have h2 : -τ ≤ -τ + s.1 * (2 * τ) := by nlinarith
    have h3 : -τ + s.1 * (2 * τ) ≤ τ := by nlinarith
    rcases le_or_gt 0 m with h | h
    · have h4 : (0 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith
    · have h4 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
      nlinarith
  have hb₀_neg : ∀ s, (κ (b₀ s)).re < 0 := fun s => by
    rw [hb₀, ← Circle.exp_add]
    set θ := -τ + (2 * Real.pi - s.1 * (2 * Real.pi - 2 * τ))
    have hs0 := s.2.1
    have hs1 := s.2.2
    have hθ1 : Real.pi / 2 < θ := by
      have : τ ≤ θ := by nlinarith
      linarith
    have hθ2 : θ < 3 * Real.pi / 2 := by
      have : θ ≤ 2 * Real.pi - τ := by nlinarith
      linarith
    simp only [κ, Circle.coe_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero]
    exact mul_neg_of_pos_of_neg hrpos (cos_neg_of_mem_Ioo_pi_div_two_three_pi_div_two hθ1 hθ2)
  exact ⟨hslit, ha₀ne, hb₀_neg⟩

/-- In a `BoundaryHalfChart`, given a closed set `D` disjoint from `g '' {z ∈ bHalf | z.re = capH52
z.im}`
and a finite list of arcs `G` in `D`, we can perturb the left semicircle of radius `5 / 2` inside
`g '' bInt` while keeping the right semicircle fixed, obtaining an `O`-arc `P` tame with respect to
`G` that bounds a closed disc `E ⊆ U` containing `g '' closedBall 0 2` and
`g '' {z : ℂ | ‖z‖ ≤ 5 / 2 ∧ 0 ≤ z.re}`. -/
theorem exists_boundary_tame_curve (hS : IsSurface S)
    {U : Set S} {h : S → ℂ} {g : ℂ → S} (c : BoundaryHalfChart U h g)
    {D : Set S} (hDcl : IsClosed D)
    (hD_disj : Disjoint D (g '' {z ∈ bHalf | z.re = capH52 z.im}))
    (G : List (𝕀 → S)) (hG : ∀ γ ∈ G, IsArcMap γ) (hGD : (⋃ γ ∈ G, range γ) ⊆ D) :
    ∃ P E : Set S, IsOArc P ∧ FinConn (P \ ⋃ γ ∈ G, range γ) ∧
      IsClosedDisc E ∧ discBd E = P ∧
      g '' (closedBall 0 2 ∩ bHalf) ⊆ E ∧
      g '' {z : ℂ | ‖z‖ ≤ 5 / 2 ∧ 0 ≤ z.re} ⊆ E ∧
      E ⊆ g '' bHalf ∧
      P ⊆ g '' bInt ∪ g '' {z : ℂ | ‖z‖ = 5 / 2 ∧ 0 ≤ z.re} := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hsc := secondCountable_of_manifold hS.2.2
  let _ : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
  have hpi := Real.pi_pos
  have hpi_gt3 : 3 < Real.pi := Real.pi_gt_three
  have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  let r : ℝ := 5 / 2
  have hrpos : 0 < r := by norm_num
  have hr2 : 2 < r := by norm_num
  have hr3 : r < 3 := by norm_num
  have hrc : (r : ℂ) ≠ 0 := by norm_num
  let κ : Circle → ℂ := fun w => (r : ℂ) * w
  have hκc : Continuous κ := by fun_prop
  have hκi : Function.Injective κ := fun w w' he => Circle.ext (mul_left_cancel₀ hrc he)
  have hκn : ∀ w, ‖κ w‖ = 5 / 2 := fun w => by simp [κ, r]
  have hκ_sph : ∀ w, κ w ∈ sphere (0 : ℂ) (5 / 2) := fun w => mem_sphere_zero_iff_norm.mpr (hκn w)
  have hκ_bHalf : ∀ w, κ w ∈ bHalf := fun w => (capH52_of_mem_sphere (hκ_sph w)).2
  -- Find `δ_τ > 0` so `θ ↦ g (κ (Circle.exp θ))` misses `D` on `[-π/2 - δ_τ, π/2 + δ_τ]`.
  let f_arc : ℝ → S := fun θ => g (κ (Circle.exp θ))
  have hf_arc : Continuous f_arc := c.gc.comp (hκc.comp Circle.exp.continuous)
  have hIcc_miss : Icc (-(Real.pi / 2)) (Real.pi / 2) ⊆ f_arc ⁻¹' Dᶜ := by
    intro θ hθ hxD
    have hre : 0 ≤ (κ (Circle.exp θ)).re := by
      simp only [κ, Circle.coe_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero]
      exact mul_nonneg hrpos.le (Real.cos_nonneg_of_mem_Icc hθ)
    have hbd_eq := (re_eq_capH52_iff_nonneg (hκ_sph (Circle.exp θ))).mpr hre
    exact Set.disjoint_left.mp hD_disj hxD ⟨κ (Circle.exp θ), ⟨hκ_bHalf _, hbd_eq⟩, rfl⟩
  obtain ⟨δ₁, hδ₁, hth_δ₁⟩ := isCompact_Icc.exists_thickening_subset_open
    (hDcl.isOpen_compl.preimage hf_arc) hIcc_miss
  set δ_τ : ℝ := min (δ₁ / 2) (1 / 4) with hδ_τ_def
  have hδ_τ_pos : 0 < δ_τ := lt_min (by positivity) (by norm_num)
  have hδ_τ_le1 : δ_τ ≤ δ₁ / 2 := min_le_left _ _
  have hδ_τ_le2 : δ_τ ≤ 1 / 4 := min_le_right _ _
  set τ : ℝ := Real.pi / 2 + δ_τ with hτ_def
  have hτ_gt : Real.pi / 2 < τ := by linarith
  have hτ_lt2 : τ < 2 := by linarith
  have hτ_pos : 0 < τ := by linarith
  obtain ⟨a₀, b₀, hab, ha₀, hb₀, _⟩ := circle_two_arcs' (Circle.exp (-τ)) (θ := 2 * τ)
    ⟨by positivity, by linarith⟩
  let Ω₀ : Set ℂ := {z | 2 < ‖z‖ ∧ ‖z‖ < 3}
  have hΩ₀ : IsOpen Ω₀ := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hκΩ : ∀ w, κ w ∈ Ω₀ := fun w => ⟨by rw [hκn]; norm_num, by rw [hκn]; norm_num⟩
  obtain ⟨hslit, ha₀ne, hb₀_neg⟩ := scaled_collar_arcs hτ_gt hτ_lt2 hrpos a₀ b₀ ha₀ hb₀
  let a : 𝕀 → S := fun s => g (κ (a₀ s))
  let b : 𝕀 → S := fun s => g (κ (b₀ s))
  have hgκc : Continuous fun w => g (κ w) := c.gc.comp hκc
  have hgκi : Function.Injective fun w => g (κ w) := fun w w' he =>
    hκi (c.hg.injOn.eq_iff (hκ_bHalf w) (hκ_bHalf w') |>.mp he)
  have ha : IsArcMap a := ⟨hgκc.comp hab.1.1, hgκi.comp hab.1.2⟩
  have hb : IsArcMap b := ⟨hgκc.comp hab.2.1, hgκi.comp hab.2.2⟩
  have ha_disj_D : Disjoint (range a) D := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, rfl⟩ hxD
    have hθ_mem : -τ + s.1 * (2 * τ) ∈ thickening δ₁ (Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
      rw [mem_thickening_iff]
      have hs0 := s.2.1
      have hs1 := s.2.2
      have h1 : -τ ≤ -τ + s.1 * (2 * τ) := by nlinarith
      have h2 : -τ + s.1 * (2 * τ) ≤ τ := by nlinarith
      rcases lt_or_ge (-τ + s.1 * (2 * τ)) (-(Real.pi / 2)) with hlt | hge
      · refine ⟨-(Real.pi / 2), ⟨le_rfl, by linarith⟩, ?_⟩
        rw [Real.dist_eq, abs_of_neg (by linarith)]
        linarith
      · rcases le_or_gt (-τ + s.1 * (2 * τ)) (Real.pi / 2) with hle | hgt
        · refine ⟨-τ + s.1 * (2 * τ), ⟨hge, hle⟩, ?_⟩
          rw [dist_self]
          exact hδ₁
        · refine ⟨Real.pi / 2, ⟨by linarith, le_rfl⟩, ?_⟩
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith
    have hnotD : f_arc (-τ + s.1 * (2 * τ)) ∈ Dᶜ := hth_δ₁ hθ_mem
    have heq : a s = f_arc (-τ + s.1 * (2 * τ)) := by
      dsimp [a, f_arc]
      rw [ha₀, ← Circle.exp_add]
    exact hnotD (heq ▸ hxD)
  let Nb : Set ℂ := Ω₀ ∩ {z : ℂ | z.re < 0}
  have hNb_open : IsOpen Nb := hΩ₀.inter (isOpen_lt Complex.continuous_re continuous_const)
  have hNb_bInt : Nb ⊆ bInt := fun z hz =>
    ⟨mem_ball_zero_iff.mpr hz.1.2, hz.2.trans_le (capH52_nonneg z.im)⟩
  have hNbS : IsOpen (g '' Nb) := c.isOpen_image_bInt hS hNb_open hNb_bInt
  have hbN : range b ⊆ g '' Nb := by
    rintro _ ⟨s, rfl⟩
    exact ⟨κ (b₀ s), ⟨hκΩ _, hb₀_neg s⟩, rfl⟩
  obtain ⟨ε₂, hε₂, hth₂⟩ := (isCompact_range hb.1).exists_thickening_subset_open hNbS hbN
  obtain ⟨b', hb', hb'0, hb'1, hm', hrb, htame⟩ :=
    exists_tame_single_arc G hG ha hb (congrArg (fun w => g (κ w)) hab.3)
      (congrArg (fun w => g (κ w)) hab.4) (fun s t he => hab.5 s t (hgκi he))
      (ha_disj_D.mono_right hGD) hε₂
  have hrb' : range b' ⊆ g '' Nb := hrb.trans hth₂
  set P : Set S := range a ∪ range b' with hPdef
  have hPO : IsOArc P := oArc_of_two_arcs ha hb' hb'0.symm hb'1.symm hm'
  have ha_bHalf : range a ⊆ g '' (Ω₀ ∩ bHalf) := by
    rintro _ ⟨s, rfl⟩
    exact ⟨κ (a₀ s), ⟨hκΩ _, hκ_bHalf _⟩, rfl⟩
  have hb'_bHalf : range b' ⊆ g '' (Ω₀ ∩ bHalf) :=
    hrb'.trans (image_mono fun z hz => ⟨hz.1, bInt_subset_bHalf (hNb_bInt hz)⟩)
  have hP_bHalf : P ⊆ g '' (Ω₀ ∩ bHalf) := union_subset ha_bHalf hb'_bHalf
  have hPU : P ⊆ U := hP_bHalf.trans (image_subset_iff.mpr fun z hz => c.gm hz.2)
  have hhP : ∀ x ∈ P, h x ∈ Ω₀ ∧ h x ∈ bHalf := fun x hx => by
    obtain ⟨z, hz, rfl⟩ := hP_bHalf hx
    rwa [c.hg hz.2]
  have hQ : IsOArc (h '' P) :=
    hPO.image (c.hc.mono hPU) (c.gc.continuousOn.mono fun z hz => by
      obtain ⟨x, hx, rfl⟩ := hz
      exact (hhP x hx).2) (c.gh.mono hPU)
  have hp0 : κ (a₀ 0) = (r : ℂ) * Complex.exp (-τ * Complex.I) := by
    simp only [κ, ha₀, Set.Icc.coe_zero, zero_mul, ← Circle.exp_add, Circle.coe_exp]
    congr 2; push_cast; ring
  have hq0 : κ (a₀ 1) = (r : ℂ) * Complex.exp (τ * Complex.I) := by
    simp only [κ, ha₀, Set.Icc.coe_one, one_mul, ← Circle.exp_add, Circle.coe_exp]
    congr 2; push_cast; ring
  have hlog : ¬ HasLogOn (h '' P) fun z => z := by
    have hAc : IsPreconnected (h '' range a) := (isPreconnected_range ha.1).image _
      (c.hc.mono (subset_union_left.trans hPU))
    have hBc : IsPreconnected (h '' range b') := (isPreconnected_range hb'.1).image _
      (c.hc.mono (subset_union_right.trans hPU))
    have hp' : h (a 0) = (r : ℂ) * Complex.exp (-τ * Complex.I) := by
      change h (g (κ (a₀ 0))) = _
      rw [c.hg (hκ_bHalf _), hp0]
    have hq' : h (a 1) = (r : ℂ) * Complex.exp (τ * Complex.I) := by
      change h (g (κ (a₀ 1))) = _
      rw [c.hg (hκ_bHalf _), hq0]
    have := not_hasLogOn_of_two_sides hAc hBc (ρ := r) (τ := τ) ?_ ?_ hrpos ⟨hτ_pos, by linarith⟩
      hp' hq' ⟨_, ⟨0, rfl⟩, rfl⟩ ⟨_, ⟨1, rfl⟩, rfl⟩ ⟨_, ⟨0, rfl⟩, ?_⟩ ⟨_, ⟨1, rfl⟩, ?_⟩
    · rwa [hPdef, image_union]
    · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      rw [c.hg (hκ_bHalf _)]
      exact hslit _ (ha₀ne s)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hrb' hx
      rw [c.hg (bInt_subset_bHalf (hNb_bInt hz))]
      exact Or.inl (neg_pos.mpr hz.2)
    · rw [hb'0]
    · rw [hb'1]
  obtain ⟨hin, hsub3⟩ := closedBall_subset_inner hQ (Set.disjoint_left.mpr fun z hz hz' => by
    obtain ⟨x, hx, rfl⟩ := hz
    have h1 := (hhP x hx).1.1
    have h2 : ‖h x‖ ≤ 2 := mem_closedBall_zero_iff.mp hz'
    linarith) (fun z hz => by
    obtain ⟨x, hx, rfl⟩ := hz
    exact mem_ball_zero_iff.mpr (hhP x hx).1.2) hlog
  have hQ_bHalf : h '' P ⊆ bHalf := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hhP x hx).2
  have hcl_bHalf : closedInner (h '' P) ⊆ bHalf := closedInner_subset_bHalf hQ hQ_bHalf hsub3
  have hhalf_sub : {z : ℂ | ‖z‖ ≤ 5 / 2 ∧ 0 ≤ z.re} ⊆ closedInner (h '' P) := by
    refine right_halfDisc_subset_closedInner hQ (A := h '' range a) (B := h '' range b')
      (by rw [hPdef, image_union]) hin ?_ ?_ ?_
    · rintro z ⟨hz_norm, hz_re⟩
      obtain ⟨s, hs⟩ := right_semicircle_subset_arc hτ_gt.le hτ_pos hz_norm hz_re
      refine ⟨a s, ⟨s, rfl⟩, ?_⟩
      change h (g (κ (a₀ s))) = z
      rw [c.hg (hκ_bHalf _)]
      simpa [κ, r, ha₀] using hs
    · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      change h (g (κ (a₀ s))) ∈ sphere 0 (5 / 2)
      rw [c.hg (hκ_bHalf _)]
      exact hκ_sph _
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hrb' hx
      rw [c.hg (bInt_subset_bHalf (hNb_bInt hz))]
      exact hz.2
  obtain ⟨hdQ, hdQb⟩ := isClosedDisc_closedInner hQ
  obtain ⟨hE, hEb⟩ := c.image_disc hdQ hcl_bHalf
  have hgP : g '' (h '' P) = P := by
    rw [image_image]
    exact (image_congr fun x hx => c.gh (hPU hx)).trans (image_id _)
  rw [hdQb, hgP] at hEb
  set E := g '' closedInner (h '' P)
  refine ⟨P, E, hPO, htame, hE, hEb, ?_, image_mono hhalf_sub, image_mono hcl_bHalf, ?_⟩
  · refine image_mono fun z hz => Or.inl (hin hz.1)
  · rintro x (⟨s, rfl⟩ | hxb')
    · by_cases hre : 0 ≤ (κ (a₀ s)).re
      · exact Or.inr ⟨κ (a₀ s), ⟨hκn _, hre⟩, rfl⟩
      · push Not at hre
        exact Or.inl ⟨κ (a₀ s), ⟨(hκ_bHalf _).1, hre.trans_le (capH52_nonneg _)⟩, rfl⟩
    · exact Or.inl (hrb'.trans (image_mono hNb_bInt) hxb')

/-- **Merging a closed disc `D` with a `BoundaryHalfChart`.**
Given a closed disc `D ⊆ Y` and a `BoundaryHalfChart U h g` with `g '' bHalf ⊆ Y`,
`g 0 ∈ discInt D`, and `Disjoint D (g '' {z ∈ bHalf | z.re = capH52 z.im})`, there is a closed
disc `D' ⊆ (Y \ bd S) ∪ D ∪ g '' {z : ℂ | ‖z‖ = 5 / 2 ∧ 0 ≤ z.re}` containing both `D` and
`g '' {z : ℂ | ‖z‖ ≤ 5 / 2 ∧ 0 ≤ z.re}`. -/
theorem exists_boundary_disc_merge (hS : IsSurface S) [ConnectedSpace S]
    (hns : ¬ IsSphere S) {Y : Set S}
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    {D : Set S} (hDY : D ⊆ Y) (hD : IsClosedDisc D)
    {U : Set S} {h : S → ℂ} {g : ℂ → S} (c : BoundaryHalfChart U h g)
    (hgY : g '' bHalf ⊆ Y)
    (hg0 : g 0 ∈ discInt D)
    (hD_disj : Disjoint D (g '' {z ∈ bHalf | z.re = capH52 z.im})) :
    ∃ D' : Set S, D' ⊆ (Y \ bd S) ∪ D ∪ g '' {z : ℂ | ‖z‖ = 5 / 2 ∧ 0 ≤ z.re} ∧
      IsClosedDisc D' ∧ D ⊆ D' ∧ g '' {z : ℂ | ‖z‖ ≤ 5 / 2 ∧ 0 ≤ z.re} ⊆ D' := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := hS.2.2
  let Y_step : Set S := (Y \ bd S) ∪ D ∪ g '' {z : ℂ | ‖z‖ = 5 / 2 ∧ 0 ≤ z.re}
  have hsemi_bHalf : {z : ℂ | ‖z‖ = 5 / 2 ∧ 0 ≤ z.re} ⊆ bHalf := fun z hz =>
    (capH52_of_mem_sphere (mem_sphere_zero_iff_norm.mpr hz.1)).2
  have hY_step_sub : Y_step ⊆ Y :=
    union_subset (union_subset sdiff_subset hDY) ((image_mono hsemi_bHalf).trans hgY)
  have hH_step : ∀ F : Set S, F ⊆ Y_step → IsOArc F →
      ∃ Δ : Set S, Δ ⊆ Y_step ∧ IsClosedDisc Δ ∧ discBd Δ = F := by
    intro F hF hFO
    obtain ⟨Δ, hΔY, hΔ, hΔb⟩ := H F (hF.trans hY_step_sub) hFO
    refine ⟨Δ, fun x hx => ?_, hΔ, hΔb⟩
    by_cases hxb : x ∈ discBd Δ
    · exact hF (hΔb ▸ hxb)
    · exact Or.inl (Or.inl ⟨hΔY hx, fun hbd => hbd (isInteriorPoint_of_mem_discInt hman hΔ ⟨hx,
        hxb⟩)⟩)
  have hG := hD.isOArc_discBd
  obtain ⟨φG⟩ := id hG
  have hne : (φG 1).1 ≠ (φG (Circle.exp Real.pi)).1 := fun he => by
    have h1 := φG.injective (Subtype.ext he)
    have h2 := congrArg (fun w : Circle => (w : ℂ)) h1
    simp at h2
    norm_num at h2
  obtain ⟨α, β, hαβ, -, -, hr⟩ := hG.exists_arcs (φG 1).2 (φG _).2 hne
  have hU2 : (⋃ g' ∈ [α, β], range g') = discBd D := by rw [← hr]; simp
  obtain ⟨P, E, hPO, htame, hE, hEb, hclosedin, hhalf_E, hE_bHalf, hP_sub⟩ :=
    exists_boundary_tame_curve hS c hD.isClosed hD_disj [α, β]
      (by simpa using ⟨hαβ.1, hαβ.2⟩) (hU2.trans_subset (discBd_subset D))
  have hbInt_Y : g '' bInt ⊆ Y \ bd S := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hgY ⟨z, bInt_subset_bHalf hz, rfl⟩, fun hbd => ?_⟩
    exact hz.2.ne ((c.bd_iff z (bInt_subset_bHalf hz)).mp hbd)
  have hPY_step : P ⊆ Y_step := by
    rintro x hx
    rcases hP_sub hx with hx1 | hx2
    · exact Or.inl (Or.inl (hbInt_Y hx1))
    · exact Or.inr hx2
  have hEY_step : E ⊆ Y_step := by
    intro x hx
    by_cases hxb : x ∈ discBd E
    · exact hPY_step (hEb ▸ hxb)
    · exact Or.inl (Or.inl ⟨hgY (hE_bHalf hx),
        fun hbd => hbd (isInteriorPoint_of_mem_discInt hman hE ⟨hx, hxb⟩)⟩)
  by_cases h2 : ∃ x y, x ∈ P ∧ y ∈ P ∧ x ∈ D ∧ y ∈ D ∧ x ≠ y
  · obtain ⟨x, y, hxP, hyP, hxD, hyD, hxy⟩ := h2
    rw [hU2] at htame
    obtain ⟨F, hFf, hFc, hFu⟩ := htame
    let F₂ : Set (Set S) := {J ∈ F | Disjoint J D}
    have hF₂ : ⋃₀ F₂ = P \ D := by
      ext w
      constructor
      · rintro ⟨J, ⟨hJ, hJD⟩, hw⟩
        have h3 : w ∈ P \ discBd D := hFu ▸ mem_sUnion_of_mem hw hJ
        exact ⟨h3.1, fun h4 => Set.disjoint_left.mp hJD hw h4⟩
      · rintro ⟨hwP, hwD⟩
        have h3 : w ∈ P \ discBd D := ⟨hwP, fun h4 => hwD (discBd_subset D h4)⟩
        rw [← hFu] at h3
        obtain ⟨J, hJ, hwJ⟩ := h3
        have hJb : Disjoint J (discBd D) := by
          rw [Set.disjoint_left]
          intro v hv hv'
          have : v ∈ P \ discBd D := hFu ▸ mem_sUnion_of_mem hv hJ
          exact this.2 hv'
        rcases hD.side hman (hFc J hJ) hJb with h4 | h4
        · exact absurd (h4 hwJ).1 hwD
        · exact ⟨J, ⟨hJ, h4⟩, hwJ⟩
    have hDY_step : D ⊆ Y_step := fun w hw => Or.inl (Or.inr hw)
    obtain ⟨D', hD'Y, hD', hDD', hPD'⟩ := exists_disc_cover hman hH_step hPY_step hPO hxP hyP hxy
      _ D F₂ hDY_step hD hxD hyD (hFf.subset fun J hJ => hJ.1) le_rfl (fun J hJ => hFc J hJ.1) hF₂
    obtain ⟨Δ, ⟨hΔD, hΔ, hΔb, -⟩, -⟩ := disc_oArc.{u} D' P hD' hPD' hPO
    have hEΔ : E = Δ := eq_of_discBd_eq hS hns hE hΔ (hEb.trans hΔb.symm)
    exact ⟨D', hD'Y, hD', hDD', hhalf_E.trans (hEΔ ▸ hΔD)⟩
  · push Not at h2
    have hdisj : Disjoint (discInt D) P := by
      rw [Set.disjoint_left]
      intro x hx hxP
      have hopen : IsOpen ({x}ᶜ : Set S) := isOpen_compl_singleton
      have hother : ∃ w ∈ P, w ≠ x := by
        obtain ⟨φP⟩ := id hPO
        by_cases h3 : (φP 1).1 = x
        · refine ⟨(φP (Circle.exp Real.pi)).1, (φP _).2, fun h4 => ?_⟩
          have h5 := φP.injective (Subtype.ext (h4.trans h3.symm))
          have h6 := congrArg (fun w : Circle => (w : ℂ)) h5
          simp at h6
          norm_num at h6
        · exact ⟨_, (φP 1).2, h3⟩
      obtain ⟨w, hwP, hwx⟩ := hother
      obtain ⟨v, hvP, hv1, hv2⟩ := hPO.isPreconnected _ _ (hD.isOpen_discInt hman) hopen
        (fun y _ => by
          by_cases h3 : y = x
          · exact .inl (h3 ▸ hx)
          · exact .inr h3) ⟨x, hxP, hx⟩ ⟨w, hwP, hwx⟩
      exact hv2 (h2 x v hxP hvP hx.1 hv1.1).symm
    have h0_in : (0 : ℂ) ∈ closedBall 0 2 ∩ bHalf :=
      ⟨mem_closedBall_zero_iff.mpr (by norm_num), mem_ball_zero_iff.mpr (by norm_num),
        capH52_nonneg 0⟩
    have hbdE : Disjoint (discInt D) (discBd E) := hEb ▸ hdisj
    rcases hE.side hman hD.isPreconnected_discInt hbdE with h3 | h3
    · refine ⟨E, hEY_step, hE, ?_, hhalf_E⟩
      exact hD.subset_closure_discInt.trans
        (closure_minimal (h3.trans (discInt_subset E)) hE.isClosed)
    · exact absurd (hclosedin ⟨0, h0_in, rfl⟩) (Set.disjoint_left.mp h3 hg0)

/-! ## 4. Collar Chart Data and Induction Over Boundary Charts -/

/-- Data of a single boundary collar chart. -/
structure CollarChartData (S : Type u) [TopologicalSpace S] where
  /-- The domain of the boundary chart. -/
  U : Set S
  /-- Coordinate map to the complex plane. -/
  h : S → ℂ
  /-- Inverse coordinate map on the chart image. -/
  g : ℂ → S
  /-- The open neighborhood selected within the chart domain. -/
  W : Set S
  /-- The boundary arc covered by the neighborhood. -/
  bdArc : Set S

/-- Validity predicate for a `CollarChartData S` relative to `Y ⊆ S`. -/
structure IsValidCollarChart (Y : Set S) (d : CollarChartData S) : Prop where
  chart : BoundaryHalfChart d.U d.h d.g
  g_sub_Y : d.g '' bHalf ⊆ Y
  isOpen_W : IsOpen d.W
  W_sub_half : d.W ⊆ d.g '' {z : ℂ | ‖z‖ ≤ 5 / 2 ∧ 0 ≤ z.re}
  bd_sub_arc : d.g '' {z ∈ bHalf | z.re = capH52 z.im} ⊆ d.bdArc
  arc_sub_bd : d.bdArc ⊆ bd S

theorem closedBall_half_subset_bInt : closedBall (0 : ℂ) (1 / 2) ⊆ bInt := by
  intro z hz
  have hnorm : ‖z‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hz
  have hre : z.re ≤ 1 / 2 := (le_abs_self _).trans ((Complex.abs_re_le_norm z).trans hnorm)
  have him : z.im ∈ Icc (-3 / 2 : ℝ) (3 / 2) := by
    have h1 := (Complex.abs_im_le_norm z).trans hnorm
    exact ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2]⟩
  have hcap : 2 ≤ capH52 z.im := two_le_capH52 him
  exact ⟨mem_ball_zero_iff.mpr (by linarith), by linarith⟩

/-- Given a list `L` of valid collar charts with pairwise disjoint `bdArc`s and a closed disc
`D₀ ⊆ Y \ bd S` containing `d.g '' closedBall 0 (1 / 2)` for every `d ∈ L`, we can merge `D₀`
with all charts in `L` to obtain a closed disc `D' ⊆ Y` containing `D₀` and `d.W` for all `d ∈ L`.
-/
theorem exists_disc_merging_collar_charts (hS : IsSurface S) [ConnectedSpace S]
    (hns : ¬ IsSphere S) {Y : Set S}
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    (L : List (CollarChartData S))
    (hvalid : ∀ d ∈ L, IsValidCollarChart Y d)
    (hpw : L.Pairwise (fun d1 d2 => Disjoint d1.bdArc d2.bdArc))
    {D₀ : Set S} (hD₀Y : D₀ ⊆ Y \ bd S) (hD₀ : IsClosedDisc D₀)
    (hballs : ∀ d ∈ L, d.g '' closedBall 0 (1 / 2) ⊆ D₀) :
    ∃ D' : Set S, D' ⊆ (Y \ bd S) ∪ ⋃ d ∈ L, d.bdArc ∧ D' ⊆ Y ∧
      IsClosedDisc D' ∧ D₀ ⊆ D' ∧ ∀ d ∈ L, d.W ⊆ D' := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  induction L with
  | nil =>
    refine ⟨D₀, ?_, hD₀Y.trans sdiff_subset, hD₀, Subset.rfl, by simp⟩
    simp only [List.not_mem_nil, iUnion_of_empty, iUnion_empty, union_empty]
    exact hD₀Y
  | cons d rest ih =>
    obtain ⟨hd_rest, hpw_rest⟩ := List.pairwise_cons.mp hpw
    have hd_val : IsValidCollarChart Y d := hvalid d List.mem_cons_self
    obtain ⟨D₁, hD₁_bd, hD₁Y, hD₁, hD₀D₁, hrest_W⟩ :=
      ih (fun d' hd' => hvalid d' (List.mem_cons_of_mem d hd')) hpw_rest
        (fun d' hd' => hballs d' (List.mem_cons_of_mem d hd'))
    -- Show `d.g 0 ∈ discInt D₁`.
    have hb_open : IsOpen (d.g '' ball 0 (1 / 2)) :=
      hd_val.chart.isOpen_image_bInt hS isOpen_ball
        (ball_subset_closedBall.trans closedBall_half_subset_bInt)
    have hb_int : ∀ x ∈ d.g '' ball 0 (1 / 2), IsInteriorPoint x := by
      rintro _ ⟨z, hz, rfl⟩
      have hz_int := closedBall_half_subset_bInt (ball_subset_closedBall hz)
      by_contra hnot
      exact hz_int.2.ne ((hd_val.chart.bd_iff z (bInt_subset_bHalf hz_int)).mp hnot)
    have hb_sub_D₁ : d.g '' ball 0 (1 / 2) ⊆ D₁ :=
      (image_mono ball_subset_closedBall).trans
        ((hballs d List.mem_cons_self).trans hD₀D₁)
    have hb_discInt : d.g '' ball 0 (1 / 2) ⊆ discInt D₁ :=
      subset_discInt_of_isOpen hb_int hb_open hb_sub_D₁
    have hg0_in : d.g 0 ∈ discInt D₁ :=
      hb_discInt ⟨0, mem_ball_zero_iff.mpr (by norm_num), rfl⟩
    -- Show `Disjoint D₁ (d.g '' {z ∈ bHalf | z.re = capH52 z.im})`.
    have hD₁_disj : Disjoint D₁ (d.g '' {z ∈ bHalf | z.re = capH52 z.im}) := by
      refine Disjoint.mono_right hd_val.bd_sub_arc (Set.disjoint_left.mpr fun x hxD₁ hxd => ?_)
      rcases hD₁_bd hxD₁ with hx_int | hx_rest
      · exact hx_int.2 (hd_val.arc_sub_bd hxd)
      · obtain ⟨d', hd', hxd'⟩ := mem_iUnion₂.mp hx_rest
        exact Set.disjoint_left.mp (hd_rest d' hd') hxd hxd'
    obtain ⟨D', hD'_step, hD', hD₁D', hhalf_D'⟩ :=
      exists_boundary_disc_merge hS hns H hD₁Y hD₁ hd_val.chart hd_val.g_sub_Y hg0_in hD₁_disj
    have hsemi_sub_arc : d.g '' {z : ℂ | ‖z‖ = 5 / 2 ∧ 0 ≤ z.re} ⊆ d.bdArc := by
      refine (image_mono ?_).trans hd_val.bd_sub_arc
      rintro z ⟨hz_norm, hz_re⟩
      have hsph : z ∈ sphere (0 : ℂ) (5 / 2) := mem_sphere_zero_iff_norm.mpr hz_norm
      exact ⟨(capH52_of_mem_sphere hsph).2, (re_eq_capH52_iff_nonneg hsph).mpr hz_re⟩
    have hsemi_sub_Y : d.g '' {z : ℂ | ‖z‖ = 5 / 2 ∧ 0 ≤ z.re} ⊆ Y := by
      refine (image_mono ?_).trans hd_val.g_sub_Y
      rintro z ⟨hz_norm, _⟩
      exact (capH52_of_mem_sphere (mem_sphere_zero_iff_norm.mpr hz_norm)).2
    refine ⟨D', ?_, ?_, hD', hD₀D₁.trans hD₁D', ?_⟩
    · intro x hx
      simp only [List.mem_cons, iUnion_iUnion_eq_or_left]
      rcases hD'_step hx with (hx_int | hxD₁) | hx_semi
      · exact Or.inl hx_int
      · rcases hD₁_bd hxD₁ with hx_int | hx_rest
        · exact Or.inl hx_int
        · exact Or.inr (Or.inr hx_rest)
      · exact Or.inr (Or.inl (hsemi_sub_arc hx_semi))
    · intro x hx
      rcases hD'_step hx with (hx_int | hxD₁) | hx_semi
      · exact hx_int.1
      · exact hD₁Y hxD₁
      · exact hsemi_sub_Y hx_semi
    · intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'_rest
      · exact hd_val.W_sub_half.trans hhalf_D'
      · exact (hrest_W d' hd'_rest).trans hD₁D'

/-! ## 5. Constructing Collar Charts and Concluding `SolidFlatBoundarySurfacePlanarStatement` -/

/-- Clamped collar depth `max 0 (min 1 (-ε * x)) ∈ 𝕀`. -/
noncomputable def tClamped (ε x : ℝ) : 𝕀 :=
  ⟨max 0 (min 1 (-ε * x)), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

@[simp] theorem coe_tClamped (ε x : ℝ) : (tClamped ε x : ℝ) = max 0 (min 1 (-ε * x)) := rfl

theorem continuous_tClamped (ε : ℝ) : Continuous (tClamped ε) := by
  unfold tClamped
  refine Continuous.subtype_mk ?_ _
  fun_prop

theorem tClamped_of_mem_Icc {ε x : ℝ} (hε : 0 < ε) (h6ε : 6 * ε < 1) (hx : x ∈ Icc (-6 : ℝ) 0) :
    (tClamped ε x : ℝ) = -ε * x ∧ (tClamped ε x : ℝ) ∈ Icc 0 (6 * ε) := by
  have h1 : 0 ≤ -ε * x := by nlinarith [hx.2]
  have h2 : -ε * x ≤ 6 * ε := by nlinarith [hx.1]
  have h3 : min 1 (-ε * x) = -ε * x := min_eq_right (by linarith)
  have h4 : max 0 (-ε * x) = -ε * x := max_eq_right h1
  have heq : (tClamped ε x : ℝ) = -ε * x := by rw [coe_tClamped, h3, h4]
  exact ⟨heq, heq ▸ h1, heq ▸ h2⟩

/-- Explicit collar chart map `g : ℂ → S` for an interval `[a, d]` along a collar `b`. -/
noncomputable def collarG (b : Circle × 𝕀 → S) (a d δ ε : ℝ) (z : ℂ) : S :=
  b (Circle.exp (stretchTo a d δ (psiShift z).im), tClamped ε (psiShift z).re)

theorem continuous_collarG {b : Circle × 𝕀 → S} (hbc : Continuous b) (a d δ ε : ℝ) :
    Continuous (collarG b a d δ ε) := by
  unfold collarG
  refine hbc.comp (Continuous.prodMk ?_ ?_)
  · refine Circle.exp.continuous.comp ?_
    have hc_stretch : Continuous (stretchTo a d δ) := by unfold stretchTo; fun_prop
    exact hc_stretch.comp (Complex.continuous_im.comp psiShift.continuous)
  · exact (continuous_tClamped ε).comp (Complex.continuous_re.comp psiShift.continuous)

theorem stretchTo_mem_Icc_of_mem_Icc {a d δ x : ℝ} (had : a < d) (hδ : 0 < δ)
    (hx : x ∈ Icc (-3 : ℝ) 3) :
    stretchTo a d δ x ∈ Icc (a - 2 * δ) (d + 2 * δ) := by
  have hmono := (stretchTo_strictMono had hδ).monotone
  have hpts := stretchTo_eval_pts a d δ
  exact ⟨hpts.1 ▸ hmono hx.1, hpts.2.2.2.2.2 ▸ hmono hx.2⟩

/-- Construct a `CollarChartData S` from an isolated collar `b : Circle × 𝕀 → S` and interval
parameters `(a, d, δ₀, δ, ε)`. -/
noncomputable def mkCollarChart [T2Space S]
    {b : Circle × 𝕀 → S} (hbc : Continuous b) (hbi : Function.Injective b)
    {a d δ₀ δ ε : ℝ} (_hδ₀ : 0 < δ₀) (ha : δ₀ ≤ a) (had : a < d) (hd : d ≤ 2 * Real.pi - δ₀)
    (hδ : 0 < δ) (h2δ : 2 * δ < δ₀) (hε : 0 < ε) (h6ε : 6 * ε < 1) :
    CollarChartData S :=
  let g := collarG b a d δ ε
  let K_big : Set ℂ := psiShift.symm '' (Icc (-6 : ℝ) 0 ×ℂ Icc (-3 : ℝ) 3)
  have hK_big : IsCompact K_big :=
    (isCompact_Icc.reProdIm isCompact_Icc).image psiShift.symm.continuous
  have hinj : InjOn g K_big := by
    rintro z₁ ⟨w₁, hw₁, rfl⟩ z₂ ⟨w₂, hw₂, rfl⟩ heq
    have hprod := Prod.ext_iff.mp (hbi heq)
    have h1 := hprod.1
    have h2 := congrArg Subtype.val hprod.2
    simp only [psiShift.apply_symm_apply] at h1 h2
    rw [(tClamped_of_mem_Icc hε h6ε hw₁.1).1, (tClamped_of_mem_Icc hε h6ε hw₂.1).1] at h2
    have hre : w₁.re = w₂.re := by nlinarith
    have hm1 := stretchTo_mem_Icc_of_mem_Icc had hδ hw₁.2
    have hm2 := stretchTo_mem_Icc_of_mem_Icc had hδ hw₂.2
    have hIoc1 : stretchTo a d δ w₁.im ∈ Ioc 0 (2 * Real.pi) :=
      ⟨by linarith [hm1.1], by linarith [hm1.2]⟩
    have hIoc2 : stretchTo a d δ w₂.im ∈ Ioc 0 (2 * Real.pi) :=
      ⟨by linarith [hm2.1], by linarith [hm2.2]⟩
    have hst_eq : stretchTo a d δ w₁.im = stretchTo a d δ w₂.im :=
      Circle.exp_injOn_Ioc (a := 0) (b := 2 * Real.pi) (by linarith) hIoc1 hIoc2 h1
    have him : w₁.im = w₂.im := by
      have := congrArg (unstretchFrom a d δ) hst_eq
      rwa [unstretchFrom_stretchTo had hδ, unstretchFrom_stretchTo had hδ] at this
    rw [Complex.ext hre him]
  let h := Classical.choose (exists_inv_of_compact hK_big (continuous_collarG hbc a d δ ε) hinj)
  { U := g '' bHalf
    h := h
    g := g
    W := b '' ((Circle.exp '' Ioo a d) ×ˢ {t : 𝕀 | t.1 < ε})
    bdArc := b '' ((Circle.exp '' Icc (a - 2 * δ) (d + 2 * δ)) ×ˢ {0}) }

theorem mkCollarChart_valid (hS : IsSurface S) {Y C : Set S} (hC_sub_bd : C ⊆ bd S)
    {b : Circle × 𝕀 → S} (hbc : Continuous b) (hbi : Function.Injective b)
    (hopen : IsOpen (range b \ b '' {x | x.2 = 1}))
    (hbd_iff : ∀ w t, b (w, t) ∈ bd S ↔ t = 0)
    (hbC : ∀ w, b (w, 0) ∈ C)
    {a d δ₀ δ ε : ℝ} (hδ₀ : 0 < δ₀) (ha : δ₀ ≤ a) (had : a < d) (hd : d ≤ 2 * Real.pi - δ₀)
    (hδ : 0 < δ) (h2δ : 2 * δ < δ₀) (hε : 0 < ε) (h6ε : 6 * ε < 1)
    (hbY : ∀ θ ∈ Icc (a - 2 * δ) (d + 2 * δ), ∀ t : 𝕀, t.1 ≤ 6 * ε → b (Circle.exp θ, t) ∈ Y) :
    let ch := @mkCollarChart S _ hS.2.1 b hbc hbi a d δ₀ δ ε hδ₀ ha had hd hδ h2δ hε h6ε
    IsValidCollarChart Y ch ∧
    ch.bdArc = b '' ((Circle.exp '' Icc (a - 2 * δ) (d + 2 * δ)) ×ˢ {0}) ∧
    ch.bdArc ⊆ C ∧
    (∀ θ ∈ Ioo a d, b (Circle.exp θ, 0) ∈ ch.W) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  set ch := @mkCollarChart S _ hS.2.1 b hbc hbi a d δ₀ δ ε hδ₀ ha had hd hδ h2δ hε h6ε
  let g := collarG b a d δ ε
  let K_big : Set ℂ := psiShift.symm '' (Icc (-6 : ℝ) 0 ×ℂ Icc (-3 : ℝ) 3)
  have hK_big : IsCompact K_big :=
    (isCompact_Icc.reProdIm isCompact_Icc).image psiShift.symm.continuous
  have hinj : InjOn g K_big := by
    rintro z₁ ⟨w₁, hw₁, rfl⟩ z₂ ⟨w₂, hw₂, rfl⟩ heq
    have hprod := Prod.ext_iff.mp (hbi heq)
    have h1 := hprod.1
    have h2 := congrArg Subtype.val hprod.2
    simp only [psiShift.apply_symm_apply] at h1 h2
    rw [(tClamped_of_mem_Icc hε h6ε hw₁.1).1, (tClamped_of_mem_Icc hε h6ε hw₂.1).1] at h2
    have hre : w₁.re = w₂.re := by nlinarith
    have hm1 := stretchTo_mem_Icc_of_mem_Icc had hδ hw₁.2
    have hm2 := stretchTo_mem_Icc_of_mem_Icc had hδ hw₂.2
    have hIoc1 : stretchTo a d δ w₁.im ∈ Ioc 0 (2 * Real.pi) :=
      ⟨by linarith [hm1.1], by linarith [hm1.2]⟩
    have hIoc2 : stretchTo a d δ w₂.im ∈ Ioc 0 (2 * Real.pi) :=
      ⟨by linarith [hm2.1], by linarith [hm2.2]⟩
    have hst_eq : stretchTo a d δ w₁.im = stretchTo a d δ w₂.im :=
      Circle.exp_injOn_Ioc (a := 0) (b := 2 * Real.pi) (by linarith) hIoc1 hIoc2 h1
    have him : w₁.im = w₂.im := by
      have := congrArg (unstretchFrom a d δ) hst_eq
      rwa [unstretchFrom_stretchTo had hδ, unstretchFrom_stretchTo had hδ] at this
    rw [Complex.ext hre him]
  have hspec := Classical.choose_spec
    (exists_inv_of_compact hK_big (continuous_collarG hbc a d δ ε) hinj)
  have hbHalf_K : bHalf ⊆ K_big := by
    intro z hz
    obtain ⟨hre, him⟩ := psiShift_ball3_bounds hz.1 hz.2
    exact ⟨psiShift z, ⟨hre, ⟨him.1.le, him.2.le⟩⟩, psiShift.symm_apply_apply z⟩
  have hch_h : ch.h = Classical.choose
      (exists_inv_of_compact hK_big (continuous_collarG hbc a d δ ε) hinj) := rfl
  have hch_g : ch.g = g := rfl
  have hchart : BoundaryHalfChart ch.U ch.h ch.g := by
    refine ⟨hspec.1.mono (image_mono hbHalf_K), continuous_collarG hbc a d δ ε,
      ?_, mapsTo_image g bHalf, ?_, hspec.2.mono hbHalf_K, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      rw [hch_h, hspec.2 (hbHalf_K hz)]
      exact hz
    · rintro _ ⟨z, hz, rfl⟩
      rw [hch_h, hch_g, hspec.2 (hbHalf_K hz)]
    · intro z hz
      obtain ⟨hre, _⟩ := psiShift_ball3_bounds hz.1 hz.2
      rw [show ch.g z = collarG b a d δ ε z from rfl, collarG, hbd_iff, Subtype.ext_iff,
        (tClamped_of_mem_Icc hε h6ε hre).1, Icc.coe_zero]
      constructor
      · intro h0
        have : (psiShift z).re = 0 := by nlinarith
        rw [psiShift_re] at this
        linarith
      · intro h0
        have : (psiShift z).re = 0 := by rw [psiShift_re]; linarith
        rw [this, mul_zero]
  have hgY : ch.g '' bHalf ⊆ Y := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hre, him⟩ := psiShift_ball3_bounds hz.1 hz.2
    exact hbY _ (stretchTo_mem_Icc_of_mem_Icc had hδ ⟨him.1.le, him.2.le⟩)
      _ (tClamped_of_mem_Icc hε h6ε hre).2.2
  have hW_open : IsOpen ch.W := by
    refine isOpen_image_of_collar hbc hbi hopen ?_ ?_
    · exact (isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo).prod
        (isOpen_lt continuous_subtype_val continuous_const)
    · rintro ⟨_, t⟩ ⟨_, ht⟩
      exact Subtype.mk_lt_mk.mpr (ht.trans (by linarith))
  have hW_half : ch.W ⊆ ch.g '' {z : ℂ | ‖z‖ ≤ 5 / 2 ∧ 0 ≤ z.re} := by
    rintro _ ⟨⟨_, t⟩, ⟨⟨θ, hθ, rfl⟩, ht : t.1 < ε⟩, rfl⟩
    let w : ℂ := ⟨-(t.1 / ε), unstretchFrom a d δ θ⟩
    let z : ℂ := psiShift.symm w
    have hw_re : w.re ∈ Icc (-2 : ℝ) 0 := by
      have h1 : t.1 / ε ≤ 1 := (div_le_one hε).mpr ht.le
      have h2 : 0 ≤ t.1 / ε := div_nonneg t.2.1 hε.le
      exact ⟨by dsimp [w]; linarith, by dsimp [w]; linarith⟩
    have hw_im : w.im ∈ Icc (-3 / 2 : ℝ) (3 / 2) := by
      dsimp [w]
      rw [unstretchFrom_of_mem_Icc ⟨hθ.1.le, hθ.2.le⟩]
      have hpos : 0 < (d - a) / 2 := by linarith
      have h1 : -1 ≤ (θ - (a + d) / 2) / ((d - a) / 2) := by
        rw [le_div_iff₀ hpos]; linarith [hθ.1]
      have h2 : (θ - (a + d) / 2) / ((d - a) / 2) ≤ 1 := by
        rw [div_le_iff₀ hpos]; linarith [hθ.2]
      exact ⟨by linarith, by linarith⟩
    refine ⟨z, psiShift_symm_mem_closedBall hw_re hw_im, ?_⟩
    change b (Circle.exp (stretchTo a d δ (psiShift z).im), tClamped ε (psiShift z).re) =
      b (Circle.exp θ, t)
    rw [psiShift.apply_symm_apply]
    have hst : stretchTo a d δ w.im = θ := stretchTo_unstretchFrom had hδ θ
    have htc : tClamped ε w.re = t := by
      ext
      dsimp [w]
      have hmul : -ε * -(t.1 / ε) = t.1 := by field_simp
      rw [hmul, min_eq_right t.2.2, max_eq_right t.2.1]
    rw [hst, htc]
  have hbd_arc : ch.g '' {z ∈ bHalf | z.re = capH52 z.im} ⊆ ch.bdArc := by
    rintro _ ⟨z, ⟨hz, hre_eq⟩, rfl⟩
    obtain ⟨_, him⟩ := psiShift_ball3_bounds hz.1 hz.2
    have hre0 : (psiShift z).re = 0 := by rw [psiShift_re, hre_eq, sub_self]
    have htc0 : tClamped ε (psiShift z).re = 0 := by
      rw [hre0]
      ext
      simp [tClamped]
    refine ⟨(Circle.exp (stretchTo a d δ (psiShift z).im), 0), ⟨⟨_, ?_, rfl⟩, rfl⟩, ?_⟩
    · exact stretchTo_mem_Icc_of_mem_Icc had hδ ⟨him.1.le, him.2.le⟩
    · change b (Circle.exp (stretchTo a d δ (psiShift z).im), 0) =
        b (Circle.exp (stretchTo a d δ (psiShift z).im), tClamped ε (psiShift z).re)
      rw [htc0]
  have harc_C : ch.bdArc ⊆ C := by
    rintro _ ⟨⟨w, t⟩, ⟨_, ht : t = 0⟩, rfl⟩
    rw [ht]
    exact hbC w
  refine ⟨⟨hchart, hgY, hW_open, hW_half, hbd_arc, harc_C.trans hC_sub_bd⟩, rfl, harc_C, ?_⟩
  intro θ hθ
  exact ⟨(Circle.exp θ, 0), ⟨⟨θ, hθ, rfl⟩, hε⟩, rfl⟩

theorem isCompact_unionIcc (L : List (ℝ × ℝ)) : IsCompact (unionIcc L) := by
  induction L with
  | nil => exact isCompact_empty
  | cons p rest ih => exact isCompact_Icc.union ih

private theorem exists_finite_angular_neighborhoods
    {K_θ target : Set ℝ} (hK_θ : IsCompact K_θ) {δ₀ η r₁ : ℝ}
    (hK_sub : K_θ ⊆ Icc (2 * δ₀) (2 * Real.pi - 2 * δ₀))
    (hη_pos : 0 < η) (hη_δ₀ : η ≤ δ₀ / 2) (hη_r₁ : η < r₁)
    (hr₁_sub : Metric.thickening r₁ K_θ ⊆ target) :
    ∃ L_raw : List (ℝ × ℝ), (∀ p ∈ L_raw, p.1 < p.2) ∧
      (∀ p ∈ L_raw, δ₀ ≤ p.1 ∧ p.2 ≤ 2 * Real.pi - δ₀) ∧
      K_θ ⊆ unionIoo L_raw ∧ unionIcc L_raw ⊆ target := by
  obtain ⟨s, hs_cov⟩ := hK_θ.elim_finite_subcover
    (fun θ : K_θ => Ioo (θ.1 - η) (θ.1 + η)) (fun _ => isOpen_Ioo)
    (fun θ hθ => mem_iUnion.mpr ⟨⟨θ, hθ⟩, by linarith, by linarith⟩)
  let L_raw : List (ℝ × ℝ) := s.toList.map (fun θ : K_θ => (θ.1 - η, θ.1 + η))
  have hL_lt : ∀ p ∈ L_raw, p.1 < p.2 := by
    rintro p hp
    obtain ⟨θ, _, rfl⟩ := List.mem_map.mp hp
    linarith
  have hL_cd : ∀ p ∈ L_raw, δ₀ ≤ p.1 ∧ p.2 ≤ 2 * Real.pi - δ₀ := by
    rintro p hp
    obtain ⟨θ, _, rfl⟩ := List.mem_map.mp hp
    exact ⟨by linarith [(hK_sub θ.2).1], by linarith [(hK_sub θ.2).2]⟩
  have hK_cov : K_θ ⊆ unionIoo L_raw := by
    intro x hx
    obtain ⟨θ, hθs, hx_Ioo⟩ := mem_iUnion₂.mp (hs_cov hx)
    refine mem_unionIoo.mpr ⟨(θ.1 - η, θ.1 + η), ?_, hx_Ioo⟩
    exact List.mem_map.mpr ⟨θ, Finset.mem_toList.mpr hθs, rfl⟩
  have hL_Y : unionIcc L_raw ⊆ target := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_unionIcc.mp hx
    obtain ⟨θ, _, rfl⟩ := List.mem_map.mp hp
    refine hr₁_sub (Metric.mem_thickening_iff.mpr ⟨θ.1, θ.2, ?_⟩)
    rw [Real.dist_eq]
    have hx_ge : θ.1 - η ≤ x := hxp.1
    have hx_le : x ≤ θ.1 + η := hxp.2
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans_lt hη_r₁
  exact ⟨L_raw, hL_lt, hL_cd, hK_cov, hL_Y⟩

/-- For a single cuff `C ∈ cuffs S` with `¬ C ⊆ Y`, construct a finite list `L` of valid collar
charts along `C` with pairwise disjoint `bdArc ⊆ C` whose open sets `d.W` cover `Z ∩ C`. -/
theorem exists_collar_charts_for_cuff (hS : IsSurface S) {Z Y C : Set S}
    (hZ : IsCompact Z) (hYo : IsOpen Y) (hZY : Z ⊆ Y) (hC : IsCuff C) (hnotCY : ¬ C ⊆ Y) :
    ∃ L : List (CollarChartData S),
      (∀ d ∈ L, IsValidCollarChart Y d ∧ d.bdArc ⊆ C) ∧
      L.Pairwise (fun d1 d2 => Disjoint d1.bdArc d2.bdArc) ∧
      Z ∩ C ⊆ ⋃ d ∈ L, d.W := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨y_miss, hy_miss, hy_notY⟩ := Set.not_subset.mp hnotCY
  have hy_notZ : y_miss ∉ Z := fun h => hy_notY (hZY h)
  have hCO : IsOArc C := (cuff_statement.{u} S hS).2.2 C hC
  obtain ⟨φ₀⟩ := id hCO
  let u_miss : Circle := φ₀.symm ⟨y_miss, hy_miss⟩
  let φ : Circle ≃ₜ C := (Homeomorph.mulRight u_miss).trans φ₀
  have hφ1 : (φ 1).1 = y_miss := by
    change (φ₀ (1 * u_miss)).1 = y_miss
    rw [one_mul, Homeomorph.apply_symm_apply]
  obtain ⟨b, hbc, hbi, _, hb0, hopen, hbd_iff⟩ :=
    exists_isolated_collar hS hC φ isOpen_univ (subset_univ _)
  have hbC : ∀ w, b (w, 0) ∈ C := fun w => by rw [hb0]; exact (φ w).2
  have hC_sub_bd : C ⊆ bd S := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  let f₀ : ℝ → S := fun θ => b (Circle.exp θ, 0)
  have hf₀c : Continuous f₀ := hbc.comp (Circle.exp.continuous.prodMk continuous_const)
  have hf₀_0 : f₀ 0 ∉ Z := by
    change b (Circle.exp 0, 0) ∉ Z
    rw [Circle.exp_zero, hb0, hφ1]
    exact hy_notZ
  have hf₀_2pi : f₀ (2 * Real.pi) ∉ Z := by
    change b (Circle.exp (2 * Real.pi), 0) ∉ Z
    rw [Circle.exp_two_pi, hb0, hφ1]
    exact hy_notZ
  have hnotZ_open : IsOpen (f₀ ⁻¹' Zᶜ) := hZ.isClosed.isOpen_compl.preimage hf₀c
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.isOpen_iff.mp hnotZ_open 0 hf₀_0
  obtain ⟨r₂, hr₂_pos, hr₂_sub⟩ := Metric.isOpen_iff.mp hnotZ_open (2 * Real.pi) hf₀_2pi
  let δ₀ : ℝ := min (1 / 2) (min (r₀ / 3) (r₂ / 3))
  have hδ₀_pos : 0 < δ₀ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδ₀_r₀ : 2 * δ₀ < r₀ := by
    have : δ₀ ≤ r₀ / 3 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hδ₀_r₂ : 2 * δ₀ < r₂ := by
    have : δ₀ ≤ r₂ / 3 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  let K_θ : Set ℝ := Icc (2 * δ₀) (2 * Real.pi - 2 * δ₀) ∩ f₀ ⁻¹' Z
  have hK_θ : IsCompact K_θ := isCompact_Icc.inter_right (hZ.isClosed.preimage hf₀c)
  have hU_θ : IsOpen (f₀ ⁻¹' Y) := hYo.preimage hf₀c
  have hKU : K_θ ⊆ f₀ ⁻¹' Y := fun θ hθ => hZY hθ.2
  obtain ⟨r₁, hr₁_pos, hr₁_sub⟩ := hK_θ.exists_thickening_subset_open hU_θ hKU
  let η : ℝ := min (δ₀ / 2) (r₁ / 2)
  have hη_pos : 0 < η := lt_min (by positivity) (by positivity)
  have hη_δ₀ : η ≤ δ₀ / 2 := min_le_left _ _
  have hη_r₁ : η < r₁ := (min_le_right _ _).trans_lt (half_lt_self hr₁_pos)
  obtain ⟨L_raw, hL_lt, hL_cd, hK_cov, hL_Y⟩ :=
    exists_finite_angular_neighborhoods hK_θ inter_subset_left hη_pos hη_δ₀ hη_r₁ hr₁_sub
  let L_merged : List (ℝ × ℝ) := mergeList L_raw
  obtain ⟨hm_bounds, hm_pw, hm_Ioo, hm_Icc⟩ :=
    mergeList_properties L_raw hL_lt δ₀ (2 * Real.pi - δ₀) hL_cd
  obtain ⟨δ₁, hδ₁_pos, h2δ₁_lt, hm_gap⟩ := exists_min_gap L_merged hδ₀_pos hm_pw
  let F_collar : ℝ × 𝕀 → S := fun x => b (Circle.exp x.1, x.2)
  have hF_cont : Continuous F_collar :=
    hbc.comp ((Circle.exp.continuous.comp continuous_fst).prodMk continuous_snd)
  have hK_box : IsCompact (unionIcc L_merged ×ˢ {(0 : 𝕀)}) :=
    (isCompact_unionIcc L_merged).prod isCompact_singleton
  have hK_box_sub : unionIcc L_merged ×ˢ {(0 : 𝕀)} ⊆ F_collar ⁻¹' Y := by
    rintro ⟨θ, t⟩ ⟨hθ, ht : t = 0⟩
    rw [ht]
    exact hL_Y (hm_Icc hθ)
  obtain ⟨r_box, hr_box_pos, hr_box_sub⟩ :=
    hK_box.exists_thickening_subset_open (hYo.preimage hF_cont) hK_box_sub
  let δ : ℝ := min δ₁ (r_box / 3)
  have hδ_pos : 0 < δ := lt_min hδ₁_pos (by positivity)
  have hδ_le_δ₁ : δ ≤ δ₁ := min_le_left _ _
  have h2δ_lt_δ₀ : 2 * δ < δ₀ := by linarith
  have h2δ_lt_r : 2 * δ < r_box := by
    have : δ ≤ r_box / 3 := min_le_right _ _
    linarith
  let ε : ℝ := min (1 / 7) (r_box / 7)
  have hε_pos : 0 < ε := lt_min (by norm_num) (by positivity)
  have h6ε_lt_1 : 6 * ε < 1 := by
    have : ε ≤ 1 / 7 := min_le_left _ _
    linarith
  have h6ε_lt_r : 6 * ε < r_box := by
    have : ε ≤ r_box / 7 := min_le_right _ _
    linarith
  have hbY_all : ∀ p ∈ L_merged, ∀ θ ∈ Icc (p.1 - 2 * δ) (p.2 + 2 * δ),
      ∀ t : 𝕀, t.1 ≤ 6 * ε → b (Circle.exp θ, t) ∈ Y := by
    intro p hp θ hθ t ht
    have hp_lt := (hm_bounds p hp).1
    let θ₀ : ℝ := max p.1 (min p.2 θ)
    have hθ₀_Icc : θ₀ ∈ Icc p.1 p.2 :=
      ⟨le_max_left _ _, max_le hp_lt.le (min_le_left _ _)⟩
    have hθ₀_mem : (θ₀, (0 : 𝕀)) ∈ unionIcc L_merged ×ˢ {(0 : 𝕀)} :=
      ⟨mem_unionIcc.mpr ⟨p, hp, hθ₀_Icc⟩, rfl⟩
    have hmem_pre : (θ, t) ∈ F_collar ⁻¹' Y := by
      refine hr_box_sub (Metric.mem_thickening_iff.mpr ⟨(θ₀, 0), hθ₀_mem, ?_⟩)
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨?_, ?_⟩
      · rw [Real.dist_eq]
        refine (abs_le.mpr ?_).trans_lt h2δ_lt_r
        constructor
        · rcases le_total θ p.2 with h1 | h1
          · simp only [θ₀, min_eq_right h1]
            rcases le_total p.1 θ with h2 | h2
            · simp [max_eq_right h2]; linarith
            · simp [max_eq_left h2]; linarith [hθ.1]
          · simp only [θ₀, min_eq_left h1, max_eq_right hp_lt.le]
            linarith [hθ.1, hp_lt]
        · rcases le_total θ p.2 with h1 | h1
          · simp only [θ₀, min_eq_right h1]
            rcases le_total p.1 θ with h2 | h2
            · simp [max_eq_right h2]; linarith
            · simp [max_eq_left h2]; linarith [hθ.1]
          · simp only [θ₀, min_eq_left h1, max_eq_right hp_lt.le]
            linarith [hθ.2]
      · rw [Subtype.dist_eq, Icc.coe_zero, Real.dist_eq, sub_zero, abs_of_nonneg t.2.1]
        exact ht.trans_lt h6ε_lt_r
    exact hmem_pre
  let mkP : {p : ℝ × ℝ // p ∈ L_merged} → CollarChartData S := fun ⟨p, hp⟩ =>
    @mkCollarChart S _ hS.2.1 b hbc hbi p.1 p.2 δ₀ δ ε
      hδ₀_pos (hm_bounds p hp).2.1 (hm_bounds p hp).1 (hm_bounds p hp).2.2
      hδ_pos h2δ_lt_δ₀ hε_pos h6ε_lt_1
  let L : List (CollarChartData S) := L_merged.attach.map mkP
  refine ⟨L, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨⟨p, hp⟩, _, rfl⟩ := List.mem_map.mp hd
    have hval := mkCollarChart_valid hS hC_sub_bd hbc hbi hopen hbd_iff hbC
      hδ₀_pos (hm_bounds p hp).2.1 (hm_bounds p hp).1 (hm_bounds p hp).2.2
      hδ_pos h2δ_lt_δ₀ hε_pos h6ε_lt_1 (hbY_all p hp)
    exact ⟨hval.1, hval.2.2.1⟩
  · rw [List.pairwise_map]
    rw [List.pairwise_iff_getElem] at hm_gap ⊢
    intro i j hi hj hij
    simp only [List.length_attach] at hi hj
    simp only [List.getElem_attach]
    set p := L_merged[i]
    set q := L_merged[j]
    have hp : p ∈ L_merged := List.getElem_mem hi
    have hq : q ∈ L_merged := List.getElem_mem hj
    have hgap := hm_gap i j hi hj hij
    have hval_p := mkCollarChart_valid hS hC_sub_bd hbc hbi hopen hbd_iff hbC
      hδ₀_pos (hm_bounds p hp).2.1 (hm_bounds p hp).1 (hm_bounds p hp).2.2
      hδ_pos h2δ_lt_δ₀ hε_pos h6ε_lt_1 (hbY_all p hp)
    have hval_q := mkCollarChart_valid hS hC_sub_bd hbc hbi hopen hbd_iff hbC
      hδ₀_pos (hm_bounds q hq).2.1 (hm_bounds q hq).1 (hm_bounds q hq).2.2
      hδ_pos h2δ_lt_δ₀ hε_pos h6ε_lt_1 (hbY_all q hq)
    rw [Set.disjoint_left]
    intro x hxp hxq
    rw [hval_p.2.1] at hxp
    rw [hval_q.2.1] at hxq
    obtain ⟨⟨_, t₁⟩, ⟨⟨θ₁, hθ₁, rfl⟩, ht₁ : t₁ = 0⟩, rfl⟩ := hxp
    obtain ⟨⟨_, t₂⟩, ⟨⟨θ₂, hθ₂, rfl⟩, ht₂ : t₂ = 0⟩, heq⟩ := hxq
    have hexp : Circle.exp θ₁ = Circle.exp θ₂ := (Prod.ext_iff.mp (hbi heq)).1.symm
    have hbp := hm_bounds p hp
    have hbq := hm_bounds q hq
    have hIoc1 : θ₁ ∈ Ioc 0 (2 * Real.pi) :=
      ⟨by linarith [hθ₁.1, hbp.2.1], by linarith [hθ₁.2, hbp.2.2]⟩
    have hIoc2 : θ₂ ∈ Ioc 0 (2 * Real.pi) :=
      ⟨by linarith [hθ₂.1, hbq.2.1], by linarith [hθ₂.2, hbq.2.2]⟩
    have hθ_eq : θ₁ = θ₂ :=
      Circle.exp_injOn_Ioc (a := 0) (b := 2 * Real.pi) (by linarith) hIoc1 hIoc2 hexp
    rcases hgap with hlt | hlt <;> linarith [hθ₁.1, hθ₁.2, hθ₂.1, hθ₂.2]
  · rintro x ⟨hxZ, hxC⟩
    let w : Circle := φ.symm ⟨x, hxC⟩
    have hbw : b (w, 0) = x := by
      rw [hb0]
      exact congrArg Subtype.val (φ.apply_symm_apply ⟨x, hxC⟩)
    obtain ⟨θ, hθ_Ioc, hθ_exp⟩ := exists_circle_angle 1 w
    rw [one_mul] at hθ_exp
    have hf₀_θ : f₀ θ = x := by
      change b (Circle.exp θ, 0) = x
      rw [← hθ_exp, hbw]
    have hθ_ge : 2 * δ₀ ≤ θ := by
      by_contra hlt
      have hmem : θ ∈ Metric.ball 0 r₀ := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hθ_Ioc.1]
        linarith
      exact hr₀_sub hmem (by show f₀ θ ∈ Z; rwa [hf₀_θ])
    have hθ_le : θ ≤ 2 * Real.pi - 2 * δ₀ := by
      by_contra hgt
      have hmem : θ ∈ Metric.ball (2 * Real.pi) r₂ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
        exact ⟨by linarith [hθ_Ioc.2], by linarith⟩
      exact hr₂_sub hmem (by show f₀ θ ∈ Z; rwa [hf₀_θ])
    have hθ_K : θ ∈ K_θ := ⟨⟨hθ_ge, hθ_le⟩, by change f₀ θ ∈ Z; rwa [hf₀_θ]⟩
    obtain ⟨p, hp, hθ_p⟩ := mem_unionIoo.mp (hm_Ioo (hK_cov hθ_K))
    have hval_p := mkCollarChart_valid hS hC_sub_bd hbc hbi hopen hbd_iff hbC
      hδ₀_pos (hm_bounds p hp).2.1 (hm_bounds p hp).1 (hm_bounds p hp).2.2
      hδ_pos h2δ_lt_δ₀ hε_pos h6ε_lt_1 (hbY_all p hp)
    refine mem_iUnion₂.mpr ⟨mkP ⟨p, hp⟩, List.mem_map.mpr ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩, ?_⟩
    rw [← hf₀_θ]
    exact hval_p.2.2.2 θ hθ_p

/-- Combine collar chart lists over a nodup list of cuffs `cs`. -/
theorem exists_combined_collar_charts (hS : IsSurface S) {Z Y : Set S}
    (hZ : IsCompact Z) (hYo : IsOpen Y) (hZY : Z ⊆ Y)
    (cs : List {C : Set S // C ∈ cuffs S}) (hnodup : cs.Nodup)
    (hnotCY : ∀ c ∈ cs, ¬ c.1 ⊆ Y) :
    ∃ L_all : List (CollarChartData S),
      (∀ d ∈ L_all, IsValidCollarChart Y d ∧ ∃ c ∈ cs, d.bdArc ⊆ c.1) ∧
      L_all.Pairwise (fun d1 d2 => Disjoint d1.bdArc d2.bdArc) ∧
      ∀ c ∈ cs, Z ∩ c.1 ⊆ ⋃ d ∈ L_all, d.W := by
  induction cs with
  | nil =>
    exact ⟨[], by simp, List.Pairwise.nil, by simp⟩
  | cons c rest ih =>
    obtain ⟨hc_notMem, hnodup_rest⟩ := List.nodup_cons.mp hnodup
    obtain ⟨L_rest, hrest_val, hrest_pw, hrest_cov⟩ :=
      ih hnodup_rest (fun c' hc' => hnotCY c' (List.mem_cons_of_mem c hc'))
    obtain ⟨L_c, hc_val, hc_pw, hc_cov⟩ :=
      exists_collar_charts_for_cuff hS hZ hYo hZY c.2 (hnotCY c List.mem_cons_self)
    refine ⟨L_c ++ L_rest, ?_, ?_, ?_⟩
    · intro d hd
      rcases List.mem_append.mp hd with hdc | hdr
      · obtain ⟨h1, h2⟩ := hc_val d hdc
        exact ⟨h1, c, List.mem_cons_self, h2⟩
      · obtain ⟨h1, c', hc', h2⟩ := hrest_val d hdr
        exact ⟨h1, c', List.mem_cons_of_mem c hc', h2⟩
    · refine List.pairwise_append.mpr ⟨hc_pw, hrest_pw, ?_⟩
      intro d₁ hd₁ d₂ hd₂
      have hd₁_sub : d₁.bdArc ⊆ c.1 := (hc_val d₁ hd₁).2
      obtain ⟨_, c', hc', hd₂_sub⟩ := hrest_val d₂ hd₂
      refine Disjoint.mono hd₁_sub hd₂_sub (Set.disjoint_left.mpr fun x hxc hxc' => ?_)
      obtain ⟨y₁, _, hEq₁⟩ := c.2
      obtain ⟨y₂, _, hEq₂⟩ := c'.2
      have hx₁ : x ∈ connectedComponentIn (bd S) y₁ := by rwa [hEq₁]
      have hx₂ : x ∈ connectedComponentIn (bd S) y₂ := by rwa [hEq₂]
      have h1 : connectedComponentIn (bd S) x = c.1 :=
        (connectedComponentIn_eq hx₁).symm.trans hEq₁
      have h2 : connectedComponentIn (bd S) x = c'.1 :=
        (connectedComponentIn_eq hx₂).symm.trans hEq₂
      exact hc_notMem (Subtype.ext (h1.symm.trans h2) ▸ hc')
    · intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'_rest
      · refine hc_cov.trans (iUnion₂_mono' fun d hd => ⟨d, List.mem_append_left _ hd, Subset.rfl⟩)
      · refine (hrest_cov c' hc'_rest).trans
          (iUnion₂_mono' fun d hd => ⟨d, List.mem_append_right _ hd, Subset.rfl⟩)

/-- **Core theorem for `SolidFlatBoundarySurfacePlanarStatement`:**
In a connected surface `S` with `bd S ≠ ∅`, if `Z ⊆ Y ⊆ S` with `Z` closed, `Y` open and
preconnected, and every `O`-arc `F ⊆ Y` bounding a closed disc `Δ ⊆ Y`, then `IsPlanar Z`. -/
theorem solidFlat_boundarySurface_planar_core (hS : IsSurface S) [ConnectedSpace S]
    (hbd : bd S ≠ ∅) {Z Y : Set S} (hZc : IsClosed Z) (hZY : Z ⊆ Y)
    (hYo : IsOpen Y) (hYp : IsPreconnected Y)
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F) :
    IsPlanar Z := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  rcases Y.eq_empty_or_nonempty with rfl | hYne
  · have hZ_empty : Z = ∅ := eq_empty_of_subset hZY rfl
    obtain ⟨x₀⟩ := ‹ConnectedSpace S›.toNonempty
    obtain ⟨D₀, _, hD₀⟩ := exists_initial_disc_interior hS isOpen_univ ⟨x₀, mem_univ x₀⟩
    exact ⟨D₀, hD₀, hZ_empty ▸ empty_subset _⟩
  · by_cases hcuff : ∃ C ∈ cuffs S, C ⊆ Y
    · obtain ⟨C, hC, hCY⟩ := hcuff
      exact isPlanar_of_cuff_subset hS hZY H hC hCY
    · push Not at hcuff
      have hns : ¬ IsSphere S := not_isSphere_of_bd_ne_empty hbd
      have hfin : (cuffs S).Finite := (cuff_statement.{u} S hS).2.1
      let cs : List {C : Set S // C ∈ cuffs S} :=
        hfin.toFinset.attach.toList.map (fun ⟨C, hC⟩ => ⟨C, hfin.mem_toFinset.mp hC⟩)
      have hcs_nodup : cs.Nodup := by
        refine (Finset.nodup_toList _).map ?_
        rintro ⟨C₁, _⟩ ⟨C₂, _⟩ heq
        exact Subtype.ext (Subtype.mk.inj heq)
      have hcs_mem : ∀ C (hC : C ∈ cuffs S), (⟨C, hC⟩ : {C : Set S // C ∈ cuffs S}) ∈ cs := by
        intro C hC
        refine List.mem_map.mpr ⟨⟨C, hfin.mem_toFinset.mpr hC⟩, ?_, rfl⟩
        exact Finset.mem_toList.mpr (Finset.mem_attach _ _)
      obtain ⟨L_all, hL_val, hL_pw, hL_cov⟩ :=
        exists_combined_collar_charts hS hZc.isCompact hYo hZY cs hcs_nodup
          (fun c _ => hcuff c.1 c.2)
      have hvalid : ∀ d ∈ L_all, IsValidCollarChart Y d := fun d hd => (hL_val d hd).1
      let W_union : Set S := ⋃ d ∈ L_all, d.W
      have hW_open : IsOpen W_union :=
        isOpen_biUnion (s := {d | d ∈ L_all}) fun d hd => (hvalid d hd).isOpen_W
      have hZ_bd_cov : Z ∩ bd S ⊆ W_union := by
        rintro x ⟨hxZ, hxb⟩
        let C := connectedComponentIn (bd S) x
        have hC : C ∈ cuffs S := ⟨x, hxb, rfl⟩
        have hxC : x ∈ C := mem_connectedComponentIn hxb
        exact hL_cov ⟨C, hC⟩ (hcs_mem C hC) ⟨hxZ, hxC⟩
      let K₁ : Set S := Z \ W_union
      have hK₁ : IsCompact K₁ := (hZc.sdiff hW_open).isCompact
      have hK₁_sub : K₁ ⊆ Y \ bd S := by
        rintro x ⟨hxZ, hxW⟩
        exact ⟨hZY hxZ, fun hxb => hxW (hZ_bd_cov ⟨hxZ, hxb⟩)⟩
      let K₂ : Set S := ⋃ d ∈ L_all, d.g '' closedBall 0 (1 / 2)
      have hK₂ : IsCompact K₂ := by
        refine L_all.finite_toSet.isCompact_biUnion fun d hd => ?_
        exact (isCompact_closedBall 0 (1 / 2)).image (hvalid d hd).chart.gc
      have hK₂_sub : K₂ ⊆ Y \ bd S := by
        refine iUnion₂_subset fun d hd => ?_
        rintro _ ⟨z, hz, rfl⟩
        have hz_int := closedBall_half_subset_bInt hz
        refine ⟨(hvalid d hd).g_sub_Y ⟨z, bInt_subset_bHalf hz_int, rfl⟩, fun hbd_g => ?_⟩
        exact hz_int.2.ne (((hvalid d hd).chart.bd_iff z (bInt_subset_bHalf hz_int)).mp hbd_g)
      let K₀ : Set S := K₁ ∪ K₂
      have hK₀ : IsCompact K₀ := hK₁.union hK₂
      have hK₀_sub : K₀ ⊆ Y \ bd S := union_subset hK₁_sub hK₂_sub
      obtain ⟨D_init, hD_init_sub, hD_init⟩ := exists_initial_disc_interior hS hYo hYne
      have hint : ∀ x ∈ Y \ bd S, IsInteriorPoint x := fun x hx =>
        Decidable.byContradiction fun hni => hx.2 hni
      have hY'o : IsOpen (Y \ bd S) := hYo.sdiff (cuff_statement.{u} S hS).1
      have hY'c : IsPreconnected (Y \ bd S) := isPreconnected_diff_bd hS hYo hYp
      have hH' : ∀ F : Set S, F ⊆ Y \ bd S → IsOArc F →
          ∃ Δ : Set S, Δ ⊆ Y \ bd S ∧ IsClosedDisc Δ ∧ discBd Δ = F :=
        fun F hF hFO => disc_subset_diff_bd_of_oArc hS H hF hFO
      obtain ⟨D₀, hD₀Y, hD₀, _, hK₀_D₀⟩ :=
        exists_disc_compact_interior hS hns hint hY'o hY'c hH' hK₀ hK₀_sub hD_init_sub hD_init
      have hballs : ∀ d ∈ L_all, d.g '' closedBall 0 (1 / 2) ⊆ D₀ := by
        intro d hd x hx
        have hxK₂ : x ∈ K₂ := mem_iUnion₂.mpr ⟨d, hd, hx⟩
        exact discInt_subset D₀ (hK₀_D₀ (Or.inr hxK₂))
      obtain ⟨D', _, _, hD', hD₀D', hW_D'⟩ :=
        exists_disc_merging_collar_charts hS hns H L_all hvalid hL_pw hD₀Y hD₀ hballs
      refine ⟨D', hD', fun x hxZ => ?_⟩
      by_cases hxW : x ∈ W_union
      · obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hxW
        exact hW_D' d hd hxd
      · have hxK₁ : x ∈ K₁ := ⟨hxZ, hxW⟩
        exact hD₀D' (discInt_subset D₀ (hK₀_D₀ (Or.inl hxK₁)))

end GraphMinor.GM07
