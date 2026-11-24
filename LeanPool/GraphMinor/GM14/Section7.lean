/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section7a
public import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.GM14.Section5
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.Surface.PushOff

/-!
# Graph Minors XIV, Section 7: Distance and Freedom (Complete)

This file completes Section 7 (pages 35–39) of N. Robertson and P. D. Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B **65** (1995) 23–50, by
proving `(7.7)` (`theorem_7_7`, pages 37–38) and re-exporting `(7.1)`–`(7.6)` from `Section7a.lean`
and `(7.8)` from `Section7b.lean`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11

universe u v w

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Pushing a Boundary Arc off a Closed Disc -/

local notation "𝕀" => unitInterval

/-- Symmetry of `IsTwoArcs`. -/
private theorem isTwoArcs_symm {u v : 𝕀 → S} (h : IsTwoArcs u v) : IsTwoArcs v u :=
  ⟨h.arc_right, h.arc_left, h.zero.symm, h.one.symm, fun s t hst =>
    (h.meet t s hst.symm).imp (fun ⟨h1, h2⟩ => ⟨h2, h1⟩) (fun ⟨h1, h2⟩ => ⟨h2, h1⟩)⟩

/-- Given a closed disc `D` in a closed surface `S`, a line `L ⊆ subBd D` with ends `a, b`, and a
closed set `Y ⊆ S` with `a ∈ Y`, `b ∈ Y`, and `Y ∩ L ⊆ {a, b}`, there is a homeomorphism `h : S ≃ₜ
S`
fixing `Y` pointwise such that `h '' L ∩ D ⊆ {a, b}`. -/
private theorem push_arc (hS : IsClosedSurface S) {D L Y : Set S} {a b : S}
    (hD : IsClosedDisc D) (hL : IsLineWithEnds L a b) (hLD : L ⊆ subBd D)
    (hY : IsClosed Y) (haY : a ∈ Y) (hbY : b ∈ Y) (hYL : Y ∩ L ⊆ {a, b}) :
    ∃ h : S ≃ₜ S, (∀ y ∈ Y, h y = y) ∧ h '' L ∩ D ⊆ {a, b} := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hint : ∀ x : S, IsInteriorPoint x := hS.2.2
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hint x).isManifoldPoint
  have hLD' : L ⊆ discBd D := by
    rwa [← IsClosedDisc.subBd_eq_discBd hS hD]
  obtain ⟨u, v, huv, hr, h0, h1, hun⟩ := exists_arcs_of_line hD.isOArc_discBd hL hLD'
  subst h0 h1 hr
  have hvu : IsTwoArcs v u := isTwoArcs_symm huv
  have hun' : range v ∪ range u = discBd D := by rw [Set.union_comm, hun]
  obtain ⟨E, c, c', hE, q1, q2, q3, q4, q5, q6, q7, q8, cl, ch⟩ :=
    exists_chart_two_arcs hman hD (fun x _ => hint x) hvu hun'
  have hb12 : Metric.closedBall (0 : ℂ) 1 ⊆ Metric.closedBall 0 2 :=
    Metric.closedBall_subset_closedBall (by norm_num)
  have hinj : InjOn c (Metric.closedBall 0 2) := q5.injOn
  have hDE : D ⊆ E := by
    rw [← q7]
    exact (image_mono hb12).trans q3.image_subset
  have hlow : ∀ t, lowArc t ∈ Metric.closedBall (0 : ℂ) 1 := fun t => by
    rw [mem_closedBall_zero_iff]
    exact (norm_of_capH (y := - capH _) (abs_two_sub_one_le t) (by ring)).le
  have hhigh : ∀ t, highArc t ∈ Metric.closedBall (0 : ℂ) 1 := fun t => by
    rw [mem_closedBall_zero_iff]
    exact (norm_of_capH (abs_two_sub_one_le t) rfl).le
  have hnsq : ∀ z : ℂ, z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hpt : ∀ x : ℝ, |x| < 1 → ∃ t : 𝕀, t ≠ 0 ∧ t ≠ 1 ∧ 2 * t.1 - 1 = x := fun x hx => by
    obtain ⟨h3, h4⟩ := abs_lt.mp hx
    refine ⟨⟨(x + 1) / 2, by linarith, by linarith⟩, fun he => ?_, fun he => ?_, by simp; ring⟩
    · have := congrArg Subtype.val he
      simp only [Set.Icc.coe_zero] at this
      linarith
    · have := congrArg Subtype.val he
      simp only [Set.Icc.coe_one] at this
      linarith
  let Yc : Set ℂ := Metric.closedBall 0 2 ∩ c ⁻¹' Y
  have hYc : IsClosed Yc := q1.preimage_isClosed_of_isClosed Metric.isClosed_closedBall hY
  have hYne : Yc.Nonempty := ⟨lowArc 0, hb12 (hlow 0), by
    change c _ ∈ Y
    rw [cl, huv.zero]
    exact haY⟩
  let d : ℝ → ℝ := fun x => Metric.infDist (⟨x, capH x⟩ : ℂ) Yc
  have hpc : ∀ {f : ℝ → ℝ}, Continuous f → Continuous fun x : ℝ => (⟨x, f x⟩ : ℂ) := fun hf =>
    Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk hf)
  have hdc : Continuous d := (Metric.continuous_infDist_pt Yc).comp (hpc continuous_capH)
  have hdpos : ∀ x, |x| < 1 → 0 < d x := fun x hx => by
    refine (hYc.notMem_iff_infDist_pos hYne).mp fun hmem => ?_
    obtain ⟨t, ht0, ht1, ht⟩ := hpt x hx
    have he : highArc t = ⟨x, capH x⟩ := by simp only [highArc, ht]
    have h3 : u t ∈ Y := by
      have := hmem.2
      rwa [mem_preimage, ← he, ch] at this
    rcases hYL ⟨h3, t, rfl⟩ with h4 | h4
    · exact ht0 (huv.arc_left.2 h4)
    · exact ht1 (huv.arc_left.2 h4)
  let e : ℝ → ℝ := fun x => min (d x / 2) (min (1 / 2) (capH x))
  have hHc := continuous_capH
  have hec : Continuous e := (hdc.div_const 2).min (continuous_const.min hHc)
  have hepos : ∀ x, |x| < 1 → 0 < e x := fun x hx =>
    lt_min (half_pos (hdpos x hx)) (lt_min (by norm_num) (capH_pos hx))
  have hele : ∀ x, e x ≤ 1 / 2 := fun x => (min_le_right _ _).trans (min_le_left _ _)
  have hdata : IsPushData (fun x => capH x - e x) capH
      (fun x => capH x + e x / 2) (fun x => capH x + e x) := by
    refine ⟨hHc.sub hec, hHc, hHc.add (hec.div_const 2), hHc.add hec,
      fun x hx => ?_, fun x hx => ?_⟩
    · have a2 := hepos x hx
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> linarith
    · have a1 := capH_eq_zero hx
      have a2 : e x = 0 := by
        simp only [e, a1]
        rw [min_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact min_eq_right (div_nonneg Metric.infDist_nonneg (by norm_num))
      simp [a1, a2]
  obtain ⟨Θ, hre, him⟩ := exists_vertical_push hdata
  have hfix : ∀ z : ℂ,
      (1 ≤ |z.re| ∨ z.im ≤ capH z.re - e z.re ∨ capH z.re + e z.re ≤ z.im) → Θ z = z := by
    intro z hz
    refine Complex.ext (hre z) ?_
    rw [him]
    rcases lt_or_ge |z.re| 1 with hx | hx
    · obtain ⟨a1, a2, -, -⟩ := hdata.2.2.2.2.1 _ hx
      rcases hz with hz | hz | hz
      · exact absurd hx (not_lt.mpr hz)
      · rw [tentMap, tent_low a1 a2 hz, mul_zero, add_zero]
      · rw [tentMap, tent_high a1 a2 hz, mul_zero, add_zero]
    · have a1 := (hdata.2.2.2.2.2 _ hx).2.1
      simp only at a1
      rw [tentMap, show capH z.re + e z.re / 2 - capH z.re = 0 by linarith, zero_mul, add_zero]
  have hHle : ∀ x, capH x ≤ 1 := fun x => by
    rw [capH]
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg x])
  have hHnn : ∀ x, 0 ≤ capH x := fun x => Real.sqrt_nonneg _
  have hfar : ∀ z : ℂ, 3 / 2 ≤ ‖z‖ → Θ z = z := by
    intro z hz
    refine hfix z ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨a1, a2, a3⟩ := hcon
    have a4 := capH_sq a1.le
    have a5 := hele z.re
    have a6 := hHle z.re
    have a7 := hHnn z.re
    have a8 : z.im ^ 2 < (capH z.re + 1 / 2) ^ 2 := sq_lt_sq' (by linarith) (by linarith)
    have a9 := hnsq z
    nlinarith
  have hmap2 : ∀ z ∈ Metric.closedBall (0 : ℂ) 2, Θ z ∈ Metric.closedBall (0 : ℂ) 2 := by
    intro z hz
    by_contra hcon
    have h3 : 2 < ‖Θ z‖ := by
      rw [mem_closedBall_zero_iff, not_le] at hcon
      exact hcon
    have h4 := Θ.injective (hfar (Θ z) (by linarith))
    rw [h4] at h3
    linarith [mem_closedBall_zero_iff.mp hz]
  obtain ⟨h, hh1, hh2⟩ := exists_homeomorph_of_collar hman hE q1 q2 q3 q4 q5 q6 q8 Θ hfar
  have hfixY : ∀ y ∈ Y, h y = y := by
    intro y hy
    by_cases hyE : y ∈ E
    · have hz := q4 hyE
      have hcz : c (c' y) = y := q6 hyE
      set z := c' y
      have hzY : z ∈ Yc := ⟨hz, by rw [mem_preimage, hcz]; exact hy⟩
      have hfixz : Θ z = z := by
        refine hfix z ?_
        by_contra hcon
        push Not at hcon
        obtain ⟨a1, a2, a3⟩ := hcon
        have a5 : d z.re ≤ dist (⟨z.re, capH z.re⟩ : ℂ) z := Metric.infDist_le_dist_of_mem hzY
        rw [Complex.dist_of_re_eq (show (⟨z.re, capH z.re⟩ : ℂ).re = z.re from rfl),
          Real.dist_eq] at a5
        have a6 : e z.re ≤ d z.re / 2 := min_le_left _ _
        have a7 := hdpos z.re a1
        have a8 : |capH z.re - z.im| < e z.re := abs_lt.mpr ⟨by linarith, by linarith⟩
        simp only [d] at a5 a6 a7
        linarith
      rw [← hcz, hh1 z hz, hfixz]
    · exact hh2 y hyE
  refine ⟨h, hfixY, ?_⟩
  rintro _ ⟨⟨_, ⟨s, rfl⟩, rfl⟩, hxD⟩
  by_cases hs0 : s = 0
  · subst hs0
    exact Or.inl (hfixY (u 0) haY)
  by_cases hs1 : s = 1
  · subst hs1
    exact Or.inr (hfixY (u 1) hbY)
  exfalso
  have hs_pos : (0 : ℝ) < s.1 := lt_of_le_of_ne s.2.1 fun h => hs0 (Subtype.ext h.symm)
  have hs_lt : s.1 < 1 := lt_of_le_of_ne s.2.2 fun h => hs1 (Subtype.ext h)
  set x := 2 * s.1 - 1
  have hx1 : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hhs : highArc s = ⟨x, capH x⟩ := rfl
  have hz2 : highArc s ∈ Metric.closedBall (0 : ℂ) 2 := hb12 (hhigh s)
  rw [← ch s, hh1 (highArc s) hz2] at hxD
  obtain ⟨ζ, hζ, he⟩ : c (Θ (highArc s)) ∈ c '' Metric.closedBall 0 1 := q7 ▸ hxD
  have hΘz : ζ = Θ (highArc s) := hinj (hb12 hζ) (hmap2 (highArc s) hz2) he
  have hn1 : ‖Θ (highArc s)‖ ≤ 1 := mem_closedBall_zero_iff.mp (hΘz ▸ hζ)
  have hn2 : (Θ (highArc s)).re ^ 2 + (Θ (highArc s)).im ^ 2 ≤ 1 := by
    rw [hnsq]
    nlinarith [norm_nonneg (Θ (highArc s))]
  have hre_s : (Θ (highArc s)).re = x := hre (highArc s)
  obtain ⟨a1, a2, -, -⟩ := hdata.2.2.2.2.1 x hx1
  simp only at a1 a2
  have him_s : (Θ (highArc s)).im = capH x + e x / 2 := by
    rw [him (highArc s), hhs]
    simp only [tentMap, tent_left a1 a2 a1.le le_rfl, div_self (sub_ne_zero.mpr a1.ne')]
    ring
  rw [hre_s, him_s] at hn2
  have hsq := capH_sq hx1.le
  have hcpos := capH_pos hx1
  have hepos' := hepos x hx1
  nlinarith

/-! ## 2. Tangle Separations from a Segregation -/

/-- For each society `S₀ ∈ S_seg` in a segregation of `G`, there is a complementary subgraph `B`
such that `IsGraphSeparation G S₀.G B` and `V(S₀.G) ∩ V(B) = S₀.Ω.bar`. -/
theorem exists_separation_of_segregation {α : Type v} {β : Type w} {G : Graph α β}
    {S_seg : Set (Society α β)} (hSeg : IsGraphSegregation G S_seg)
    {S₀ : Society α β} (hS₀ : S₀ ∈ S_seg) :
    ∃ B : Graph α β, IsGraphSeparation G S₀.G B ∧ V(S₀.G) ∩ V(B) = S₀.Ω.bar ∧
      V(B) = (V(G) \ V(S₀.G)) ∪ S₀.Ω.bar ∧ E(B) = E(G) \ E(S₀.G) := by
  have hle₀ : S₀.G ≤ G := hSeg.le S₀ hS₀
  have hbar₀ : S₀.Ω.bar ⊆ V(S₀.G) := S₀.bar_subset
  let X_B : Set α := (V(G) \ V(S₀.G)) ∪ S₀.Ω.bar
  have hXB_sub : X_B ⊆ V(G) :=
    union_subset sdiff_subset (hbar₀.trans hle₀.vertexSet_mono)
  let B : Graph α β := (G.induce X_B).restrict (E(G) \ E(S₀.G))
  have hB_le : B ≤ G := restrict_le.trans (induce_le hXB_sub)
  have hVB : V(B) = X_B := by simp [B]
  have hV_inter : V(S₀.G) ∩ V(B) = S₀.Ω.bar := by
    rw [hVB]
    ext v
    simp only [X_B, mem_inter_iff, mem_union, mem_sdiff]
    exact ⟨fun ⟨hv0, h⟩ => h.elim (fun ⟨_, hnot⟩ => (hnot hv0).elim) id,
      fun hvbar => ⟨hbar₀ hvbar, Or.inr hvbar⟩⟩
  have hV_union : V(S₀.G) ∪ V(B) = V(G) := by
    rw [hVB]
    ext v
    simp only [X_B, mem_union, mem_sdiff]
    constructor
    · rintro (hv0 | (⟨hvG, _⟩ | hvbar))
      · exact hle₀.vertexSet_mono hv0
      · exact hvG
      · exact hle₀.vertexSet_mono (hbar₀ hvbar)
    · intro hvG
      by_cases hv0 : v ∈ V(S₀.G)
      · exact Or.inl hv0
      · exact Or.inr (Or.inl ⟨hvG, hv0⟩)
  have hEB : E(B) = E(G) \ E(S₀.G) := by
    ext e
    simp only [B, edgeSet_restrict, mem_inter_iff, edgeSet_induce, Set.mem_ofPred_eq]
    refine ⟨fun h => h.2, fun ⟨heG, he_not_0⟩ => ⟨?_, heG, he_not_0⟩⟩
    have he_union : e ∈ E(subgraphSUnion G ((fun S₁ : Society α β => S₁.G) '' S_seg)) :=
      hSeg.union_eq.symm ▸ heG
    simp only [subgraphSUnion, edgeSet_restrict, mem_inter_iff, mem_iUnion, mem_image,
      exists_prop] at he_union
    obtain ⟨_, ⟨S₁, hS₁, rfl⟩, heS₁⟩ := he_union.2
    have hne : S₀ ≠ S₁ := fun h => he_not_0 (h ▸ heS₁)
    obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet heG
    have hlink₁ : S₁.G.IsLink e x y := ((hSeg.le S₁ hS₁).isLink_iff heS₁).mpr hlink
    have hx_B : x ∈ X_B := by
      by_cases hx0 : x ∈ V(S₀.G)
      · exact Or.inr ((hSeg.vertex_inter_subset S₀ hS₀ S₁ hS₁ hne ⟨hx0, hlink₁.left_mem⟩).1)
      · exact Or.inl ⟨hlink.left_mem, hx0⟩
    have hy_B : y ∈ X_B := by
      by_cases hy0 : y ∈ V(S₀.G)
      · exact Or.inr ((hSeg.vertex_inter_subset S₀ hS₀ S₁ hS₁ hne ⟨hy0, hlink₁.right_mem⟩).1)
      · exact Or.inl ⟨hlink.right_mem, hy0⟩
    exact ⟨x, y, hlink, hx_B, hy_B⟩
  have hE_union : E(S₀.G) ∪ E(B) = E(G) := by
    rw [hEB]
    ext e
    exact ⟨fun h => h.elim (fun he => hle₀.edgeSet_mono he) (fun he => he.1),
      fun he => by by_cases h : e ∈ E(S₀.G) <;> [exact Or.inl h; exact Or.inr ⟨he, h⟩]⟩
  have hE_disj : Disjoint E(S₀.G) E(B) := by
    rw [hEB]
    exact disjoint_sdiff_self_right
  exact ⟨B, ⟨hle₀, hB_le, hV_union, hE_union, hE_disj⟩, hV_inter, hVB, hEB⟩

/-- Applying `IsTangleLocal` to a society `S₀ ∈ S_seg` in a 3-segregation yields a separation
`(A_H, B_H) ∈ T` of `H` with `(A_H ∩ B_H).vertexSet = {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}` of size
`≤ 3`. -/
theorem exists_tangle_separation_of_threeSegregation {α : Type v} {β : Type w} {G : Graph α β}
    {H : Drawing S} {η : SpanEmbedding H G}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {S_seg : Set (Society α β)}
    (hSeg : IsThreeSegregation G S_seg) (hLoc : IsTangleLocal G H η T S_seg)
    {S₀ : Society α β} (hS₀ : S₀ ∈ S_seg) :
    ∃ A_H B_H : Hypergraph S (Set S),
      H.toHypergraph.IsSeparation A_H B_H ∧
      A_H.vertexSet = {v ∈ H.V | η.vMap v ∈ V(S₀.G)} ∧
      (A_H ∩ B_H).vertexSet = {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar} ∧
      A_H.edgeSet = {e ∈ H.E | η.eMap e ∈ E(S₀.G)} ∧
      B_H.edgeSet = {e ∈ H.E | η.eMap e ∉ E(S₀.G)} ∧
      (A_H ∩ B_H).vertexSet.ncard ≤ 3 ∧
      (A_H, B_H) ∈ T := by
  obtain ⟨B, hsepB, hV_inter, _, hEB⟩ := exists_separation_of_segregation hSeg.1 hS₀
  obtain ⟨A_H, B_H, hsepH, hAV, hBV, hAE, hBE, hmemT⟩ := hLoc S₀ hS₀ B hsepB hV_inter
  have hinterV : (A_H ∩ B_H).vertexSet = {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar} := by
    change A_H.vertexSet ∩ B_H.vertexSet = _
    rw [hAV, hBV, ← hV_inter]
    ext v
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  have hBE' : B_H.edgeSet = {e ∈ H.E | η.eMap e ∉ E(S₀.G)} := by
    rw [hBE, hEB]
    ext e
    simp only [mem_ofPred_eq, mem_sdiff]
    exact ⟨fun ⟨he, _, hnot⟩ => ⟨he, hnot⟩,
      fun ⟨he, hnot⟩ => ⟨he, η.imageGraph_le.edgeSet_mono (η.bijOn_e.mapsTo he), hnot⟩⟩
  have hcard : (A_H ∩ B_H).vertexSet.ncard ≤ 3 := by
    rw [hinterV]
    have hsub : η.vMap '' {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar} ⊆ S₀.Ω.bar := by
      rintro _ ⟨v, ⟨_, hv⟩, rfl⟩
      exact hv
    have hinj : InjOn η.vMap {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar} :=
      η.bijOn_v.injOn.mono fun _ hv => hv.1
    have hfin : S₀.Ω.bar.Finite := S₀.Ω.finite_bar
    calc
      {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}.ncard
        = (η.vMap '' {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}).ncard := hinj.ncard_image.symm
      _ ≤ S₀.Ω.bar.ncard := ncard_le_ncard hsub hfin
      _ ≤ 3 := hSeg.2 S₀ hS₀
  exact ⟨A_H, B_H, hsepH, hAV, hinterV, hAE, hBE', hcard, hmemT⟩

/-! ## 3. Proof of (7.7) (pages 37–38) -/

/-- Core contradiction in the proof of (7.7): if `C_i` (`i = 1` or `2`) is a circuit of `H` bounding
a closed disc `Δ_i ⊆ Δ₁` with `Δ₂ ⊆ Δ_i`, and `S₀ ∈ S_seg` contains an edge `e_i ∈ C_i.E` while
`C_i.V` contains at most one vertex of `{v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}`, we obtain a contradiction
from (7.4), (7.6), and hypothesis (iii). -/
private theorem no_circuit_in_arrangement_piece [T2Space S]
    (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {α : Type v} {β : Type w}
    {G : Graph α β} {H C_i : Drawing S} {η : SpanEmbedding H G}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Δ₁ Δ₂ Δ_i : Set S}
    {S_seg : Set (Society α β)} (hθ : 6 ≤ θ) (hd : HasTangleMetric H θ T d)
    (hz : z ∈ H.A) (_hΔ₁ : IsClosedDisc Δ₁) (_hΔ₂ : IsClosedDisc Δ₂) (hΔ_i : IsClosedDisc Δ_i)
    (hz_sub : z ⊆ Δ₂ \ subBd Δ₂) (_hΔ₂_sub₁ : Δ₂ ⊆ Δ₁ \ subBd Δ₁)
    (hΔ₂_sub_i : Δ₂ ⊆ Δ_i) (hΔ_i_sub₁ : Δ_i ⊆ Δ₁)
    (hii : ∀ x ∈ H.A, x ⊆ Δ₁ → d z x ≤ θ - 4)
    (hiii : ∀ x ∈ H.A, d z x ≤ 3 → x ⊆ Δ₂ \ subBd Δ₂)
    (hC_i : C_i.IsCircuit) (hC_is : C_i.IsSubdrawing H) (hbd_i : subBd Δ_i = C_i.U)
    (hSeg : IsThreeSegregation G S_seg) (hLoc : IsTangleLocal G H η T S_seg)
    {S₀ : Society α β} (hS₀ : S₀ ∈ S_seg) {e_i : Set S} (he_i : e_i ∈ C_i.E)
    (he_S₀ : η.eMap e_i ∈ E(S₀.G))
    (hle1 : (C_i.V ∩ {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}).ncard ≤ 1) : False := by
  obtain ⟨hResp, K, ins, hK, hins, hd_eq⟩ := hd
  obtain ⟨A_H, B_H, hsepH, _, hinterV, hAE, _, hcard, hmemT⟩ :=
    exists_tangle_separation_of_threeSegregation hSeg hLoc hS₀
  have hle1' : (C_i.V ∩ (A_H ∩ B_H).vertexSet).ncard ≤ 1 := by rwa [hinterV]
  have he_A : e_i ∈ A_H.edgeSet := by
    rw [hAE]
    exact ⟨hC_is.2 he_i, he_S₀⟩
  have hsubA := circuit_subset_of_inter_ncard_le_one hsepH hC_i hC_is hle1'
    (Or.inr ⟨e_i, he_i, he_A⟩)
  obtain ⟨D, hD, hDs, hlen2θ, hDV_sub, hCU_sub⟩ :=
    theorem_7_4_proof hS hConn hResp hK hins hmemT hC_i hC_is hsubA.1 hsubA.2
  have hfin_AB : (A_H ∩ B_H).vertexSet.Finite :=
    hinterV ▸ H.finite_V.subset fun _ hv => hv.1
  have hDV_card : (D.V ∩ H.V).ncard ≤ 3 :=
    (ncard_le_ncard hDV_sub hfin_AB).trans hcard
  have hDeq := (circuit_length_eq_two_mul_ncard hK.2.1 hD hDs).1
  have hDlen : D.length < 2 * (θ - (θ - 4)) := by omega
  have hint_sub : Δ₂ \ subBd Δ₂ ⊆ Δ_i \ subBd Δ_i := by
    have h₁ : Δ₂ \ subBd Δ₂ = interior Δ₂ := by
      rw [← subBd_eq_frontier']
      ext x
      exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
        fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
    have h₂ : Δ_i \ subBd Δ_i = interior Δ_i := by
      rw [← subBd_eq_frontier']
      ext x
      exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
        fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
    rw [h₁, h₂]
    exact interior_mono hΔ₂_sub_i
  have hZone_i : IsLambdaZoneAround H d (θ - 4) z (Δ_i \ subBd Δ_i) := by
    obtain ⟨hOD_i, hcl_i, hbd_i'⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ_i
    refine ⟨hz, hOD_i, hz_sub.trans hint_sub, ?_, ?_, ?_, ?_, fun _ => by omega⟩
    · rw [hbd_i', hbd_i]
      exact isOArc_of_isCircuit hC_i
    · rw [hcl_i]
      exact hΔ_i
    · rw [hbd_i', hbd_i]
      exact hC_is.U_subset
    · intro x hx hsub
      rw [hcl_i] at hsub
      exact hii x hx (hsub.trans hΔ_i_sub₁)
  obtain ⟨_, hcl_i, hbd_i'⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ_i
  have hbd_in_D : subBd (Δ_i \ subBd Δ_i) ⊆ ins D := by
    rw [hbd_i', hbd_i]
    exact hCU_sub
  have hΔ_i_in_D : Δ_i ⊆ ins D := by
    have h := theorem_7_6_proof hS hConn ⟨hResp, K, ins, hK, hins, hd_eq⟩ hK hins hZone_i
      hD hDs hDlen hbd_in_D
    rwa [hcl_i] at h
  obtain ⟨p_z, hp_z⟩ := atom_nonempty hz
  have hz_D : (z ∩ ins D).Nonempty :=
    ⟨p_z, hp_z, hΔ_i_in_D ((hz_sub.trans hint_sub hp_z).1)⟩
  have he_iH : e_i ∈ H.E := hC_is.2 he_i
  have he_iA : e_i ∈ H.A := Or.inl (Or.inr he_iH)
  obtain ⟨p_e, hp_e⟩ := atom_nonempty he_iA
  have hp_e_CU : p_e ∈ C_i.U := (he_i.2.1 hp_e).1
  have he_D : (e_i ∩ ins D).Nonempty :=
    ⟨p_e, hp_e, hCU_sub hp_e_CU⟩
  have hd_le : d z e_i ≤ 3 := by
    rw [hd_eq z hz e_i he_iA]
    exact (tangleMetric_le_of_circuit hS hK hins hD hDs hlen2θ hz he_iA hz_D he_D).2.trans hDV_card
  have he_in₂ : p_e ∈ Δ₂ \ subBd Δ₂ := hiii e_i he_iA hd_le hp_e
  have he_in_i : p_e ∈ Δ_i \ subBd Δ_i := hint_sub he_in₂
  exact he_in_i.2 (hbd_i ▸ hp_e_CU)

/-- No society `S₀ ∈ S_seg` can contain both an edge of `C₁` and an edge of `C₂`. -/
private theorem no_two_circuits_in_arrangement_piece [T2Space S]
    (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {α : Type v} {β : Type w}
    {G : Graph α β} {H C₁ C₂ : Drawing S} {η : SpanEmbedding H G}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Δ₁ Δ₂ : Set S}
    {S_seg : Set (Society α β)} (hθ : 6 ≤ θ) (hd : HasTangleMetric H θ T d)
    (hz : z ∈ H.A) (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂)
    (hz_sub : z ⊆ Δ₂ \ subBd Δ₂) (hΔ₂_sub₁ : Δ₂ ⊆ Δ₁ \ subBd Δ₁)
    (hii : ∀ x ∈ H.A, x ⊆ Δ₁ → d z x ≤ θ - 4)
    (hiii : ∀ x ∈ H.A, d z x ≤ 3 → x ⊆ Δ₂ \ subBd Δ₂)
    (hC₁ : C₁.IsCircuit) (hC₁s : C₁.IsSubdrawing H) (hbd₁ : subBd Δ₁ = C₁.U)
    (hC₂ : C₂.IsCircuit) (hC₂s : C₂.IsSubdrawing H) (hbd₂ : subBd Δ₂ = C₂.U)
    (hdisj : Disjoint C₁.V C₂.V)
    (hSeg : IsThreeSegregation G S_seg) (hLoc : IsTangleLocal G H η T S_seg)
    {S₀ : Society α β} (hS₀ : S₀ ∈ S_seg)
    {e₁ e₂ : Set S} (he₁ : e₁ ∈ C₁.E) (he₁_S₀ : η.eMap e₁ ∈ E(S₀.G))
    (he₂ : e₂ ∈ C₂.E) (he₂_S₀ : η.eMap e₂ ∈ E(S₀.G)) : False := by
  obtain ⟨A_H, B_H, _, _, hinterV, _, _, hcard, _⟩ :=
    exists_tangle_separation_of_threeSegregation hSeg hLoc hS₀
  let X_S₀ : Set S := {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}
  have hX_fin : X_S₀.Finite := H.finite_V.subset fun _ hv => hv.1
  have hX_lt : X_S₀.ncard < 2 * 2 := by
    have : X_S₀.ncard ≤ 3 := by
      change {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}.ncard ≤ 3
      rwa [← hinterV]
    omega
  let P_fam : Fin 2 → Set S := ![C₁.V, C₂.V]
  have hP_disj : Pairwise (fun i j : Fin 2 => Disjoint (P_fam i) (P_fam j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hdisj
    · exact hdisj.symm
    · exact absurd rfl hij
  obtain ⟨i, hi⟩ := exists_inter_ncard_le_one_of_ncard_lt_two_mul hP_disj hX_fin hX_lt
  fin_cases i
  · exact no_circuit_in_arrangement_piece hS hConn hθ hd hz hΔ₁ hΔ₂ hΔ₁ hz_sub
      hΔ₂_sub₁ (hΔ₂_sub₁.trans sdiff_subset) subset_rfl hii hiii hC₁ hC₁s hbd₁ hSeg hLoc hS₀
      he₁ he₁_S₀ hi
  · exact no_circuit_in_arrangement_piece hS hConn hθ hd hz hΔ₁ hΔ₂ hΔ₂ hz_sub
      hΔ₂_sub₁ subset_rfl (hΔ₂_sub₁.trans sdiff_subset) hii hiii hC₂ hC₂s hbd₂ hSeg hLoc hS₀
      he₂ he₂_S₀ hi

/-- If `S₀ ∈ S_seg` contains an edge of `C₂`, then `(α_pt '' S₀.Ω.bar).ncard ≥ 2`. -/
private theorem two_le_bar_image_ncard_of_mem_C2 [T2Space S]
    (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {α : Type v} {β : Type w}
    {G : Graph α β} {H C₂ : Drawing S} {η : SpanEmbedding H G}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Δ₁ Δ₂ : Set S}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hθ : 6 ≤ θ) (hd : HasTangleMetric H θ T d)
    (hz : z ∈ H.A) (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂)
    (hz_sub : z ⊆ Δ₂ \ subBd Δ₂) (hΔ₂_sub₁ : Δ₂ ⊆ Δ₁ \ subBd Δ₁)
    (hii : ∀ x ∈ H.A, x ⊆ Δ₁ → d z x ≤ θ - 4)
    (hiii : ∀ x ∈ H.A, d z x ≤ 3 → x ⊆ Δ₂ \ subBd Δ₂)
    (hC₂ : C₂.IsCircuit) (hC₂s : C₂.IsSubdrawing H) (hbd₂ : subBd Δ₂ = C₂.U)
    (hSeg : IsThreeSegregation G S_seg) (hLoc : IsTangleLocal G H η T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    {S₀ : Society α β} (hS₀ : S₀ ∈ S_seg)
    {e₂ : Set S} (he₂ : e₂ ∈ C₂.E) (he₂_S₀ : η.eMap e₂ ∈ E(S₀.G)) :
    2 ≤ (α_pt '' S₀.Ω.bar).ncard ∧ S₀.Ω.bar.Nonempty := by
  have hinj_α : InjOn α_pt S₀.Ω.bar :=
    hArr.injOn_pts.mono (subset_biUnion_of_mem (u := fun S₁ : Society α β => S₁.Ω.bar) hS₀)
  have hcard_eq : (α_pt '' S₀.Ω.bar).ncard = S₀.Ω.bar.ncard := hinj_α.ncard_image
  have h2 : 2 ≤ S₀.Ω.bar.ncard := by
    by_contra hlt
    push Not at hlt
    have hle1_bar : S₀.Ω.bar.ncard ≤ 1 := by omega
    have hsub : η.vMap '' (C₂.V ∩ {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}) ⊆ S₀.Ω.bar := by
      rintro _ ⟨v, ⟨_, _, hv⟩, rfl⟩
      exact hv
    have hinj_η : InjOn η.vMap (C₂.V ∩ {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}) :=
      η.bijOn_v.injOn.mono fun _ hv => hv.2.1
    have hle1 : (C₂.V ∩ {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}).ncard ≤ 1 := by
      calc
        (C₂.V ∩ {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}).ncard
          = (η.vMap '' (C₂.V ∩ {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar})).ncard := hinj_η.ncard_image.symm
        _ ≤ S₀.Ω.bar.ncard := ncard_le_ncard hsub S₀.Ω.finite_bar
        _ ≤ 1 := hle1_bar
    exact no_circuit_in_arrangement_piece hS hConn hθ hd hz hΔ₁ hΔ₂ hΔ₂ hz_sub
      hΔ₂_sub₁ subset_rfl (hΔ₂_sub₁.trans sdiff_subset) hii hiii hC₂ hC₂s hbd₂ hSeg hLoc hS₀
      he₂ he₂_S₀ hle1
  refine ⟨hcard_eq ▸ h2, ?_⟩
  exact (ncard_pos S₀.Ω.finite_bar).mp (by omega)

/-- Gluing a finite family of drawings that pairwise meet only in common vertices. -/
private theorem exists_glued_drawing {ι : Type*} (s : Finset ι) (D_fam : ι → Drawing S)
    (hmeet : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (D_fam i).U ∩ (D_fam j).U ⊆ (D_fam i).V ∩ (D_fam j).V) :
    ∃ J : Drawing S,
      J.U = (⋃ i ∈ s, (D_fam i).U) ∧
      J.V = (⋃ i ∈ s, (D_fam i).V) ∧
      J.E = (⋃ i ∈ s, (D_fam i).E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hE_emp : arcComponentsIn ((∅ : Set S) \ ∅) = ∅ := by
      ext C
      simp only [sdiff_self, mem_empty_iff_false, iff_false]
      rintro ⟨⟨x, hx⟩, hsub, -⟩
      exact hsub hx
    refine ⟨{ U := ∅, V := ∅, V_subset_U := subset_rfl, isClosed_U := isClosed_empty,
              finite_V := finite_empty, finite_edges := by rw [hE_emp]; exact finite_empty,
              edge_cond := fun e he => by rw [hE_emp] at he; exact False.elim he },
      by simp, by simp, by change arcComponentsIn (∅ \ ∅) = _; rw [hE_emp]; simp⟩
  | @insert a s ha ih =>
    obtain ⟨J₀, hU₀, hV₀, hE₀⟩ :=
      ih (fun i hi j hj hij => hmeet i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij)
    have hm : (D_fam a).U ∩ J₀.U ⊆ (D_fam a).V ∩ J₀.V := by
      rw [hU₀, hV₀]
      rintro x ⟨hxa, hxU⟩
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      have h := hmeet a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) hne ⟨hxa, hxi⟩
      exact ⟨h.1, mem_iUnion₂.mpr ⟨i, hi, h.2⟩⟩
    refine ⟨(D_fam a).glue J₀ hm, ?_, ?_, ?_⟩
    · change (D_fam a).U ∪ J₀.U = _
      rw [hU₀, Finset.set_biUnion_insert]
    · change (D_fam a).V ∪ J₀.V = _
      rw [hV₀, Finset.set_biUnion_insert]
    · rw [Drawing.glue_E hm, hE₀, Finset.set_biUnion_insert]

/-- Every point of `C.U` in a circuit `C` belongs to the closure of some edge `e ∈ C.E`. -/
private theorem exists_edge_closure_of_mem_circuit_U {C : Drawing S} (hC : C.IsCircuit)
    {x : S} (hx : x ∈ C.U) : ∃ e ∈ C.E, x ∈ closure e := by
  by_cases hxV : x ∈ C.V
  · obtain ⟨W, _, hpos, _, hE⟩ := exists_walk_at hC hxV
    cases W with
    | nil _ => exact absurd hpos (Nat.lt_irrefl 0)
    | @cons _ w _ e hl r =>
      have he : e ∈ C.E := by rw [hE]; exact List.mem_cons_self
      have hx_cl : x ∈ closure e ∩ C.V := by rw [hl.2.2.2]; exact Or.inl rfl
      exact ⟨e, he, hx_cl.1⟩
  · have hx_diff : x ∈ C.U \ C.V := ⟨hx, hxV⟩
    have he : pathComponentIn (C.U \ C.V) x ∈ C.E :=
      ⟨⟨x, mem_pathComponentIn_self hx_diff⟩, pathComponentIn_subset,
        isPathConnected_pathComponentIn hx_diff, fun D hD hc hsub =>
          subset_antisymm (hc.subset_pathComponentIn (hsub (mem_pathComponentIn_self hx_diff)) hD)
            hsub⟩
    exact ⟨pathComponentIn (C.U \ C.V) x, he, subset_closure (mem_pathComponentIn_self hx_diff)⟩

/-- Any `O`-arc contained in the boundary `subBd D` of a closed disc `D` equals `subBd D`. -/
theorem eq_subBd_of_isOArc_subset [T2Space S] (hS : IsClosedSurface S) {D F : Set S}
    (hD : IsClosedDisc D) (hF : IsOArc F) (hF_sub : F ⊆ subBd D) : F = subBd D := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨Δ₀, ⟨hΔ₀_sub, hΔ₀_disc, hΔ₀_bd, -⟩, -⟩ :=
    disc_oArc D F hD (hF_sub.trans fun _ hx => hD.isClosed.closure_eq ▸ hx.1) hF
  have hbd₀ : subBd Δ₀ = F := by
    rw [IsClosedDisc.subBd_eq_discBd hS hΔ₀_disc, hΔ₀_bd]
  have hfr₀ : frontier Δ₀ = F := by rw [subBd_eq_frontier', hbd₀]
  obtain ⟨hOD₀, _, _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ₀_disc
  obtain ⟨p, hp⟩ := IsOpenDisc.nonempty hOD₀
  have hp_int₀ : p ∈ interior Δ₀ := by
    by_contra hni
    exact hp.2 (by rw [← subBd_eq_frontier']; exact ⟨subset_closure hp.1, hni⟩)
  have hp_intD : p ∈ interior D := interior_mono hΔ₀_sub hp_int₀
  obtain ⟨hOD, hclD, _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hD
  have hp_D : p ∈ D \ subBd D :=
    ⟨interior_subset hp_intD, fun hf => by rw [← subBd_eq_frontier'] at hf; exact hf.2 hp_intD⟩
  have hdisj : Disjoint (D \ subBd D) (frontier Δ₀) := by
    rw [hfr₀]
    exact disjoint_sdiff_left.mono_right hF_sub
  have hsub : D \ subBd D ⊆ Δ₀ :=
    subset_of_disjoint_frontier hOD.isPathConnected.isConnected.isPreconnected
      hΔ₀_disc.isClosed hdisj hp_D hp.1
  have h_eq : D = Δ₀ :=
    subset_antisymm (hclD ▸ hΔ₀_disc.isClosed.closure_subset_iff.mpr hsub) hΔ₀_sub
  rw [h_eq, hbd₀]

/-- For each `S₀ ∈ S_seg`, the open disc `α_disc S₀ \ subBd (α_disc S₀)` is a region of `J` when
`J.U = ⋃ S₁ ∈ S_seg, subBd (α_disc S₁)`. -/
private theorem region_of_glued_arrangement [T2Space S] (hS : IsClosedSurface S)
    {α : Type v} {β : Type w} {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S} {α_pt : α → S} {J : Drawing S}
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hJU : J.U = ⋃ S₁ ∈ S_seg, subBd (α_disc S₁))
    {S₀ : Society α β} (hS₀ : S₀ ∈ S_seg) :
    α_disc S₀ \ subBd (α_disc S₀) ∈ J.R := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hD₀ : IsClosedDisc (α_disc S₀) := (hArr.isClosedDisc S₀ hS₀).1
  obtain ⟨hOD₀, _, _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hD₀
  have hsub_compl : α_disc S₀ \ subBd (α_disc S₀) ⊆ univ \ J.U := by
    rintro x ⟨hxD, hxnot⟩
    refine ⟨mem_univ x, fun hxJ => ?_⟩
    rw [hJU] at hxJ
    obtain ⟨S₁, hS₁, hx₁⟩ := mem_iUnion₂.mp hxJ
    by_cases h_eq : S₁ = S₀
    · exact hxnot (h_eq ▸ hx₁)
    · have hx_inter : x ∈ α_disc S₀ ∩ α_disc S₁ :=
        ⟨hxD, (hArr.isClosedDisc S₁ hS₁).1.isClosed.closure_eq ▸ hx₁.1⟩
      obtain ⟨v, ⟨hv₀, _⟩, rfl⟩ := hArr.inter_discs S₀ hS₀ S₁ hS₁ (Ne.symm h_eq) hx_inter
      exact hxnot ((hArr.isClosedDisc S₀ hS₀).2 v hv₀)
  obtain ⟨p, hp⟩ := IsOpenDisc.nonempty hOD₀
  have hp_compl : p ∈ univ \ J.U := hsub_compl hp
  refine ⟨p, hp_compl, subset_antisymm ?_
    (hOD₀.isPathConnected.isConnected.isPreconnected.subset_connectedComponentIn hp hsub_compl)⟩
  have hbd_sub : subBd (α_disc S₀) ⊆ J.U := by
    rw [hJU]
    exact subset_biUnion_of_mem (u := fun S₁ : Society α β => subBd (α_disc S₁)) hS₀
  have hfr₀ : frontier (α_disc S₀) = subBd (α_disc S₀) := subBd_eq_frontier' _
  have hC_sub_compl : connectedComponentIn (univ \ J.U) p ⊆ univ \ J.U :=
    connectedComponentIn_subset (univ \ J.U) p
  have hdisj : Disjoint (connectedComponentIn (univ \ J.U) p) (frontier (α_disc S₀)) := by
    rw [hfr₀]
    refine disjoint_left.mpr fun x hxC hxbd => (hC_sub_compl hxC).2 (hbd_sub hxbd)
  have hC_sub_D₀ : connectedComponentIn (univ \ J.U) p ⊆ α_disc S₀ :=
    subset_of_disjoint_frontier isPreconnected_connectedComponentIn hD₀.isClosed hdisj
      (mem_connectedComponentIn hp_compl) hp.1
  exact fun x hxC => ⟨hC_sub_D₀ hxC, fun hxbd => (hC_sub_compl hxC).2 (hbd_sub hxbd)⟩

/-- Every edge `e ∈ H.E` is contained in `α_disc S₀ \ subBd (α_disc S₀)` for some `S₀ ∈ S_seg` with
`η.eMap e ∈ E(S₀.G)`, and any region `r ∈ J.R` meeting `e` equals `α_disc S₀ \ subBd (α_disc S₀)`.
-/
private theorem edge_in_arrangement_disc [T2Space S] (hS : IsClosedSurface S)
    {α : Type v} {β : Type w} {G : Graph α β} {H J : Drawing S} {η : SpanEmbedding H G}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hSeg : IsThreeSegregation G S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G H η S_seg α_disc α_pt)
    (hJU : J.U = ⋃ S₁ ∈ S_seg, subBd (α_disc S₁))
    {e : Set S} (he : e ∈ H.E) :
    ∃ S₀ ∈ S_seg, η.eMap e ∈ E(S₀.G) ∧ e ⊆ α_disc S₀ \ subBd (α_disc S₀) ∧
      ∀ r ∈ J.R, (r ∩ e).Nonempty → r = α_disc S₀ \ subBd (α_disc S₀) := by
  have he_G : η.eMap e ∈ E(G) := η.imageGraph_le.edgeSet_mono (η.bijOn_e.mapsTo he)
  have he_union : η.eMap e ∈ E(subgraphSUnion G ((fun S₁ : Society α β => S₁.G) '' S_seg)) :=
    hSeg.1.union_eq.symm ▸ he_G
  simp only [subgraphSUnion, edgeSet_restrict, mem_inter_iff, mem_iUnion, mem_image,
    exists_prop] at he_union
  obtain ⟨_, ⟨S₀, hS₀, rfl⟩, he_S₀⟩ := he_union.2
  have he_disc : e ⊆ α_disc S₀ := (hComp.inter_E_iff S₀ hS₀ e he).mpr he_S₀
  have he_diff : e ⊆ α_disc S₀ \ subBd (α_disc S₀) := by
    intro x hxe
    refine ⟨he_disc hxe, fun hxbd => ?_⟩
    have hx_inter : x ∈ H.U ∩ subBd (α_disc S₀) := ⟨(he.2.1 hxe).1, hxbd⟩
    rw [hComp.bd_inter_eq S₀ hS₀] at hx_inter
    exact (he.2.1 hxe).2 hx_inter.1
  refine ⟨S₀, hS₀, he_S₀, he_diff, fun r hr ⟨x, hxr, hxe⟩ => ?_⟩
  have hreg₀ : α_disc S₀ \ subBd (α_disc S₀) ∈ J.R :=
    region_of_glued_arrangement hS hArr hJU hS₀
  exact region_eq_of_mem hr hreg₀ hxr (he_diff hxe)

/-- Claim (1) in the proof of (7.7) (page 38):
"$r \subseteq \Delta_1 - bd(\Delta_1)$ for every region $r$ of $J$ with $\bar{r} \cap
(\Delta_2 - bd(\Delta_2)) \ne \emptyset$." -/
private theorem lemma_7_7_claim_1 [T2Space S]
    (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {α : Type v} {β : Type w}
    {G : Graph α β} {H C₁ C₂ J : Drawing S} {η : SpanEmbedding H G}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Δ₁ Δ₂ : Set S}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hθ : 6 ≤ θ) (hd : HasTangleMetric H θ T d)
    (hz : z ∈ H.A) (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂)
    (hz_sub : z ⊆ Δ₂ \ subBd Δ₂) (hΔ₂_sub₁ : Δ₂ ⊆ Δ₁ \ subBd Δ₁)
    (hii : ∀ x ∈ H.A, x ⊆ Δ₁ → d z x ≤ θ - 4)
    (hiii : ∀ x ∈ H.A, d z x ≤ 3 → x ⊆ Δ₂ \ subBd Δ₂)
    (hC₁ : C₁.IsCircuit) (hC₁s : C₁.IsSubdrawing H) (hbd₁ : subBd Δ₁ = C₁.U)
    (hC₂ : C₂.IsCircuit) (hC₂s : C₂.IsSubdrawing H) (hbd₂ : subBd Δ₂ = C₂.U)
    (hdisj : Disjoint C₁.V C₂.V)
    (hSeg : IsThreeSegregation G S_seg) (hLoc : IsTangleLocal G H η T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G H η S_seg α_disc α_pt)
    (hJU : J.U = ⋃ S₁ ∈ S_seg, subBd (α_disc S₁))
    {r : Set S} (hr : r ∈ J.R) (hinter : (closure r ∩ (Δ₂ \ subBd Δ₂)).Nonempty) :
    r ⊆ Δ₁ \ subBd Δ₁ := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  by_contra hnot_sub
  obtain ⟨hOD₂, _, _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ₂
  obtain ⟨y₀, hy₀_cl, hy₀_Δ₂⟩ := hinter
  obtain ⟨x₂, hx₂_Δ₂, hx₂_r⟩ := mem_closure_iff.mp hy₀_cl (Δ₂ \ subBd Δ₂) hOD₂.1 hy₀_Δ₂
  obtain ⟨y, hy_r, hy_not₁⟩ := not_subset.mp hnot_sub
  have hr_open : IsOpen r := region_isOpen hr
  have hr_conn : IsPreconnected r := region_isPreconnected hr
  have hfr₁ : frontier Δ₁ = C₁.U := by rw [subBd_eq_frontier', hbd₁]
  have hfr₂ : frontier Δ₂ = C₂.U := by rw [subBd_eq_frontier', hbd₂]
  have hr_C₁ : (r ∩ C₁.U).Nonempty := by
    by_cases hy_Δ₁ : y ∈ Δ₁
    · have hy_bd₁ : y ∈ subBd Δ₁ := by_contra fun hn => hy_not₁ ⟨hy_Δ₁, hn⟩
      exact ⟨y, hy_r, hbd₁ ▸ hy_bd₁⟩
    · by_contra h_emp
      rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty, ← hfr₁] at h_emp
      have hsub₁ : r ⊆ Δ₁ :=
        subset_of_disjoint_frontier hr_conn hΔ₁.isClosed h_emp hx₂_r (hΔ₂_sub₁ hx₂_Δ₂.1).1
      exact hy_Δ₁ (hsub₁ hy_r)
  have hr_C₂ : (r ∩ C₂.U).Nonempty := by
    by_contra h_emp
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty, ← hfr₂] at h_emp
    have hsub₂ : r ⊆ Δ₂ :=
      subset_of_disjoint_frontier hr_conn hΔ₂.isClosed h_emp hx₂_r hx₂_Δ₂.1
    exact hy_not₁ (hΔ₂_sub₁ (hsub₂ hy_r))
  obtain ⟨p₁, hp₁_r, hp₁_C₁⟩ := hr_C₁
  obtain ⟨e₁, he₁, hp₁_cl⟩ := exists_edge_closure_of_mem_circuit_U hC₁ hp₁_C₁
  have hre₁ : (r ∩ e₁).Nonempty := mem_closure_iff.mp hp₁_cl r hr_open hp₁_r
  obtain ⟨p₂, hp₂_r, hp₂_C₂⟩ := hr_C₂
  obtain ⟨e₂, he₂, hp₂_cl⟩ := exists_edge_closure_of_mem_circuit_U hC₂ hp₂_C₂
  have hre₂ : (r ∩ e₂).Nonempty := mem_closure_iff.mp hp₂_cl r hr_open hp₂_r
  obtain ⟨S₁, hS₁, he₁_S₁, _, hr_eq₁⟩ :=
    edge_in_arrangement_disc hS hSeg hArr hComp hJU (hC₁s.2 he₁)
  obtain ⟨S₂, hS₂, he₂_S₂, _, hr_eq₂⟩ :=
    edge_in_arrangement_disc hS hSeg hArr hComp hJU (hC₂s.2 he₂)
  have hr₁ : r = α_disc S₁ \ subBd (α_disc S₁) := hr_eq₁ r hr hre₁
  have hr₂ : r = α_disc S₂ \ subBd (α_disc S₂) := hr_eq₂ r hr hre₂
  have hS_eq : S₁ = S₂ := by
    by_contra hne
    obtain ⟨q, hq⟩ := region_nonempty hr
    have hq₁ : q ∈ α_disc S₁ \ subBd (α_disc S₁) := hr₁ ▸ hq
    have hq₂ : q ∈ α_disc S₂ \ subBd (α_disc S₂) := hr₂ ▸ hq
    obtain ⟨v, ⟨hv₁, _⟩, rfl⟩ := hArr.inter_discs S₁ hS₁ S₂ hS₂ hne ⟨hq₁.1, hq₂.1⟩
    exact hq₁.2 ((hArr.isClosedDisc S₁ hS₁).2 v hv₁)
  subst hS_eq
  exact no_two_circuits_in_arrangement_piece hS hConn hθ hd hz hΔ₁ hΔ₂ hz_sub
    hΔ₂_sub₁ hii hiii hC₁ hC₁s hbd₁ hC₂ hC₂s hbd₂ hdisj hSeg hLoc hS₁ he₁ he₁_S₁ he₂ he₂_S₂

/-- Every edge `e ∈ C.E` belonging to `(D_J S₀).E` is a line with two distinct ends in `(D_J S₀).V`
(and cannot be a loop). -/
private theorem circuit_edge_isLineWithEnds [T2Space S]
    (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {α : Type v} {β : Type w}
    {G : Graph α β} {H C₁ C₂ J C D₀ : Drawing S} {η : SpanEmbedding H G}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Δ₁ Δ₂ Λ : Set S}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hθ : 6 ≤ θ) (hd : HasTangleMetric H θ T d)
    (hz : z ∈ H.A) (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂)
    (hz_sub : z ⊆ Δ₂ \ subBd Δ₂) (hΔ₂_sub₁ : Δ₂ ⊆ Δ₁ \ subBd Δ₁)
    (hii : ∀ x ∈ H.A, x ⊆ Δ₁ → d z x ≤ θ - 4)
    (hiii : ∀ x ∈ H.A, d z x ≤ 3 → x ⊆ Δ₂ \ subBd Δ₂)
    (hC₁ : C₁.IsCircuit) (hC₁s : C₁.IsSubdrawing H) (hbd₁ : subBd Δ₁ = C₁.U)
    (hC₂ : C₂.IsCircuit) (hC₂s : C₂.IsSubdrawing H) (hbd₂ : subBd Δ₂ = C₂.U)
    (hSeg : IsThreeSegregation G S_seg) (hLoc : IsTangleLocal G H η T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G H η S_seg α_disc α_pt)
    (hJU : J.U = ⋃ S₁ ∈ S_seg, subBd (α_disc S₁))
    (hOpenΛ : IsOpenDisc Λ) (hclΛ_sub : closure Λ ⊆ Δ₁) (hclΛ_disc : IsClosedDisc (closure Λ))
    (hbd_clΛ : subBd (closure Λ) = C.U) (hdiffΛ : closure Λ \ C.U = Λ)
    (hZΛ : Δ₂ \ subBd Δ₂ ⊆ Λ)
    {S₀ : Society α β} (hS₀ : S₀ ∈ S_seg)
    (hD₀U : D₀.U = subBd (α_disc S₀)) (hD₀V : α_pt '' S₀.Ω.bar ⊆ D₀.V)
    {e : Set S} (heC : e ∈ C.E) (heD₀ : e ∈ D₀.E) :
    ∃ a b : S, a ≠ b ∧ closure e ∩ D₀.V = {a, b} ∧ IsLineWithEnds (closure e) a b := by
  rcases D₀.edge_cond e heD₀ with hline | ⟨u, huV, hO_e⟩
  · exact hline
  · exfalso
    have hD₀_disc : IsClosedDisc (α_disc S₀) := (hArr.isClosedDisc S₀ hS₀).1
    have hcl_sub_bd₀ : closure e ⊆ subBd (α_disc S₀) :=
      hD₀U ▸ D₀.closure_subset_U heD₀
    have hcl_eq_bd₀ : closure e = subBd (α_disc S₀) :=
      eq_subBd_of_isOArc_subset hS hD₀_disc hO_e hcl_sub_bd₀
    have hcl_sub_CU : closure e ⊆ subBd (closure Λ) :=
      hbd_clΛ.symm ▸ C.closure_subset_U heC
    have hcl_eq_CU : closure e = subBd (closure Λ) :=
      eq_subBd_of_isOArc_subset hS hclΛ_disc hO_e hcl_sub_CU
    have hbd_eq : subBd (closure Λ) = subBd (α_disc S₀) :=
      hcl_eq_CU.symm.trans hcl_eq_bd₀
    have hbar_sub_u : α_pt '' S₀.Ω.bar ⊆ {u} := by
      rw [← huV, hcl_eq_bd₀, ← hD₀U, inter_eq_right.mpr D₀.V_subset_U]
      exact hD₀V
    by_cases h_eq : closure Λ = α_disc S₀
    · obtain ⟨p₂, hp₂⟩ := IsOArc.nonempty (isOArc_of_isCircuit hC₂)
      obtain ⟨e₂, he₂, _⟩ := exists_edge_closure_of_mem_circuit_U hC₂ hp₂
      obtain ⟨_, hcl₂, _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ₂
      have hΔ₂_sub_clΛ : Δ₂ ⊆ closure Λ :=
        hcl₂ ▸ isClosed_closure.closure_subset_iff.mpr (hZΛ.trans subset_closure)
      have he₂_sub : e₂ ⊆ α_disc S₀ := by
        intro x hxe₂
        exact h_eq ▸ hΔ₂_sub_clΛ (hΔ₂.isClosed.closure_eq ▸ (hbd₂ ▸ (he₂.2.1 hxe₂).1).1)
      have he₂_S₀ : η.eMap e₂ ∈ E(S₀.G) :=
        (hComp.inter_E_iff S₀ hS₀ e₂ (hC₂s.2 he₂)).mp he₂_sub
      have h2 := (two_le_bar_image_ncard_of_mem_C2 hS hConn hθ hd hz hΔ₁ hΔ₂ hz_sub
        hΔ₂_sub₁ hii hiii hC₂ hC₂s hbd₂ hSeg hLoc hArr hS₀ he₂ he₂_S₀).1
      have hle1 : (α_pt '' S₀.Ω.bar).ncard ≤ 1 :=
        (ncard_le_ncard hbar_sub_u (finite_singleton u)).trans (by simp)
      omega
    · have hdiscBd_eq : discBd (closure Λ) = discBd (α_disc S₀) := by
        rw [← IsClosedDisc.subBd_eq_discBd hS hclΛ_disc,
          ← IsClosedDisc.subBd_eq_discBd hS hD₀_disc, hbd_eq]
      have hcov : closure Λ ∪ α_disc S₀ = univ :=
        cover_of_discBd_eq hS hclΛ_disc hD₀_disc hdiscBd_eq h_eq
      obtain ⟨p₁, hp₁⟩ := IsOArc.nonempty (isOArc_of_isCircuit hC₁)
      obtain ⟨e₁, he₁, _⟩ := exists_edge_closure_of_mem_circuit_U hC₁ hp₁
      obtain ⟨S₁, hS₁, he₁_S₁, he₁_diff, _⟩ :=
        edge_in_arrangement_disc hS hSeg hArr hComp hJU (hC₁s.2 he₁)
      by_cases hS_eq : S₁ = S₀
      · subst hS_eq
        have hinj_α : InjOn α_pt S₁.Ω.bar :=
          hArr.injOn_pts.mono (subset_biUnion_of_mem (u := fun S₂ : Society α β => S₂.Ω.bar) hS₁)
        have hbar_le1 : S₁.Ω.bar.ncard ≤ 1 := by
          rw [← hinj_α.ncard_image]
          exact (ncard_le_ncard hbar_sub_u (finite_singleton u)).trans (by simp)
        have hsub : η.vMap '' (C₁.V ∩ {v ∈ H.V | η.vMap v ∈ S₁.Ω.bar}) ⊆ S₁.Ω.bar := by
          rintro _ ⟨v, ⟨_, _, hv⟩, rfl⟩
          exact hv
        have hinj_η : InjOn η.vMap (C₁.V ∩ {v ∈ H.V | η.vMap v ∈ S₁.Ω.bar}) :=
          η.bijOn_v.injOn.mono fun _ hv => hv.2.1
        have hle1 : (C₁.V ∩ {v ∈ H.V | η.vMap v ∈ S₁.Ω.bar}).ncard ≤ 1 := by
          calc
            (C₁.V ∩ {v ∈ H.V | η.vMap v ∈ S₁.Ω.bar}).ncard
              = (η.vMap '' (C₁.V ∩ {v ∈ H.V | η.vMap v ∈ S₁.Ω.bar})).ncard :=
                hinj_η.ncard_image.symm
            _ ≤ S₁.Ω.bar.ncard := ncard_le_ncard hsub S₁.Ω.finite_bar
            _ ≤ 1 := hbar_le1
        exact no_circuit_in_arrangement_piece hS hConn hθ hd hz hΔ₁ hΔ₂ hΔ₁ hz_sub
          hΔ₂_sub₁ (hΔ₂_sub₁.trans sdiff_subset) subset_rfl hii hiii hC₁ hC₁s hbd₁ hSeg hLoc hS₁
          he₁ he₁_S₁ hle1
      · obtain ⟨q₁, hq₁⟩ := atom_nonempty (Or.inl (Or.inr (hC₁s.2 he₁)))
        have hq₁_S₁ : q₁ ∈ α_disc S₁ \ subBd (α_disc S₁) := he₁_diff hq₁
        have hq₁_not₀ : q₁ ∉ α_disc S₀ := by
          intro hq₁_0
          obtain ⟨v, ⟨hv₁, _⟩, rfl⟩ := hArr.inter_discs S₁ hS₁ S₀ hS₀ hS_eq ⟨hq₁_S₁.1, hq₁_0⟩
          exact hq₁_S₁.2 ((hArr.isClosedDisc S₁ hS₁).2 v hv₁)
        have hq₁_clΛ : q₁ ∈ closure Λ := by
          have h_univ : q₁ ∈ closure Λ ∪ α_disc S₀ := hcov.symm ▸ mem_univ q₁
          exact h_univ.resolve_right hq₁_not₀
        have hq₁_not_CU : q₁ ∉ C.U := by
          intro hq₁_CU
          exact hq₁_not₀ (hD₀_disc.isClosed.closure_eq ▸ (hbd_eq ▸ hbd_clΛ ▸ hq₁_CU).1)
        have hq₁_Λ : q₁ ∈ Λ := hdiffΛ ▸ ⟨hq₁_clΛ, hq₁_not_CU⟩
        have hq₁_int₁ : q₁ ∈ interior Δ₁ :=
          interior_maximal (subset_closure.trans hclΛ_sub) hOpenΛ.1 hq₁_Λ
        have hq₁_bd₁ : q₁ ∈ frontier Δ₁ := by
          rw [subBd_eq_frontier', hbd₁]
          exact (he₁.2.1 hq₁).1
        exact hq₁_bd₁.2 hq₁_int₁

open Classical in
private noncomputable abbrev arrangement_boundary_vertices
    {α β : Type*} {S_seg : Set (Society α β)} {α_disc : Society α β → Set S}
    {α_pt : α → S} (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (p_S : S) (S₀ : Society α β) : Set S :=
  if h : S₀ ∈ S_seg then
    if S₀.Ω.bar.Nonempty then α_pt '' S₀.Ω.bar
    else {(IsOArc.nonempty (hArr.natural_order S₀ h).1).some}
  else {p_S}

private theorem disc_boundary_drawing_exists
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type v}
    {β : Type w}
    {H : Drawing S}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (p_S : S) :
    ∀ (S₀ : Society α β), ∃ D : Drawing S,
      S₀ ∈ S_seg → D.U = subBd (α_disc S₀) ∧
        D.V = arrangement_boundary_vertices hArr p_S S₀ := by
  classical
  let V_J := arrangement_boundary_vertices hArr p_S
  intro S₀
  by_cases hS₀ : S₀ ∈ S_seg
  · have hO₀ : IsOArc (subBd (α_disc S₀)) := (hArr.natural_order S₀ hS₀).1
    have hfin : (V_J S₀).Finite := by
      by_cases hne : S₀.Ω.bar.Nonempty
      · simp only [V_J, arrangement_boundary_vertices, hS₀, hne, ↓reduceDIte, ↓reduceIte]
        exact S₀.Ω.finite_bar.image α_pt
      · simp only [V_J, arrangement_boundary_vertices, hS₀, hne, ↓reduceDIte, ↓reduceIte]
        exact finite_singleton _
    have hne_V : (V_J S₀).Nonempty := by
      by_cases hne : S₀.Ω.bar.Nonempty
      · simp only [V_J, arrangement_boundary_vertices, hS₀, hne, ↓reduceDIte, ↓reduceIte]
        exact hne.image α_pt
      · simp only [V_J, arrangement_boundary_vertices, hS₀, hne, ↓reduceDIte, ↓reduceIte]
        exact singleton_nonempty _
    have hsub_V : V_J S₀ ⊆ subBd (α_disc S₀) := by
      by_cases hne : S₀.Ω.bar.Nonempty
      · simp only [V_J, arrangement_boundary_vertices, hS₀, hne, ↓reduceDIte, ↓reduceIte]
        rintro _ ⟨v, hv, rfl⟩
        exact (hArr.isClosedDisc S₀ hS₀).2 v hv
      · simp only [V_J, arrangement_boundary_vertices, hS₀, hne, ↓reduceDIte, ↓reduceIte,
          singleton_subset_iff]
        exact (IsOArc.nonempty hO₀).some_mem
    obtain ⟨D, hDU, hDV⟩ := exists_drawing_on_oArc hO₀ hfin hne_V hsub_V
    exact ⟨D, fun _ => ⟨hDU, hDV⟩⟩
  · exact ⟨H, fun h => absurd h hS₀⟩

private theorem push_finite_boundary_edges
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    {α : Type v}
    {β : Type w}
    {G : Graph α β}
    {H : Drawing S}
    {C₁ : Drawing S}
    {C₂ : Drawing S}
    {η : SpanEmbedding H G}
    {Δ₁ : Set S}
    {Δ₂ : Set S}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    (hΔ₁ : IsClosedDisc Δ₁)
    (hΔ₂ : IsClosedDisc Δ₂)
    (hC₁s : C₁.IsSubdrawing H)
    (hbd₁ : subBd Δ₁ = C₁.U)
    (hC₂s : C₂.IsSubdrawing H)
    (hbd₂ : subBd Δ₂ = C₂.U)
    (hSeg : IsThreeSegregation G S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G H η S_seg α_disc α_pt)
    (V_J : Society α β → Set S)
    (D_J : Society α β → Drawing S)
    (hDJ : ∀ S₀ ∈ S_seg, (D_J S₀).U = subBd (α_disc S₀) ∧ (D_J S₀).V = V_J S₀)
    (J : Drawing S)
    (hJV : J.V = ⋃ S₀ ∈ S_seg, (D_J S₀).V)
    (hJE : J.E = ⋃ S₀ ∈ S_seg, (D_J S₀).E)
    (C : Drawing S)
    (Λ : Set S)
    (hCJ : C.IsSubdrawing J)
    (hCU : C.U ⊆ Δ₁)
    (hdiffΛ : closure Λ \ C.U = Λ)
    (hZΛ : Δ₂ \ subBd Δ₂ ⊆ Λ)
    (hline : ∀ e ∈ C.E, ∀ S₀ ∈ S_seg, e ∈ (D_J S₀).E → ∃ a b, a ≠ b ∧ closure e ∩ (D_J S₀).V = {a,
      b} ∧ IsLineWithEnds (closure e) a b ∧ (D_J S₀).V = α_pt '' S₀.Ω.bar) :
    ∀ (s : Finset (Set S)), ↑s ⊆ C.E → ∃ Ψ : S ≃ₜ S,
      (∀ x ∈ Δ₂ ∪ univ \ (Δ₁ \ subBd Δ₁) ∪ J.V, Ψ x = x) ∧
      (∀ e ∈ C.E \ ↑s, ∀ x ∈ closure e, Ψ x = x) ∧ ∀ e ∈ s, ∀ S₁ ∈ S_seg, ⇑Ψ '' closure e ∩ α_disc
      S₁ ⊆ α_pt '' S₁.Ω.bar := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨Homeomorph.refl S, fun _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ h => False.elim (by simp at h)⟩
  | @insert e₀ s he₀_not ih =>
    intro hs_sub
    have he₀C : e₀ ∈ C.E := hs_sub (Finset.mem_insert_self e₀ s)
    have hs_sub' : (s : Set (Set S)) ⊆ C.E :=
      fun e he => hs_sub (Finset.mem_insert_of_mem he)
    obtain ⟨Ψ₀, hΨ₀_fix, hΨ₀_unpushed, hΨ₀_pushed⟩ := ih hs_sub'
    have he₀_unpushed : ∀ x ∈ closure e₀, Ψ₀ x = x :=
      hΨ₀_unpushed e₀ ⟨he₀C, he₀_not⟩
    have he₀_img : Ψ₀ '' (closure e₀) = closure e₀ := by
      ext x
      exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ (he₀_unpushed y hy).symm ▸ hy,
        fun hx => ⟨x, hx, he₀_unpushed x hx⟩⟩
    have he₀J : e₀ ∈ J.E := hCJ.2 he₀C
    rw [hJE] at he₀J
    obtain ⟨S₀, hS₀, he₀_D₀⟩ := mem_iUnion₂.mp he₀J
    obtain ⟨a, b, hab, hV_ab, hL, hDV_eq⟩ := hline e₀ he₀C S₀ hS₀ he₀_D₀
    have hD₀_disc : IsClosedDisc (α_disc S₀) := (hArr.isClosedDisc S₀ hS₀).1
    have hL_bd₀ : closure e₀ ⊆ subBd (α_disc S₀) :=
      (hDJ S₀ hS₀).1 ▸ (D_J S₀).closure_subset_U he₀_D₀
    let Y : Set S :=
      Δ₂ ∪ (univ \ (Δ₁ \ subBd Δ₁)) ∪ J.V ∪
        (⋃ S₁ ∈ S_seg \ {S₀}, α_disc S₁) ∪
        (⋃ e ∈ C.E \ {e₀}, Ψ₀ '' (closure e))
    have hY_closed : IsClosed Y := by
      refine ((((hΔ₂.isClosed.union ?_).union J.finite_V.isClosed).union ?_).union ?_)
      · exact isClosed_univ.sdiff (IsClosedDisc.isOpenDisc_diff_subBd hS hΔ₁).1.1
      · exact (hSeg.1.finite.subset sdiff_subset).isClosed_biUnion fun S₁ hS₁ =>
          (hArr.isClosedDisc S₁ hS₁.1).1.isClosed
      · exact (C.finite_edges.subset sdiff_subset).isClosed_biUnion fun e _ =>
          Ψ₀.isClosed_image.mpr isClosed_closure
    have ha_JV : a ∈ J.V := by
      rw [hJV]
      have ha_V₀ : a ∈ (D_J S₀).V := by
        have : a ∈ closure e₀ ∩ (D_J S₀).V := by rw [hV_ab]; exact mem_insert a {b}
        exact this.2
      exact mem_iUnion₂.mpr ⟨S₀, hS₀, ha_V₀⟩
    have hb_JV : b ∈ J.V := by
      rw [hJV]
      have hb_V₀ : b ∈ (D_J S₀).V := by
        have : b ∈ closure e₀ ∩ (D_J S₀).V := by rw [hV_ab]; exact mem_insert_of_mem a rfl
        exact this.2
      exact mem_iUnion₂.mpr ⟨S₀, hS₀, hb_V₀⟩
    have haY : a ∈ Y := Or.inl (Or.inl (Or.inr ha_JV))
    have hbY : b ∈ Y := Or.inl (Or.inl (Or.inr hb_JV))
    have hHU_inter : H.U ∩ closure e₀ ⊆ {a, b} := by
      rintro x ⟨hxH, hxe₀⟩
      have hx_bd : x ∈ H.U ∩ subBd (α_disc S₀) := ⟨hxH, hL_bd₀ hxe₀⟩
      rw [hComp.bd_inter_eq S₀ hS₀] at hx_bd
      have hx_pt : α_pt (η.vMap x) = x :=
        hComp.pt_eq x hx_bd.1 (subset_biUnion_of_mem (u := fun S₁ : Society α β
          => S₁.Ω.bar) hS₀ hx_bd.2)
      have hx_V₀ : x ∈ (D_J S₀).V := by
        rw [hDV_eq]
        exact ⟨η.vMap x, hx_bd.2, hx_pt⟩
      rw [← hV_ab]
      exact ⟨hxe₀, hx_V₀⟩
    have hJV_inter : J.V ∩ closure e₀ ⊆ {a, b} := by
      rintro x ⟨hxJV, hxe₀⟩
      rw [hJV] at hxJV
      obtain ⟨S₁, hS₁, hxV₁⟩ := mem_iUnion₂.mp hxJV
      by_cases h_eq : S₁ = S₀
      · subst h_eq
        rw [← hV_ab]
        exact ⟨hxe₀, hxV₁⟩
      · have hx_D₁ : x ∈ α_disc S₁ :=
          (hArr.isClosedDisc S₁ hS₁).1.isClosed.closure_eq ▸
            ((hDJ S₁ hS₁).1 ▸ (D_J S₁).V_subset_U hxV₁).1
        have hx_D₀ : x ∈ α_disc S₀ :=
          hD₀_disc.isClosed.closure_eq ▸ (hL_bd₀ hxe₀).1
        obtain ⟨v, ⟨_, hv₀⟩, rfl⟩ := hArr.inter_discs S₁ hS₁ S₀ hS₀ h_eq ⟨hx_D₁, hx_D₀⟩
        have hx_V₀ : α_pt v ∈ (D_J S₀).V := by
          rw [hDV_eq]
          exact ⟨v, hv₀, rfl⟩
        rw [← hV_ab]
        exact ⟨hxe₀, hx_V₀⟩
    have hYL : Y ∩ closure e₀ ⊆ {a, b} := by
      rintro x ⟨hxY, hxe₀⟩
      have hx_CU : x ∈ C.U := C.closure_subset_U he₀C hxe₀
      rcases hxY with (((hxΔ₂ | hx_out₁) | hxJV) | hxS₁) | hxe
      · have hx_not_int₂ : x ∉ Δ₂ \ subBd Δ₂ := by
          intro hx_int₂
          have hx_Λ : x ∈ Λ := hZΛ hx_int₂
          rw [← hdiffΛ] at hx_Λ
          exact hx_Λ.2 hx_CU
        have hx_bd₂ : x ∈ subBd Δ₂ := by_contra fun hn => hx_not_int₂ ⟨hxΔ₂, hn⟩
        exact hHU_inter ⟨hC₂s.U_subset (hbd₂ ▸ hx_bd₂), hxe₀⟩
      · have hx_Δ₁ : x ∈ Δ₁ := hCU hx_CU
        have hx_bd₁ : x ∈ subBd Δ₁ := by_contra fun hn => hx_out₁.2 ⟨hx_Δ₁, hn⟩
        exact hHU_inter ⟨hC₁s.U_subset (hbd₁ ▸ hx_bd₁), hxe₀⟩
      · exact hJV_inter ⟨hxJV, hxe₀⟩
      · obtain ⟨S₁, ⟨hS₁, hne⟩, hxD₁⟩ := mem_iUnion₂.mp hxS₁
        have hx_D₀ : x ∈ α_disc S₀ := hD₀_disc.isClosed.closure_eq ▸ (hL_bd₀ hxe₀).1
        obtain ⟨v, ⟨_, hv₀⟩, rfl⟩ := hArr.inter_discs S₁ hS₁ S₀ hS₀ hne ⟨hxD₁, hx_D₀⟩
        rw [← hV_ab, hDV_eq]
        exact ⟨hxe₀, ⟨v, hv₀, rfl⟩⟩
      · obtain ⟨e, ⟨heC, hne⟩, hx_img⟩ := mem_iUnion₂.mp hxe
        by_cases hes : e ∈ s
        · have hx_bar : x ∈ α_pt '' S₀.Ω.bar :=
            hΨ₀_pushed e hes S₀ hS₀ ⟨hx_img, hD₀_disc.isClosed.closure_eq ▸ (hL_bd₀ hxe₀).1⟩
          rw [← hV_ab, hDV_eq]
          exact ⟨hxe₀, hx_bar⟩
        · have hx_cl_e : x ∈ closure e := by
            obtain ⟨y, hy, rfl⟩ := hx_img
            rwa [hΨ₀_unpushed e ⟨heC, hes⟩ y hy]
          have hx_JV : x ∈ J.V := by
            by_contra hx_not_V
            have hxe' : x ∈ e := J.closure_diff_V (hCJ.2 heC) ▸ ⟨hx_cl_e, hx_not_V⟩
            have hxe₀' : x ∈ e₀ := J.closure_diff_V (hCJ.2 he₀C) ▸ ⟨hxe₀, hx_not_V⟩
            exact hne (J.edge_eq_of_mem (hCJ.2 heC) (hCJ.2 he₀C) hxe' hxe₀')
          exact hJV_inter ⟨hx_JV, hxe₀⟩
    obtain ⟨h, hh_fix, hh_push⟩ :=
      push_arc hS hD₀_disc hL hL_bd₀ hY_closed haY hbY hYL
    refine ⟨Ψ₀.trans h, ?_, ?_, ?_⟩
    · intro x hx
      change h (Ψ₀ x) = x
      rw [hΨ₀_fix x hx]
      exact hh_fix x (Or.inl (Or.inl hx))
    · intro e he x hx
      change h (Ψ₀ x) = x
      have he_not_s : e ∉ s := fun hes => he.2 (Finset.mem_insert_of_mem hes)
      have he_ne : e ≠ e₀ := fun h_eq => he.2 (h_eq ▸ Finset.mem_insert_self e₀ s)
      have hΨ₀x : Ψ₀ x = x := hΨ₀_unpushed e ⟨he.1, he_not_s⟩ x hx
      rw [hΨ₀x]
      refine hh_fix x (Or.inr (mem_iUnion₂.mpr ⟨e, ⟨he.1, he_ne⟩, ⟨x, hx, hΨ₀x⟩⟩))
    · intro e he S₁ hS₁
      rcases Finset.mem_insert.mp he with he_eq | hes
      · subst he_eq
        have himg_eq : (Ψ₀.trans h) '' (closure e) = h '' (closure e) := by
          change (h ∘ Ψ₀) '' (closure e) = _
          rw [image_comp, he₀_img]
        rw [himg_eq]
        by_cases hS_eq : S₁ = S₀
        · subst hS_eq
          refine hh_push.trans ?_
          rw [← hDV_eq, ← hV_ab]
          exact inter_subset_right
        · rintro x ⟨⟨y, hy, rfl⟩, hxD₁⟩
          have hy_Y : h y ∈ Y :=
            Or.inl (Or.inr (mem_iUnion₂.mpr ⟨S₁, ⟨hS₁, hS_eq⟩, hxD₁⟩))
          have hhy : h (h y) = h y := hh_fix (h y) hy_Y
          have hy_eq : h y = y := h.injective hhy
          rw [hy_eq] at hxD₁ ⊢
          have hyD₀ : y ∈ α_disc S₀ := hD₀_disc.isClosed.closure_eq ▸ (hL_bd₀ hy).1
          obtain ⟨v, ⟨_, hv₁⟩, rfl⟩ :=
            hArr.inter_discs S₀ hS₀ S₁ hS₁ (Ne.symm hS_eq) ⟨hyD₀, hxD₁⟩
          exact ⟨v, hv₁, rfl⟩
      · have he_ne : e ≠ e₀ := fun h_eq => he₀_not (h_eq ▸ hes)
        have himg_eq : (Ψ₀.trans h) '' (closure e) = Ψ₀ '' (closure e) := by
          change (h ∘ Ψ₀) '' (closure e) = _
          rw [image_comp]
          ext x
          exact ⟨fun ⟨y, hy, hyx⟩ =>
            hyx ▸ (hh_fix y (Or.inr (mem_iUnion₂.mpr ⟨e, ⟨hs_sub' hes, he_ne⟩, hy⟩))).symm ▸ hy,
            fun hx => ⟨x, hx, hh_fix x (Or.inr (mem_iUnion₂.mpr ⟨e, ⟨hs_sub' hes, he_ne⟩, hx⟩))⟩⟩
        rw [himg_eq]
        exact hΨ₀_pushed e hes S₁ hS₁

private theorem proper_arrangement_boundary_edge_is_arc
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S]
    {α : Type v}
    {β : Type w}
    {G : Graph α β}
    {H : Drawing S}
    {C₁ : Drawing S}
    {C₂ : Drawing S}
    {η : SpanEmbedding H G}
    {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {z : Set S}
    {Δ₁ : Set S}
    {Δ₂ : Set S}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    (hθ : 6 ≤ θ)
    (hd : HasTangleMetric H θ T d)
    (hz : z ∈ H.A)
    (hΔ₁ : IsClosedDisc Δ₁)
    (hΔ₂ : IsClosedDisc Δ₂)
    (hz_sub : z ⊆ Δ₂ \ subBd Δ₂)
    (hΔ₂_sub₁ : Δ₂ ⊆ Δ₁ \ subBd Δ₁)
    (hii : ∀ x ∈ H.A, x ⊆ Δ₁ → d z x ≤ θ - 4)
    (hiii : ∀ x ∈ H.A, d z x ≤ 3 → x ⊆ Δ₂ \ subBd Δ₂)
    (hC₁ : C₁.IsCircuit)
    (hC₁s : C₁.IsSubdrawing H)
    (hbd₁ : subBd Δ₁ = C₁.U)
    (hC₂ : C₂.IsCircuit)
    (hC₂s : C₂.IsSubdrawing H)
    (hbd₂ : subBd Δ₂ = C₂.U)
    (hSeg : IsThreeSegregation G S_seg)
    (hLoc : IsTangleLocal G H η T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G H η S_seg α_disc α_pt)
    (p_S : S)
    (hVJ_sub_bar : ∀ S₀ ∈ S_seg, α_pt '' S₀.Ω.bar ⊆ arrangement_boundary_vertices hArr p_S S₀)
    (D_J : Society α β → Drawing S)
    (hDJ : ∀ S₀ ∈ S_seg,
      (D_J S₀).U = subBd (α_disc S₀) ∧ (D_J S₀).V = arrangement_boundary_vertices hArr p_S S₀)
    (J : Drawing S)
    (hJU : J.U = ⋃ S₀ ∈ S_seg, subBd (α_disc S₀))
    (C : Drawing S)
    (Λ : Set S)
    (hOpenΛ : IsOpenDisc Λ)
    (hclΛ_sub : closure Λ ⊆ Δ₁)
    (hclΛ_disc : IsClosedDisc (closure Λ))
    (hbd_clΛ : subBd (closure Λ) = C.U)
    (hdiffΛ : closure Λ \ C.U = Λ)
    (hZΛ : Δ₂ \ subBd Δ₂ ⊆ Λ) :
    ∀ e ∈ C.E, ∀ S₀ ∈ S_seg, e ∈ (D_J S₀).E → ∃ a b, a ≠ b ∧ closure e ∩ (D_J S₀).V = {a, b} ∧
      IsLineWithEnds (closure e) a b ∧ (D_J S₀).V = α_pt '' S₀.Ω.bar  := by
  classical
  intro e heC S₀ hS₀ heD₀
  obtain ⟨a, b, hab, hV_ab, hL⟩ :=
    circuit_edge_isLineWithEnds hS hConn hθ hd hz hΔ₁ hΔ₂ hz_sub hΔ₂_sub₁
      hii hiii hC₁ hC₁s hbd₁ hC₂ hC₂s hbd₂ hSeg hLoc hArr hComp hJU hOpenΛ hclΛ_sub hclΛ_disc
      hbd_clΛ hdiffΛ hZΛ hS₀ (hDJ S₀ hS₀).1 ((hDJ S₀ hS₀).2 ▸ hVJ_sub_bar S₀ hS₀) heC heD₀
  refine ⟨a, b, hab, hV_ab, hL, ?_⟩
  rw [(hDJ S₀ hS₀).2]
  have hne_bar : S₀.Ω.bar.Nonempty := by
    by_contra hnot
    have hV_sing : arrangement_boundary_vertices hArr p_S S₀ =
        {(IsOArc.nonempty (hArr.natural_order S₀ hS₀).1).some} := by
      simp [arrangement_boundary_vertices, hS₀, hnot]
    have ha_mem : a ∈ arrangement_boundary_vertices hArr p_S S₀ := by
      rw [← (hDJ S₀ hS₀).2]
      have : a ∈ closure e ∩ (D_J S₀).V := by rw [hV_ab]; exact mem_insert a {b}
      exact this.2
    have hb_mem : b ∈ arrangement_boundary_vertices hArr p_S S₀ := by
      rw [← (hDJ S₀ hS₀).2]
      have : b ∈ closure e ∩ (D_J S₀).V := by rw [hV_ab]; exact mem_insert_of_mem a rfl
      exact this.2
    rw [hV_sing, mem_singleton_iff] at ha_mem hb_mem
    exact hab (ha_mem.trans hb_mem.symm)
  simp [arrangement_boundary_vertices, hS₀, hne_bar]

/-- Graph Minors XIV, (7.7) (pages 37–38):
"Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in $H$
of order $\theta \ge 6$. Let $z \in A(H)$, let $C_1$, $C_2$ be disjoint circuits of $H$, and
let $U(C_1)$, $U(C_2)$ bound closed discs $\Delta_1$, $\Delta_2 \subseteq \Sigma$ with the
following properties:* (i) $z \subseteq \Delta_2 - bd(\Delta_2)$, and $\Delta_2 \subseteq
\Delta_1 - bd(\Delta_1)$ (ii) $d(z, x) \le \theta - 4$ for all $x \in A(H)$ with $x
\subseteq \Delta_1$ (iii) $x \subseteq \Delta_2 - bd(\Delta_2)$ for all $x \in A(H)$ with
$d(z, x) \le 3$. *Let $H$ be a subgraph of $G$, let $\mathscr{S}$ be a $\mathscr{T}$-local
3-segregation of $G$, and let $\alpha$ be an arrangement of $\mathscr{S}$ in $\Sigma$
compatible with $H$. Then there is an $\alpha$-normal $O$-arc $F \subseteq \Delta_1$,
bounding a closed disc in $\Delta_1$ including $\Delta_2$." -/
theorem theorem_7_7_proof
    [T2Space S] (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {α : Type v} {β : Type w}
    {G : Graph α β} {H C₁ C₂ : Drawing S} {η : SpanEmbedding H G}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Δ₁ Δ₂ : Set S}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hθ : 6 ≤ θ) (hd : HasTangleMetric H θ T d)
    (hz : z ∈ H.A) (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂)
    (hz_sub : z ⊆ Δ₂ \ subBd Δ₂) (hΔ₂_sub₁ : Δ₂ ⊆ Δ₁ \ subBd Δ₁)
    (hii : ∀ x ∈ H.A, x ⊆ Δ₁ → d z x ≤ θ - 4)
    (hiii : ∀ x ∈ H.A, d z x ≤ 3 → x ⊆ Δ₂ \ subBd Δ₂)
    (hC₁ : C₁.IsCircuit) (hC₁s : C₁.IsSubdrawing H) (hbd₁ : subBd Δ₁ = C₁.U)
    (hC₂ : C₂.IsCircuit) (hC₂s : C₂.IsSubdrawing H) (hbd₂ : subBd Δ₂ = C₂.U)
    (hdisj : Disjoint C₁.V C₂.V)
    (hSeg : IsThreeSegregation G S_seg) (hLoc : IsTangleLocal G H η T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G H η S_seg α_disc α_pt) :
    ∃ F Δ : Set S,
      IsOArc F ∧ F ⊆ Δ₁ ∧ IsArrangementNormal S_seg α_disc α_pt F ∧
      IsClosedDisc Δ ∧ subBd Δ = F ∧ Δ ⊆ Δ₁ ∧ Δ₂ ⊆ Δ := by
  classical
  have : ConnectedSpace S := hConn
  obtain ⟨p_S⟩ : Nonempty S := inferInstance
  let V_J := arrangement_boundary_vertices hArr p_S
  have hVJ_sub_bar : ∀ S₀ ∈ S_seg, α_pt '' S₀.Ω.bar ⊆ V_J S₀ := by
    intro S₀ hS₀
    by_cases hne : S₀.Ω.bar.Nonempty
    · simp [V_J, arrangement_boundary_vertices, hS₀, hne]
    · rw [not_nonempty_iff_eq_empty.mp hne, image_empty]
      exact empty_subset _
  have hDJ_exists : ∀ S₀ : Society α β, ∃ D : Drawing S,
      (S₀ ∈ S_seg → D.U = subBd (α_disc S₀) ∧ D.V = V_J S₀) := by
    exact disc_boundary_drawing_exists (S := S) (α := α) (β := β) (H := H) (S_seg := S_seg)
      (α_disc := α_disc) (α_pt := α_pt) hArr p_S
  choose D_J hDJ using hDJ_exists
  let s_seg : Finset (Society α β) := hSeg.1.finite.toFinset
  have hs_seg : ∀ S₀, S₀ ∈ s_seg ↔ S₀ ∈ S_seg := fun S₀ => Finite.mem_toFinset _
  have hmeet : ∀ S₁ ∈ s_seg, ∀ S₂ ∈ s_seg, S₁ ≠ S₂ →
      (D_J S₁).U ∩ (D_J S₂).U ⊆ (D_J S₁).V ∩ (D_J S₂).V := by
    intro S₁ hS₁ S₂ hS₂ hne x ⟨hx₁, hx₂⟩
    have hS₁' : S₁ ∈ S_seg := (hs_seg S₁).mp hS₁
    have hS₂' : S₂ ∈ S_seg := (hs_seg S₂).mp hS₂
    rw [(hDJ S₁ hS₁').1] at hx₁
    rw [(hDJ S₂ hS₂').1] at hx₂
    have hx_inter : x ∈ α_disc S₁ ∩ α_disc S₂ :=
      ⟨(hArr.isClosedDisc S₁ hS₁').1.isClosed.closure_eq ▸ hx₁.1,
       (hArr.isClosedDisc S₂ hS₂').1.isClosed.closure_eq ▸ hx₂.1⟩
    obtain ⟨v, ⟨hv₁, hv₂⟩, rfl⟩ := hArr.inter_discs S₁ hS₁' S₂ hS₂' hne hx_inter
    rw [(hDJ S₁ hS₁').2, (hDJ S₂ hS₂').2]
    exact ⟨hVJ_sub_bar S₁ hS₁' ⟨v, hv₁, rfl⟩, hVJ_sub_bar S₂ hS₂' ⟨v, hv₂, rfl⟩⟩
  obtain ⟨J, hJU_fin, hJV_fin, hJE_fin⟩ := exists_glued_drawing s_seg D_J hmeet
  have hJU : J.U = ⋃ S₀ ∈ S_seg, subBd (α_disc S₀) := by
    rw [hJU_fin]
    ext x
    simp only [mem_iUnion, hs_seg]
    exact ⟨fun ⟨S₀, hS₀, hx⟩ => ⟨S₀, hS₀, (hDJ S₀ hS₀).1 ▸ hx⟩,
      fun ⟨S₀, hS₀, hx⟩ => ⟨S₀, hS₀, (hDJ S₀ hS₀).1.symm ▸ hx⟩⟩
  have hJV : J.V = ⋃ S₀ ∈ S_seg, (D_J S₀).V := by
    rw [hJV_fin]
    ext x
    simp only [mem_iUnion, hs_seg]
  have hJE : J.E = ⋃ S₀ ∈ S_seg, (D_J S₀).E := by
    rw [hJE_fin]
    ext e
    simp only [mem_iUnion, hs_seg]
  obtain ⟨hOD₂, hcl₂, _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ₂
  have hZne : (Δ₂ \ subBd Δ₂).Nonempty := IsOpenDisc.nonempty hOD₂
  have hZconn : IsPreconnected (Δ₂ \ subBd Δ₂) := hOD₂.isPathConnected.isConnected.isPreconnected
  have hClaim1 : ∀ r ∈ J.R, (closure r ∩ (Δ₂ \ subBd Δ₂)).Nonempty → r ⊆ Δ₁ \ subBd Δ₁ :=
    fun r hr hinter => lemma_7_7_claim_1 hS hConn hθ hd hz hΔ₁ hΔ₂ hz_sub hΔ₂_sub₁
      hii hiii hC₁ hC₁s hbd₁ hC₂ hC₂s hbd₂ hdisj hSeg hLoc hArr hComp hJU hr hinter
  obtain ⟨C, Λ, hCJ, hC, hCU, hOpenΛ, hclΛ_sub, hclΛ_disc, _, hbd_clΛ, hdiffΛ, hZΛ, _⟩ :=
    theorem_5_2_full hS J hΔ₁ hZne hZconn hClaim1
  have hline : ∀ e ∈ C.E, ∀ S₀ ∈ S_seg, e ∈ (D_J S₀).E →
      ∃ a b : S, a ≠ b ∧ closure e ∩ (D_J S₀).V = {a, b} ∧ IsLineWithEnds (closure e) a b ∧
        (D_J S₀).V = α_pt '' S₀.Ω.bar := by
    exact proper_arrangement_boundary_edge_is_arc (S := S) hS (α := α) (β := β) (G := G) (H := H)
      (C₁ := C₁) (C₂ := C₂) (η := η) (θ := θ) (T := T) (d := d) (z := z) (Δ₁ := Δ₁) (Δ₂ := Δ₂)
      (S_seg := S_seg) (α_disc := α_disc) (α_pt := α_pt) hθ hd hz hΔ₁ hΔ₂ hz_sub hΔ₂_sub₁ hii hiii
      hC₁ hC₁s hbd₁ hC₂ hC₂s hbd₂ hSeg hLoc hArr hComp p_S hVJ_sub_bar D_J hDJ J hJU C Λ
      hOpenΛ hclΛ_sub hclΛ_disc hbd_clΛ hdiffΛ hZΛ
  have hpush_ind : ∀ (s : Finset (Set S)), (s : Set (Set S)) ⊆ C.E →
      ∃ Ψ : S ≃ₜ S,
        (∀ x ∈ Δ₂ ∪ (univ \ (Δ₁ \ subBd Δ₁)) ∪ J.V, Ψ x = x) ∧
        (∀ e ∈ C.E \ (s : Set (Set S)), ∀ x ∈ closure e, Ψ x = x) ∧
        (∀ e ∈ s, ∀ S₁ ∈ S_seg, Ψ '' (closure e) ∩ α_disc S₁ ⊆ α_pt '' S₁.Ω.bar) := by
    exact push_finite_boundary_edges (S := S) hS (α := α) (β := β) (G := G) (H := H) (C₁ := C₁)
      (C₂ := C₂) (η := η) (Δ₁ := Δ₁) (Δ₂ := Δ₂) (S_seg := S_seg) (α_disc := α_disc) (α_pt := α_pt)
      hΔ₁ hΔ₂ hC₁s hbd₁ hC₂s hbd₂ hSeg hArr hComp V_J D_J hDJ J hJV hJE C Λ hCJ hCU hdiffΛ hZΛ
      hline
  let s_all : Finset (Set S) := C.finite_edges.toFinset
  have hs_all : (s_all : Set (Set S)) ⊆ C.E := by
    intro e he
    exact (Finite.mem_toFinset _).mp he
  obtain ⟨Ψ, hΨ_fix, _, hΨ_pushed⟩ := hpush_ind s_all hs_all
  refine ⟨Ψ '' C.U, Ψ '' (closure Λ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isOArc_of_isCircuit hC).image Ψ.continuous.continuousOn
      Ψ.symm.continuous.continuousOn (fun x _ => Ψ.symm_apply_apply x)
  · rintro _ ⟨x, hx, rfl⟩
    by_contra hx_not₁
    have hΨx_out : Ψ x ∈ univ \ (Δ₁ \ subBd Δ₁) := ⟨mem_univ _, fun h => hx_not₁ h.1⟩
    have hΨΨx : Ψ (Ψ x) = Ψ x := hΨ_fix (Ψ x) (Or.inl (Or.inr hΨx_out))
    have hx_eq : Ψ x = x := Ψ.injective hΨΨx
    exact hx_not₁ (hx_eq.symm ▸ hCU hx)
  · rintro S₁ hS₁ _ ⟨⟨x, hxCU, rfl⟩, hyD₁⟩
    obtain ⟨e, heC, hx_cl⟩ := exists_edge_closure_of_mem_circuit_U hC hxCU
    have hes : e ∈ s_all := (Finite.mem_toFinset _).mpr heC
    exact hΨ_pushed e hes S₁ hS₁ ⟨⟨x, hx_cl, rfl⟩, hyD₁⟩
  · exact (hclΛ_disc.image Ψ.continuous.continuousOn
      Ψ.symm.continuous.continuousOn (fun x _ => Ψ.symm_apply_apply x)).1
  · rw [← subBd_eq_frontier', ← Ψ.image_frontier, subBd_eq_frontier', hbd_clΛ]
  · rintro _ ⟨x, hx, rfl⟩
    by_contra hx_not₁
    have hΨx_out : Ψ x ∈ univ \ (Δ₁ \ subBd Δ₁) := ⟨mem_univ _, fun h => hx_not₁ h.1⟩
    have hΨΨx : Ψ (Ψ x) = Ψ x := hΨ_fix (Ψ x) (Or.inl (Or.inr hΨx_out))
    have hx_eq : Ψ x = x := Ψ.injective hΨΨx
    exact hx_not₁ (hx_eq.symm ▸ hclΛ_sub hx)
  · have hΔ₂_sub_clΛ : Δ₂ ⊆ closure Λ :=
      hcl₂ ▸ isClosed_closure.closure_subset_iff.mpr (hZΛ.trans subset_closure)
    intro x hx
    exact ⟨x, hΔ₂_sub_clΛ hx, hΨ_fix x (Or.inl (Or.inl hx))⟩

end GraphMinor.GM14
