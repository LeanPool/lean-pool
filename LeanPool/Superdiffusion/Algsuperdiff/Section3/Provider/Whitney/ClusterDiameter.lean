/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.ClusterLayerConstraint

/-!
# ClusterDiameter

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `l.bad.clusters.geometry`, clause (2): the diameter bound

```
diam(𝒩(𝒞)) < 4 · 3^{b(((n-1)∨1) + h_{(n-1)∨1})} · 3^{m-(((n-1)∨1) + h_{(n-1)∨1})}
```

As in clause (1) only the **deterministic geometric layer** is delivered: the
statements are conditional on avoidance of the bad-cluster diameter failure,
carried by the binder `havoid`, which is the manuscript's own conditioning on
`p.minimal.scale.separation` (see the module docstring of
`ClusterLayerConstraint`).  No probability estimate is used.

## The diameter carrier, and why this one

The printed `diam(𝒩(𝒞))` is the diameter of a *set of cubes*.  Two choices have
to be made explicit.

* **Closed or half-open cubes.**  `closedCubeCarrier 𝒥 = ⋃_{□ ∈ 𝒥}
  \overline{□}` takes the union of the **closed** cubes.  This is the exact
  analogue of the site-level choice already proved in
  `Provider/Percolation/ClusterTwo.lean`, where `closedLatDiam = latDiam + 1` —
  the diameter of the union of the closed cubes — was preferred to the
  centre-to-centre `latDiam` as "the larger and hence the faithful reading of
  the printed `diam`".  The same reasoning applies here: `cubeSet □ ⊆
  \overline{□}`, so `closedCubeCarrier` dominates the half-open union and the
  bound proved for it is the stronger statement.
* **`ℓ^∞` or Euclidean.**  `Metric.diam` on `Vec d = Fin d → ℝ` is the **sup**
  diameter, because the ambient metric on a `Pi` type is the sup metric.  No
  such conversion is performed here; every statement below is an `ℓ^∞`
  statement.
* **Non-vacuity.**  `Metric.diam` is `0` on an unbounded set, so a `diam` bound
  is only informative together with boundedness of the carrier.  The primitive
  content is in any case the *pointwise* estimate
  `norm_sub_lt_three_rpow_add_three_of_mem_whitneyNeighborhood`, which is what
  every consumer of a diameter actually uses, and from which both the `diam`
  bound `diam_closedCubeCarrier_whitneyNeighborhood_lt_four_mul_three_rpow` and
  the boundedness are read off.

## The accounting, and where the factor `4` comes from

Write `l` for the least Whitney layer that `𝒩(𝒞)` occupies, `j ≤ l` for the base
index of the lift, `L = j + h_j`, `s = m - L` and `A = 3^{bL}`.  Clause (1)
places every cube of `𝒩(𝒞)` in layer `l` or `l+1`, hence at depth `≥ L`, hence at
side `≤ 3^s`; so every cube in sight — the two endpoint cubes `□, □'` of
`𝒩(𝒞)` and the two cubes `Q, Q' ∈ 𝒞` they touch — has radius `≤ 3^s/2`.  The
core estimate `norm_cubeCenter_sub_lt_of_connected₂` of clause (1), run at the
common lift depth `L`, gives `‖c_Q - c_{Q'}‖ < A·3^s`, and the five-term triangle
inequality

```
‖x - y‖ ≤ ρ□ + (ρ□ + ρQ) + ‖c_Q - c_{Q'}‖ + (ρQ' + ρ□') + ρ□'
        < 3^s/2 + 3^s + A·3^s + 3^s + 3^s/2 = (A + 3)·3^s
```

The printed display is stated at the index `(n-1)∨1` for a layer `n` that
`𝒩(𝒞)` intersects.  Clause (1) gives `l ≤ n ≤ l+1` and `1 ≤ l`, hence
`(n-1)∨1 ≤ l` and `l ≤ ((n-1)∨1) + 2`, which is precisely the admissible range
of base indices `j` in the general statements.

## References

* ABK26, `l.bad.clusters.geometry`; `e.cluster.diameter.bound`;
  `e.neighborhood.def`; `e.diameter.deterministic`.
-/

namespace Algsuperdiff.Section3.Provider.Whitney

open HCPolySupport
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The closed carrier of a family of cubes -/

/-- **The carrier of `diam` in `e.cluster.diameter.bound`**: the union of the
**closed** cubes of a family, a subset of `Vec d = Fin d → ℝ`, whose ambient
metric is the sup metric. -/
def closedCubeCarrier (J : Set (TriadicCube d)) : Set (Vec d) :=
  ⋃ Q ∈ J, Metric.closedBall (cubeCenter Q) (HCPolySupport.cubeRadius Q)

theorem mem_closedCubeCarrier_iff {J : Set (TriadicCube d)} {x : Vec d} :
    x ∈ closedCubeCarrier J ↔
      ∃ Q ∈ J, x ∈ Metric.closedBall (cubeCenter Q) (HCPolySupport.cubeRadius Q) := by
  simp only [closedCubeCarrier, Set.mem_iUnion, exists_prop]

theorem closedBall_subset_closedCubeCarrier {J : Set (TriadicCube d)} {Q : TriadicCube d}
    (hQ : Q ∈ J) :
    Metric.closedBall (cubeCenter Q) (HCPolySupport.cubeRadius Q) ⊆ closedCubeCarrier J :=
  fun _ hx => mem_closedCubeCarrier_iff.mpr ⟨Q, hQ, hx⟩

/-! ## The corrected rounding -/

theorem three_rpow_add_three_mul_lt_four_mul {b : ℝ} (hb0 : 0 < b) {hs k₀ : ℕ}
    (hk₀ : 3 ≤ k₀) (m : ℤ) (j : ℕ) :
    ((3 : ℝ) ^ (b * ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℝ)) + 3) *
        (3 : ℝ) ^ (m - ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℤ)) <
      4 * (3 : ℝ) ^ (b * ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℝ)) *
        (3 : ℝ) ^ (m - ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℤ)) := by
  have hdepth : 3 ≤ j + whitneyScaleSeq b hs k₀ j := by
    have := add_le_whitneyScaleSeq b hs k₀ j
    omega
  have hexp : 0 < b * ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℝ) := by
    have h3 : (3 : ℝ) ≤ ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℝ) := by exact_mod_cast hdepth
    nlinarith [hb0, h3]
  have hA : 1 < (3 : ℝ) ^ (b * ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℝ)) :=
    (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, hexp⟩)
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (m - ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℤ)) :=
    zpow_pos (by norm_num) _
  have hmul := mul_lt_mul_of_pos_right hA hpos
  rw [one_mul] at hmul
  linarith [hmul]

/-! ## The lift chain at a common base index -/

section Core

variable {M : ABKModel d} {m : ℤ} {b : ℝ} {hs k₀ : ℕ} {omega : CutoffSample d}

/-- The lift carried along the chain relation of the component, at an arbitrary
admissible base index `j`: every cube of the component has a lift at depth `j +
h_j` whose site is 2-connected to the lift of the base cube `Q₀`.

This is the clause-(1) core induction with its layer half removed — the layer
window is supplied here by the hypothesis `hwin`, which clause (1) itself
provides at every admissible `j`. -/
private theorem core_lift_connected₂ (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q)
    {Q₀ : TriadicCube d} (hQ₀ : Q₀ ∈ S) {j : ℕ}
    (hwin : ∀ V ∈ badComponent S Q₀, ∀ q : ℕ,
      V ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) q → j ≤ q ∧ q ≤ j + 3)
    {A₀ : TriadicCube d}
    (hA₀ : IsWhitneyLift m (j + whitneyScaleSeq b hs k₀ j) Q₀ A₀) :
    ∀ V : TriadicCube d,
      Relation.ReflTransGen (fun X Y => X ∈ S ∧ Y ∈ S ∧ CubeTouch X Y) Q₀ V →
      ∃ A, IsWhitneyLift m (j + whitneyScaleSeq b hs k₀ j) V A ∧
        Percolation.Connected₂
          (Percolation.badSiteFinset M m (j + whitneyScaleSeq b hs k₀ j) omega)
          A₀.index A.index := by
  classical
  set hn := whitneyScaleSeq b hs k₀ with hhn
  set L : ℕ := j + hn j with hL
  have hmono : Monotone hn := by
    rw [hhn]; exact whitneyScaleSeq_mono (by linarith) (by linarith) hs k₀
  have hdepth10 : ∀ r' n' : ℕ, r' ≤ n' → n' ≤ r' + 3 →
      (n' + hn n') - (r' + hn r') < 10 := by
    rw [hhn]
    intro r' n' h1 h2
    exact whitneyDepth_sub_lt_ten hb0 hb hs k₀ h1 h2
  have hA₀site : A₀.index ∈ Percolation.badSiteFinset M m L omega :=
    index_mem_badSiteFinset_of_isWhitneyLift hA₀ (hSbad Q₀ hQ₀)
  intro V hV
  induction hV with
  | refl => exact ⟨A₀, hA₀, Percolation.Connected₂.refl hA₀site⟩
  | @tail V' V hchain hstep ih =>
      obtain ⟨A', hA'lift, hA'conn⟩ := ih
      obtain ⟨hV'S, hVS, htouch⟩ := hstep
      have hVC : V ∈ badComponent S Q₀ :=
        ⟨hVS, Relation.ReflTransGen.tail hchain ⟨hV'S, hVS, htouch⟩⟩
      obtain ⟨nV, hnV⟩ := hSsub hVS
      obtain ⟨hlo, hhi⟩ := hwin V hVC nV hnV
      have hdepthle : L ≤ nV + hn nV := by
        have := hmono hlo
        omega
      have hgap : nV + hn nV - L < 10 := by
        have := hdepth10 j nV hlo hhi
        omega
      obtain ⟨A, hAlift⟩ := exists_isWhitneyLift hnV hdepthle hgap
      have hAsite : A.index ∈ Percolation.badSiteFinset M m L omega :=
        index_mem_badSiteFinset_of_isWhitneyLift hAlift (hSbad V hVS)
      have hadj : Percolation.latDist A'.index A.index ≤ 1 :=
        latDist_index_le_one_of_cubeTouch hA'lift hAlift htouch
      have hconn : Percolation.Connected₂ (Percolation.badSiteFinset M m L omega)
          A₀.index A.index := by
        refine hA'conn.trans ⟨1, fun i => if i = 0 then A'.index else A.index, by simp,
          by simp, ?_, ?_⟩
        · intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          simpa using le_trans hadj (by omega : (1 : ℕ) ≤ 2)
        · intro i _
          by_cases hi : i = 0
          · simpa [hi] using hA'conn.mem_right
          · simpa [hi] using hAsite
      exact ⟨A, hAlift, hconn⟩

/-- The first inequality at an arbitrary admissible base index `j`: the centres of
two cubes of the component are less than `3^{bL}·3^{m-L}` apart, `L = j + h_j`.
This is `norm_cubeCenter_sub_lt_of_connected₂` of clause (1) fed by the lift
chain above. -/
private theorem norm_cubeCenter_sub_lt_of_mem_badComponent (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q)
    {Q₀ : TriadicCube d} (hQ₀ : Q₀ ∈ S) {j : ℕ}
    (hwin : ∀ V ∈ badComponent S Q₀, ∀ q : ℕ,
      V ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) q → j ≤ q ∧ q ≤ j + 3)
    {A₀ : TriadicCube d}
    (hA₀ : IsWhitneyLift m (j + whitneyScaleSeq b hs k₀ j) Q₀ A₀)
    {U W : TriadicCube d} (hU : U ∈ badComponent S Q₀) (hW : W ∈ badComponent S Q₀) :
    ‖cubeCenter U - cubeCenter W‖ <
      (3 : ℝ) ^ (b * ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℝ)) *
        (3 : ℝ) ^ (m - ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℤ)) := by
  have hsL : hs ≤ j + whitneyScaleSeq b hs k₀ j := by
    have := hsep_le_whitneyScaleSeq b hs k₀ j
    omega
  have hA₀site : A₀.index ∈
      Percolation.badSiteFinset M m (j + whitneyScaleSeq b hs k₀ j) omega :=
    index_mem_badSiteFinset_of_isWhitneyLift hA₀ (hSbad Q₀ hQ₀)
  have hdiam := havoid (j + whitneyScaleSeq b hs k₀ j) hsL A₀.index
    (index_mem_cubeFinset_of_mem_descendantsAtDepth hA₀.1)
  have hchain := core_lift_connected₂ hb0 hb hSsub hSbad hQ₀ hwin hA₀
  obtain ⟨AU, hAUlift, hAUconn⟩ := hchain U hU.2
  obtain ⟨AW, hAWlift, hAWconn⟩ := hchain W hW.2
  exact norm_cubeCenter_sub_lt_of_connected₂ hAUlift hAWlift hA₀site hAUconn hAWconn hdiam

end Core

/-! ## The headline estimates -/

/-- **`e.cluster.diameter.bound`, the sharp pointwise form.**  On avoidance of
the bad-cluster diameter failure, any two points of the closed cubes of the
closure-touching neighborhood of a connected component of an abstract bad family
are less than `(3^{bL} + 3)·3^{m-L}` apart in the `ℓ^∞` sense, where
`L = j + h_j` for any base index `j` inside the admissible window
`j ≤ n_min(𝒩(𝒞)) ≤ j + 2`. -/
theorem norm_sub_lt_three_rpow_add_three_of_mem_whitneyNeighborhood {M : ABKModel d}
    {m : ℤ} {b : ℝ} {hs k₀ : ℕ} {omega : CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q)
    {Q₀ : TriadicCube d} (hQ₀ : Q₀ ∈ S) {j : ℕ}
    (hjl : j ≤ leastWhitneyLayer m (whitneyScaleSeq b hs k₀)
      (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀)))
    (hlj : leastWhitneyLayer m (whitneyScaleSeq b hs k₀)
      (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀)) ≤ j + 2)
    {U W : TriadicCube d}
    (hU : U ∈ whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀))
    (hW : W ∈ whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀))
    {x y : Vec d}
    (hx : x ∈ Metric.closedBall (cubeCenter U) (HCPolySupport.cubeRadius U))
    (hy : y ∈ Metric.closedBall (cubeCenter W) (HCPolySupport.cubeRadius W)) :
    ‖x - y‖ <
      ((3 : ℝ) ^ (b * ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℝ)) + 3) *
        (3 : ℝ) ^ (m - ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℤ)) := by
  classical
  -- clause (1): the neighborhood occupies its least layer and its successor
  have hlayer := (whitneyNeighborhood_finite_and_mem_leastLayer_or_succ hb0 hb hk₀ havoid
    hSsub hSbad hQ₀).2
  set hn := whitneyScaleSeq b hs k₀ with hhn
  set C := badComponent S Q₀ with hC
  set N := whitneyNeighborhood m hn C with hN
  set l := leastWhitneyLayer m hn N with hl
  set L : ℕ := j + hn j with hL
  have hmono : Monotone hn := by
    rw [hhn]; exact whitneyScaleSeq_mono (by linarith) (by linarith) hs k₀
  have hdepth10 : ∀ r' n' : ℕ, r' ≤ n' → n' ≤ r' + 3 →
      (n' + hn n') - (r' + hn r') < 10 := by
    rw [hhn]
    intro r' n' h1 h2
    exact whitneyDepth_sub_lt_ten hb0 hb hs k₀ h1 h2
  have hCsub : C ⊆ whitneyPartition m hn := fun Q hQ => hSsub hQ.1
  have hCN : C ⊆ N := subset_whitneyNeighborhood hCsub
  have hNwin : ∀ R ∈ N, ∀ q : ℕ, R ∈ whitneyLayer m hn q → l ≤ q ∧ q ≤ l + 1 := by
    intro R hR q hRq
    rcases hlayer R hR with h | h
    · have := whitneyLayer_index_unique hmono hRq h
      omega
    · have := whitneyLayer_index_unique hmono hRq h
      omega
  have hwin : ∀ V ∈ C, ∀ q : ℕ, V ∈ whitneyLayer m hn q → j ≤ q ∧ q ≤ j + 3 := by
    intro V hV q hVq
    obtain ⟨h1, h2⟩ := hNwin V (hCN hV) q hVq
    omega
  -- every cube of the neighborhood is at least as deep as the lift scale
  have hrad : ∀ {R : TriadicCube d}, R ∈ N →
      HCPolySupport.cubeRadius R ≤ (3 : ℝ) ^ (m - (L : ℤ)) / 2 := by
    intro R hR
    obtain ⟨q, hRq⟩ := (whitneyNeighborhood_subset m hn C) hR
    obtain ⟨h1, -⟩ := hNwin R hR q hRq
    have hmm := hmono (le_trans hjl h1)
    have hRs := scale_eq_of_mem_whitneyLayer hRq
    have hle : (3 : ℝ) ^ R.scale ≤ (3 : ℝ) ^ (m - (L : ℤ)) := by
      refine zpow_le_zpow_right₀ (by norm_num) ?_
      rw [hRs]
      omega
    rw [cubeRadius_eq_zpow_div_two]
    linarith
  -- the base lift of `Q₀`
  have hQ₀C : Q₀ ∈ C := self_mem_badComponent hQ₀
  obtain ⟨q₀, hq₀⟩ := hCsub hQ₀C
  obtain ⟨hq₀lo, hq₀hi⟩ := hwin Q₀ hQ₀C q₀ hq₀
  have hdepthle : L ≤ q₀ + hn q₀ := by
    have := hmono hq₀lo
    omega
  have hgap : q₀ + hn q₀ - L < 10 := by
    have := hdepth10 j q₀ hq₀lo hq₀hi
    omega
  obtain ⟨A₀, hA₀⟩ := exists_isWhitneyLift hq₀ hdepthle hgap
  -- the two core cubes touched by the endpoints
  obtain ⟨QU, hQU, hQUt⟩ := hU.2
  obtain ⟨QW, hQW, hQWt⟩ := hW.2
  have hcore := norm_cubeCenter_sub_lt_of_mem_badComponent hb0 hb havoid hSsub hSbad hQ₀
    hwin hA₀ hQU hQW
  -- the five-term triangle inequality
  have htri : ‖x - y‖ ≤ ‖x - cubeCenter U‖ + ‖cubeCenter U - cubeCenter QU‖ +
      ‖cubeCenter QU - cubeCenter QW‖ + ‖cubeCenter QW - cubeCenter W‖ +
      ‖cubeCenter W - y‖ := by
    have a1 : ‖x - y‖ ≤ ‖x - cubeCenter U‖ + ‖cubeCenter U - y‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have a2 : ‖cubeCenter U - y‖ ≤
        ‖cubeCenter U - cubeCenter QU‖ + ‖cubeCenter QU - y‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have a3 : ‖cubeCenter QU - y‖ ≤
        ‖cubeCenter QU - cubeCenter QW‖ + ‖cubeCenter QW - y‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have a4 : ‖cubeCenter QW - y‖ ≤
        ‖cubeCenter QW - cubeCenter W‖ + ‖cubeCenter W - y‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    linarith
  have hxU : ‖x - cubeCenter U‖ ≤ HCPolySupport.cubeRadius U := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    exact hx
  have hyW : ‖cubeCenter W - y‖ ≤ HCPolySupport.cubeRadius W := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    rw [← norm_neg, neg_sub]
    exact hy
  have htU := norm_cubeCenter_sub_le_of_cubeTouch hQUt
  have htW := norm_cubeCenter_sub_le_of_cubeTouch hQWt.symm
  have hradU := hrad hU
  have hradW := hrad hW
  have hradQU := hrad (hCN hQU)
  have hradQW := hrad (hCN hQW)
  linarith [htri, hxU, hyW, htU, htW, hcore, hradU, hradW, hradQU, hradQW]

theorem diam_closedCubeCarrier_whitneyNeighborhood_lt_four_mul_three_rpow
    {M : ABKModel d} {m : ℤ} {b : ℝ} {hs k₀ : ℕ} {omega : CutoffSample d} (hb0 : 0 < b)
    (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q)
    {Q₀ : TriadicCube d} (hQ₀ : Q₀ ∈ S) {j : ℕ}
    (hjl : j ≤ leastWhitneyLayer m (whitneyScaleSeq b hs k₀)
      (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀)))
    (hlj : leastWhitneyLayer m (whitneyScaleSeq b hs k₀)
      (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀)) ≤ j + 2) :
    Metric.diam (closedCubeCarrier
        (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀))) <
      4 * (3 : ℝ) ^ (b * ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℝ)) *
        (3 : ℝ) ^ (m - ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℤ)) := by
  refine lt_of_le_of_lt (Metric.diam_le_of_forall_dist_le ?_ ?_)
    (three_rpow_add_three_mul_lt_four_mul hb0 hk₀ m j)
  · have hA : (0 : ℝ) ≤ (3 : ℝ) ^ (b * ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℝ)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (m - ((j + whitneyScaleSeq b hs k₀ j : ℕ) : ℤ)) :=
      zpow_pos (by norm_num) _
    positivity
  · intro p hp q hq
    obtain ⟨U, hU, hpU⟩ := mem_closedCubeCarrier_iff.mp hp
    obtain ⟨W, hW, hqW⟩ := mem_closedCubeCarrier_iff.mp hq
    rw [dist_eq_norm]
    exact (norm_sub_lt_three_rpow_add_three_of_mem_whitneyNeighborhood hb0 hb hk₀ havoid
      hSsub hSbad hQ₀ hjl hlj hU hW hpU hqW).le

/-! ## The printed display -/

/-- ```
diam(𝒩(𝒞)) < 4 · 3^{b(((n-1)∨1)+h_{(n-1)∨1})} · 3^{m-(((n-1)∨1)+h_{(n-1)∨1})} .
```

The manuscript's own justification of the index shift — "`n_min ≥ (n-1)∨1`
whenever `𝒩(𝒞)` intersects layer `n`" — is here the pair `(n-1)∨1 ≤
n_min(𝒩(𝒞))` and `n_min(𝒩(𝒞)) ≤ ((n-1)∨1) + 2`, both read off the proved clause
(1). -/
theorem diam_closedCubeCarrier_whitneyNeighborhood_lt_of_intersectsLayer {M : ABKModel d}
    {m : ℤ} {b : ℝ} {hs k₀ : ℕ} {omega : CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q)
    {Q₀ : TriadicCube d} (hQ₀ : Q₀ ∈ S) {n : ℕ}
    (hmeet : IntersectsLayer m (whitneyScaleSeq b hs k₀)
      (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀)) n) :
    Metric.diam (closedCubeCarrier
        (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀))) <
      4 * (3 : ℝ) ^ (b * ((max (n - 1) 1 +
              whitneyScaleSeq b hs k₀ (max (n - 1) 1) : ℕ) : ℝ)) *
        (3 : ℝ) ^ (m - ((max (n - 1) 1 +
              whitneyScaleSeq b hs k₀ (max (n - 1) 1) : ℕ) : ℤ)) := by
  classical
  have hCsub : badComponent S Q₀ ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀) :=
    fun Q hQ => hSsub hQ.1
  have hQ₀N : Q₀ ∈ whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀) :=
    subset_whitneyNeighborhood hCsub (self_mem_badComponent hQ₀)
  have hNsub : whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀) ⊆
      whitneyPartition m (whitneyScaleSeq b hs k₀) :=
    whitneyNeighborhood_subset m (whitneyScaleSeq b hs k₀) (badComponent S Q₀)
  obtain ⟨R₀, hR₀N, hR₀lay⟩ := exists_mem_leastWhitneyLayer ⟨Q₀, hQ₀N⟩ hNsub
  have hl1 : 1 ≤ leastWhitneyLayer m (whitneyScaleSeq b hs k₀)
      (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀)) :=
    one_le_of_mem_whitneyLayer hR₀lay
  obtain ⟨R, hRN, hRn⟩ := intersectsLayer_iff.mp hmeet
  have hn1 : 1 ≤ n := one_le_of_mem_whitneyLayer hRn
  have hlow : leastWhitneyLayer m (whitneyScaleSeq b hs k₀)
      (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀)) ≤ n :=
    leastWhitneyLayer_le_of_mem hRN hRn
  have hcl := whitneyNeighborhood_layer_index_close hb0 hb hk₀ havoid hSsub hSbad hQ₀
    hRN hR₀N hRn hR₀lay
  exact diam_closedCubeCarrier_whitneyNeighborhood_lt_four_mul_three_rpow hb0 hb hk₀
    havoid hSsub hSbad hQ₀ (by omega) (by omega)

end

end Algsuperdiff.Section3.Provider.Whitney
