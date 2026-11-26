/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffTouch

/-!
# The height functions and the trees of a collar

Graph Minors VII, (5.9), page 235. The heights `f` say how far up each box the collapse starts, and
the ramps `g` say how the top of a box maps to the bottom. The trees are the unions of `N_i(C)` and
`Q_i`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

/-- The height over the top of a box: it is `1` at the points of `Z` on level `1`, and above that
elsewhere. -/
noncomputable def topHeight (Z : Set (ℝ × ℝ)) (m : ℝ) : ℝ := 1 + 1 / 2 * min 1 (infDist (m,
  (1 : ℝ)) Z)

/-- The ramp from `0` to `1` between `a` and `b`. -/
noncomputable def clampRamp (a b m : ℝ) : ℝ := max 0 (min 1 ((m - a) / (b - a)))

theorem topHeight_bounds (Z : Set (ℝ × ℝ)) (m : ℝ) : 1 ≤ topHeight Z m ∧ topHeight Z m ≤ 3 / 2 := by
  have h1 : 0 ≤ min 1 (infDist (m, (1 : ℝ)) Z) := le_min zero_le_one infDist_nonneg
  have h2 : min 1 (infDist (m, (1 : ℝ)) Z) ≤ 1 := min_le_left _ _
  constructor <;> simp only [topHeight] <;> linarith

theorem topHeight_le {Z : Set (ℝ × ℝ)} {m w : ℝ} (h : (m, w) ∈ Z) (hw : 1 ≤ w) : topHeight Z m
  ≤ 1 + (w - 1) / 2 := by
  have h1 : infDist (m, (1 : ℝ)) Z ≤ dist (m, (1 : ℝ)) (m, w) := infDist_le_dist_of_mem h
  have h2 : dist (m, (1 : ℝ)) (m, w) = w - 1 := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact max_eq_right (by linarith)
  have h3 := min_le_right 1 (infDist (m, (1 : ℝ)) Z)
  simp only [topHeight]
  linarith

theorem topHeight_eq_one {Z : Set (ℝ × ℝ)} (hc : IsClosed Z) (hne : Z.Nonempty) {m : ℝ}
  (h : topHeight Z m = 1) : (m, (1 : ℝ)) ∈ Z := by
  have h1 : min 1 (infDist (m, (1 : ℝ)) Z) = 0 := by
    simp only [topHeight] at h
    linarith
  have h2 : infDist (m, (1 : ℝ)) Z = 0 := by
    rcases min_choice 1 (infDist (m, (1 : ℝ)) Z) with h3 | h3
    · rw [h3] at h1
      exact absurd h1 one_ne_zero
    · rwa [h3] at h1
  exact (hc.mem_iff_infDist_zero hne).mpr h2

theorem isCollapseData_ramp {Z : Set (ℝ × ℝ)} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
  (h0 : ((0 : ℝ), (1 : ℝ)) ∈ Z) (h1 : ((1 : ℝ), (1 : ℝ)) ∈ Z) : IsCollapseData (clampRamp a b)
    (topHeight Z) := by
  have hd : 0 < b - a := by linarith
  have hone : ∀ {m : ℝ}, (m, (1 : ℝ)) ∈ Z → topHeight Z m = 1 := fun {m} hm => by
    have h2 : infDist (m, (1 : ℝ)) Z = 0 := infDist_zero_of_mem hm
    simp [topHeight, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun m _ => topHeight_bounds Z m, hone h0, hone h1⟩
  · have : Continuous (clampRamp a b) := by
      unfold clampRamp
      fun_prop (disch := exact hd.ne')
    exact this.continuousOn
  · have : Continuous (topHeight Z) := by
      unfold topHeight
      have h2 : Continuous fun m : ℝ => infDist (m, (1 : ℝ)) Z := (continuous_infDist_pt Z).comp
        (by fun_prop)
      fun_prop
    exact this.continuousOn
  · intro m _ m' _ hm
    have h2 : (m - a) / (b - a) ≤ (m' - a) / (b - a) := div_le_div_of_nonneg_right
      (by linarith) hd.le
    exact max_le_max le_rfl (min_le_min le_rfl h2)
  · have h2 : (0 - a) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    exact max_eq_left ((min_le_right _ _).trans h2)
  · have h2 : 1 ≤ (1 - a) / (b - a) := by
      rw [le_div_iff₀ hd]
      linarith
    simp [clampRamp, min_eq_left h2]

theorem clampRamp_low {a b m : ℝ} (hab : a < b) (h : m ≤ a) : clampRamp a b m = 0 := by
  have h2 : (m - a) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  exact max_eq_left ((min_le_right _ _).trans h2)

theorem clampRamp_high {a b m : ℝ} (hab : a < b) (h : b ≤ m) : clampRamp a b m = 1 := by
  have h2 : 1 ≤ (m - a) / (b - a) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  simp [clampRamp, min_eq_left h2]

theorem clampRamp_strict {a b m m' : ℝ} (hab : a < b) (he : clampRamp a b m = clampRamp a b m')
  (h0 : 0 < clampRamp a b m) (h1 : clampRamp a b m < 1) : m = m' := by
  have hd : b - a ≠ 0 := by
    have : 0 < b - a := by linarith
    exact this.ne'
  have hval : ∀ {n : ℝ}, 0 < clampRamp a b n → clampRamp a b n < 1 → clampRamp a b n = (n - a) /
    (b - a) := fun {n} h2 h3 => by
    unfold clampRamp at h2 h3 ⊢
    have h4 : 0 < min 1 ((n - a) / (b - a)) := by
      rcases max_choice 0 (min 1 ((n - a) / (b - a))) with h5 | h5
      · rw [h5] at h2
        exact absurd h2 (lt_irrefl _)
      · rwa [h5] at h2
    rw [max_eq_right h4.le] at h3 ⊢
    rcases min_choice 1 ((n - a) / (b - a)) with h5 | h5
    · rw [h5] at h3
      exact absurd h3 (lt_irrefl _)
    · exact h5
  have h2 := hval h0 h1
  have h3 := hval (he ▸ h0) (he ▸ h1)
  rw [h2, h3] at he
  have h4 := (div_left_inj₀ hd).mp he
  linarith

variable {S : Type u} [TopologicalSpace S]

/-- A path contains no `O`-arc. -/
theorem no_oArc_of_path [T2Space S] {P : Drawing S} {a b : S}
  (hP : P.IsPathBetween a b) {J : Set S} (hJ : IsOArc J) (hs : J ⊆ P.U) : False := by
  by_cases hab : a = b
  · subst hab
    obtain ⟨W, hW, hV, hE⟩ := hP
    have hW0 : W.support = [a] ∧ W.edges = [] := by
      cases W with
      | nil _ => exact ⟨rfl, rfl⟩
      | cons _ r => exact absurd r.end_mem_support (List.nodup_cons.mp hW).1
    have hsing : P.U ⊆ {a} := fun x hx => by
      by_cases hxV : x ∈ P.V
      · rw [hV, mem_ofPred_eq, hW0.1, List.mem_singleton] at hxV
        exact hxV
      · obtain ⟨e, he, -⟩ := P.exists_edge_of_mem hx hxV
        rw [hE, mem_ofPred_eq, hW0.2] at he
        simp at he
    exact (isOArc_infinite_any hJ) ((finite_singleton a).subset (hs.trans hsing))
  · obtain ⟨f, -, -⟩ := isLine_of_isPathBetween hP hab
    exact not_isOArc_of_subset_line ⟨f⟩ hJ hs

/-- Two paths that meet in just one vertex make a forest. -/
theorem isForest_of_two_paths [T2Space S] [ConnectedSpace S] {F A B : Drawing S} {a b c d y : S}
  (hA : A.IsPathBetween a b) (hB : B.IsPathBetween c d) (hAF : A.IsSubdrawing F) (hFU : F.U
    = A.U ∪ B.U) (hy : y ∈ A.V) (hyB : y ∈ B.U) (hmeet : A.U ∩ B.U ⊆ {y}) : IsGraphForest F.toGraph
      := by
  refine isForest_of_noOArc (H := F) fun X hX hsub => ?_
  have hpre : IsPreconnected (X \ {y}) := by
    by_cases hm : y ∈ X
    · obtain ⟨Cc, hCc, hCF, hCU⟩ := exists_circuit_of_oArc hX hsub
      rw [← hCU]
      exact isPreconnected_U_diff hCc (mem_V_of_subdrawing hCF (hCU ▸ hm) (hAF.1 hy))
    · rw [sdiff_singleton_eq_self hm]
      exact (isConnected_of_isOArc hX).isPreconnected
  have hdj : Disjoint (X \ {y}) (A.U ∩ B.U) := by
    rw [disjoint_left]
    intro z hz hz'
    exact hz.2 (hmeet hz')
  rcases GM12.subset_side A.isClosed_U B.isClosed_U hpre (fun z hz => hFU ▸ hsub hz.1) hdj with h1
    | h1
  · refine no_oArc_of_path hA hX fun z hz => ?_
    by_cases hzy : z = y
    · exact hzy ▸ A.V_subset_U hy
    · exact h1 ⟨hz, hzy⟩
  · refine no_oArc_of_path hB hX fun z hz => ?_
    by_cases hzy : z = y
    · exact hzy ▸ hyB
    · exact h1 ⟨hz, hzy⟩

/-- In a path, any two vertices are joined by a walk. -/
theorem exists_walk_of_isPathBetween {P : Drawing S} {a b : S} (hP : P.IsPathBetween a b) {y y' :
  S} (hy : y ∈ P.V) (hy' : y' ∈ P.V) : Nonempty (GraphWalk P.toGraph y y') := by
  obtain ⟨W, -, hV, -⟩ := hP
  rw [hV] at hy hy'
  obtain ⟨_, rfl, T₁, -⟩ := exists_last_in {y} W ⟨y, hy, rfl⟩
  obtain ⟨_, rfl, T₂, -⟩ := exists_last_in {y'} W ⟨y', hy', rfl⟩
  exact ⟨T₁.append T₂.reverse⟩

end GraphMinor.GM07
