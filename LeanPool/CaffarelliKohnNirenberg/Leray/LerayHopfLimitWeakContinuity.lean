/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Extending weak continuity from a dense family of tests

This is the density step in the weak-continuity argument for
`prop:leray-hopf-limit`.
-/

public section

open Filter Set
open scoped InnerProductSpace Topology



namespace CKN.Leray

/-- A uniform norm bound extends continuity of Hilbert pairings from a dense
family of tests to every test. -/
theorem continuousOn_inner_of_dense_tests
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T M : ℝ} (hM : 0 ≤ M) (v : ℝ → E) (D : Set E)
    (hD : Dense D)
    (hbound : ∀ t ∈ Icc 0 T, ‖v t‖ ≤ M)
    (hcont : ∀ w ∈ D,
      ContinuousOn (fun t => ⟪v t, w⟫_ℝ) (Icc 0 T)) :
    ∀ w : E, ContinuousOn (fun t => ⟪v t, w⟫_ℝ) (Icc 0 T) := by
  intro w t ht
  change Tendsto (fun s => ⟪v s, w⟫_ℝ)
    (nhdsWithin t (Icc 0 T)) (nhds (⟪v t, w⟫_ℝ))
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ : ℝ := ε / (8 * (M + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨d, hdD, hwd⟩ := hD.exists_dist_lt w hδ
  have hsmall : M * dist w d < ε / 8 := by
    calc
      M * dist w d ≤ (M + 1) * dist w d := by
        exact mul_le_mul_of_nonneg_right (by linarith only [hM]) (dist_nonneg)
      _ < (M + 1) * δ :=
        mul_lt_mul_of_pos_left hwd (by linarith only [hM])
      _ = ε / 8 := by
        dsimp [δ]
        field_simp
  have herr (s : ℝ) (hs : s ∈ Icc 0 T) :
      dist ⟪v s, w⟫_ℝ ⟪v s, d⟫_ℝ ≤ M * dist w d := by
    calc
      dist ⟪v s, w⟫_ℝ ⟪v s, d⟫_ℝ = |⟪v s, w - d⟫_ℝ| := by
        rw [dist_eq_norm, ← inner_sub_right, Real.norm_eq_abs]
      _ ≤ ‖v s‖ * ‖w - d‖ := abs_real_inner_le_norm _ _
      _ ≤ M * dist w d := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_right (hbound s hs) (norm_nonneg _)
  have hnear : ∀ᶠ s in 𝓝[ Icc 0 T ] t,
      dist ⟪v s, d⟫_ℝ ⟪v t, d⟫_ℝ < ε / 2 := by
    have hc := hcont d hdD t ht
    exact hc.eventually (Metric.ball_mem_nhds _ (by linarith only [hε]))
  filter_upwards [self_mem_nhdsWithin, hnear] with s hs hmid
  have hsIcc : s ∈ Icc 0 T := hs
  have hleft : dist ⟪v s, w⟫_ℝ ⟪v s, d⟫_ℝ < ε / 8 :=
    (herr s hsIcc).trans_lt hsmall
  have hright : dist ⟪v t, d⟫_ℝ ⟪v t, w⟫_ℝ < ε / 8 := by
    simpa only [dist_comm] using (herr t ht).trans_lt hsmall
  calc
    dist ⟪v s, w⟫_ℝ ⟪v t, w⟫_ℝ ≤
        dist ⟪v s, w⟫_ℝ ⟪v s, d⟫_ℝ +
          dist ⟪v s, d⟫_ℝ ⟪v t, w⟫_ℝ := dist_triangle _ _ _
    _ ≤ dist ⟪v s, w⟫_ℝ ⟪v s, d⟫_ℝ +
          (dist ⟪v s, d⟫_ℝ ⟪v t, d⟫_ℝ +
            dist ⟪v t, d⟫_ℝ ⟪v t, w⟫_ℝ) := by
      calc
        dist ⟪v s, w⟫_ℝ ⟪v s, d⟫_ℝ +
            dist ⟪v s, d⟫_ℝ ⟪v t, w⟫_ℝ =
            dist ⟪v s, d⟫_ℝ ⟪v t, w⟫_ℝ +
              dist ⟪v s, w⟫_ℝ ⟪v s, d⟫_ℝ := add_comm _ _
        _ ≤ dist ⟪v s, d⟫_ℝ ⟪v t, d⟫_ℝ +
              dist ⟪v t, d⟫_ℝ ⟪v t, w⟫_ℝ +
                dist ⟪v s, w⟫_ℝ ⟪v s, d⟫_ℝ :=
          add_le_add_left
            (dist_triangle (⟪v s, d⟫_ℝ) (⟪v t, d⟫_ℝ) (⟪v t, w⟫_ℝ)) _
        _ = dist ⟪v s, w⟫_ℝ ⟪v s, d⟫_ℝ +
              (dist ⟪v s, d⟫_ℝ ⟪v t, d⟫_ℝ +
                dist ⟪v t, d⟫_ℝ ⟪v t, w⟫_ℝ) := by ring
    _ < ε / 8 + (ε / 2 + ε / 8) := add_lt_add hleft (add_lt_add hmid hright)
    _ < ε := by nlinarith only [hε]

end CKN.Leray
