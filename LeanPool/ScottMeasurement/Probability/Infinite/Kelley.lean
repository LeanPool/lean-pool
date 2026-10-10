/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.Probability.Infinite.HahnBanach
public import Mathlib.Analysis.Normed.Module.Dual

/-!
# A generalized Kelley cover

The countable cover below is the explicit Archimedean hypothesis used in the
reconstructed infinite theorem.  Each layer is a closed convex upper set over
the weak-comparison cone and is bounded away from zero.  Hahn--Banach supplies
one positive separator per nonempty layer.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures.Probability.Infinite

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LocallyConvexSpace ℝ E]

/-- Countable Kelley cover of strict-comparison vectors above a closed weak
comparison cone. -/
structure KelleyCover (C : ProperCone ℝ E) (S : Set E) where
  /-- Closed convex layers separating the strict comparisons from zero. -/
  layer : ℕ → Set E
  strictInCone : S ⊆ C
  covers : S ⊆ ⋃ n, layer n
  convex : ∀ n, Convex ℝ (layer n)
  closed : ∀ n, IsClosed (layer n)
  avoidsZero : ∀ n, (0 : E) ∉ layer n
  upper : ∀ n, ConeUpperSet C (layer n)

/-- Hahn--Banach produces a positive separator for every layer, with the zero
functional used harmlessly on empty layers. -/
theorem KelleyCover.exists_separator_family {C : ProperCone ℝ E} {S : Set E}
    (h : KelleyCover C S) :
    ∃ f : ℕ → StrongDual ℝ E,
      (∀ n c, c ∈ C → 0 ≤ f n c) ∧
      (∀ n x, x ∈ h.layer n → 0 < f n x) := by
  classical
  have hex : ∀ n, ∃ f : StrongDual ℝ E,
      (∀ c, c ∈ C → 0 ≤ f c) ∧
      (∀ x, x ∈ h.layer n → 0 < f x) := by
    intro n
    by_cases hne : (h.layer n).Nonempty
    · obtain ⟨f, hfC, hfK⟩ :=
        exists_positive_separator_of_coneUpper C hne
          (h.convex n) (h.closed n) (h.avoidsZero n) (h.upper n)
      exact ⟨f, hfC, hfK⟩
    · refine ⟨0, by simp, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  choose f hf using hex
  exact ⟨f, fun n c hc ↦ (hf n).1 c hc, fun n x hx ↦ (hf n).2 x hx⟩

/-- A summable positive combination of the layer separators is nonnegative on
the weak cone and strictly positive on every covered strict vector. -/
theorem KelleyCover.exists_combined_separator
    {C : ProperCone ℝ E} {S : Set E} (h : KelleyCover C S) :
    ∃ F : StrongDual ℝ E,
      (∀ c ∈ C, 0 ≤ F c) ∧ ∀ x ∈ S, 0 < F x := by
  classical
  obtain ⟨f, hfC, hfK⟩ := h.exists_separator_family
  let w : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n / (1 + ‖f n‖)
  let g : ℕ → StrongDual ℝ E := fun n ↦ w n • f n
  have hwpos : ∀ n, 0 < w n := by
    intro n
    exact div_pos (pow_pos (by norm_num) _) (by positivity)
  have hgnorm : ∀ n, ‖g n‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    have hb : 0 ≤ (1 / 2 : ℝ) ^ n := (pow_nonneg (by norm_num) _)
    have hd : 0 < 1 + ‖f n‖ := by positivity
    have hr : ‖f n‖ / (1 + ‖f n‖) ≤ 1 :=
      (div_le_one hd).2 (by linarith [norm_nonneg (f n)])
    change ‖w n • f n‖ ≤ (1 / 2 : ℝ) ^ n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hwpos n)]
    calc
      w n * ‖f n‖ =
          (1 / 2 : ℝ) ^ n * (‖f n‖ / (1 + ‖f n‖)) := by
            dsimp [w]
            ring
      _ ≤ (1 / 2 : ℝ) ^ n * 1 := mul_le_mul_of_nonneg_left hr hb
      _ = (1 / 2 : ℝ) ^ n := mul_one _
  have hgeom : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hnormsum : Summable (fun n ↦ ‖g n‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hgnorm hgeom
  have hgsum : Summable g := Summable.of_norm hnormsum
  let F : StrongDual ℝ E := ∑' n, g n
  refine ⟨F, ?_, ?_⟩
  · intro c hc
    have happly := ((ContinuousLinearMap.apply ℝ ℝ) c).map_tsum hgsum
    change F c = ∑' n, g n c at happly
    rw [show F c = ∑' n, g n c from happly]
    apply tsum_nonneg
    intro n
    change 0 ≤ w n * f n c
    exact mul_nonneg (hwpos n).le (hfC n c hc)
  · intro x hx
    rcases Set.mem_iUnion.mp (h.covers hx) with ⟨n, hxn⟩
    have heval : Summable (fun k ↦ g k x) := by
      have hm := hgsum.map ((ContinuousLinearMap.apply ℝ ℝ) x)
        ((ContinuousLinearMap.apply ℝ ℝ) x).continuous
      change Summable (fun k ↦ g k x) at hm
      exact hm
    have hterm : 0 < g n x := by
      change 0 < w n * f n x
      exact mul_pos (hwpos n) (hfK n x hxn)
    have hle : g n x ≤ ∑' k, g k x :=
      heval.le_tsum n (fun k _ ↦ by
        change 0 ≤ w k * f k x
        exact mul_nonneg (hwpos k).le (hfC k x (h.strictInCone hx)))
    have happly := ((ContinuousLinearMap.apply ℝ ℝ) x).map_tsum hgsum
    change F x = ∑' k, g k x at happly
    rw [show F x = ∑' k, g k x from happly]
    exact hterm.trans_le hle

end

end Scott1964.MeasurementStructures.Probability.Infinite
