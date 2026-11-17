/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Bases

/-!
# An almost-everywhere bound on `⟪f t, f t'⟫` bounds `‖f t‖²` almost everywhere

Let `m` be an s-finite measure on `T` and `f : T → H` a map, not assumed measurable, into a
separable real inner product space. If `⟪f t, f t'⟫ ≤ M` for almost every `(t, t')` in `T × T`,
then `‖f t‖² ≤ M` for almost every `t`, although the diagonal of `T × T` may be null. The proof is
a covering argument: a piece `f⁻¹(B(d, δ))` of the set where `‖f t‖² ≥ M + η`, with `4 δ² ≤ η`,
whose square lies in the exceptional set, is null.

## Main statements

* `MeasureTheory.measure_eq_zero_of_forall_lt_inner`: a set on which every pair satisfies
  `M < ⟪f t, f t'⟫` is null.
* `lt_real_inner_of_dist_lt`: if `‖u‖², ‖v‖² ≥ M + η` and `u, v` lie in a ball of radius `δ`
  with `4 δ² ≤ η`, then `M < ⟪u, v⟫`.
* `MeasureTheory.ae_norm_sq_le_of_ae_inner_le`, `MeasureTheory.ae_norm_sq_le_of_ae_abs_inner_le`:
  the bound on the diagonal.
-/

public section

open MeasureTheory TopologicalSpace

namespace MeasureTheory

variable {T H : Type*} [MeasurableSpace T] {m : Measure T}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A set on which every pair satisfies `M < ⟪f t, f t'⟫` is null, when the bound
`⟪f t, f t'⟫ ≤ M` holds almost everywhere on `T × T`. No measurability is required. -/
theorem measure_eq_zero_of_forall_lt_inner [SFinite m] {f : T → H} {M : ℝ}
    (h : ∀ᵐ p ∂(m.prod m), inner ℝ (f p.1) (f p.2) ≤ M) {A : Set T}
    (hA : ∀ t ∈ A, ∀ t' ∈ A, M < inner ℝ (f t) (f t')) : m A = 0 := by
  have h0 : m.prod m (A ×ˢ A) = 0 := by
    refine measure_mono_null (fun p hp => ?_) (ae_iff.mp h)
    exact not_le.mpr (hA p.1 hp.1 p.2 hp.2)
  rw [Measure.prod_prod] at h0
  exact mul_self_eq_zero.mp h0

/-- Two vectors of squared norm at least `M + η` in a common ball of radius `δ`, with
`4 δ² ≤ η`, have inner product greater than `M`. -/
theorem _root_.lt_real_inner_of_dist_lt {u v d : H} {M η δ : ℝ} (hη : 0 < η) (hδ : 4 * δ ^ 2 ≤ η)
    (hu : M + η ≤ ‖u‖ ^ 2) (hv : M + η ≤ ‖v‖ ^ 2) (hud : dist u d < δ) (hvd : dist v d < δ) :
    M < inner ℝ u v := by
  have hsub : ‖u - v‖ < 2 * δ := by
    rw [← dist_eq_norm]
    calc dist u v ≤ dist u d + dist v d := dist_triangle_right u v d
      _ < 2 * δ := by linarith
  have hsq : ‖u - v‖ ^ 2 < 4 * δ ^ 2 := by
    nlinarith [norm_nonneg (u - v)]
  have := norm_sub_sq_real u v
  nlinarith

/-- For `m` s-finite and `f` with values in a separable real inner product
space, an almost-everywhere bound `⟪f t, f t'⟫ ≤ M` on `T × T` gives `‖f t‖² ≤ M` for almost
every `t`. -/
theorem ae_norm_sq_le_of_ae_inner_le [SFinite m] [SeparableSpace H] {f : T → H} {M : ℝ}
    (h : ∀ᵐ p ∂(m.prod m), inner ℝ (f p.1) (f p.2) ≤ M) : ∀ᵐ t ∂m, ‖f t‖ ^ 2 ≤ M := by
  set u : ℕ → H := denseSeq H
  set A : ℕ → ℕ → Set T := fun n k =>
    {t | M + 1 / ((n : ℝ) + 1) ≤ ‖f t‖ ^ 2 ∧ dist (f t) (u k) < 1 / (2 * ((n : ℝ) + 1))}
  have hA : ∀ n k, m (A n k) = 0 := by
    intro n k
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine measure_eq_zero_of_forall_lt_inner h fun t ht t' ht' => ?_
    refine lt_real_inner_of_dist_lt (one_div_pos.mpr hn) ?_ ht.1 ht'.1 ht.2 ht'.2
    rw [div_pow, mul_pow]
    rw [one_pow, mul_one_div, div_le_div_iff₀ (by positivity) hn]
    nlinarith
  have hcover : {t | ¬ ‖f t‖ ^ 2 ≤ M} ⊆ ⋃ n, ⋃ k, A n k := by
    intro t ht
    have ht : 0 < ‖f t‖ ^ 2 - M := by have := not_le.mp ht; linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
    have hδ : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp (denseRange_denseSeq H) (f t) _ hδ
    simp only [Set.mem_iUnion]
    exact ⟨n, k, by linarith, hk⟩
  rw [ae_iff]
  exact measure_mono_null hcover (measure_iUnion_null fun n => measure_iUnion_null (hA n))

/-- The same with the hypothesis `|⟪f t, f t'⟫| ≤ M` almost everywhere on `T × T`. -/
theorem ae_norm_sq_le_of_ae_abs_inner_le [SFinite m] [SeparableSpace H] {f : T → H} {M : ℝ}
    (h : ∀ᵐ p ∂(m.prod m), |inner ℝ (f p.1) (f p.2)| ≤ M) : ∀ᵐ t ∂m, ‖f t‖ ^ 2 ≤ M :=
  ae_norm_sq_le_of_ae_inner_le (h.mono fun _ hp => (le_abs_self _).trans hp)

end MeasureTheory
