/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.BallTopology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormTriangle

/-!
# The interior supremum bound for weakly harmonic `L^{3/2}` functions

This file proves the first display `eq:harm-sup` of `lem:harmonic-interior` in
`paper/ckn.tex`: for a function `h` that is weakly harmonic on the ball
`B_ρ(x₀)` and lies in `L^{3/2}(B_ρ(x₀))`,

  `‖h‖_{L^∞(B_{3ρ/4}(x₀))} ≤ C₁₇ ρ^{-2} ‖h‖_{L^{3/2}(B_ρ(x₀))}`,

with an absolute constant `C₁₇`.

The established interior displays `weak_harmonic_interior_displays` produce a
continuously differentiable representative of `h` on the half ball together
with a pointwise bound for that representative on the three-quarter ball.  The
essential supremum of `h` itself on the three-quarter ball is obtained here by
applying those displays at every centre `y ∈ B_{3ρ/4}(x₀)` on the ball
`B_{ρ/4}(y) ⊆ B_ρ(x₀)`, which identifies `h` with its representative almost
everywhere on `B_{ρ/8}(y)`, and by localizing the resulting null sets: a set
that is null in a neighbourhood of each of its points is null in a
second-countable space.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

noncomputable section

namespace CKN.Foundation.Heat

/-- The absolute constant `C₁₇` of `eq:harm-sup`. -/
@[expose]
def harmonicInteriorSupDisplayConstant : ℝ := 16 * harmonicInteriorDisplayConstant

theorem harmonicInteriorSupDisplayConstant_nonneg : 0 ≤ harmonicInteriorSupDisplayConstant := by
  rw [harmonicInteriorSupDisplayConstant]
  exact mul_nonneg (by norm_num) harmonicInteriorDisplayConstant_nonneg

/-- A smaller Euclidean ball around the same centre is contained in a larger one. -/
private theorem euclideanBall_subset_of_le {x : Vec3} {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) : euclideanBall x r ⊆ euclideanBall x R := by
  intro y hy
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
  exact lt_of_lt_of_le ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy) hrR

/-- The quarter ball around an interior centre stays inside the full ball. -/
private theorem quarter_ball_subset {x₀ y : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hy : y ∈ euclideanBall x₀ (3 * ρ / 4)) :
    euclideanBall y (ρ / 4) ⊆ euclideanBall x₀ ρ := by
  intro x hx
  have hxy : vecEuclideanNorm (x - y) < ρ / 4 :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  have hy₀ : vecEuclideanNorm (y - x₀) < 3 * ρ / 4 :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy
  have htri : vecEuclideanNorm (x - x₀) ≤
      vecEuclideanNorm (x - y) + vecEuclideanNorm (y - x₀) := by
    rw [show x - x₀ = (x - y) + (y - x₀) by abel]
    exact CKN.vecEuclideanNorm_add_le _ _
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hρ]
  linarith only [htri, hxy, hy₀]

/-- The `L^{3/2}` norm over a subball is at most the `L^{3/2}` norm over the ball. -/
private theorem lpNorm_mono_ball {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    {S : Set Vec3} (hS : S ⊆ euclideanBall x₀ ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ))) :
    lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict S) ≤
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) := by
  have hle : eLpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict S) ≤
      eLpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) :=
    eLpNorm_mono_measure h (Measure.restrict_mono_set volume hS)
  exact ENNReal.toReal_mono hmem.ne hle

/-- The local form of `eq:harm-sup`: around every centre of the three-quarter
ball the datum is bounded almost everywhere on a ball of radius `ρ/8` by the
constant of the display. -/
private theorem harmonic_local_ae_bound {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ ρ) h)
    {y : Vec3} (hy : y ∈ euclideanBall x₀ (3 * ρ / 4)) :
    ∀ᵐ x ∂volume.restrict (euclideanBall y (ρ / 8)),
      |h x| ≤ harmonicInteriorSupDisplayConstant * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
  have hρ4 : 0 < ρ / 4 := by positivity
  have hsub : euclideanBall y (ρ / 4) ⊆ euclideanBall x₀ ρ :=
    quarter_ball_subset hρ hy
  have hmem4 : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall y (ρ / 4))) :=
    hmem.mono_measure (Measure.restrict_mono_set volume hsub)
  have hweak4 : WeaklyHarmonicOn (euclideanBall y (ρ / 4)) h :=
    local_weak_harmonic hsub hweak
  obtain ⟨H, _hHdiff, hHae, hHvalue, _hHgrad, _hHplain, _hHosc⟩ :=
    weak_harmonic_interior_displays hρ4 hmem4 hweak4
  have hhalf : ρ / 4 / 2 = ρ / 8 := by ring
  rw [hhalf] at hHae
  have hcoef : harmonicInteriorDisplayConstant * ((ρ / 4) ^ 2)⁻¹ =
      harmonicInteriorSupDisplayConstant * (ρ ^ 2)⁻¹ := by
    rw [harmonicInteriorSupDisplayConstant]
    field_simp
    ring
  have hLmono :
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall y (ρ / 4))) ≤
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) :=
    lpNorm_mono_ball hsub hmem
  have hCnn : 0 ≤ harmonicInteriorSupDisplayConstant * (ρ ^ 2)⁻¹ := by
    have := harmonicInteriorSupDisplayConstant_nonneg
    positivity
  filter_upwards [hHae,
    self_mem_ae_restrict (CKN.measurableSet_euclideanBall y (ρ / 8))] with x hx hxmem
  have hx34 : x ∈ euclideanBall y (3 * (ρ / 4) / 4) := by
    refine euclideanBall_subset_of_le (by positivity) ?_ hxmem
    linarith only [hρ]
  have hbound := hHvalue x hx34
  rw [hx]
  calc |H x| ≤ harmonicInteriorDisplayConstant * ((ρ / 4) ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall y (ρ / 4))) := hbound
    _ = harmonicInteriorSupDisplayConstant * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall y (ρ / 4))) := by rw [hcoef]
    _ ≤ harmonicInteriorSupDisplayConstant * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) :=
        mul_le_mul_of_nonneg_left hLmono hCnn

/-- **The interior supremum bound `eq:harm-sup` of `lem:harmonic-interior`.**
There is an absolute constant `C₁₇` such that every weakly harmonic
`L^{3/2}` function on a ball satisfies
`‖h‖_{L^∞(B_{3ρ/4})} ≤ C₁₇ ρ^{-2} ‖h‖_{L^{3/2}(B_ρ)}`. -/
theorem weak_harmonic_interior_sup :
    ∃ C₁₇ : ℝ, ∀ (h : Vec3 → ℝ) (x₀ : Vec3) (ρ : ℝ), 0 < ρ →
      MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) →
      WeaklyHarmonicOn (euclideanBall x₀ ρ) h →
      eLpNorm h ⊤ (volume.restrict (euclideanBall x₀ (3 * ρ / 4))) ≤
        ENNReal.ofReal (C₁₇ * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ))) := by
  refine ⟨harmonicInteriorSupDisplayConstant, ?_⟩
  intro h x₀ ρ hρ hmem hweak
  set K : ℝ := harmonicInteriorSupDisplayConstant * (ρ ^ 2)⁻¹ *
    lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)) with hK
  set S : Set Vec3 :=
    {x | ¬ (x ∈ euclideanBall x₀ (3 * ρ / 4) → |h x| ≤ K)} with hS
  have hSnull : volume S = 0 := by
    refine measure_null_of_locally_null S ?_
    intro y hy
    have hy34 : y ∈ euclideanBall x₀ (3 * ρ / 4) := by
      by_contra hcon
      exact hy (fun hmem' => absurd hmem' hcon)
    refine ⟨S ∩ euclideanBall y (ρ / 8), ?_, ?_⟩
    · refine inter_mem_nhdsWithin S ?_
      refine (CKN.isOpen_euclideanBall y (ρ / 8)).mem_nhds ?_
      simp only [CKN.euclideanBall, Set.mem_ofPred_eq, CKN.euclideanSqDist_self]
      positivity
    · have hlocal := harmonic_local_ae_bound hρ hmem hweak hy34
      have hlocal' : ∀ᵐ x ∂volume,
          x ∈ euclideanBall y (ρ / 8) → |h x| ≤ K :=
        (ae_restrict_iff' (CKN.measurableSet_euclideanBall y (ρ / 8))).1 hlocal
      refine measure_mono_null ?_ (ae_iff.1 hlocal')
      intro x hx
      exact fun hcon => hx.1 (fun _ => hcon hx.2)
  have hae : ∀ᵐ x ∂volume.restrict (euclideanBall x₀ (3 * ρ / 4)), ‖h x‖ ≤ K := by
    refine (ae_restrict_iff' (CKN.measurableSet_euclideanBall x₀ (3 * ρ / 4))).2 ?_
    have : ∀ᵐ x ∂volume, x ∈ euclideanBall x₀ (3 * ρ / 4) → |h x| ≤ K :=
      ae_iff.2 hSnull
    filter_upwards [this] with x hx hxmem
    rw [Real.norm_eq_abs]
    exact hx hxmem
  have hmeas : AEStronglyMeasurable h
      (volume.restrict (euclideanBall x₀ (3 * ρ / 4))) := by
    refine hmem.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume ?_)
    exact euclideanBall_subset_of_le (by positivity) (by linarith only [hρ])
  rw [eLpNorm_exponent_top hmeas]
  exact eLpNormEssSup_le_of_ae_bound hae

end CKN.Foundation.Heat
