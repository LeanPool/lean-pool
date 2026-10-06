/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainSlice
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityCutoff

/-!
# Separated cutoffs and their spatial derivatives

For a separated field `c(t) g(x - x₀)` with `g` smooth, the spatial word
derivatives are `c(t) (∂^γ g)(x - x₀)`. For compactly supported `g` and
bounded `c` they are bounded independently of the center `x₀` and of `c`
beyond its bound. These are the cutoff bounds of `lem:local-heat-gain`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

theorem spatialPartial_separated {c : ℝ → ℝ} {g : Vec3 → ℝ} (hg : Differentiable ℝ g)
    (x₀ : Vec3) (j : Fin 3) (p : Vec3 × ℝ) :
    spatialPartial (fun q : Vec3 × ℝ => c q.2 * g (q.1 - x₀)) j p =
      c p.2 * spatialDeriv g j (p.1 - x₀) := by
  change (fderiv ℝ (fun y : Vec3 => c p.2 * g (y - x₀)) p.1) (basisVec j) = _
  have hd : DifferentiableAt ℝ (fun y : Vec3 => g (y - x₀)) p.1 :=
    (hg (p.1 - x₀)).comp p.1 ((differentiableAt_id).sub (differentiableAt_const _))
  rw [fderiv_const_mul hd]
  have h := vorticitySpatialDeriv_translate g x₀ p.1 j
  unfold spatialDeriv at h ⊢
  simp only [smul_apply, smul_eq_mul]
  rw [h]

/-- Spatial word derivatives of separated fields. -/
theorem spaceTimeWord_separated (γ : List (Fin 3)) (c : ℝ → ℝ) {g : Vec3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x₀ : Vec3) :
    spaceTimeWord γ (fun q : Vec3 × ℝ => c q.2 * g (q.1 - x₀)) =
      fun p => c p.2 * wordDeriv γ g (p.1 - x₀) := by
  induction γ generalizing g with
  | nil => rfl
  | cons j γ ih =>
      have h1 : (fun p : Vec3 × ℝ =>
          spatialPartial (fun q : Vec3 × ℝ => c q.2 * g (q.1 - x₀)) j p) =
          fun q : Vec3 × ℝ => c q.2 * spatialDeriv g j (q.1 - x₀) :=
        funext (spatialPartial_separated (hg.differentiable (by simp)) x₀ j)
      change spaceTimeWord γ (fun p : Vec3 × ℝ =>
        spatialPartial (fun q : Vec3 × ℝ => c q.2 * g (q.1 - x₀)) j p) = _
      rw [h1, ih (contDiff_spatialDeriv_smooth hg j)]
      rfl

theorem contDiff_wordDeriv_of_contDiff {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (γ : List (Fin 3)) : ContDiff ℝ (⊤ : ℕ∞) (wordDeriv γ g) := by
  induction γ generalizing g with
  | nil => exact hg
  | cons j γ ih => exact ih (contDiff_spatialDeriv_smooth hg j)

theorem hasCompactSupport_wordDeriv {g : Vec3 → ℝ} (hgc : HasCompactSupport g)
    (γ : List (Fin 3)) : HasCompactSupport (wordDeriv γ g) := by
  induction γ generalizing g with
  | nil => exact hgc
  | cons j γ ih => exact ih (hgc.fderiv_apply (𝕜 := ℝ) (basisVec j))

/-- Word derivatives of separated fields with compactly supported spatial
factor are bounded uniformly in the center and in the time factor. -/
theorem spaceTimeWord_separated_bound {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (Cc : ℝ) (γ : List (Fin 3)) :
    ∃ L : ℝ, ∀ (x₀ : Vec3) (c : ℝ → ℝ), (∀ t, |c t| ≤ Cc) →
      ∀ p, |spaceTimeWord γ (fun q : Vec3 × ℝ => c q.2 * g (q.1 - x₀)) p| ≤ L := by
  obtain ⟨M, hM⟩ := (contDiff_wordDeriv_of_contDiff hg γ).continuous.bounded_above_of_compact_support
    (hasCompactSupport_wordDeriv hgc γ)
  refine ⟨|Cc| * M, fun x₀ c hc p => ?_⟩
  rw [spaceTimeWord_separated γ c hg x₀, abs_mul]
  exact mul_le_mul ((hc p.2).trans (le_abs_self _)) (hM _) (abs_nonneg _) (abs_nonneg _)

end ESS
