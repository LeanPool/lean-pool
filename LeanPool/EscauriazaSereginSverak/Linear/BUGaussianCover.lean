/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.CollarCover
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Gaussian collar covers in the velocity carrier

The bounded-overlap cover is first constructed in L2Vec3; this file
transports it to the explicit Vec3 carrier used by the weak derivatives.
-/

public section


open Metric Set Classical
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

@[expose] def buGaussianCoverCenterMap
    (p : Fin (Besicovitch.multiplicity BUGaussianSpace) × BUGaussianSpace) :
    Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3 :=
  (p.1, vec3Homeomorph.symm p.2)

private theorem buGaussianCover_distance_eq (y : Vec3) (q : BUGaussianSpace) :
    vec3EuclideanNorm (y - vec3Homeomorph.symm q) =
      dist (vec3Homeomorph y) q := by
  rw [vec3EuclideanNorm_eq_l2]
  rw [WithLp.toLp_sub]
  have hq : WithLp.toLp 2 (vec3Homeomorph.symm q) = q := by
    rw [← vec3Homeomorph_apply]
    exact vec3Homeomorph.apply_symm_apply q
  rw [hq, ← vec3Homeomorph_apply y, dist_eq_norm]

/-- The transition annulus has a finite cover by Vec3 balls with doubled-ball
containment and the spatial overlap inherited from `Besicovitch`.
(`eq:bu-gaussian-collar`) -/
theorem exists_buGaussian_transition_cover_vec3
    (ρ r : ℝ) (hρ : 4 < ρ) (hr : 0 < r) (hrle : r ≤ 1 / 16) :
    ∃ Y : Finset (Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3),
      (∀ p ∈ Y, vec3EuclideanNorm p.2 ≤ ρ - 1 / 2) ∧
      (∀ p ∈ Y, 13 * ρ / 20 ≤ vec3EuclideanNorm p.2) ∧
      (∀ y : Vec3, 13 * ρ / 20 ≤ vec3EuclideanNorm y →
        vec3EuclideanNorm y ≤ 3 * ρ / 4 →
        ∃ p ∈ Y, y ∈ vec3Ball p.2 r) ∧
      (∀ p ∈ Y, vec3Ball p.2 (2 * r) ⊆ vec3Ball 0 ρ) ∧
      (∀ z : Vec3,
        (Y.filter fun p => z ∈ vec3Ball p.2 (2 * r)).card ≤
          Besicovitch.multiplicity BUGaussianSpace ^ 2) := by
  obtain ⟨Y, hcenter, hinner, hcover, houter, hmult⟩ :=
    exists_buGaussian_transition_cover ρ r hρ hr hrle
  let Φ := buGaussianCoverCenterMap
  let Y' := Y.image Φ
  have hnorm (y : Vec3) :
      vec3EuclideanNorm y = ‖vec3Homeomorph y‖ :=
    vec3EuclideanNorm_eq_l2 y
  have hnormSymm (q : BUGaussianSpace) :
      vec3EuclideanNorm (vec3Homeomorph.symm q) = ‖q‖ := by
    rw [vec3EuclideanNorm_eq_l2,
      ← vec3Homeomorph_apply (vec3Homeomorph.symm q),
      vec3Homeomorph.apply_symm_apply]
  have hdist (y : Vec3) (q : BUGaussianSpace) :
      vec3EuclideanNorm (y - vec3Homeomorph.symm q) =
        dist (vec3Homeomorph y) q := buGaussianCover_distance_eq y q
  have hcenter' (p : Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3)
      (hp : p ∈ Y') : vec3EuclideanNorm p.2 ≤ ρ - 1 / 2 := by
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    change vec3EuclideanNorm (vec3Homeomorph.symm q.2) ≤ ρ - 1 / 2
    rw [hnormSymm]
    exact hcenter q hq
  have hinner' (p : Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3)
      (hp : p ∈ Y') : 13 * ρ / 20 ≤ vec3EuclideanNorm p.2 := by
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    change 13 * ρ / 20 ≤ vec3EuclideanNorm (vec3Homeomorph.symm q.2)
    rw [hnormSymm]
    exact hinner q hq
  have hcover' : ∀ y : Vec3, 13 * ρ / 20 ≤ vec3EuclideanNorm y →
      vec3EuclideanNorm y ≤ 3 * ρ / 4 → ∃ p ∈ Y', y ∈ vec3Ball p.2 r := by
    intro y hylo hyhi
    obtain ⟨q, hq, hqy⟩ := hcover (vec3Homeomorph y) (by
      change 13 * ρ / 20 ≤ ‖vec3Homeomorph y‖ ∧
        ‖vec3Homeomorph y‖ ≤ 3 * ρ / 4
      rw [← hnorm y]
      exact ⟨hylo, hyhi⟩)
    refine ⟨Φ q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, ?_⟩
    change vec3EuclideanNorm (y - vec3Homeomorph.symm q.2) < r
    rw [hdist]
    exact hqy
  have houter' : ∀ p ∈ Y', vec3Ball p.2 (2 * r) ⊆ vec3Ball 0 ρ := by
    intro p hp y hy
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have hyq : dist (vec3Homeomorph y) q.2 < 2 * r := by
      have h := hy
      rw [mem_vec3Ball] at h
      change vec3EuclideanNorm (y - vec3Homeomorph.symm q.2) < 2 * r at h
      rwa [hdist] at h
    have hzero : dist (vec3Homeomorph y) 0 < ρ := by
      have h := houter q hq (Metric.mem_ball.mpr hyq)
      simpa only [mem_ball, dist_zero_right] using h
    change vec3EuclideanNorm (y - 0) < ρ
    rw [sub_zero, hnorm]
    have hzero' : ‖vec3Homeomorph y‖ < ρ := by
      simpa only [dist_eq_norm, sub_zero] using hzero
    exact hzero'
  have hinj : Set.InjOn Φ Y := by
    intro p hp q hq heq
    rcases p with ⟨i, x⟩
    rcases q with ⟨j, y⟩
    dsimp [Φ, buGaussianCoverCenterMap] at heq
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨hij, hxy⟩
    exact Prod.ext hij (vec3Homeomorph.symm.injective hxy)
  have hfilter (z : Vec3) :
      Y'.filter (fun p => z ∈ vec3Ball p.2 (2 * r)) =
        (Y.filter (fun q => dist (vec3Homeomorph z) q.2 < 2 * r)).image Φ := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpY, hpball⟩
      rcases Finset.mem_image.mp hpY with ⟨q, hqY, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨q, Finset.mem_filter.mpr ⟨hqY, ?_⟩, rfl⟩
      change vec3EuclideanNorm (z - vec3Homeomorph.symm q.2) < 2 * r at hpball
      rw [← hdist]
      exact hpball
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨q, hqfilter, rfl⟩
      rcases Finset.mem_filter.mp hqfilter with ⟨hqY, hdistq⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨q, hqY, rfl⟩, ?_⟩
      change vec3EuclideanNorm (z - vec3Homeomorph.symm q.2) < 2 * r
      rw [hdist]
      exact hdistq
  have hmult' (z : Vec3) :
      (Y'.filter fun p => z ∈ vec3Ball p.2 (2 * r)).card ≤
        Besicovitch.multiplicity BUGaussianSpace ^ 2 := by
    rw [hfilter]
    rw [Finset.card_image_of_injOn (f := Φ) (by
      intro p hp q hq heq
      exact hinj (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hq).1 heq)]
    exact hmult (vec3Homeomorph z)
  exact ⟨Y', hcenter', hinner', hcover', houter', hmult'⟩

end ESS

end
