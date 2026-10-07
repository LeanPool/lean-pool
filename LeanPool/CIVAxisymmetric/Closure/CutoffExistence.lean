/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Analysis.CurlCutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball

/-!
The explicit round Euclidean ball of the ambient cutoff library agrees, at a
positive radius, with this repository's own `vec3Ball`. -/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV


theorem euclideanBall_eq_vec3Ball (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    CKN.euclideanBall x₀ R = vec3Ball x₀ R := by
  ext x
  simp only [CKN.euclideanBall, CKN.euclideanSqDist, Set.mem_ofPred_eq, mem_vec3Ball,
    vec3EuclideanNorm, CKN.vecNormSq_eq_sum_sq]
  exact (Real.sqrt_lt' hR).symm

/-!
A smooth, compactly supported cutoff exists, equal to `1` on `B(ρ)` and
supported inside `B(Rstar)`, for any `0 ≤ ρ < Rstar` — the cutoff `χ` of
`lem:aniso:closure`'s energy setup.
-/
theorem exists_smooth_cutoff_eq_one_on_vec3Ball_support_subset {ρ Rstar : ℝ} (hρ : 0 ≤ ρ)
    (hρR : ρ < Rstar) :
    ∃ χ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ vec3Ball (0 : Vec3) Rstar ∧ ∀ x ∈ vec3Ball (0 : Vec3) ρ, χ x = 1 := by
  have hRpos : 0 < Rstar := lt_of_le_of_lt hρ hρR
  refine ⟨CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar,
    CKN.canonicalBallCutoff_smooth (0 : Vec3) hρ hρR,
    CKN.canonicalBallCutoff_hasCompactSupport hρ hρR, ?_, ?_⟩
  · have hsupp := CKN.canonicalBallCutoff_tsupport_subset_outer (d := 3) (x₀ := (0 : Vec3))
      hρ hρR
    intro y hy
    have hy' := hsupp hy
    rw [← euclideanBall_eq_vec3Ball (0 : Vec3) hRpos]
    exact hy'
  · rcases eq_or_lt_of_le hρ with (hρ0 | hρpos)
    · intro x hx
      rw [← hρ0] at hx
      have hnonneg := vec3EuclideanNorm_nonneg (x - (0 : Vec3))
      exact absurd hx (not_lt.mpr hnonneg)
    · intro x hx
      have hx' : x ∈ CKN.euclideanBall (0 : Vec3) ρ := by
        simpa [← euclideanBall_eq_vec3Ball (0 : Vec3) hρpos] using hx
      exact CKN.canonicalBallCutoff_eq_one_on_inner hρ hρR hx'

/-!
The cutoff of the previous theorem vanishes outside `B(Rstar)`. -/
theorem canonicalBallCutoff_eq_zero_of_notMem_vec3Ball {ρ Rstar : ℝ} (hρ : 0 ≤ ρ)
    (hρR : ρ < Rstar) {x : Vec3} (hx : x ∉ vec3Ball (0 : Vec3) Rstar) :
    CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar x = 0 := by
  have hRpos : 0 < Rstar := lt_of_le_of_lt hρ hρR
  have hsupp := CKN.canonicalBallCutoff_tsupport_subset_outer (d := 3) (x₀ := (0 : Vec3))
    hρ hρR
  have hsupp' : tsupport (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) ⊆
      vec3Ball (0 : Vec3) Rstar := by
    intro y hy
    have hy' := hsupp hy
    rw [← euclideanBall_eq_vec3Ball (0 : Vec3) hRpos]
    exact hy'
  by_contra hne
  exact hx (hsupp' (subset_tsupport _ hne))

/-!
This repository's Euclidean norm on `Vec3` agrees with the ambient cutoff
library's own Euclidean norm.
-/
theorem vec3EuclideanNorm_eq_vecEuclideanNorm (v : Vec3) :
    vec3EuclideanNorm v = CKN.vecEuclideanNorm v := by
  simp [vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot, pow_two]

/-!
The gradient of the cutoff of
`exists_smooth_cutoff_eq_one_on_vec3Ball_support_subset`, read with this
repository's own Euclidean norm and gradient, obeys the explicit bound
`32/(Rstar − ρ)`. -/
theorem vec3EuclideanNorm_gradVec_canonicalBallCutoff_le {ρ Rstar : ℝ} (hρ : 0 ≤ ρ)
    (hρR : ρ < Rstar) (x : Vec3) :
    vec3EuclideanNorm (gradVec (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) x)
      ≤ 32 / (Rstar - ρ) := by
  have h_eq : gradVec (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) x =
      CKN.classicalGradient (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) x := rfl
  rw [h_eq, vec3EuclideanNorm_eq_vecEuclideanNorm]
  exact CKN.canonicalBallCutoff_gradient_bound hρ hρR x

end CIV
