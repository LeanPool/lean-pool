/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineInterval

/-!
# Scalar weak identities on affine time intervals

Integration by parts transports through the translated interval used in
`lem:bu-small-time`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A scalar integration-by-parts identity transfers through an affine
parabolic change of variables on corresponding time intervals. -/
theorem bu_affine_weak_identity_interval
    (τ scale a b c d : ℝ) (hscale : 0 < scale) (hd : d ≠ 0)
    (f g : ParabolicPoint → ℝ)
    (D : (ParabolicPoint → ℝ) → ParabolicPoint → ℝ)
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)))))
    (hDcont : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) →
      Continuous (D φ))
    (hDpull : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2} (Ioo a b) →
      ∀ z : ParabolicPoint,
        D (show ParabolicPoint → ℝ from
          ψ ∘ (buAffineHomeomorph τ scale hscale).symm)
          (buAffinePoint τ scale z) = d⁻¹ * D ψ z)
    (hsource : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) →
      (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)), f z * D φ z) =
        -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)), g z * φ z)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      {x : Vec3 | 0 < x 2} (Ioo a b)) :
    (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
      (c * f (buAffinePoint τ scale z)) * D ψ z) =
      -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
        (c * d * g (buAffinePoint τ scale z)) * ψ z := by
  let ψhat : Vec3 × ℝ → ℝ :=
    ψ ∘ (buAffineHomeomorph τ scale hscale).symm
  have hψhat : ψhat ∈ spaceTimeTestFunction (V := ℝ)
      {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) :=
    bu_affine_pullback_test_interval τ scale a b hscale hψ
  have hS := hsource ψhat hψhat
  let Q := spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))
  let A := fun z : ParabolicPoint => f z * D ψhat z
  let B := fun z : ParabolicPoint => g z * ψhat z
  have hhatC : Continuous (fun z : ParabolicPoint => ψhat z) := by
    have hc := hψhat.1.continuous.comp parabolicHomeomorph.continuous
    exact hc.congr (fun _ => rfl)
  have hAm : AEStronglyMeasurable A (volume.restrict Q) :=
    hf.mul (hDcont ψhat hψhat).aestronglyMeasurable
  have hBm : AEStronglyMeasurable B (volume.restrict Q) :=
    hg.mul hhatC.aestronglyMeasurable
  have hAchange := bu_affine_integral_comp_interval τ scale a b hscale A hAm
  have hBchange := bu_affine_integral_comp_interval τ scale a b hscale B hBm
  have hhat_at (z : ParabolicPoint) :
      ψhat (buAffinePoint τ scale z) = ψ z := by
    change ψ ((buAffineHomeomorph τ scale hscale).symm
      (buAffinePoint τ scale z)) = ψ z
    have hp : buAffinePoint τ scale z =
        (buAffineHomeomorph τ scale hscale) (show Vec3 × ℝ from z) := by
      exact congrFun (buAffineHomeomorph_eq τ scale hscale).symm z
    rw [hp]
    exact congrArg ψ ((buAffineHomeomorph τ scale hscale).symm_apply_apply _)
  have hderiv' (z : ParabolicPoint) :
      D ψ z = d * D ψhat (buAffinePoint τ scale z) := by
    have hp := hDpull ψ hψ z
    change D ψhat (buAffinePoint τ scale z) = d⁻¹ * D ψ z at hp
    rw [hp]
    field_simp
  have hAint :
      (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
        (c * f (buAffinePoint τ scale z)) * D ψ z) =
      c * d * (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
        A (buAffinePoint τ scale z)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [A]
    rw [hderiv']
    ring
  have hBint :
      (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
        (c * d * g (buAffinePoint τ scale z)) * ψ z) =
      c * d * (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
        B (buAffinePoint τ scale z)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [B]
    rw [hhat_at]
    ring
  calc
    (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
        (c * f (buAffinePoint τ scale z)) * D ψ z) =
      c * d * (scale⁻¹ ^ 5 * ∫ z in Q, A z) := by
        rw [hAint, hAchange]
    _ = -(c * d * (scale⁻¹ ^ 5 * ∫ z in Q, B z)) := by
      rw [hS]
      ring
    _ = -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
        (c * d * g (buAffinePoint τ scale z)) * ψ z := by
      rw [hBint, hBchange]

/-- The scalar spatial weak derivative identity transfers with one power of
the affine spatial scale. -/
theorem bu_affine_spatial_weak_identity_interval
    (τ scale a b c : ℝ) (hscale : 0 < scale)
    (f g : ParabolicPoint → ℝ) (j : Fin 3)
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)))))
    (hsource : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) →
      (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)), f z * spatialPartial φ j z) =
        -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)), g z * φ z)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      {x : Vec3 | 0 < x 2} (Ioo a b)) :
    (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
      (c * f (buAffinePoint τ scale z)) * spatialPartial ψ j z) =
      -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
        (c * scale * g (buAffinePoint τ scale z)) * ψ z := by
  apply bu_affine_weak_identity_interval τ scale a b c scale hscale hscale.ne'
    f g (fun φ z => spatialPartial φ j z) hf hg
  · intro φ hφ
    have hc := (spatialPartial_contDiff hφ.1 j).continuous.comp
      parabolicHomeomorph.continuous
    exact hc.congr (fun _ => rfl)
  · intro ψ hψ z
    rw [buAffineHomeomorph_symm_eq τ scale hscale]
    have hp := CKN.spatialPartial_pullback scale hscale
      ((0 : Vec3), τ) hψ.1 j z
    rw [← buAffinePoint_eq_scalingParabolic] at hp
    have heq : (show ParabolicPoint → ℝ from
        ψ ∘ fun q : Vec3 × ℝ =>
          (scale⁻¹ • q.1, (scale ^ 2)⁻¹ * (q.2 - τ))) =
        ψ ∘ fun q : ParabolicPoint =>
          (scale⁻¹ • (q.1 - (0 : Vec3)),
            (scale ^ 2)⁻¹ * (q.2 - τ)) := by
      funext q
      change ψ (scale⁻¹ • q.1, (scale ^ 2)⁻¹ * (q.2 - τ)) =
        ψ (scale⁻¹ • (q.1 - (0 : Vec3)), (scale ^ 2)⁻¹ * (q.2 - τ))
      simp only [sub_zero]
    rw [heq]
    exact hp
  · exact hsource
  · exact hψ

/-- The scalar weak time derivative identity transfers with two powers of
the affine spatial scale. -/
theorem bu_affine_time_weak_identity_interval
    (τ scale a b c : ℝ) (hscale : 0 < scale)
    (f g : ParabolicPoint → ℝ)
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)))))
    (hsource : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) →
      (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)), f z * timePartial φ z) =
        -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)), g z * φ z)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      {x : Vec3 | 0 < x 2} (Ioo a b)) :
    (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
      (c * f (buAffinePoint τ scale z)) * timePartial ψ z) =
      -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
        (c * scale ^ 2 * g (buAffinePoint τ scale z)) * ψ z := by
  apply bu_affine_weak_identity_interval τ scale a b c (scale ^ 2) hscale
    (sq_pos_of_pos hscale).ne' f g (fun φ z => timePartial φ z) hf hg
  · intro φ hφ
    have hc := (contDiff_timePartial hφ.1).continuous.comp
      parabolicHomeomorph.continuous
    exact hc.congr (fun _ => rfl)
  · intro ψ hψ z
    rw [buAffineHomeomorph_symm_eq τ scale hscale]
    have hp := CKN.timePartial_pullback scale hscale
      ((0 : Vec3), τ) hψ.1 z
    rw [← buAffinePoint_eq_scalingParabolic] at hp
    have heq : (show ParabolicPoint → ℝ from
        ψ ∘ fun q : Vec3 × ℝ =>
          (scale⁻¹ • q.1, (scale ^ 2)⁻¹ * (q.2 - τ))) =
        ψ ∘ fun q : ParabolicPoint =>
          (scale⁻¹ • (q.1 - (0 : Vec3)),
            (scale ^ 2)⁻¹ * (q.2 - τ)) := by
      funext q
      change ψ (scale⁻¹ • q.1, (scale ^ 2)⁻¹ * (q.2 - τ)) =
        ψ (scale⁻¹ • (q.1 - (0 : Vec3)), (scale ^ 2)⁻¹ * (q.2 - τ))
      simp only [sub_zero]
    rw [heq]
    exact hp
  · exact hsource
  · exact hψ

end ESS
