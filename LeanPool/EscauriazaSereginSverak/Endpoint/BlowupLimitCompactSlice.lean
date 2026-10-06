/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitRepresentativeExtension
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitSliceBounds

/-!
# Compact slice bounds for rescaled trace fields

On any closed time interval whose source times stay in the trace interval,
the measurable rescalings satisfy the compact-slice hypothesis of
`lem:compactness` of the CKN manuscript.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The all-time trace representative supplies every-time compact spatial
`L²` bounds for a rescaled sequence, including the closed top time. -/
theorem blowup_limit_rescaling_compact_slice_bound
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (M : ℝ)
    (hsource : ∀ t,
      MemLp ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
        (fun x => W (x,t))) 3 volume ∧
      eLpNorm (fun x => vec3EuclideanNorm
        ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
          (fun y => W (y,t)) x)) 3 volume ≤ ENNReal.ofReal M)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n)
    (C : Set Vec3) (hC : IsCompact C)
    (a b : ℝ)
    (hsourceTime : ∀ n t, t ∈ Icc a b →
      t₀ + (r n) ^ 2 * t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0) :
    ∀ n t, t ∈ Icc a b →
      (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm
        (blowupLimitTraceRescaling W x₀ t₀ (r n) (x,t))) ^ (2 : ℝ)
        ∂volume) ≤ (ENNReal.ofReal M * (volume C) ^ (1 / 6 : ℝ)) ^ (2 : ℝ) := by
  intro n t ht
  let τ : ℝ := t₀ + (r n) ^ 2 * t
  have hτ : τ ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 := hsourceTime n t ht
  let τI : Icc (-(3 / 4 : ℝ) ^ 2) 0 := ⟨τ, hτ⟩
  have hfun : (fun x : Vec3 =>
      blowupLimitTraceRescaling W x₀ t₀ (r n) ((x,t) : ParabolicPoint)) =
      fun x => (r n) • (vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
        (fun y => W (y,τI)) (x₀ + (r n) • x) := by
    funext x
    by_cases hx : x₀ + (r n) • x ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ)
    · have hpair : x₀ + (r n) • x ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ) ∧
          t₀ + (r n) ^ 2 * t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 := ⟨hx, by simpa [τ] using hτ⟩
      have hτeq : (⟨t₀ + (r n) ^ 2 * t, hpair.2⟩ :
          Icc (-(3 / 4 : ℝ) ^ 2) 0) = τI := by
        apply Subtype.ext
        rfl
      simp [blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
        parabolicTranslate, parabolicScale, τI, hpair, hτeq]
    · simp [blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
        parabolicTranslate, parabolicScale, τI, hx]
  calc
    (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm
        (blowupLimitTraceRescaling W x₀ t₀ (r n) ((x,t) : ParabolicPoint))) ^
        (2 : ℝ) ∂volume) =
      ∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm ((r n) •
        (vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
          (fun y => W (y,τI)) (x₀ + (r n) • x))) ^ (2 : ℝ) ∂volume := by
            apply lintegral_congr_ae
            filter_upwards [] with x
            rw [congrFun hfun x]
    _ ≤ (ENNReal.ofReal M * (volume C) ^ (1 / 6 : ℝ)) ^ (2 : ℝ) :=
      blowup_limit_trace_rescaled_compact_slice_bound W M hsource
        x₀ (r n) (hr n) C hC τI

end ESS

end
