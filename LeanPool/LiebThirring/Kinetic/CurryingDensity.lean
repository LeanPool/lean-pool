/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.CurryingState
public import LeanPool.LiebThirring.Kinetic.CurryingMarginal

/-!
# The curried density field

Curried fiber norms identify the particle marginals and the scaled density field.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Extended squared norm of a finite Hilbert sum. -/
theorem piLp_enorm_sq {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] (u : PiLp 2 E) :
    ‖u‖ₑ ^ 2 = ∑ i, ‖u i‖ₑ ^ 2 := by
  simp only [← ofReal_norm]
  simp_rw [← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [PiLp.norm_sq_eq_of_L2]
  exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)

/-- Each marginal is the squared norm of the currying outer fiber a.e. -/
theorem particle_marginal_eq_currying_norm_sq_ae {N q : ℕ} (i : Fin N) (ψ : State N q) :
    (fun x : Position => ∫⁻ y : OtherConfiguration i,
      (‖ψ (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2) =ᵐ[volume]
    fun x => (‖oneParticleCurrying i ψ x‖₊ : ℝ≥0∞) ^ 2 := by
  filter_upwards [oneParticleCurrying_ae i ψ] with x hx
  have hxy : ∀ᵐ y : OtherConfiguration i, ∀ s : Fin q, ∀ t : OtherSpinLabels i q,
      oneParticleCurrying i ψ x s y t = ψ (insertParticle i x y) (insertSpin i s t) :=
    ae_all_iff.mpr hx
  calc
    _ = ∫⁻ y : OtherConfiguration i,
        ‖spinCurryingLinearIsometryEquiv i (ψ (insertParticle i x y))‖ₑ ^ 2 := by
      apply lintegral_congr
      intro y
      rw [LinearIsometryEquiv.enorm_map]
      rfl
    _ = ∫⁻ y : OtherConfiguration i, ∑ s : Fin q,
        ‖oneParticleCurrying i ψ x s y‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [hxy] with y hy
      rw [piLp_enorm_sq]
      apply Finset.sum_congr rfl
      intro s _
      congr 2
      ext t
      exact (hy s t).symm
    _ = ∑ s : Fin q, ∫⁻ y : OtherConfiguration i,
        ‖oneParticleCurrying i ψ x s y‖ₑ ^ 2 :=
      lintegral_finsetSum _ (fun s _ =>
        ((Lp.stronglyMeasurable (oneParticleCurrying i ψ x s)).enorm.pow_const 2))
    _ = ∑ s : Fin q, ‖oneParticleCurrying i ψ x s‖ₑ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      exact lintegral_l2_enorm_sq _
    _ = _ := (piLp_enorm_sq _).symm

/-- The density is `N` times the squared norm of any selected curried fiber. -/
theorem density_eq_mul_currying_norm_sq_ae {N q : ℕ} (i : Fin N) (ψ : State N q)
    (hψ : antisymmetric ψ) :
    density ψ =ᵐ[volume] fun x : Position =>
      (N : ℝ≥0∞) * (‖oneParticleCurrying i ψ x‖₊ : ℝ≥0∞) ^ 2 := by
  filter_upwards [density_eq_mul_particle_marginal_ae ψ hψ i,
    particle_marginal_eq_currying_norm_sq_ae i ψ] with x hx hy
  exact hx.trans (congrArg (fun z : ℝ≥0∞ => (N : ℝ≥0∞) * z) hy)

/-- The outer density field used by the Rumin argument. -/
@[expose] noncomputable def densityField {N q : ℕ} (i : Fin N) (ψ : State N q) :
    Lp (OneParticleFiber i q) 2 (volume : Measure Position) :=
  (Real.sqrt N : ℂ) • oneParticleCurrying i ψ

/-- The density is the squared fiber norm of the density field a.e. -/
theorem density_eq_densityField_norm_sq_ae {N q : ℕ} (i : Fin N) (ψ : State N q)
    (hψ : antisymmetric ψ) :
    density ψ =ᵐ[volume] fun x : Position => (‖densityField i ψ x‖₊ : ℝ≥0∞) ^ 2 := by
  filter_upwards [density_eq_mul_currying_norm_sq_ae i ψ hψ,
    Lp.coeFn_smul (Real.sqrt N : ℂ) (oneParticleCurrying i ψ)] with x hx hs
  simp only [Pi.smul_apply] at hs
  rw [hx]
  change _ = (‖((Real.sqrt N : ℂ) • oneParticleCurrying i ψ) x‖₊ : ℝ≥0∞) ^ 2
  rw [hs]
  have hnorm : ‖(Real.sqrt N : ℂ) • oneParticleCurrying i ψ x‖ ^ 2 =
      (N : ℝ) * ‖oneParticleCurrying i ψ x‖ ^ 2 := by
    rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg N)]
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (norm_nonneg ((Real.sqrt N : ℂ) • oneParticleCurrying i ψ x)),
    ENNReal.ofReal_pow (norm_nonneg (oneParticleCurrying i ψ x)),
    ofReal_norm, enorm_eq_nnnorm]
    using (congrArg ENNReal.ofReal hnorm).symm

end LiebThirring

end
