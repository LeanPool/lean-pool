/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import LeanPool.LiebThirring.Defs.Density
public import LeanPool.LiebThirring.Kinetic.Insertion
/-!
# Measurability, testing and mass of the one-particle density

Arbitrary representatives agreeing almost everywhere give the same density almost everywhere,
with no measurability assumption on the replacement.
-/
public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring

theorem measurable_particlePosition {N : ℕ} (i : Fin N) :
    Measurable (fun x : Configuration N => particlePosition x i) := by
  exact ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (continuous_pi (fun a => PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ)
      (i, a)))).measurable

theorem measurable_state_norm_sq {N q : ℕ} (ψ : State N q) :
    Measurable (fun x : Configuration N => (‖ψ x‖₊ : ℝ≥0∞) ^ 2) :=
  (Lp.stronglyMeasurable ψ).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2

theorem measurable_inserted_state_norm_sq {N q : ℕ} (ψ : State N q) (i : Fin N) :
    Measurable (fun z : Position × OtherConfiguration i =>
      (‖ψ (insertParticle i z.1 z.2)‖₊ : ℝ≥0∞) ^ 2) :=
  (measurable_state_norm_sq ψ).comp (measurePreserving_insertParticle i).measurable

theorem measurable_particle_marginal {N q : ℕ} (ψ : State N q) (i : Fin N) :
    Measurable (fun x : Position => ∫⁻ y : OtherConfiguration i,
      (‖ψ (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2) :=
  (measurable_inserted_state_norm_sq ψ i).lintegral_prod_right'

theorem measurable_density {N q : ℕ} (ψ : State N q) : Measurable (density ψ) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_particle_marginal ψ i)

theorem particle_marginal_testing {N q : ℕ} (ψ : State N q) (i : Fin N)
    (v : Position → ℝ≥0∞) (hv : Measurable v) :
    (∫⁻ x : Position, v x * ∫⁻ y : OtherConfiguration i,
      (‖ψ (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2) =
    ∫⁻ x : Configuration N, v (particlePosition x i) * (‖ψ x‖₊ : ℝ≥0∞) ^ 2 := by
  have hf : Measurable (fun z : Configuration N =>
      v (particlePosition z i) * (‖ψ z‖₊ : ℝ≥0∞) ^ 2) :=
    (hv.comp (measurable_particlePosition i)).mul (measurable_state_norm_sq ψ)
  have hm : Measurable (fun z : Position × OtherConfiguration i =>
      v z.1 * (‖ψ (insertParticle i z.1 z.2)‖₊ : ℝ≥0∞) ^ 2) :=
    (hv.comp measurable_fst).mul (measurable_inserted_state_norm_sq ψ i)
  calc
    _ = ∫⁻ x : Position, ∫⁻ y : OtherConfiguration i,
        v x * (‖ψ (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr
      intro x
      have hy := (measurable_inserted_state_norm_sq ψ i).comp
        (measurable_prodMk_left (x := x))
      exact (lintegral_const_mul (v x) hy).symm
    _ = ∫⁻ z : Position × OtherConfiguration i,
        v z.1 * (‖ψ (insertParticle i z.1 z.2)‖₊ : ℝ≥0∞) ^ 2 :=
      (lintegral_prod _ hm.aemeasurable).symm
    _ = _ := by
      have ht := (measurePreserving_insertParticle i).lintegral_comp hf
      simpa only [particlePosition_insertParticle] using ht

theorem density_testing (N q : ℕ) (ψ : State N q) (v : Position → ℝ≥0∞)
    (hv : Measurable v) :
    (∫⁻ x : Position, v x * density ψ x) =
      ∑ i : Fin N, ∫⁻ x : Configuration N,
        v (particlePosition x i) * (‖ψ x‖₊ : ℝ≥0∞) ^ 2 := by
  simp only [density, Finset.mul_sum]
  rw [lintegral_finsetSum (f := fun i x => v x * ∫⁻ y : OtherConfiguration i,
    (‖ψ (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2) Finset.univ
    (fun i _ => hv.mul (measurable_particle_marginal ψ i))]
  exact Finset.sum_congr rfl (fun i _ => particle_marginal_testing ψ i v hv)

theorem lintegral_state_norm_sq {N q : ℕ} (ψ : State N q) :
    (∫⁻ x : Configuration N, (‖ψ x‖₊ : ℝ≥0∞) ^ 2) = (‖ψ‖₊ : ℝ≥0∞) ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (Lp.aestronglyMeasurable ψ)
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
    ← Lp.enorm_def, enorm_eq_nnnorm] using h.symm

theorem density_mass {N q : ℕ} (ψ : State N q) :
    (∫⁻ x : Position, density ψ x) = (N : ℝ≥0∞) * (‖ψ‖₊ : ℝ≥0∞) ^ 2 := by
  have h := density_testing N q ψ (fun _ => 1) measurable_const
  simpa only [one_mul, lintegral_state_norm_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

end LiebThirring
end
