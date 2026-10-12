/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import LeanPool.LiebThirring.Defs.Antisymmetric
/-!
# Particle permutations

Spatial coordinate permutation as a linear isometry.

The finite spin labels are permuted bijectively.
-/
public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring

/-- Spatial coordinate permutation as a linear isometry. -/
@[expose] noncomputable def permutationLinearIsometryEquiv {N : ℕ}
    (σ : Equiv.Perm (Fin N)) : Configuration N ≃ₗᵢ[ℝ] Configuration N :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (σ.symm.prodCongr (Equiv.refl (Fin 3)))

theorem permutationLinearIsometryEquiv_apply {N : ℕ} (σ : Equiv.Perm (Fin N))
    (x : Configuration N) : permutationLinearIsometryEquiv σ x = permutePositions σ x := by
  rfl

theorem measurePreserving_permutePositions {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (permutePositions σ) volume volume := by
  have h : (permutationLinearIsometryEquiv σ : Configuration N → Configuration N) =
      permutePositions σ := funext (permutationLinearIsometryEquiv_apply σ)
  rw [← h]
  exact (permutationLinearIsometryEquiv σ).measurePreserving

theorem measurableEmbedding_permutePositions {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    MeasurableEmbedding (permutePositions σ) := by
  have h : (permutationLinearIsometryEquiv σ : Configuration N → Configuration N) =
      permutePositions σ := funext (permutationLinearIsometryEquiv_apply σ)
  rw [← h]
  exact (permutationLinearIsometryEquiv σ).toHomeomorph.measurableEmbedding

@[simp] theorem particlePosition_permutePositions {N : ℕ} (σ : Equiv.Perm (Fin N))
    (x : Configuration N) (i : Fin N) :
    particlePosition (permutePositions σ x) i = particlePosition x (σ i) := rfl

/-- The finite spin labels are permuted bijectively. -/
@[expose] def spinPermutationEquiv {N q : ℕ} (σ : Equiv.Perm (Fin N)) :
    SpinLabels N q ≃ SpinLabels N q where
  toFun := permuteSpins σ
  invFun := permuteSpins σ.symm
  left_inv s := by funext i; simp [permuteSpins]
  right_inv s := by funext i; simp [permuteSpins]

/-- Spin-coordinate reindexing is a complex linear isometry. -/
@[expose] noncomputable def spinPermutationLinearIsometryEquiv {N q : ℕ}
    (σ : Equiv.Perm (Fin N)) : SpinAmplitudes N q ≃ₗᵢ[ℂ] SpinAmplitudes N q :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (spinPermutationEquiv (q := q) σ).symm

theorem norm_permutePositions_ae {N q : ℕ} (ψ : State N q) (hψ : antisymmetric ψ)
    (σ : Equiv.Perm (Fin N)) :
    ∀ᵐ x ∂(volume : Measure (Configuration N)), ‖ψ (permutePositions σ x)‖ = ‖ψ x‖ := by
  filter_upwards [hψ σ] with x hx
  have heq : spinPermutationLinearIsometryEquiv σ (ψ (permutePositions σ x)) =
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) • ψ x := by
    ext s
    exact hx s
  have hc : ‖((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  calc
    ‖ψ (permutePositions σ x)‖ =
        ‖spinPermutationLinearIsometryEquiv σ (ψ (permutePositions σ x))‖ :=
      ((spinPermutationLinearIsometryEquiv σ).norm_map _).symm
    _ = ‖ψ x‖ := by rw [heq, norm_smul, hc, one_mul]

/-- The norm equality also holds in the nonnegative norm used by the density. -/
theorem nnnorm_permutePositions_ae {N q : ℕ} (ψ : State N q) (hψ : antisymmetric ψ)
    (σ : Equiv.Perm (Fin N)) :
    ∀ᵐ x ∂(volume : Measure (Configuration N)), ‖ψ (permutePositions σ x)‖₊ = ‖ψ x‖₊ := by
  filter_upwards [norm_permutePositions_ae ψ hψ σ] with x hx
  exact NNReal.coe_injective hx

/-- Relabeling particles preserves every nonnegative marginal test. -/
theorem particle_marginal_permutation {N q : ℕ} (ψ : State N q) (hψ : antisymmetric ψ)
    (σ : Equiv.Perm (Fin N)) (i : Fin N) (v : Position → ℝ≥0∞) :
    (∫⁻ x : Configuration N, v (particlePosition x (σ i)) * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : Configuration N, v (particlePosition x i) * (‖ψ x‖₊ : ℝ≥0∞) ^ 2 := by
  calc
    _ = ∫⁻ x : Configuration N, v (particlePosition (permutePositions σ x) i) *
        (‖ψ (permutePositions σ x)‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [nnnorm_permutePositions_ae ψ hψ σ] with x hx
      rw [particlePosition_permutePositions, hx]
    _ = _ := (measurePreserving_permutePositions σ).lintegral_comp_emb
      (measurableEmbedding_permutePositions σ)
      (fun x : Configuration N => v (particlePosition x i) * (‖ψ x‖₊ : ℝ≥0∞) ^ 2)

/-- All particle marginals of an antisymmetric state have the same tests. -/
theorem particle_marginals_eq {N q : ℕ} (ψ : State N q) (hψ : antisymmetric ψ)
    (i j : Fin N) (v : Position → ℝ≥0∞) :
    (∫⁻ x : Configuration N, v (particlePosition x i) * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : Configuration N, v (particlePosition x j) * (‖ψ x‖₊ : ℝ≥0∞) ^ 2 := by
  simpa only [Equiv.swap_apply_left] using
    particle_marginal_permutation ψ hψ (Equiv.swap j i) j v

end LiebThirring
end
