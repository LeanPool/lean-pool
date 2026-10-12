/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Assembly.RealFormSlices
public import LeanPool.LiebThirring.Assembly.RealForm

/-!
# Electron-pair expectations from the one-body Coulomb estimate

One-body Coulomb estimates and particle slicing control electron-pair expectations by the
selected particle’s Fourier energy.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring.Assembly

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

/-- Inserting one particle does not move any other particle. -/
theorem realForm_particlePosition_insert_ne {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x : Position) (y : OtherConfiguration i) :
    particlePosition (insertParticle i x y) j = particlePosition (insertParticle i 0 y) j := by
  ext a
  simp only [particlePosition, insertParticle, PiLp.toLp_apply, dite_eq_right hij.symm]

/-- A pair expectation is the integral of the one-body expectations on the
remaining-coordinate slices, with centre at the other particle. -/
theorem realForm_pair_lintegral_eq_slices {N q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State N q) :
    (∫⁻ X : Configuration N, coulombKernel (particlePosition X i) (particlePosition X j) *
      (‖ψ X‖₊ : ℝ≥0∞) ^ 2) =
    ∫⁻ y : OtherConfiguration i, ∫⁻ x : Position,
      coulombKernel x (particlePosition (insertParticle i 0 y) j) *
        (‖realFormSwapCurrying (realFormParticleCurrying i ψ) y x‖₊ : ℝ≥0∞) ^ 2 := by
  let F : Configuration N → ℝ≥0∞ := fun X =>
    coulombKernel (particlePosition X i) (particlePosition X j) * (‖ψ X‖₊ : ℝ≥0∞) ^ 2
  have hF : Measurable F :=
    (measurable_coulombKernel.comp
      ((measurable_particlePosition i).prodMk (measurable_particlePosition j))).mul
      (measurable_state_norm_sq ψ)
  have hI : Measurable (fun z : Position × OtherConfiguration i =>
      F (insertParticle i z.1 z.2)) :=
    hF.comp (measurePreserving_insertParticle i).measurable
  calc
    _ = ∫⁻ z : Position × OtherConfiguration i, F (insertParticle i z.1 z.2) :=
      ((measurePreserving_insertParticle i).lintegral_comp hF).symm
    _ = ∫⁻ y : OtherConfiguration i, ∫⁻ x : Position, F (insertParticle i x y) :=
      lintegral_prod_symm _ hI.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [realFormParticleSlices_ae i ψ] with y hy
      apply lintegral_congr_ae
      filter_upwards [hy] with x hx
      exact congrArg₂ (fun (a b : ℝ≥0∞) => a * b)
        (congrArg₂ coulombKernel (particlePosition_insertParticle i x y)
          (realForm_particlePosition_insert_ne i j hij x y))
        (congrArg (fun a : SpinAmplitudes N q => (‖a‖₊ : ℝ≥0∞) ^ 2) hx).symm

/-- Conditional pair estimate: the input is the exact Hardy
one-body Fourier Coulomb bound, specialized to the full finite spin space. -/
theorem lintegral_pair_coulomb_le_of_one_body_bound {N q : ℕ}
    (hHardy : ∀ (c : Position) (u : Lp (SpinAmplitudes N q) 2 (volume : Measure Position)),
      (∫⁻ x : Position, coulombKernel x c * (‖u x‖₊ : ℝ≥0∞) ^ 2) ≤
        (‖u‖₊ : ℝ≥0∞) ^ 2 + 4 * ∫⁻ ξ : Position,
          ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
            (‖(Lp.fourierTransformₗᵢ Position (SpinAmplitudes N q) u) ξ‖₊ : ℝ≥0∞) ^ 2)
    (i j : Fin N) (hij : i ≠ j) (ψ : State N q) :
    (∫⁻ X : Configuration N, coulombKernel (particlePosition X i) (particlePosition X j) *
      (‖ψ X‖₊ : ℝ≥0∞) ^ 2) ≤
      (‖ψ‖₊ : ℝ≥0∞) ^ 2 + 4 * particleFourierEnergy ψ i := by
  let u := realFormParticleCurrying i ψ
  let v := realFormSwapCurrying u
  let w : Position → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2
  have hw : Measurable w :=
    measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have henergy : (∫⁻ y : OtherConfiguration i, ∫⁻ ξ : Position, w ξ *
      (‖(Lp.fourierTransformₗᵢ Position (SpinAmplitudes N q) (v y)) ξ‖₊ : ℝ≥0∞) ^ 2) =
      particleFourierEnergy ψ i :=
    (realFormSwapCurrying_fourier_weighted_norm_sq u w hw).trans
      (realFormParticleCurrying_fourier_energy i ψ)
  have hmass : (∫⁻ y : OtherConfiguration i, (‖v y‖₊ : ℝ≥0∞) ^ 2) =
      (‖ψ‖₊ : ℝ≥0∞) ^ 2 := by
    change (∫⁻ y : OtherConfiguration i, ‖v y‖ₑ ^ 2) = ‖ψ‖ₑ ^ 2
    rw [lintegral_l2_enorm_sq, ← ofReal_norm, ← ofReal_norm,
      LinearIsometryEquiv.norm_map, realFormParticleCurrying_norm]
  have hmeas : Measurable (fun y : OtherConfiguration i => (‖v y‖₊ : ℝ≥0∞) ^ 2) := by
    simpa only [enorm_eq_nnnorm] using (Lp.stronglyMeasurable v).enorm.pow_const 2
  rw [realForm_pair_lintegral_eq_slices i j hij ψ]
  calc
    _ ≤ ∫⁻ y : OtherConfiguration i, (‖v y‖₊ : ℝ≥0∞) ^ 2 +
        4 * ∫⁻ ξ : Position, w ξ *
          (‖(Lp.fourierTransformₗᵢ Position (SpinAmplitudes N q) (v y)) ξ‖₊ : ℝ≥0∞) ^ 2 :=
      lintegral_mono (fun y => hHardy (particlePosition (insertParticle i 0 y) j) (v y))
    _ = _ := by
      rw [lintegral_add_left hmeas,
        lintegral_const_mul' 4 _ (by norm_num), hmass, henergy]

/-- Each particle energy is dominated by the total kinetic energy. -/
theorem realForm_particleFourierEnergy_le {N q : ℕ} (i : Fin N) (ψ : State N q) :
    particleFourierEnergy ψ i ≤ kineticEnergy ψ := by
  rw [kineticEnergy_eq_sum_particleFourierEnergy]
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)

/-- Conditional finiteness of the electron repulsion on the finite kinetic
form domain, with no symmetry or normalization required. -/
theorem lintegral_electronRepulsion_lt_top_of_one_body_bound {N q : ℕ}
    (hHardy : ∀ (c : Position) (u : Lp (SpinAmplitudes N q) 2 (volume : Measure Position)),
      (∫⁻ x : Position, coulombKernel x c * (‖u x‖₊ : ℝ≥0∞) ^ 2) ≤
        (‖u‖₊ : ℝ≥0∞) ^ 2 + 4 * ∫⁻ ξ : Position,
          ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
            (‖(Lp.fourierTransformₗᵢ Position (SpinAmplitudes N q) u) ξ‖₊ : ℝ≥0∞) ^ 2)
    (ψ : State N q) (hT : kineticEnergy ψ < ⊤) :
    (∫⁻ x : Configuration N, electronRepulsion x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
  classical
  unfold electronRepulsion
  simp_rw [Finset.sum_mul]
  rw [lintegral_finsetSum]
  · apply ENNReal.sum_lt_top.mpr
    intro i _
    rw [lintegral_finsetSum]
    · apply ENNReal.sum_lt_top.mpr
      intro j hj
      have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
      apply (lintegral_pair_coulomb_le_of_one_body_bound hHardy i j hij ψ).trans_lt
      apply ENNReal.add_lt_top.mpr
      refine ⟨ENNReal.pow_lt_top ENNReal.coe_lt_top, ?_⟩
      exact ENNReal.mul_lt_top (by norm_num)
        ((realForm_particleFourierEnergy_le i ψ).trans_lt hT)
    · intro j _
      exact (measurable_coulombKernel.comp
        ((measurable_particlePosition i).prodMk (measurable_particlePosition j))).mul
        (measurable_state_norm_sq ψ)
  · intro i _
    exact Finset.measurable_sum _ (fun j _ =>
      (measurable_coulombKernel.comp
        ((measurable_particlePosition i).prodMk (measurable_particlePosition j))).mul
        (measurable_state_norm_sq ψ))

end LiebThirring.Assembly
end
