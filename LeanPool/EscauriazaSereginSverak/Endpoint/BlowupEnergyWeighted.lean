/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupEnergyDensity
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.AELocalEnergy

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set
noncomputable section
namespace ESS

/-- The local energy inequality bounds the cutoff-weighted gradient by the
three standard velocity-pressure terms, uniformly in the upper time cutoff. -/
theorem blowupEnergyCutoff_weighted_gradient_bound
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), b < 0 →
      ∀ {q : ℝ} {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ},
      IsSuitableWeakSolutionIntegrable
        (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) q u Du p 0 →
      IntegrableOn (fun z : ParabolicPoint =>
        (8 + 3 * C) * (vec3EuclideanNorm (u z)) ^ 2 +
          3 * C * (vec3EuclideanNorm (u z)) ^ 3 +
          6 * C * |p z| * vec3EuclideanNorm (u z))
        (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0)) volume →
      2 * ∫ z in spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0),
        spatialGradientSq u Du z * blowupEnergyCutoff R a b z ≤
      ∫ z in spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0),
        (8 + 3 * C) * (vec3EuclideanNorm (u z)) ^ 2 +
          3 * C * (vec3EuclideanNorm (u z)) ^ 3 +
          6 * C * |p z| * vec3EuclideanNorm (u z) := by
  obtain ⟨C, hC, hpoint⟩ := blowupEnergyCutoff_localEnergyRhs_power_le R hR
  refine ⟨C, hC, fun a b hb q u Du p hsol hint => ?_⟩
  let Ω : Set Vec3 := CKN.euclideanBall 0 (R + 1)
  let I : Set ℝ := Ioo (a - 2) 0
  let ψ : Vec3 × ℝ → ℝ := blowupEnergyCutoff R a b
  have htest := (blowupEnergyCutoff_test R a b hR hb).1
  have hpos := (blowupEnergyCutoff_test R a b hR hb).2
  have hrhs : IntegrableOn (fun z : ParabolicPoint => localEnergyRhs u p 0 ψ z)
      (spaceTimeSet Ω I) volume :=
    (suitableWeakSolution_energy_integrable hsol htest hpos).2.1.integrableOn
  have hmono :
      (∫ z in spaceTimeSet Ω I, localEnergyRhs u p 0 ψ z) ≤
      ∫ z in spaceTimeSet Ω I,
        (8 + 3 * C) * (vec3EuclideanNorm (u z)) ^ 2 +
          3 * C * (vec3EuclideanNorm (u z)) ^ 3 +
          6 * C * |p z| * vec3EuclideanNorm (u z) := by
    apply integral_mono_ae hrhs hint
    filter_upwards [] with z
    exact hpoint a b hb u p z
  exact (suitableWeakSolution_energyInequality hsol htest hpos).trans hmono

/-- The gradient energy on the inner past cylinder is dominated by the
cutoff-weighted energy on the larger cylinder. -/
theorem blowupEnergyCutoff_inner_gradient_le
    (R a b : ℝ) (hR : 0 < R) (hb : b < 0)
    {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable
      (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) q u Du p 0) :
    (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a b),
      spatialGradientSq u Du z) ≤
      ∫ z in spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0),
        spatialGradientSq u Du z * blowupEnergyCutoff R a b z := by
  let outer := spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0)
  let inner := spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a b)
  let ψ := blowupEnergyCutoff R a b
  have htest := (blowupEnergyCutoff_test R a b hR hb).1
  have hpos := (blowupEnergyCutoff_test R a b hR hb).2
  have hint : IntegrableOn (fun z : ParabolicPoint => spatialGradientSq u Du z * ψ z)
      outer volume :=
    (suitableWeakSolution_energy_integrable hsol htest hpos).1.integrableOn
  have hsubset : inner ⊆ outer := by
    intro z hz
    change z.1 ∈ CKN.euclideanBall 0 R ∧ z.2 ∈ Ioo a b at hz
    change z.1 ∈ CKN.euclideanBall 0 (R + 1) ∧ z.2 ∈ Ioo (a - 2) 0
    constructor
    · have hr := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hz.1
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith only [hR])).2
      linarith only [hr]
    · exact ⟨by linarith only [hz.2.1], by linarith only [hz.2.2, hb]⟩
  have hmono : (∫ z in inner, spatialGradientSq u Du z * ψ z) ≤
      ∫ z in outer, spatialGradientSq u Du z * ψ z := by
    apply setIntegral_mono_set hint
    · filter_upwards [] with z
      exact mul_nonneg (by dsimp [spatialGradientSq]; positivity) (hpos z)
    · exact Filter.Eventually.of_forall hsubset
  have hinnerMeas : MeasurableSet inner := by
    change MeasurableSet (CKN.euclideanBall 0 R ×ˢ Ioo a b)
    exact (isOpen_euclideanBall 0 R).measurableSet.prod measurableSet_Ioo
  have heq : (∫ z in inner, spatialGradientSq u Du z) =
      ∫ z in inner, spatialGradientSq u Du z * ψ z := by
    apply setIntegral_congr_fun hinnerMeas
    intro z hz
    have hz' : z.1 ∈ CKN.euclideanBall 0 R ∧ z.2 ∈ Icc a b := by
      exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2.le⟩⟩
    change spatialGradientSq u Du z =
      spatialGradientSq u Du z * blowupEnergyCutoff R a b z
    rw [blowupEnergyCutoff_eq_one hR hb hz', mul_one]
  exact heq.le.trans hmono

/-- A bound for the three velocity-pressure terms gives the same bound,
up to the energy factor two, for the gradient on the inner cylinder. -/
theorem blowupEnergyCutoff_gradient_bound_of_majorant
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), b < 0 →
      ∀ {q : ℝ} {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
        (M : ℝ),
      IsSuitableWeakSolutionIntegrable
        (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) q u Du p 0 →
      IntegrableOn (fun z : ParabolicPoint =>
        (8 + 3 * C) * (vec3EuclideanNorm (u z)) ^ 2 +
          3 * C * (vec3EuclideanNorm (u z)) ^ 3 +
          6 * C * |p z| * vec3EuclideanNorm (u z))
        (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0)) volume →
      (∫ z in spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0),
        (8 + 3 * C) * (vec3EuclideanNorm (u z)) ^ 2 +
          3 * C * (vec3EuclideanNorm (u z)) ^ 3 +
          6 * C * |p z| * vec3EuclideanNorm (u z)) ≤ M →
      2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a b),
        spatialGradientSq u Du z) ≤ M := by
  obtain ⟨C, hC, hweighted⟩ := blowupEnergyCutoff_weighted_gradient_bound R hR
  refine ⟨C, hC, fun a b hb q u Du p M hsol hint hM => ?_⟩
  have hinner := blowupEnergyCutoff_inner_gradient_le R a b hR hb hsol
  have hw := hweighted a b hb hsol hint
  calc
    2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a b),
      spatialGradientSq u Du z) ≤
        2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 (R + 1))
          (Ioo (a - 2) 0),
          spatialGradientSq u Du z * blowupEnergyCutoff R a b z) := by
      gcongr
    _ ≤ ∫ z in spaceTimeSet (CKN.euclideanBall 0 (R + 1))
          (Ioo (a - 2) 0),
          (8 + 3 * C) * (vec3EuclideanNorm (u z)) ^ 2 +
            3 * C * (vec3EuclideanNorm (u z)) ^ 3 +
            6 * C * |p z| * vec3EuclideanNorm (u z) := hw
    _ ≤ M := hM

end ESS
