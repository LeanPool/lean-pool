/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityProducts
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevMollify

/-!
# Unconditional vorticity product estimates

The smooth compactly supported density theorem supplies the approximation
hypothesis in the whole-space and local estimates of `lem:vorticity-products`.
-/

public section

open Filter MeasureTheory Set Topology
open CKN CKN.Foundation.Parabolic
open scoped ENNReal


noncomputable section

namespace ESS.VorticityProductsFinal

private theorem vorticityProducts_smoothApprox
    {ι : Type} [Fintype ι] {m : ℕ} {f : ι → Vec3 → ℝ}
    {D : ι → List (Fin 3) → Vec3 → ℝ}
    (h : ∀ i, IsSobolevFamilyOn m univ (f i) (D i)) :
    ∃ g : ℕ → ι → Vec3 → ℝ,
      (∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i)) ∧
      (∀ n i, HasCompactSupport (g n i)) ∧
      (∀ i (α : List (Fin 3)), α.length ≤ m →
        Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D i α) 2 volume)
          atTop (𝓝 0)) ∧
      ∀ M : ℝ, (∀ᵐ x ∂volume, Real.sqrt (∑ i, f i x ^ 2) ≤ M) →
        ∀ n x, Real.sqrt (∑ i, g n i x ^ 2) ≤ M := by
  exact sobolevFamily_smooth_approx (D := fun α i => D i α) h

/-- The unconditional order-two product estimate in `lem:vorticity-products`. -/
theorem vorticityProducts_H2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Vec3 → Vec3, HasCompactSupport v →
      hNormOn 2 univ (vecComponents v) < ⊤ →
      eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤ volume < ⊤ →
      hNormOn 2 univ (tensorSquareComponents v) ≤
        ENNReal.ofReal C * eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤ volume *
          hNormOn 2 univ (vecComponents v) := by
  exact ESS.vorticityProducts_H2 (hApprox := vorticityProducts_smoothApprox)

/-- The unconditional order-three product estimate in `lem:vorticity-products`. -/
theorem vorticityProducts_H3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Vec3 → Vec3,
      hNormOn 3 univ (vecComponents v) < ⊤ →
      hNormOn 3 univ (tensorSquareComponents v) ≤
        ENNReal.ofReal C * hNormOn 2 univ (vecComponents v) *
          hNormOn 3 univ (vecComponents v) := by
  exact ESS.vorticityProducts_H3 (hApprox := vorticityProducts_smoothApprox)

/-- The unconditional local product estimates in `lem:vorticity-products`. -/
theorem vorticityProducts_local {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (v : Vec3 → Vec3),
      (hNormOn 2 (vec3Ball x₀ R) (vecComponents v) < ⊤ →
        eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤
          (volume.restrict (vec3Ball x₀ R)) < ⊤ →
        hNormOn 2 (vec3Ball x₀ r) (tensorSquareComponents v) ≤
          ENNReal.ofReal C *
            eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤
              (volume.restrict (vec3Ball x₀ R)) *
            hNormOn 2 (vec3Ball x₀ R) (vecComponents v)) ∧
      (hNormOn 3 (vec3Ball x₀ R) (vecComponents v) < ⊤ →
        hNormOn 3 (vec3Ball x₀ r) (tensorSquareComponents v) ≤
          ENNReal.ofReal C * hNormOn 2 (vec3Ball x₀ R) (vecComponents v) *
            hNormOn 3 (vec3Ball x₀ R) (vecComponents v)) := by
  exact ESS.vorticityProducts_local (hApprox := vorticityProducts_smoothApprox)
    hr hrR

end ESS.VorticityProductsFinal
