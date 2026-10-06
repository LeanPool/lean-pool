/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatKernel

/-!
# Linearity of the forced heat response

The forced heat response is linear in the tensor wherever the defining kernel
integrals converge absolutely; for smooth compactly supported tensors they
always do. This is the linearity used for the bilinear response of
`lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The forced heat response is homogeneous. -/
theorem forcedHeat_smul (c : ℝ) (G : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
    (z : ParabolicPoint) : forcedHeat (c • G) z = c • forcedHeat G z := by
  funext i
  have hpt (p : ParabolicPoint) : ∑ j : Fin 3, heatKernelSpaceDerivative p.1 p.2 j *
      (c • G) i j (z.1 - p.1, z.2 - p.2) = c * ∑ j : Fin 3,
        heatKernelSpaceDerivative p.1 p.2 j * G i j (z.1 - p.1, z.2 - p.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change _ * (c * G i j _) = c * (_ * G i j _)
    ring
  change (∫ p : ParabolicPoint, ∑ j : Fin 3, heatKernelSpaceDerivative p.1 p.2 j *
      (c • G) i j (z.1 - p.1, z.2 - p.2)) = c * ∫ p : ParabolicPoint, ∑ j : Fin 3,
        heatKernelSpaceDerivative p.1 p.2 j * G i j (z.1 - p.1, z.2 - p.2)
  simp_rw [hpt]
  exact integral_const_mul _ _

/-- The forced heat response is additive at every point where the kernel
integrals of both tensors converge absolutely. -/
theorem forcedHeat_add {G G' : Fin 3 → Fin 3 → ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hG : ∀ i j, Integrable (fun p : ParabolicPoint =>
      heatKernelSpaceDerivative p.1 p.2 j * G i j (z.1 - p.1, z.2 - p.2)))
    (hG' : ∀ i j, Integrable (fun p : ParabolicPoint =>
      heatKernelSpaceDerivative p.1 p.2 j * G' i j (z.1 - p.1, z.2 - p.2))) :
    forcedHeat (G + G') z = forcedHeat G z + forcedHeat G' z := by
  funext i
  have hpt (p : ParabolicPoint) : ∑ j : Fin 3, heatKernelSpaceDerivative p.1 p.2 j *
      (G + G') i j (z.1 - p.1, z.2 - p.2) =
      (∑ j : Fin 3, heatKernelSpaceDerivative p.1 p.2 j * G i j (z.1 - p.1, z.2 - p.2)) +
        ∑ j : Fin 3, heatKernelSpaceDerivative p.1 p.2 j * G' i j (z.1 - p.1, z.2 - p.2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    change _ * (G i j _ + G' i j _) = _
    ring
  change (∫ p : ParabolicPoint, ∑ j : Fin 3, heatKernelSpaceDerivative p.1 p.2 j *
      (G + G') i j (z.1 - p.1, z.2 - p.2)) =
    (∫ p : ParabolicPoint, ∑ j : Fin 3,
      heatKernelSpaceDerivative p.1 p.2 j * G i j (z.1 - p.1, z.2 - p.2)) +
    ∫ p : ParabolicPoint, ∑ j : Fin 3,
      heatKernelSpaceDerivative p.1 p.2 j * G' i j (z.1 - p.1, z.2 - p.2)
  simp_rw [hpt]
  exact integral_add (integrable_finsetSum _ fun j _ => hG i j)
    (integrable_finsetSum _ fun j _ => hG' i j)

/-- For a smooth compactly supported tensor the kernel integrals defining the
forced heat response converge absolutely at every point. -/
theorem forcedHeat_integrand_integrable {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p))
    (z : ParabolicPoint) (i j : Fin 3) :
    Integrable (fun p : ParabolicPoint =>
      heatKernelSpaceDerivative p.1 p.2 j * G i j (z.1 - p.1, z.2 - p.2)) := by
  have h := (heatKernelSpaceDerivative_locallyIntegrable j).integrable_smul_right_of_hasCompactSupport
    ((hG i j).continuous.comp (continuous_const.sub continuous_id))
    ((hGc i j).comp_homeomorph (Homeomorph.subLeft (show Vec3 × ℝ from z)))
  exact h

end ESS

end
