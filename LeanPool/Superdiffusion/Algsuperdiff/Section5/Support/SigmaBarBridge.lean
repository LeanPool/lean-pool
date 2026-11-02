/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionBounds

/-!
# SigmaBarBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Comparing the generator and canonical running diffusivities

The generator-renormalization theorem introduces a positive scalar through an
existential quantifier, while the localized quantities use
`Annealed.sigmaBar`.  Both scalars satisfy the same relative approximation to
the explicit square-root scale.  The triangle inequality therefore compares
the existential scalar directly with the canonical one.

-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport

noncomputable section

/-- Any positive scalar satisfying the generator approximation is close to the
canonical running diffusivity.  This form keeps the comparison attached to the
same scalar used by a caller's other conclusions. -/
theorem generatorSigmaBar_close_to_sigmaBar_of_approx (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) :
    ∃ gamma0 Cind : ℝ, 0 < gamma0 ∧ 0 < Cind ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ (m : ℤ) (Cgen sigmaBarM : ℝ), 0 < Cgen → 0 < sigmaBarM →
          |sigmaBarM -
              Real.sqrt (M.nu ^ (2 : ℕ) +
                cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
            Cgen * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM →
          |sigmaBarM - (Annealed.sigmaBar M m : ℝ)| ≤
            max Cgen (Cind * cstar⁻¹ ^ (2 : ℕ)) *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (sigmaBarM + (Annealed.sigmaBar M m : ℝ)) := by
  obtain ⟨Cind, hCind, hind⟩ := Algsuperdiff.Frozen.Section3.induction_bounds d
  have hregime : 0 < (Cind⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ) := by positivity
  refine ⟨(Cind⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ), Cind, hregime, hCind, ?_⟩
  intro M hcs hgamma m Cgen sigmaBarM hCgen hsigma hsigmaApprox
  have hgammaInd : M.gamma ≤ (Cind⁻¹) ^ (10 : ℕ) *
      (Disorder.cstar M) ^ (10 : ℕ) := by simpa only [hcs] using hgamma
  have hcanonical := (hind M hgammaInd).2 m
  rw [hcs] at hcanonical
  let target : ℝ := Real.sqrt (M.nu ^ (2 : ℕ) +
    cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))
  have htri : |sigmaBarM - (Annealed.sigmaBar M m : ℝ)| ≤
      |sigmaBarM - target| + |(Annealed.sigmaBar M m : ℝ) - target| := by
    calc
      |sigmaBarM - (Annealed.sigmaBar M m : ℝ)| =
          |(sigmaBarM - target) - ((Annealed.sigmaBar M m : ℝ) - target)| := by ring_nf
      _ ≤ _ := abs_sub _ _
  have hfactor : 0 ≤ Real.sqrt M.gamma * |Real.log M.gamma| :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hcanonicalPos : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hgenBase := mul_le_mul_of_nonneg_right
    (le_max_left Cgen (Cind * cstar⁻¹ ^ (2 : ℕ))) hfactor
  have hindBase := mul_le_mul_of_nonneg_right
    (le_max_right Cgen (Cind * cstar⁻¹ ^ (2 : ℕ))) hfactor
  calc
    |sigmaBarM - (Annealed.sigmaBar M m : ℝ)| ≤
        |sigmaBarM - target| + |(Annealed.sigmaBar M m : ℝ) - target| := htri
    _ ≤ Cgen * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM +
        (Cind * cstar⁻¹ ^ (2 : ℕ)) * Real.sqrt M.gamma * |Real.log M.gamma| *
          (Annealed.sigmaBar M m : ℝ) := add_le_add hsigmaApprox hcanonical
    _ ≤ max Cgen (Cind * cstar⁻¹ ^ (2 : ℕ)) *
          Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM +
        max Cgen (Cind * cstar⁻¹ ^ (2 : ℕ)) *
          Real.sqrt M.gamma * |Real.log M.gamma| *
            (Annealed.sigmaBar M m : ℝ) := by
      have hgenTerm := mul_le_mul_of_nonneg_right hgenBase hsigma.le
      have hindTerm := mul_le_mul_of_nonneg_right hindBase hcanonicalPos.le
      simpa only [mul_assoc] using add_le_add hgenTerm hindTerm
    _ = max Cgen (Cind * cstar⁻¹ ^ (2 : ℕ)) *
        Real.sqrt M.gamma * |Real.log M.gamma| *
          (sigmaBarM + (Annealed.sigmaBar M m : ℝ)) := by ring

end

end Algsuperdiff.Section5.Support
