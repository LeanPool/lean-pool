/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocity
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedPressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegPressureL2
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationPressure

/-!
# The Riesz pressure identity (R4)

For any velocity whose slices represent a curve `U` of spatial `L²` fields,
the canonical pressure `forcedQuadPressure` of `U` is, on each slice, the
Riesz pressure of the regularized tensor `(J_ε u)_i u_j`, and it satisfies the
Laplacian identity of `thm:regularised` (R4).
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- `thm:regularised` (R4) for a velocity whose slices represent a curve. -/
theorem regR12_R4 (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (U : ℝ → RealVectorL2) (u : ParabolicPoint → Vec3) (t : ℝ)
    (hrep : (fun x : Vec3 => u (x, t)) =ᵐ[volume] realVectorL2Representative (U t)) :
    ∃ hF : ∀ i j : Fin 3, MemLp
        (fun x : Vec3 =>
          CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
            u (x, t) j) (ENNReal.ofReal (2 : ℝ)) volume,
      (fun x : Vec3 => forcedQuadPressure ρ ε hε U (x, t)) =ᵐ[volume]
        CKN.Leray.rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hF i j).toLp
            (fun x : Vec3 =>
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j)) ∧
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        (∫ x : Vec3, forcedQuadPressure ρ ε hε U (x, t) * spatialLaplacian ψ x) =
          -∑ i : Fin 3, ∑ j : Fin 3,
            ∫ x : Vec3,
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j * mixedSecond ψ i j x := by
  have hF : ∀ i j : Fin 3, MemLp
      (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j)
      (ENNReal.ofReal (2 : ℝ)) volume := fun i j =>
    (memLp_forcedTensorComp (regularizedMildTensor ρ ε hε (U t)) i j).ae_eq
      (regPressureTensorSlice_ae_eq ρ ε hε hrep i j).symm
  have hEq : (fun i j => (hF i j).toLp (fun x : Vec3 =>
      regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j)) =
      forcedPressureTensorLp (regularizedMildTensor ρ ε hε (U t)) := by
    funext i j
    exact MemLp.toLp_congr _ _ (regPressureTensorSlice_ae_eq ρ ε hε hrep i j)
  have hslice : (fun x : Vec3 => forcedQuadPressure ρ ε hε U (x, t)) =ᵐ[volume]
      rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
        (fun i j => (hF i j).toLp (fun x : Vec3 =>
          regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j)) := by
    rw [hEq]
    exact forcedQuadPressure_slice ρ ε hε _ t
  refine ⟨hF, hslice, fun ψ hψ hψc => ?_⟩
  refine (integral_congr_ae ?_).trans (regularisedPressureSlice_riesz_laplacian_pairing
    (fun i j x => regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j) hF ψ hψ hψc)
  filter_upwards [hslice] with x hx
  rw [hx]

end CKN.Leray
