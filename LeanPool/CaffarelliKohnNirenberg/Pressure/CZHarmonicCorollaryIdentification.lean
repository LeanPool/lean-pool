/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicCorollaryParts
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZUnconditional

/-!
# Identifying the Calderón–Zygmund part with `-RᵢRⱼ(η Uᵢⱼ)` (`cor:CZ-harmonic`)

In `eq:CZ-harmonic` the Calderón–Zygmund part is `p_CZ = p₁ = -RᵢRⱼ(η Uᵢⱼ)`.
The repository realizes the operator `-RᵢRⱼ` as the `L^{3/2}` extension
`pressureSecondExtensionOperator` built on the canonical `L²` inputs and their
weak endpoint certificate, so the identity reads
`p_CZ(·, t) =ᵐ T (η U(·, t))`.

The identification is the Liouville step: `p₁` and the extension solve the same
distributional equation `Δ w = ∂ᵢ∂ⱼ (η Uᵢⱼ)`, and a difference of linear growth
in `L^{3/2}` on the round balls is constant, hence zero.  The distributional
identity, its integrability and the residual growth enter in the exact binder
shapes in which they are currently available.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
noncomputable section

namespace CKN

open CKN.Foundation.Euclidean

/-- The `-RᵢRⱼ(η Uᵢⱼ)` of `eq:CZ-harmonic`, as the canonical `L^{3/2}`
extension applied to the tensor source `η U` at time `s`. -/
@[expose]
def czPressureRieszPart (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3)
    (c : ℝ → Vec3) (s : ℝ) : Vec3 → ℝ :=
  pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
    (czPressureSource η u c s)

/-- The extension of an `L^{3/2}` tensor source pairs integrably with the
Laplacian of every smooth compactly supported test. -/
theorem czPressureRieszPart_laplacian_integrable
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hG : ∀ i j, MemLp (czPressureSource η u c s i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun x => czPressureRieszPart η u c s x *
      spatialLaplacian ψ x) volume := by
  let _ : ENNReal.HolderConjugate (ENNReal.ofReal (3 / 2 : ℝ))
      (ENNReal.ofReal (3 : ℝ)) :=
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      Real.HolderConjugate (3 / 2 : ℝ) 3).ennrealOfReal
  have hlap : MemLp (spatialLaplacian ψ) (ENNReal.ofReal (3 : ℝ)) volume :=
    (contDiff_spatialLaplacian_smooth hψ).continuous.memLp_of_hasCompactSupport
      (CKN.Foundation.Heat.laplacian_compact_support_global hψc)
  exact (pressureSecondExtension_memLp rieszSecondL2Input
    rieszSecondL2_weak_type hG).integrable_mul hlap

/-- `p_CZ(·, s) = -RᵢRⱼ(η Uᵢⱼ)(·, s)` almost everywhere, from the whole-space
distributional identity of `p₁` and the linear growth of the residual. -/
theorem czHarmonic_czPart_eq_rieszPart
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {s C : ℝ}
    (hC : 0 ≤ C)
    (hG : ∀ i j, MemLp (czPressureSource η u c s i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hP1 : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => czPressurePart η u c p f s x *
        spatialLaplacian ψ x) volume →
      ∫ x, czPressurePart η u c p f s x * spatialLaplacian ψ x =
        pressureSecondPairing (czPressureSource η u c s) ψ)
    (hP1Int : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => czPressurePart η u c p f s x *
        spatialLaplacian ψ x) volume)
    (hmem : ∀ R : ℝ, 0 < R →
      MemLp (fun x => czPressurePart η u c p f s x -
        czPressureRieszPart η u c s x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) R)))
    (hgrowth : ∀ R : ℝ, 0 < R →
      lpNorm (fun x => czPressurePart η u c p f s x -
        czPressureRieszPart η u c s x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R)) :
    czPressurePart η u c p f s =ᵐ[volume] czPressureRieszPart η u c s := by
  exact pressureP1_hident_of_pressureSecondExtension
    rieszSecondL2Input rieszSecondL2_weak_type hC hG hP1 hP1Int
    (fun ψ hψ hψc => czPressureRieszPart_laplacian_integrable hG hψ hψc)
    hmem hgrowth

end CKN
