/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalRepresentative
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorInvariantEvent
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorJointLimit
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalLimit
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LocalGradientTranslation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.EquivariantPhysicalCorrectorFamilyWrapper

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Global representatives of equivariant corrector families

Projective local-gradient covariance determines covariance of the canonical
global representatives.  This module combines that passage with the exact
slope algebra of normalized local carriers and the zero extension away from
an invariant construction event.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem ae_eq_volume_of_localGradientCubes
    {E : Type*} {f g : Vec d → E}
    (h : ∀ q : ℕ, f =ᵐ[volumeMeasureOn (localGradientCube d q)] g) :
    f =ᵐ[volume] g := by
  have hall : ∀ᵐ x ∂volume, ∀ q : ℕ,
      x ∈ localGradientCube d q → f x = g x := by
    apply ae_all_iff.2
    intro q
    exact (ae_restrict_iff' (isOpen_openCubeSet
      (originCube d (q : ℤ))).measurableSet).mp (h q)
  filter_upwards [hall] with x hx
  have hxUnion : x ∈ ⋃ q, localGradientCube d q := by
    rw [iUnion_localGradientCube]
    trivial
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxUnion
  exact hx q hxq

/-- Addition of normalized carriers is addition of their canonical global
gradient representatives, almost everywhere. -/
theorem NormalizedLocalH1Carrier.globalGradientRepresentative_addCarrier
    (z w : NormalizedLocalH1Carrier d) :
    (NormalizedLocalH1Carrier.addCarrier z w).globalGradientRepresentative
      =ᵐ[volume] fun x ↦
        z.globalGradientRepresentative x + w.globalGradientRepresentative x := by
  apply ae_eq_volume_of_localGradientCubes
  intro n
  have hsum :=
    NormalizedLocalH1Carrier.globalGradientRepresentative_ae_eq_component
      (NormalizedLocalH1Carrier.addCarrier z w) n
  simp only [NormalizedLocalH1Carrier.addCarrier_gradientComponent] at hsum
  filter_upwards [
    hsum,
    z.globalGradientRepresentative_ae_eq_component n,
    w.globalGradientRepresentative_ae_eq_component n,
    coeFn_hilbertVectorL2ToVectorL2
      ((z.gradientComponent n) + (w.gradientComponent n)),
    Lp.coeFn_add (z.gradientComponent n) (w.gradientComponent n),
    coeFn_hilbertVectorL2ToVectorL2 (z.gradientComponent n),
    coeFn_hilbertVectorL2ToVectorL2 (w.gradientComponent n)] with
      x hsum hz hw hconv hadd hzconv hwconv
  rw [hsum, hconv, hadd, Pi.add_apply]
  change (((z.gradientComponent n : Vec d → HilbertVec d) x).toVec) +
      (((w.gradientComponent n : Vec d → HilbertVec d) x).toVec) = _
  rw [← hzconv, ← hwconv, ← hz, ← hw]

/-- Scalar multiplication of a normalized carrier is scalar multiplication
of its canonical global gradient representative, almost everywhere. -/
theorem NormalizedLocalH1Carrier.globalGradientRepresentative_smulCarrier
    (c : ℝ) (z : NormalizedLocalH1Carrier d) :
    (NormalizedLocalH1Carrier.smulCarrier c z).globalGradientRepresentative
      =ᵐ[volume] fun x ↦ c • z.globalGradientRepresentative x := by
  apply ae_eq_volume_of_localGradientCubes
  intro n
  have hscaled :=
    NormalizedLocalH1Carrier.globalGradientRepresentative_ae_eq_component
      (NormalizedLocalH1Carrier.smulCarrier c z) n
  simp only [NormalizedLocalH1Carrier.smulCarrier_gradientComponent] at hscaled
  filter_upwards [
    hscaled,
    z.globalGradientRepresentative_ae_eq_component n,
    coeFn_hilbertVectorL2ToVectorL2 (c • z.gradientComponent n),
    Lp.coeFn_smul c (z.gradientComponent n),
    coeFn_hilbertVectorL2ToVectorL2 (z.gradientComponent n)] with
      x hscaled hz hconv hsmul hzconv
  rw [hscaled, hconv, hsmul, Pi.smul_apply]
  change c • (((z.gradientComponent n : Vec d → HilbertVec d) x).toVec) = _
  rw [← hzconv, ← hz]

end

end Root
end HighContrast
end HCPolySupport
