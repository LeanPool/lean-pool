/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleGradientUniqueness
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleReverseClassification

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleReverseValueGradient

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Reverse Liouville classification with gradient readout

The available reverse theorem identifies the scalar representative. Uniformly
elliptic weak-gradient uniqueness upgrades that result to the global gradient
identity needed by phase covariance.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set Filter

noncomputable section

/-- Reverse Liouville classification for a joint corrector
family, augmented with the globally almost-everywhere gradient identity. -/
theorem exists_scalarIdentityGoodTailLiouvilleReverseValueGradientForJointEquationConstant
    (d : ℕ) [NeZero d] (s theta : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) (htheta : theta < 1) :
    ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (Phi : Vec d → NormalizedLocalH1Carrier d),
          IsFiniteAffineCorrectionJointLocalEquation a Phi →
          ∀ {b : CoeffField d}, IsAELocallyUniformlyElliptic b →
            (∀ q : ℕ,
              Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a
                =ᵐ[volume.restrict (localGradientCube d q)] b) →
            ∀ {v : Vec d → ℝ} {Dv : Vec d → Vec d},
              MemLiouvilleClass b theta v Dv →
              ∃ (e : Vec d) (c0 : ℝ),
                (v =ᵐ[volume] fun x =>
                  vecDot e x + (Phi e).globalValueRepresentative x + c0) ∧
                (Dv =ᵐ[volume] fun x =>
                  e + (Phi e).globalGradientRepresentative x) := by
  obtain ⟨c, hc, hreverse⟩ :=
    exists_scalarIdentityGoodTailLiouvilleReverseForJointEquationConstant
      d s theta hs hs_lt htheta
  refine ⟨c, hc, ?_⟩
  intro a delta n hdelta hgood Phi hPhi b hb hcoeff v Dv hv
  obtain ⟨e, c0, hvalue⟩ :=
    hreverse a delta n hdelta hgood Phi hPhi hb hcoeff hv
  have hcanonical : MemH1sLoc b
      (fun x => vecDot e x + (Phi e).globalValueRepresentative x + c0)
      (fun x => e + (Phi e).globalGradientRepresentative x) :=
    (Phi e).memH1sLoc_affineAdd_globalRepresentatives hb e c0
  have hgradient := gradient_ae_eq_of_memH1sLoc_of_value_ae
    hb hv.1 hcanonical hvalue
  exact ⟨e, c0, hvalue, hgradient⟩

end

end HighContrast
end HCPolySupport
