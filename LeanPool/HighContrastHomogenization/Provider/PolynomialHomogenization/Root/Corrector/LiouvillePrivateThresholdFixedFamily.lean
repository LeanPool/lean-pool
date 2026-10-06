/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.LiouvillePrivateThresholdRestart

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.LiouvillePrivateThresholdFixedFamily

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Private Liouville restart for a fixed joint corrector family

Restarting the summable error tail changes only its first index.  The unique
joint corrector limit already retained by the physical family is therefore
kept fixed throughout the two inclusions.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set Filter

noncomputable section

/-- The private threshold restart supplies both scalar Liouville inclusions
for the particular joint corrector family supplied by the root. -/
theorem scalarIdentityGoodTail_liouvilleDoubleInclusion_fixedFamily_after_restart
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2)
    {b : CoeffField d} (hb : IsAELocallyUniformlyElliptic b)
    (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ)
    (hgood : ScalarIdentityGoodTail a s delta n)
    (hcoeff : ∀ q : ℕ,
      Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a
        =ᵐ[volumeMeasureOn (localGradientCube d q)] b)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation a
      (finiteAffineCorrectionJointLocalLimit a hCauchy)) :
    ∀ theta : ℝ, theta ∈ Set.Ioo (0 : ℝ) 1 →
      ( ∀ {v : Vec d → ℝ} {Dv : Vec d → Vec d},
          MemLiouvilleClass b theta v Dv →
          ∃ (e : Vec d) (c₀ : ℝ),
            v =ᵐ[volume] fun x ↦ vecDot e x +
              (finiteAffineCorrectionJointLocalLimit a hCauchy e).globalValueRepresentative x + c₀) ∧
        ∀ (e : Vec d) (c₀ : ℝ),
          MemLiouvilleClass b theta
            (fun x ↦ vecDot e x +
              (finiteAffineCorrectionJointLocalLimit a hCauchy e).globalValueRepresentative x + c₀)
            (fun x ↦ e +
              (finiteAffineCorrectionJointLocalLimit a hCauchy e).globalGradientRepresentative x) := by
  intro theta htheta
  obtain ⟨_K, cForward, _hK, hcForward, hforward⟩ :=
    exists_scalarIdentityGoodTailAffineCorrectorMemLiouvilleConstant
      d s hs hs_lt
  obtain ⟨cReverse, hcReverse, hreverse⟩ :=
    exists_scalarIdentityGoodTailLiouvilleReverseForJointEquationConstant
      d s theta hs hs_lt htheta.2
  let c : ℝ := min cForward cReverse
  have hc : c ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨lt_min hcForward.1 hcReverse.1, ?_⟩
    exact (min_le_left cForward cReverse).trans_lt hcForward.2
  obtain ⟨n', _hnn', hsmall⟩ :=
    ScalarIdentityGoodTail.exists_restart_at_tolerance hgood hc.1
  have hdForward : c ∈ Set.Ioc (0 : ℝ) cForward :=
    ⟨hc.1, min_le_left _ _⟩
  have hdReverse : c ∈ Set.Ioc (0 : ℝ) cReverse :=
    ⟨hc.1, min_le_right _ _⟩
  constructor
  · intro v Dv hv
    exact hreverse a c n' hdReverse hsmall
      (finiteAffineCorrectionJointLocalLimit a hCauchy) hPhi
      hb hcoeff hv
  · intro e c₀
    exact hforward a c n' hdForward hsmall hb hcoeff hCauchy e c₀ theta htheta.1

end

end Root
end HighContrast
end HCPolySupport
