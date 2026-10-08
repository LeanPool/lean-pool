/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleAdditiveConstant
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleFixedCubeExcess

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleReverseClassification

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Reverse Liouville classification

This module composes fixed-cube excess vanishing, compact slope selection,
canonical slope compatibility, and additive-gauge recovery.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

/-- Deterministic composition of the global-slope and additive-constant
engines. -/
theorem exists_affineCorrectorRepresentation_of_liouvilleFixedCubeExcess
    {d : ℕ} [NeZero d] {s : ℝ}
    {a : Book.Ch02.TriadicCoeffFamily d} {delta c : ℝ} {n : ℤ}
    (hthreshold : c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c → ScalarIdentityGoodTail a s delta n →
        ∀ (q t : ℕ), n ≤ (q : ℤ) → ∀ e : Vec d,
          euclideanNorm e ≤ 2 * euclideanNorm
            (cubeAverageVec (originCube d (q : ℤ))
              (finiteAffineSolution a ((q + t + 2 : ℕ) : ℤ) e).toH1.grad))
    (hcoercive : ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
      (e : Vec d) (q : ℕ), n ≤ (q : ℤ) →
      euclideanNorm e ≤ 2 * euclideanNorm
        (localGradientClassAverage
          ((show LocalGradientL2 d q from
              constantGradientOnOriginCube e (q : ℤ)) +
            (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q)))
    (hdelta : delta ∈ Set.Ioc (0 : ℝ) c)
    (hgood : ScalarIdentityGoodTail a s delta n)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (u : ∀ p : ℕ,
      Book.Ch03.CubeSolution (originCube d ((p : ℤ) - 2)) a)
    (v : Vec d → ℝ) (Dv : Vec d → Vec d)
    (hu : ∀ p, (u p).toH1.toFun = v ∧ (u p).toH1.grad = Dv)
    (hexcess : ∀ k : ℤ, n ≤ k →
      Tendsto
        (fun p : ℕ => finiteAffineGradientExcess a k ((p : ℤ) - 2) (u p))
        atTop (nhds 0)) :
    ∃ (e : Vec d) (c₀ : ℝ),
      v =ᵐ[volume] fun x => vecDot e x +
        (finiteAffineCorrectionJointLocalLimit a hCauchy e).globalValueRepresentative x + c₀ := by
  obtain ⟨e, he⟩ := exists_common_jointSlope_of_liouvilleFixedCubeExcess
    hthreshold hcoercive hdelta hgood hCauchy u Dv (fun p => (hu p).2) hexcess
  obtain ⟨c₀, hc₀⟩ := exists_additiveConstant_of_common_jointSlope
    hCauchy u v (fun p => (hu p).1) e he
  exact ⟨e, c₀, hc₀⟩

/-- Quantitative reverse Liouville classification under one sufficiently
small scalar good-tail threshold. -/
theorem exists_scalarIdentityGoodTailLiouvilleReverseConstant
    (d : ℕ) [NeZero d] (s theta : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) (htheta : theta < 1) :
    ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        (∃! Phi : Vec d → NormalizedLocalH1Carrier d,
          IsFiniteAffineCorrectionJointLocalEquation a Phi) ∧
        ∀ {b : CoeffField d}, IsAELocallyUniformlyElliptic b →
          (∀ q : ℕ,
            Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a
              =ᵐ[volumeMeasureOn (openCubeSet (originCube d (q : ℤ)))] b) →
          ∀ {v : Vec d → ℝ} {Dv : Vec d → Vec d},
            MemLiouvilleClass b theta v Dv →
            ∃ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
              (e : Vec d) (c₀ : ℝ),
              v =ᵐ[volume] fun x => vecDot e x +
                (finiteAffineCorrectionJointLocalLimit a hCauchy e).globalValueRepresentative x
                  + c₀ := by
  obtain ⟨cFinite, hcFinite, hFinite⟩ :=
    exists_scalarIdentityGoodTailFiniteAffineSlopeAverageCoercivityThreshold
      d s hs hs_lt
  obtain ⟨cCanonical, hcCanonical, hCanonical⟩ :=
    exists_scalarIdentityGoodTailCanonicalLocalSlopeCoercivityThreshold
      d s hs hs_lt
  obtain ⟨cCauchy, hcCauchy, hCauchy⟩ :=
    exists_finiteAffineCorrectionLocalCauchyThreshold d s hs hs_lt
  obtain ⟨eta, Cfamily, cFixed, Cdec, _hetaMax, _hetaOne,
      _hCfamily, hcFixed, _hCdec, hFixed⟩ :=
    exists_scalarIdentityLiouvilleFixedCubeExcessVanishingConstants
      d s theta hs hs_lt htheta
  let c := min cFinite (min cCanonical (min cCauchy cFixed))
  have hc : c ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨lt_min hcFinite.1 (lt_min hcCanonical.1
      (lt_min hcCauchy.1 hcFixed.1)), ?_⟩
    exact (min_le_left cFinite _).trans_lt hcFinite.2
  refine ⟨c, hc, ?_⟩
  intro a delta n hdelta hgood
  have hdFinite : delta ∈ Set.Ioc (0 : ℝ) cFinite :=
    ⟨hdelta.1, hdelta.2.trans (min_le_left _ _)⟩
  have hdCanonical : delta ∈ Set.Ioc (0 : ℝ) cCanonical :=
    ⟨hdelta.1, hdelta.2.trans
      ((min_le_right cFinite _).trans (min_le_left _ _))⟩
  have hdCauchy : delta ∈ Set.Ioc (0 : ℝ) cCauchy :=
    ⟨hdelta.1, hdelta.2.trans
      ((min_le_right cFinite _).trans
        ((min_le_right cCanonical _).trans (min_le_left _ _)))⟩
  have hdFixed : delta ∈ Set.Ioc (0 : ℝ) cFixed :=
    ⟨hdelta.1, hdelta.2.trans
      ((min_le_right cFinite _).trans
        ((min_le_right cCanonical _).trans (min_le_right _ _)))⟩
  have hfixedData := hFixed a delta n hdFixed hgood
  refine ⟨hfixedData.1, ?_⟩
  intro b hb hcoeff v Dv hv
  obtain ⟨u, hu, hexcess⟩ := hfixedData.2 hb hcoeff hv
  let hloc : FiniteAffineCorrectionLocalCauchy a :=
    hCauchy a delta n hdCauchy hgood
  obtain ⟨e, c₀, hrep⟩ :=
    exists_affineCorrectorRepresentation_of_liouvilleFixedCubeExcess
      ⟨hcFinite, hFinite⟩
      (hCanonical a delta n hdCanonical hgood)
      hdFinite hgood hloc u v Dv hu hexcess
  exact ⟨hloc, e, c₀, hrep⟩

/-- Reverse classification stated for any joint corrector family
satisfying the frozen local-limit/equation predicate. -/
theorem exists_scalarIdentityGoodTailLiouvilleReverseForJointEquationConstant
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
                =ᵐ[volumeMeasureOn (openCubeSet (originCube d (q : ℤ)))] b) →
            ∀ {v : Vec d → ℝ} {Dv : Vec d → Vec d},
              MemLiouvilleClass b theta v Dv →
              ∃ (e : Vec d) (c₀ : ℝ),
                v =ᵐ[volume] fun x =>
                  vecDot e x + (Phi e).globalValueRepresentative x + c₀ := by
  obtain ⟨c, hc, hreverse⟩ :=
    exists_scalarIdentityGoodTailLiouvilleReverseConstant
      d s theta hs hs_lt htheta
  refine ⟨c, hc, ?_⟩
  intro a delta n hdelta hgood Phi hPhi b hb hcoeff v Dv hv
  have hdata := hreverse a delta n hdelta hgood
  obtain ⟨hCauchy, e, c₀, hrep⟩ := hdata.2 hb hcoeff hv
  have hPhiLimit : IsFiniteAffineCorrectionJointLocalLimit a Phi := by
    simpa only [IsFiniteAffineCorrectionJointLocalLimit] using hPhi.1
  have hPhiEq : Phi = finiteAffineCorrectionJointLocalLimit a hCauchy :=
    (isFiniteAffineCorrectionJointLocalLimit_iff_eq a hCauchy Phi).mp hPhiLimit
  rw [← hPhiEq] at hrep
  exact ⟨e, c₀, hrep⟩

end

end HighContrast
end HCPolySupport
