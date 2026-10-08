/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalPmProvider

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalProjectionInverseControl

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quantitative inverse control for the canonical projection

The coefficient-weighted projection is fixed at one inner and outer cube.
Its quantitative distance from the identity gives both bijectivity and a
uniform bound on the inverse slope.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

noncomputable section

private theorem euclideanNorm_sub_le_projection
    {d : ℕ} (x y : Vec d) :
    euclideanNorm (x - y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec]
  simpa only [WithLp.toLp_sub] using
    norm_sub_le (HilbertVec.ofVec x) (HilbertVec.ofVec y)

private theorem euclideanNorm_le_add_sub_projection
    {d : ℕ} (P : Vec d →ₗ[ℝ] Vec d) (e : Vec d) :
    euclideanNorm e ≤ euclideanNorm (P e - e) + euclideanNorm (P e) := by
  calc
    euclideanNorm e = euclideanNorm (P e - (P e - e)) := by
      congr 1
      abel
    _ ≤ euclideanNorm (P e) + euclideanNorm (P e - e) :=
      euclideanNorm_sub_le_projection _ _
    _ = euclideanNorm (P e - e) + euclideanNorm (P e) := add_comm _ _

/-- Below a dimension-only tail threshold, the canonical weighted projection
is bijective and its inverse has norm at most two. -/
theorem exists_canonicalFiniteCorrectorProjectionInverseControlThreshold
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n0 : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n0 →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
          (Phi : Vec d → NormalizedLocalH1Carrier d),
          IsFiniteAffineCorrectionJointLocalEquation a Phi →
          ∀ (q m : ℕ), n0 ≤ (q : ℤ) →
            ∀ hqm2 : q + 2 ≤ m,
            ∃ hT : Function.Injective
                (finiteTrialHarmonicGradientLinearMap a (by omega : q ≤ m)),
              let P := finiteCorrectorWeightedProjection a hCauchy
                (by omega : q ≤ m) hT
              Function.Bijective P ∧
                ∀ e : Vec d, euclideanNorm e ≤ 2 * euclideanNorm (P e) := by
  obtain ⟨Ctail, cTail, hCtail, hcTail, htail⟩ :=
    exists_jointFiniteCorrectorWeightedTailConstants d s hs hs_lt
  obtain ⟨cCoercive, hcCoercive, hcoercive⟩ :=
    exists_scalarIdentityGoodTailFiniteAffineSlopeAverageCoercivityThreshold
      d s hs hs_lt
  let C : ℝ := 4 * Real.sqrt (4 * (d : ℝ)) * Ctail
  let cSmall : ℝ := min (1 / 2 : ℝ) (1 / (4 * C))
  let c : ℝ := min cTail (min cCoercive cSmall)
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_neZero d
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by positivity))) hCtail
  have hcSmall0 : 0 < cSmall := by
    dsimp only [cSmall]
    exact lt_min (by norm_num) (div_pos zero_lt_one (mul_pos (by norm_num) hC))
  have hc0 : 0 < c := by
    dsimp only [c]
    exact lt_min hcTail.1 (lt_min hcCoercive.1 hcSmall0)
  have hc1 : c < 1 := (min_le_left cTail (min cCoercive cSmall)).trans_lt hcTail.2
  refine ⟨c, ⟨hc0, hc1⟩, ?_⟩
  intro a delta n0 hdelta hgood hCauchy Phi hPhi q m hnq hqm2
  have hdeltaTail : delta ∈ Set.Ioc (0 : ℝ) cTail :=
    ⟨hdelta.1, hdelta.2.trans (min_le_left _ _)⟩
  have hdeltaCoercive : delta ∈ Set.Ioc (0 : ℝ) cCoercive :=
    ⟨hdelta.1, hdelta.2.trans
      ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hdeltaSmall : delta ≤ cSmall := hdelta.2.trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hdeltaHalf : delta ≤ 1 / 2 := hdeltaSmall.trans (min_le_left _ _)
  have hdeltaInv : delta ≤ 1 / (4 * C) :=
    hdeltaSmall.trans (min_le_right _ _)
  let hT := finiteTrialHarmonicGradientLinearMap_injective
    a s delta cCoercive n0 hdeltaCoercive hgood hcoercive
      q m hnq hqm2
  let P := finiteCorrectorWeightedProjection a hCauchy
    (by omega : q ≤ m) hT
  have htailRaw := fun e ↦
    htail a delta n0 hdeltaTail hgood Phi hPhi e q m hnq hqm2
  have htailCanonical :=
    jointTargetHarmonicGradient_tail_of_jointLocalEquation
      a hCauchy Phi hPhi q m hqm2
        (Ctail * (1 + delta) * delta) htailRaw
  have hclose : ∀ e : Vec d,
      euclideanNorm (P e - e) ≤
        C * (1 + delta) * delta * euclideanNorm e := by
    intro e
    have hraw := finiteCorrectorWeightedProjection_sub_identity_le
      a hCauchy s delta cCoercive n0 hs hcCoercive.2.le
        hdeltaCoercive hgood hcoercive q m hnq hqm2
        (Ctail * (1 + delta) * delta)
        (mul_nonneg
          (mul_nonneg hCtail.le (add_nonneg zero_le_one hdelta.1.le))
          hdelta.1.le)
        htailCanonical e
    change euclideanNorm (P e - e) ≤
      C * (1 + delta) * delta * euclideanNorm e
    calc
      _ ≤ 4 * Real.sqrt (4 * (d : ℝ)) *
          (Ctail * (1 + delta) * delta) * euclideanNorm e := by
        simpa only [P, hT] using hraw
      _ = C * (1 + delta) * delta * euclideanNorm e := by
        dsimp only [C]
        ring
  let theta : ℝ := C * (1 + delta) * delta
  have hthetaHalf : theta ≤ 1 / 2 := by
    have hCle : C * delta ≤ 1 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left hdeltaInv hC.le
      calc
        C * delta ≤ C * (1 / (4 * C)) := hmul
        _ = 1 / 4 := by field_simp [hC.ne']
    have hone : 1 + delta ≤ 3 / 2 := by linarith only [hdeltaHalf]
    dsimp only [theta]
    calc
      C * (1 + delta) * delta = (1 + delta) * (C * delta) := by ring
      _ ≤ (3 / 2 : ℝ) * (1 / 4) :=
        mul_le_mul hone hCle (mul_nonneg hC.le hdelta.1.le) (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have htheta : theta < 1 := hthetaHalf.trans_lt (by norm_num)
  refine ⟨hT, finiteCorrectorWeightedProjection_bijective P theta htheta ?_, ?_⟩
  · intro e
    simpa only [theta] using hclose e
  · intro e
    have htri := euclideanNorm_le_add_sub_projection P e
    have hsmall := (hclose e).trans
      (mul_le_mul_of_nonneg_right hthetaHalf (euclideanNorm_nonneg e))
    linarith only [htri, hsmall, euclideanNorm_nonneg e,
      euclideanNorm_nonneg (P e)]

end

end Root
end HighContrast
end HCPolySupport
