/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.FiniteQAggregateBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.LowerLegProfile

/-!
# FiniteQPresplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The conditional finite-`q` pre-split producer

Its analytic input is pointwise and per depth: the normalized Chapter 4
descendant maximum is at most the deterministic profile `Cprof * 3^(gamma n)`
plus a nonnegative random remainder.  The split is kept inside the defining
`ell^(q/2)` aggregate.

The total `q/2`-power summability needed by the aggregate comparison is proved
below from the two separate lanes.  It is deliberately not an interface
hypothesis.  The random lane is linearized only after the pre-split, and is
then summed with the countable `Gamma_sigma` triangle inequality.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-- A pointwise finite-`q` pre-split at every depth produces the lower
coarse-ellipticity two-slot payload.  Summability of the combined profile is a
conclusion inside the proof, not a hypothesis of this theorem. -/
theorem twoTermFamilySplit_cutoffLowerEllipticityInv_of_finiteQPresplit
    [NeZero d] (M : ABKModel d) (m : ℤ)
    (r : {r : ℝ // 1 ≤ r}) (hr : 2 ≤ (r : ℝ))
    {s Cprof scaling sigmaTail B : ℝ} (hs : 0 < s)
    (hgap : 0 < 2 * s - M.gamma) (hCprof : 0 ≤ Cprof)
    (hscaling : 0 ≤ scaling) (hsigmaTail : 0 < sigmaTail)
    {L0 : ℤ} {U : ℕ → Cutoff.CutoffSample d → ℝ} {a : ℕ → ℝ}
    (hUnonneg : ∀ n omega, 0 ≤ U n omega)
    (hUmeas : ∀ n, Measurable (U n))
    (hUqsum : ∀ omega, Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n * U n omega ^ ((r : ℝ) / 2))
    (hUlinsum : ∀ omega, Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) * U n omega)
    (ha : ∀ n, 0 < a n)
    (hasum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) * a n)
    (hUO : ∀ n, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma sigmaTail) (U n) (a n))
    (hbudget : 2 * gammaTriangleConst sigmaTail *
      (∑' n : ℕ,
        Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) * a n) ≤ B)
    (hdepth : ∀ omega, ∀ L : ℤ, L0 ≤ L → ∀ n : ℕ,
      scaling *
          Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
            (originCube d m) (m - (n : ℤ))
            (Cutoff.coefficientCutoff M.nu L omega) ≤
        finiteQGeometricProfile Cprof M.gamma n + U n omega) :
    ∃ Ydet Y : Cutoff.CutoffSample d → ℝ,
      (∀ omega, ∀ L : ℤ, L0 ≤ L →
        Observable.cutoffLowerEllipticityInv M m L s hs
              (CoarseEllipticityExponent.finite r) omega * scaling ≤
          Ydet omega + Y omega) ∧
      (∀ omega, Ydet omega ≤ 4 * Cprof * s * (2 * s - M.gamma)⁻¹) ∧
      Measurable Y ∧
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma sigmaTail) Y B := by
  let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s (r : ℝ) n
  let v : ℕ → ℝ := fun n => w n ^ (2 / (r : ℝ))
  let D : ℕ → ℝ := finiteQGeometricProfile Cprof M.gamma
  let Z : ℤ → Cutoff.CutoffSample d → ℕ → ℝ := fun L omega n =>
    scaling *
      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        (originCube d m) (m - (n : ℤ))
        (Cutoff.coefficientCutoff M.nu L omega)
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have ht : (1 : ℝ) ≤ (r : ℝ) / 2 := by linarith
  have ht0 : (0 : ℝ) ≤ (r : ℝ) / 2 := by linarith
  have hroot0 : (0 : ℝ) ≤ 2 / (r : ℝ) := by positivity
  have hsr : (0 : ℝ) < s * (r : ℝ) := mul_pos hs hr0
  have hwpos : ∀ n, 0 < w n := fun n =>
    HCPolySupport.geometricWeight_pos n hsr
  have hw : ∀ n, 0 ≤ w n := fun n => (hwpos n).le
  have hvpos : ∀ n, 0 < v n := fun n =>
    Real.rpow_pos_of_pos (hwpos n) _
  have hD : ∀ n, 0 ≤ D n := fun n =>
    finiteQGeometricProfile_nonneg hCprof M.gamma n
  have hDqsum : Summable fun n : ℕ => w n * D n ^ ((r : ℝ) / 2) := by
    simpa [w, D] using
      summable_geometricWeight_mul_finiteQGeometricProfile_rpow hCprof hgap hr0
  have hDroot :
      (∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) ≤
        2 * Cprof * s * (2 * s - M.gamma)⁻¹ := by
    simpa [w, D] using
      finiteQGeometricProfile_aggregate_le_of_two_le
        hCprof M.shellPrefix.gamma_pos.le hs hr hgap
  have htotalSum : ∀ omega, Summable fun n : ℕ =>
      w n * (D n + U n omega) ^ ((r : ℝ) / 2) := by
    intro omega
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hw n)
        (Real.rpow_nonneg (add_nonneg (hD n) (hUnonneg n omega)) _))
      (fun n => ?_)
      ((hDqsum.add (hUqsum omega)).mul_left
        ((2 : ℝ) ^ ((r : ℝ) / 2 - 1)))
    have hpow := rpow_half_add_le_mul_rpow_half_add_rpow_half
      (hD n) (hUnonneg n omega) hr
    calc
      w n * (D n + U n omega) ^ ((r : ℝ) / 2)
          ≤ w n * ((2 : ℝ) ^ ((r : ℝ) / 2 - 1) *
              (D n ^ ((r : ℝ) / 2) + U n omega ^ ((r : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left hpow (hw n)
      _ = (2 : ℝ) ^ ((r : ℝ) / 2 - 1) *
          (w n * D n ^ ((r : ℝ) / 2) +
            w n * U n omega ^ ((r : ℝ) / 2)) := by ring
  have hrootIdentity : 1 / ((r : ℝ) / 2) = 2 / (r : ℝ) := by
    field_simp
  refine ⟨fun _ => 4 * Cprof * s * (2 * s - M.gamma)⁻¹,
    fun omega => 2 * ∑' n : ℕ, v n * U n omega, ?_, fun _ => le_rfl, ?_, ?_⟩
  · intro omega L hL
    have hscale : (originCube d m).scale = m := rfl
    have hZ : ∀ n, 0 ≤ Z L omega n := by
      intro n
      refine mul_nonneg hscaling ?_
      exact Book.Ch05.Section52.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_nonneg_of_le
        (originCube d m) (Cutoff.coefficientCutoff M.nu L omega)
        (by rw [hscale]; omega)
    have hZU : ∀ n, Z L omega n ≤ D n + U n omega := by
      intro n
      simpa [Z, D] using hdepth omega L hL n
    have hZqsum : Summable fun n : ℕ =>
        w n * Z L omega n ^ ((r : ℝ) / 2) := by
      refine Summable.of_nonneg_of_le
        (fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hZ n) _))
        (fun n => mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hZ n) (hZU n) ht0) (hw n))
        (htotalSum omega)
    have hsumZU :
        (∑' n : ℕ, w n * Z L omega n ^ ((r : ℝ) / 2)) ≤
          ∑' n : ℕ, w n * (D n + U n omega) ^ ((r : ℝ) / 2) :=
      hZqsum.tsum_le_tsum
        (fun n => mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hZ n) (hZU n) ht0) (hw n))
        (htotalSum omega)
    have hZaggregate :
        (∑' n : ℕ, w n * Z L omega n ^ ((r : ℝ) / 2)) ^
              (2 / (r : ℝ)) ≤
          (∑' n : ℕ, w n * (D n + U n omega) ^ ((r : ℝ) / 2)) ^
              (2 / (r : ℝ)) :=
      Real.rpow_le_rpow
        (tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hZ n) _))
        hsumZU hroot0
    have hpresplit := rpow_inv_tsum_presplit_le hw hD
      (fun n => hUnonneg n omega) ht hDqsum (hUqsum omega) (htotalSum omega)
    rw [hrootIdentity] at hpresplit
    have hUroot :
        (∑' n : ℕ, w n * U n omega ^ ((r : ℝ) / 2)) ^
              (2 / (r : ℝ)) ≤
          ∑' n : ℕ, v n * U n omega := by
      simpa [v] using tsum_weighted_rpow_root_le hr hw
        (fun n => hUnonneg n omega) (hUqsum omega) (hUlinsum omega)
    rw [cutoffLowerEllipticityInv_mul_eq_rpow M m L hs rfl hr0 hscaling omega]
    change
      (∑' n : ℕ, w n * Z L omega n ^ ((r : ℝ) / 2)) ^
          (2 / (r : ℝ)) ≤
        4 * Cprof * s * (2 * s - M.gamma)⁻¹ +
          2 * ∑' n : ℕ, v n * U n omega
    calc
      (∑' n : ℕ, w n * Z L omega n ^ ((r : ℝ) / 2)) ^
            (2 / (r : ℝ)) ≤
          (∑' n : ℕ, w n * (D n + U n omega) ^ ((r : ℝ) / 2)) ^
            (2 / (r : ℝ)) := hZaggregate
      _ ≤ 2 * ((∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) ^
              (2 / (r : ℝ)) +
            (∑' n : ℕ, w n * U n omega ^ ((r : ℝ) / 2)) ^
              (2 / (r : ℝ))) := hpresplit
      _ ≤ 2 * (2 * Cprof * s * (2 * s - M.gamma)⁻¹ +
            ∑' n : ℕ, v n * U n omega) :=
        mul_le_mul_of_nonneg_left (add_le_add hDroot hUroot) (by norm_num)
      _ = 4 * Cprof * s * (2 * s - M.gamma)⁻¹ +
          2 * ∑' n : ℕ, v n * U n omega := by ring
  · exact (measurable_tsum_of_nonneg
      (fun n => (hUmeas n).const_mul (v n))
      (fun n omega => mul_nonneg (hvpos n).le (hUnonneg n omega))
      (by simpa [v, w] using hUlinsum)).const_mul 2
  · have hsumO : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma sigmaTail) (fun omega => ∑' n : ℕ, v n * U n omega)
        (gammaTriangleConst sigmaTail * ∑' n : ℕ, v n * a n) :=
      isBigOWith_gammaSigma_tsum_weighted hsigmaTail hvpos hUnonneg hUmeas ha
        (by simpa [v, w] using hasum) hUO le_rfl
    exact (IsBigOWith.const_mul (by norm_num : (0 : ℝ) ≤ 2) hsumO).mono_scale
      (by simpa [v, w, mul_assoc] using hbudget)

/-- The finite-`q` pre-split interface, uniformly over the induction data,
discharges exactly the `payloadTwoLe` argument of
`coarse_ellipticity_lower_payload_of_branchPayloads`.

The constant gate `4 * Cprof <= Clow` absorbs only the dimension-free factor
two from the pre-split and the factor two in the deterministic geometric
profile estimate. -/
theorem coarse_ellipticity_lower_branchPayload_two_le_of_finiteQPresplit
    (d : ℕ) [NeZero d] {Clow Cprof : ℝ} (hCprof : 0 ≤ Cprof)
    (habsorb : 4 * Cprof ≤ Clow)
    (finiteQPresplit :
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ r : {r : ℝ // 1 ≤ r}, 2 ≤ (r : ℝ) →
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              ∃ (U : ℕ → Cutoff.CutoffSample d → ℝ) (a : ℕ → ℝ),
                (∀ n omega, 0 ≤ U n omega) ∧
                (∀ n, Measurable (U n)) ∧
                (∀ omega, Summable fun n : ℕ =>
                  Book.Ch02.geometricWeight s (r : ℝ) n *
                    U n omega ^ ((r : ℝ) / 2)) ∧
                (∀ omega, Summable fun n : ℕ =>
                  Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) *
                    U n omega) ∧
                (∀ n, 0 < a n) ∧
                (Summable fun n : ℕ =>
                  Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) * a n) ∧
                (∀ n, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
                  (gammaSigma ((1 - sigma) / 2)) (U n) (a n)) ∧
                (2 * gammaTriangleConst ((1 - sigma) / 2) *
                    (∑' n : ℕ,
                      Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) *
                        a n) ≤
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ∧
                (∀ omega, ∀ L : ℤ, m - 1 ≤ L → ∀ n : ℕ,
                  (Annealed.sigmaBar M (m - 1) : ℝ) *
                      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                        (originCube d m) (m - (n : ℤ))
                        (Cutoff.coefficientCutoff M.nu L omega) ≤
                    finiteQGeometricProfile Cprof M.gamma n + U n omega)) :
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ r : {r : ℝ // 1 ≤ r}, 2 ≤ (r : ℝ) →
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              ∃ Ydet Y : Cutoff.CutoffSample d → ℝ,
                (∀ omega, ∀ L : ℤ, m - 1 ≤ L →
                    Observable.cutoffLowerEllipticityInv
                          M m L s
                          (by
                            exact
                              (add_pos
                                (div_pos M.shellPrefix.gamma_pos (by norm_num))
                              (Real.exp_pos
                                (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          (CoarseEllipticityExponent.finite r) omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ) ≤
                      Ydet omega + Y omega) ∧
                (∀ omega, Ydet omega ≤
                  Clow * s * (2 * s - M.gamma)⁻¹) ∧
                Measurable Y ∧
                IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
                  (gammaSigma ((1 - sigma) / 2)) Y
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  intro M m E hstate sigma hsigma hE1 hE2 r hr s hsWindow
  obtain ⟨U, a, hUnonneg, hUmeas, hUqsum, hUlinsum, ha, hasum, hUO,
    hbudget, hdepth⟩ :=
    finiteQPresplit M m E hstate sigma hsigma hE1 hE2 r hr s hsWindow
  have hexppos : (0 : ℝ) <
      Real.exp (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
    Real.exp_pos _
  have hwin : M.gamma / 2 +
      Real.exp (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ s :=
    hsWindow.1
  have hs : (0 : ℝ) < s := by
    linarith [M.shellPrefix.gamma_pos]
  have hgap : (0 : ℝ) < 2 * s - M.gamma := by
    linarith
  have hsigmaTail : (0 : ℝ) < (1 - sigma) / 2 := by
    linarith [hsigma.2]
  obtain ⟨Ydet, Y, hdom, hdet, hYmeas, htail⟩ :=
    twoTermFamilySplit_cutoffLowerEllipticityInv_of_finiteQPresplit
      M m r hr hs hgap hCprof (Annealed.sigmaBar M (m - 1)).2.le
      hsigmaTail hUnonneg hUmeas hUqsum hUlinsum ha hasum hUO hbudget hdepth
  refine ⟨Ydet, Y, hdom, ?_, hYmeas, htail⟩
  intro omega
  have hfactor : (0 : ℝ) ≤ s * (2 * s - M.gamma)⁻¹ :=
    mul_nonneg hs.le (inv_nonneg.mpr hgap.le)
  calc
    Ydet omega ≤ 4 * Cprof * s * (2 * s - M.gamma)⁻¹ := hdet omega
    _ = (4 * Cprof) * (s * (2 * s - M.gamma)⁻¹) := by ring
    _ ≤ Clow * (s * (2 * s - M.gamma)⁻¹) :=
      mul_le_mul_of_nonneg_right habsorb hfactor
    _ = Clow * s * (2 * s - M.gamma)⁻¹ := by ring

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
