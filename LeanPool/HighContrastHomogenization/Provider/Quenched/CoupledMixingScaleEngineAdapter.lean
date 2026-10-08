/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledMixingScale
public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedPolynomialNormalizer

/-!
# High-contrast homogenization: Provider.Quenched.CoupledMixingScaleEngineAdapter

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Coupled witness from the quenched bad-tail engine

The stopping engine selects one random scale together with its marginal tail
and its all-later bad-event certificate.  This module places those outputs,
the weighted row series, and the final normalizer in the dependent structure
consumed by the physical-scale argument.
-/

namespace HCPolySupport.HighContrast.Quenched

open Filter MeasureTheory
open Book.Ch05.Section57

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A second factor of three can be absorbed by one additional polynomial
cost, with the three exponent costs combined additively. -/
theorem three_mul_le_rpow_of_le_rpow
    {base A Cstop Cround Cmix : ℝ}
    (hbase : 1 ≤ base) (hA : 0 ≤ A)
    (hthree : (3 : ℝ) ≤ base ^ Cround)
    (hstop : A ≤ base ^ Cstop)
    (hcost : Cround + Cstop ≤ Cmix) :
    3 * A ≤ base ^ Cmix := by
  have hbasePos : 0 < base := zero_lt_one.trans_le hbase
  have hproduct : 3 * A ≤ base ^ Cround * base ^ Cstop :=
    mul_le_mul hthree hstop hA (Real.rpow_nonneg hbasePos.le _)
  calc
    3 * A ≤ base ^ Cround * base ^ Cstop := hproduct
    _ = base ^ (Cround + Cstop) := (Real.rpow_add hbasePos _ _).symm
    _ ≤ base ^ Cmix := Real.rpow_le_rpow_of_exponent_le hbase hcost

/-- Package one selected scale, its row series, and its own bad-event
certificate into the coupled witness used by the physical-scale argument. -/
@[expose]
def coupledMixingScaleWitnessOfSelectedEngine
    {P : Measure Omega} {B F : ℕ → Omega → ℝ}
    {cMix cd eta kappa delta Astop Amix : ℝ} {Rmix : Omega → ℝ}
    (hAstop : 1 ≤ Astop) (hAmix : 1 ≤ Amix)
    (hbuffer : 3 * Astop ≤ Amix)
    (hRmixMeasurable : Measurable Rmix) (hRmixOne : ∀ a, 1 ≤ Rmix a)
    (hRmixTail : ∀ t : ℝ, 1 ≤ t →
      P.real {a | cMix * t ≤ Rmix a} ≤ Real.exp (-cd * t ^ eta))
    (hBNonnegative : ∀ m a, 0 ≤ B m a)
    (hFsum : ∀ᵐ a ∂P, ∀ n,
      HasSum (fun j : ℕ => (3 : ℝ) ^ (kappa * (j : ℝ)) * B (n + j) a)
        (F n a))
    (hBadMeasurable : ∀ n, MeasurableSet (rowBadEvent delta F n))
    (hcertificate : ∀ᵐ a ∂P, ∀ n : ℕ,
      Astop * Rmix a ≤ (3 : ℝ) ^ n → a ∉ rowBadEvent delta F n) :
    CoupledMixingScaleWitness P B cMix cd eta kappa delta where
  stoppingNormalization := Astop
  normalization := Amix
  scale := Rmix
  row := B
  tailSum := F
  bad := rowBadEvent delta F
  one_le_stoppingNormalization := hAstop
  one_le_normalization := hAmix
  three_mul_stoppingNormalization_le := hbuffer
  measurable_scale := hRmixMeasurable
  one_le_scale := hRmixOne
  scale_tail := hRmixTail
  row_eq_selected := fun _ _ => rfl
  row_nonneg := hBNonnegative
  hasSum_tail := hFsum
  bad_eq := fun _ => rfl
  measurableSet_bad := hBadMeasurable
  eventually_not_mem_bad := hcertificate

/-- The polynomial bad-tail engine supplies the complete dual-normalizer
coupled witness.  The raw engine normalizer is used for its certificate; one
additional factor of three is absorbed into the final replay normalizer. -/
theorem exists_coupledMixingScaleWitness_of_polynomial_engine
    {P : Measure Omega} [IsProbabilityMeasure P]
    {nstar qfb b : ℕ} {R B F : ℕ → Omega → ℝ}
    {theta mu eta cd delta Cblk : ℝ}
    {base C1 C2 C3 Cstop Cround Cmix : ℝ}
    (htheta : 0 < theta) (hmu : 0 < mu) (heta : eta = 2 * mu)
    (hcd : 0 < cd) (hdelta : 0 < delta) (hCblk : 0 < Cblk)
    (hFmeas : ∀ n, Measurable (F n))
    (hRtail : ∀ n q : ℕ, nstar ≤ n →
      P.real {a | (3 : ℝ) ^ (n + q + b) < R n a} ≤
        Real.exp (-(cd * (3 : ℝ) ^ (2 * mu * (q : ℝ)))))
    (hBdecay : ∀ᵐ a ∂P, ∀ (m : ℕ), nstar ≤ m →
      B m a ≤ Cblk * delta *
        (3 : ℝ) ^ (-theta *
          ((m : ℝ) - (stoppingGeneration nstar qfb R m a : ℝ) -
            (nstar : ℝ))))
    (hBNonnegative : ∀ m a, 0 ≤ B m a)
    (hFsum : ∀ᵐ a ∂P, ∀ k : ℕ,
      HasSum (fun j : ℕ => (3 : ℝ) ^ (theta / 2 * (j : ℝ)) * B (k + j) a)
        (F k a))
    {N0 : ℕ} {Bconst : ℝ} (hstar : nstar ≤ N0) (hBconst : 1 ≤ Bconst)
    (hN0low : (qfb : ℝ) + (b : ℝ) + 1 + rowSplitOffset theta Cblk ≤
      (N0 : ℝ) - (nstar : ℝ))
    (hN0gain : Real.log 2 ≤
      cd * (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b)) * ((3 : ℝ) ^ (mu / 2) - 1))
    (hN0abs : 2 * Real.log 4 ≤
      cd * (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b)))
    (hBrel : (3 : ℝ) ^ (2 * mu *
        ((nstar : ℝ) + badTailOffset theta Cblk qfb b - (N0 : ℝ))) ≤
      cd / 2 * Bconst ^ (2 * mu))
    (hbase : 1 ≤ base) (hthree : (3 : ℝ) ≤ base ^ C3)
    (hgen : (3 : ℝ) ^ N0 ≤ base ^ C1)
    (hnorm : Bconst ≤ base ^ C2) (hrawCost : C1 + C2 + C3 ≤ Cstop)
    (hround : (3 : ℝ) ≤ base ^ Cround)
    (hfinalCost : Cround + Cstop ≤ Cmix) :
    ∃ W : CoupledMixingScaleWitness P B 2 1 eta (theta / 2) delta,
      W.normalization ≤ base ^ Cmix := by
  obtain ⟨Astop, Rmix, hAstop, hAstopBound, hRmixMeasurable,
    hRmixOne, hRmixTail, hBadMeasurable, -, hcertificate⟩ :=
    exists_coupled_mixingScale_polynomial htheta hmu heta hcd hdelta hCblk
      hFmeas hRtail hBdecay hFsum hstar hBconst hN0low hN0gain hN0abs
      hBrel hbase hthree hgen hnorm hrawCost
  let Amix : ℝ := 3 * Astop
  have hAmix : 1 ≤ Amix := by
    dsimp only [Amix]
    nlinarith only [hAstop]
  have hAmixBound : Amix ≤ base ^ Cmix := by
    exact three_mul_le_rpow_of_le_rpow hbase
      (zero_le_one.trans hAstop) hround hAstopBound hfinalCost
  let W : CoupledMixingScaleWitness P B 2 1 eta (theta / 2) delta :=
    coupledMixingScaleWitnessOfSelectedEngine hAstop hAmix le_rfl
      hRmixMeasurable hRmixOne hRmixTail hBNonnegative hFsum
      hBadMeasurable hcertificate
  refine ⟨W, ?_⟩
  change Amix ≤ base ^ Cmix
  exact hAmixBound

end

end HCPolySupport.HighContrast.Quenched
