/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperFiniteQLtTwo
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperSaturatedBlockProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandRareAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AESummability

/-!
# UpperFiniteQLtTwoAggregation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Section 3.3 finite-exponent upper aggregation below two

This module passes from a normalized, per-descendant
three-term block split to the finite-`q < 2` upper coarse-ellipticity payload.
The only caller-supplied analytic input is the per-descendant split.  The
pointwise summability demanded by the existing finite-`q` consumer is recovered
here from its per-depth weak-Orlicz bounds by changing the normalized depth
families on a measurable null set.

The deterministic ordinary and rare scale-series estimates are discharged
internally before the resulting split is packaged in the upper-tail carrier.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-- Replace a nonnegative normalized depth family on a measurable null set so
its weighted linear series is summable at every sample point. -/
private theorem exists_everywhere_summable_ae_eq_of_isBigOWith_gammaSigma
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {w a : ℕ → ℝ} {V : ℕ → Omega → ℝ} {r sigma : ℝ}
    (hsigma : 0 < sigma)
    (hw : ∀ n, 0 < w n) (ha : ∀ n, 0 < a n)
    (hVnonneg : ∀ n omega, 0 ≤ V n omega)
    (hVmeas : ∀ n, Measurable (V n))
    (hasum : Summable fun n : ℕ => w n * a n ^ (r / 2))
    (hVO : ∀ n, IsBigOWith mu (gammaSigma sigma) (V n) 1) :
    ∃ V' : ℕ → Omega → ℝ,
      (∀ n omega, 0 ≤ V' n omega) ∧
      (∀ n, Measurable (V' n)) ∧
      (∀ omega, Summable fun n : ℕ =>
        w n * a n ^ (r / 2) * V' n omega) ∧
      (∀ n, V n =ᵐ[mu] V' n) ∧
      (∀ n, IsBigOWith mu (gammaSigma sigma) (V' n) 1) := by
  classical
  let b : ℕ → ℝ := fun n => w n * a n ^ (r / 2)
  let X : ℕ → Omega → ℝ := fun n omega => b n * V n omega
  have hbpos : ∀ n, 0 < b n := fun n =>
    mul_pos (hw n) (Real.rpow_pos_of_pos (ha n) _)
  have hXnonneg : ∀ n omega, 0 ≤ X n omega := fun n omega =>
    mul_nonneg (hbpos n).le (hVnonneg n omega)
  have hXmeas : ∀ n, AEMeasurable (X n) mu := fun n =>
    ((hVmeas n).const_mul (b n)).aemeasurable
  have hXsum : Summable b := by
    simpa only [b] using hasum
  have hXO : ∀ n, IsBigOWith mu (gammaSigma sigma) (X n) (b n) := by
    intro n
    have hscaled := (hVO n).const_mul (hbpos n).le
    simpa only [X, mul_one] using hscaled
  have hsumAE : ∀ᵐ omega ∂mu, Summable fun n => X n omega :=
    Algsuperdiff.Section3.Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
      hsigma hXnonneg hXmeas hbpos hXsum hXO
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hsumAE)
  let V' : ℕ → Omega → ℝ := fun n => Nᶜ.indicator (V n)
  have hnmem : ∀ᵐ omega ∂mu, omega ∉ N :=
    measure_eq_zero_iff_ae_notMem.mp hNzero
  refine ⟨V', ?_, ?_, ?_, ?_, ?_⟩
  · intro n omega
    by_cases homega : omega ∈ N
    · simp [V', homega]
    · simp [V', homega, hVnonneg n omega]
  · intro n
    exact (hVmeas n).indicator hNmeas.compl
  · intro omega
    by_cases homega : omega ∈ N
    · have hzero : (fun n : ℕ => w n * a n ^ (r / 2) * V' n omega) = 0 := by
        funext n
        simp [V', homega]
      rw [hzero]
      exact summable_zero
    · have hraw : Summable fun n => X n omega := by
        by_contra hnot
        exact homega (hNsub hnot)
      refine hraw.congr fun n => ?_
      simp only [X, b]
      simp [V', homega]
  · intro n
    filter_upwards [hnmem] with omega homega
    simp [V', homega]
  · intro n
    refine Provider.Tail.isBigOWith_of_ae_eq ?_ (hVO n)
    filter_upwards [hnmem] with omega homega
    simp [V', homega]

private theorem descendantUpperFlux_depthBound :
    ∀ {d : ℕ} [NeZero d] (M : ABKModel d) (m : ℤ)
      {scaling Cblock Krare eps sigmaExp : ℝ},
      (0 : ℝ) ≤ scaling →
        ∀ (UoneCube UexpCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ),
          (∀ (k : ℕ) (R : TriadicCube d) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ UoneCube k R
            omega) →
            (∀ (k : ℕ) (R : TriadicCube d) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ UexpCube k R
              omega) →
              (∀ (k : ℕ),
                  ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
                    ∀ (omega : Cutoff.CutoffSample d),
                      |cutoffBBlockFamily M m scaling R omega| ≤ Cblock + UoneCube k R omega +
                        UexpCube k R omega) →
                let Gone : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k
                  (UoneCube k);
                let Gexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k
                  (UexpCube k);
                let a1 : ℕ → ℝ := fun (n : ℕ) =>
                  gridBlockAmp d (1 : ℝ) (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M)
                    M.gamma n.pred) n.pred;
                let aexp : ℕ → ℝ := fun (n : ℕ) =>
                  gridBlockAmp d sigmaExp (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((↑n.pred : ℝ) + (1 :
                    ℝ))) * eps ^ (15 : ℕ))
                    n.pred;
                let VoneRaw : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) (omega :
                  Cutoff.CutoffSample d) =>
                  (a1 n)⁻¹ * Gone n.pred omega;
                let VexpRaw : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) (omega :
                  Cutoff.CutoffSample d) =>
                  (aexp n)⁻¹ * Gexp n.pred omega;
                (∀ (n : ℕ), (0 : ℝ) < a1 n) →
                  (∀ (n : ℕ), (0 : ℝ) < aexp n) →
                    ∀ (n : ℕ) (omega : Cutoff.CutoffSample d),
                      scaling *
                          Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale (originCube d m) (m
                            - (↑n : ℤ))
                            (Cutoff.coefficientCutoff M.nu m omega) ≤
                        Cblock + a1 n * VoneRaw n omega + aexp n * VexpRaw n omega := by
  intro d _ M m scaling Cblock _ _ _ hscaling _ _ hUoneCubeNonneg hUexpCubeNonneg hblock Gone Gexp
    a1 aexp VoneRaw VexpRaw ha1 haexp n omega
  have hgrid : scaling *
        Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          (originCube d m) (m - (n : ℤ))
          (Cutoff.coefficientCutoff M.nu m omega) ≤
      blockGridSup d m n.pred (cutoffBBlockFamily M m scaling) omega := by
    cases n with
    | zero =>
        simpa only [Nat.cast_zero, sub_zero, Nat.pred_zero] using
          (scaledB_le_blockGridSup M m 0 hscaling
            (maxDescendantBCoeffField_top_le m
              (Cutoff.coefficientCutoff M.nu m omega))
            (fun _ _ => le_rfl))
    | succ k =>
        have hscale : m - (((k + 1 : ℕ) : ℤ)) = m - 1 - (k : ℤ) := by
          push_cast
          ring
        rw [hscale]
        exact scaledB_le_blockGridSup M m k hscaling le_rfl fun _ _ => le_rfl
  have hsplit := blockGridSup_le_add_add_of_perCube
    (hUoneCubeNonneg n.pred) (hUexpCubeNonneg n.pred)
    (hblock n.pred) omega
  calc
    scaling *
        Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          (originCube d m) (m - (n : ℤ))
          (Cutoff.coefficientCutoff M.nu m omega) ≤
        blockGridSup d m n.pred (cutoffBBlockFamily M m scaling) omega := hgrid
    _ ≤ Cblock + Gone n.pred omega + Gexp n.pred omega := by
      simpa only [Gone, Gexp] using hsplit
    _ = Cblock + a1 n * VoneRaw n omega + aexp n * VexpRaw n omega := by
      rw [show a1 n * VoneRaw n omega = Gone n.pred omega by
        simp only [VoneRaw, ← mul_assoc, mul_inv_cancel₀ (ha1 n).ne', one_mul]]
      rw [show aexp n * VexpRaw n omega = Gexp n.pred omega by
        simp only [VexpRaw, ← mul_assoc, mul_inv_cancel₀ (haexp n).ne', one_mul]]

private theorem finiteSmallExponent_deterministicBudget :
    ∀ (r : { r : ℝ // (1 : ℝ) ≤ r }) {s Cblock Bdet : ℝ},
      (0 : ℝ) < s →
        (0 : ℝ) < Cblock →
          (4 : ℝ) * Cblock ≤ Bdet →
            let D : ℕ → ℝ := fun (_ : ℕ) => Cblock;
            (4 : ℝ) *
                (∑' (n : ℕ), Book.Ch02.geometricWeight s (↑r : ℝ) n * D n ^ ((↑r : ℝ) / (2 : ℝ)))
                  ^ ((2 : ℝ) / (↑r : ℝ)) ≤
              Bdet := by
  intro r s Cblock _ hs hCblock hdetBudget D
  have hweights : (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n) = 1 :=
    HCPolySupport.tsum_geometricWeight_eq_one
      (mul_pos hs (lt_of_lt_of_le zero_lt_one r.property))
  have hsum : (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
      D n ^ ((r : ℝ) / 2)) = Cblock ^ ((r : ℝ) / 2) := by
    simp only [D]
    rw [tsum_mul_right, hweights, one_mul]
  have hcancel : (r : ℝ) / 2 * (2 / (r : ℝ)) = 1 := by
    field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one r.property)]
  rw [hsum, ← Real.rpow_mul hCblock.le, hcancel, Real.rpow_one]
  exact hdetBudget

/-- The finite-`q < 2` upper payload obtained from a normalized
per-descendant block split.  The root depth reuses strict row zero, while
positive source depth `n + 1` uses strict row `n`. -/
private theorem finiteQLtTwoSplit_of_perDescendantAndBudgets
    [NeZero d] (hd : 1 ≤ d)
    (M : ABKModel d) (m : ℤ)
    (r : {r : ℝ // 1 ≤ r}) (hr : (r : ℝ) < 2)
    {s scaling Cblock Krare eps Bdet B1 Bexp sigmaExp : ℝ}
    (hs : 0 < s) (hscaling : 0 ≤ scaling)
    (hCblock : 0 < Cblock) (hKrare : 0 < Krare) (heps : 0 < eps)
    (hsigmaExp : 0 < sigmaExp)
    (hper : ∀ (k : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
        ∃ Uone Uexp : Cutoff.CutoffSample d → ℝ,
          (∀ omega, 0 ≤ Uone omega) ∧
          Measurable Uone ∧
          (∀ omega, 0 ≤ Uexp omega) ∧
          Measurable Uexp ∧
          (∀ omega,
            cutoffBBlockFamily M m scaling R omega ≤
              Cblock + Uone omega + Uexp omega) ∧
          IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
            (gammaSigma 1) Uone
            (upperSaturatedPerCubeAmplitude Cblock
              (Disorder.cstar M) M.gamma k) ∧
          IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
            (gammaSigma sigmaExp) Uexp
            (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 15))
    (ha1sum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n *
        (gridBlockAmp d 1
          (upperSaturatedPerCubeAmplitude Cblock
            (Disorder.cstar M) M.gamma n.pred) n.pred) ^ ((r : ℝ) / 2))
    (haexpsum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n *
        (gridBlockAmp d sigmaExp
          (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((n.pred : ℝ) + 1)) * eps ^ 15)
          n.pred) ^ ((r : ℝ) / 2))
    (hdetBudget : 4 * Cblock ≤ Bdet)
    (honeBudget :
      (4 * (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
        (gridBlockAmp d 1
          (upperSaturatedPerCubeAmplitude Cblock
            (Disorder.cstar M) M.gamma n.pred) n.pred) ^ ((r : ℝ) / 2)) ^
          (2 / (r : ℝ))) * gammaTriangleConst 1 ≤ B1)
    (hexpBudget :
      (4 * (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
        (gridBlockAmp d sigmaExp
          (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((n.pred : ℝ) + 1)) * eps ^ 15)
          n.pred) ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ))) *
        gammaTriangleConst sigmaExp ≤ Bexp) :
    ∃ Udet Uone Utail : Cutoff.CutoffSample d → ℝ,
      (∀ omega,
        Observable.cutoffUpperEllipticity M m m s hs
              (CoarseEllipticityExponent.finite r) omega * scaling ≤
          Udet omega + Uone omega + Utail omega) ∧
      (∀ omega, Udet omega ≤ Bdet) ∧
      Measurable Uone ∧ Measurable Utail ∧
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 1) Uone B1 ∧
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma sigmaExp) Utail Bexp := by
  classical
  let mu : Measure (Cutoff.CutoffSample d) :=
    (Cutoff.cutoffSampleLaw M).toMeasure
  let UoneCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ :=
    fun k R =>
      if hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) then
        Classical.choose (hper k R hR)
      else fun _ => 0
  let UexpCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ :=
    fun k R =>
      if hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) then
        Classical.choose (Classical.choose_spec (hper k R hR))
      else fun _ => 0
  have hUoneCubeNonneg : ∀ (k : ℕ) (R : TriadicCube d) omega,
      0 ≤ UoneCube k R omega := by
    intro k R omega
    by_cases hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ))
    · obtain ⟨hUone, _⟩ :=
        Classical.choose_spec (Classical.choose_spec (hper k R hR))
      simpa only [UoneCube, dite_eq_left hR] using hUone omega
    · simp [UoneCube, hR]
  have hUexpCubeNonneg : ∀ (k : ℕ) (R : TriadicCube d) omega,
      0 ≤ UexpCube k R omega := by
    intro k R omega
    by_cases hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ))
    · obtain ⟨_, _, hUexp, _⟩ :=
        Classical.choose_spec (Classical.choose_spec (hper k R hR))
      simpa only [UexpCube, dite_eq_left hR] using hUexp omega
    · simp [UexpCube, hR]
  have hUoneCubeMeas : ∀ (k : ℕ) (R : TriadicCube d),
      Measurable (UoneCube k R) := by
    intro k R
    by_cases hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ))
    · obtain ⟨_, hUone, _⟩ :=
        Classical.choose_spec (Classical.choose_spec (hper k R hR))
      simpa only [UoneCube, dite_eq_left hR] using hUone
    · simp [UoneCube, hR]
  have hUexpCubeMeas : ∀ (k : ℕ) (R : TriadicCube d),
      Measurable (UexpCube k R) := by
    intro k R
    by_cases hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ))
    · obtain ⟨_, _, _, hUexp, _⟩ :=
        Classical.choose_spec (Classical.choose_spec (hper k R hR))
      simpa only [UexpCube, dite_eq_left hR] using hUexp
    · simp [UexpCube, hR]
  have hUoneCubeO : ∀ (k : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
      IsBigOWith mu (gammaSigma 1) (UoneCube k R)
        (upperSaturatedPerCubeAmplitude Cblock
          (Disorder.cstar M) M.gamma k) := by
    intro k R hR
    obtain ⟨_, _, _, _, _, hUone, _⟩ :=
      Classical.choose_spec (Classical.choose_spec (hper k R hR))
    simpa only [mu, UoneCube, dite_eq_left hR] using hUone
  have hUexpCubeO : ∀ (k : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
      IsBigOWith mu (gammaSigma sigmaExp) (UexpCube k R)
        (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 15) := by
    intro k R hR
    obtain ⟨_, _, _, _, _, _, hUexp⟩ :=
      Classical.choose_spec (Classical.choose_spec (hper k R hR))
    simpa only [mu, UexpCube, dite_eq_left hR] using hUexp
  have hblock : ∀ (k : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
      ∀ omega, |cutoffBBlockFamily M m scaling R omega| ≤
        Cblock + UoneCube k R omega + UexpCube k R omega := by
    intro k R hR omega
    obtain ⟨_, _, _, _, hdom, _, _⟩ :=
      Classical.choose_spec (Classical.choose_spec (hper k R hR))
    have hnonneg : 0 ≤ cutoffBBlockFamily M m scaling R omega :=
      mul_nonneg hscaling (coarseBNormCoeffField_nonneg R _)
    rw [abs_of_nonneg hnonneg]
    simpa only [UoneCube, UexpCube, dite_eq_left hR] using hdom omega
  let Gone : ℕ → Cutoff.CutoffSample d → ℝ := fun k =>
    blockGridSup d m k (UoneCube k)
  let Gexp : ℕ → Cutoff.CutoffSample d → ℝ := fun k =>
    blockGridSup d m k (UexpCube k)
  let a1 : ℕ → ℝ := fun n =>
    gridBlockAmp d 1
      (upperSaturatedPerCubeAmplitude Cblock
        (Disorder.cstar M) M.gamma n.pred) n.pred
  let aexp : ℕ → ℝ := fun n =>
    gridBlockAmp d sigmaExp
      (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((n.pred : ℝ) + 1)) * eps ^ 15)
      n.pred
  let VoneRaw : ℕ → Cutoff.CutoffSample d → ℝ := fun n omega =>
    (a1 n)⁻¹ * Gone n.pred omega
  let VexpRaw : ℕ → Cutoff.CutoffSample d → ℝ := fun n omega =>
    (aexp n)⁻¹ * Gexp n.pred omega
  have hcstar : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have ha1 : ∀ n, 0 < a1 n := fun n =>
    gridBlockAmp_pos hd 1
      (upperSaturatedPerCubeAmplitude_pos hCblock hcstar M.shellPrefix.gamma_pos n.pred)
      n.pred
  have hrareAmp : ∀ k : ℕ,
      0 < Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 15 := by
    intro k
    exact mul_pos
      (mul_pos (inv_pos.mpr hKrare) (Real.rpow_pos_of_pos (by norm_num) _))
      (pow_pos heps 15)
  have haexp : ∀ n, 0 < aexp n := fun n =>
    gridBlockAmp_pos hd sigmaExp (hrareAmp n.pred) n.pred
  have hGoneNonneg : ∀ k omega, 0 ≤ Gone k omega := fun k omega =>
    blockGridSup_nonneg d m k (UoneCube k) omega
  have hGexpNonneg : ∀ k omega, 0 ≤ Gexp k omega := fun k omega =>
    blockGridSup_nonneg d m k (UexpCube k) omega
  have hGoneMeas : ∀ k, Measurable (Gone k) := fun k =>
    measurable_blockGridSup d m k (hUoneCubeMeas k)
  have hGexpMeas : ∀ k, Measurable (Gexp k) := fun k =>
    measurable_blockGridSup d m k (hUexpCubeMeas k)
  have hGoneO : ∀ k, IsBigOWith mu (gammaSigma 1) (Gone k) (a1 (k + 1)) := by
    intro k
    simpa only [Gone, a1, Nat.pred_succ] using
      (isBigOWith_gammaSigma_blockGridSup hd m k one_pos
        (upperSaturatedPerCubeAmplitude_nonneg hCblock.le
          (inv_nonneg.mpr hcstar.le) M.shellPrefix.gamma_pos.le k)
        (hUoneCubeNonneg k) (hUoneCubeO k))
  have hGexpO : ∀ k,
      IsBigOWith mu (gammaSigma sigmaExp) (Gexp k) (aexp (k + 1)) := by
    intro k
    simpa only [Gexp, aexp, Nat.pred_succ] using
      (isBigOWith_gammaSigma_blockGridSup hd m k hsigmaExp
        (hrareAmp k).le (hUexpCubeNonneg k) (hUexpCubeO k))
  have hVoneRawNonneg : ∀ n omega, 0 ≤ VoneRaw n omega := fun n omega =>
    mul_nonneg (inv_nonneg.mpr (ha1 n).le) (hGoneNonneg n.pred omega)
  have hVexpRawNonneg : ∀ n omega, 0 ≤ VexpRaw n omega := fun n omega =>
    mul_nonneg (inv_nonneg.mpr (haexp n).le) (hGexpNonneg n.pred omega)
  have hVoneRawMeas : ∀ n, Measurable (VoneRaw n) := fun n =>
    (hGoneMeas n.pred).const_mul (a1 n)⁻¹
  have hVexpRawMeas : ∀ n, Measurable (VexpRaw n) := fun n =>
    (hGexpMeas n.pred).const_mul (aexp n)⁻¹
  have hVoneRawO : ∀ n, IsBigOWith mu (gammaSigma 1) (VoneRaw n) 1 := by
    intro n
    have hgrid : IsBigOWith mu (gammaSigma 1) (Gone n.pred) (a1 n) := by
      cases n with
      | zero => simpa only [Nat.pred_zero] using! hGoneO 0
      | succ k => simpa only [Nat.pred_succ] using hGoneO k
    have hscaled := hgrid.const_mul (inv_nonneg.mpr (ha1 n).le)
    simpa only [VoneRaw, inv_mul_cancel₀ (ha1 n).ne'] using hscaled
  have hVexpRawO : ∀ n,
      IsBigOWith mu (gammaSigma sigmaExp) (VexpRaw n) 1 := by
    intro n
    have hgrid : IsBigOWith mu (gammaSigma sigmaExp) (Gexp n.pred) (aexp n) := by
      cases n with
      | zero => simpa only [Nat.pred_zero] using! hGexpO 0
      | succ k => simpa only [Nat.pred_succ] using hGexpO k
    have hscaled := hgrid.const_mul (inv_nonneg.mpr (haexp n).le)
    simpa only [VexpRaw, inv_mul_cancel₀ (haexp n).ne'] using hscaled
  have hdepthRaw := @descendantUpperFlux_depthBound (d) (by infer_instance) (M) (m) (scaling)
    (Cblock) (Krare) (eps) (sigmaExp) (hscaling) (UoneCube) (UexpCube) (hUoneCubeNonneg)
      (hUexpCubeNonneg) (hblock) (ha1) (haexp)
  have hwpos : ∀ n, 0 < Book.Ch02.geometricWeight s (r : ℝ) n := fun n =>
    HCPolySupport.geometricWeight_pos n
      (mul_pos hs (lt_of_lt_of_le zero_lt_one r.property))
  obtain ⟨Vone, hVoneNonneg, hVoneMeas, hVoneSum, hVoneEq, hVoneO⟩ :=
    exists_everywhere_summable_ae_eq_of_isBigOWith_gammaSigma
      (mu := mu) one_pos hwpos ha1 hVoneRawNonneg hVoneRawMeas
      (by simpa only [a1] using ha1sum) hVoneRawO
  obtain ⟨Vexp, hVexpNonneg, hVexpMeas, hVexpSum, hVexpEq, hVexpO⟩ :=
    exists_everywhere_summable_ae_eq_of_isBigOWith_gammaSigma
      (mu := mu) hsigmaExp hwpos haexp hVexpRawNonneg hVexpRawMeas
      (by simpa only [aexp] using haexpsum) hVexpRawO
  let D : ℕ → ℝ := fun _ => Cblock
  have hDnonneg : ∀ n, 0 ≤ D n := fun _ => hCblock.le
  have hDsum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n * D n ^ ((r : ℝ) / 2) := by
    simpa only [D] using!
      (HCPolySupport.summable_geometricWeight
        (mul_pos hs (lt_of_lt_of_le zero_lt_one r.property))).mul_right
          (Cblock ^ ((r : ℝ) / 2))
  have hdetBudget' := @finiteSmallExponent_deterministicBudget (r) (s) (Cblock) (Bdet) (hs)
    (hCblock) (hdetBudget)
  have hdepth : ∀ n : ℕ, ∀ᵐ omega ∂mu,
      scaling *
          Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
            (originCube d m) (m - (n : ℤ))
            (Cutoff.coefficientCutoff M.nu m omega) ≤
        D n + a1 n * Vone n omega + aexp n * Vexp n omega := by
    intro n
    filter_upwards [hVoneEq n, hVexpEq n] with omega hone hexp
    rw [← hone, ← hexp]
    simpa only [D] using hdepthRaw n omega
  exact threeTermSplit_cutoffUpperEllipticity_of_finiteQLtTwoPresplit
    M m m r hr hs hscaling one_pos hsigmaExp
    hDnonneg ha1 haexp hVoneNonneg hVexpNonneg hVoneMeas hVexpMeas
    hDsum (by simpa only [a1] using ha1sum) (by simpa only [aexp] using haexpsum)
    hVoneSum hVexpSum
    (by simpa only [mu] using hVoneO) (by simpa only [mu] using hVexpO)
    hdetBudget' (by simpa only [a1] using honeBudget)
    (by simpa only [aexp] using hexpBudget)
    (by simpa only [mu] using hdepth)

private theorem finiteQLtTwo_upperSaturatedProfile_le_upperPolyProfile
    {A gamma : ℝ} (hA : 0 ≤ A) (n : ℕ) :
    upperSaturatedProfile A gamma n ≤ upperPolyProfile (A * gamma) gamma n := by
  have hN : 0 ≤ (n : ℝ) + 1 := by positivity
  have hpow : 0 ≤ (3 : ℝ) ^ (gamma * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmin : min 1 (gamma * ((n : ℝ) + 1)) ≤
      gamma * ((n : ℝ) + 1) := min_le_right _ _
  have hminStep := mul_le_mul_of_nonneg_left hmin (mul_nonneg hA hN)
  rw [upperSaturatedProfile, upperPolyProfile]
  exact (mul_le_mul_of_nonneg_right hminStep hpow).trans_eq (by ring)

private theorem finiteQLtTwo_summable_upperSaturatedGridProfile
    (d : ℕ) {C cstar gamma s q : ℝ}
    (hC : 0 ≤ C) (hcstar : 0 ≤ cstar⁻¹) (hgamma : 0 ≤ gamma)
    (hs : 0 < s) (hs1 : s ≤ 1) (hq1 : 1 ≤ q)
    (hgap : 0 < 2 * s - gamma) :
    Summable fun k : ℕ => Book.Ch02.geometricWeight s q k *
      (gridBlockAmp d 1 (upperSaturatedPerCubeAmplitude C cstar gamma k) k) ^
        (q / 2) := by
  let A : ℝ := upperSaturatedGridProfileConst d C cstar gamma
  let rho : ℝ := 2 * s - gamma
  let Cgeom : ℝ := 96 * (A * gamma) * rho⁻¹ ^ 2
  let gamma' : ℝ := gamma + rho / 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact upperSaturatedGridProfileConst_nonneg d hC hcstar
  have hrho : 0 < rho := by simpa only [rho] using hgap
  have hrho2 : rho ≤ 2 := by
    dsimp only [rho]
    linarith
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hsq : 0 ≤ s * q := (mul_pos hs hq0).le
  have hCgeom : 0 ≤ Cgeom := by
    dsimp only [Cgeom]
    positivity
  have hgamma' : 0 ≤ gamma' := by
    dsimp only [gamma', rho]
    linarith
  have hgap' : 0 < 2 * s - gamma' := by
    have : 2 * s - gamma' = rho / 2 := by
      dsimp only [gamma', rho]
      ring
    rw [this]
    positivity
  have hsum : Summable fun k : ℕ => Book.Ch02.geometricWeight s q k *
      finiteQGeometricProfile Cgeom gamma' k ^ (q / 2) :=
    summable_geometricWeight_mul_finiteQGeometricProfile_rpow
      hCgeom hgap' hq0
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hsum
  · exact mul_nonneg (HCPolySupport.geometricWeight_nonneg k hsq)
      (Real.rpow_nonneg
        (gridBlockAmp_nonneg d 1
          (upperSaturatedPerCubeAmplitude_nonneg hC hcstar hgamma k) k) _)
  · have hEq :
        gridBlockAmp d 1 (upperSaturatedPerCubeAmplitude C cstar gamma k) k =
          upperSaturatedProfile A gamma k := by
      dsimp only [A]
      simpa only [gridBlockAmp] using
        gridNetConst_mul_upperSaturatedPerCubeAmplitude_eq
          d C cstar gamma k
    have hsat : upperSaturatedProfile A gamma k ≤
        upperPolyProfile (A * gamma) gamma k :=
      finiteQLtTwo_upperSaturatedProfile_le_upperPolyProfile hA k
    have hpoly : upperPolyProfile (A * gamma) gamma k ≤
        finiteQGeometricProfile Cgeom gamma' k := by
      simpa only [Cgeom, gamma', rho] using
        upperPolyProfile_le_finiteQGeometricProfile
          (mul_nonneg hA hgamma) hrho hrho2 gamma k
    refine mul_le_mul_of_nonneg_left ?_
      (HCPolySupport.geometricWeight_nonneg k hsq)
    rw [hEq]
    exact Real.rpow_le_rpow
      (upperSaturatedProfile_nonneg hA hgamma k) (hsat.trans hpoly) (by positivity)

private theorem finiteQLtTwo_upperSaturatedGridProfile_pred_budget
    (d : ℕ) {C cstar gamma s q : ℝ}
    (hC : 0 ≤ C) (hcstar : 0 ≤ cstar⁻¹) (hgamma : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hgap : 0 < 2 * s - gamma) :
    Summable (fun n : ℕ => Book.Ch02.geometricWeight s q n *
        (gridBlockAmp d 1
          (upperSaturatedPerCubeAmplitude C cstar gamma n.pred) n.pred) ^
            (q / 2)) ∧
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        (gridBlockAmp d 1
          (upperSaturatedPerCubeAmplitude C cstar gamma n.pred) n.pred) ^
            (q / 2)) ^ (2 / q) ≤
        12288 * upperSaturatedGridProfileBound d C cstar * s * gamma *
          (2 * s - gamma)⁻¹ ^ 3 := by
  let P : ℕ → ℝ := fun k =>
    gridBlockAmp d 1 (upperSaturatedPerCubeAmplitude C cstar gamma k) k
  let F : ℕ → ℝ := fun n =>
    Book.Ch02.geometricWeight s q n * P n.pred ^ (q / 2)
  let G : ℕ → ℝ := fun k =>
    Book.Ch02.geometricWeight s q k * P k ^ (q / 2)
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hsq : 0 ≤ s * q := (mul_pos hs hq0).le
  have hP : ∀ k, 0 ≤ P k := fun k => by
    dsimp only [P]
    exact gridBlockAmp_nonneg d 1
      (upperSaturatedPerCubeAmplitude_nonneg hC hcstar hgamma k) k
  have hGsum : Summable G := by
    simpa only [G, P] using
      finiteQLtTwo_summable_upperSaturatedGridProfile d hC hcstar hgamma
        hs hs1 hq1 hgap
  have htailLe : ∀ k, F (k + 1) ≤ G k := by
    intro k
    dsimp only [F, G]
    rw [Nat.pred_succ]
    exact mul_le_mul_of_nonneg_right
      (geometricWeight_succ_le_self hsq k)
      (Real.rpow_nonneg (hP k) _)
  have htail : Summable fun k => F (k + 1) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg
        (HCPolySupport.geometricWeight_nonneg (k + 1) hsq)
        (Real.rpow_nonneg (hP k) _)) htailLe hGsum
  have hFsum : Summable F := (summable_nat_add_iff 1).mp htail
  have hT0 : 0 ≤ ∑' k, G k := tsum_nonneg fun k =>
    mul_nonneg (HCPolySupport.geometricWeight_nonneg k hsq)
      (Real.rpow_nonneg (hP k) _)
  have hF0 : F 0 ≤ ∑' k, G k := by
    have hterm := hGsum.le_tsum 0 (fun k _ =>
      mul_nonneg (HCPolySupport.geometricWeight_nonneg k hsq)
        (Real.rpow_nonneg (hP k) _))
    simpa only [F, G, Nat.pred_zero] using hterm
  have htailTsum : (∑' k, F (k + 1)) ≤ ∑' k, G k :=
    htail.tsum_le_tsum htailLe hGsum
  have hsumLe : (∑' n, F n) ≤ 2 * ∑' k, G k := by
    rw [hFsum.tsum_eq_zero_add]
    linarith
  have hS0 : 0 ≤ ∑' n, F n := tsum_nonneg fun n =>
    mul_nonneg (HCPolySupport.geometricWeight_nonneg n hsq)
      (Real.rpow_nonneg (hP n.pred) _)
  have hp0 : 0 ≤ 2 / q := by positivity
  have hp2 : 2 / q ≤ 2 := by
    rw [div_le_iff₀ hq0]
    linarith
  have htwo : (2 : ℝ) ^ (2 / q) ≤ 4 := by
    calc
      (2 : ℝ) ^ (2 / q) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
      _ = 4 := by norm_num
  have hGbudget : (∑' k, G k) ^ (2 / q) ≤
      3072 * upperSaturatedGridProfileBound d C cstar * s * gamma *
        (2 * s - gamma)⁻¹ ^ 3 := by
    simpa only [G, P, gridBlockAmp] using
      upperSaturatedGridProfile_enlarged_aggregate_le
        d hC hcstar hgamma hgamma1 hs hs1 hq1 hq2 hgap
  refine ⟨by simpa only [F, P] using hFsum, ?_⟩
  change (∑' n, F n) ^ (2 / q) ≤ _
  calc
    (∑' n, F n) ^ (2 / q) ≤ (2 * ∑' k, G k) ^ (2 / q) :=
      Real.rpow_le_rpow hS0 hsumLe hp0
    _ = (2 : ℝ) ^ (2 / q) * (∑' k, G k) ^ (2 / q) := by
      rw [Real.mul_rpow (by norm_num) hT0]
    _ ≤ 4 * (∑' k, G k) ^ (2 / q) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hT0 _)
    _ ≤ 4 * (3072 * upperSaturatedGridProfileBound d C cstar * s * gamma *
          (2 * s - gamma)⁻¹ ^ 3) :=
      mul_le_mul_of_nonneg_left hGbudget (by norm_num)
    _ = 12288 * upperSaturatedGridProfileBound d C cstar * s * gamma *
          (2 * s - gamma)⁻¹ ^ 3 := by ring

/-- The strengthened rare normalizer shared with the other two upper-exponent
branches.  The second triangle factor is needed by the `q ≥ 2` fold and is
harmless in the present `q < 2` branch. -/
noncomputable def upperFiniteQLtTwoRareBudgetConst (d : ℕ) : ℝ :=
  4 * upperAfterBandRareTriangleConst ^ 2 * (1658880 : ℝ) ^ 2 *
    upperAfterBandRareGridNetConst d

private theorem upperFiniteQLtTwoRareBudgetConst_pos
    {d : ℕ} (hd : 2 ≤ d) :
    0 < upperFiniteQLtTwoRareBudgetConst d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [upperFiniteQLtTwoRareBudgetConst,
    upperAfterBandRareTriangleConst, upperAfterBandRareGridNetConst]
  positivity

private theorem finiteQLtTwo_rpow_add_le_two_mul_add_rpow
    {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    (x + y) ^ p ≤ 2 * (x ^ p + y ^ p) := by
  have hcoeff : (2 : ℝ) ^ (p - 1) ≤ 2 := by
    calc
      (2 : ℝ) ^ (p - 1) ≤ (2 : ℝ) ^ (1 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        linarith
      _ = 2 := Real.rpow_one 2
  exact (rpow_add_le_mul_rpow_add_rpow hx hy hp1).trans
    (mul_le_mul_of_nonneg_right hcoeff
      (add_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)))

private theorem finiteQLtTwo_rare_strict_weighted_term_le
    (d : ℕ) {s q sigma K eps gamma : ℝ}
    (hs : 0 < s) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hK : 0 < K) (heps : 0 < eps)
    (hp : sigma⁻¹ ≤ (6 : ℝ)) (k : ℕ) :
    Book.Ch02.geometricWeight s q (k + 1) *
        (gridBlockAmp d sigma
          (K⁻¹ * (3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) * eps ^ 15) k) ^
            (q / 2) ≤
      (gridNetConst d sigma * K⁻¹ * eps ^ 15) ^ (q / 2) *
        (((k : ℝ) + 1) ^ 6 *
          gridWeight ((q / 2) * (2 * s - gamma)) k) := by
  let t : ℝ := q / 2
  let rho : ℝ := t * (2 * s - gamma)
  let N : ℝ := (k : ℝ) + 1
  let base : ℝ := gridNetConst d sigma * K⁻¹ * eps ^ 15
  let amp : ℝ := K⁻¹ * (3 : ℝ) ^ (gamma * N) * eps ^ 15
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; linarith
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hNpow0 : 0 ≤ N ^ 6 := pow_nonneg (zero_le_one.trans hN1) 6
  have hamp0 : 0 ≤ amp := by
    dsimp only [amp]
    positivity
  have hbase0 : 0 ≤ base := by
    dsimp only [base]
    exact mul_nonneg
      (mul_nonneg (gridNetConst_nonneg d sigma) (inv_nonneg.mpr hK.le))
      (pow_nonneg heps.le 15)
  have hgridAmp0 : 0 ≤ gridBlockAmp d sigma amp k :=
    gridBlockAmp_nonneg d sigma hamp0 k
  have hampLe : gridBlockAmp d sigma amp k ≤
      gridNetConst d sigma * amp * N ^ 6 := by
    simpa only [N] using gridBlockAmp_le_natPow hamp0 6 hp k
  have hmajorEq : gridNetConst d sigma * amp * N ^ 6 =
      base * N ^ 6 * (3 : ℝ) ^ (gamma * N) := by
    dsimp only [amp, base]
    ring
  have hNpow : (N ^ 6) ^ t ≤ N ^ 6 := by
    calc
      (N ^ 6) ^ t ≤ (N ^ 6) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hN1) ht1
      _ = N ^ 6 := Real.rpow_one _
  have hdisc : Book.Ch02.geometricDiscount s q ≤ 1 := by
    rw [Book.Ch02.geometricDiscount]
    exact sub_le_self 1 (Real.rpow_nonneg (by norm_num) _)
  have hdisc0 : 0 ≤ Book.Ch02.geometricDiscount s q :=
    HCPolySupport.geometricDiscount_nonneg
      (mul_nonneg hs.le (zero_le_one.trans hq1))
  have hexp :
      (3 : ℝ) ^ (-s * q * (((k + 1 : ℕ) : ℝ))) *
          ((3 : ℝ) ^ (gamma * N)) ^ t = gridWeight rho k := by
    have hgrid : gridWeight rho k =
        (3 : ℝ) ^ (-rho * (((k + 1 : ℕ) : ℝ))) := by
      rw [gridWeight]
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-rho)) (k + 1),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hgrid]
    congr 1
    dsimp only [rho, t, N]
    push_cast
    ring
  change Book.Ch02.geometricWeight s q (k + 1) *
      (gridBlockAmp d sigma amp k) ^ t ≤
    base ^ t * (N ^ 6 * gridWeight rho k)
  calc
    Book.Ch02.geometricWeight s q (k + 1) *
        (gridBlockAmp d sigma amp k) ^ t ≤
      Book.Ch02.geometricWeight s q (k + 1) *
        (gridNetConst d sigma * amp * N ^ 6) ^ t :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hgridAmp0 hampLe ht0)
        (HCPolySupport.geometricWeight_nonneg (k + 1)
          (mul_nonneg hs.le (zero_le_one.trans hq1)))
    _ = Book.Ch02.geometricDiscount s q *
        (3 : ℝ) ^ (-s * q * (((k + 1 : ℕ) : ℝ))) *
          (base ^ t * (N ^ 6) ^ t *
            ((3 : ℝ) ^ (gamma * N)) ^ t) := by
      rw [Book.Ch02.geometricWeight, hmajorEq,
        Real.mul_rpow (mul_nonneg hbase0 hNpow0)
          (Real.rpow_nonneg (by norm_num) _),
        Real.mul_rpow hbase0 hNpow0]
      rw [show (((k + 1 : ℕ) : ℝ)) = N by simp [N]]
      rfl
    _ ≤ 1 * (3 : ℝ) ^ (-s * q * (((k + 1 : ℕ) : ℝ))) *
          (base ^ t * N ^ 6 * ((3 : ℝ) ^ (gamma * N)) ^ t) := by
      gcongr
    _ = base ^ t * (N ^ 6 * gridWeight rho k) := by
      rw [one_mul]
      rw [show
        (3 : ℝ) ^ (-s * q * (((k + 1 : ℕ) : ℝ))) *
            (base ^ t * N ^ 6 * ((3 : ℝ) ^ (gamma * N)) ^ t) =
          base ^ t * N ^ 6 *
            ((3 : ℝ) ^ (-s * q * (((k + 1 : ℕ) : ℝ))) *
              ((3 : ℝ) ^ (gamma * N)) ^ t) by ring,
        hexp]
      ring

private theorem finiteQLtTwo_polyGridWeight_six_eps_budget
    {rho eps : ℝ} (hrho : 0 < rho) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hepsRho : eps ≤ rho) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 6 * gridWeight rho k) ∧
      (∑' k : ℕ, ((k : ℝ) + 1) ^ 6 * gridWeight rho k) ≤
        92160 * eps⁻¹ ^ 7 := by
  have hsum := polyGridWeight_summable 6 hrho
  have hInvRhoEps : rho⁻¹ ≤ eps⁻¹ :=
    (inv_le_inv₀ hrho heps).2 hepsRho
  have hInvEps1 : 1 ≤ eps⁻¹ := one_le_inv_of_le_one heps heps1
  have hOneInv : 1 + rho⁻¹ ≤ 2 * eps⁻¹ := by linarith
  have hGeomInv : (1 - (3 : ℝ) ^ (-rho))⁻¹ ≤ 1 + rho⁻¹ :=
    one_sub_rpow_neg_inv_le hrho
  have hGeomInv0 : 0 ≤ (1 - (3 : ℝ) ^ (-rho))⁻¹ :=
    (inv_pos.mpr (one_sub_rpow_neg_pos hrho)).le
  have hOneInv0 : 0 ≤ 1 + rho⁻¹ := by positivity
  have hraw := polyGridWeight_tsum_le 6 hrho
  have hfirst : (1 - (3 : ℝ) ^ (-rho))⁻¹ ^ 7 ≤ (1 + rho⁻¹) ^ 7 :=
    pow_le_pow_left₀ hGeomInv0 hGeomInv 7
  have hsecond : (1 + rho⁻¹) ^ 7 ≤ (2 * eps⁻¹) ^ 7 :=
    pow_le_pow_left₀ hOneInv0 hOneInv 7
  norm_num [Nat.factorial] at hraw
  rw [← inv_pow] at hraw
  refine ⟨hsum, ?_⟩
  calc
    (∑' k : ℕ, ((k : ℝ) + 1) ^ 6 * gridWeight rho k) ≤
        720 * (1 - (3 : ℝ) ^ (-rho))⁻¹ ^ 7 := hraw
    _ ≤ 720 * (1 + rho⁻¹) ^ 7 :=
      mul_le_mul_of_nonneg_left hfirst (by norm_num)
    _ ≤ 720 * (2 * eps⁻¹) ^ 7 :=
      mul_le_mul_of_nonneg_left hsecond (by norm_num)
    _ = 92160 * eps⁻¹ ^ 7 := by ring

private theorem finiteQLtTwo_rareGridProfile_strict_tail_budget
    (d : ℕ) {s q sigma K eps gamma : ℝ}
    (hs : 0 < s) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hK : 0 < K) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hgap : 0 < 2 * s - gamma)
    (hwindow : 2 * eps ≤ 2 * s - gamma)
    (hp : sigma⁻¹ ≤ (6 : ℝ)) :
    Summable (fun k : ℕ => Book.Ch02.geometricWeight s q (k + 1) *
        (gridBlockAmp d sigma
          (K⁻¹ * (3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) * eps ^ 15) k) ^
            (q / 2)) ∧
      (∑' k : ℕ, Book.Ch02.geometricWeight s q (k + 1) *
        (gridBlockAmp d sigma
          (K⁻¹ * (3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) * eps ^ 15) k) ^
            (q / 2)) ^ (2 / q) ≤
        (92160 : ℝ) ^ 2 * gridNetConst d sigma * K⁻¹ * eps := by
  let t : ℝ := q / 2
  let p : ℝ := 2 / q
  let rho : ℝ := t * (2 * s - gamma)
  let base : ℝ := gridNetConst d sigma * K⁻¹ * eps ^ 15
  let F : ℕ → ℝ := fun k => Book.Ch02.geometricWeight s q (k + 1) *
    (gridBlockAmp d sigma
      (K⁻¹ * (3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) * eps ^ 15) k) ^ t
  let P : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ 6 * gridWeight rho k
  let H : ℕ → ℝ := fun k => base ^ t * P k
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have htHalf : (1 : ℝ) / 2 ≤ t := by dsimp only [t]; linarith
  have hp0 : 0 ≤ p := by dsimp only [p]; positivity
  have hp2 : p ≤ 2 := by
    dsimp only [p]
    rw [div_le_iff₀ hq0]
    linarith
  have htp : t * p = 1 := by
    dsimp only [t, p]
    field_simp [ne_of_gt hq0]
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hepsRho : eps ≤ rho := by
    calc
      eps = ((1 : ℝ) / 2) * (2 * eps) := by ring
      _ ≤ ((1 : ℝ) / 2) * (2 * s - gamma) :=
        mul_le_mul_of_nonneg_left hwindow (by norm_num)
      _ ≤ t * (2 * s - gamma) :=
        mul_le_mul_of_nonneg_right htHalf hgap.le
      _ = rho := by rfl
  have hbase0 : 0 ≤ base := by
    dsimp only [base]
    exact mul_nonneg
      (mul_nonneg (gridNetConst_nonneg d sigma) (inv_nonneg.mpr hK.le))
      (pow_nonneg heps.le 15)
  have hF0 : ∀ k, 0 ≤ F k := fun k => by
    dsimp only [F]
    exact mul_nonneg
      (HCPolySupport.geometricWeight_nonneg (k + 1)
        (mul_nonneg hs.le (zero_le_one.trans hq1)))
      (Real.rpow_nonneg (gridBlockAmp_nonneg d sigma (by positivity) k) _)
  obtain ⟨hPsum, hPbound⟩ :=
    finiteQLtTwo_polyGridWeight_six_eps_budget hrho heps heps1 hepsRho
  have hP0 : ∀ k, 0 ≤ P k := fun k => by
    dsimp only [P]
    exact mul_nonneg (pow_nonneg (by positivity) 6) (gridWeight_nonneg rho k)
  have hH0 : ∀ k, 0 ≤ H k := fun k =>
    mul_nonneg (Real.rpow_nonneg hbase0 _) (hP0 k)
  have hHsum : Summable H := hPsum.mul_left (base ^ t)
  have hFH : ∀ k, F k ≤ H k := fun k => by
    dsimp only [F, H, P]
    simpa only [base, t, rho] using
      finiteQLtTwo_rare_strict_weighted_term_le d hs hq1 hq2 hK heps hp k
  have hFsum : Summable F := Summable.of_nonneg_of_le hF0 hFH hHsum
  have hFtsum0 : 0 ≤ ∑' k, F k := tsum_nonneg hF0
  have hFtsumLe : (∑' k, F k) ≤ ∑' k, H k :=
    hFsum.tsum_le_tsum hFH hHsum
  have hPtsum0 : 0 ≤ ∑' k, P k := tsum_nonneg hP0
  have hHtsum : (∑' k, H k) = base ^ t * ∑' k, P k := by
    simpa only [H] using tsum_mul_left
  have hPmajor1 : 1 ≤ 92160 * eps⁻¹ ^ 7 := by
    have hpow1 : 1 ≤ eps⁻¹ ^ 7 :=
      one_le_pow₀ (one_le_inv_of_le_one heps heps1)
    linarith only [hpow1]
  have hPpower : (∑' k, P k) ^ p ≤
      (92160 : ℝ) ^ 2 * eps⁻¹ ^ 14 := by
    calc
      (∑' k, P k) ^ p ≤ (92160 * eps⁻¹ ^ 7) ^ p :=
        Real.rpow_le_rpow hPtsum0 hPbound hp0
      _ ≤ (92160 * eps⁻¹ ^ 7) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hPmajor1 hp2
      _ = (92160 : ℝ) ^ 2 * eps⁻¹ ^ 14 := by
        rw [Real.rpow_two]
        ring
  refine ⟨by simpa only [F, t] using hFsum, ?_⟩
  change (∑' k, F k) ^ p ≤ _
  calc
    (∑' k, F k) ^ p ≤ (∑' k, H k) ^ p :=
      Real.rpow_le_rpow hFtsum0 hFtsumLe hp0
    _ = (base ^ t * ∑' k, P k) ^ p := by rw [hHtsum]
    _ = (base ^ t) ^ p * (∑' k, P k) ^ p := by
      rw [Real.mul_rpow (Real.rpow_nonneg hbase0 _) hPtsum0]
    _ = base * (∑' k, P k) ^ p := by
      rw [← Real.rpow_mul hbase0, htp, Real.rpow_one]
    _ ≤ base * ((92160 : ℝ) ^ 2 * eps⁻¹ ^ 14) :=
      mul_le_mul_of_nonneg_left hPpower hbase0
    _ = (92160 : ℝ) ^ 2 * gridNetConst d sigma * K⁻¹ * eps := by
      dsimp only [base]
      field_simp [ne_of_gt heps]

private theorem finiteQLtTwo_rareGridProfile_zero_root_budget
    (d : ℕ) {s q sigma K eps gamma : ℝ}
    (hs : 0 < s) (hq1 : 1 ≤ q)
    (hK : 0 < K) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hgamma1 : gamma ≤ 1) (hp : sigma⁻¹ ≤ (6 : ℝ)) :
    (Book.Ch02.geometricWeight s q 0 *
        (gridBlockAmp d sigma
          (K⁻¹ * (3 : ℝ) ^ gamma * eps ^ 15) 0) ^ (q / 2)) ^ (2 / q) ≤
      3 * gridNetConst d sigma * K⁻¹ * eps := by
  let t : ℝ := q / 2
  let p : ℝ := 2 / q
  let base : ℝ := gridNetConst d sigma * K⁻¹ * eps ^ 15
  let A : ℝ := gridBlockAmp d sigma (K⁻¹ * (3 : ℝ) ^ gamma * eps ^ 15) 0
  let F0 : ℝ := Book.Ch02.geometricWeight s q 0 * A ^ t
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have hp0 : 0 ≤ p := by dsimp only [p]; positivity
  have htp : t * p = 1 := by
    dsimp only [t, p]
    field_simp [ne_of_gt hq0]
  have hbase0 : 0 ≤ base := by
    dsimp only [base]
    exact mul_nonneg
      (mul_nonneg (gridNetConst_nonneg d sigma) (inv_nonneg.mpr hK.le))
      (pow_nonneg heps.le 15)
  have hamp0 : 0 ≤ K⁻¹ * (3 : ℝ) ^ gamma * eps ^ 15 := by positivity
  have hA0 : 0 ≤ A := gridBlockAmp_nonneg d sigma hamp0 0
  have hF0nonneg : 0 ≤ F0 := by
    dsimp only [F0]
    exact mul_nonneg
      (HCPolySupport.geometricWeight_nonneg 0
        (mul_nonneg hs.le (zero_le_one.trans hq1)))
      (Real.rpow_nonneg hA0 _)
  have hgrid : A ≤ base * (3 : ℝ) ^ gamma := by
    have hraw := gridBlockAmp_le_natPow (d := d) hamp0 6 hp 0
    dsimp only [A, base] at hraw ⊢
    norm_num at hraw ⊢
    exact hraw.trans_eq (by ring)
  have hw0 : Book.Ch02.geometricWeight s q 0 ≤ 1 := by
    rw [Book.Ch02.geometricWeight]
    norm_num
    exact sub_le_self 1 (Real.rpow_nonneg (by norm_num) _)
  have hbaseGamma0 : 0 ≤ base * (3 : ℝ) ^ gamma :=
    mul_nonneg hbase0 (Real.rpow_nonneg (by norm_num) _)
  have hF0Le : F0 ≤ (base * (3 : ℝ) ^ gamma) ^ t := by
    dsimp only [F0]
    calc
      Book.Ch02.geometricWeight s q 0 * A ^ t ≤ 1 * A ^ t :=
        mul_le_mul_of_nonneg_right hw0 (Real.rpow_nonneg hA0 _)
      _ ≤ (base * (3 : ℝ) ^ gamma) ^ t := by
        rw [one_mul]
        exact Real.rpow_le_rpow hA0 hgrid ht0
  have hthreeGamma : (3 : ℝ) ^ gamma ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hgamma1
  have hepsPow : eps ^ 15 ≤ eps := by
    calc
      eps ^ 15 = eps * eps ^ 14 := by ring
      _ ≤ eps * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ heps.le heps1) heps.le
      _ = eps := by ring
  change F0 ^ p ≤ _
  calc
    F0 ^ p ≤ ((base * (3 : ℝ) ^ gamma) ^ t) ^ p :=
      Real.rpow_le_rpow hF0nonneg hF0Le hp0
    _ = base * (3 : ℝ) ^ gamma := by
      rw [← Real.rpow_mul hbaseGamma0, htp, Real.rpow_one]
    _ ≤ 3 * base := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hthreeGamma hbase0
    _ ≤ 3 * (gridNetConst d sigma * K⁻¹ * eps) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hepsPow
          (mul_nonneg (gridNetConst_nonneg d sigma) (inv_nonneg.mpr hK.le)))
        (by norm_num)
    _ = 3 * gridNetConst d sigma * K⁻¹ * eps := by ring

private theorem finiteQLtTwo_rareGridProfile_pred_budget
    (d : ℕ) {s q sigma K eps gamma : ℝ}
    (hs : 0 < s) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hK : 0 < K) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hgamma1 : gamma ≤ 1)
    (hgap : 0 < 2 * s - gamma)
    (hwindow : 2 * eps ≤ 2 * s - gamma)
    (hp : sigma⁻¹ ≤ (6 : ℝ)) :
    Summable (fun n : ℕ => Book.Ch02.geometricWeight s q n *
        (gridBlockAmp d sigma
          (K⁻¹ * (3 : ℝ) ^ (gamma * ((n.pred : ℝ) + 1)) * eps ^ 15)
          n.pred) ^ (q / 2)) ∧
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        (gridBlockAmp d sigma
          (K⁻¹ * (3 : ℝ) ^ (gamma * ((n.pred : ℝ) + 1)) * eps ^ 15)
          n.pred) ^ (q / 2)) ^ (2 / q) ≤
        (1658880 : ℝ) ^ 2 * gridNetConst d sigma * K⁻¹ * eps := by
  let F : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s q n *
    (gridBlockAmp d sigma
      (K⁻¹ * (3 : ℝ) ^ (gamma * ((n.pred : ℝ) + 1)) * eps ^ 15)
      n.pred) ^ (q / 2)
  have htail := finiteQLtTwo_rareGridProfile_strict_tail_budget d hs hq1 hq2
    hK heps heps1 hgap hwindow hp
  have htailSum : Summable fun k => F (k + 1) := by
    simpa only [F, Nat.pred_succ] using htail.1
  have hFsum : Summable F := (summable_nat_add_iff 1).mp htailSum
  have hF0 : ∀ n, 0 ≤ F n := fun n => by
    dsimp only [F]
    exact mul_nonneg
      (HCPolySupport.geometricWeight_nonneg n
        (mul_nonneg hs.le (zero_le_one.trans hq1)))
      (Real.rpow_nonneg (gridBlockAmp_nonneg d sigma (by positivity) n.pred) _)
  have htailTsum0 : 0 ≤ ∑' k, F (k + 1) := tsum_nonneg fun k => hF0 (k + 1)
  have htailRoot : (∑' k, F (k + 1)) ^ (2 / q) ≤
      (92160 : ℝ) ^ 2 * gridNetConst d sigma * K⁻¹ * eps := by
    simpa only [F, Nat.pred_succ] using htail.2
  have hzeroRoot : (F 0) ^ (2 / q) ≤
      3 * gridNetConst d sigma * K⁻¹ * eps := by
    simpa only [F, Nat.pred_zero, Nat.cast_zero, zero_add, zero_mul,
      Real.rpow_zero, one_mul, mul_one] using
      finiteQLtTwo_rareGridProfile_zero_root_budget d hs hq1 hK heps heps1
        hgamma1 hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hp1 : 1 ≤ 2 / q := by rw [le_div_iff₀ hq0]; linarith
  have hp2 : 2 / q ≤ 2 := by rw [div_le_iff₀ hq0]; linarith
  let common : ℝ := gridNetConst d sigma * K⁻¹ * eps
  have hcommon0 : 0 ≤ common := by
    dsimp only [common]
    exact mul_nonneg
      (mul_nonneg (gridNetConst_nonneg d sigma) (inv_nonneg.mpr hK.le)) heps.le
  have hsumEq : (∑' n, F n) = F 0 + ∑' k, F (k + 1) :=
    hFsum.tsum_eq_zero_add
  refine ⟨by simpa only [F] using hFsum, ?_⟩
  change (∑' n, F n) ^ (2 / q) ≤ _
  rw [hsumEq]
  calc
    (F 0 + ∑' k, F (k + 1)) ^ (2 / q) ≤
        2 * ((F 0) ^ (2 / q) + (∑' k, F (k + 1)) ^ (2 / q)) :=
      finiteQLtTwo_rpow_add_le_two_mul_add_rpow (hF0 0) htailTsum0 hp1 hp2
    _ ≤ 2 * (3 * common + (92160 : ℝ) ^ 2 * common) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
      · simpa only [common, mul_assoc] using hzeroRoot
      · simpa only [common, mul_assoc] using htailRoot
    _ ≤ (1658880 : ℝ) ^ 2 * common := by linarith only [hcommon0]
    _ = (1658880 : ℝ) ^ 2 * gridNetConst d sigma * K⁻¹ * eps := by
      dsimp only [common]
      ring

/-- The finite-`q < 2` upper carrier from the normalized per-descendant split.
All deterministic scale summability and budget obligations are discharged in
this theorem; the caller supplies only the normalized block split and the two
dimension-only merge inequalities. -/
theorem upper_finite_lt_two_of_per_descendant
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (m : ℤ)
    (r : {r : ℝ // 1 ≤ r}) (hr : (r : ℝ) < 2)
    {sigma s scaling Cblock eps Cup : ℝ}
    (hsigma0 : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hs : 0 < s) (hs1 : s ≤ 1) (hscaling : 0 ≤ scaling)
    (hCblock : 0 < Cblock) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hwin : M.gamma / 2 + eps ≤ s)
    (hCup : 0 < Cup)
    (hdetHead : 4 * Cblock ≤ Cup)
    (hordinaryHead :
      147456 * gammaTriangleConst 1 * gridNetConst d 1 * Cblock ≤ Cup)
    (hper : ∀ (k : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
        ∃ Uone Uexp : Cutoff.CutoffSample d → ℝ,
          (∀ omega, 0 ≤ Uone omega) ∧
          Measurable Uone ∧
          (∀ omega, 0 ≤ Uexp omega) ∧
          Measurable Uexp ∧
          (∀ omega,
            cutoffBBlockFamily M m scaling R omega ≤
              Cblock + Uone omega + Uexp omega) ∧
          IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
            (gammaSigma 1) Uone
            (upperSaturatedPerCubeAmplitude Cblock
              (Disorder.cstar M) M.gamma k) ∧
          IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
            (gammaSigma ((1 - sigma) / 3)) Uexp
            ((upperFiniteQLtTwoRareBudgetConst d)⁻¹ *
              (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 15)) :
    Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (gammaSigma ((1 - sigma) / 3))
      (fun omega =>
        Observable.cutoffUpperEllipticity M m m s hs
          (CoarseEllipticityExponent.finite r) omega * scaling)
      Cup
      (Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
        (2 * s - M.gamma)⁻¹ ^ 3)
      eps := by
  let sigmaExp : ℝ := (1 - sigma) / 3
  let Krare : ℝ := upperFiniteQLtTwoRareBudgetConst d
  let B1 : ℝ := Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
    (2 * s - M.gamma)⁻¹ ^ 3
  have hsigmaExp : 0 < sigmaExp := by
    dsimp only [sigmaExp]
    linarith
  have hp : sigmaExp⁻¹ ≤ (6 : ℝ) := by
    dsimp only [sigmaExp]
    exact frozenUpperIndex_inv_le_natSix hsigmaHalf
  have hgamma0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hgamma1 : M.gamma ≤ 1 := by
    linarith [M.shellPrefix.gamma_le_quarter]
  have hgap : 0 < 2 * s - M.gamma := by
    linarith
  have hwindow : 2 * eps ≤ 2 * s - M.gamma := by
    linarith
  have hcstar : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hKrare : 0 < Krare := by
    dsimp only [Krare]
    exact upperFiniteQLtTwoRareBudgetConst_pos hd
  have hordinary := finiteQLtTwo_upperSaturatedGridProfile_pred_budget d
    hCblock.le (inv_nonneg.mpr hcstar.le) hgamma0 hgamma1 hs hs1
      r.property (le_of_lt hr) hgap
  have hrare := finiteQLtTwo_rareGridProfile_pred_budget d hs r.property
    (le_of_lt hr) hKrare heps heps1 hgamma1 hgap hwindow hp
  have hB1pos : 0 < B1 := by
    dsimp only [B1]
    exact mul_pos
      (mul_pos (mul_pos (mul_pos hCup (inv_pos.mpr hcstar)) hs)
        M.shellPrefix.gamma_pos)
      (pow_pos (inv_pos.mpr hgap) 3)
  have hordinaryBudget :
      (4 * (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
        (gridBlockAmp d 1
          (upperSaturatedPerCubeAmplitude Cblock
            (Disorder.cstar M) M.gamma n.pred) n.pred) ^ ((r : ℝ) / 2)) ^
          (2 / (r : ℝ))) * gammaTriangleConst 1 ≤ B1 := by
    have hmult0 : 0 ≤ 4 * gammaTriangleConst 1 :=
      mul_nonneg (by norm_num) gammaTriangleConst_pos.le
    have hprofile0 : 0 ≤ (Disorder.cstar M)⁻¹ * s * M.gamma *
        (2 * s - M.gamma)⁻¹ ^ 3 := by positivity
    calc
      (4 * (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
        (gridBlockAmp d 1
          (upperSaturatedPerCubeAmplitude Cblock
            (Disorder.cstar M) M.gamma n.pred) n.pred) ^ ((r : ℝ) / 2)) ^
          (2 / (r : ℝ))) * gammaTriangleConst 1 ≤
        (4 * (12288 * upperSaturatedGridProfileBound d Cblock
          (Disorder.cstar M) * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3)) * gammaTriangleConst 1 := by
          simpa only [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right hordinary.2 hmult0
      _ = (147456 * gammaTriangleConst 1 * gridNetConst d 1 * Cblock) *
          ((Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3) := by
        rw [upperSaturatedGridProfileBound]
        ring
      _ ≤ Cup * ((Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3) :=
        mul_le_mul_of_nonneg_right hordinaryHead hprofile0
      _ = B1 := by
        dsimp only [B1]
        ring
  have hTbar1 : 1 ≤ upperAfterBandRareTriangleConst := by
    rw [upperAfterBandRareTriangleConst]
    have hpow : 1 ≤ (117649 : ℝ) ^ (12 : ℝ) :=
      Real.one_le_rpow (by norm_num) (by norm_num)
    linarith only [hpow]
  have hTbar0 : 0 ≤ upperAfterBandRareTriangleConst := zero_le_one.trans hTbar1
  have hGbar0 : 0 ≤ upperAfterBandRareGridNetConst d := by
    rw [upperAfterBandRareGridNetConst]
    exact Real.rpow_nonneg (by positivity) _
  have htriangle : gammaTriangleConst sigmaExp ≤
      upperAfterBandRareTriangleConst := by
    dsimp only [sigmaExp]
    exact gammaTriangleConst_upperProfileTarget_le hsigma0 hsigmaHalf
  have hgrid : gridNetConst d sigmaExp ≤
      upperAfterBandRareGridNetConst d := by
    dsimp only [sigmaExp]
    exact gridNetConst_upperProfileTarget_le hd hsigma0 hsigmaHalf
  have hTSquare : upperAfterBandRareTriangleConst ≤
      upperAfterBandRareTriangleConst ^ 2 := by
    calc
      upperAfterBandRareTriangleConst =
          1 * upperAfterBandRareTriangleConst := by ring
      _ ≤ upperAfterBandRareTriangleConst * upperAfterBandRareTriangleConst :=
        mul_le_mul_of_nonneg_right hTbar1 hTbar0
      _ = upperAfterBandRareTriangleConst ^ 2 := by ring
  have hcoef :
      4 * (1658880 : ℝ) ^ 2 * gridNetConst d sigmaExp *
          gammaTriangleConst sigmaExp ≤ Krare := by
    have hGT : gridNetConst d sigmaExp * gammaTriangleConst sigmaExp ≤
        upperAfterBandRareGridNetConst d * upperAfterBandRareTriangleConst := by
      calc
        gridNetConst d sigmaExp * gammaTriangleConst sigmaExp ≤
            upperAfterBandRareGridNetConst d * gammaTriangleConst sigmaExp :=
          mul_le_mul_of_nonneg_right hgrid gammaTriangleConst_pos.le
        _ ≤ upperAfterBandRareGridNetConst d *
            upperAfterBandRareTriangleConst :=
          mul_le_mul_of_nonneg_left htriangle hGbar0
    calc
      4 * (1658880 : ℝ) ^ 2 * gridNetConst d sigmaExp *
          gammaTriangleConst sigmaExp =
        (4 * (1658880 : ℝ) ^ 2) *
          (gridNetConst d sigmaExp * gammaTriangleConst sigmaExp) := by ring
      _ ≤ (4 * (1658880 : ℝ) ^ 2) *
          (upperAfterBandRareGridNetConst d *
            upperAfterBandRareTriangleConst) :=
        mul_le_mul_of_nonneg_left hGT (by positivity)
      _ ≤ (4 * (1658880 : ℝ) ^ 2) *
          (upperAfterBandRareGridNetConst d *
            upperAfterBandRareTriangleConst ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hTSquare hGbar0) (by positivity)
      _ = Krare := by
        dsimp only [Krare, upperFiniteQLtTwoRareBudgetConst]
        ring
  have hrareBudget :
      (4 * (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
        (gridBlockAmp d sigmaExp
          (Krare⁻¹ *
            (3 : ℝ) ^ (M.gamma * ((n.pred : ℝ) + 1)) * eps ^ 15)
          n.pred) ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ))) *
        gammaTriangleConst sigmaExp ≤ eps := by
    have hmult0 : 0 ≤ 4 * gammaTriangleConst sigmaExp :=
      mul_nonneg (by norm_num) gammaTriangleConst_pos.le
    calc
      (4 * (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
        (gridBlockAmp d sigmaExp
          (Krare⁻¹ *
            (3 : ℝ) ^ (M.gamma * ((n.pred : ℝ) + 1)) * eps ^ 15)
          n.pred) ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ))) *
          gammaTriangleConst sigmaExp ≤
        (4 * ((1658880 : ℝ) ^ 2 * gridNetConst d sigmaExp *
          Krare⁻¹ * eps)) * gammaTriangleConst sigmaExp := by
          simpa only [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right hrare.2 hmult0
      _ = (4 * (1658880 : ℝ) ^ 2 * gridNetConst d sigmaExp *
          gammaTriangleConst sigmaExp) * (Krare⁻¹ * eps) := by ring
      _ ≤ Krare * (Krare⁻¹ * eps) :=
        mul_le_mul_of_nonneg_right hcoef
          (mul_nonneg (inv_nonneg.mpr hKrare.le) heps.le)
      _ = eps := by
        rw [← mul_assoc, mul_inv_cancel₀ hKrare.ne', one_mul]
  obtain ⟨Udet, Uone, Utail, hdom, hdet, hUoneM, hUtailM,
      hUoneO, hUtailO⟩ :=
    finiteQLtTwoSplit_of_perDescendantAndBudgets
      (hd := by omega) M m r hr
      (s := s) (scaling := scaling) (Cblock := Cblock)
      (Krare := Krare) (eps := eps) (Bdet := Cup) (B1 := B1)
      (Bexp := eps) (sigmaExp := sigmaExp)
      hs hscaling hCblock hKrare heps hsigmaExp
      (by simpa only [Krare, sigmaExp] using hper)
      hordinary.1 hrare.1 hdetHead hordinaryBudget hrareBudget
  rw [Probability.deterministicShiftTwoTermOneSidedOrlicz_iff_exists]
  refine ⟨Uone, Utail, Probability.isAdmissibleTail_gammaSigma one_pos,
    Probability.isAdmissibleTail_gammaSigma hsigmaExp, hB1pos, heps,
    (Observable.measurable_cutoffUpperEllipticity M m m s hs
      (CoarseEllipticityExponent.finite r)).mul_const scaling,
    hUoneM, hUtailM, ?_, hUoneO, hUtailO⟩
  intro omega
  have hdomOmega := hdom omega
  have hdetOmega := hdet omega
  linarith

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
