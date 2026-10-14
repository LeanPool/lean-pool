/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperFiniteQLtTwo
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCommonEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperSaturatedOrdinaryComparison
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileCloseEndpoint
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerSeries
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AESummability
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandRareAbsorption

/-!
# UpperFiniteQGeTwoInfinityAggregation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Upper aggregation for finite exponents at least two and infinity

This module aggregates a strict-descendant per-cube decomposition through the
joint grid-and-depth ordinary envelope and the normalized rare folded pole.  Its
public theorem supplies both the finite-`q ≥ 2` and `q = ∞` upper Orlicz
bounds from the same per-descendant estimate.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

private abbrev upperFiniteQGeTwoInfinityAggregation_momentBounds3_statement : Prop :=
    ∀ {d : ℕ} (_ : (1 : ℕ) ≤ d) (M : ABKModel d) (m : ℤ) {s scaling Cblock Krare eps Bexp sigmaExp
      : ℝ}
      (_ : (0 : ℝ) < Cblock) (_ : (0 : ℝ) < sigmaExp) (_ : M.gamma ≤ (1 : ℝ))
      (_ : sigmaExp⁻¹ ≤ (6 : ℝ))
      (_ :
        foldedBlockPole d sigmaExp (Krare⁻¹ * eps ^ (15 : ℕ)) (1 : ℝ) ((2 : ℝ) * s - M.gamma) ((3
          : ℝ) ^ ((2 : ℝ) * s))
            (6 : ℕ) ≤
          Bexp)
      (hper :
        ∀ (k : ℕ),
          ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
            ∃ (Uone : Cutoff.CutoffSample d → ℝ) (Uexp : Cutoff.CutoffSample d → ℝ),
              (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uone omega) ∧
                Measurable Uone ∧
                  (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uexp omega) ∧
                    Measurable Uexp ∧
                      (∀ (omega : Cutoff.CutoffSample d),
                          cutoffBBlockFamily M m scaling R omega ≤ Cblock + Uone omega + Uexp
                            omega) ∧
                        IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
                          (gammaSigma (1 : ℝ)) Uone
                            (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M) M.gamma k) ∧
                          IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
                            d)) (gammaSigma sigmaExp)
                            Uexp (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * eps ^ (15
                              : ℕ))),
      let mu : Measure (Cutoff.CutoffSample d) := (↑(Cutoff.cutoffSampleLaw M) : Measure
        (Cutoff.CutoffSample d));
      let gamma : ℝ := M.gamma;
      let rho : ℝ := (2 : ℝ) * s - gamma;
      let abase : ℝ := Krare⁻¹ * eps ^ (15 : ℕ);
      let ctop : ℝ := (3 : ℝ) ^ ((2 : ℝ) * s);
      let A : ℝ := upperOrdinaryJointProfileBound d Cblock (Disorder.cstar M) gamma;
      ∀ (_ : (0 : ℝ) < rho) (_ : (0 : ℝ) < Disorder.cstar M) (_ : (0 : ℝ) < abase) (_ : (0 : ℝ) <
        ctop),
        let UoneCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R :
          TriadicCube d) =>
          if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
            Classical.choose (hper k R hR)
          else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
        let UexpCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R :
          TriadicCube d) =>
          if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
            Classical.choose (Classical.choose_spec (hper k R hR))
          else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
        ∀
          (_ :
            ∀ (k : ℕ) (R : TriadicCube d) (omega : Cutoff.CutoffSample d),
              (0 : ℝ) ≤
                (fun (k : ℕ) (R : TriadicCube d) =>
                    if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
                      Classical.choose (hper k R hR)
                    else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                  k R omega)
          (_ :
            ∀ (k : ℕ) (R : TriadicCube d) (omega : Cutoff.CutoffSample d),
              (0 : ℝ) ≤
                (fun (k : ℕ) (R : TriadicCube d) =>
                    if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
                      Classical.choose (Classical.choose_spec (hper k R hR))
                    else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                  k R omega)
          (_ :
            ∀ (k : ℕ) (R : TriadicCube d),
              Measurable
                ((fun (k : ℕ) (R : TriadicCube d) =>
                    if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
                      Classical.choose (hper k R hR)
                    else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                  k R))
          (_ :
            ∀ (k : ℕ),
              ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
                IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
                  (gammaSigma (1 : ℝ))
                  ((fun (k : ℕ) (R : TriadicCube d) =>
                      if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
                        Classical.choose (hper k R hR)
                      else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                    k R)
                  (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M) M.gamma k))
          (_ :
            ∀ (k : ℕ),
              ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
                IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
                  (gammaSigma sigmaExp)
                  ((fun (k : ℕ) (R : TriadicCube d) =>
                      if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
                        Classical.choose (Classical.choose_spec (hper k R hR))
                      else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                    k R)
                  ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * (Krare⁻¹ * eps ^ (15 : ℕ)))),
          let Gone : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k (UoneCube
            k);
          let Gexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k (UexpCube
            k);
          ∀ (_ : ∀ (k : ℕ) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Gexp k omega)
            (_ : ∀ (k : ℕ), Measurable (Gexp k)),
            let aone : ℕ → ℝ := fun (k : ℕ) => upperSaturatedPerCubeAmplitude Cblock
              (Disorder.cstar M) gamma k;
            ∀ (_ : ∀ (k : ℕ), (0 : ℝ) < aone k),
              ∃ (_ :
                (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ jointGridDepthEnvelope d m UoneCube
                  aone omega) ∧
                  Measurable (jointGridDepthEnvelope d m UoneCube aone) ∧
                    IsBigOWith mu (gammaSigma (1 : ℝ)) (jointGridDepthEnvelope d m UoneCube aone)
                      (1 : ℝ) ∧
                      ∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu,
                        ∀ (k : ℕ),
                          ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
                            UoneCube k R omega ≤
                              triadicJointDepthEntropyConst d * ((↑k : ℝ) + (1 : ℝ)) * aone k *
                                jointGridDepthEnvelope d m UoneCube aone omega)
                (_ :
                ∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu,
                  ∀ (k : ℕ), Gone k omega ≤ upperPolyProfile A gamma k * jointGridDepthEnvelope d
                    m UoneCube aone omega)
                (_ : ∀ (k : ℕ), (0 : ℝ) < (fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 :
                  ℝ)))) k) (_ :
                ∀ (k : ℕ) (omega : Cutoff.CutoffSample d),
                  (0 : ℝ) ≤
                    (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                        ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ)))) k)⁻¹ * Gexp k
                          omega)
                      k omega)
                (_ :
                ∀ (k : ℕ) (omega : Cutoff.CutoffSample d),
                  (fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ)))) k *
                      (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                          ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ)))) k)⁻¹ * Gexp k
                            omega)
                        k omega =
                    Gexp k omega)
                (_ :
                ∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu,
                  Summable fun (k : ℕ) =>
                    (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                        gridWeight rho k *
                          (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                              ctop *
                                  (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                      ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ))))
                                        k)⁻¹ * Gexp k omega)
                                    (0 : ℕ) omega +
                                (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                    ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ))))
                                      k)⁻¹ * Gexp k omega)
                                  k omega)
                            k omega)
                      k omega)
                (hRrawAE :
                AEMeasurable
                  (fun (omega : Cutoff.CutoffSample d) =>
                    ∑' (k : ℕ),
                      (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                          gridWeight rho k *
                            (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                ctop *
                                    (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                        ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ))))
                                          k)⁻¹ * Gexp k omega)
                                      (0 : ℕ) omega +
                                  (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                      ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ))))
                                        k)⁻¹ * Gexp k omega)
                                    k omega)
                              k omega)
                        k omega)
                  mu)
                (_ :
                Measurable
                  (AEMeasurable.mk
                    (fun (omega : Cutoff.CutoffSample d) =>
                      ∑' (k : ℕ),
                        (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                            gridWeight rho k *
                              (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                  ctop *
                                      (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                          ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 :
                                            ℝ)))) k)⁻¹ * Gexp k omega)
                                        (0 : ℕ) omega +
                                    (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                        ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ))))
                                          k)⁻¹ * Gexp k omega)
                                      k omega)
                                k omega)
                          k omega)
                    hRrawAE))
                (_ :
                (fun (omega : Cutoff.CutoffSample d) =>
                    ∑' (k : ℕ),
                      (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                          gridWeight rho k *
                            (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                ctop *
                                    (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                        ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ))))
                                          k)⁻¹ * Gexp k omega)
                                      (0 : ℕ) omega +
                                  (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                      ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ))))
                                        k)⁻¹ * Gexp k omega)
                                    k omega)
                              k omega)
                        k omega) =ᵐ[mu]
                  AEMeasurable.mk
                    (fun (omega : Cutoff.CutoffSample d) =>
                      ∑' (k : ℕ),
                        (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                            gridWeight rho k *
                              (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                  ctop *
                                      (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                          ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 :
                                            ℝ)))) k)⁻¹ * Gexp k omega)
                                        (0 : ℕ) omega +
                                    (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                        ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ))))
                                          k)⁻¹ * Gexp k omega)
                                      k omega)
                                k omega)
                          k omega)
                    hRrawAE)
                (_ :
                IsBigOWith mu (gammaSigma sigmaExp)
                  (AEMeasurable.mk
                    (fun (omega : Cutoff.CutoffSample d) =>
                      ∑' (k : ℕ),
                        (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                            gridWeight rho k *
                              (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                  ctop *
                                      (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                          ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 :
                                            ℝ)))) k)⁻¹ * Gexp k omega)
                                        (0 : ℕ) omega +
                                    (fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
                                        ((fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ))))
                                          k)⁻¹ * Gexp k omega)
                                      k omega)
                                k omega)
                          k omega)
                    hRrawAE)
                  Bexp),
                True

private abbrev upperFiniteExponent_pointwiseAggregation_statement : Prop :=
    ∀ {d : ℕ} [NeZero d] (M : ABKModel d) (m : ℤ)
      {s scaling Cblock Krare eps sigmaExp : ℝ} (hs : (0 : ℝ) < s),
      s ≤ (1 : ℝ) →
        (0 : ℝ) ≤ scaling →
          (0 : ℝ) < Cblock →
            (0 : ℝ) < (2 : ℝ) * s - M.gamma →
              ∀
                (hper :
                  ∀ (k : ℕ),
                    ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
                      ∃ (Uone : Cutoff.CutoffSample d → ℝ) (Uexp : Cutoff.CutoffSample d → ℝ),
                        (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uone omega) ∧
                          Measurable Uone ∧
                            (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uexp omega) ∧
                              Measurable Uexp ∧
                                (∀ (omega : Cutoff.CutoffSample d),
                                    cutoffBBlockFamily M m scaling R omega ≤ Cblock + Uone omega +
                                      Uexp omega) ∧
                                  IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
                                    (Cutoff.CutoffSample d))
                                      (gammaSigma (1 : ℝ)) Uone
                                      (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M)
                                        M.gamma k) ∧
                                    IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
                                      (Cutoff.CutoffSample d))
                                      (gammaSigma sigmaExp) Uexp
                                      (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * eps
                                        ^ (15 : ℕ))),
                let mu : Measure (Cutoff.CutoffSample d) := (↑(Cutoff.cutoffSampleLaw M) : Measure
                  (Cutoff.CutoffSample d));
                let gamma : ℝ := M.gamma;
                let rho : ℝ := (2 : ℝ) * s - gamma;
                let ctop : ℝ := (3 : ℝ) ^ ((2 : ℝ) * s);
                let A : ℝ := upperOrdinaryJointProfileBound d Cblock (Disorder.cstar M) gamma;
                let Bone : ℝ := (384 : ℝ) * A * s * rho⁻¹ ^ (3 : ℕ);
                (0 : ℝ) < gamma →
                  (0 : ℝ) ≤ A →
                    let UoneCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R
                      : TriadicCube d) =>
                      if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
                        Classical.choose (hper k R hR)
                      else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
                    let UexpCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R
                      : TriadicCube d) =>
                      if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
                        Classical.choose (Classical.choose_spec (hper k R hR))
                      else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
                    let Gone : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k
                      (UoneCube k);
                    let Gexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k
                      (UexpCube k);
                    let aone : ℕ → ℝ := fun (k : ℕ) => upperSaturatedPerCubeAmplitude Cblock
                      (Disorder.cstar M) gamma k;
                    let V : Cutoff.CutoffSample d → ℝ := jointGridDepthEnvelope d m UoneCube aone;
                    ((∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ jointGridDepthEnvelope d m
                      UoneCube aone omega) ∧
                        Measurable (jointGridDepthEnvelope d m UoneCube aone) ∧
                          IsBigOWith mu (gammaSigma (1 : ℝ)) (jointGridDepthEnvelope d m UoneCube
                            aone) (1 : ℝ) ∧
                            ∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu,
                              ∀ (k : ℕ),
                                ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
                                  UoneCube k R omega ≤
                                    triadicJointDepthEntropyConst d * ((↑k : ℝ) + (1 : ℝ)) * aone
                                      k *
                                      jointGridDepthEnvelope d m UoneCube aone omega) →
                      let collar : ℕ → ℝ := fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ)));
                      let Wexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega :
                        Cutoff.CutoffSample d) =>
                        (collar k)⁻¹ * Gexp k omega;
                      let Fexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega :
                        Cutoff.CutoffSample d) =>
                        ctop * Wexp (0 : ℕ) omega + Wexp k omega;
                      let Xexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega :
                        Cutoff.CutoffSample d) =>
                        gridWeight rho k * Fexp k omega;
                      let Rraw : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
                        ∑' (k : ℕ), Xexp k omega;
                      ∀ (hRrawAE : AEMeasurable Rraw mu),
                        let Yexp : Cutoff.CutoffSample d → ℝ := AEMeasurable.mk Rraw hRrawAE;
                        let Odepth : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) => Gone n.pred;
                        let Edepth : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) => Gexp n.pred;
                        let Z : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) (omega :
                          Cutoff.CutoffSample d) =>
                          scaling *
                            Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale (originCube d m)
                              (m - (↑n : ℤ))
                              (Cutoff.coefficientCutoff M.nu m omega);
                        (∀ (n : ℕ) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Odepth n omega) →
                          (∀ (n : ℕ) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Edepth n omega) →
                            (∀ (n : ℕ) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Z n omega) →
                              (∀ (n : ℕ) (omega : Cutoff.CutoffSample d),
                                  Z n omega ≤ Cblock + Odepth n omega + Edepth n omega) →
                                let Yone : Cutoff.CutoffSample d → ℝ := fun (omega :
                                  Cutoff.CutoffSample d) =>
                                  Bone * V omega;
                                (∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu,
                                    (∀ (n : ℕ), Odepth n omega ≤ upperPolyProfile A gamma n * V
                                      omega) ∧
                                      (Summable fun (n : ℕ) => endpointWeight ((2 : ℝ) * s) n *
                                        Edepth n omega) ∧
                                        ∑' (n : ℕ), endpointWeight ((2 : ℝ) * s) n * Edepth n
                                          omega ≤ Yexp omega) →
                                  ∀ (r : { r : ℝ // (1 : ℝ) ≤ r }),
                                    (2 : ℝ) ≤ (↑r : ℝ) →
                                      (0 : ℝ) < (↑r : ℝ) →
                                        (1 : ℝ) ≤ (↑r : ℝ) / (2 : ℝ) →
                                          (0 : ℝ) < s * (↑r : ℝ) →
                                            let w : ℕ → ℝ := fun (n : ℕ) =>
                                              Book.Ch02.geometricWeight s (↑r : ℝ) n;
                                            (∀ (n : ℕ), (0 : ℝ) ≤ w n) →
                                              Summable w →
                                                ∑' (n : ℕ), w n = (1 : ℝ) →
                                                  ∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu,
                                                    Observable.cutoffUpperEllipticity M m m s hs
                                                          (CoarseEllipticityExponent.finite r)
                                                            omega *
                                                        scaling ≤
                                                      Cblock + Yone omega + Yexp omega

private theorem two_term_one_sided_orlicz_of_pointwise_split {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {sigma1 sigma2 : ℝ}
    {X Udet Uone Uexp : Ω → ℝ} {b Aone Aexp : ℝ}
    (hsigma1 : 0 < sigma1) (hsigma2 : 0 < sigma2)
    (hAone : 0 < Aone) (hAexp : 0 < Aexp)
    (hXmeas : Measurable X) (hUoneMeas : Measurable Uone)
    (hUexpMeas : Measurable Uexp)
    (hdom : ∀ omega, X omega ≤ Udet omega + Uone omega + Uexp omega)
    (hdet : ∀ omega, Udet omega ≤ b)
    (hUone : IsBigOWith μ (gammaSigma sigma1) Uone Aone)
    (hUexp : IsBigOWith μ (gammaSigma sigma2) Uexp Aexp) :
    Probability.IsDeterministicShiftTwoTermOneSidedOrlicz μ
      (gammaSigma sigma1) (gammaSigma sigma2) X b Aone Aexp := by
  rw [Probability.deterministicShiftTwoTermOneSidedOrlicz_iff_exists]
  refine ⟨Uone, Uexp, Probability.isAdmissibleTail_gammaSigma hsigma1,
    Probability.isAdmissibleTail_gammaSigma hsigma2, hAone, hAexp, hXmeas,
    hUoneMeas, hUexpMeas, ?_, hUone, hUexp⟩
  intro omega
  have hdomOmega := hdom omega
  have hdetOmega := hdet omega
  linarith

private theorem upperPolyProfile_pred_le
    {A gamma : ℝ} (hA : 0 ≤ A) (hgamma : 0 ≤ gamma) (n : ℕ) :
    upperPolyProfile A gamma n.pred ≤ upperPolyProfile A gamma n := by
  rw [upperPolyProfile, upperPolyProfile]
  have hpred : ((n.pred : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    have hn : (n.pred : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.pred_le n
    linarith
  have hsq : ((n.pred : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    have hp0 : (0 : ℝ) ≤ (n.pred : ℝ) := Nat.cast_nonneg n.pred
    exact pow_le_pow_left₀ (by linarith only [hp0]) hpred 2
  have hexp : gamma * (n.pred : ℝ) ≤ gamma * (n : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.pred_le n) hgamma
  have hpow : (3 : ℝ) ^ (gamma * (n.pred : ℝ)) ≤
      (3 : ℝ) ^ (gamma * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hhead : 0 ≤ A * (((n.pred : ℝ) + 1) ^ 2) :=
    mul_nonneg hA (sq_nonneg _)
  calc
    A * (((n.pred : ℝ) + 1) ^ 2) * (3 : ℝ) ^ (gamma * (n.pred : ℝ))
        ≤ A * (((n : ℝ) + 1) ^ 2) *
            (3 : ℝ) ^ (gamma * (n.pred : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq hA)
            (Real.rpow_nonneg (by norm_num) _)
    _ ≤ A * (((n : ℝ) + 1) ^ 2) * (3 : ℝ) ^ (gamma * (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hpow
            (mul_nonneg hA (sq_nonneg _))

private theorem endpointWeight_mul_upperPolyProfile_le
    {A gamma s : ℝ} (hA : 0 ≤ A) (hgamma : 0 ≤ gamma)
    (_hs : 0 < s) (hs1 : s ≤ 1) (hgap : 0 < 2 * s - gamma) (n : ℕ) :
    endpointWeight (2 * s) n * upperPolyProfile A gamma n ≤
      192 * A * s * (2 * s - gamma)⁻¹ ^ 3 := by
  let rho : ℝ := 2 * s - gamma
  have hrho : 0 < rho := by simpa [rho] using hgap
  have hrho2 : rho ≤ 2 := by dsimp [rho]; linarith
  have hpoly := natCast_succ_sq_le_inv_sq_mul_three_rpow hrho hrho2 n
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hhalf : (3 : ℝ) ^ (-(rho / 2) * (n : ℝ)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hprod : (0 : ℝ) ≤ rho / 2 * (n : ℝ) :=
      mul_nonneg (by linarith only [hrho.le]) hn0
    linarith only [hprod]
  have hrewrite : endpointWeight (2 * s) n * upperPolyProfile A gamma n =
      A * (((n : ℝ) + 1) ^ 2) * (3 : ℝ) ^ (-(rho) * (n : ℝ)) := by
    rw [endpointWeight_eq_rpow, upperPolyProfile]
    calc
      (3 : ℝ) ^ (-(2 * s) * (n : ℝ)) *
          (A * ((n : ℝ) + 1) ^ 2 * (3 : ℝ) ^ (gamma * (n : ℝ))) =
          A * ((n : ℝ) + 1) ^ 2 *
            ((3 : ℝ) ^ (-(2 * s) * (n : ℝ)) *
              (3 : ℝ) ^ (gamma * (n : ℝ))) := by ring
      _ = A * ((n : ℝ) + 1) ^ 2 * (3 : ℝ) ^ (-rho * (n : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 2
        dsimp [rho]
        ring
  have hbase :
      A * (((n : ℝ) + 1) ^ 2) * (3 : ℝ) ^ (-rho * (n : ℝ)) ≤
        96 * A * rho⁻¹ ^ 2 := by
    calc
      A * (((n : ℝ) + 1) ^ 2) * (3 : ℝ) ^ (-rho * (n : ℝ))
          ≤ A * (96 * rho⁻¹ ^ 2 *
              (3 : ℝ) ^ ((rho / 2) * (n : ℝ))) *
              (3 : ℝ) ^ (-rho * (n : ℝ)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpoly hA)
              (Real.rpow_nonneg (by norm_num) _)
      _ = 96 * A * rho⁻¹ ^ 2 *
            (3 : ℝ) ^ (-(rho / 2) * (n : ℝ)) := by
          have hpowe :
              (3 : ℝ) ^ ((rho / 2) * (n : ℝ)) *
                  (3 : ℝ) ^ (-rho * (n : ℝ)) =
                (3 : ℝ) ^ (-(rho / 2) * (n : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
            congr 1
            ring
          rw [show A * (96 * rho⁻¹ ^ 2 *
                (3 : ℝ) ^ ((rho / 2) * (n : ℝ))) *
                (3 : ℝ) ^ (-rho * (n : ℝ)) =
              96 * A * rho⁻¹ ^ 2 *
                ((3 : ℝ) ^ ((rho / 2) * (n : ℝ)) *
                  (3 : ℝ) ^ (-rho * (n : ℝ))) by ring,
            hpowe]
      _ ≤ 96 * A * rho⁻¹ ^ 2 := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hhalf
              (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 96) hA)
                (sq_nonneg (rho⁻¹))))
  have hrho_le : rho ≤ 2 * s := by dsimp [rho]; linarith
  have hinv : 0 ≤ rho⁻¹ := (inv_pos.2 hrho).le
  have hconvert : rho⁻¹ ^ 2 = rho * rho⁻¹ ^ 3 := by
    field_simp [ne_of_gt hrho]
  rw [hrewrite]
  calc
    A * (((n : ℝ) + 1) ^ 2) * (3 : ℝ) ^ (-rho * (n : ℝ))
        ≤ 96 * A * rho⁻¹ ^ 2 := hbase
    _ = 96 * A * (rho * rho⁻¹ ^ 3) := by rw [hconvert]
    _ ≤ 96 * A * (2 * s * rho⁻¹ ^ 3) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hrho_le (pow_nonneg hinv 3))
        (mul_nonneg (by norm_num) hA)
    _ = 192 * A * s * (2 * s - gamma)⁻¹ ^ 3 := by
      dsimp [rho]
      ring

private theorem weightedLp_three_le
    {w f g h : ℕ → ℝ} {t : ℝ} (ht : 1 ≤ t)
    (hw : ∀ n, 0 ≤ w n) (hf : ∀ n, 0 ≤ f n)
    (hg : ∀ n, 0 ≤ g n) (hh : ∀ n, 0 ≤ h n)
    (hfs : Summable fun n => w n * f n ^ t)
    (hgs : Summable fun n => w n * g n ^ t)
    (hhs : Summable fun n => w n * h n ^ t) :
    (Summable fun n => w n * (f n + g n + h n) ^ t) ∧
      ( ∑' n, w n * (f n + g n + h n) ^ t) ^ (1 / t) ≤
        (∑' n, w n * f n ^ t) ^ (1 / t) +
          (∑' n, w n * g n ^ t) ^ (1 / t) +
            (∑' n, w n * h n ^ t) ^ (1 / t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let c : ℕ → ℝ := fun n => w n ^ (1 / t)
  let F : ℕ → ℝ := fun n => c n * f n
  let G : ℕ → ℝ := fun n => c n * g n
  let H : ℕ → ℝ := fun n => c n * h n
  have hc : ∀ n, 0 ≤ c n := fun n => Real.rpow_nonneg (hw n) _
  have hcancel : (1 / t) * t = 1 := by field_simp
  have hFpow : ∀ n, F n ^ t = w n * f n ^ t := by
    intro n
    dsimp [F, c]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw n) _) (hf n),
      ← Real.rpow_mul (hw n), hcancel, Real.rpow_one]
  have hGpow : ∀ n, G n ^ t = w n * g n ^ t := by
    intro n
    dsimp [G, c]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw n) _) (hg n),
      ← Real.rpow_mul (hw n), hcancel, Real.rpow_one]
  have hHpow : ∀ n, H n ^ t = w n * h n ^ t := by
    intro n
    dsimp [H, c]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw n) _) (hh n),
      ← Real.rpow_mul (hw n), hcancel, Real.rpow_one]
  have hFsum : Summable fun n => F n ^ t := hfs.congr fun n => (hFpow n).symm
  have hGsum : Summable fun n => G n ^ t := hgs.congr fun n => (hGpow n).symm
  have hHsum : Summable fun n => H n ^ t := hhs.congr fun n => (hHpow n).symm
  have hF0 : ∀ n, 0 ≤ F n := fun n => mul_nonneg (hc n) (hf n)
  have hG0 : ∀ n, 0 ≤ G n := fun n => mul_nonneg (hc n) (hg n)
  have hH0 : ∀ n, 0 ≤ H n := fun n => mul_nonneg (hc n) (hh n)
  have hFG := Real.Lp_add_le_tsum_of_nonneg ht hF0 hG0 hFsum hGsum
  have hFGH := Real.Lp_add_le_tsum_of_nonneg ht
    (fun n => add_nonneg (hF0 n) (hG0 n)) hH0 hFG.1 hHsum
  have htotalPow : ∀ n,
      (F n + G n + H n) ^ t = w n * (f n + g n + h n) ^ t := by
    intro n
    have hlin : F n + G n + H n = c n * (f n + g n + h n) := by
      dsimp [F, G, H]
      ring
    rw [hlin]
    dsimp [c]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw n) _)
        (add_nonneg (add_nonneg (hf n) (hg n)) (hh n)),
      ← Real.rpow_mul (hw n), hcancel, Real.rpow_one]
  refine ⟨hFGH.1.congr fun n => htotalPow n, ?_⟩
  rw [← tsum_congr htotalPow, ← tsum_congr hFpow, ← tsum_congr hGpow,
    ← tsum_congr hHpow]
  exact hFGH.2.trans (add_le_add hFG.2 le_rfl)

private theorem summable_rpow_of_nonneg
    {x : ℕ → ℝ} {t : ℝ} (hx0 : ∀ n, 0 ≤ x n) (ht : 1 ≤ t)
    (hx : Summable x) : Summable fun n => x n ^ t := by
  apply hx.of_norm_bounded_eventually_nat
  filter_upwards [hx.tendsto_atTop_zero.eventually_le_const zero_lt_one] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hx0 n) t)]
  exact Real.rpow_le_self_of_le_one (hx0 n) hn ht

private theorem summable_weight_mul_rpow_of_summable_root_mul
    {w f : ℕ → ℝ} {t : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hf : ∀ n, 0 ≤ f n) (ht : 1 ≤ t)
    (hsum : Summable fun n => w n ^ (1 / t) * f n) :
    Summable fun n => w n * f n ^ t := by
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht)
  have hbase0 : ∀ n, 0 ≤ w n ^ (1 / t) * f n := fun n =>
    mul_nonneg (Real.rpow_nonneg (hw n) _) (hf n)
  refine (summable_rpow_of_nonneg hbase0 ht hsum).congr fun n => ?_
  rw [Real.mul_rpow (Real.rpow_nonneg (hw n) _) (hf n)]
  rw [show (1 / t : ℝ) = t⁻¹ by simp only [one_div],
    Real.rpow_inv_rpow (hw n) ht0]

private theorem upperFiniteExponent_pointwiseAggregation :
  upperFiniteExponent_pointwiseAggregation_statement := by
  intro _ _ M m s _ Cblock _ _ _ hs hs1 hscaling hCblock hgap _ _ gamma _ _ A Bone hgamma hA _ _ _
    _ _ V hVspec _ _ _ _ _ _ Yexp Odepth Edepth Z hOnonneg hEnonneg hZnonneg hdepth Yone hGood r
      hr hr0 ht hsr w hw hwsum hwtsum
  filter_upwards [hGood] with omega hgood
  have hDsum : Summable fun n => w n * Cblock ^ ((r : ℝ) / 2) := by
    simpa only [mul_comm] using hwsum.mul_right (Cblock ^ ((r : ℝ) / 2))
  have hOprofileSum : Summable fun n =>
      w n * upperPolyProfile A gamma n ^ ((r : ℝ) / 2) := by
    simpa only [w] using
      summable_geometricWeight_mul_upperPolyProfile_rpow_of_two_le
        hA hgamma.le hs hs1 hr hgap
  have hOscaledSum : Summable fun n =>
      w n * (upperPolyProfile A gamma n * V omega) ^ ((r : ℝ) / 2) := by
    have hV0 := hVspec.1 omega
    refine (hOprofileSum.mul_right (V omega ^ ((r : ℝ) / 2))).congr fun n => ?_
    rw [Real.mul_rpow (upperPolyProfile_nonneg hA gamma n) hV0]
    ring
  have hOsum : Summable fun n => w n * Odepth n omega ^ ((r : ℝ) / 2) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hOnonneg n omega) _))
      (fun n => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hOnonneg n omega) (hgood.1 n) (by positivity))
        (hw n)) hOscaledSum
  have hrootExp : 1 / ((r : ℝ) / 2) = 2 / (r : ℝ) := by
    field_simp
  have hRareLin : Summable fun n =>
      w n ^ (2 / (r : ℝ)) * Edepth n omega := by
    have heq : ∀ n,
        w n ^ (2 / (r : ℝ)) * Edepth n omega =
          gridSumConst s (r : ℝ) *
            (endpointWeight (2 * s) n * Edepth n omega) := by
      intro n
      rw [show w n ^ (2 / (r : ℝ)) =
          gridSumConst s (r : ℝ) * endpointWeight (2 * s) n by
        simpa only [w] using
          geometricWeight_rpow_two_div_eq_endpointWeight hsr.le hr0.ne' n]
      ring
    exact ((hgood.2.1).mul_left (gridSumConst s (r : ℝ))).congr
      fun n => (heq n).symm
  have hRareLinLe :
      (∑' n, w n ^ (2 / (r : ℝ)) * Edepth n omega) ≤ Yexp omega := by
    have heq : (∑' n, w n ^ (2 / (r : ℝ)) * Edepth n omega) =
        gridSumConst s (r : ℝ) *
          ∑' n, endpointWeight (2 * s) n * Edepth n omega := by
      rw [← tsum_mul_left]
      exact tsum_congr fun n => by
        rw [show w n ^ (2 / (r : ℝ)) =
            gridSumConst s (r : ℝ) * endpointWeight (2 * s) n by
          simpa only [w] using
            geometricWeight_rpow_two_div_eq_endpointWeight hsr.le hr0.ne' n]
        ring
    have hmass := gridSumConst_le_one hs hr0
    have hmass0 := gridSumConst_nonneg hsr.le
    have hsum0 : 0 ≤ ∑' n, endpointWeight (2 * s) n * Edepth n omega :=
      tsum_nonneg fun n => mul_nonneg (endpointWeight_nonneg _ n)
        (hEnonneg n omega)
    rw [heq]
    exact (mul_le_of_le_one_left hsum0 hmass).trans hgood.2.2
  have hEsum : Summable fun n => w n * Edepth n omega ^ ((r : ℝ) / 2) := by
    apply summable_weight_mul_rpow_of_summable_root_mul hw
      (fun n => hEnonneg n omega) ht
    simpa only [hrootExp] using hRareLin
  have hMink := weightedLp_three_le ht hw (fun _ => hCblock.le)
    (fun n => hOnonneg n omega) (fun n => hEnonneg n omega)
    hDsum hOsum hEsum
  have htotalSum := hMink.1
  have hZsum : Summable fun n => w n * Z n omega ^ ((r : ℝ) / 2) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hZnonneg n omega) _))
      (fun n => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hZnonneg n omega) (hdepth n omega) (by positivity))
        (hw n)) htotalSum
  have hsumLe : (∑' n, w n * Z n omega ^ ((r : ℝ) / 2)) ≤
      ∑' n, w n * (Cblock + Odepth n omega + Edepth n omega) ^
        ((r : ℝ) / 2) :=
    hZsum.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hZnonneg n omega) (hdepth n omega) (by positivity))
        (hw n)) htotalSum
  have hDnorm :
      (∑' n, w n * Cblock ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) =
        Cblock := by
    have hcancel : (r : ℝ) / 2 * (2 / (r : ℝ)) = 1 := by field_simp
    rw [tsum_mul_right, hwtsum, one_mul, ← Real.rpow_mul hCblock.le,
      hcancel, Real.rpow_one]
  have hOnorm :
      (∑' n, w n * Odepth n omega ^ ((r : ℝ) / 2)) ^
          (2 / (r : ℝ)) ≤ Yone omega := by
    simpa only [w, Yone, Bone] using
      (upperPolyProfile_aggregate_le_commonEnvelope
        (Omega := Unit) (U := fun n _ => Odepth n omega)
        (V := fun _ => V omega)
        hA hgamma.le hs hs1 hr hgap
        (fun n _ => hOnonneg n omega) (fun _ => hVspec.1 omega)
        (fun n _ => hgood.1 n) ())
  have hEnorm :
      (∑' n, w n * Edepth n omega ^ ((r : ℝ) / 2)) ^
          (2 / (r : ℝ)) ≤ Yexp omega :=
    (tsum_weighted_rpow_root_le hr hw (fun n => hEnonneg n omega)
      hEsum hRareLin).trans hRareLinLe
  rw [cutoffUpperEllipticity_mul_eq_rpow M m m hs rfl hr0 hscaling omega]
  change (∑' n, w n * Z n omega ^ ((r : ℝ) / 2)) ^
      (2 / (r : ℝ)) ≤ Cblock + Yone omega + Yexp omega
  calc
    (∑' n, w n * Z n omega ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) ≤
        (∑' n, w n * (Cblock + Odepth n omega + Edepth n omega) ^
          ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) :=
      Real.rpow_le_rpow
        (tsum_nonneg fun n => mul_nonneg (hw n)
          (Real.rpow_nonneg (hZnonneg n omega) _)) hsumLe (by positivity)
    _ ≤ (∑' n, w n * Cblock ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) +
          (∑' n, w n * Odepth n omega ^ ((r : ℝ) / 2)) ^
            (2 / (r : ℝ)) +
          (∑' n, w n * Edepth n omega ^ ((r : ℝ) / 2)) ^
          (2 / (r : ℝ)) := by simpa only [hrootExp] using hMink.2
    _ ≤ Cblock + Yone omega + Yexp omega := by
      rw [hDnorm]
      exact add_le_add (add_le_add_right hOnorm Cblock) hEnorm

private theorem upperFiniteQGeTwoInfinityAggregation_momentBounds1 :
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ) {s scaling Cblock Krare eps sigmaExp : ℝ}
    (hper :
    ∀ (k : ℕ),
    ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
    ∃ (Uone : Cutoff.CutoffSample d → ℝ) (Uexp : Cutoff.CutoffSample d → ℝ),
    (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uone omega) ∧
    Measurable Uone ∧
    (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uexp omega) ∧
    Measurable Uexp ∧
    (∀ (omega : Cutoff.CutoffSample d),
    cutoffBBlockFamily M m scaling R omega ≤ Cblock + Uone omega + Uexp omega) ∧
    IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) (gammaSigma (1 :
      ℝ)) Uone
    (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M) M.gamma k) ∧
    IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) (gammaSigma sigmaExp)
    Uexp (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * eps ^ (15 : ℕ))),
    let mu : Measure (Cutoff.CutoffSample d) := (↑(Cutoff.cutoffSampleLaw M) : Measure
      (Cutoff.CutoffSample d));
    let gamma : ℝ := M.gamma;
    let rho : ℝ := (2 : ℝ) * s - gamma;
    let ctop : ℝ := (3 : ℝ) ^ ((2 : ℝ) * s);
    let A : ℝ := upperOrdinaryJointProfileBound d Cblock (Disorder.cstar M) gamma;
    let Bone : ℝ := (384 : ℝ) * A * s * rho⁻¹ ^ (3 : ℕ);
    (0 : ℝ) < rho →
    (0 : ℝ) < ctop →
    (0 : ℝ) ≤ Bone →
    let UoneCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R : TriadicCube
      d) =>
    if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then Classical.choose
      (hper k R hR)
    else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
    let UexpCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R : TriadicCube
      d) =>
    if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
    Classical.choose (Classical.choose_spec (hper k R hR))
    else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
    let Gone : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k (UoneCube k);
    let Gexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k (UexpCube k);
    let aone : ℕ → ℝ := fun (k : ℕ) => upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M)
      gamma k;
    let V : Cutoff.CutoffSample d → ℝ := jointGridDepthEnvelope d m UoneCube aone;
    ((∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ jointGridDepthEnvelope d m UoneCube aone omega) ∧
    Measurable (jointGridDepthEnvelope d m UoneCube aone) ∧
    IsBigOWith mu (gammaSigma (1 : ℝ)) (jointGridDepthEnvelope d m UoneCube aone) (1 : ℝ) ∧
    ∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu,
    ∀ (k : ℕ),
    ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
    UoneCube k R omega ≤
    triadicJointDepthEntropyConst d * ((↑k : ℝ) + (1 : ℝ)) * aone k *
    jointGridDepthEnvelope d m UoneCube aone omega) →
    let collar : ℕ → ℝ := fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ)));
    (∀ (k : ℕ), (0 : ℝ) < collar k) →
    let Wexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
    (collar k)⁻¹ * Gexp k omega;
    (∀ (k : ℕ) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Wexp k omega) →
    (∀ (k : ℕ) (omega : Cutoff.CutoffSample d), collar k * Wexp k omega = Gexp k omega) →
    let Fexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
    ctop * Wexp (0 : ℕ) omega + Wexp k omega;
    let Xexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
    gridWeight rho k * Fexp k omega;
    (∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu, Summable fun (k : ℕ) => Xexp k omega) →
    let Rraw : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
    ∑' (k : ℕ), Xexp k omega;
    ∀ (hRrawAE : AEMeasurable Rraw mu),
    let Yexp : Cutoff.CutoffSample d → ℝ := AEMeasurable.mk Rraw hRrawAE;
    Rraw =ᵐ[mu] Yexp →
    let Odepth : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) => Gone n.pred;
    let Edepth : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) => Gexp n.pred;
    (∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu,
    ∀ (n : ℕ), Odepth n omega ≤ upperPolyProfile A gamma n * V omega) →
    let Yone : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) => Bone * V omega;
    Measurable Yone ∧
    IsBigOWith mu (gammaSigma (1 : ℝ)) Yone Bone ∧
    ∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu,
    (∀ (n : ℕ), Odepth n omega ≤ upperPolyProfile A gamma n * V omega) ∧
    (Summable fun (n : ℕ) => endpointWeight ((2 : ℝ) * s) n * Edepth n omega) ∧
    ∑' (n : ℕ), endpointWeight ((2 : ℝ) * s) n * Edepth n omega ≤ Yexp omega := by
  intro _ _ _ s _ _ _ _ _ _ mu gamma rho ctop A Bone hrho hctop hBone _ _ _ _ _ V hVspec collar
    hcollar Wexp hWexpNonneg hGexpEq Fexp Xexp hXexpSumAE Rraw _ Yexp hRrawEqYexp Odepth Edepth
      hODomAE Yone
  have hYoneMeas : Measurable Yone := hVspec.2.1.const_mul Bone
  have hYoneO : IsBigOWith mu (gammaSigma 1) Yone Bone := by
    simpa only [Yone, mul_one] using
      (hVspec.2.2.1.const_mul hBone)
  have hRareCoreAE : ∀ᵐ omega ∂mu,
      Summable (fun n => endpointWeight (2 * s) n * Edepth n omega) ∧
      (∑' n, endpointWeight (2 * s) n * Edepth n omega) ≤ Rraw omega := by
    filter_upwards [hXexpSumAE] with omega hsum
    have hFsum : Summable fun k => gridWeight rho k * Fexp k omega := by
      simpa only [Xexp] using hsum
    have hWsum : Summable fun k => gridWeight rho k * Wexp k omega := by
      refine Summable.of_nonneg_of_le
        (fun k => mul_nonneg (gridWeight_nonneg rho k) (hWexpNonneg k omega))
        (fun k => mul_le_mul_of_nonneg_left
          (by dsimp [Fexp]; linarith [mul_nonneg hctop.le (hWexpNonneg 0 omega)])
          (gridWeight_nonneg rho k)) hFsum
    have hcover : 1 ≤ (3 : ℝ) ^ rho * ∑' k, gridWeight rho k :=
      one_le_rpow_mul_tsum_gridWeight hrho
    have hfold : ∀ k,
        (3 : ℝ) ^ rho * (collar 0 * Wexp 0 omega) + Wexp k omega ≤
          Fexp k omega := by
      intro k
      have hpow : (3 : ℝ) ^ rho * collar 0 = ctop := by
        dsimp [rho, collar, ctop, gamma]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring
      change (3 : ℝ) ^ rho * (collar 0 * Wexp 0 omega) + Wexp k omega ≤
        ctop * Wexp 0 omega + Wexp k omega
      rw [← mul_assoc, hpow]
    have hcore := top_add_gridSum_le_gridSum hrho (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg (hcollar 0).le (hWexpNonneg 0 omega))
      (fun k => hWexpNonneg k omega) hcover hfold (by
        simpa only [one_mul] using hFsum)
    let H : ℕ → ℝ := fun n => endpointWeight (2 * s) n * Edepth n omega
    have hHzero : H 0 = collar 0 * Wexp 0 omega := by
      dsimp [H, Edepth]
      rw [endpointWeight_zero, one_mul, hGexpEq]
    have hHsucc : ∀ k, H (k + 1) = gridWeight rho k * Wexp k omega := by
      intro k
      dsimp [H, Edepth]
      rw [← hGexpEq k omega]
      have hcollarWeight := rpow_collar_eq_endpointWeight s gamma (k + 1)
      have hleft : (3 : ℝ) ^ (-2 * s * ((k + 1 : ℕ) : ℝ)) * collar k =
          endpointWeight rho (k + 1) := by
        simpa only [collar, rho, Nat.cast_add, Nat.cast_one] using hcollarWeight
      have hfactor : endpointWeight (2 * s) (k + 1) * collar k =
          gridWeight rho k := by
        calc
          endpointWeight (2 * s) (k + 1) * collar k =
              (3 : ℝ) ^ (-2 * s * ((k + 1 : ℕ) : ℝ)) * collar k := by
            rw [endpointWeight_eq_rpow]
            congr 2
            ring
          _ = endpointWeight rho (k + 1) := hleft
          _ = gridWeight rho k := by
            simp only [endpointWeight, gridWeight, pow_succ]
      calc
        endpointWeight (2 * s) (k + 1) * (collar k * Wexp k omega) =
            (endpointWeight (2 * s) (k + 1) * collar k) * Wexp k omega := by ring
        _ = gridWeight rho k * Wexp k omega := by rw [hfactor]
    have hHtail : Summable fun k => H (k + 1) :=
      hWsum.congr fun k => (hHsucc k).symm
    have hHsum : Summable H := (summable_nat_add_iff 1).mp hHtail
    refine ⟨by simpa only [H] using hHsum, ?_⟩
    have hHtsum : (∑' n, H n) =
        collar 0 * Wexp 0 omega + ∑' k, gridWeight rho k * Wexp k omega := by
      rw [hHsum.tsum_eq_zero_add, hHzero]
      congr 1
      exact tsum_congr hHsucc
    change (∑' n, H n) ≤ Rraw omega
    calc
      (∑' n, H n) =
          collar 0 * Wexp 0 omega + ∑' k, gridWeight rho k * Wexp k omega :=
        hHtsum
      _ ≤ ∑' k, gridWeight rho k * Fexp k omega := by
        simpa only [one_mul] using hcore
      _ = Rraw omega := by rfl
  have hGood : ∀ᵐ omega ∂mu,
      (∀ n, Odepth n omega ≤ upperPolyProfile A gamma n * V omega) ∧
      Summable (fun n => endpointWeight (2 * s) n * Edepth n omega) ∧
      (∑' n, endpointWeight (2 * s) n * Edepth n omega) ≤ Yexp omega := by
    filter_upwards [hODomAE, hRareCoreAE, hRrawEqYexp] with omega hO hrare heq
    exact ⟨hO, hrare.1, hrare.2.trans_eq heq⟩
  exact ⟨hYoneMeas, hYoneO, hGood⟩

private theorem upperFiniteQGeTwoInfinityAggregation_momentBounds2 :
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ) {scaling Cblock Krare eps sigmaExp : ℝ},
    (0 : ℝ) ≤ scaling →
    ∀
    (hper :
    ∀ (k : ℕ),
    ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
    ∃ (Uone : Cutoff.CutoffSample d → ℝ) (Uexp : Cutoff.CutoffSample d → ℝ),
    (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uone omega) ∧
    Measurable Uone ∧
    (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uexp omega) ∧
    Measurable Uexp ∧
    (∀ (omega : Cutoff.CutoffSample d),
    cutoffBBlockFamily M m scaling R omega ≤ Cblock + Uone omega + Uexp omega) ∧
    IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) (gammaSigma (1 : ℝ))
    Uone (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M) M.gamma k) ∧
    IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
    (gammaSigma sigmaExp) Uexp
    (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * eps ^ (15 : ℕ))),
    let mu : Measure (Cutoff.CutoffSample d) := (↑(Cutoff.cutoffSampleLaw M) : Measure
      (Cutoff.CutoffSample d));
    let gamma : ℝ := M.gamma;
    let abase : ℝ := Krare⁻¹ * eps ^ (15 : ℕ);
    let UoneCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R : TriadicCube
      d) =>
    if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then Classical.choose
      (hper k R hR)
    else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
    let UexpCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R : TriadicCube
      d) =>
    if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
    Classical.choose (Classical.choose_spec (hper k R hR))
    else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
    (∀ (k : ℕ) (R : TriadicCube d) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ UoneCube k R omega) ∧
    (∀ (k : ℕ) (R : TriadicCube d) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ UexpCube k R omega) ∧
    (∀ (k : ℕ) (R : TriadicCube d), Measurable (UoneCube k R)) ∧
    (∀ (k : ℕ) (R : TriadicCube d), Measurable (UexpCube k R)) ∧
    (∀ (k : ℕ),
    ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
    IsBigOWith mu (gammaSigma (1 : ℝ)) (UoneCube k R)
    (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M) gamma k)) ∧
    (∀ (k : ℕ),
    ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
    IsBigOWith mu (gammaSigma sigmaExp) (UexpCube k R)
    ((3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ))) * abase)) ∧
    ∀ (k : ℕ),
    ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
    ∀ (omega : Cutoff.CutoffSample d),
    |cutoffBBlockFamily M m scaling R omega| ≤ Cblock + UoneCube k R omega + UexpCube k R omega :=
      by
  intro d M m scaling Cblock _ _ sigmaExp hscaling hper mu gamma abase UoneCube UexpCube
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
          (Disorder.cstar M) gamma k) := by
    intro k R hR
    obtain ⟨_, _, _, _, _, hUone, _⟩ :=
      Classical.choose_spec (Classical.choose_spec (hper k R hR))
    simpa only [mu, gamma, UoneCube, dite_eq_left hR] using hUone
  have hUexpCubeO : ∀ (k : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
      IsBigOWith mu (gammaSigma sigmaExp) (UexpCube k R)
        ((3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) * abase) := by
    intro k R hR
    obtain ⟨_, _, _, _, _, _, hUexp⟩ :=
      Classical.choose_spec (Classical.choose_spec (hper k R hR))
    convert hUexp using 1
    · simp only [UexpCube, dite_eq_left hR]
    · dsimp [gamma, abase]
      ring
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
  exact ⟨hUoneCubeNonneg, hUexpCubeNonneg, hUoneCubeMeas, hUexpCubeMeas, hUoneCubeO, hUexpCubeO,
    hblock⟩

private theorem upperGrid_geometricDepthWeight :
    ∀ {d : ℕ} [NeZero d] (M : ABKModel d) (m : ℤ)
      {scaling Cblock Krare eps sigmaExp : ℝ} (_ : (0 : ℝ) ≤ scaling)
      (hper :
        ∀ (k : ℕ),
          ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
            ∃ (Uone : Cutoff.CutoffSample d → ℝ) (Uexp : Cutoff.CutoffSample d → ℝ),
              (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uone omega) ∧
                Measurable Uone ∧
                  (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uexp omega) ∧
                    Measurable Uexp ∧
                      (∀ (omega : Cutoff.CutoffSample d),
                          cutoffBBlockFamily M m scaling R omega ≤ Cblock + Uone omega + Uexp
                            omega) ∧
                        IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
                          (gammaSigma (1 : ℝ)) Uone
                            (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M) M.gamma k) ∧
                          IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
                            d)) (gammaSigma sigmaExp)
                            Uexp (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * eps ^ (15
                              : ℕ))),
      let UoneCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R : TriadicCube
        d) =>
        if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
          Classical.choose (hper k R hR)
        else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
      let UexpCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R : TriadicCube
        d) =>
        if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
          Classical.choose (Classical.choose_spec (hper k R hR))
        else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
      ∀
        (_ :
          ∀ (k : ℕ) (R : TriadicCube d) (omega : Cutoff.CutoffSample d),
            (0 : ℝ) ≤
              (fun (k : ℕ) (R : TriadicCube d) =>
                  if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
                    Classical.choose (hper k R hR)
                  else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                k R omega)
        (_ :
          ∀ (k : ℕ) (R : TriadicCube d) (omega : Cutoff.CutoffSample d),
            (0 : ℝ) ≤
              (fun (k : ℕ) (R : TriadicCube d) =>
                  if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
                    Classical.choose (Classical.choose_spec (hper k R hR))
                  else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                k R omega)
        (_ :
          ∀ (k : ℕ),
            ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
              ∀ (omega : Cutoff.CutoffSample d),
                |cutoffBBlockFamily M m scaling R omega| ≤
                  Cblock +
                      (fun (k : ℕ) (R : TriadicCube d) =>
                          if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))
                            then
                            Classical.choose (hper k R hR)
                          else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                        k R omega +
                    (fun (k : ℕ) (R : TriadicCube d) =>
                        if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))
                          then
                          Classical.choose (Classical.choose_spec (hper k R hR))
                        else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                      k R omega),
        let Gone : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k (UoneCube k);
        let Gexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k (UexpCube k);
        let Odepth : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) => Gone n.pred;
        let Edepth : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) => Gexp n.pred;
        let Z : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) (omega : Cutoff.CutoffSample d) =>
          scaling *
            Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale (originCube d m) (m - (↑n : ℤ))
              (Cutoff.coefficientCutoff M.nu m omega);
        ∀ (n : ℕ) (omega : Cutoff.CutoffSample d), Z n omega ≤ Cblock + Odepth n omega + Edepth n
          omega := by
  intro d _ M m scaling _ _ _ _ hscaling _ _ _ hUoneCubeNonneg hUexpCubeNonneg hblock Gone Gexp
    Odepth Edepth Z n omega
  have hgrid : Z n omega ≤
      blockGridSup d m n.pred (cutoffBBlockFamily M m scaling) omega := by
    cases n with
    | zero =>
        simpa only [Z, Nat.cast_zero, sub_zero, Nat.pred_zero] using
          (scaledB_le_blockGridSup M m 0 hscaling
            (maxDescendantBCoeffField_top_le m
              (Cutoff.coefficientCutoff M.nu m omega))
            (fun _ _ => le_rfl))
    | succ k =>
        have hscale : m - (((k + 1 : ℕ) : ℤ)) = m - 1 - (k : ℤ) := by
          push_cast
          ring
        change scaling *
            Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
              (originCube d m) (m - (((k + 1 : ℕ) : ℤ)))
              (Cutoff.coefficientCutoff M.nu m omega) ≤
          blockGridSup d m k (cutoffBBlockFamily M m scaling) omega
        rw [hscale]
        exact scaledB_le_blockGridSup M m k hscaling le_rfl fun _ _ => le_rfl
  have hsplit := blockGridSup_le_add_add_of_perCube
    (hUoneCubeNonneg n.pred) (hUexpCubeNonneg n.pred)
    (hblock n.pred) omega
  exact hgrid.trans (by simpa only [Odepth, Edepth, Gone, Gexp] using hsplit)

private theorem upperFiniteQGeTwoInfinityAggregation_estimate1 :
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ)
      {scaling Cblock Krare eps sigmaExp : ℝ} (_ : (0 : ℝ) < Cblock) (_ : M.gamma ≤ (1 : ℝ))
      (hper :
        ∀ (k : ℕ),
          ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
            ∃ (Uone : Cutoff.CutoffSample d → ℝ) (Uexp : Cutoff.CutoffSample d → ℝ),
              (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uone omega) ∧
                Measurable Uone ∧
                  (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uexp omega) ∧
                    Measurable Uexp ∧
                      (∀ (omega : Cutoff.CutoffSample d),
                          cutoffBBlockFamily M m scaling R omega ≤ Cblock + Uone omega + Uexp
                            omega) ∧
                        IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
                          (gammaSigma (1 : ℝ)) Uone
                            (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M) M.gamma k) ∧
                          IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
                            d)) (gammaSigma sigmaExp)
                            Uexp (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * eps ^ (15
                              : ℕ))),
      let mu : Measure (Cutoff.CutoffSample d) := (↑(Cutoff.cutoffSampleLaw M) : Measure
        (Cutoff.CutoffSample d));
      let gamma : ℝ := M.gamma;
      let A : ℝ := upperOrdinaryJointProfileBound d Cblock (Disorder.cstar M) gamma;
      ∀ (_ : (0 : ℝ) < Disorder.cstar M),
        let UoneCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R :
          TriadicCube d) =>
          if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
            Classical.choose (hper k R hR)
          else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
        ∀
          (_ :
            ∀ (k : ℕ) (R : TriadicCube d) (omega : Cutoff.CutoffSample d),
              (0 : ℝ) ≤
                (fun (k : ℕ) (R : TriadicCube d) =>
                    if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
                      Classical.choose (hper k R hR)
                    else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                  k R omega),
          let Gone : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k (UoneCube
            k);
          let aone : ℕ → ℝ := fun (k : ℕ) => upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar
            M) gamma k;
          let V : Cutoff.CutoffSample d → ℝ := jointGridDepthEnvelope d m UoneCube aone;
          ∀
            (_ :
              (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ jointGridDepthEnvelope d m UoneCube
                aone omega) ∧
                Measurable (jointGridDepthEnvelope d m UoneCube aone) ∧
                  IsBigOWith mu (gammaSigma (1 : ℝ)) (jointGridDepthEnvelope d m UoneCube aone) (1
                    : ℝ) ∧
                    ∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu,
                      ∀ (k : ℕ),
                        ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
                          UoneCube k R omega ≤
                            triadicJointDepthEntropyConst d * ((↑k : ℝ) + (1 : ℝ)) * aone k *
                              jointGridDepthEnvelope d m UoneCube aone omega),
            ∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu, ∀ (k : ℕ), Gone k omega ≤ upperPolyProfile A
              gamma k * V omega := by
  intro d M _ _ _ _ _ _ hCblock hgamma1 _ _ gamma A hcstar _ hUoneCubeNonneg Gone aone V hVspec
  filter_upwards [hVspec.2.2.2] with omega homega
  intro k
  have hgrid : Gone k omega ≤
      (triadicJointDepthEntropyConst d * ((k : ℝ) + 1) * aone k) *
        V omega := by
    apply blockGridSup_le
    intro R hR
    rw [abs_of_nonneg (hUoneCubeNonneg k R omega)]
    simpa only [Gone, V] using homega k R hR
  have hprofile :
      triadicJointDepthEntropyConst d * ((k : ℝ) + 1) * aone k ≤
        upperPolyProfile A gamma k := by
    dsimp [aone, A, gamma]
    exact
      triadicJointDepthEntropyConst_mul_upperSaturatedPerCubeAmplitude_le_bound
        d hCblock.le (inv_nonneg.mpr hcstar.le)
          M.shellPrefix.gamma_pos.le hgamma1 k
  exact hgrid.trans
    (mul_le_mul_of_nonneg_right hprofile (hVspec.1 omega))

private theorem upperFiniteQGeTwoInfinityAggregation_estimate2 :
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ)
      {s scaling Cblock Krare eps sigmaExp : ℝ} (_ : (0 : ℝ) < s) (_ : s ≤ (1 : ℝ))
      (_ : (0 : ℝ) < (2 : ℝ) * s - M.gamma)
      (hper :
        ∀ (k : ℕ),
          ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
            ∃ (Uone : Cutoff.CutoffSample d → ℝ) (Uexp : Cutoff.CutoffSample d → ℝ),
              (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uone omega) ∧
                Measurable Uone ∧
                  (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uexp omega) ∧
                    Measurable Uexp ∧
                      (∀ (omega : Cutoff.CutoffSample d),
                          cutoffBBlockFamily M m scaling R omega ≤ Cblock + Uone omega + Uexp
                            omega) ∧
                        IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
                          (gammaSigma (1 : ℝ)) Uone
                            (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M) M.gamma k) ∧
                          IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
                            d)) (gammaSigma sigmaExp)
                            Uexp (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * eps ^ (15
                              : ℕ))),
      let mu : Measure (Cutoff.CutoffSample d) := (↑(Cutoff.cutoffSampleLaw M) : Measure
        (Cutoff.CutoffSample d));
      let gamma : ℝ := M.gamma;
      let rho : ℝ := (2 : ℝ) * s - gamma;
      let ctop : ℝ := (3 : ℝ) ^ ((2 : ℝ) * s);
      let A : ℝ := upperOrdinaryJointProfileBound d Cblock (Disorder.cstar M) gamma;
      let Bone : ℝ := (384 : ℝ) * A * s * rho⁻¹ ^ (3 : ℕ);
      ∀ (_ : (0 : ℝ) < gamma) (_ : (0 : ℝ) ≤ A),
        let UoneCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R :
          TriadicCube d) =>
          if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
            Classical.choose (hper k R hR)
          else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
        let UexpCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R :
          TriadicCube d) =>
          if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
            Classical.choose (Classical.choose_spec (hper k R hR))
          else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
        let Gone : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k (UoneCube k);
        let Gexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k (UexpCube k);
        let aone : ℕ → ℝ := fun (k : ℕ) => upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar
          M) gamma k;
        let V : Cutoff.CutoffSample d → ℝ := jointGridDepthEnvelope d m UoneCube aone;
        ∀
          (_ :
            (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ jointGridDepthEnvelope d m UoneCube aone
              omega) ∧
              Measurable (jointGridDepthEnvelope d m UoneCube aone) ∧
                IsBigOWith mu (gammaSigma (1 : ℝ)) (jointGridDepthEnvelope d m UoneCube aone) (1 :
                  ℝ) ∧
                  ∀ᵐ (omega : Cutoff.CutoffSample d) ∂mu,
                    ∀ (k : ℕ),
                      ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
                        UoneCube k R omega ≤
                          triadicJointDepthEntropyConst d * ((↑k : ℝ) + (1 : ℝ)) * aone k *
                            jointGridDepthEnvelope d m UoneCube aone omega),
          let collar : ℕ → ℝ := fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ)));
          let Wexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
            (collar k)⁻¹ * Gexp k omega;
          let Fexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
            ctop * Wexp (0 : ℕ) omega + Wexp k omega;
          let Xexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
            gridWeight rho k * Fexp k omega;
          let Rraw : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) => ∑' (k :
            ℕ), Xexp k omega;
          ∀ (hRrawAE : AEMeasurable Rraw mu),
            let Odepth : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) => Gone n.pred;
            let Yone : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) => Bone *
              V omega;
            ∀ (omega : Cutoff.CutoffSample d)
              (_ :
                (∀ (n : ℕ),
                    blockGridSup d m n.pred
                        (fun (R : TriadicCube d) =>
                          if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑n.pred
                            : ℤ)) then
                            Classical.choose (hper n.pred R hR)
                          else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                        omega ≤
                      upperPolyProfile (upperOrdinaryJointProfileBound d Cblock (Disorder.cstar M)
                        M.gamma) M.gamma n *
                        jointGridDepthEnvelope d m
                          (fun (k : ℕ) (R : TriadicCube d) =>
                            if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k :
                              ℤ)) then
                              Classical.choose (hper k R hR)
                            else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                          (fun (k : ℕ) => upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M)
                            M.gamma k) omega) ∧
                  (Summable fun (n : ℕ) =>
                      endpointWeight ((2 : ℝ) * s) n *
                        blockGridSup d m n.pred
                          (fun (R : TriadicCube d) =>
                            if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) -
                              (↑n.pred : ℤ)) then
                              Classical.choose (Classical.choose_spec (hper n.pred R hR))
                            else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                          omega) ∧
                    ∑' (n : ℕ),
                        endpointWeight ((2 : ℝ) * s) n *
                          blockGridSup d m n.pred
                            (fun (R : TriadicCube d) =>
                              if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) -
                                (↑n.pred : ℤ)) then
                                Classical.choose (Classical.choose_spec (hper n.pred R hR))
                              else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                            omega ≤
                      AEMeasurable.mk
                        (fun (omega : Cutoff.CutoffSample d) =>
                          ∑' (k : ℕ),
                            gridWeight ((2 : ℝ) * s - M.gamma) k *
                              ((3 : ℝ) ^ ((2 : ℝ) * s) *
                                  (((3 : ℝ) ^ (M.gamma * ((↑(0 : ℕ) : ℝ) + (1 : ℝ))))⁻¹ *
                                    blockGridSup d m (0 : ℕ)
                                      (fun (R : TriadicCube d) =>
                                        if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 :
                                          ℤ) - (↑(0 : ℕ) : ℤ)) then
                                          Classical.choose (Classical.choose_spec (hper (0 : ℕ) R
                                            hR))
                                        else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                                      omega) +
                                ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))))⁻¹ *
                                  blockGridSup d m k
                                    (fun (R : TriadicCube d) =>
                                      if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ)
                                        - (↑k : ℤ)) then
                                        Classical.choose (Classical.choose_spec (hper k R hR))
                                      else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ))
                                    omega))
                        hRrawAE omega)
              (n : ℕ) (_ : (0 : ℝ) ≤ endpointWeight ((2 : ℝ) * s) n),
              endpointWeight ((2 : ℝ) * s) n * Odepth n omega ≤ Yone omega := by
  intro _ _ _ s _ _ _ _ _ hs hs1 hgap _ _ gamma rho _ A Bone hgamma hA _ _ _ _ _ V hVspec _ _ _ _
    _ _ _ Yone omega hgood n hweight0
  have hfirst := mul_le_mul_of_nonneg_left (hgood.1 n) hweight0
  have hprofile := endpointWeight_mul_upperPolyProfile_le hA hgamma.le
    hs hs1 hgap n
  have hV0 := hVspec.1 omega
  have hBsmall :
      endpointWeight (2 * s) n * upperPolyProfile A gamma n * V omega ≤
        (192 * A * s * rho⁻¹ ^ 3) * V omega := by
    exact mul_le_mul_of_nonneg_right (by simpa only [rho] using hprofile) hV0
  have hcoef : 192 * A * s * rho⁻¹ ^ 3 ≤ Bone := by
    have hbase0 : 0 ≤ A * s * rho⁻¹ ^ 3 := by positivity
    dsimp [Bone]
    linarith only [hbase0]
  exact hfirst.trans <| calc
    endpointWeight (2 * s) n * (upperPolyProfile A gamma n * V omega) =
        endpointWeight (2 * s) n * upperPolyProfile A gamma n * V omega := by
      ring
    _ ≤ (192 * A * s * rho⁻¹ ^ 3) * V omega := hBsmall
    _ ≤ Bone * V omega := mul_le_mul_of_nonneg_right hcoef hV0
    _ = Yone omega := rfl

private theorem upperFiniteQGeTwoInfinityAggregation_estimate3 :
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ)
      {s scaling Cblock Krare eps sigmaExp : ℝ}
      (hper :
        ∀ (k : ℕ),
          ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
            ∃ (Uone : Cutoff.CutoffSample d → ℝ) (Uexp : Cutoff.CutoffSample d → ℝ),
              (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uone omega) ∧
                Measurable Uone ∧
                  (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uexp omega) ∧
                    Measurable Uexp ∧
                      (∀ (omega : Cutoff.CutoffSample d),
                          cutoffBBlockFamily M m scaling R omega ≤ Cblock + Uone omega + Uexp
                            omega) ∧
                        IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
                          (gammaSigma (1 : ℝ)) Uone
                            (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M) M.gamma k) ∧
                          IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
                            d)) (gammaSigma sigmaExp)
                            Uexp (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * eps ^ (15
                              : ℕ))),
      let mu : Measure (Cutoff.CutoffSample d) := (↑(Cutoff.cutoffSampleLaw M) : Measure
        (Cutoff.CutoffSample d));
      let gamma : ℝ := M.gamma;
      let rho : ℝ := (2 : ℝ) * s - gamma;
      let ctop : ℝ := (3 : ℝ) ^ ((2 : ℝ) * s);
      let A : ℝ := upperOrdinaryJointProfileBound d Cblock (Disorder.cstar M) gamma;
      let Bone : ℝ := (384 : ℝ) * A * s * rho⁻¹ ^ (3 : ℕ);
      let UoneCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R : TriadicCube
        d) =>
        if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
          Classical.choose (hper k R hR)
        else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
      let UexpCube : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (R : TriadicCube
        d) =>
        if hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) then
          Classical.choose (Classical.choose_spec (hper k R hR))
        else fun (_ : Cutoff.CutoffSample d) => (0 : ℝ);
      let Gone : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k (UoneCube k);
      let Gexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) => blockGridSup d m k (UexpCube k);
      let aone : ℕ → ℝ := fun (k : ℕ) => upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M)
        gamma k;
      let V : Cutoff.CutoffSample d → ℝ := jointGridDepthEnvelope d m UoneCube aone;
      let collar : ℕ → ℝ := fun (k : ℕ) => (3 : ℝ) ^ (gamma * ((↑k : ℝ) + (1 : ℝ)));
      let Wexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
        (collar k)⁻¹ * Gexp k omega;
      let Fexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
        ctop * Wexp (0 : ℕ) omega + Wexp k omega;
      let Xexp : ℕ → Cutoff.CutoffSample d → ℝ := fun (k : ℕ) (omega : Cutoff.CutoffSample d) =>
        gridWeight rho k * Fexp k omega;
      let Rraw : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) => ∑' (k : ℕ),
        Xexp k omega;
      ∀ (hRrawAE : AEMeasurable Rraw mu),
        let Yexp : Cutoff.CutoffSample d → ℝ := AEMeasurable.mk Rraw hRrawAE;
        let Odepth : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) => Gone n.pred;
        let Edepth : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) => Gexp n.pred;
        let Z : ℕ → Cutoff.CutoffSample d → ℝ := fun (n : ℕ) (omega : Cutoff.CutoffSample d) =>
          scaling *
            Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale (originCube d m) (m - (↑n : ℤ))
              (Cutoff.coefficientCutoff M.nu m omega);
        ∀ (_ : ∀ (n : ℕ) (omega : Cutoff.CutoffSample d), Z n omega ≤ Cblock + Odepth n omega +
          Edepth n omega),
          let Yone : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) => Bone * V
            omega;
          ∀ (omega : Cutoff.CutoffSample d) (n : ℕ) (_ : (0 : ℝ) ≤ endpointWeight ((2 : ℝ) * s) n)
            (_ : endpointWeight ((2 : ℝ) * s) n * Cblock ≤ Cblock)
            (_ : endpointWeight ((2 : ℝ) * s) n * Odepth n omega ≤ Yone omega)
            (_ : endpointWeight ((2 : ℝ) * s) n * Edepth n omega ≤ Yexp omega),
            endpointWeight ((2 : ℝ) * s) n * Z n omega ≤ Cblock + Yone omega + Yexp omega := by
  intro _ _ _ s _ Cblock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Yexp Odepth Edepth Z hdepth
    Yone omega n hweight0 hdet hordinary hrareTerm
  calc
    endpointWeight (2 * s) n * Z n omega ≤
        endpointWeight (2 * s) n *
          (Cblock + Odepth n omega + Edepth n omega) :=
      mul_le_mul_of_nonneg_left (hdepth n omega) hweight0
    _ = endpointWeight (2 * s) n * Cblock +
        endpointWeight (2 * s) n * Odepth n omega +
        endpointWeight (2 * s) n * Edepth n omega := by ring
    _ ≤ Cblock + Yone omega + Yexp omega :=
      add_le_add (add_le_add hdet hordinary) hrareTerm

private theorem upperFiniteQGeTwoInfinityAggregation_momentBounds3 :
  upperFiniteQGeTwoInfinityAggregation_momentBounds3_statement := by
  classical
  intro d hd M m _ scaling Cblock Krare eps Bexp sigmaExp hCblock hsigmaExp hgamma1 hp hrareBudget
    hper mu gamma rho abase ctop A hrho hcstar habase hctop UoneCube _ hUoneCubeNonneg
      hUexpCubeNonneg hUoneCubeMeas hUoneCubeO hUexpCubeO Gone Gexp hGexpNonneg hGexpMeas aone haone
  let V : Cutoff.CutoffSample d → ℝ :=
    jointGridDepthEnvelope d m UoneCube aone
  have hVspec := jointGridDepthEnvelope_spec
    (mu := mu) d m UoneCube aone haone
      (fun k R _ => hUoneCubeMeas k R) hUoneCubeO
  have hGoneDomAE : ∀ᵐ omega ∂mu, ∀ k,
      Gone k omega ≤ upperPolyProfile A gamma k * V omega  :=
        @upperFiniteQGeTwoInfinityAggregation_estimate1 (d) (M) (m) (scaling) (Cblock) (Krare)
          (eps) (sigmaExp) (hCblock) (hgamma1) (hper) (hcstar) (hUoneCubeNonneg) (hVspec)
  let collar : ℕ → ℝ := fun k =>
    (3 : ℝ) ^ (gamma * ((k : ℝ) + 1))
  have hcollar : ∀ k, 0 < collar k := fun k => by
    dsimp [collar]
    positivity
  have hGexpO : ∀ k, IsBigOWith mu (gammaSigma sigmaExp) (Gexp k)
      (gridBlockAmp d sigmaExp (collar k * abase) k) := by
    intro k
    simpa only [Gexp] using
      (isBigOWith_gammaSigma_blockGridSup hd m k hsigmaExp
        (mul_nonneg (hcollar k).le habase.le)
        (hUexpCubeNonneg k) (hUexpCubeO k))
  let Wexp : ℕ → Cutoff.CutoffSample d → ℝ := fun k omega =>
    (collar k)⁻¹ * Gexp k omega
  have hWexpNonneg : ∀ k omega, 0 ≤ Wexp k omega := fun k omega =>
    mul_nonneg (inv_nonneg.mpr (hcollar k).le) (hGexpNonneg k omega)
  have hWexpMeas : ∀ k, Measurable (Wexp k) := fun k =>
    (hGexpMeas k).const_mul (collar k)⁻¹
  have hWexpO : ∀ k, IsBigOWith mu (gammaSigma sigmaExp) (Wexp k)
      (gridBlockAmp d sigmaExp abase k) := by
    intro k
    have hscaled := (hGexpO k).const_mul (inv_nonneg.mpr (hcollar k).le)
    have hscaleEq : (collar k)⁻¹ *
        gridBlockAmp d sigmaExp (collar k * abase) k =
          gridBlockAmp d sigmaExp abase k := by
      rw [gridBlockAmp, gridBlockAmp]
      field_simp [(hcollar k).ne']
    simpa only [Wexp, hscaleEq] using hscaled
  have hGexpEq : ∀ k omega, collar k * Wexp k omega = Gexp k omega := by
    intro k omega
    dsimp [Wexp]
    rw [← mul_assoc, mul_inv_cancel₀ (hcollar k).ne', one_mul]
  let Fexp : ℕ → Cutoff.CutoffSample d → ℝ := fun k omega =>
    ctop * Wexp 0 omega + Wexp k omega
  let afold : ℕ → ℝ := fun k =>
    foldedAmp sigmaExp ctop (fun j => gridBlockAmp d sigmaExp abase j) k
  have hFexpNonneg : ∀ k omega, 0 ≤ Fexp k omega := fun k omega =>
    add_nonneg (mul_nonneg hctop.le (hWexpNonneg 0 omega))
      (hWexpNonneg k omega)
  have hFexpMeas : ∀ k, Measurable (Fexp k) := fun k =>
    ((hWexpMeas 0).const_mul ctop).add (hWexpMeas k)
  have hafold : ∀ k, 0 < afold k := fun k => by
    dsimp [afold]
    exact foldedAmp_pos hctop.le
      (fun j => gridBlockAmp_pos hd sigmaExp habase j) k
  have hFexpO : ∀ k, IsBigOWith mu (gammaSigma sigmaExp) (Fexp k) (afold k) := by
    intro k
    have hfirst := (hWexpO 0).const_mul hctop.le
    simpa only [Fexp, afold, foldedAmp] using
      (isBigOWith_gammaSigma_add hsigmaExp
        (fun omega => mul_nonneg hctop.le (hWexpNonneg 0 omega))
        (hWexpNonneg k) ((hWexpMeas 0).const_mul ctop) (hWexpMeas k)
        (mul_pos hctop (gridBlockAmp_pos hd sigmaExp habase 0))
        (gridBlockAmp_pos hd sigmaExp habase k) hfirst (hWexpO k))
  let Xexp : ℕ → Cutoff.CutoffSample d → ℝ := fun k omega =>
    gridWeight rho k * Fexp k omega
  let bexp : ℕ → ℝ := fun k => gridWeight rho k * afold k
  have hXexpNonneg : ∀ k omega, 0 ≤ Xexp k omega := fun k omega =>
    mul_nonneg (gridWeight_nonneg rho k) (hFexpNonneg k omega)
  have hXexpMeas : ∀ k, AEMeasurable (Xexp k) mu := fun k =>
    ((hFexpMeas k).const_mul (gridWeight rho k)).aemeasurable
  have hbexp : ∀ k, 0 < bexp k := fun k =>
    mul_pos (gridWeight_pos rho k) (hafold k)
  have hbaseSum : Summable fun k : ℕ =>
      (1 : ℝ) * gridWeight rho k * gridBlockAmp d sigmaExp abase k :=
    summable_gridWeight_mul_gridBlockAmp (by norm_num) hrho habase.le 6 hp
  have hbexpSum : Summable bexp := by
    simpa only [bexp, one_mul] using
      (summable_foldedAmp (mass := (1 : ℝ)) hrho hbaseSum)
  have hXexpO : ∀ k, IsBigOWith mu (gammaSigma sigmaExp) (Xexp k) (bexp k) := by
    intro k
    simpa only [Xexp, bexp] using
      (hFexpO k).const_mul (gridWeight_nonneg rho k)
  have hXexpSumAE : ∀ᵐ omega ∂mu, Summable fun k => Xexp k omega :=
    Algsuperdiff.Section3.Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
      hsigmaExp hXexpNonneg hXexpMeas hbexp hbexpSum hXexpO
  let Rraw : Cutoff.CutoffSample d → ℝ := fun omega => ∑' k, Xexp k omega
  have hRrawAE : AEMeasurable Rraw mu := by
    dsimp [Rraw]
    exact Algsuperdiff.Section3.Provider.Orlicz.aemeasurable_tsum_of_nonneg
      hXexpMeas hXexpNonneg
  let Yexp : Cutoff.CutoffSample d → ℝ := hRrawAE.mk Rraw
  have hYexpMeas : Measurable Yexp := hRrawAE.measurable_mk
  have hRrawEqYexp : Rraw =ᵐ[mu] Yexp := hRrawAE.ae_eq_mk
  have hfoldBudget : gammaTriangleConst sigmaExp * ∑' k, bexp k ≤ Bexp := by
    have hpole := gammaTriangleConst_mul_tsum_foldedGridBlockAmp_le
      (d := d) (mass := (1 : ℝ)) (rho := rho) (sigma := sigmaExp)
      (A := abase) (ctop := ctop) (by norm_num) hrho hctop.le habase.le 6 hp
    have hpole' : gammaTriangleConst sigmaExp * ∑' k, bexp k ≤
        foldedBlockPole d sigmaExp abase 1 rho ctop 6 := by
      simpa only [bexp, one_mul] using hpole
    have hbudget' : foldedBlockPole d sigmaExp abase 1 rho ctop 6 ≤ Bexp := by
      simpa only [rho, gamma, abase, ctop] using hrareBudget
    exact hpole'.trans hbudget'
  have hRrawO : IsBigOWith mu (gammaSigma sigmaExp) Rraw Bexp := by
    have hsumO :=
      Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_tsum_aemeasurable
        hsigmaExp hXexpNonneg hXexpMeas hbexp hbexpSum hXexpO
    exact hsumO.mono_scale hfoldBudget
  have hYexpO : IsBigOWith mu (gammaSigma sigmaExp) Yexp Bexp :=
    Provider.Tail.isBigOWith_of_ae_eq hRrawEqYexp hRrawO
  exact ⟨hVspec, hGoneDomAE, hcollar, hWexpNonneg, hGexpEq, hXexpSumAE, hRrawAE, hYexpMeas,
    hRrawEqYexp, hYexpO, True.intro⟩

private theorem upper_finite_two_le_and_infinity_split_of_per_descendant
    {d : ℕ} [NeZero d] (hd : 1 ≤ d)
    (M : ABKModel d) (m : ℤ)
    {s scaling Cblock Krare eps Bexp sigmaExp : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hscaling : 0 ≤ scaling)
    (hCblock : 0 < Cblock) (hKrare : 0 < Krare) (heps : 0 < eps)
    (hsigmaExp : 0 < sigmaExp) (hgamma1 : M.gamma ≤ 1)
    (hgap : 0 < 2 * s - M.gamma)
    (hp : sigmaExp⁻¹ ≤ (6 : ℝ))
    (hrareBudget :
      foldedBlockPole d sigmaExp (Krare⁻¹ * eps ^ 15) 1
          (2 * s - M.gamma) ((3 : ℝ) ^ (2 * s)) 6 ≤ Bexp)
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
            (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 15)) :
    (∀ (r : {r : ℝ // 1 ≤ r}), 2 ≤ (r : ℝ) →
      ∃ Udet Uone Utail : Cutoff.CutoffSample d → ℝ,
        (∀ omega,
          Observable.cutoffUpperEllipticity M m m s hs
                (CoarseEllipticityExponent.finite r) omega * scaling ≤
            Udet omega + Uone omega + Utail omega) ∧
        (∀ omega, Udet omega ≤ Cblock) ∧
        Measurable Uone ∧ Measurable Utail ∧
        IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 1) Uone
          (384 * upperOrdinaryJointProfileBound d Cblock
              (Disorder.cstar M) M.gamma * s *
            (2 * s - M.gamma)⁻¹ ^ 3) ∧
        IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
          (gammaSigma sigmaExp) Utail Bexp) ∧
      (∀ q : CoarseEllipticityExponent,
        q.1 = Book.Ch02.MultiscaleExponent.infinity →
        ∃ Udet Uone Utail : Cutoff.CutoffSample d → ℝ,
          (∀ omega,
            Observable.cutoffUpperEllipticity M m m s hs q omega * scaling ≤
              Udet omega + Uone omega + Utail omega) ∧
          (∀ omega, Udet omega ≤ Cblock) ∧
          Measurable Uone ∧ Measurable Utail ∧
          IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 1) Uone
            (384 * upperOrdinaryJointProfileBound d Cblock
                (Disorder.cstar M) M.gamma * s *
              (2 * s - M.gamma)⁻¹ ^ 3) ∧
          IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
            (gammaSigma sigmaExp) Utail Bexp) := by
  classical
  let mu : Measure (Cutoff.CutoffSample d) :=
    (Cutoff.cutoffSampleLaw M).toMeasure
  let gamma : ℝ := M.gamma
  let rho : ℝ := 2 * s - gamma
  let abase : ℝ := Krare⁻¹ * eps ^ 15
  let ctop : ℝ := (3 : ℝ) ^ (2 * s)
  let A : ℝ := upperOrdinaryJointProfileBound d Cblock
    (Disorder.cstar M) gamma
  let Bone : ℝ := 384 * A * s * rho⁻¹ ^ 3
  have hgamma : 0 < gamma := by
    simpa only [gamma] using M.shellPrefix.gamma_pos
  have hrho : 0 < rho := by simpa only [rho, gamma] using hgap
  have hcstar : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have habase : 0 < abase := by
    dsimp [abase]
    positivity
  have hctop : 0 < ctop := by
    dsimp [ctop]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A, gamma]
    exact upperOrdinaryJointProfileBound_nonneg d hCblock.le
      (inv_nonneg.mpr hcstar.le) M.shellPrefix.gamma_pos.le
  have hBone : 0 ≤ Bone := by
    dsimp [Bone]
    positivity
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
  obtain ⟨hUoneCubeNonneg, hUexpCubeNonneg, hUoneCubeMeas, hUexpCubeMeas, hUoneCubeO, hUexpCubeO,
    hblock⟩ :=
    @upperFiniteQGeTwoInfinityAggregation_momentBounds2 (d) (M) (m) (scaling) (Cblock) (Krare)
      (eps) (sigmaExp) (hscaling) (hper)
  let Gone : ℕ → Cutoff.CutoffSample d → ℝ := fun k =>
    blockGridSup d m k (UoneCube k)
  let Gexp : ℕ → Cutoff.CutoffSample d → ℝ := fun k =>
    blockGridSup d m k (UexpCube k)
  have hGoneNonneg : ∀ k omega, 0 ≤ Gone k omega := fun k omega =>
    blockGridSup_nonneg d m k (UoneCube k) omega
  have hGexpNonneg : ∀ k omega, 0 ≤ Gexp k omega := fun k omega =>
    blockGridSup_nonneg d m k (UexpCube k) omega
  have hGoneMeas : ∀ k, Measurable (Gone k) := fun k =>
    measurable_blockGridSup d m k (hUoneCubeMeas k)
  have hGexpMeas : ∀ k, Measurable (Gexp k) := fun k =>
    measurable_blockGridSup d m k (hUexpCubeMeas k)
  let aone : ℕ → ℝ := fun k =>
    upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M) gamma k
  have haone : ∀ k, 0 < aone k := fun k => by
    dsimp [aone, gamma]
    exact upperSaturatedPerCubeAmplitude_pos hCblock hcstar
      M.shellPrefix.gamma_pos k
  obtain ⟨hVspec, hGoneDomAE, hcollar, hWexpNonneg, hGexpEq, hXexpSumAE, hRrawAE, hYexpMeas,
    hRrawEqYexp, hYexpO, _⟩ :=
    @upperFiniteQGeTwoInfinityAggregation_momentBounds3 (d) (hd) (M) (m) (s) (scaling) (Cblock)
      (Krare) (eps) (Bexp) (sigmaExp) (hCblock) (hsigmaExp) (hgamma1) (hp) (hrareBudget) (hper)
        (hrho) (hcstar) (habase) (hctop) (hUoneCubeNonneg) (hUexpCubeNonneg) (hUoneCubeMeas)
          (hUoneCubeO) (hUexpCubeO) (hGexpNonneg) (hGexpMeas) (haone)
  let V : Cutoff.CutoffSample d → ℝ :=
    jointGridDepthEnvelope d m UoneCube aone
  let collar : ℕ → ℝ := fun k =>
    (3 : ℝ) ^ (gamma * ((k : ℝ) + 1))
  let Wexp : ℕ → Cutoff.CutoffSample d → ℝ := fun k omega =>
    (collar k)⁻¹ * Gexp k omega
  let Fexp : ℕ → Cutoff.CutoffSample d → ℝ := fun k omega =>
    ctop * Wexp 0 omega + Wexp k omega
  let afold : ℕ → ℝ := fun k =>
    foldedAmp sigmaExp ctop (fun j => gridBlockAmp d sigmaExp abase j) k
  let Xexp : ℕ → Cutoff.CutoffSample d → ℝ := fun k omega =>
    gridWeight rho k * Fexp k omega
  let bexp : ℕ → ℝ := fun k => gridWeight rho k * afold k
  let Rraw : Cutoff.CutoffSample d → ℝ := fun omega => ∑' k, Xexp k omega
  let Yexp : Cutoff.CutoffSample d → ℝ := hRrawAE.mk Rraw
  let Odepth : ℕ → Cutoff.CutoffSample d → ℝ := fun n => Gone n.pred
  let Edepth : ℕ → Cutoff.CutoffSample d → ℝ := fun n => Gexp n.pred
  let Z : ℕ → Cutoff.CutoffSample d → ℝ := fun n omega =>
    scaling * Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
      (originCube d m) (m - (n : ℤ))
      (Cutoff.coefficientCutoff M.nu m omega)
  have hOnonneg : ∀ n omega, 0 ≤ Odepth n omega := fun n omega =>
    hGoneNonneg n.pred omega
  have hEnonneg : ∀ n omega, 0 ≤ Edepth n omega := fun n omega =>
    hGexpNonneg n.pred omega
  have hZnonneg : ∀ n omega, 0 ≤ Z n omega := by
    intro n omega
    refine mul_nonneg hscaling ?_
    exact Book.Ch05.Section52.maxDescendantBMatrixNormCoeffFieldAtScale_nonneg_of_le
      (originCube d m) (Cutoff.coefficientCutoff M.nu m omega)
        (by rw [show (originCube d m).scale = m from rfl]; omega)
  have hdepth : ∀ n omega,
      Z n omega ≤ Cblock + Odepth n omega + Edepth n omega  := @upperGrid_geometricDepthWeight (d)
        (by infer_instance) (M) (m) (scaling) (Cblock) (Krare) (eps) (sigmaExp) (hscaling) (hper)
          (hUoneCubeNonneg) (hUexpCubeNonneg) (hblock)
  have hODomAE : ∀ᵐ omega ∂mu, ∀ n,
      Odepth n omega ≤ upperPolyProfile A gamma n * V omega := by
    filter_upwards [hGoneDomAE] with omega homega
    intro n
    have hfirst := homega n.pred
    have hprof := upperPolyProfile_pred_le hA hgamma.le n
    exact hfirst.trans
      (mul_le_mul_of_nonneg_right hprof (hVspec.1 omega))
  let Yone : Cutoff.CutoffSample d → ℝ := fun omega => Bone * V omega
  obtain ⟨hYoneMeas, hYoneO, hGood⟩ :=
    @upperFiniteQGeTwoInfinityAggregation_momentBounds1 (d) (M) (m) (s) (scaling) (Cblock) (Krare)
      (eps) (sigmaExp) (hper) (hrho) (hctop) (hBone) (hVspec) (hcollar) (hWexpNonneg) (hGexpEq)
        (hXexpSumAE) (hRrawAE) (hRrawEqYexp) (hODomAE)
  constructor
  · intro r hr
    have hr0 : 0 < (r : ℝ) := lt_of_lt_of_le zero_lt_one r.property
    have ht : 1 ≤ (r : ℝ) / 2 := by linarith
    have hsr : 0 < s * (r : ℝ) := mul_pos hs hr0
    let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s (r : ℝ) n
    have hw : ∀ n, 0 ≤ w n := fun n =>
      HCPolySupport.geometricWeight_nonneg n hsr.le
    have hwsum : Summable w := by
      simpa only [w] using! HCPolySupport.summable_geometricWeight hsr
    have hwtsum : (∑' n, w n) = 1 := by
      simpa only [w] using! HCPolySupport.tsum_geometricWeight_eq_one hsr
    have hae := @upperFiniteExponent_pointwiseAggregation (d) (by infer_instance) (M) (m) (s)
      (scaling) (Cblock) (Krare) (eps) (sigmaExp) (hs) (hs1) (hscaling) (hCblock) (hgap) (hper)
        (hgamma) (hA) (hVspec) (hRrawAE) (hOnonneg) (hEnonneg) (hZnonneg) (hdepth) (hGood) (r)
          (hr) (hr0) (ht) (hsr) (hw) (hwsum) (hwtsum)
    simpa only [mu, Bone, A, rho, gamma] using
      (exists_pointwise_of_ae_threeTermSplit
        ((Observable.measurable_cutoffUpperEllipticity M m m s hs
          (CoarseEllipticityExponent.finite r)).mul_const scaling)
        hYoneMeas hYexpMeas hYoneO hYexpO hae)
  · intro q hq
    have hae : ∀ᵐ omega ∂mu,
        Observable.cutoffUpperEllipticity M m m s hs q omega * scaling ≤
          Cblock + Yone omega + Yexp omega := by
      filter_upwards [hGood] with omega hgood
      rw [congrFun (Observable.cutoffUpperEllipticity_eq_literal M m m s hs q) omega]
      apply cutoffUpperEllipticityLiteral_infinity_mul_le_of_forall
        M m m s hq hscaling omega
      intro n
      have hweight0 : 0 ≤ endpointWeight (2 * s) n := endpointWeight_nonneg _ n
      have hdet : endpointWeight (2 * s) n * Cblock ≤ Cblock := by
        exact mul_le_of_le_one_left hCblock.le
          (endpointWeight_le_one (by linarith : 0 < 2 * s) n)
      have hordinary : endpointWeight (2 * s) n * Odepth n omega ≤
          Yone omega  := @upperFiniteQGeTwoInfinityAggregation_estimate2 (d) (M) (m) (s) (scaling)
            (Cblock) (Krare) (eps) (sigmaExp) (hs) (hs1) (hgap) (hper) (hgamma) (hA) (hVspec)
              (hRrawAE) (omega) (hgood) (n) (hweight0)
      have hrareTerm : endpointWeight (2 * s) n * Edepth n omega ≤ Yexp omega :=
        (hgood.2.1.le_tsum n fun j _ =>
          mul_nonneg (endpointWeight_nonneg _ j) (hEnonneg j omega)).trans
            hgood.2.2
      have hweighted : endpointWeight (2 * s) n * Z n omega ≤
          Cblock + Yone omega + Yexp omega  := @upperFiniteQGeTwoInfinityAggregation_estimate3 (d)
            (M) (m) (s) (scaling) (Cblock) (Krare) (eps) (sigmaExp) (hper) (hRrawAE) (hdepth)
              (omega) (n) (hweight0) (hdet) (hordinary) (hrareTerm)
      calc
        scaling * (Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
            Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
              (originCube d m) (m - (n : ℤ))
              (Cutoff.coefficientCutoff M.nu m omega)) =
            endpointWeight (2 * s) n * Z n omega := by
          rw [endpointWeight_eq_rpow]
          dsimp [Z]
          ring_nf
        _ ≤ Cblock + Yone omega + Yexp omega := hweighted
    simpa only [mu, Bone, A, rho, gamma] using
      (exists_pointwise_of_ae_threeTermSplit
        ((Observable.measurable_cutoffUpperEllipticity M m m s hs q).mul_const scaling)
        hYoneMeas hYexpMeas hYoneO hYexpO hae)

private theorem foldedBlockPole_normalized_rare_gate_le
    {d : ℕ} (hd : 2 ≤ d) {sigma gamma s eps : ℝ}
    (hsigma0 : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hs1 : s ≤ 1)
    (hwin : gamma / 2 + eps ≤ s) :
    foldedBlockPole d ((1 - sigma) / 3)
        ((4 * upperAfterBandRareTriangleConst ^ 2 * (1658880 : ℝ) ^ 2 *
          upperAfterBandRareGridNetConst d)⁻¹ * eps ^ 15)
        1 (2 * s - gamma) ((3 : ℝ) ^ (2 * s)) 6 ≤ eps := by
  let tau : ℝ := (1 - sigma) / 3
  let T : ℝ := gammaTriangleConst tau
  let Tbar : ℝ := upperAfterBandRareTriangleConst
  let G : ℝ := gridNetConst d tau
  let Gbar : ℝ := upperAfterBandRareGridNetConst d
  let ctop : ℝ := (3 : ℝ) ^ (2 * s)
  let Krare : ℝ := 4 * Tbar ^ 2 * (1658880 : ℝ) ^ 2 * Gbar
  have hT0 : 0 ≤ T := gammaTriangleConst_pos.le
  have hTbar0 : 0 ≤ Tbar := by
    dsimp only [Tbar]
    rw [upperAfterBandRareTriangleConst]
    positivity
  have hTbarPos : 0 < Tbar := by
    dsimp only [Tbar]
    rw [upperAfterBandRareTriangleConst]
    positivity
  have hG0 : 0 ≤ G := gridNetConst_nonneg d tau
  have hGbar0 : 0 ≤ Gbar := by
    dsimp only [Gbar]
    rw [upperAfterBandRareGridNetConst]
    positivity
  have hGbarPos : 0 < Gbar := by
    have hdpos : (0 : ℝ) < d := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    dsimp only [Gbar]
    rw [upperAfterBandRareGridNetConst]
    positivity
  have hKrarePos : 0 < Krare := by
    dsimp only [Krare]
    positivity
  have hT : T ≤ Tbar := by
    dsimp only [T, Tbar, tau]
    simpa only [upperProfileTargetSigma] using
      gammaTriangleConst_upperProfileTarget_le hsigma0 hsigmaHalf
  have hG : G ≤ Gbar := by
    dsimp only [G, Gbar, tau]
    simpa only [upperProfileTargetSigma] using
      gridNetConst_upperProfileTarget_le hd hsigma0 hsigmaHalf
  have hTpow : T ^ 2 ≤ Tbar ^ 2 :=
    pow_le_pow_left₀ hT0 hT 2
  have hTG : T ^ 2 * G ≤ Tbar ^ 2 * Gbar :=
    mul_le_mul hTpow hG hG0 (pow_nonneg hTbar0 2)
  have hTGbar0 : 0 ≤ Tbar ^ 2 * Gbar :=
    mul_nonneg (pow_nonneg hTbar0 2) hGbar0
  have hctop0 : 0 ≤ ctop := by
    dsimp only [ctop]
    exact Real.rpow_nonneg (by norm_num) _
  have hctop : ctop ≤ 9 := by
    have hpow : (3 : ℝ) ^ (2 * s) ≤ (3 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    dsimp only [ctop]
    norm_num at hpow ⊢
    exact hpow
  have hC0 : 0 ≤ 128 * (ctop + 720) := by positivity
  have hC : 128 * (ctop + 720) ≤ 4 * (1658880 : ℝ) ^ 2 := by
    calc
      128 * (ctop + 720) ≤ 128 * (9 + 720) := by linarith only [hctop]
      _ ≤ 4 * (1658880 : ℝ) ^ 2 := by norm_num
  have hcoef :
      T ^ 2 * (1 * G) * (128 * (ctop + 720)) ≤ Krare := by
    calc
      T ^ 2 * (1 * G) * (128 * (ctop + 720)) =
          (T ^ 2 * G) * (128 * (ctop + 720)) := by ring
      _ ≤ (Tbar ^ 2 * Gbar) * (4 * (1658880 : ℝ) ^ 2) :=
        mul_le_mul hTG hC hC0 hTGbar0
      _ = Krare := by
        dsimp only [Krare]
        ring
  have hcoefInv :
      (T ^ 2 * (1 * G) * (128 * (ctop + 720))) * Krare⁻¹ ≤ 1 := by
    calc
      (T ^ 2 * (1 * G) * (128 * (ctop + 720))) * Krare⁻¹
          ≤ Krare * Krare⁻¹ :=
        mul_le_mul_of_nonneg_right hcoef (inv_nonneg.mpr hKrarePos.le)
      _ = 1 := mul_inv_cancel₀ hKrarePos.ne'
  have hgate :
      T ^ 2 * (1 * G) * (128 * (ctop + 720)) *
          (Krare⁻¹ * eps ^ 15) ≤ eps ^ 8 := by
    calc
      T ^ 2 * (1 * G) * (128 * (ctop + 720)) *
            (Krare⁻¹ * eps ^ 15) =
          ((T ^ 2 * (1 * G) * (128 * (ctop + 720))) * Krare⁻¹) *
            eps ^ 15 := by ring
      _ ≤ 1 * eps ^ 15 :=
        mul_le_mul_of_nonneg_right hcoefInv (pow_nonneg heps.le 15)
      _ = eps ^ 15 := one_mul _
      _ ≤ eps ^ 8 :=
        pow_le_pow_of_le_one heps.le heps1 (by norm_num)
  change foldedBlockPole d tau (Krare⁻¹ * eps ^ 15) 1
      (2 * s - gamma) ctop 6 ≤ eps
  refine foldedBlockPole_frozenUpper_le (by norm_num) ?_ hctop0
    heps heps1 hwin ?_
  · exact mul_nonneg (inv_nonneg.mpr hKrarePos.le) (pow_nonneg heps.le 15)
  · simpa only [T, G] using hgate

private theorem upper_finite_two_le_and_infinity_of_per_descendant_with_rare_budget
    {d : ℕ} [NeZero d] (hd : 1 ≤ d)
    (M : ABKModel d) (m : ℤ)
    {s scaling Cblock Krare eps sigmaExp Cup : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hscaling : 0 ≤ scaling)
    (hCblock : 0 < Cblock) (hKrare : 0 < Krare) (heps : 0 < eps)
    (hsigmaExp : 0 < sigmaExp) (hgamma1 : M.gamma ≤ 1)
    (hgap : 0 < 2 * s - M.gamma)
    (hp : sigmaExp⁻¹ ≤ (6 : ℝ))
    (hCup : 0 < Cup) (hCblockCup : Cblock ≤ Cup)
    (hordinaryHead :
      1152 * triadicJointDepthEntropyConst d * Cblock ≤ Cup)
    (hrareBudget :
      foldedBlockPole d sigmaExp (Krare⁻¹ * eps ^ 15) 1
          (2 * s - M.gamma) ((3 : ℝ) ^ (2 * s)) 6 ≤ eps)
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
            (Krare⁻¹ * (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 15)) :
    (∀ (r : {r : ℝ // 1 ≤ r}), 2 ≤ (r : ℝ) →
      Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
        (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 1)
        (gammaSigma sigmaExp)
        (fun omega =>
          Observable.cutoffUpperEllipticity M m m s hs
            (CoarseEllipticityExponent.finite r) omega * scaling)
        Cup
        (Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
          (2 * s - M.gamma)⁻¹ ^ 3) eps) ∧
      (∀ q : CoarseEllipticityExponent,
        q.1 = Book.Ch02.MultiscaleExponent.infinity →
        Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
          (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 1)
          (gammaSigma sigmaExp)
          (fun omega =>
            Observable.cutoffUpperEllipticity M m m s hs q omega * scaling)
          Cup
          (Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3) eps) := by
  have hsplit :=
    upper_finite_two_le_and_infinity_split_of_per_descendant
      hd M m hs hs1 hscaling hCblock hKrare heps hsigmaExp hgamma1 hgap hp
        hrareBudget hper
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hcstar : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hAone : 0 < Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
      (2 * s - M.gamma)⁻¹ ^ 3 := by
    positivity
  have hordinaryBudget :
      384 * upperOrdinaryJointProfileBound d Cblock
          (Disorder.cstar M) M.gamma * s *
        (2 * s - M.gamma)⁻¹ ^ 3 ≤
      Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
        (2 * s - M.gamma)⁻¹ ^ 3 := by
    rw [upperOrdinaryJointProfileBound]
    have htail : 0 ≤ (Disorder.cstar M)⁻¹ * s * M.gamma *
        (2 * s - M.gamma)⁻¹ ^ 3 :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (inv_nonneg.mpr hcstar.le) hs.le) hgamma.le)
        (pow_nonneg (inv_nonneg.mpr hgap.le) 3)
    calc
      384 * (3 * triadicJointDepthEntropyConst d * Cblock *
            (Disorder.cstar M)⁻¹ * M.gamma) * s *
          (2 * s - M.gamma)⁻¹ ^ 3 =
        (1152 * triadicJointDepthEntropyConst d * Cblock) *
          ((Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3) := by ring
      _ ≤ Cup * ((Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3) :=
        mul_le_mul_of_nonneg_right hordinaryHead htail
      _ = Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3 := by ring
  constructor
  · intro r hr
    obtain ⟨Udet, Uone, Utail, hdom, hdet, hUoneM, hUtailM,
        hUoneO, hUtailO⟩ := hsplit.1 r hr
    exact two_term_one_sided_orlicz_of_pointwise_split
      one_pos hsigmaExp hAone heps
      ((Observable.measurable_cutoffUpperEllipticity M m m s hs
        (CoarseEllipticityExponent.finite r)).mul_const scaling)
      hUoneM hUtailM hdom (fun omega => (hdet omega).trans hCblockCup)
      (hUoneO.mono_scale hordinaryBudget) hUtailO
  · intro q hq
    obtain ⟨Udet, Uone, Utail, hdom, hdet, hUoneM, hUtailM,
        hUoneO, hUtailO⟩ := hsplit.2 q hq
    exact two_term_one_sided_orlicz_of_pointwise_split
      one_pos hsigmaExp hAone heps
      ((Observable.measurable_cutoffUpperEllipticity M m m s hs q).mul_const scaling)
      hUoneM hUtailM hdom (fun omega => (hdet omega).trans hCblockCup)
      (hUoneO.mono_scale hordinaryBudget) hUtailO

/-- Aggregate one per-descendant ordinary/rare decomposition simultaneously
for every finite exponent `q ≥ 2` and for the infinite exponent. -/
theorem upper_finite_two_le_and_infinity_of_per_descendant
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (m : ℤ)
    {sigma s scaling Cblock eps Cup : ℝ}
    (hsigma0 : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hs : 0 < s) (hs1 : s ≤ 1) (hscaling : 0 ≤ scaling)
    (hCblock : 0 < Cblock) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hgamma1 : M.gamma ≤ 1) (hgap : 0 < 2 * s - M.gamma)
    (hwin : M.gamma / 2 + eps ≤ s)
    (hCup : 0 < Cup) (hCblockCup : Cblock ≤ Cup)
    (hordinaryHead :
      1152 * triadicJointDepthEntropyConst d * Cblock ≤ Cup)
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
            ((4 * upperAfterBandRareTriangleConst ^ 2 * (1658880 : ℝ) ^ 2 *
                upperAfterBandRareGridNetConst d)⁻¹ *
              (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 15)) :
    (∀ (r : {r : ℝ // 1 ≤ r}), 2 ≤ (r : ℝ) →
      Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
        (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 1)
        (gammaSigma ((1 - sigma) / 3))
        (fun omega =>
          Observable.cutoffUpperEllipticity M m m s hs
            (CoarseEllipticityExponent.finite r) omega * scaling)
        Cup
        (Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
          (2 * s - M.gamma)⁻¹ ^ 3) eps) ∧
      (∀ q : CoarseEllipticityExponent,
        q.1 = Book.Ch02.MultiscaleExponent.infinity →
        Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
          (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 1)
          (gammaSigma ((1 - sigma) / 3))
          (fun omega =>
            Observable.cutoffUpperEllipticity M m m s hs q omega * scaling)
          Cup
          (Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3) eps) := by
  let Krare : ℝ := 4 * upperAfterBandRareTriangleConst ^ 2 *
    (1658880 : ℝ) ^ 2 * upperAfterBandRareGridNetConst d
  have hKrare : 0 < Krare := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    dsimp only [Krare]
    rw [upperAfterBandRareTriangleConst, upperAfterBandRareGridNetConst]
    positivity
  have hsigmaExp : 0 < (1 - sigma) / 3 := by linarith
  have hp : ((1 - sigma) / 3)⁻¹ ≤ (6 : ℝ) :=
    frozenUpperIndex_inv_le_natSix hsigmaHalf
  have hrare : foldedBlockPole d ((1 - sigma) / 3) (Krare⁻¹ * eps ^ 15) 1
      (2 * s - M.gamma) ((3 : ℝ) ^ (2 * s)) 6 ≤ eps := by
    simpa only [Krare] using foldedBlockPole_normalized_rare_gate_le hd hsigma0
      hsigmaHalf heps heps1 hs1 hwin
  exact upper_finite_two_le_and_infinity_of_per_descendant_with_rare_budget
    (by omega) M m hs hs1 hscaling hCblock hKrare heps hsigmaExp hgamma1 hgap hp
      hCup hCblockCup hordinaryHead hrare (by simpa only [Krare] using hper)

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
