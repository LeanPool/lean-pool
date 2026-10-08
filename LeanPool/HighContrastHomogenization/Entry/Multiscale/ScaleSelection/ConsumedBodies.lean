/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.SelectionData
public import LeanPool.HighContrastHomogenization.Entry.SuccessfulShortBridge
public import LeanPool.HighContrastHomogenization.Entry.OneGridPropagation
public import LeanPool.HighContrastHomogenization.Entry.TwoGridTransport
public import LeanPool.HighContrastHomogenization.Entry.ProjectiveStep
public import LeanPool.HighContrastHomogenization.Entry.Geometry.BridgeEccentricity
public import LeanPool.HighContrastHomogenization.Entry.Geometry.CanonicalMetricBounds
public import LeanPool.HighContrastHomogenization.Entry.Geometry.ProjectiveStep
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Entry.Annealed.ShortBridge
public import LeanPool.HighContrastHomogenization.Entry.Annealed.BridgeBoundarySum
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.SelectionExponentBounds

/-!
# High-contrast homogenization: Entry.Multiscale.ScaleSelection.ConsumedBodies

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The consumed statement bodies and the selection length

The three propositions this decomposition consumes, each written as the body of its
statement after the outermost constants (`OneGridBody`, `TransportBody`,
`BridgeBody`), and the selection length `L = L₀ + ⌈(3/2) log₃ σ⁻¹⌉`
of `e.bridge.length.choice` (`p.scale.selection`).

Two admitted strengthenings of the printed choices are used, documented here rather than
only repeated by formula: `L₀ ≥ 1` is obtained by the printed permission to increase `L₀`,
ensuring `L > 0`; `B₀ ≥ 2 C_tr (L+1)` is a stronger choice of
the statement's own threshold, licensed by `p.scale.selection`, using
`log₃(2+Π) ≥ 1/2` from `Π ≥ 0`. It does not add a hypothesis to `Selects`.

Part of the proof of
`HCPoly/Entry/Statements/ScaleSelection.lean`.  Conventions of the group: `q = 𝒬(𝔪)` is
`Geometry.explicitRoundedGrid jStar m`; the printed data are `h = 2Q`, `c = c₀`,
`L(ε,σ) = selectionLength L₀ σ` and
`B₀(ε,σ) = max 1 (max (B₀^bridge (√ε σ) L) (2 C_tr (L+1)))`; `√ε` is the printed
`ε^{1/2}`; the source lower scale `e.source.lower.scale` is carried wherever
`j_*` appears with the law, and no integrability, finiteness or
measurability premise is added anywhere.  Unused hypothesis binders of a statement are
underscore-prefixed; the tree compiles with `-DwarningAsError=true`.

The declaration text of this file is the closed skeleton's, copied unchanged; only this
header, the imports and the namespace frame are new.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ### The consumed statement bodies, after their constants -/

/-- The body of `Entry.fixed_geometry_one_grid_propagation_full`
(`HCPoly/Entry/Statements/OneGridPropagation.lean`)
after `∃ Csrc, 0 < Csrc ∧ ∃ C, 0 < C ∧`, verbatim. -/
@[expose]
def OneGridBody (d : ℕ) (γ Csrc C : ℝ) : Prop :=
  ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ),
    IsProbabilityMeasure P →
    IsStationaryLaw P →
    IsUnitRangeLaw P →
    CoarseEllipticityDagger P γ E Ψ K S →
    ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
      ∀ L : ℤ, 1 ≤ L →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ (metric : Mat d), metric.PosDef →
            ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
              history P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                  C * profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ∧
                (n + (h : ℤ) ≤ m →
                  profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h : ℤ)) ≤
                    1 / 8 *
                        Real.exp ((bigQ d γ : ℝ) *
                          synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                            (h : ℤ) m) *
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                      C *
                        (Real.exp ((bigQ d γ : ℝ) *
                            synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                              (h : ℤ) m) - 1)) ∧
                (n + (h : ℤ) ≤ m →
                  profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ≤ 1 →
                    profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) ≤
                      C * (L : ℝ) *
                        (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          Real.exp ((bigQ d γ : ℝ) *
                            detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m +
                              L)) - 1)) ∧
                (m = n →
                  history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n ≤ 1 →
                    profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (n + L) ≤
                      C * (L : ℝ) *
                        (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
                          Real.exp ((bigQ d γ : ℝ) *
                            detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n +
                              L)) - 1)) ∧
                fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
                      meanHistory P γ (Geometry.explicitRoundedGrid jStar metric) (jStar : ℤ) m +
                      determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                    C * (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                      determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m) ∧
                (n + (h : ℤ) ≤ m →
                  profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h : ℤ)) +
                      determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                        (m + (h : ℤ)) ≤
                    1 / 8 *
                        Real.exp ((bigQ d γ : ℝ) *
                          synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                            (h : ℤ) m) *
                        (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            m) +
                      C *
                        (Real.exp ((bigQ d γ : ℝ) *
                            synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                              (h : ℤ) m) - 1)) ∧
                (∀ m₀ : ℤ, (jStar : ℤ) + (h : ℤ) ≤ m₀ →
                  ∀ Ksteps : ℕ, 1 ≤ Ksteps →
                    ∑ k ∈ Finset.range Ksteps,
                        synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ)
                          (m₀ + (k : ℤ) * (h : ℤ)) ≤
                      (h : ℝ) *
                        detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                          (m₀ + 1 - (h : ℤ)) (m₀ + (Ksteps : ℤ) * (h : ℤ))) ∧
                ((m = n ∨ n + (h : ℤ) ≤ m) →
                  profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                      determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤ 1 →
                    profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) +
                        determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                          (m + L) ≤
                      C * (L : ℝ) *
                        (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
                          Real.exp ((bigQ d γ : ℝ) *
                            detIncrement P (Geometry.explicitRoundedGrid jStar metric) m
                              (m + L)) - 1))

/-- The body of `Entry.two_grid_transport` (`HCPoly/Entry/Statements/TwoGridTransport.lean`) after
`∃ C, 1 ≤ C ∧ ∃ Csrc, 0 < Csrc ∧`, verbatim. -/
@[expose]
def TransportBody (d : ℕ) (γ C Csrc : ℝ) : Prop :=
  ∀ ρ : ℝ, ρ ∈ Set.Ioc (0 : ℝ) 1 →
  ∀ δ : ℝ, δ ∈ Set.Icc (0 : ℝ) (1 / 4) →
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
        ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
          ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n →
            ∀ L : ℕ,
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
                  HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mPlus) (n + (L :
                    ℤ)) ⊆
                HighContrast.centeredCube d (2 * (jStar : ℤ)) →
              C * ((L : ℝ) +
                  Real.logb 3 ((2 + aspectRatio E) * (‖m‖ * ‖m⁻¹‖))) ≤
                (n : ℝ) - (jStar : ℝ) →
              projectiveDistance m mPlus ≤ 1 →
              C + Real.logb 3 ρ⁻¹ ≤ (L : ℝ) →
              profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + 2 * (L : ℤ)) +
                  determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
                    (n + 2 * (L : ℤ)) ≤
                (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * (L : ℝ)) * ρ →
              BlockMatLoewnerLE
                  (blockScale (1 - δ)
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
                  (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) →
              BlockMatLoewnerLE
                  (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
                  (blockScale (1 + δ)
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)))) →
              profile P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar (n + (L : ℤ))
                    (n + (L : ℤ)) +
                  determinantDrift P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar
                    (n + (L : ℤ)) ≤
                C * (δ + ρ)

/-- The body of `Entry.successful_short_bridge`
(`HCPoly/Entry/Statements/SuccessfulShortBridge.lean`) after
`∃ L₀ c₀, c₀ ∈ Ioo 0 1 ∧ ∃ Csrc, 0 < Csrc ∧`, with the inner `∃ B₀` Skolemized into the
function `B₀ : ℝ → ℕ → ℝ` of `(σ, L)`; otherwise verbatim. -/
@[expose]
def BridgeBody (d : ℕ) (γ : ℝ) (L₀ : ℕ) (c₀ Csrc : ℝ) (B₀ : ℝ → ℕ → ℝ) : Prop :=
  ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) 1 →
  ∀ L : ℕ, (L₀ : ℤ) + ⌈Real.logb 3 σ⁻¹⌉ ≤ (L : ℤ) →
    1 ≤ B₀ σ L ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
            ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n →
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
                  HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mPlus)
                    (n + (L : ℤ)) ⊆
                HighContrast.centeredCube d (2 * (jStar : ℤ)) →
              Real.log (‖m‖ * ‖m⁻¹‖) ≤
                c₀ / (L : ℝ) *
                  ((k : ℝ) - (jStar : ℝ) -
                    (⌈B₀ σ L * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) →
              k + 2 * (bigQ d γ : ℤ) ≤ n →
              projectiveDistance m mPlus ≤ 1 →
              profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                    determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
                  detIncrement P (Geometry.explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ)) ≤
                c₀ * σ →
              BlockMatLoewnerLE
                  (blockScale (1 - σ)
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
                  (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) ∧
                BlockMatLoewnerLE
                  (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
                  (blockScale (1 + σ)
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                      (n + 2 * (L : ℤ))))

/-- The selection length `L = L₀ + ⌈(3/2) log₃(σ⁻¹)⌉` of `e.bridge.length.choice`
(`p.scale.selection`). It does not depend on `ε`. -/
@[expose]
noncomputable def selectionLength (L₀ : ℕ) (σ : ℝ) : ℕ :=
  L₀ + ⌈3 / 2 * Real.logb 3 σ⁻¹⌉₊

end

end HCPolySupport.HighContrast.Multiscale
