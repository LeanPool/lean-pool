/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.SelectionData
public import LeanPool.HighContrastHomogenization.Entry.ResponseTransfer

/-!
# High-contrast homogenization: Entry.Statements.ResponseTransfer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Proposition `p.response.transfer` — duality gap on Euclidean cubes

`p.response.transfer`, the paper's Proposition "Duality gap on Euclidean cubes",
transcribed from the printed display.

Reading of the display, stated here so that no divergence is silent:

* This is the
  generalized raw-output statement. The numerical global-selection data `ε`, `Cprof` and
  `Cglob` are raw inputs satisfying the displayed ranges and output inequalities, with the
  response constants allowed to depend on them. At the furnished values
  `ε(d,γ)`, `Cprof(H,d,γ)` and `Cglob(H,σ,d,γ)`, this reduces to the printed dependencies
  `Bresp(d,γ,δ,σ)` and `C(d,γ,δ,σ)`.
* "Any output of Proposition `p.global.selection` with these parameters" is expanded as the
  output tuple `(F,s,t)` together with the printed global-selection clauses
  `e.global.selection.scales`, `e.global.selection.calibration`, `e.global.selection.profile`
  and `e.global.selection.eccentricity`, at the grid
  `q = Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)`. No new output-record
  definition is
  introduced.
* The two raw global-selection constants are named distinctly from the response constants:
  `Cprof`, corresponding at the furnished value to `C(H,d,γ)` in
  `e.global.selection.profile`, and `Cglob`, corresponding at the furnished value to
  `C(H,σ,d,γ)` in the lower scale, upper scale and eccentricity bounds. They are fixed in
  the same relative positions as in `p.global.selection` before the response proof chooses
  `σ₀`, `Bresp` and `Cresp`, while all response choices remain independent of `E`, the
  coefficient law and `Π`.
* **The source lower scale is a standing hypothesis.**
  Near `e.source.lower.scale` reads "From now on `j_*` satisfies
  `e.source.lower.scale`", with `C_src` the constant of the source estimate
  (near `e.source.lower.scale`). Thus
  `j_* ≥ ⌈C_src(d,γ) log_3(2K_{Ψ_S})⌉` with `C_src` chosen before the raw `ε`. That sentence stands
  from there onward, of the same kind as `3^{j_*} ≥ 2d`
  near `e.rounded.grid.bounds`: every later statement whose type mentions `j_*` carries it. Here
  it appears inside the printed global-selection lower-scale antecedent, before the rest of
  the output display.
* `H = H(d,γ,δ)` is a natural number with `H ≥ max {4,h}`. `σ₀ ∈ (0,ε]`; for
  `σ ∈ (0,σ₀]`, `Bresp ≥ 1` and `Cresp < ∞` are bound before `P`, `E`, `Ψ`, `K`, `Src`,
  `B`, `j_*` and the output tuple, so the final sentence "All choices are independent of
  `E`, the coefficient law, and `Π`" is part of the declaration.
* `Π` is `aspectRatio E`, `Θ_m` is `annealedContrast P m`, `𝔪 = m(F)` is
  `explicitCanonicalMetric F`, `𝐀hom_{s,q}` is `adaptedMean P q s`, `D_{q,j_*}` is
  `determinantDrift`, `𝒫_q(m;n)` is `profile P γ q jStar n m`, and `□_{2j_*}` is
  `HighContrast.centeredCube d (2 * jStar)`. The deterministic Euclidean generation
  `m_ent` is an integer generation, satisfying the printed strict inequality `m_ent > t`.
* The display names no hypothesis on the coefficient law; the manuscript's standing
  assumptions are in force throughout and are carried in the binder order of the root statement
  `HCPoly/Entry/Statements/PolynomialEntry.lean`, after the response constants, whose printed
  argument
  lists say they do not depend on the law.

The proof is one application of `HCPolySupport.HighContrast.Entry.response_transfer`
(`HCPoly/Entry/ResponseTransfer.lean`) to the binders of the statement.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean annealedContrast aspectRatio blockScale)
namespace HCPolySupport.HighContrast

open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- **Proposition `p.response.transfer`**. In the
the generalized raw-output form, one source constant `Csrc(d,γ)` works for every raw
`ε ∈ (0,ε₀]`; for every `δ ∈ (0,1]` there are `H ≥ max {4,h}` and `σ₀ ∈ (0,ε]`
such that, for every `σ ∈ (0,σ₀]` and raw global constant `Cglob`, there are response
constants `Bresp ≥ 1` and `Cresp < ∞` with: every qualifying global-selection output at
`B ≥ max {B₀,Bresp}` admits a deterministic Euclidean generation `m_ent > t` satisfying
`m_ent - t ≤ ⌈Cresp log₃(2+Π)⌉` and `Θ_{m_ent}-1 ≤ δ`. -/
theorem response_transfer
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 →
      ∀ δ : ℝ, δ ∈ Set.Ioc (0 : ℝ) 1 →
        ∃ H : ℕ, max 4 S.h ≤ H ∧
          ∀ Cprof : ℝ, 0 < Cprof →
            ∃ σ₀ : ℝ, σ₀ ∈ Set.Ioc (0 : ℝ) ε ∧
              ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) σ₀ →
                ∀ Cglob : ℝ, 0 < Cglob →
                  ∃ Bresp : ℝ, 1 ≤ Bresp ∧
                    ∃ Cresp : ℝ, 0 < Cresp ∧
                      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                        (Src : CoeffSpace d → ℝ),
                        IsProbabilityMeasure P →
                        IsStationaryLaw P →
                        IsUnitRangeLaw P →
                        CoarseEllipticityDagger P γ E Ψ K Src →
                        ∀ B : ℝ, max (S.B0 ε σ) Bresp ≤ B →
                          ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                            ⌈Cglob * (B + 1) * Real.logb 3 (2 + aspectRatio E) +
                                Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                              ∀ (F : BlockMat d) (s t : ℤ),
                                IsSymmetricBlockMat F →
                                Book.Ch02.BlockPosDef F →
                                s < t →
                                t = s + (H : ℤ) →
                                (jStar : ℤ) +
                                    ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ s →
                                t ≤ (jStar : ℤ) +
                                    ⌈(B + Cglob) * Real.logb 3 (2 + aspectRatio E)⌉ →
                                HighContrast.adaptedCell
                                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t ⊆
                                  HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                                BlockMatLoewnerLE
                                  (blockScale (1 - Real.sqrt ε * σ) F)
                                  (adaptedMean P
                                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s) →
                                BlockMatLoewnerLE
                                  (adaptedMean P
                                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s)
                                  (blockScale (1 + Real.sqrt ε * σ) F) →
                                (d : ℝ)⁻¹ *
                                    detIncrement P
                                      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s t < σ →
                                max
                                      (max
                                        (profile P γ
                                          (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
                                          jStar s s)
                                        (profile P γ
                                          (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
                                          jStar s t))
                                      (profile P γ
                                        (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
                                        jStar t t) +
                                    determinantDrift P γ
                                      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s +
                                    determinantDrift P γ
                                      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t ≤
                                  Cprof * σ ^ ((1 - γ) / 8) →
                                (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) ^
                                    ((1 : ℝ) / 2) ≤
                                  (2 + aspectRatio E) ^ Cglob →
                                ∃ mEnt : ℤ,
                                  t < mEnt ∧
                                    mEnt - t ≤
                                      ⌈Cresp * Real.logb 3 (2 + aspectRatio E)⌉ ∧
                                    annealedContrast P mEnt - 1 ≤ δ := by exact HCPolySupport.HighContrast.Entry.response_transfer d hd γ hγ S hS

end HCPolySupport.HighContrast
