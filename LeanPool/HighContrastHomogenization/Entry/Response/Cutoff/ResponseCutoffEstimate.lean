/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseTransferFromCutoffBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.FirstErrorRowArithmetic
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CutoffEnergyDefectRowObligations
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CutoffMeanRowCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.TerminalHalfEnergyIntegrability
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio

/-!
# High-contrast homogenization: Entry.Response.Cutoff.ResponseCutoffEstimate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cutoff estimate

The cutoff decomposition of the centred response, before the final scalar inequality, bounds
`|Jtilde^±(e)|` by the three error rows — the energy-defect row, the cutoff-mean row, and the
cutoff-oscillation row — plus the cutoff pairing term; combining that bound with the constant
`32 d^2 3^{-t}` needed to construct a genuine cutoff, in place of the naive class's vacuous one,
closes it under a weak-pairing hypothesis on the maximizer family. This file then states and
proves the cutoff estimate `e.response.cutoff.estimate` itself, one of the inputs to the response
decomposition `adapted_response_core`: the bound on the centred response `Jtilde^±(e)` in terms of
the energy-defect row, the cutoff-mean row, and the cutoff pairing term, closed on the response's
own concrete data.
-/

section
open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]
/-! ## The variational calculation of AK.HC (3.45)-(3.54) with the cutoff decomposition
(3.46) and the mean cancellation of `p.response.transfer`.

The two cutoff-mean terms `e2` below are exactly the two rows re-typed here onto the current
carriers `respTauMinus/Plus` (`ResponseBlockObjects.lean`), `respEJMinus/Plus`,
`respLsMinus/Plus`, the paper's `𝓛_s^±`, built from `respSourceLoad`).

The three error terms of `p.response.transfer` are, in order:

* `e1` — replacing the terminal optimizer by its scale-`s` cell optimizers:
  `C (τ^± + (τ^± E[J_t^±])^{1/2} + 3^{-H} E[J_t^±])`;
* `e2` — the two cutoff-mean terms, after subtracting the cell average of `φ`.  The constant cell
  means cancel after expectation because the scale-`s` translations are integral and
  `(φ)_{U_t} = 1`; what is left costs `C (τ^± 𝓛_s^±)^{1/2}`;
* `e3` — pairing the within-cell oscillations with the gradient and the flux and summing the
  descendants with weights `3^{3(k-s)/2}`: `C 3^{-H} (E[J_t^±] 𝓛_s^±)^{1/2}`.

The fourth summand on the right is the cutoff pairing term `e4`, bounded by `C W^±`; the
mean-cancellation assertion is exactly that NO further term (the difference between
the inserted means `P^±, Q^±` and the actual annealed means) appears in this decomposition. -/

/-- **Cutoff rows** (`p.response.transfer`; AK.HC (3.45)-(3.54) and (3.46)).  The cutoff
decomposition of the centred response, before Young's inequality: `|Jtilde^±(e)|` is bounded by
the three error rows `e1 + e2 + e3` plus the cutoff pairing term `e4`.

The original formulation of `IsResponseCutoff` was vacuous: it asked a function supported in a
cube of side `3^t` to have mean one while its pullback was only `3⁻ᵗ`-Lipschitz, and such a
function is at most `1 / 2` everywhere.  With the cutoff constant `32 * d ^ 2 * 3 ^ (-t)`,
`exists_isResponseCutoff` above constructs a member of the class, and what remains is the genuine
variational calculation of AK.HC (3.45)-(3.54).

Without the additional integrability hypotheses the theorem is false: three of the
four summands on each right-hand side are Bochner integrals whose integrands have no
sample-uniform bound (`respJ` is an `sSup` over an uncountable admissible class, and a point of
`CoeffSpace d` is only QUALITATIVELY elliptic -- see the collapse diagnostics above), so on a law
where they fail to be `P`-integrable the junk value `0` zeroes every error row and the statement
forces `Jtilde^±(e) = 0`, which the purely algebraic left-hand side does not satisfy.  That
implication is machine-checked above by `hc3_h8c_minus_row_forces_centeredJ_eq_zero`.

The CONCLUSION is unchanged, character for character.  Eight premises are ADDED, all of them
`raw`-derivable at the sole call site `response_cutoff_estimate` (`ResponseCutoffEstimate.lean`),
and every
one of them is discharged there:

| new premise | discharged at the call site from |
|---|---|
| `IsStationaryLaw P` | `raw.stat` |
| `IsUnit (respGrid jStar F)` | `raw.hj`, `raw.symm`, `raw.pos` (the existing `hq`) |
| `(jStar : ℤ) ≤ s` | `raw.hs_lo` **plus** the two range hypotheses `ε ∈ (0, S.eps0]`, `σ ∈ (0,
ε]`, which `response_cutoff_estimate` now carries -- see below |
| the two `Summable (respSourceLoadSummand...)` | `hLB`, i.e. `RespLoadBound`, which now carries
the summability of the source-load family as two further conjuncts.  Without them `respSourceLoad`
is the junk value `0` of a divergent `tsum` and the two cutoff-mean rows assert that the centred
cutoff mean vanishes |
| `HasIntegrableCoarseBlock P (respCell jStar F k)` on `[jStar, t]` |
`Annealed.hasIntegrableCoarseBlock_adapted` from `raw.stat`, `raw.ell`, `raw.hj` |
| `(toFullBlockMat (respMean P jStar F k)).PosDef` on `[jStar, t]` | `Annealed.adaptedMean_posDef`
from the same three fields |
| the four `Integrable (fun a => respJ... u... (respCoeff± F a)) P`, `u ∈ {s, t}` | the
`raw`-consuming lemma `integrable_respJ_respCell` above |
| the two `Integrable (fun a => |cutoffPairingOnCellAux...|) P` | the `raw`-consuming lemma
`integrable_abs_cutoffPairingOnCell` above |

`IsStationaryLaw P` is not decoration.  The mean-cancellation sentence this decomposition rests on
(`p.response.transfer`, "The constant cell means cancel after expectation, BECAUSE the
scale-`s` translations are integral and `(φ)_{U_t} = 1`") is a stationarity argument:
`E[(X)_{z+U_s}]` is independent of the translation `z` only for a stationary law, which in this
checkout is `Annealed.annealedBlock_adaptedCellAtCenter`
(`HCPoly/Entry/Annealed/AnnealedBlockOrder.lean`, whose
hypotheses are exactly `hstat`, `raw.hj` and `(jStar : ℤ) ≤ j` -- hence also the third premise
above).  Without it the `e2` row has no reason to close.

`hjs : jStar ≤ s` is not directly available in `raw` as `raw.hs_lo`: as `respAllScale_window`
(`HCPoly/Entry/Response/Core/EnergyDefectBound.lean`) records, `raw.hs_lo` reads
`jStar + ⌈B log_3(2 + Pi)⌉ ≤ s` and is VACUOUS unless `1 ≤ B`, which comes only from
`SelectionData.one_le_B0`, which is stated only for `ε ∈ (0, S.eps0]` and `σ ∈ (0, ε]`.
`response_cutoff_estimate` did not carry those two ranges.  They have therefore been ADDED to it,
in the same position and with the same names as its siblings
`response_energy_and_defect` and `response_load_and_mean`, and the one
place that applies it (`AdaptedResponseAssembly.lean`, inside `adapted_response_core_of_holes`)
passes the
`hε`/`hσε` it already has in context.  No statement is changed: `adapted_response_core` is
untouched.

**Seven further premises complete the variational calculation.**  The
variational calculation `e1 + e2 + e3` is closed: the energy-defect row `e1` by
`CutoffEnergyDefectRowObligations`, the cutoff-mean rows `e2 + e3` by `CutoffMeanRowCarriers`, and
the assembly by
`CutoffEstimateRowClosure`.  Seven premises are ADDED, all `raw`-derivable at the sole call site
`response_cutoff_estimate` and all discharged there:

| new premise | discharged at the call site from |
|---|---|
| `2 ≤ d` (on the theorem itself) | `_hd` |
| `2 * d ≤ 3 ^ jStar` | `raw.hj` (already used there for `hq`) |
| `(explicitCanonicalMetric F).PosDef` | `Geometry.explicitCanonicalMetric_posDef raw.symm
raw.pos` (already in scope as `hm`) |
| `(toFullBlockMat F).PosDef` | `posDef_toFullBlockMat raw.symm raw.pos` |
| `∃ γ E Ψ Kg Src, CoarseEllipticityDagger P γ E Ψ Kg Src` | `raw.ell` |
| the two `∀ Y, Summable (respSourceLoadSummand … Y)` |
`exists_summable_respSourceLoadSummand_all` (`OptimizerMeanRowCarriers`) from `raw.stat`,
`raw.ell`, `raw.hj`, `raw.hsrc`, `raw.cube`, `raw.hst` and `RespCalibrated` |
| the two `0 ≤ respTau∓` | `RespEnergyDefect` (`hED`), which `response_cutoff_estimate` already
carries |

The `∀ Y` summability is what the `2d` coordinate instantiations of the oscillation half need:
`RespLoadBound` supplies the source-load convergence only at `Y = Y^∓`, and at `Y = (0, δ_i)` the
generation layer is not dominated by the `Y^∓` layer.  Supplying it forced
`response_cutoff_estimate` to EXPORT its own source threshold `Csrc`, in the sibling pattern of
`response_source_load_bound` and `response_weak_estimate`; `AdaptedResponseAssembly` takes the
maximum, so
nothing downstream sees the change.  The conclusion of this theorem is unchanged, character for
character, and `RespCutoffBound` is untouched. -/
theorem abs_respCenteredJ_le_cutoffRows (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
        (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ),
        t = s + (H : ℤ) →
        IsResponseCutoff (respGrid jStar F) t φ →
        -- Every one of the eight premises below is
        -- discharged at the sole call site `response_cutoff_estimate`
        -- (`ResponseCutoffEstimate.lean`); see
        -- the section docstring for the discharge table.
        IsStationaryLaw P →
        IsUnit (respGrid jStar F) →
        (jStar : ℤ) ≤ s →
        -- Seven further premises, all `raw`-derivable at the sole
        -- call site `response_cutoff_estimate` and all discharged there; see the docstring table.
        2 * d ≤ 3 ^ jStar →
        (explicitCanonicalMetric F).PosDef →
        (toFullBlockMat F).PosDef →
        (∃ (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ),
          CoarseEllipticityDagger P γ E Ψ Kg Src) →
        (∀ Y : BlockVec d,
          Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F) Y)) →
        (∀ Y : BlockVec d,
          Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F) Y)) →
        0 ≤ respTauMinus P jStar F s t e →
        0 ≤ respTauPlus P jStar F s t e →
        Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F)
          (respYMinus P jStar F t e)) →
        Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F)
          (respYPlus P jStar F t e)) →
        (∀ k : ℤ, (jStar : ℤ) ≤ k → k ≤ t → HasIntegrableCoarseBlock P (respCell jStar F k)) →
        -- The terminal-optimizer
        -- replacement row compares the terminal cell with EVERY aligned cell of the coarse
        -- scale, so the entrywise integrability of the sample's coarse block is needed at every
        -- aligned translate and not only at the cell through the origin.  Discharged at
        -- `response_cutoff_estimate` by `Annealed.hasIntegrableCoarseBlock_adapted`, whose last
        -- argument is the translate and which the origin discharge already calls at `0`.
        (∀ (k : ℤ) (w : Fin d → ℤ),
          HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w)) →
        (∀ k : ℤ, (jStar : ℤ) ≤ k → k ≤ t →
          (toFullBlockMat (respMean P jStar F k)).PosDef) →
        Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)) P →
        Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)) P →
        Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)) P →
        Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)) P →
        ∀ uM : (a : CoeffSpace d) →
            AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t),
          (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) →
          Integrable (fun a =>
            |cutoffPairingOnCellAux (respCell jStar F t) φ (respYMinus P jStar F t e)
              (respCoeffMinus F a) (uM a)|) P →
        ∀ uP : (a : CoeffSpace d) →
            AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t),
          (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) →
          Integrable (fun a =>
            |cutoffPairingOnCellAux (respCell jStar F t) φ (respYPlus P jStar F t e)
              (respCoeffPlus F a) (uP a)|) P →
        |respCenteredJMinus P jStar F t e| ≤
              C * (respTauMinus P jStar F s t e +
                  Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
                  (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) +
                C * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) +
                C * ((3 : ℝ) ^ (-(H : ℝ)) *
                  Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) +
                (∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ (respYMinus P jStar F t e)
                  (respCoeffMinus F a) (uM a)| ∂P) ∧
          |respCenteredJPlus P jStar F t e| ≤
              C * (respTauPlus P jStar F s t e +
                  Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
                  (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) +
                C * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) +
                C * ((3 : ℝ) ^ (-(H : ℝ)) *
                  Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) +
                (∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ (respYPlus P jStar F t e)
                  (respCoeffPlus F a) (uP a)| ∂P) := by
  classical
  refine ⟨max (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      (max 1 (respCutoffOscConst d)), ?_, ?_⟩
  · have h3 : (3 : ℝ) ≤ max (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
        (max 1 (respCutoffOscConst d)) := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith only [h3]
  intro P _ jStar F H s t e φ ht hφ hstat hq hjs hjStar hm hF hdagE hsummM hsummP hτM hτP
    _hsumM0 _hsumP0 hblkk hblkw _hpd hJMt hJMs hJPt hJPs uM hmaxM hpairM uP hmaxP hpairP
  obtain ⟨γ, E, Ψ, Kg, Src, hdag⟩ := hdagE
  have hjt : (jStar : ℤ) ≤ t := by omega
  have hblkt : HasIntegrableCoarseBlock P (respCell jStar F t) := hblkk t hjt le_rfl
  have hφc : Continuous φ := hφ.2.2.2.2.2.1.continuous
  have hUm : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hφint : IntegrableOn φ (respCell jStar F t) := by
    have h := integrableOn_isResponseCutoff hq hφ t 0
    rw [adaptedCellAtCenter_zero] at h
    exact h
  have hφb : ∀ x : Vec d, ‖φ x‖ ≤ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.1 x)]
    exact hφ.2.1 x
  have hEJM : 0 ≤ respEJMinus P jStar F t e := zero_le_respEJMinus P jStar F t e hq
  have hEJP : 0 ≤ respEJPlus P jStar F t e := zero_le_respEJPlus P jStar F t e hq
  have hEintM : ∀ a : CoeffSpace d, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) (respCell jStar F t) :=
    fun a => integrableOn_energy_respCell_respCoeffMinus jStar hjStar F hm t uM a
  have hEintP : ∀ a : CoeffSpace d, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) (respCell jStar F t) :=
    fun a => integrableOn_energy_respCell_respCoeffPlus jStar hjStar F hm t uP a
  have hptM : ∀ (a : CoeffSpace d) (x : Vec d),
      vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
          (optimizerField (respCoeffMinus F a) (uM a) x).2
        = scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x := by
    intro a x
    simp only [scalarVariationEnergyIntegrand, optimizerField]
    exact (vecDot_matVecMul_symmPart (respCoeffMinus F a x) ((uM a).toH1.grad x)).symm
  have hptP : ∀ (a : CoeffSpace d) (x : Vec d),
      vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
          (optimizerField (respCoeffPlus F a) (uP a) x).2
        = scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x := by
    intro a x
    simp only [scalarVariationEnergyIntegrand, optimizerField]
    exact (vecDot_matVecMul_symmPart (respCoeffPlus F a x) ((uP a).toH1.grad x)).symm
  have hEcellM : ∀ a : CoeffSpace d, IntegrableOn (fun x => φ x *
      vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
        (optimizerField (respCoeffMinus F a) (uM a) x).2) (respCell jStar F t) := by
    intro a
    refine ((hEintM a).bdd_mul (c := 2) hφc.measurable.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall hφb)).congr (Filter.Eventually.of_forall fun x => ?_)
    change φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x
      = φ x * vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
          (optimizerField (respCoeffMinus F a) (uM a) x).2
    rw [hptM a x]
  have hEcellP : ∀ a : CoeffSpace d, IntegrableOn (fun x => φ x *
      vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
        (optimizerField (respCoeffPlus F a) (uP a) x).2) (respCell jStar F t) := by
    intro a
    refine ((hEintP a).bdd_mul (c := 2) hφc.measurable.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall hφb)).congr (Filter.Eventually.of_forall fun x => ?_)
    change φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x
      = φ x * vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
          (optimizerField (respCoeffPlus F a) (uP a) x).2
    rw [hptP a x]
  obtain ⟨-, -, -, -, hM1M, hM2M, -, -⟩ :=
    integrable_cutoffMeanDefect_coords_respCoeffMinus hd P hstat γ E Ψ Kg Src hdag jStar hjStar
      F hm H s t ht hjs e φ hφ uM hmaxM hEintM hJMt hsummM
  obtain ⟨-, -, -, -, hM1P, hM2P, -, -⟩ :=
    integrable_cutoffMeanDefect_coords_respCoeffPlus hd P hstat γ E Ψ Kg Src hdag jStar hjStar
      F hm H s t ht hjs e φ hφ uP hmaxP hEintP hJPt hsummP
  have hrow1M := cutoffEnergyDefectRowMinus_of_carriers_clean P hstat jStar hjStar F hm H s t ht
    hjs e φ hφ uM hmaxM hblkw hJMt hJMs
  have hrow1P := cutoffEnergyDefectRowPlus_of_carriers_clean P hstat jStar hjStar F hm H s t ht
    hjs e φ hφ uP hmaxP hblkw hJPt hJPs
  have hrow2M := cutoffMeanRowMinus_of_carriers hd P hstat γ E Ψ Kg Src hdag jStar hjStar F hm hF
    H s t ht hjs e φ hφ uM hmaxM hblkw hblkt hJMt hJMs hsummM hτM
  have hrow2P := cutoffMeanRowPlus_of_carriers hd P hstat γ E Ψ Kg Src hdag jStar hjStar F hm hF
    H s t ht hjs e φ hφ uP hmaxP hblkw hblkt hJPt hJPs hsummP hτP
  refine ⟨?_, ?_⟩
  · exact abs_respCenteredJMinus_le_cutoffRows_of_obligations P jStar F t e φ uM hq hblkt hJMt
      (integrable_half_cutoffPairingOnCell_respCoeffMinus P jStar F t hjStar hm φ hφ
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (respYMinus P jStar F t e) uM hmaxM hpairM)
      (integrable_cutoffHalfEnergyAux_sub_respJ_respCoeffMinus P jStar hjStar F hm t e φ hφ uM
        hmaxM hJMt)
      hM1M hM2M hφ hφint hEcellM
      (fun a i => (integrableOn_weighted_optimizerField_respCell_respCoeffMinus jStar hjStar F hm
        t uM hUm (fun x hx => hx) hφc a i).1)
      (fun a i => (integrableOn_weighted_optimizerField_respCell_respCoeffMinus jStar hjStar F hm
        t uM hUm (fun x hx => hx) hφc a i).2)
      (max (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
        (max 1 (respCutoffOscConst d))) H s
      (cutoffEnergyDefectRowMinus_mono P jStar F H s t e φ uM hτM hEJM
        (le_max_left _ _) hrow1M)
      (cutoffMeanRowMinus_mono P jStar F H s t e φ uM (le_max_right _ _) hrow2M)
  · exact abs_respCenteredJPlus_le_cutoffRows_of_obligations P jStar F t e φ uP hq hblkt hJPt
      (integrable_half_cutoffPairingOnCell_respCoeffPlus P jStar F t hjStar hm φ hφ
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (respYPlus P jStar F t e) uP hmaxP hpairP)
      (integrable_cutoffHalfEnergyAux_sub_respJ_respCoeffPlus P jStar hjStar F hm t e φ hφ uP
        hmaxP hJPt)
      hM1P hM2P hφ hφint hEcellP
      (fun a i => (integrableOn_weighted_optimizerField_respCell_respCoeffPlus jStar hjStar F hm
        t uP hUm (fun x hx => hx) hφc a i).1)
      (fun a i => (integrableOn_weighted_optimizerField_respCell_respCoeffPlus jStar hjStar F hm
        t uP hUm (fun x hx => hx) hφc a i).2)
      (max (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
        (max 1 (respCutoffOscConst d))) H s
      (cutoffEnergyDefectRowPlus_mono P jStar F H s t e φ uP hτP hEJP
        (le_max_left _ _) hrow1P)
      (cutoffMeanRowPlus_mono P jStar F H s t e φ uP (le_max_right _ _) hrow2P)

/-! ## The final combination of the cutoff rows and the weak pairing.

The two branches combine the primal and adjoint rows of the cutoff decomposition against the
weak quantity under one common constant.  The conclusion is LITERALLY `RespCutoffBound`
(`CenteredEnergyIdentity.lean`), i.e. exactly the payload of `response_cutoff_estimate`
(`ResponseCutoffEstimate.lean`). -/

omit [NeZero d] in
/-- **Cutoff bound from the rows and the weak pairing** (`p.response.transfer`,
`e.response.cutoff.estimate`).  The three error rows of the cutoff decomposition plus the bound
on the cutoff pairing term combine, under the common constant `max C₁ C₂`, into
`RespCutoffBound`.

`eM`/`eP` stand for the two expected cutoff pairing terms `e4^∓`, so that `hrowsMinus`/`hrowsPlus`
are the cutoff-row conclusions and `hweakMinus`/`hweakPlus` the weak-pairing conclusions.  The
nonnegativity hypotheses are the ones needed to collect the rows under a single constant; each is
available in the calling context (`RespLoadBound` `CenteredEnergyIdentity.lean` and `RespWeakBound`
 already assert nonnegativity of `𝓛_s^±` and of `W^±`). -/
theorem respCutoffBound_of_cutoffRows_of_weakPairing
    (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d)
    (eM eP : ℝ)
    (hτM : 0 ≤ respTauMinus P jStar F s t e) (hτP : 0 ≤ respTauPlus P jStar F s t e)
    (hEJM : 0 ≤ respEJMinus P jStar F t e) (hEJP : 0 ≤ respEJPlus P jStar F t e)
    (hLM : 0 ≤ respLsMinus P jStar F s t e) (hLP : 0 ≤ respLsPlus P jStar F s t e)
    (hWM : 0 ≤ respWMinus P jStar F t e) (hWP : 0 ≤ respWPlus P jStar F t e)
    (hrowsMinus : |respCenteredJMinus P jStar F t e| ≤
      C₁ * (respTauMinus P jStar F s t e +
          Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
          (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) +
        C₁ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) +
        C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) + eM)
    (hrowsPlus : |respCenteredJPlus P jStar F t e| ≤
      C₁ * (respTauPlus P jStar F s t e +
          Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
          (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) +
        C₁ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) +
        C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) + eP)
    (hweakMinus : eM ≤ C₂ * respWMinus P jStar F t e)
    (hweakPlus : eP ≤ C₂ * respWPlus P jStar F t e) :
    RespCutoffBound (max C₁ C₂) P jStar F H s t e := by
  -- The first four `have` statements are no-op uses of the binders the `unusedVariables` linter
  -- flags; the two strict positivities are part of the contract with `response_cutoff_estimate`
  -- but only `le_max_left`/`le_max_right` are needed below.
  have _ := hC₁
  have _ := hC₂
  have _ := hLM
  have _ := hLP
  have hle1 : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hle2 : C₂ ≤ max C₁ C₂ := le_max_right _ _
  have hp : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
  refine ⟨?_, ?_⟩
  · -- Minus row.
    have expand1 :
        C₁ * (respTauMinus P jStar F s t e +
            Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) +
          C₁ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) +
          C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) + eM
        = C₁ * respTauMinus P jStar F s t e
            + C₁ * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + C₁ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e)
            + C₁ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)
            + C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
                Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))
            + eM := by ring
    rw [expand1] at hrowsMinus
    have expand2 :
        max C₁ C₂ * (respTauMinus P jStar F s t e +
            Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
            Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * (respEJMinus P jStar F t e +
              Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) +
            respWMinus P jStar F t e)
        = max C₁ C₂ * respTauMinus P jStar F s t e
            + max C₁ C₂ * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e)
            + max C₁ C₂ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)
            + max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
                Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))
            + max C₁ C₂ * respWMinus P jStar F t e := by ring
    rw [expand2]
    have i1 : C₁ * respTauMinus P jStar F s t e ≤ max C₁ C₂ * respTauMinus P jStar F s t e :=
      mul_le_mul_of_nonneg_right hle1 hτM
    have i2 : C₁ * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) ≤
        max C₁ C₂ * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) :=
      mul_le_mul_of_nonneg_right hle1 (Real.sqrt_nonneg _)
    have i3 : C₁ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) ≤
        max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) :=
      mul_le_mul_of_nonneg_right hle1 (mul_nonneg hp hEJM)
    have i4 : C₁ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) ≤
        max C₁ C₂ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) :=
      mul_le_mul_of_nonneg_right hle1 (Real.sqrt_nonneg _)
    have i5 : C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) ≤
        max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) :=
      mul_le_mul_of_nonneg_right hle1 (mul_nonneg hp (Real.sqrt_nonneg _))
    have i6 : eM ≤ max C₁ C₂ * respWMinus P jStar F t e := by
      have h := mul_le_mul_of_nonneg_right hle2 hWM
      linarith only [hweakMinus, h]
    linarith only [hrowsMinus, i1, i2, i3, i4, i5, i6]
  · -- Plus row, symmetric.
    have expand1 :
        C₁ * (respTauPlus P jStar F s t e +
            Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) +
          C₁ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) +
          C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) + eP
        = C₁ * respTauPlus P jStar F s t e
            + C₁ * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
            + C₁ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e)
            + C₁ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)
            + C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
                Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))
            + eP := by ring
    rw [expand1] at hrowsPlus
    have expand2 :
        max C₁ C₂ * (respTauPlus P jStar F s t e +
            Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
            Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * (respEJPlus P jStar F t e +
              Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) +
            respWPlus P jStar F t e)
        = max C₁ C₂ * respTauPlus P jStar F s t e
            + max C₁ C₂ * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
            + max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e)
            + max C₁ C₂ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)
            + max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
                Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))
            + max C₁ C₂ * respWPlus P jStar F t e := by ring
    rw [expand2]
    have i1 : C₁ * respTauPlus P jStar F s t e ≤ max C₁ C₂ * respTauPlus P jStar F s t e :=
      mul_le_mul_of_nonneg_right hle1 hτP
    have i2 : C₁ * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) ≤
        max C₁ C₂ * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) :=
      mul_le_mul_of_nonneg_right hle1 (Real.sqrt_nonneg _)
    have i3 : C₁ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) ≤
        max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) :=
      mul_le_mul_of_nonneg_right hle1 (mul_nonneg hp hEJP)
    have i4 : C₁ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) ≤
        max C₁ C₂ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) :=
      mul_le_mul_of_nonneg_right hle1 (Real.sqrt_nonneg _)
    have i5 : C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) ≤
        max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) :=
      mul_le_mul_of_nonneg_right hle1 (mul_nonneg hp (Real.sqrt_nonneg _))
    have i6 : eP ≤ max C₁ C₂ * respWPlus P jStar F t e := by
      have h := mul_le_mul_of_nonneg_right hle2 hWP
      linarith only [hweakPlus, h]
    linarith only [hrowsPlus, i1, i2, i3, i4, i5, i6]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff estimate

The cutoff estimate `e.response.cutoff.estimate`, one part of the proof of
`adapted_response_core`.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  aspectRatio)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-! ## The cutoff estimate -/

/-- **The cutoff estimate** (`e.response.cutoff.estimate`):
`|Jtilde^±(e)| <= C(tau^± + (tau^± E[J_t^±])^{1/2} + (tau^± L_s^±)^{1/2}
  + 3^{-H}(E[J_t^±] + (E[J_t^±] L_s^±)^{1/2}) + W^±)`.

-- KERNEL.  This is the second true analytic kernel: the variational calculation of
`\cite[(3.45)--(3.54)]{AK.HC}` before Young's inequality, with `\cite[(3.46)]{AK.HC}` and
`\cite[Lemma A.1, (A.4)]{AK.HC}`, is never reproved in the paper.

Route (`p.response.transfer`): choose a cutoff `phi` of the class `IsResponseCutoff`.  The
cutoff compares the terminal optimizer with its scale-`s` cell optimizers, and the
quadratic-response identity measures the mean energy of their difference by `2 tau^±`.  Insert
`P^±, Q^±` into the cutoff decomposition; the term containing the difference between these
means and the actual annealed means is zero.  Integration by parts and the direct
full-dual pairing give
`E[|avg_{U_t} phi (grad v - P).(a grad v - Q)|] <= C W^±`.  The rounded/unrounded
metric comparison costs only a dimensional constant, since
`|m^{-1/2}q||q^{-1}m^{1/2}| <= 3`.  Keeping the last product is essential.

The proof combines the pieces of the variational calculation:
`exists_isResponseCutoff` (`HCPoly/Entry/Response/Cutoff/ResponseCutoffExistence.lean`) discharges
the
choice of cutoff at `p.response.transfer`, the maximizer-existence lemmas supply the two maximizer
families, the cutoff-rows estimate gives the three error rows, the weak-pairing estimate gives
the cutoff pairing term, and the two are collected under `max C₁ C₂`.  The invertibility of the
selected grid comes from `RawOutput.hj/symm/pos`, and `0 ≤ W^±` from the weak-pairing estimate
itself (its left-hand side is an integral of absolute values).

The proof invokes `abs_respCenteredJ_le_cutoffRows`,
`integral_abs_cutoffPairingOnCell_le_respWeak`, and the two `raw`-consuming integrability
lemmas `integrable_besovSeminorm_sq_respCell` and `integrable_abs_cutoffPairingOnCell`.  The
theorem is axiom-clean.

It exports its own source threshold `Csrc`, in the same pattern as
`response_source_load_bound` and `response_weak_estimate`.  Two inputs need one: the
measurability and `L^Q(P)`-integrability of the all-scale maximum, which the two
`raw`-consuming lemmas consume, and the convergence of the source-load series at every dual
vector, which the `2d` coordinate readouts need and which is a theorem of
`annealedBlock_le_adaptedMean`, whose threshold on `j_*` is not implied by an arbitrary
`Csrc`.  The exported threshold is the maximum of the two.  `AdaptedResponseAssembly` in turn
takes the
maximum of the thresholds exported by the inputs it combines, so the interface seen by consumers
is unchanged; the extra binder `0 ≤ Cglob` matches `response_source_load_bound`'s. -/
theorem response_cutoff_estimate (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (_hS : S.Selects d γ) (Cc Ce Cl Cld : ℝ) (_hCc : 0 < Cc)
    (_hCe : 0 < Ce) (_hCl : 0 < Cl) (_hCld : 0 < Cld) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (ε σ : ℝ) (_hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (_hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
        (Cglob Cprof Bresp : ℝ) (_hCglob : 0 ≤ Cglob) (H : ℕ) (P : Measure (CoeffSpace d))
        (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ)
        (F : BlockMat d) (s t : ℤ),
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        RespCalibrated Cc P jStar F s t →
        ∀ e : Vec d, vecDot e e = 1 →
          RespEnergyDefect Ce P jStar F s t e →
          RespLoadMean Cl P jStar F s t e →
          RespLoadBound Cld P jStar F s t e →
          RespCutoffBound C P jStar F H s t e := by
  classical
  have : NeZero d := ⟨by omega⟩
  -- Two source thresholds are exported by the inputs this proof consumes: `CsrcM`, above which
  -- the all-scale maximum is measurable and `L^Q(P)`-integrable, and `Csrc0`, above which the
  -- source-load series converges at every dual vector.  This theorem exports their maximum;
  -- `AdaptedResponseAssembly` takes the maximum of the exported thresholds, and
  -- `RawOutput.of_le_csrc` lowers `raw` to each.
  obtain ⟨CsrcM, hCsrcM, hMdata⟩ :=
    respAllScaleMax_aestronglyMeasurable_integrable d _hd γ _hγ S _hS
  obtain ⟨Csrc0, hCsrc0, hloadAllY⟩ := exists_summable_respSourceLoadSummand_all d _hd γ _hγ
  obtain ⟨C₁, hC₁, h8c⟩ := abs_respCenteredJ_le_cutoffRows d _hd
  obtain ⟨C₂, hC₂, h8b⟩ := integral_abs_cutoffPairingOnCell_le_respWeak d
  refine ⟨max CsrcM Csrc0, lt_of_lt_of_le hCsrcM (le_max_left _ _), max C₁ C₂,
    lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src Bb jStar F s t raw hcal e _he hED
    _hLMean hLB
  -- The all-scale maximum of `p.response.transfer` is measurable and lies in
  -- `L^Q(P)`; this is the input the weak-quantity integrability consumes.
  obtain ⟨hMmeas, hMint⟩ := hMdata ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src Bb jStar F
    s t (RawOutput.of_le_csrc raw (le_max_left _ _))
  have := raw.prob
  -- The selected grid is invertible (`RawOutput.hj`, `RawOutput.symm`, `RawOutput.pos`).
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
    raw.symm raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid raw.hj hm
  -- The weak-pairing estimate carries `2 * d ≤ 3 ^ jStar`, without which the selected grid
  -- need not be invertible and the change of variables `x = q y` of `p.response.transfer` is
  -- unavailable at any constant.  It is discharged here by `raw.hj`, the very hypothesis that
  -- already supplies `hq` on the line above.
  have hjStar : 2 * d ≤ 3 ^ jStar := raw.hj
  -- A cutoff of the class exists: the ``p.response.transfer`` choice, discharged by
  -- `exists_isResponseCutoff`.
  obtain ⟨φ, hφ⟩ := exists_isResponseCutoff hq t
  -- Maximizer families for both signs.
  have hMne : ∀ a : CoeffSpace d,
      Nonempty (ScalarCanonicalMaximizer (respCell jStar F t)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a)) :=
    fun a => nonempty_scalarCanonicalMaximizer_respCoeffMinus (respGrid jStar F) hq t F a _ _
  have hPne : ∀ a : CoeffSpace d,
      Nonempty (ScalarCanonicalMaximizer (respCell jStar F t)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)) :=
    fun a => nonempty_scalarCanonicalMaximizer_respCoeffPlus (respGrid jStar F) hq t F a _ _
  set uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t) :=
    fun a => (hMne a).some.toAHarmonicFunctionMeanZero.toAHarmonicFunction with huMdef
  set uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t) :=
    fun a => (hPne a).some.toAHarmonicFunctionMeanZero.toAHarmonicFunction with huPdef
  have huM : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a) :=
    fun a => (hMne a).some.isResponseMaximizer
  have huP : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a) :=
    fun a => (hPne a).some.isResponseMaximizer
  -- The weak-pairing estimate carries, once per sign, the integrability of the Besov square
  -- of the family whose cutoff pairing it bounds -- without it `W^±` collapses to the Bochner
  -- junk value `0` and the estimate is false.  Nothing in this theorem's own premises discharges
  -- it, so it is supplied by `integrable_besovSeminorm_sq_respCell`, whose statement consumes
  -- exactly `raw`.
  have hiM := integrable_besovSeminorm_sq_respCell d _hd γ S ε σ Cglob Cprof (max CsrcM Csrc0)
    Bresp H P E Ψ Kg Src Bb jStar F s t raw hMmeas hMint (respCoeffMinus F) (Or.inl rfl)
    (respP (respMean P jStar F t) e)
    (respqMinus P jStar F t e) (respYMinus P jStar F t e) uM huM
  have hiP := integrable_besovSeminorm_sq_respCell d _hd γ S ε σ Cglob Cprof (max CsrcM Csrc0)
    Bresp H P E Ψ Kg Src Bb jStar F s t raw hMmeas hMint (respCoeffPlus F) (Or.inr rfl)
    (respP (respMean P jStar F t) e)
    (respqPlus P jStar F t e) (respYPlus P jStar F t e) uP huP
  -- The cutoff-rows estimate carries `raw`-derivable premises.  Its eight premises are
  -- discharged here, in the order they appear in its statement.
  --
  -- (1) stationarity of the law -- load-bearing for the `e2` mean cancellation of
  -- `p.response.transfer` ("the scale-`s` translations are integral"), which is a
  -- stationarity argument: `E[(X)_{z+U_s}]` is independent of `z` only for a stationary law.
  have hstat : IsStationaryLaw P := raw.stat
  -- (2) invertibility of the selected grid is `hq`, already in hand above.
  -- (3) the response window lies above `j_*`.  `raw.hs_lo` places `s` at least
  -- `B log_3(2 + Pi)` generations above `j_*`; it is USABLE only with `1 <= B`, which needs
  -- `S.one_le_B0 ε σ hε hσ`, i.e. the two range hypotheses this theorem now carries (same
  -- pattern, same placement, as its siblings `response_energy_and_defect`
  -- (`HCPoly/Entry/Response/Core/EnergyDefectBound.lean`) and `response_load_and_mean`
  -- (`HCPoly/Entry/Response/Core/LoadMeanIdentity.lean`)).  See `respAllScale_window`
  -- (`HCPoly/Entry/Response/Core/EnergyDefectBound.lean`) for the same derivation.
  have hjs : (jStar : ℤ) ≤ s := by
    have hB : (1 : ℝ) ≤ Bb :=
      le_trans (S.one_le_B0 ε σ hε hσ) (le_trans (le_max_left _ _) raw.hB)
    have hA : (1 : ℝ) ≤ aspectRatio E :=
      HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger raw.ell
    have h3 : (3 : ℝ) ≤ 2 + aspectRatio E := by linarith only [hA]
    have hlog : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := by
      have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      have h2 : Real.log 3 ≤ Real.log (2 + aspectRatio E) := Real.log_le_log (by norm_num) h3
      rw [Real.logb, le_div_iff₀ hl3]
      linarith only [h2]
    have hpos : (0 : ℝ) < Bb * Real.logb 3 (2 + aspectRatio E) :=
      mul_pos (by linarith only [hB]) (by linarith only [hlog])
    have hceil : (0 : ℤ) < ⌈Bb * Real.logb 3 (2 + aspectRatio E)⌉ :=
      Int.lt_ceil.mpr (by exact_mod_cast hpos)
    have h1 := raw.hs_lo
    omega
  -- (4)/(5) entrywise integrability and positive-definiteness of the annealed block at every
  -- scale of the window, from `raw.stat`/`raw.ell`/`raw.hj` and `hm`
  -- (`Annealed.hasIntegrableCoarseBlock_adapted`, `Annealed.adaptedMean_posDef`).  Both hold at
  -- EVERY scale, so the `[j_*, t]` restriction of the cutoff-rows estimate's premises is
  -- discharged a fortiori.
  have hblk : ∀ k : ℤ, (jStar : ℤ) ≤ k → k ≤ t →
      HasIntegrableCoarseBlock P (respCell jStar F k) := by
    intro k _ _
    simpa only [respCell, respGrid, HighContrast.adaptedCellTranslate, zero_add, Set.image_id']
      using
      Annealed.hasIntegrableCoarseBlock_adapted d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
        (explicitCanonicalMetric F) hm k 0
  have hblkw : ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w) := by
    intro k w
    simpa only [respGrid, adaptedCellAtCenter] using
      Annealed.hasIntegrableCoarseBlock_adapted d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
        (explicitCanonicalMetric F) hm k (adaptedCellCenter (respGrid jStar F) k w)
  have hpd : ∀ k : ℤ, (jStar : ℤ) ≤ k → k ≤ t →
      (toFullBlockMat (respMean P jStar F k)).PosDef := by
    intro k _ _
    simpa only [respMean, respGrid] using
      Annealed.adaptedMean_posDef d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
        (explicitCanonicalMetric F) hm k
  -- (6) the four pathwise-response integrabilities, and (7)/(8) the two cutoff-pairing
  -- integrabilities.  These parallel the Besov-square integrability carried by the
  -- weak-pairing estimate: they are supplied by `integrable_respJ_respCell` and
  -- `integrable_abs_cutoffPairingOnCell`, whose statements consume exactly `raw`.
  have hjM : ∀ u : ℤ, (jStar : ℤ) ≤ u → u ≤ t →
      Integrable (fun a => respJ (respGrid jStar F) u (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P :=
    fun u hlo hhi => integrable_respJ_respCell d γ S ε σ Cglob Cprof (max CsrcM Csrc0) Bresp H P
      E Ψ Kg Src Bb jStar F s t raw (respCoeffMinus F) (Or.inl rfl) u hlo hhi _ _
  have hjP : ∀ u : ℤ, (jStar : ℤ) ≤ u → u ≤ t →
      Integrable (fun a => respJ (respGrid jStar F) u (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P :=
    fun u hlo hhi => integrable_respJ_respCell d γ S ε σ Cglob Cprof (max CsrcM Csrc0) Bresp H P
      E Ψ Kg Src Bb jStar F s t raw (respCoeffPlus F) (Or.inr rfl) u hlo hhi _ _
  have hst : s ≤ t := raw.hst.le
  have hpairM := integrable_abs_cutoffPairingOnCell d _hd γ S ε σ Cglob Cprof (max CsrcM Csrc0)
    Bresp H P E Ψ Kg Src Bb jStar F s t raw hMmeas hMint (respCoeffMinus F) (Or.inl rfl) φ hφ
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respYMinus P jStar F t e) uM huM
  have hpairP := integrable_abs_cutoffPairingOnCell d _hd γ S ε σ Cglob Cprof (max CsrcM Csrc0)
    Bresp H P E Ψ Kg Src Bb jStar F s t raw hMmeas hMint (respCoeffPlus F) (Or.inr rfl) φ hφ
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respYPlus P jStar F t e) uP huP
  -- The weak-pairing estimate and the cutoff-rows estimate on that cutoff and those families.
  obtain ⟨hbM, hbP⟩ := h8b P jStar F t e φ hjStar hφ uM huM hiM uP huP hiP
  -- The cutoff-rows estimate carries seven further premises, all `raw`-derivable here.
  -- The rounded grid is invertible from `raw.hj`/`raw.symm`/`raw.pos`; the flattened reference
  -- block is positive definite by `posDef_toFullBlockMat`; the coarse ellipticity of
  -- the law is `raw.ell`; the two scale defects are nonnegative by `RespEnergyDefect`; and the
  -- source-load series converges at EVERY dual vector -- not only at the annealed means `Y^∓`
  -- of `RespLoadBound` -- by `exists_summable_respSourceLoadSummand_all`, whose own source
  -- threshold `Csrc0` this theorem exports in the same pattern as `response_source_load_bound`
  -- and `response_weak_estimate`.
  have hFfull : (toFullBlockMat F).PosDef :=
    posDef_toFullBlockMat raw.symm raw.pos
  have hKg : (1 : ℝ) < Kg := raw.ell.one_lt_growthWitness
  have hlogK : (0 : ℝ) ≤ Real.logb 3 (2 * Kg) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hKg])
  have hB1 : (1 : ℝ) ≤ Bb :=
    le_trans (S.one_le_B0 ε σ hε hσ) (le_trans (le_max_left _ _) raw.hB)
  have hPi := Annealed.aspectRatio_pos_and_three_le raw.ell
  have hlogPi : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := by
    refine (Real.le_logb_iff_rpow_le (by norm_num) (by linarith only [hPi.2])).mpr ?_
    rw [Real.rpow_one]
    linarith only [hPi.2]
  have hthr : ⌈Csrc0 * Real.logb 3 (2 * Kg)⌉ ≤ (jStar : ℤ) := by
    refine le_trans (Int.ceil_le_ceil ?_) raw.hsrc
    have h0 : (0 : ℝ) ≤ Cglob * (Bb + 1) * Real.logb 3 (2 + aspectRatio E) :=
      mul_nonneg (mul_nonneg hCglob (by linarith only [hB1])) (by linarith only [hlogPi])
    have hmax : Csrc0 * Real.logb 3 (2 * Kg) ≤ max CsrcM Csrc0 * Real.logb 3 (2 * Kg) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hlogK
    linarith only [hmax, h0]
  have hwin : HighContrast.adaptedCell (respGrid jStar F) s ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)) :=
    subset_trans (adaptedCell_subset (respGrid jStar F) (le_of_lt raw.hst)) raw.cube
  have hcM0 : (0 : ℝ) ≤ Cc * Real.sqrt (respKappa P jStar F s) :=
    mul_nonneg _hCc.le (Real.sqrt_nonneg _)
  have hloadY := hloadAllY P E Ψ Kg Src raw.stat raw.ell jStar raw.hj hthr F hFfull hm s hjs
    hwin (Cc * Real.sqrt (respKappa P jStar F s)) hcM0 hcal.2.2.2.2.1 hcal.2.2.2.2.2
  obtain ⟨hcM, hcP⟩ := h8c P jStar F H s t e φ raw.ht hφ hstat hq hjs
    hjStar hm hFfull ⟨γ, E, Ψ, Kg, Src, raw.ell⟩
    (fun Y => (hloadY Y).1) (fun Y => (hloadY Y).2)
    hED.2.2.2.2.2.2.1 hED.2.2.2.2.2.2.2.1
    hLB.2.2.2.2.1 hLB.2.2.2.2.2 hblk hblkw hpd
    (hjM t (hjs.trans hst) le_rfl) (hjM s hjs hst) (hjP t (hjs.trans hst) le_rfl)
    (hjP s hjs hst) uM huM hpairM uP huP hpairP
  -- `W^± ≥ 0`: the cutoff pairing term is an integral of absolute values, so the weak-pairing
  -- estimate forces it.
  have hWM : 0 ≤ respWMinus P jStar F t e := by
    have h0 : (0 : ℝ) ≤
        ∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ (respYMinus P jStar F t e)
          (respCoeffMinus F a) (uM a)| ∂P :=
      integral_nonneg fun a => abs_nonneg _
    exact nonneg_of_mul_nonneg_right (h0.trans hbM) hC₂
  have hWP : 0 ≤ respWPlus P jStar F t e := by
    have h0 : (0 : ℝ) ≤
        ∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ (respYPlus P jStar F t e)
          (respCoeffPlus F a) (uP a)| ∂P :=
      integral_nonneg fun a => abs_nonneg _
    exact nonneg_of_mul_nonneg_right (h0.trans hbP) hC₂
  -- The final assembly collects the four rows under the single constant `max C₁ C₂`.
  exact respCutoffBound_of_cutoffRows_of_weakPairing C₁ C₂ hC₁ hC₂ P jStar F H s t e _ _
    hED.2.2.2.2.2.2.1 hED.2.2.2.2.2.2.2.1 hED.1 hED.2.1 hLB.1 hLB.2.1 hWM hWP hcM hcP hbM hbP

end HCPolySupport.HighContrast.Multiscale
end
