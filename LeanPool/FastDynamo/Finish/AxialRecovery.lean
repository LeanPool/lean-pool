/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.TransverseWeightedDiffusion
public import LeanPool.FastDynamo.Finish.AxialRecoveryRegularity
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `lem:axial-recovery`: recovery of the axial magnetic component

Third of the three modules proving `lem:axial-recovery` (Lemma 8.1).

Let `ε > 0`, `K ∈ ℤ \ {0}`, let `u` be a divergence-free `x₃`-independent `W^{1,∞}` velocity and
let `0 ≠ h ∈ H²(T²;ℂ²)` satisfy `A_{ε,K} h = λ h` (`eq:torus-sector`).  Setting

`b₃ = -Div⊥h/(2πiK)`,  `b = (h, b₃)`,  `V(y, x₃) = e^{2πiKx₃} b(y)`   (statement of
`lem:axial-recovery`)

the paper proves `b ∈ H²(T²;ℂ³)`, `0 ≠ V ∈ H²(T³;ℂ³) ∩ L²_σ(T³)` and `L_{ε,u}V = λV`.

**Statement and proof route.**  The statement is the paper's, read through the axial-sector
reduction: the Lean conclusion (`exists_reducedInductionEigenpair_of_horizontalEigenpair`) is
that `b` is an eigenvector of the three-component reduced operator on `T²` and that
`V = e^{2πiKx₃}b` is solenoidal; the passage to `L_{ε,u}V = λV` on `T³` is made downstream.
The *proof* is not the paper's: the paper argues on `V` itself (proof of `lem:axial-recovery`).
It puts `F := λV − εΔV − curl(u×V) ∈ H⁻¹(T³;ℂ³)`, gets `F⊥ = 0` from the horizontal eigenvalue
equation, notes `Div F = 0` and that every term of `F` has axial index `K`, so that
`0 = Div F = ∂_{x₃}F₃ = 2πiK F₃` in distributions and hence `F = 0`; then
`εΔV = λV − curl(u×V) ∈ L²` and elliptic regularity give `V ∈ H²` in one step.

This development follows a different route: a scalar equation for `b₃` alone, then elliptic
regularity for `b₃`.  The conclusion is the same; the two displays this route uses are not
labels of the paper, so the names below carry them:

* *the recovered axial equation* `(λ − S)b₃ = (h·∇⊥)u₃` with
  `S = ε(Δ⊥ − (2πK)²) − u⊥·∇⊥ − 2πiK u₃` (the paper has no such display);
* *the transport–stretching divergence identity*
  `Div[-(w·∇)F + (F·∇)w] = -w·∇ Div F`.  The paper states only the underlying
  distributional curl identity `curl(u×V) = (V·∇)u − (u·∇)V` (proof of `lem:axial-recovery`).

With that reading the three steps are:

1. The recovered axial equation is obtained by taking the sector divergence of
   `A_{ε,K}h = λh`.  The transport and stretching terms are handled together through the curl
   identity, in the sector form proved in
   `FastDynamo/Finish/AxialRecoveryDivergence.lean`; the extra term
   `Div⊥(u₃h) = u₃ Div⊥h + h·∇⊥u₃` is the weak Leibniz rule, and
   `Div⊥u⊥ = 0` removes the diagonal velocity-gradient term.  Frequency by frequency this is
   `axialRecoveredComponent_coeff_equation`.
2. The regularity upgrade of `b₃` from `H¹` to `H²` by periodic elliptic regularity
   is, in the Fourier-graph model, the observation that the right-hand side of the
   recovered axial equation is an `L²` field while the symbol
   `ε(4π²|n|² + (2πK)²)` is bounded below by `ε(1 + 4π²|n|²)` when `K ≠ 0`.  The weighted
   order-two certificate of `b₃` is therefore a bounded Fourier multiple of the coefficients
   of that right-hand side, which is `axialRecoveredCertificate`.  The paper runs the same
   ellipticity on `V` instead (last paragraph of the proof of `lem:axial-recovery`).
3. The assembly and the eigenvalue equation (end of the proof of `lem:axial-recovery`) are read
   off row by row from `transverseCoordL2_reducedInductionAction`, and solenoidality
   `Div V = e^{2πiKx₃}(Div⊥h + 2πiK b₃) = 0` holds by the definition of `b₃`.

The output is an eigenpair of the three-component `reducedInductionOperator`, so the rest of
the finish (`FastDynamo/Finish/RealSolution.lean`,
`FastDynamo/Operator/Compatibility.lean`, the exact real-part norm law of
`FastDynamo/Fourier/AxialL2.lean` and `axialLiftH2 K` of `FastDynamo/Fourier/ProductH2.lean`)
applies to it directly, and `MainReducedClauses` (`FastDynamo/Main.lean`) is inhabited
through it.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## The transverse divergence of the velocity in the Leibniz rule -/

/--
For a divergence-free `x₃`-independent velocity the diagonal velocity-gradient contribution of
the weak Leibniz rule vanishes: `∑_{j<2} (∂_j u_j) d = (Div⊥u⊥) d = 0`.  This is the transverse
counterpart of `productVelocityDiagonalDerivMul_add_eq_zero`.
-/
theorem transverseVelocityDiagonalDerivMul_eq_zero (u : TransverseRealW1Inf)
    (hdiv : IsTransverseDivergenceFree u) (d : TransverseScalarL2) :
    ∑ j : Fin 2,
      scalarMulTransverse (transverseW1InfComplexDerivCoordLInf j j.castSucc u) d = 0 := by
  have hc0 : Fin.castSucc (0 : Fin 2) = (0 : Fin 3) := by decide
  have hc1 : Fin.castSucc (1 : Fin 2) = (1 : Fin 3) := by decide
  rw [Fin.sum_univ_two, hc0, hc1, ← add_apply, ← map_add, hdiv]
  simp

/--
**The sector divergence of the transport term** (curl identity in the proof of
`lem:axial-recovery`).  For divergence-free `u⊥` and
a scalar field `d` with `L²` periodic weak derivatives `dd j`, the transverse divergence of
`u⊥ d` is `u⊥·∇⊥ d`, frequency by frequency.
-/
theorem transverseDivergence_velocityTimesScalar_coeff (u : TransverseRealW1Inf)
    (hdiv : IsTransverseDivergenceFree u) {d : TransverseScalarL2}
    {dd : Fin 2 → TransverseScalarL2}
    (hd : ∀ j : Fin 2, HasTransverseScalarFourierDerivative j d (dd j))
    (n : TransverseFrequency) :
    (∑ j : Fin 2, (2 * Real.pi * Complex.I * (n j : ℂ)) *
        transverseScalarCoeffCLM n
          (scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u) d)) =
      ∑ j : Fin 2, transverseScalarCoeffCLM n
        (scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u) (dd j)) := by
  have hleib : ∀ j : Fin 2,
      (2 * Real.pi * Complex.I * (n j : ℂ)) *
          transverseScalarCoeffCLM n
            (scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u) d) =
        transverseScalarCoeffCLM n
            (scalarMulTransverse (transverseW1InfComplexDerivCoordLInf j j.castSucc u) d) +
          transverseScalarCoeffCLM n
            (scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u)
              (dd j)) := by
    intro j
    have hl := hasTransverseScalarDeriv_scalarMulTransverse
      (transverseW1InfCoord_hasScalarFourierDerivative u j j.castSucc) (hd j) n
    rw [map_add] at hl
    exact hl.symm
  rw [Finset.sum_congr rfl fun j _ => hleib j, Finset.sum_add_distrib, ← map_sum,
    transverseVelocityDiagonalDerivMul_eq_zero u hdiv d, map_zero, zero_add]

/-! ## The diffusion symbol of the recovered axial equation -/

/-- The elliptic symbol `ε(4π²|n|² + (2πK)²)` of the recovered axial equation. -/
def axialRecoveredSymbol (ε : ℝ) (K : ℤ) (n : TransverseFrequency) : ℝ :=
  ε * (transverseFrequencyEnergy n + (2 * Real.pi * K) ^ 2)

/--
For `K ≠ 0` the elliptic symbol dominates `ε` times the order-two weight: this is the
quantitative form of the elliptic regularity step in the proof of `lem:axial-recovery`, applied
to `b₃` instead of `V`.  The point is
`(2πK)² ≥ 4π² > 1`, so `1 + 4π²|n|² ≤ 4π²|n|² + (2πK)²`.
-/
theorem transverseH2Weight_le_axialRecoveredSymbol {ε : ℝ} (hε : 0 < ε) {K : ℤ} (hK : K ≠ 0)
    (n : TransverseFrequency) :
    ε * transverseH2Weight n ≤ axialRecoveredSymbol ε K n := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ K ^ 2 := by
      rcases lt_or_gt_of_ne hK with hneg | hpos
      · nlinarith
      · nlinarith
    exact_mod_cast this
  have hpi : (1 : ℝ) < (2 * Real.pi) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hkey : (1 : ℝ) ≤ (2 * Real.pi * K) ^ 2 := by
    have : (2 * Real.pi * (K : ℝ)) ^ 2 = (2 * Real.pi) ^ 2 * (K : ℝ) ^ 2 := by ring
    nlinarith
  unfold axialRecoveredSymbol transverseH2Weight
  nlinarith

/-- The elliptic symbol is strictly positive, hence invertible. -/
theorem axialRecoveredSymbol_pos {ε : ℝ} (hε : 0 < ε) {K : ℤ} (hK : K ≠ 0)
    (n : TransverseFrequency) : 0 < axialRecoveredSymbol ε K n := by
  have h1 := transverseH2Weight_le_axialRecoveredSymbol hε hK n
  have h2 : 0 < ε * transverseH2Weight n := mul_pos hε (transverseH2Weight_pos n)
  linarith

/-- The complexified elliptic symbol is nonzero. -/
theorem axialRecoveredSymbol_ne_zero {ε : ℝ} (hε : 0 < ε) {K : ℤ} (hK : K ≠ 0)
    (n : TransverseFrequency) : ((axialRecoveredSymbol ε K n : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (axialRecoveredSymbol_pos hε hK n).ne'

/-! ## The elliptic Fourier multiplier producing the order-two certificate -/

/-- The Fourier multiplier `(1 + 4π²|n|²) / (ε(4π²|n|² + (2πK)²))` of the elliptic upgrade. -/
def axialRecoveredWeightMultiplier (ε : ℝ) (K : ℤ) (n : TransverseFrequency) : ℂ :=
  (transverseH2Weight n : ℂ) / ((axialRecoveredSymbol ε K n : ℝ) : ℂ)

/-- The elliptic multiplier is bounded by `1/ε`, uniformly in the frequency. -/
theorem norm_axialRecoveredWeightMultiplier_le {ε : ℝ} (hε : 0 < ε) {K : ℤ} (hK : K ≠ 0)
    (n : TransverseFrequency) :
    ‖axialRecoveredWeightMultiplier ε K n‖ ≤ 1 / ε := by
  rw [axialRecoveredWeightMultiplier, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (transverseH2Weight_pos n),
    abs_of_pos (axialRecoveredSymbol_pos hε hK n),
    div_le_div_iff₀ (axialRecoveredSymbol_pos hε hK n) hε]
  have h := transverseH2Weight_le_axialRecoveredSymbol hε hK n
  nlinarith

/-- The bounded coefficient map of the elliptic upgrade. -/
def axialRecoveredCertificateMap {ε : ℝ} (hε : 0 < ε) {K : ℤ} (hK : K ≠ 0) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ) (axialRecoveredWeightMultiplier ε K n))
    (div_nonneg zero_le_one hε.le)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (axialRecoveredWeightMultiplier ε K n)).trans
        (norm_axialRecoveredWeightMultiplier_le hε hK n))

/-- The elliptic coefficient map acts diagonally. -/
@[simp] theorem axialRecoveredCertificateMap_apply {ε : ℝ} (hε : 0 < ε) {K : ℤ} (hK : K ≠ 0)
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    axialRecoveredCertificateMap hε hK a n = axialRecoveredWeightMultiplier ε K n * a n :=
  rfl

/-! ## The right-hand side of the recovered axial equation -/

/--
The `L²` right-hand side of the recovered axial equation rewritten for the elliptic upgrade
(the paper upgrades `V` instead, in the proof of `lem:axial-recovery`):

`-λb₃ + (h·∇⊥)u₃ - u⊥·∇⊥b₃ - 2πiK u₃ b₃`.

Every summand is an `L²` field, because `b₃` carries `L²` weak derivatives
(`axialRecoveredComponentDeriv`) and `u ∈ W^{1,∞}`.
-/
def axialRecoveredSource (u : TransverseRealW1Inf) (K : ℤ) (lam : ℂ) (h : TransverseC2H2) :
    TransverseScalarL2 :=
  -lam • axialRecoveredComponent K h + axialStretchingSource u h -
      (∑ j : Fin 2, scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u)
        (axialRecoveredComponentDeriv K j h)) -
    axialMultiplier K • scalarMulTransverse (transverseW1InfComplexValueCoordLInf 2 u)
      (axialRecoveredComponent K h)

/-- Fourier coefficients of the right-hand side of the recovered axial equation. -/
theorem transverseScalarCoeffCLM_axialRecoveredSource (u : TransverseRealW1Inf) (K : ℤ)
    (lam : ℂ) (h : TransverseC2H2) (n : TransverseFrequency) :
    transverseScalarCoeffCLM n (axialRecoveredSource u K lam h) =
      -lam * transverseScalarCoeffCLM n (axialRecoveredComponent K h) +
          transverseScalarCoeffCLM n (axialStretchingSource u h) -
        (∑ j : Fin 2, transverseScalarCoeffCLM n
          (scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u)
            (axialRecoveredComponentDeriv K j h))) -
      axialMultiplier K * transverseScalarCoeffCLM n
        (scalarMulTransverse (transverseW1InfComplexValueCoordLInf 2 u)
          (axialRecoveredComponent K h)) := by
  rw [axialRecoveredSource, map_sub, map_sub, map_add, map_smul, map_smul, map_sum]
  simp [smul_eq_mul]

/-! ## Taking the sector divergence of the horizontal eigenvalue equation -/

/--
The sector divergence symbol of `A₃(h, 0)`: the horizontal rows contribute `λ Div⊥h` by the
horizontal eigenvalue equation, and the axial row contributes `2πiK (h·∇⊥)u₃`.
-/
theorem fixedSectorDivergenceCoeff_reducedInductionAction_horizontalEmbedH2
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (lam : ℂ) (h : TransverseC2H2)
    (heigen : horizontalInductionAction u ε K h = lam • transverseH2Embedding h)
    (n : TransverseFrequency) :
    fixedSectorDivergenceCoeff K n (reducedInductionAction u ε K (horizontalEmbedH2 h)) =
      lam * transverseScalarCoeffCLM n (horizontalDivergenceFromH2 h) +
        axialMultiplier K * transverseScalarCoeffCLM n (axialStretchingSource u h) := by
  have hcast : ∀ j : Fin 2,
      transverseCoeffCLM n j.castSucc (reducedInductionAction u ε K (horizontalEmbedH2 h)) =
        lam * transverseCoeffCLM n j (transverseH2Embedding h) := by
    intro j
    rw [← transverseCoeffCLM_horizontalProjL2,
      horizontalProjL2_reducedInductionAction_horizontalEmbedH2, heigen, map_smul, smul_eq_mul]
  have hlast : transverseCoeffCLM n (2 : Fin 3)
      (reducedInductionAction u ε K (horizontalEmbedH2 h)) =
      transverseScalarCoeffCLM n (axialStretchingSource u h) := by
    change transverseScalarCoeffCLM n
      (transverseCoordL2 (2 : Fin 3)
        (reducedInductionAction u ε K (horizontalEmbedH2 h))) = _
    rw [transverseCoordL2_reducedInductionAction_horizontalEmbedH2]
  rw [fixedSectorDivergenceCoeff_apply, hlast,
    transverseScalarCoeffCLM_horizontalDivergenceFromH2, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcast j]
  ring

/-- The sector divergence symbol of the physical field of `(h, 0)` is `Div⊥h`. -/
theorem fixedSectorDivergenceCoeff_transverseH2Embedding_horizontalEmbedH2
    (K : ℤ) (h : TransverseC2H2) (n : TransverseFrequency) :
    fixedSectorDivergenceCoeff K n (transverseH2Embedding (horizontalEmbedH2 h)) =
      transverseScalarCoeffCLM n (horizontalDivergenceFromH2 h) := by
  rw [← transverseScalarCoeffCLM_fixedSectorDivergence, fixedSectorDivergence_horizontalEmbedH2]

/--
The sector divergence symbol of `u (Div⊥h)`, after the weak Leibniz rule and `Div⊥u⊥ = 0`:
the transverse part becomes `u⊥·∇⊥ Div⊥h`, and the axial part keeps the
multiplier `2πiK`.
-/
theorem fixedSectorDivergenceCoeff_velocityTimesScalar_horizontalEmbedH2
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u) (K : ℤ)
    (h : TransverseC2H2) (n : TransverseFrequency) :
    fixedSectorDivergenceCoeff K n
        (transverseVelocityTimesScalar u (fixedSectorDivergence K (horizontalEmbedH2 h))) =
      (∑ j : Fin 2, transverseScalarCoeffCLM n
          (scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u)
            (horizontalDivergenceDerivFromH2 j h))) +
        axialMultiplier K * transverseScalarCoeffCLM n
          (scalarMulTransverse (transverseW1InfComplexValueCoordLInf 2 u)
            (horizontalDivergenceFromH2 h)) := by
  have hco : ∀ i : Fin 3,
      transverseCoeffCLM n i
          (transverseVelocityTimesScalar u (horizontalDivergenceFromH2 h)) =
        transverseScalarCoeffCLM n
          (scalarMulTransverse (transverseW1InfComplexValueCoordLInf i u)
            (horizontalDivergenceFromH2 h)) := by
    intro i
    change transverseScalarCoeffCLM n
      (transverseCoordL2 i
        (transverseVelocityTimesScalar u (horizontalDivergenceFromH2 h))) = _
    rw [transverseCoordL2_transverseVelocityTimesScalar]
  have hsum : (∑ j : Fin 2, (2 * Real.pi * Complex.I * (n j : ℂ)) *
      transverseCoeffCLM n j.castSucc
        (transverseVelocityTimesScalar u (horizontalDivergenceFromH2 h))) =
      ∑ j : Fin 2, (2 * Real.pi * Complex.I * (n j : ℂ)) *
        transverseScalarCoeffCLM n
          (scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u)
            (horizontalDivergenceFromH2 h)) :=
    Finset.sum_congr rfl fun j _ => by rw [hco j.castSucc]
  rw [fixedSectorDivergence_horizontalEmbedH2, fixedSectorDivergenceCoeff_apply, hsum,
    hco (2 : Fin 3),
    transverseDivergence_velocityTimesScalar_coeff u hdiv
      (fun j => horizontalDivergenceFromH2_hasScalarFourierDerivative j h) n]

/-! ## The recovered axial equation -/

/-- `Div⊥h = -(2πiK) b₃`, the defining relation of the recovered axial component. -/
theorem horizontalDivergenceFromH2_eq_neg_smul {K : ℤ} (hK : K ≠ 0) (h : TransverseC2H2) :
    horizontalDivergenceFromH2 h = -(axialMultiplier K • axialRecoveredComponent K h) := by
  rw [axialMultiplier_smul_axialRecoveredComponent hK, neg_neg]

/-- `∂_j Div⊥h = -(2πiK) ∂_j b₃`, the derivative of the defining relation. -/
theorem horizontalDivergenceDerivFromH2_eq_neg_smul {K : ℤ} (hK : K ≠ 0) (j : Fin 2)
    (h : TransverseC2H2) :
    horizontalDivergenceDerivFromH2 j h =
      -(axialMultiplier K • axialRecoveredComponentDeriv K j h) := by
  rw [axialRecoveredComponentDeriv, smul_smul, mul_neg,
    mul_inv_cancel₀ (axialMultiplier_ne_zero hK)]
  simp

/--
**The recovered axial equation** (a display the paper does not have), at each transverse
Fourier frequency:

`ε(4π²|n|² + (2πK)²) b̂₃(n) = ĝ(n)`,  `g = -λb₃ + (h·∇⊥)u₃ - u⊥·∇⊥b₃ - 2πiK u₃ b₃`,

which is `(λ - S)b₃ = (h·∇⊥)u₃` with `S = ε(Δ⊥ - (2πK)²) - u⊥·∇⊥ - 2πiK u₃`.  It is obtained
by taking the sector divergence of the horizontal eigenvalue equation `A_{ε,K}h = λh` and
dividing by the nonzero multiplier `2πiK`.
-/
theorem axialRecoveredComponent_coeff_equation
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u) (ε : ℝ) {K : ℤ}
    (hK : K ≠ 0) (lam : ℂ) (h : TransverseC2H2)
    (heigen : horizontalInductionAction u ε K h = lam • transverseH2Embedding h)
    (n : TransverseFrequency) :
    ((axialRecoveredSymbol ε K n : ℝ) : ℂ) *
        transverseScalarCoeffCLM n (axialRecoveredComponent K h) =
      transverseScalarCoeffCLM n (axialRecoveredSource u K lam h) := by
  have hA : axialMultiplier K ≠ 0 := axialMultiplier_ne_zero hK
  have hsym : -(ε : ℂ) * ((transverseFrequencyEnergy n + (2 * Real.pi * K) ^ 2 : ℝ) : ℂ) =
      -((axialRecoveredSymbol ε K n : ℝ) : ℂ) := by
    rw [axialRecoveredSymbol]
    push_cast
    ring
  have hmaster := fixedSectorDivergenceCoeff_reducedInductionAction u hdiv ε K
    (horizontalEmbedH2 h) n
  rw [fixedSectorDivergenceCoeff_reducedInductionAction_horizontalEmbedH2 u ε K lam h heigen n,
    fixedSectorDivergenceCoeff_transverseH2Embedding_horizontalEmbedH2,
    fixedSectorDivergenceCoeff_velocityTimesScalar_horizontalEmbedH2 u hdiv K h n] at hmaster
  have hD : transverseScalarCoeffCLM n (horizontalDivergenceFromH2 h) =
      -(axialMultiplier K *
        transverseScalarCoeffCLM n (axialRecoveredComponent K h)) := by
    rw [horizontalDivergenceFromH2_eq_neg_smul hK]
    simp
  have hU : transverseScalarCoeffCLM n
        (scalarMulTransverse (transverseW1InfComplexValueCoordLInf 2 u)
          (horizontalDivergenceFromH2 h)) =
      -(axialMultiplier K * transverseScalarCoeffCLM n
        (scalarMulTransverse (transverseW1InfComplexValueCoordLInf 2 u)
          (axialRecoveredComponent K h))) := by
    rw [horizontalDivergenceFromH2_eq_neg_smul hK]
    simp
  have hTterm : ∀ j : Fin 2,
      transverseScalarCoeffCLM n
          (scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u)
            (horizontalDivergenceDerivFromH2 j h)) =
        -(axialMultiplier K * transverseScalarCoeffCLM n
          (scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u)
            (axialRecoveredComponentDeriv K j h))) := by
    intro j
    rw [horizontalDivergenceDerivFromH2_eq_neg_smul hK]
    simp
  have hT : (∑ j : Fin 2, transverseScalarCoeffCLM n
        (scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u)
          (horizontalDivergenceDerivFromH2 j h))) =
      -(axialMultiplier K * ∑ j : Fin 2, transverseScalarCoeffCLM n
        (scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u)
          (axialRecoveredComponentDeriv K j h))) := by
    rw [Finset.sum_congr rfl fun j _ => hTterm j]
    simp only [Fin.sum_univ_two]
    ring
  rw [hsym, hD, hU, hT] at hmaster
  rw [transverseScalarCoeffCLM_axialRecoveredSource]
  refine mul_left_cancel₀ hA ?_
  linear_combination -hmaster

/-! ## The order-two certificate of the recovered axial component -/

/-- The weighted order-two Fourier certificate of `b₃`: the elliptic upgrade, applied to `b₃`. -/
def axialRecoveredCertificate {ε : ℝ} (hε : 0 < ε) {K : ℤ} (hK : K ≠ 0)
    (u : TransverseRealW1Inf) (lam : ℂ) (h : TransverseC2H2) : TransverseScalarFourierL2 :=
  axialRecoveredCertificateMap hε hK
    (transverseScalarFourierAnalysis (axialRecoveredSource u K lam h))

/-- The certificate is the elliptic multiplier applied to the coefficients of the source. -/
theorem axialRecoveredCertificate_apply {ε : ℝ} (hε : 0 < ε) {K : ℤ} (hK : K ≠ 0)
    (u : TransverseRealW1Inf) (lam : ℂ) (h : TransverseC2H2) (n : TransverseFrequency) :
    axialRecoveredCertificate hε hK u lam h n =
      axialRecoveredWeightMultiplier ε K n *
        transverseScalarCoeffCLM n (axialRecoveredSource u K lam h) :=
  rfl

/--
**The elliptic upgrade** (applied to `b₃`; the paper applies it to `V`): the array
`axialRecoveredCertificate` is the weighted order-two Fourier certificate of `b₃`, so
`b₃ ∈ H²(T²;ℂ)`.  It is square-summable because it is a bounded Fourier multiple of the
coefficients of the `L²` field
`axialRecoveredSource u K lam h`.
-/
theorem axialRecoveredCertificate_eq (u : TransverseRealW1Inf)
    (hdiv : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε) {K : ℤ} (hK : K ≠ 0)
    (lam : ℂ) (h : TransverseC2H2)
    (heigen : horizontalInductionAction u ε K h = lam • transverseH2Embedding h)
    (n : TransverseFrequency) :
    axialRecoveredCertificate hε hK u lam h n =
      (transverseH2Weight n : ℂ) *
        transverseScalarCoeffCLM n (axialRecoveredComponent K h) := by
  have hQ := axialRecoveredSymbol_ne_zero hε hK n
  rw [axialRecoveredCertificate_apply,
    ← axialRecoveredComponent_coeff_equation u hdiv ε hK lam h heigen n,
    axialRecoveredWeightMultiplier]
  field_simp

/-! ## The bridge into the three-component reduced operator -/

private theorem reducedInductionAction_coeff_castSucc
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (lam : ℂ)
    (b : TransverseC3H2) (h : TransverseC2H2)
    (hproj : horizontalProjH2 b = h)
    (heigen : horizontalInductionAction u ε K h = lam • transverseH2Embedding h)
    (n : TransverseFrequency) (j : Fin 2) :
    transverseCoeffCLM n j.castSucc (reducedInductionAction u ε K b) =
      lam * transverseCoeffCLM n j (transverseH2Embedding h) := by
  rw [← transverseCoeffCLM_horizontalProjL2, horizontalProjL2_reducedInductionAction,
    hproj, heigen, map_smul, smul_eq_mul]

/--
**`lem:axial-recovery`** (Lemma 8.1), in sector form.

Let `ε > 0`, `K ∈ ℤ \ {0}`, let `u` be a transversally divergence-free `x₃`-independent
`W^{1,∞}` velocity, and let `(λ, h)` be an eigenpair of the horizontal torus operator
`A_{ε,K}` of `eq:torus-sector`.  Then `b = (h, b₃)` with `b₃ = -Div⊥h/(2πiK)` lies in
`H²(T²;ℂ³)` and is an eigenpair of the **three-component** reduced induction operator with the
same eigenvalue; moreover `V = e^{2πiKx₃}b` is solenoidal by construction, both at the level of
the sector amplitude and on the product torus.

Consequently the rest of the finish — `FastDynamo/Finish/RealSolution.lean`,
`FastDynamo/Operator/Compatibility.lean`, the exact real-part norm law of
`FastDynamo/Fourier/AxialL2.lean` and `axialLiftH2 K` of `FastDynamo/Fourier/ProductH2.lean` —
applies to `b`, and `MainReducedClauses` of `FastDynamo/Main.lean` is inhabited through it.
The paper states the conclusion on `T³` (`V ∈ H²(T³;ℂ³) ∩ L²_σ`, `L_{ε,u}V = λV`); here it is
stated for the sector amplitude `b`, with the solenoidality of `axialLiftH2 K b`.
-/
theorem exists_reducedInductionEigenpair_of_horizontalEigenpair
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)
    {K : ℤ} (hK : K ≠ 0) {lam : ℂ} {h : TransverseC2H2}
    (hpair : (horizontalInductionOperator u ε K).IsEigenpair lam h) :
    ∃ b : TransverseC3H2,
      (reducedInductionOperator u ε K).IsEigenpair lam b ∧
        horizontalProjH2 b = h ∧
        transverseCoordL2 (2 : Fin 3) (transverseH2Embedding b) =
          axialRecoveredComponent K h ∧
        fixedSectorDivergence K b = 0 ∧
        productDivergenceFromH2 (axialLiftH2 K b) = 0 := by
  obtain ⟨hne, heigen⟩ := hpair
  have heigen' : horizontalInductionAction u ε K h = lam • transverseH2Embedding h := heigen
  have hne' : transverseH2Embedding h ≠ 0 := hne
  have hcert : ∀ n, axialRecoveredCertificate hε hK u lam h n =
      (transverseH2Weight n : ℂ) *
        transverseScalarCoeffCLM n (axialRecoveredComponent K h) :=
    fun n => axialRecoveredCertificate_eq u hdiv hε hK lam h heigen' n
  obtain ⟨b, hemb⟩ : ∃ b : TransverseC3H2, transverseH2Embedding b =
      transverseSnocL2 (transverseH2Embedding h) (axialRecoveredComponent K h) :=
    ⟨transverseSnocH2 h (axialRecoveredComponent K h)
      (axialRecoveredCertificate hε hK u lam h) hcert,
      transverseH2Embedding_transverseSnocH2 _ _ _ hcert⟩
  have hcoord2 : transverseCoordL2 (2 : Fin 3) (transverseH2Embedding b) =
      axialRecoveredComponent K h := by
    rw [hemb, transverseCoordL2_transverseSnocL2_last]
  have hcoeff2 : ∀ n : TransverseFrequency,
      transverseCoeffCLM n (2 : Fin 3) (transverseH2Embedding b) =
        transverseScalarCoeffCLM n (axialRecoveredComponent K h) := by
    intro n
    change transverseScalarCoeffCLM n
      (transverseCoordL2 (2 : Fin 3) (transverseH2Embedding b)) = _
    rw [hcoord2]
  have hcoeffj : ∀ (n : TransverseFrequency) (j : Fin 2),
      transverseCoeffCLM n j.castSucc (transverseH2Embedding b) =
        transverseCoeffCLM n j (transverseH2Embedding h) := by
    intro n j
    rw [hemb, transverseCoeffCLM_transverseSnocL2_castSucc]
  have hproj : horizontalProjH2 b = h := by
    apply transverseH2Embedding_injective
    rw [transverseH2Embedding_horizontalProjH2, hemb, horizontalProjL2_transverseSnocL2]
  have hdivzero : fixedSectorDivergence K b = 0 := by
    apply transverseScalarL2_ext_coeff
    intro n
    have hsum : (∑ j : Fin 2, (2 * Real.pi * Complex.I * (n j : ℂ)) *
        transverseCoeffCLM n j.castSucc (transverseH2Embedding b)) =
        transverseScalarCoeffCLM n (horizontalDivergenceFromH2 h) := by
      rw [transverseScalarCoeffCLM_horizontalDivergenceFromH2]
      exact Finset.sum_congr rfl fun j _ => by rw [hcoeffj n j]
    rw [transverseScalarCoeffCLM_fixedSectorDivergence, fixedSectorDivergenceCoeff_apply,
      map_zero, hcoeff2 n, hsum, horizontalDivergenceFromH2_eq_neg_smul hK]
    simp
  refine ⟨b, ⟨?_, ?_⟩, hproj, hcoord2, hdivzero, ?_⟩
  · intro hzero
    have hzero' : transverseH2Embedding b = 0 := hzero
    apply hne'
    have hph : horizontalProjL2 (transverseH2Embedding b) = transverseH2Embedding h := by
      rw [hemb, horizontalProjL2_transverseSnocL2]
    rw [hzero', map_zero] at hph
    exact hph.symm
  · change reducedInductionAction u ε K b = lam • transverseH2Embedding b
    apply transverseVecL2_ext_coeff
    intro n i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change transverseCoeffCLM n (2 : Fin 3) (reducedInductionAction u ε K b) =
        transverseCoeffCLM n (2 : Fin 3) (lam • transverseH2Embedding b)
      have hderiv : ∀ j : Fin 2,
          transverseCoordL2 (2 : Fin 3) (transverseDerivFromH2 j b) =
            axialRecoveredComponentDeriv K j h := by
        intro j
        apply transverseScalarL2_ext_coeff
        intro m
        have hl : transverseScalarCoeffCLM m
            (transverseCoordL2 (2 : Fin 3) (transverseDerivFromH2 j b)) =
            (2 * Real.pi * Complex.I * (m j : ℂ)) *
              transverseScalarCoeffCLM m (axialRecoveredComponent K h) := by
          change transverseCoeffCLM m (2 : Fin 3) (transverseDerivFromH2 j b) = _
          rw [transverseCoeffCLM_transverseDerivFromH2, hcoeff2 m]
        rw [hl]
        exact (axialRecoveredComponent_hasScalarFourierDerivative K j h m).symm
      have hlapcoeff : transverseScalarCoeffCLM n
          (transverseCoordL2 (2 : Fin 3) (transverseLaplacianFromH2 b)) =
          -((transverseFrequencyEnergy n : ℝ) : ℂ) *
            transverseScalarCoeffCLM n (axialRecoveredComponent K h) := by
        change transverseCoeffCLM n (2 : Fin 3) (transverseLaplacianFromH2 b) = _
        rw [transverseCoeffCLM_transverseLaplacianFromH2, hcoeff2 n]
      have hstretch : (∑ j : Fin 2,
          scalarMulTransverse (transverseW1InfComplexDerivCoordLInf j (2 : Fin 3) u)
            (transverseCoordL2 j.castSucc (transverseH2Embedding b))) =
          axialStretchingSource u h := by
        rw [axialStretchingSource]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hemb, transverseCoordL2_transverseSnocL2_castSucc]
      have hrow := transverseCoordL2_reducedInductionAction u ε K b (2 : Fin 3)
      rw [hcoord2, hstretch] at hrow
      simp only [hderiv] at hrow
      have hcoeffrow := congrArg (transverseScalarCoeffCLM n) hrow
      simp only [map_add, map_sub, map_smul, map_sum, smul_eq_mul, hlapcoeff] at hcoeffrow
      have heq := axialRecoveredComponent_coeff_equation u hdiv ε hK lam h heigen' n
      rw [transverseScalarCoeffCLM_axialRecoveredSource] at heq
      have hQ : ((axialRecoveredSymbol ε K n : ℝ) : ℂ) =
          (ε : ℂ) * ((transverseFrequencyEnergy n : ℝ) : ℂ) +
            (ε : ℂ) * (2 * Real.pi * K : ℂ) ^ 2 := by
        rw [axialRecoveredSymbol]
        push_cast
        ring
      rw [hQ] at heq
      change transverseScalarCoeffCLM n
        (transverseCoordL2 (2 : Fin 3) (reducedInductionAction u ε K b)) = _
      rw [hcoeffrow, map_smul, smul_eq_mul, hcoeff2 n]
      linear_combination -heq
    · change transverseCoeffCLM n j.castSucc (reducedInductionAction u ε K b) =
        transverseCoeffCLM n j.castSucc (lam • transverseH2Embedding b)
      rw [reducedInductionAction_coeff_castSucc u ε K lam b h hproj heigen',
        map_smul, smul_eq_mul, hcoeffj n j]
  · rw [productDivergenceFromH2_axialLiftH2, hdivzero, map_zero]

end

end FastDynamo
