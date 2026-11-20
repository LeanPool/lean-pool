/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Finish.AxialRecoveryDivergence

/-!
# The recovered axial component `b₃ = -Div⊥h/(2πiK)` and the three-component assembly

Second of the three modules proving `lem:axial-recovery` (Lemma 8.1).  It supplies the objects
`b₃`, `b`, `V` that the statement of `lem:axial-recovery` introduces, and the `H²`-level
coordinate assembly `H²(T²;ℂ²) × H²(T²;ℂ) → H²(T²;ℂ³)`, which complements the Fourier-graph
model of `FastDynamo/Fourier/PeriodicH2.lean`.

Contents:

* `transverseVecSecondDerivFromH2 ι j m`, the bounded second transverse derivative
  `∂_j∂_m : H² → L²`, obtained from the stored order-two certificate exactly as
  `transverseVecDerivFromH2` is;
* `horizontalDivergenceFromH2`, the transverse divergence `Div⊥h` of a two-component `H²`
  field, and `horizontalDivergenceDerivFromH2 j`, its `j`-th derivative, with the Fourier
  weak-derivative certificate that makes the weak Leibniz rule of
  `FastDynamo/Analysis/TransverseWeightedLeibniz.lean` applicable to `u_j (Div⊥h)`;
* `axialRecoveredComponent K h = -Div⊥h/(2πiK)`, the paper's `b₃`;
* `transverseSnocH2`, the coordinate assembly `(h, b₃) ↦ b`, and
  `horizontalEmbedH2 h = (h, 0)`;
* `transverseCoordL2_reducedInductionAction`, the `i`-th row of the three-component reduced
  action, and its two consequences for `(h, 0)`: the horizontal row is `A_{ε,K}h`, the axial
  row is the stretching source `(h·∇⊥)u₃` of the recovered axial equation (see
  `FastDynamo/Finish/AxialRecovery.lean`: a display the paper does not have).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Bounded second transverse derivatives -/

/-- The Fourier multiplier of `∂_j∂_m` acting on the stored order-two certificate. -/
def transverseSecondDerivFourierMultiplier (j m : Fin 2) (n : TransverseFrequency) : ℂ :=
  (2 * Real.pi * Complex.I * (n j : ℂ)) * (2 * Real.pi * Complex.I * (n m : ℂ)) /
    (transverseH2Weight n : ℂ)

/--
The symbol `(2πi n_j)(2πi n_m)` divided by the order-two weight has modulus at most one, by
`4π²|n_j||n_m| ≤ 4π²|n|² ≤ transverseH2Weight n`.  This is why second derivatives are bounded
maps out of the periodic `H²` graph.
-/
lemma norm_transverseSecondDerivFourierMultiplier_le_one (j m : Fin 2)
    (n : TransverseFrequency) :
    ‖transverseSecondDerivFourierMultiplier j m n‖ ≤ 1 := by
  have hsq : ∀ i : Fin 2, (n i : ℝ) ^ 2 ≤ ∑ q, (n q : ℝ) ^ 2 := fun i =>
    Finset.single_le_sum (fun q _ => sq_nonneg (n q : ℝ)) (Finset.mem_univ i)
  have hprod : |(n j : ℝ)| * |(n m : ℝ)| ≤ ∑ q, (n q : ℝ) ^ 2 := by
    have h1 := hsq j
    have h2 := hsq m
    nlinarith [sq_nonneg (|(n j : ℝ)| - |(n m : ℝ)|), sq_abs (n j : ℝ), sq_abs (n m : ℝ)]
  have hpi : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have hkey : (2 * Real.pi) ^ 2 * (|(n j : ℝ)| * |(n m : ℝ)|) ≤ transverseH2Weight n := by
    have hmul := mul_le_mul_of_nonneg_left hprod hpi
    unfold transverseH2Weight transverseFrequencyEnergy
    linarith
  have hq : ∀ q : Fin 2,
      ‖2 * (Real.pi : ℂ) * Complex.I * (n q : ℂ)‖ = 2 * Real.pi * |(n q : ℝ)| := by
    intro q
    rw [norm_mul, norm_mul, norm_mul]
    simp [abs_of_pos Real.pi_pos]
  rw [transverseSecondDerivFourierMultiplier, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (transverseH2Weight_pos n)]
  refine (div_le_one (transverseH2Weight_pos n)).2 ?_
  rw [norm_mul, hq j, hq m]
  calc (2 * Real.pi * |(n j : ℝ)|) * (2 * Real.pi * |(n m : ℝ)|)
      = (2 * Real.pi) ^ 2 * (|(n j : ℝ)| * |(n m : ℝ)|) := by ring
    _ ≤ transverseH2Weight n := hkey

/-- Bounded scalar coefficient map realizing the second transverse derivative `∂_j∂_m`. -/
def transverseSecondDerivCoeffMap (j m : Fin 2) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ)
      (transverseSecondDerivFourierMultiplier j m n))
    zero_le_one
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (transverseSecondDerivFourierMultiplier j m n)).trans
        (norm_transverseSecondDerivFourierMultiplier_le_one j m n))

/-- The second-derivative coefficient map acts diagonally. -/
@[simp] theorem transverseSecondDerivCoeffMap_apply (j m : Fin 2)
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    transverseSecondDerivCoeffMap j m a n =
      transverseSecondDerivFourierMultiplier j m n * a n :=
  rfl

/-- The Fourier-characterized second transverse derivative `∂_j∂_m` as a bounded map
`H² → L²`, at an arbitrary finite fibre. -/
def transverseVecSecondDerivFromH2 (ι : Type*) [Fintype ι] [DecidableEq ι] (j m : Fin 2) :
    TransverseVecH2 ι →L[ℂ] TransverseVecL2 ι :=
  transverseVecOfCoordsL2.comp
    ((mapWeightedTransverseCoords
      (transverseScalarFourierSynthesis.comp (transverseSecondDerivCoeffMap j m))).comp
        transverseH2WeightedCoeffs)

/-- Fourier characterization of the second transverse derivative. -/
theorem transverseCoeffCLM_transverseVecSecondDerivFromH2 (j m : Fin 2)
    (b : TransverseVecH2 ι) (n : TransverseFrequency) (i : ι) :
    transverseCoeffCLM n i (transverseVecSecondDerivFromH2 ι j m b) =
      (2 * Real.pi * Complex.I * (n j : ℂ)) * (2 * Real.pi * Complex.I * (n m : ℂ)) *
        transverseCoeffCLM n i (transverseH2Embedding b) := by
  have hw : (transverseH2Weight n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (transverseH2Weight_pos n))
  have hstep : transverseCoeffCLM n i (transverseVecSecondDerivFromH2 ι j m b) =
      transverseSecondDerivFourierMultiplier j m n *
        ((transverseH2Weight n : ℂ) *
          transverseCoeffCLM n i (transverseH2Embedding b)) := by
    change transverseScalarCoeffCLM n (transverseCoordL2 i
      (transverseVecOfCoordsL2
        (mapWeightedTransverseCoords
          (transverseScalarFourierSynthesis.comp (transverseSecondDerivCoeffMap j m))
          (transverseH2WeightedCoeffs b)))) = _
    rw [transverseCoordL2_transverseVecOfCoordsL2, mapWeightedTransverseCoords_apply,
      ContinuousLinearMap.comp_apply, transverseScalarCoeffCLM_synthesis,
      transverseSecondDerivCoeffMap_apply, transverseH2WeightedCoeffs_apply]
  rw [hstep, transverseSecondDerivFourierMultiplier, div_mul_eq_mul_div, mul_div_assoc,
    mul_comm (transverseH2Weight n : ℂ) (transverseCoeffCLM n i (transverseH2Embedding b)),
    mul_div_assoc, div_self hw, mul_one]

/-! ## The transverse divergence of a horizontal `H²` field -/

/-- The transverse divergence `Div⊥h = ∑_{j<2} ∂_j h_j` of a two-component `H²` field
(statement of `lem:axial-recovery`). -/
def horizontalDivergenceFromH2 : TransverseC2H2 →L[ℂ] TransverseScalarL2 :=
  ∑ j : Fin 2,
    (transverseCoordL2 (ι := Fin 2) j).comp (transverseVecDerivFromH2 (Fin 2) j)

/-- Fourier coefficients of the transverse divergence. -/
theorem transverseScalarCoeffCLM_horizontalDivergenceFromH2 (h : TransverseC2H2)
    (n : TransverseFrequency) :
    transverseScalarCoeffCLM n (horizontalDivergenceFromH2 h) =
      ∑ j : Fin 2, (2 * Real.pi * Complex.I * (n j : ℂ)) *
        transverseCoeffCLM n j (transverseH2Embedding h) := by
  rw [horizontalDivergenceFromH2, sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact transverseCoeffCLM_transverseDerivFromH2 j h n j

/-- The `j`-th derivative `∂_j Div⊥h = ∑_{m<2} ∂_j∂_m h_m` of the transverse divergence. -/
def horizontalDivergenceDerivFromH2 (j : Fin 2) :
    TransverseC2H2 →L[ℂ] TransverseScalarL2 :=
  ∑ m : Fin 2,
    (transverseCoordL2 (ι := Fin 2) m).comp (transverseVecSecondDerivFromH2 (Fin 2) j m)

/-- Fourier coefficients of the derivative of the transverse divergence. -/
theorem transverseScalarCoeffCLM_horizontalDivergenceDerivFromH2 (j : Fin 2)
    (h : TransverseC2H2) (n : TransverseFrequency) :
    transverseScalarCoeffCLM n (horizontalDivergenceDerivFromH2 j h) =
      ∑ m : Fin 2, (2 * Real.pi * Complex.I * (n j : ℂ)) *
        ((2 * Real.pi * Complex.I * (n m : ℂ)) *
          transverseCoeffCLM n m (transverseH2Embedding h)) := by
  rw [horizontalDivergenceDerivFromH2, sum_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm : transverseScalarCoeffCLM n
      (((transverseCoordL2 (ι := Fin 2) m).comp
        (transverseVecSecondDerivFromH2 (Fin 2) j m)) h) =
      (2 * Real.pi * Complex.I * (n j : ℂ)) * (2 * Real.pi * Complex.I * (n m : ℂ)) *
        transverseCoeffCLM n m (transverseH2Embedding h) :=
    transverseCoeffCLM_transverseVecSecondDerivFromH2 j m h n m
  rw [hm]
  ring

/--
`horizontalDivergenceDerivFromH2 j h` is the `j`-th periodic weak derivative of
`Div⊥h`, in the Fourier-coefficient formulation of
`FastDynamo/Analysis/WeakLeibniz.lean`.  This is what lets the weak Leibniz rule be applied to
`u_j Div⊥h`, the only place in `lem:axial-recovery` where a derivative of `Div⊥h` is needed.
-/
theorem horizontalDivergenceFromH2_hasScalarFourierDerivative (j : Fin 2)
    (h : TransverseC2H2) :
    HasTransverseScalarFourierDerivative j (horizontalDivergenceFromH2 h)
      (horizontalDivergenceDerivFromH2 j h) := by
  intro n
  rw [transverseScalarCoeffCLM_horizontalDivergenceDerivFromH2,
    transverseScalarCoeffCLM_horizontalDivergenceFromH2, transverseFourierDerivMultiplier,
    Finset.mul_sum]

/-! ## The recovered axial component -/

/-- The axial Fourier multiplier `2πiK` is nonzero for a nonzero axial index. -/
theorem axialMultiplier_ne_zero {K : ℤ} (hK : K ≠ 0) : axialMultiplier K ≠ 0 := by
  rw [axialMultiplier]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
  · exact_mod_cast Real.pi_ne_zero
  · exact_mod_cast hK

/--
**The recovered axial magnetic component** `b₃ = -Div⊥h/(2πiK)` of `lem:axial-recovery`.
As defined here it is an `L²` field; the `H²`
regularity is the content of `FastDynamo/Finish/AxialRecovery.lean`.
-/
def axialRecoveredComponent (K : ℤ) (h : TransverseC2H2) : TransverseScalarL2 :=
  -(axialMultiplier K)⁻¹ • horizontalDivergenceFromH2 h

/-- The `j`-th periodic weak derivative of the recovered axial component. -/
def axialRecoveredComponentDeriv (K : ℤ) (j : Fin 2) (h : TransverseC2H2) :
    TransverseScalarL2 :=
  -(axialMultiplier K)⁻¹ • horizontalDivergenceDerivFromH2 j h

/-- The recovered axial component has `L²` periodic weak derivatives of every transverse
direction; in particular it lies in `H¹` (first line of the proof of
`lem:axial-recovery`). -/
theorem axialRecoveredComponent_hasScalarFourierDerivative (K : ℤ) (j : Fin 2)
    (h : TransverseC2H2) :
    HasTransverseScalarFourierDerivative j (axialRecoveredComponent K h)
      (axialRecoveredComponentDeriv K j h) := by
  intro n
  rw [axialRecoveredComponent, axialRecoveredComponentDeriv, map_smul, map_smul,
    horizontalDivergenceFromH2_hasScalarFourierDerivative j h n]
  simp only [smul_eq_mul]
  ring

/-- The defining relation `2πiK b₃ = -Div⊥h` of the recovered axial component. -/
theorem axialMultiplier_smul_axialRecoveredComponent {K : ℤ} (hK : K ≠ 0)
    (h : TransverseC2H2) :
    axialMultiplier K • axialRecoveredComponent K h = -horizontalDivergenceFromH2 h := by
  rw [axialRecoveredComponent, smul_smul, mul_neg, mul_inv_cancel₀ (axialMultiplier_ne_zero hK)]
  simp

/-! ## The three-component coordinate assembly -/

/-- Append a scalar coordinate to two scalar coordinates. -/
def transverseSnocCoords (a : Fin 2 → TransverseScalarL2) (f : TransverseScalarL2) :
    TransverseC3CoordinateL2 :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ : Fin 3 => TransverseScalarL2) a f)

/-- The appended coordinate array reads off as `Fin.snoc`. -/
@[simp] theorem transverseSnocCoords_apply (a : Fin 2 → TransverseScalarL2)
    (f : TransverseScalarL2) (i : Fin 3) :
    transverseSnocCoords a f i =
      Fin.snoc (α := fun _ : Fin 3 => TransverseScalarL2) a f i :=
  rfl

/-- Append a scalar coefficient array to two scalar coefficient arrays. -/
def transverseSnocWeighted (a : Fin 2 → TransverseScalarFourierL2)
    (c : TransverseScalarFourierL2) : WeightedTransverseC3Coeffs :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ : Fin 3 => TransverseScalarFourierL2) a c)

/-- The appended certificate array reads off as `Fin.snoc`. -/
@[simp] theorem transverseSnocWeighted_apply (a : Fin 2 → TransverseScalarFourierL2)
    (c : TransverseScalarFourierL2) (i : Fin 3) :
    transverseSnocWeighted a c i =
      Fin.snoc (α := fun _ : Fin 3 => TransverseScalarFourierL2) a c i :=
  rfl

/-- The three-component `L²` field `(h, f)` built from a two-component field and a scalar. -/
def transverseSnocL2 (h : TransverseC2L2) (f : TransverseScalarL2) : TransverseC3L2 :=
  transverseVecOfCoordsL2
    (transverseSnocCoords (fun j : Fin 2 => transverseCoordL2 j h) f)

/-- The horizontal coordinates of `(h, f)` are those of `h`. -/
@[simp] theorem transverseCoordL2_transverseSnocL2_castSucc (h : TransverseC2L2)
    (f : TransverseScalarL2) (j : Fin 2) :
    transverseCoordL2 j.castSucc (transverseSnocL2 h f) = transverseCoordL2 j h := by
  rw [transverseSnocL2, transverseCoordL2_transverseVecOfCoordsL2, transverseSnocCoords_apply,
    Fin.snoc_castSucc]

/-- The axial coordinate of `(h, f)` is `f`. -/
@[simp] theorem transverseCoordL2_transverseSnocL2_last (h : TransverseC2L2)
    (f : TransverseScalarL2) :
    transverseCoordL2 (2 : Fin 3) (transverseSnocL2 h f) = f := by
  rw [transverseSnocL2, transverseCoordL2_transverseVecOfCoordsL2, transverseSnocCoords_apply]
  exact Fin.snoc_last _ _

/-- The horizontal Fourier coefficients of `(h, f)` are those of `h`. -/
theorem transverseCoeffCLM_transverseSnocL2_castSucc (h : TransverseC2L2)
    (f : TransverseScalarL2) (n : TransverseFrequency) (j : Fin 2) :
    transverseCoeffCLM n j.castSucc (transverseSnocL2 h f) = transverseCoeffCLM n j h := by
  change transverseScalarCoeffCLM n (transverseCoordL2 j.castSucc (transverseSnocL2 h f)) =
    transverseScalarCoeffCLM n (transverseCoordL2 j h)
  rw [transverseCoordL2_transverseSnocL2_castSucc]

/-- The axial Fourier coefficients of `(h, f)` are those of `f`. -/
theorem transverseCoeffCLM_transverseSnocL2_last (h : TransverseC2L2)
    (f : TransverseScalarL2) (n : TransverseFrequency) :
    transverseCoeffCLM n (2 : Fin 3) (transverseSnocL2 h f) =
      transverseScalarCoeffCLM n f := by
  change transverseScalarCoeffCLM n (transverseCoordL2 (2 : Fin 3) (transverseSnocL2 h f)) = _
  rw [transverseCoordL2_transverseSnocL2_last]

/-- The horizontal projection of `(h, f)` is `h`. -/
theorem horizontalProjL2_transverseSnocL2 (h : TransverseC2L2) (f : TransverseScalarL2) :
    horizontalProjL2 (transverseSnocL2 h f) = h := by
  apply transverseVecL2_ext_coeff
  intro n j
  rw [transverseCoeffCLM_horizontalProjL2, transverseCoeffCLM_transverseSnocL2_castSucc]

/-- The assembled pair again satisfies the coordinatewise `H²` graph equation. -/
theorem transverseSnocH2_graph_mem (h : TransverseC2H2) (f : TransverseScalarL2)
    (c : TransverseScalarFourierL2)
    (hc : ∀ n, c n = (transverseH2Weight n : ℂ) * transverseScalarCoeffCLM n f) :
    (transverseSnocL2 (transverseH2Embedding h) f,
        transverseSnocWeighted (fun j : Fin 2 => transverseH2WeightedCoeffs h j) c) ∈
      transverseH2Submodule (ι := Fin 3) := by
  rw [mem_transverseH2Submodule_iff]
  have hlast : ∀ n : TransverseFrequency,
      transverseSnocWeighted (fun j : Fin 2 => transverseH2WeightedCoeffs h j) c
          (2 : Fin 3) n =
        (transverseH2Weight n : ℂ) * transverseCoeffCLM n (2 : Fin 3)
          (transverseSnocL2 (transverseH2Embedding h) f) := by
    intro n
    rw [transverseSnocWeighted_apply, transverseCoeffCLM_transverseSnocL2_last]
    exact congrArg (fun x : TransverseScalarFourierL2 => x n) (Fin.snoc_last _ _) |>.trans (hc n)
  have hcast : ∀ (n : TransverseFrequency) (j : Fin 2),
      transverseSnocWeighted (fun j : Fin 2 => transverseH2WeightedCoeffs h j) c
          j.castSucc n =
        (transverseH2Weight n : ℂ) * transverseCoeffCLM n j.castSucc
          (transverseSnocL2 (transverseH2Embedding h) f) := by
    intro n j
    rw [transverseSnocWeighted_apply, Fin.snoc_castSucc,
      transverseCoeffCLM_transverseSnocL2_castSucc, transverseH2WeightedCoeffs_apply]
  intro n i
  exact Fin.lastCases (hlast n) (fun j => hcast n j) i

/--
**The `H²`-level coordinate assembly** `H²(T²;ℂ²) × H²(T²;ℂ) → H²(T²;ℂ³)`, `(h, b₃) ↦ b`.
The scalar second factor is presented by its physical field `f` together with its weighted
order-two Fourier certificate `c`, exactly as the graph model of
`FastDynamo/Fourier/PeriodicH2.lean` presents every `H²` element; the graph equation is
coordinatewise, so the assembled pair again lies in `transverseH2Submodule`.
-/
def transverseSnocH2 (h : TransverseC2H2) (f : TransverseScalarL2)
    (c : TransverseScalarFourierL2)
    (hc : ∀ n, c n = (transverseH2Weight n : ℂ) * transverseScalarCoeffCLM n f) :
    TransverseC3H2 :=
  ⟨(transverseSnocL2 (transverseH2Embedding h) f,
      transverseSnocWeighted (fun j : Fin 2 => transverseH2WeightedCoeffs h j) c),
    transverseSnocH2_graph_mem h f c hc⟩

/-- The physical field of the assembled `H²` element. -/
theorem transverseH2Embedding_transverseSnocH2 (h : TransverseC2H2)
    (f : TransverseScalarL2) (c : TransverseScalarFourierL2)
    (hc : ∀ n, c n = (transverseH2Weight n : ℂ) * transverseScalarCoeffCLM n f) :
    transverseH2Embedding (transverseSnocH2 h f c hc) =
      transverseSnocL2 (transverseH2Embedding h) f :=
  rfl

/-- The horizontal part of the assembled `H²` element is the given two-component field. -/
theorem horizontalProjH2_transverseSnocH2 (h : TransverseC2H2) (f : TransverseScalarL2)
    (c : TransverseScalarFourierL2)
    (hc : ∀ n, c n = (transverseH2Weight n : ℂ) * transverseScalarCoeffCLM n f) :
    horizontalProjH2 (transverseSnocH2 h f c hc) = h := by
  apply transverseH2Embedding_injective
  rw [transverseH2Embedding_horizontalProjH2, transverseH2Embedding_transverseSnocH2,
    horizontalProjL2_transverseSnocL2]

/-- The horizontal embedding `h ↦ (h, 0) : H²(T²;ℂ²) → H²(T²;ℂ³)`. -/
def horizontalEmbedH2 (h : TransverseC2H2) : TransverseC3H2 :=
  transverseSnocH2 h 0 0 (by intro n; simp)

/-- The physical field of `(h, 0)`. -/
theorem transverseH2Embedding_horizontalEmbedH2 (h : TransverseC2H2) :
    transverseH2Embedding (horizontalEmbedH2 h) =
      transverseSnocL2 (transverseH2Embedding h) 0 :=
  rfl

/-- The horizontal part of `(h, 0)` is `h`. -/
@[simp] theorem horizontalProjH2_horizontalEmbedH2 (h : TransverseC2H2) :
    horizontalProjH2 (horizontalEmbedH2 h) = h :=
  horizontalProjH2_transverseSnocH2 h 0 0 _

/-- The axial coordinate of `(h, 0)` vanishes. -/
theorem transverseCoordL2_horizontalEmbedH2_last (h : TransverseC2H2) :
    transverseCoordL2 (2 : Fin 3) (transverseH2Embedding (horizontalEmbedH2 h)) = 0 := by
  rw [transverseH2Embedding_horizontalEmbedH2, transverseCoordL2_transverseSnocL2_last]

/-- The horizontal coordinates of `(h, 0)` are those of `h`. -/
theorem transverseCoordL2_horizontalEmbedH2_castSucc (h : TransverseC2H2)
    (j : Fin 2) :
    transverseCoordL2 j.castSucc (transverseH2Embedding (horizontalEmbedH2 h)) =
      transverseCoordL2 j (transverseH2Embedding h) := by
  rw [transverseH2Embedding_horizontalEmbedH2, transverseCoordL2_transverseSnocL2_castSucc]

/-! ## Rows of the three-component reduced action -/

/--
The `i`-th row of the reduced induction action, written out with scalar multipliers.  The
stretching term reads only the two horizontal coordinates of `b`, which is the block structure
`A₃ = [[A₂, 0], [S, D]]` in coordinates.
-/
theorem transverseCoordL2_reducedInductionAction
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (b : TransverseC3H2) (i : Fin 3) :
    transverseCoordL2 i (reducedInductionAction u ε K b) =
      (ε : ℂ) • (transverseCoordL2 i (transverseLaplacianFromH2 b) -
            (2 * Real.pi * K : ℂ) ^ 2 • transverseCoordL2 i (transverseH2Embedding b)) -
        (∑ j : Fin 2,
          scalarMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u)
            (transverseCoordL2 i (transverseDerivFromH2 j b))) -
        axialMultiplier K • scalarMulTransverse (transverseW1InfComplexValueCoordLInf 2 u)
          (transverseCoordL2 i (transverseH2Embedding b)) +
        (∑ j : Fin 2,
          scalarMulTransverse (transverseW1InfComplexDerivCoordLInf j i u)
            (transverseCoordL2 j.castSucc (transverseH2Embedding b))) := by
  rw [reducedInductionAction_apply]
  simp only [map_add, map_sub, map_smul, map_sum,
    transverseCoordL2_scalarVectorMulTransverse, transverseCoordL2_vectorScalarMulTransverse]
  rfl

/--
**The stretching source of the recovered axial equation**:
`(h·∇⊥)u₃ = ∑_{j<2} h_j ∂_j u₃`, the `(3,⊥)` block of the three-component operator applied to
the horizontal eigenfunction.
-/
def axialStretchingSource (u : TransverseRealW1Inf) (h : TransverseC2H2) :
    TransverseScalarL2 :=
  ∑ j : Fin 2,
    scalarMulTransverse (transverseW1InfComplexDerivCoordLInf j (2 : Fin 3) u)
      (transverseCoordL2 j (transverseH2Embedding h))

omit [DecidableEq ι] in
/-- A coordinate of a transverse `L²` field with vanishing Fourier coefficients vanishes. -/
theorem transverseCoordL2_eq_zero_of_coeff {f : TransverseVecL2 ι} {i : ι}
    (h : ∀ n, transverseCoeffCLM n i f = 0) : transverseCoordL2 i f = 0 := by
  apply transverseScalarL2_ext_coeff
  intro n
  rw [map_zero]
  exact h n

/-- The axial coordinate of the Laplacian of `(h, 0)` vanishes. -/
theorem transverseCoordL2_transverseLaplacianFromH2_horizontalEmbedH2 (h : TransverseC2H2) :
    transverseCoordL2 (2 : Fin 3) (transverseLaplacianFromH2 (horizontalEmbedH2 h)) = 0 := by
  refine transverseCoordL2_eq_zero_of_coeff fun n => ?_
  rw [transverseCoeffCLM_transverseLaplacianFromH2]
  change _ * transverseScalarCoeffCLM n
    (transverseCoordL2 (2 : Fin 3) (transverseH2Embedding (horizontalEmbedH2 h))) = 0
  rw [transverseCoordL2_horizontalEmbedH2_last, map_zero, mul_zero]

/-- The axial coordinate of each transverse derivative of `(h, 0)` vanishes. -/
theorem transverseCoordL2_transverseDerivFromH2_horizontalEmbedH2 (j : Fin 2)
    (h : TransverseC2H2) :
    transverseCoordL2 (2 : Fin 3) (transverseDerivFromH2 j (horizontalEmbedH2 h)) = 0 := by
  refine transverseCoordL2_eq_zero_of_coeff fun n => ?_
  rw [transverseCoeffCLM_transverseDerivFromH2]
  change _ * transverseScalarCoeffCLM n
    (transverseCoordL2 (2 : Fin 3) (transverseH2Embedding (horizontalEmbedH2 h))) = 0
  rw [transverseCoordL2_horizontalEmbedH2_last, map_zero, mul_zero]

/--
**The axial row of the reduced action at `(h, 0)`** is exactly the stretching source
`(h·∇⊥)u₃` of the recovered axial equation: the diagonal scalar block annihilates the zero
axial component and only the `(3,⊥)` block survives.
-/
theorem transverseCoordL2_reducedInductionAction_horizontalEmbedH2
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (h : TransverseC2H2) :
    transverseCoordL2 (2 : Fin 3)
        (reducedInductionAction u ε K (horizontalEmbedH2 h)) =
      axialStretchingSource u h := by
  rw [transverseCoordL2_reducedInductionAction,
    transverseCoordL2_transverseLaplacianFromH2_horizontalEmbedH2,
    transverseCoordL2_horizontalEmbedH2_last, axialStretchingSource]
  simp only [transverseCoordL2_transverseDerivFromH2_horizontalEmbedH2,
    transverseCoordL2_horizontalEmbedH2_castSucc, map_zero, smul_zero, sub_zero,
    Finset.sum_const_zero, sub_zero]
  simp

/-- The sector divergence of `(h, 0)` is the transverse divergence of `h`. -/
theorem fixedSectorDivergence_horizontalEmbedH2 (K : ℤ) (h : TransverseC2H2) :
    fixedSectorDivergence K (horizontalEmbedH2 h) = horizontalDivergenceFromH2 h := by
  apply transverseScalarL2_ext_coeff
  intro n
  rw [transverseScalarCoeffCLM_fixedSectorDivergence, fixedSectorDivergenceCoeff_apply,
    transverseScalarCoeffCLM_horizontalDivergenceFromH2]
  have hlast : transverseCoeffCLM n (2 : Fin 3)
      (transverseH2Embedding (horizontalEmbedH2 h)) = 0 := by
    change transverseScalarCoeffCLM n
      (transverseCoordL2 (2 : Fin 3) (transverseH2Embedding (horizontalEmbedH2 h))) = 0
    rw [transverseCoordL2_horizontalEmbedH2_last, map_zero]
  rw [hlast, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change transverseScalarCoeffCLM n
      (transverseCoordL2 j.castSucc (transverseH2Embedding (horizontalEmbedH2 h))) =
    transverseScalarCoeffCLM n (transverseCoordL2 j (transverseH2Embedding h))
  rw [transverseCoordL2_horizontalEmbedH2_castSucc]

/-- The horizontal row of the reduced action at `(h, 0)` is the horizontal operator
`A_{ε,K}h` of `eq:torus-sector`. -/
theorem horizontalProjL2_reducedInductionAction_horizontalEmbedH2
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (h : TransverseC2H2) :
    horizontalProjL2 (reducedInductionAction u ε K (horizontalEmbedH2 h)) =
      horizontalInductionAction u ε K h := by
  rw [horizontalProjL2_reducedInductionAction, horizontalProjH2_horizontalEmbedH2]

end

end FastDynamo
