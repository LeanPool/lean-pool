/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.InductionDivergence
public import LeanPool.FastDynamo.Operator.HorizontalSector

/-!
# The transport--stretching divergence identity in one axial Fourier sector

This module is the first of the three that prove `lem:axial-recovery` (Lemma 8.1).  The route
formalised here is not the paper's (see `FastDynamo/Finish/AxialRecovery.lean` for the
comparison with its shorter proof); it starts from the distributional identity

`Div[-(w·∇)F + (F·∇)w] = -w·∇ Div F`  (the paper states only the distributional curl
identity `curl(u×V) = (V·∇)u − (u·∇)V`, in the proof of `lem:axial-recovery`)

for a divergence-free `x₃`-independent `w ∈ W^{1,∞}(T³; ℝ³)` and `F ∈ H²(T³; ℂ³)`, justified
by the curl representation `curl(w × F) - w Div F` of the bracket.  The paper uses the
same representation, in the equivalent form `curl(u×V) = (V·∇)u − (u·∇)V`.

That identity is proved in this library, for the all-frequency product torus,
as `productInductionLowerField_add_velocityDiv_eq_weakCurl` together with
`productVelocityCrossWeakCurl_solenoidal`
(`FastDynamo/Analysis/InductionDivergence.lean`).  Rather than re-running the curl argument in
two transverse dimensions, this module **transports it into a single axial Fourier sector**
along `axialLiftL2 K`: applying the product identity to `F = e^{2πiKx₃} b` and reading the
resulting divergence symbol at the axial frequency `K` gives

`div⊥ᴷ(A₃ b) = -ε(4π²|n|² + (2πK)²) div⊥ᴷ b - div⊥ᴷ(u · div⊥ᴷ b)`

frequency by frequency, which is `fixedSectorDivergenceCoeff_reducedInductionAction` below and
is the exact transverse shadow of that identity.

Contents:

* coordinate formulas for the two transverse `L∞`-multipliers;
* `transverseVelocityTimesScalar`, the transverse field `u d`, and its compatibility with the
  axial lift;
* `fixedSectorDivergenceCoeff`, the sector divergence symbol
  `∑_{j<2} 2πi n_j f̂_j(n) + 2πiK f̂₃(n)`, and its identification with the product divergence
  symbol of an axial lift;
* the sector form of the transport--stretching divergence identity.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## Coordinates of the transverse `L∞` multipliers -/

/-- At the scalar fibre the two Hölder multiplications agree: `a • g = g • a`. -/
theorem vectorScalarMulL2_scalar_eq
    (a : TransverseScalarLInf) (g : TransverseScalarL2) :
    vectorScalarMulL2 transverseMeasure a g = scalarMulTransverse a g := by
  apply Lp.ext
  filter_upwards [vectorScalarMulL2_coe_ae transverseMeasure a g,
    scalarMulTransverse_coe_ae a g] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/--
The `i`-th coordinate of the product of a `ℂ³`-valued `L∞` coefficient with a scalar `L²`
field is the product of the `i`-th coefficient component with that field: `(a g)_i = a_i g`.
-/
theorem transverseCoordL2_vectorScalarMulTransverse
    (a : TransverseC3LInf) (g : TransverseScalarL2) (i : Fin 3) :
    transverseCoordL2 i (vectorScalarMulTransverse a g) =
      scalarMulTransverse (transverseCoordLInf i a) g := by
  have h := compLpL_vectorScalarMulL2 (EuclideanSpace.proj (𝕜 := ℂ) i) a g
  rw [vectorScalarMulL2_scalar_eq] at h
  exact h

/-! ## The transverse field `u d` -/

/-- The three scalar coordinates `u_i d` of the transverse field `u d`. -/
def transverseVelocityTimesScalarCoords (u : TransverseRealW1Inf) :
    TransverseScalarL2 →L[ℂ] TransverseC3CoordinateL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 => TransverseScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      scalarMulTransverse (transverseW1InfComplexValueCoordLInf i u))

/--
Pointwise scalar multiplication `d ↦ u d` by the `x₃`-independent velocity, as a bounded map
`L²(T²; ℂ) → L²(T²; ℂ³)`.  It is the transverse counterpart of `productVelocityTimesScalar`
(`FastDynamo/Analysis/WeakLeibniz.lean`).
-/
def transverseVelocityTimesScalar (u : TransverseRealW1Inf) :
    TransverseScalarL2 →L[ℂ] TransverseC3L2 :=
  transverseC3OfCoordsL2.comp (transverseVelocityTimesScalarCoords u)

/-- The `i`-th coordinate of `u d` is `u_i d`. -/
@[simp] theorem transverseCoordL2_transverseVelocityTimesScalar
    (u : TransverseRealW1Inf) (d : TransverseScalarL2) (i : Fin 3) :
    transverseCoordL2 i (transverseVelocityTimesScalar u d) =
      scalarMulTransverse (transverseW1InfComplexValueCoordLInf i u) d := by
  rw [transverseVelocityTimesScalar, ContinuousLinearMap.comp_apply,
    transverseCoordL2_transverseC3OfCoordsL2]
  rfl

/--
Multiplication by the `x₃`-independent velocity commutes with the axial lift: the product-torus
field `u (e^{2πiKx₃} d)` is the axial lift of the transverse field `u d`.
-/
theorem productVelocityTimesScalar_scalarAxialLiftL2
    (u : TransverseRealW1Inf) (K : ℤ) (d : TransverseScalarL2) :
    productVelocityTimesScalar u (scalarAxialLiftL2 K d) =
      axialLiftL2 K (transverseVelocityTimesScalar u d) := by
  apply productC3L2_ext_coeff
  intro n k i
  have hcoord : productCoordL2 i (productVelocityTimesScalar u (scalarAxialLiftL2 K d)) =
      productCoordL2 i (axialLiftL2 K (transverseVelocityTimesScalar u d)) := by
    rw [productCoordL2_productVelocityTimesScalar, productCoordL2_axialLiftL2,
      transverseCoordL2_transverseVelocityTimesScalar]
    exact scalarMul_axialLift (transverseW1InfComplexValueCoordLInf i u) K d
  change productScalarCoeffCLM n k
      (productCoordL2 i (productVelocityTimesScalar u (scalarAxialLiftL2 K d))) =
    productScalarCoeffCLM n k
      (productCoordL2 i (axialLiftL2 K (transverseVelocityTimesScalar u d)))
  rw [hcoord]

/-! ## The sector divergence symbol -/

/--
The divergence symbol of a transverse amplitude in the axial Fourier sector `K`:

`∑_{j<2} 2πi n_j f̂_j(n) + 2πiK f̂₃(n)`,

as a continuous linear functional on transverse `L²`.  It is the exact Fourier coefficient of
`Div V` at `(n, K)` when `V = e^{2πiKx₃} f`.
-/
def fixedSectorDivergenceCoeff (K : ℤ) (n : TransverseFrequency) :
    TransverseC3L2 →L[ℂ] ℂ :=
  (∑ j : Fin 2,
      (2 * Real.pi * Complex.I * (n j : ℂ)) • transverseCoeffCLM n j.castSucc) +
    axialMultiplier K • transverseCoeffCLM n (2 : Fin 3)

/-- The sector divergence symbol, expanded. -/
theorem fixedSectorDivergenceCoeff_apply (K : ℤ) (n : TransverseFrequency)
    (f : TransverseC3L2) :
    fixedSectorDivergenceCoeff K n f =
      (∑ j : Fin 2,
        (2 * Real.pi * Complex.I * (n j : ℂ)) * transverseCoeffCLM n j.castSucc f) +
      axialMultiplier K * transverseCoeffCLM n (2 : Fin 3) f := by
  simp [fixedSectorDivergenceCoeff]

/--
The full product divergence symbol, as a continuous linear functional; it agrees with the plain
function `productFrequencyDivergenceCoeff` of
`FastDynamo/Analysis/ProductVectorCalculus.lean`.
-/
abbrev productDivergenceCoeff (n : TransverseFrequency) (k : ℤ) :
    ProductC3L2 →L[ℂ] ℂ :=
  productFrequencyDivergenceCLM n k

/-- The bundled product divergence symbol is the repository's divergence coefficient. -/
theorem productDivergenceCoeff_eq (n : TransverseFrequency) (k : ℤ) (V : ProductC3L2) :
    productDivergenceCoeff n k V = productFrequencyDivergenceCoeff n k V :=
  rfl

/--
In the axial sector `K` the product divergence symbol of a lifted amplitude is the transverse
sector divergence symbol of that amplitude.
-/
theorem productDivergenceCoeff_axialLiftL2 (K : ℤ) (n : TransverseFrequency)
    (g : TransverseC3L2) :
    productDivergenceCoeff n K (axialLiftL2 K g) = fixedSectorDivergenceCoeff K n g := by
  simp only [productDivergenceCoeff, productFrequencyDivergenceCLM, fixedSectorDivergenceCoeff,
    add_apply, sum_apply, smul_apply, smul_eq_mul, productCoeffCLM_axialLiftL2]
  rfl

/--
The `n`-th Fourier coefficient of the sector divergence `fixedSectorDivergence K b` is the
sector divergence symbol of the physical field of `b`.
-/
theorem transverseScalarCoeffCLM_fixedSectorDivergence (K : ℤ) (b : TransverseC3H2)
    (n : TransverseFrequency) :
    transverseScalarCoeffCLM n (fixedSectorDivergence K b) =
      fixedSectorDivergenceCoeff K n (transverseH2Embedding b) := by
  have hsum : ∀ j : Fin 2,
      transverseScalarCoeffCLM n
          (transverseCoordL2 j.castSucc (transverseDerivFromH2 j b)) =
        (2 * Real.pi * Complex.I * (n j : ℂ)) *
          transverseCoeffCLM n j.castSucc (transverseH2Embedding b) :=
    fun j => transverseCoeffCLM_transverseDerivFromH2 j b n j.castSucc
  rw [fixedSectorDivergence_apply, map_add, map_sum, map_smul, smul_eq_mul,
    fixedSectorDivergenceCoeff_apply, Finset.sum_congr rfl (fun j _ => hsum j)]
  rfl

/-! ## The sector form of the transport--stretching divergence identity -/

/-- The product frequency energy at axial index `K` splits off the axial symbol `(2πK)²`. -/
theorem productFrequencyEnergy_eq_transverse_add (n : TransverseFrequency) (K : ℤ) :
    productFrequencyEnergy n K = transverseFrequencyEnergy n + (2 * Real.pi * K) ^ 2 := by
  unfold productFrequencyEnergy transverseFrequencyEnergy
  ring

/--
**The transport--stretching divergence identity in one axial sector** (the paper's
distributional curl identity in the proof of `lem:axial-recovery`, read at the axial frequency
`K`).  For a
divergence-free `x₃`-independent `W^{1,∞}` velocity `u` and a transverse
`H²` amplitude `b`, the sector divergence symbol of the reduced induction action is

`div⊥ᴷ(A₃ b)(n) = -ε(4π²|n|² + (2πK)²) div⊥ᴷ b(n) - div⊥ᴷ(u · div⊥ᴷ b)(n)`.

The proof applies the proved product identity
`productInductionLowerField_add_velocityDiv_eq_weakCurl` (the curl representation of the
transport-stretching bracket) to `V = e^{2πiKx₃} b` and reads the result at the axial
frequency `K`; no derivative of `u` is taken twice.
-/
theorem fixedSectorDivergenceCoeff_reducedInductionAction
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u) (ε : ℝ) (K : ℤ)
    (b : TransverseC3H2) (n : TransverseFrequency) :
    fixedSectorDivergenceCoeff K n (reducedInductionAction u ε K b) =
      -(ε : ℂ) * ((transverseFrequencyEnergy n + (2 * Real.pi * K) ^ 2 : ℝ) : ℂ) *
          fixedSectorDivergenceCoeff K n (transverseH2Embedding b) -
        fixedSectorDivergenceCoeff K n
          (transverseVelocityTimesScalar u (fixedSectorDivergence K b)) := by
  have hcurl := productInductionLowerField_add_velocityDiv_eq_weakCurl u hdiv (axialLiftH2 K b)
  have hsol : productDivergenceCoeff n K
      (productVelocityCrossWeakCurl u (axialLiftH2 K b)) = 0 := by
    rw [productDivergenceCoeff_eq]
    exact productVelocityCrossWeakCurl_solenoidal u (axialLiftH2 K b) n K
  have hlower : productDivergenceCoeff n K
        (productInductionLowerField u (axialLiftH2 K b)) =
      -productDivergenceCoeff n K
        (productVelocityTimesScalar u (productDivergenceFromH2 (axialLiftH2 K b))) := by
    have h := congrArg (productDivergenceCoeff n K) hcurl
    rw [map_add, hsol] at h
    exact eq_neg_of_add_eq_zero_left h
  have hlap : productDivergenceCoeff n K (productLaplacianFromH2 (axialLiftH2 K b)) =
      -((productFrequencyEnergy n K : ℝ) : ℂ) *
        productDivergenceCoeff n K (productH2Embedding (axialLiftH2 K b)) := by
    rw [productDivergenceCoeff_eq, productDivergenceCoeff_eq]
    exact productFrequencyDivergenceCoeff_laplacian (axialLiftH2 K b) n K
  have haction : productDivergenceCoeff n K
        (productInductionAction u ε (axialLiftH2 K b)) =
      -(ε : ℂ) * ((productFrequencyEnergy n K : ℝ) : ℂ) *
          productDivergenceCoeff n K (productH2Embedding (axialLiftH2 K b)) -
        productDivergenceCoeff n K
          (productVelocityTimesScalar u
            (productDivergenceFromH2 (axialLiftH2 K b))) := by
    rw [productInductionAction_eq_diffusion_add_lower, map_add, map_smul, hlap, hlower,
      smul_eq_mul]
    ring
  have h1 : productDivergenceCoeff n K (productInductionAction u ε (axialLiftH2 K b)) =
      fixedSectorDivergenceCoeff K n (reducedInductionAction u ε K b) := by
    rw [productInductionAction_axialLiftH2, fixedSectorInductionAction_intertwines,
      productDivergenceCoeff_axialLiftL2]
  have h2 : productDivergenceCoeff n K (productH2Embedding (axialLiftH2 K b)) =
      fixedSectorDivergenceCoeff K n (transverseH2Embedding b) := by
    rw [show productH2Embedding (axialLiftH2 K b) =
        axialLiftL2 K (transverseH2Embedding b) from rfl,
      productDivergenceCoeff_axialLiftL2]
  have h3 : productDivergenceCoeff n K
        (productVelocityTimesScalar u (productDivergenceFromH2 (axialLiftH2 K b))) =
      fixedSectorDivergenceCoeff K n
        (transverseVelocityTimesScalar u (fixedSectorDivergence K b)) := by
    rw [productDivergenceFromH2_axialLiftH2, productVelocityTimesScalar_scalarAxialLiftL2,
      productDivergenceCoeff_axialLiftL2]
  rw [h1, h2, h3, productFrequencyEnergy_eq_transverse_add] at haction
  exact haction

end

end FastDynamo
