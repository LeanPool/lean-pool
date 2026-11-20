/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WeakLeibnizVelocity

/-!
# The weighted diffusion integration by parts on the transverse torus: the core estimate

This module is the first half of the weighted-diffusion layer of §6 of the paper;
`Analysis/TransverseWeightedLeibniz.lean` is the second half and imports it.  Here
are the fibre-generic vocabulary and the weighted-diffusion estimate used in the proof
of `prop:background-resolvent`:

`Re <grad h, grad((1 + i beta)h)> >= ‖grad h‖₂² - ∫ |grad beta| |h| |grad h| dy`
(the estimate of the diffusion term `I₁` of `eq:background-testing`),

for a real `beta` in `W^{1,infty}(T²)` and `h` in `H²(T²)`, together with the Young absorption

`eps ∫ |grad beta| |h| |grad h| <= (eps/4) ‖grad h‖₂² + eps ‖grad beta‖_infty² ‖h‖₂²`

that follows it in the estimate of `I₁` and enters `eq:background-coercivity`.

The companion identities for the remaining terms of the weighted form `a_z(h, (1 + i beta)h)`,
the transport term and the three bridges consumed by the §6 assembly are in
`Analysis/TransverseWeightedLeibniz.lean`.

## Conventions

Mathlib's inner product is conjugate-linear in its **first** slot, while the paper's is
linear in its first slot.  Consequently the paper's pairing `a_z(h, phi) = <(z - A)h, phi>` is
`inner ℂ phi ((z - A)h)` here, and every statement below pairs the **test field**
`(1 + i beta)h` in the first slot with the operator output in the second.  Real parts are
conjugation-symmetric, so the orientation is immaterial for the coercivity estimate.

The estimates are *fibre-blind*: only the scalar coefficient `beta`, the pointwise norms `|h|`,
`|grad h|` and the `L²` pairing enter.  They are therefore stated on the fibre-generic spaces
`TransverseVecL2 iota` and `TransverseVecH2 iota` of `FastDynamo/Fourier/PeriodicH2.lean` for an
arbitrary finite fibre index `iota`.

## The scalar multiplier type

The background multiplier `beta_n` of `eq:background-multiplier`
is a **scalar** real `W^{1,infty}(T²;ℝ)` function, while the
repository's bundled `TransverseRealW1Inf` is a *vector* `W^{1,infty}` field.  We therefore
introduce the scalar graph `TransverseScalarW1Inf` (value, two essentially bounded Fourier weak
derivatives, reality of the value).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Fibre-generic transverse Fourier weak derivatives

`Analysis/PeriodicWeakDerivative.lean` fixes the fibre of its weak-derivative
predicate at `Fin 3`.  §§5–7 of the paper work on `L²(T²;ℂ²)`, so the same predicate is
restated here for an arbitrary finite fibre `ι`; at `ι = Fin 3` it is
definitionally the predicate of that module.
-/

omit [DecidableEq ι] in
/-- `df` is the `j`-th periodic weak derivative of `f : TransverseVecL2 ι`,
expressed by the equivalent Fourier-coefficient characterization.  This is the
fibre-generic form of `HasTransverseFourierDerivative`. -/
def HasTransverseVecFourierDerivative (j : Fin 2)
    (f df : TransverseVecL2 ι) : Prop :=
  ∀ n i, transverseCoeffCLM n i df =
    (2 * Real.pi * Complex.I * (n j : ℂ)) *
      transverseCoeffCLM n i f

/-- The bounded derivative synthesized from a transverse `H²` certificate is the
periodic Fourier weak derivative of its physical field, at any finite fibre. -/
theorem transverseVecDerivFromH2_hasFourierDerivative (j : Fin 2)
    (b : TransverseVecH2 ι) :
    HasTransverseVecFourierDerivative j (transverseH2Embedding b)
      (transverseVecDerivFromH2 ι j b) := by
  intro n i
  exact transverseCoeffCLM_transverseDerivFromH2 j b n i

/-! ## Fibre-generic scalar multipliers

`Analysis/Holder.lean` introduces `scalarVectorMulTransverseVec ι` but names its
pointwise representative and its Hölder bound only at the fibres `Fin 2` and
`Fin 3`.  The two fibre-generic forms are recorded here. -/

omit [DecidableEq ι] in
/-- The product of a transverse scalar `L∞` factor with a transverse
`ℂ^ι`-valued `L²` field is represented almost everywhere by the pointwise
product `x ↦ a x • f x`. -/
theorem scalarVectorMulTransverseVec_coe_ae (a : TransverseScalarLInf)
    (f : TransverseVecL2 ι) :
    (scalarVectorMulTransverseVec ι a f : TransverseTorus → EuclideanSpace ℂ ι)
      =ᵐ[transverseMeasure] fun x ↦ a x • f x :=
  scalarVectorMulL2_coe_ae transverseMeasure a f

omit [DecidableEq ι] in
/-- Hölder's inequality for the fibre-generic transverse scalar-vector
product. -/
theorem norm_scalarVectorMulTransverseVec_apply_le (a : TransverseScalarLInf)
    (f : TransverseVecL2 ι) :
    ‖scalarVectorMulTransverseVec ι a f‖ ≤ ‖a‖ * ‖f‖ :=
  norm_scalarVectorMulL2_apply_le transverseMeasure a f

/-! ## Real scalar `L∞` coefficients -/

/-- An essentially bounded complex transverse scalar coefficient is real-valued
almost everywhere.  This is the transverse-torus counterpart of
`IsRealProductScalarLInf`. -/
def IsRealTransverseScalarLInf (a : TransverseScalarLInf) : Prop :=
  ∀ᵐ x ∂transverseMeasure, starRingEnd ℂ (a x) = a x

/-- Every scalar coordinate of a bundled real `W^{1,∞}` velocity is real-valued
almost everywhere. -/
theorem transverseW1InfComplexValueCoordLInf_isReal
    (u : TransverseRealW1Inf) (i : Fin 3) :
    IsRealTransverseScalarLInf (transverseW1InfComplexValueCoordLInf i u) := by
  have hcoord := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
    (transverseW1InfComplexValueLInf u)
  have hcomp := transverseW1InfComplexValueLInf_coe_ae u
  filter_upwards [hcoord, hcomp] with y hc hv
  change ((transverseCoordLInf i
    (transverseW1InfComplexValueLInf u) : TransverseScalarLInf) :
      TransverseTorus → ℂ) y = _ at hc
  change starRingEnd ℂ
      (((transverseCoordLInf i
        (transverseW1InfComplexValueLInf u) : TransverseScalarLInf) :
          TransverseTorus → ℂ) y) =
    (((transverseCoordLInf i
      (transverseW1InfComplexValueLInf u) : TransverseScalarLInf) :
        TransverseTorus → ℂ) y)
  rw [hc, hv]
  simp

/-! ## Scalar periodic `W^{1,∞}` -/

/--
Real periodic `W^{1,∞}(T²;ℝ)` scalars, bundled as the essentially bounded
complex value together with its two essentially bounded Fourier weak
derivatives and the reality of the value.

This is the type of the background multiplier `β_n` of
`eq:background-multiplier`; `|β_n| ≤ 1` is
recorded downstream as `‖value‖ ≤ 1`, and `‖∇β_n‖_∞` as `gradSupNormSq`.
-/
structure TransverseScalarW1Inf where
  /-- The essentially bounded complex value field, almost everywhere real. -/
  value : TransverseScalarLInf
  /-- The two essentially bounded transverse Fourier weak derivatives. -/
  grad : Fin 2 → TransverseScalarLInf
  /-- The value field is real-valued almost everywhere. -/
  value_isReal : IsRealTransverseScalarLInf value
  /-- Each stored gradient component is the corresponding Fourier weak
  derivative of the value field. -/
  hasFourierDeriv : ∀ j : Fin 2,
    HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 value) (transverseScalarLInfToL2 (grad j))

/-- `Σ_j ‖∂_j β‖_∞²`, an upper bound for the squared essential supremum
`‖ |∇β| ‖_∞²` of the Euclidean length of the gradient (the two agree exactly
when the component suprema are attained together, and in general only
`‖ |∇β| ‖_∞² ≤ Σ_j ‖∂_j β‖_∞²` holds).  It is the form in which the Young
absorption in the estimate of `I₁` (proof of `prop:background-resolvent`) uses it, and it
appears only on the larger side of upper bounds, so the inequality is in the safe direction; the
background layer supplies `ε · gradSupNormSq ≤ C² δ₊ d(K₀)²`, a factor-`√2` strengthening of
`eq:background-multiplier-bounds`. -/
def TransverseScalarW1Inf.gradSupNormSq (β : TransverseScalarW1Inf) : ℝ :=
  ∑ j : Fin 2, ‖β.grad j‖ ^ 2

/-! ## Transverse Fourier partial sums -/

/-- The Hilbert-basis representation coefficients coincide with the values of
the transverse scalar Fourier analysis map. -/
lemma transverseScalarFourierBasis_repr_apply
    (f : TransverseScalarL2) (n : TransverseFrequency) :
    transverseScalarFourierBasis.repr f n = transverseScalarCoeffCLM n f := rfl

/-- The finite Fourier partial sum of `f` over a finite transverse frequency
set, as a trigonometric polynomial. -/
def transverseFourierPartial (f : TransverseScalarL2)
    (s : Finset TransverseFrequency) : TransverseTrigPolynomial :=
  ∑ n ∈ s, Finsupp.single n (transverseScalarCoeffCLM n f)

/-- Synthesis of the Fourier partial sum is the finite sum of basis vectors. -/
theorem transverseTrigPolynomialToL2_fourierPartial
    (f : TransverseScalarL2) (s : Finset TransverseFrequency) :
    transverseTrigPolynomialToL2 (transverseFourierPartial f s) =
      ∑ n ∈ s, transverseScalarCoeffCLM n f • transverseMonomialL2 n := by
  simp [transverseFourierPartial]

/-- Transverse Fourier partial sums converge in scalar `L²`. -/
theorem transverseFourierPartial_tendsto (f : TransverseScalarL2) :
    Filter.Tendsto
      (fun s : Finset TransverseFrequency =>
        transverseTrigPolynomialToL2 (transverseFourierPartial f s))
      (SummationFilter.unconditional TransverseFrequency).filter (nhds f) := by
  have h := transverseScalarFourierBasis.hasSum_repr f
  change Filter.Tendsto
    (fun s : Finset TransverseFrequency =>
      ∑ n ∈ s, transverseScalarFourierBasis.repr f n •
        transverseScalarFourierBasis n)
    (SummationFilter.unconditional TransverseFrequency).filter (nhds f) at h
  convert h using 1
  funext s
  rw [transverseTrigPolynomialToL2_fourierPartial]
  apply Finset.sum_congr rfl
  intro n hn
  rw [transverseScalarFourierBasis_repr_apply]
  rfl

/-- Differentiating a Fourier partial sum of `f` gives the Fourier partial sum
of its weak derivative, over the same finite frequency set. -/
theorem transverseTrigDerivative_fourierPartial
    {j : Fin 2} {f df : TransverseScalarL2}
    (h : HasTransverseScalarFourierDerivative j f df)
    (s : Finset TransverseFrequency) :
    transverseTrigPolynomialDeriv j (transverseFourierPartial f s) =
      transverseFourierPartial df s := by
  rw [transverseFourierPartial, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [transverseTrigPolynomialDeriv_single, h n]
  ext q
  by_cases hqn : q = n
  · subst q
    rw [Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_same]
    simp only [smul_eq_mul]
    ring
  · simp [hqn]

/-- The derivatives of the Fourier partial sums converge to the weak
derivative. -/
theorem transverseFourierPartial_deriv_tendsto
    {j : Fin 2} {f df : TransverseScalarL2}
    (h : HasTransverseScalarFourierDerivative j f df) :
    Filter.Tendsto
      (fun s : Finset TransverseFrequency =>
        transverseTrigPolynomialToL2
          (transverseTrigPolynomialDeriv j (transverseFourierPartial f s)))
      (SummationFilter.unconditional TransverseFrequency).filter (nhds df) := by
  convert transverseFourierPartial_tendsto df using 1
  funext s
  rw [transverseTrigDerivative_fourierPartial h s]

/-- The transverse scalar Fourier weak-derivative graph is closed in `L² × L²`
along an arbitrary filter. -/
theorem HasTransverseScalarFourierDerivative.closed_of_tendsto_filter
    {α : Type*} {l : Filter α} [l.NeBot] {j : Fin 2}
    {f df : TransverseScalarL2} {fseq dfseq : α → TransverseScalarL2}
    (hseq : ∀ r, HasTransverseScalarFourierDerivative j (fseq r) (dfseq r))
    (hf : Filter.Tendsto fseq l (nhds f))
    (hdf : Filter.Tendsto dfseq l (nhds df)) :
    HasTransverseScalarFourierDerivative j f df := by
  intro n
  have hleft : Filter.Tendsto
      (fun r => transverseScalarCoeffCLM n (dfseq r)) l
      (nhds (transverseScalarCoeffCLM n df)) :=
    ((transverseScalarCoeffCLM n).continuous.tendsto df).comp hdf
  have hright : Filter.Tendsto
      (fun r => transverseFourierDerivMultiplier j n *
        transverseScalarCoeffCLM n (fseq r)) l
      (nhds (transverseFourierDerivMultiplier j n *
        transverseScalarCoeffCLM n f)) :=
    tendsto_const_nhds.mul
      (((transverseScalarCoeffCLM n).continuous.tendsto f).comp hf)
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Filter.Eventually.of_forall fun r => (hseq r n).symm)

/-! ## The weak Leibniz rule on the transverse torus -/

/-- **Weak Leibniz rule**, scalar transverse form: multiplication by a scalar
`W^{1,∞}` coefficient maps the periodic `L²` weak-derivative graph to itself,
with the exact product formula `∂_j(a f) = (∂_j a) f + a ∂_j f`.  This is the
transverse-torus counterpart of `hasProductFlatDeriv_scalarMul` and is what
makes `(1 + iβ)h` an admissible test field in `𝔞_z`. -/
theorem hasTransverseScalarDeriv_scalarMulTransverse
    {j : Fin 2} {a da : TransverseScalarLInf}
    (ha : HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 a) (transverseScalarLInfToL2 da))
    {f df : TransverseScalarL2}
    (hf : HasTransverseScalarFourierDerivative j f df) :
    HasTransverseScalarFourierDerivative j
      (scalarMulTransverse a f)
      (scalarMulTransverse da f + scalarMulTransverse a df) := by
  apply HasTransverseScalarFourierDerivative.closed_of_tendsto_filter
    (l := (SummationFilter.unconditional TransverseFrequency).filter)
    (fseq := fun s : Finset TransverseFrequency =>
      scalarMulTransverse a
        (transverseTrigPolynomialToL2 (transverseFourierPartial f s)))
    (dfseq := fun s : Finset TransverseFrequency =>
      scalarMulTransverse da
          (transverseTrigPolynomialToL2 (transverseFourierPartial f s)) +
        scalarMulTransverse a
          (transverseTrigPolynomialToL2
            (transverseTrigPolynomialDeriv j (transverseFourierPartial f s))))
  · intro s
    exact hasDeriv_scalarMul_trig ha (transverseFourierPartial f s)
  · exact ((scalarMulTransverse a).continuous.tendsto f).comp
      (transverseFourierPartial_tendsto f)
  · exact (((scalarMulTransverse da).continuous.tendsto f).comp
        (transverseFourierPartial_tendsto f)).add
      (((scalarMulTransverse a).continuous.tendsto df).comp
        (transverseFourierPartial_deriv_tendsto hf))

omit [DecidableEq ι] in
/-- Multiplication by a scalar `L∞` coefficient acts componentwise on
vector-valued `L²` fields. -/
private theorem coordL2_scalarVectorMulTransverse
    (a : TransverseScalarLInf) (f : TransverseVecL2 ι) (i : ι) :
    transverseCoordL2 i (scalarVectorMulTransverseVec ι a f) =
      scalarMulTransverse a (transverseCoordL2 i f) := by
  apply Lp.ext
  filter_upwards [
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
      (scalarVectorMulTransverseVec ι a f),
    scalarVectorMulTransverseVec_coe_ae a f,
    scalarMulTransverse_coe_ae a (transverseCoordL2 i f),
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL f]
      with x hcoord hmul hscalar hfcoord
  have hcoord' :
      (transverseCoordL2 i (scalarVectorMulTransverseVec ι a f) :
        TransverseTorus → ℂ) x =
        (EuclideanSpace.proj (𝕜 := ℂ) i)
          ((scalarVectorMulTransverseVec ι a f :
            TransverseTorus → EuclideanSpace ℂ ι) x) :=
    hcoord
  have hfcoord' :
      (transverseCoordL2 i f : TransverseTorus → ℂ) x =
        (EuclideanSpace.proj (𝕜 := ℂ) i) (f x) := hfcoord
  rw [hcoord', hmul, hscalar, hfcoord']
  rfl

omit [DecidableEq ι] in
/-- The vector Fourier coefficient functional is the scalar functional applied
to the corresponding coordinate. -/
private theorem transverseCoeffCLM_eq_scalarCoeff (n : TransverseFrequency)
    (i : ι) (f : TransverseVecL2 ι) :
    transverseCoeffCLM n i f =
      transverseScalarCoeffCLM n (transverseCoordL2 i f) := rfl

omit [DecidableEq ι] in
/-- Each coordinate of a vector Fourier weak derivative is the scalar Fourier
weak derivative of that coordinate. -/
private theorem hasScalarDeriv_coord {j : Fin 2} {f df : TransverseVecL2 ι}
    (hf : HasTransverseVecFourierDerivative j f df) (i : ι) :
    HasTransverseScalarFourierDerivative j (transverseCoordL2 i f)
      (transverseCoordL2 i df) := by
  intro n
  have h := hf n i
  rw [transverseCoeffCLM_eq_scalarCoeff, transverseCoeffCLM_eq_scalarCoeff] at h
  simp only [transverseFourierDerivMultiplier]
  exact h

omit [DecidableEq ι] in
/-- Conversely, coordinatewise scalar Fourier weak derivatives assemble into a
vector Fourier weak derivative. -/
private theorem hasVectorDeriv_of_coord {j : Fin 2} {f df : TransverseVecL2 ι}
    (h : ∀ i : ι, HasTransverseScalarFourierDerivative j
      (transverseCoordL2 i f) (transverseCoordL2 i df)) :
    HasTransverseVecFourierDerivative j f df := by
  intro n i
  have hn := h i n
  simp only [transverseFourierDerivMultiplier] at hn
  rw [transverseCoeffCLM_eq_scalarCoeff, transverseCoeffCLM_eq_scalarCoeff]
  exact hn

omit [DecidableEq ι] in
/-- **Weak Leibniz rule**, vector transverse form. -/
theorem hasTransverseFourierDerivative_scalarVectorMul
    {j : Fin 2} {a da : TransverseScalarLInf}
    (ha : HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 a) (transverseScalarLInfToL2 da))
    {f df : TransverseVecL2 ι} (hf : HasTransverseVecFourierDerivative j f df) :
    HasTransverseVecFourierDerivative j
      (scalarVectorMulTransverseVec ι a f)
      (scalarVectorMulTransverseVec ι da f + scalarVectorMulTransverseVec ι a df) := by
  refine hasVectorDeriv_of_coord (fun i ↦ ?_)
  have hmain := hasTransverseScalarDeriv_scalarMulTransverse ha
    (hasScalarDeriv_coord hf i)
  intro n
  rw [map_add, coordL2_scalarVectorMulTransverse,
    coordL2_scalarVectorMulTransverse, coordL2_scalarVectorMulTransverse]
  exact hmain n

/-! ## Linearity of the Fourier weak-derivative relation -/

omit [DecidableEq ι] in
/-- The vector Fourier weak-derivative relation is additive. -/
theorem hasTransverseFourierDerivative_add {j : Fin 2}
    {f df g dg : TransverseVecL2 ι}
    (hf : HasTransverseVecFourierDerivative j f df)
    (hg : HasTransverseVecFourierDerivative j g dg) :
    HasTransverseVecFourierDerivative j (f + g) (df + dg) := by
  intro n i
  simp only [map_add, hf n i, hg n i]
  ring

omit [DecidableEq ι] in
/-- The vector Fourier weak-derivative relation is homogeneous. -/
theorem hasTransverseFourierDerivative_smul {j : Fin 2} (c : ℂ)
    {f df : TransverseVecL2 ι} (hf : HasTransverseVecFourierDerivative j f df) :
    HasTransverseVecFourierDerivative j (c • f) (c • df) := by
  intro n i
  simp only [map_smul, smul_eq_mul, hf n i]
  ring

/-! ## Periodic integration by parts against a weak `H¹` test field -/

/-- Scalar Fourier integration by parts against the periodic Laplacian
multiplier.  Both fields are only required to carry `L²` Fourier weak
derivatives; no `H¹` graph is needed. -/
private theorem inner_scalarLaplacian_eq_neg_sum
    {φ : TransverseScalarL2} {dφ : Fin 2 → TransverseScalarL2}
    (hφ : ∀ j, HasTransverseScalarFourierDerivative j φ (dφ j))
    {g lap : TransverseScalarL2} {dg : Fin 2 → TransverseScalarL2}
    (hg : ∀ j, HasTransverseScalarFourierDerivative j g (dg j))
    (hlap : ∀ n, transverseScalarCoeffCLM n lap =
      -(transverseFrequencyEnergy n : ℂ) * transverseScalarCoeffCLM n g) :
    inner ℂ φ lap = -∑ j : Fin 2, inner ℂ (dφ j) (dg j) := by
  rw [← transverseScalarFourierAnalysis.inner_map_map]
  simp_rw [← transverseScalarFourierAnalysis.inner_map_map]
  simp only [Fin.sum_univ_two]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← (lp.summable_inner
      (transverseScalarFourierAnalysis (dφ (0 : Fin 2)))
      (transverseScalarFourierAnalysis (dg (0 : Fin 2)))).tsum_add
    (lp.summable_inner
      (transverseScalarFourierAnalysis (dφ (1 : Fin 2)))
      (transverseScalarFourierAnalysis (dg (1 : Fin 2))))]
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  rw [show transverseScalarFourierAnalysis φ n =
      transverseScalarCoeffCLM n φ from rfl,
    show transverseScalarFourierAnalysis lap n =
      transverseScalarCoeffCLM n lap from rfl,
    show transverseScalarFourierAnalysis (dφ (0 : Fin 2)) n =
      transverseScalarCoeffCLM n (dφ (0 : Fin 2)) from rfl,
    show transverseScalarFourierAnalysis (dφ (1 : Fin 2)) n =
      transverseScalarCoeffCLM n (dφ (1 : Fin 2)) from rfl,
    show transverseScalarFourierAnalysis (dg (0 : Fin 2)) n =
      transverseScalarCoeffCLM n (dg (0 : Fin 2)) from rfl,
    show transverseScalarFourierAnalysis (dg (1 : Fin 2)) n =
      transverseScalarCoeffCLM n (dg (1 : Fin 2)) from rfl,
    hlap n, hφ (0 : Fin 2) n, hφ (1 : Fin 2) n, hg (0 : Fin 2) n,
    hg (1 : Fin 2) n]
  unfold transverseFrequencyEnergy transverseFourierDerivMultiplier
  simp only [Fin.sum_univ_two, RCLike.inner_apply]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast,
    map_ofNat]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Periodic integration by parts against a weak `H¹` test field.**
If `φ ∈ L²(T²;ℂ³)` has `L²` transverse Fourier weak derivatives `dφ j`, and
`h ∈ H²(T²;ℂ³)`, then `⟨φ, Δ_⊥ h⟩ = -Σ_j ⟨∂_j φ, ∂_j h⟩`.

This is the exact identity behind the integration by parts in the proof of
`prop:background-resolvent`, where the paper pairs `(z - A^bg_{ε,n})h` with `(1 + iβ_n)h` and
obtains the diffusion term `I₁ = ε Re ⟨∇_⊥ h, ∇_⊥((1 + iβ_n)h)⟩` of `eq:background-testing`. -/
theorem inner_transverseLaplacianFromH2_eq_neg_sum
    {φ : TransverseVecL2 ι} {dφ : Fin 2 → TransverseVecL2 ι}
    (hφ : ∀ j, HasTransverseVecFourierDerivative j φ (dφ j))
    (h : TransverseVecH2 ι) :
    inner ℂ φ (transverseVecLaplacianFromH2 ι h) =
      -∑ j : Fin 2, inner ℂ (dφ j) (transverseVecDerivFromH2 ι j h) := by
  rw [inner_transverseC3L2_eq_sum_coord]
  have hcoord : ∀ i : ι,
      inner ℂ (transverseCoordL2 i φ)
          (transverseCoordL2 i (transverseVecLaplacianFromH2 ι h)) =
        -∑ j : Fin 2, inner ℂ (transverseCoordL2 i (dφ j))
          (transverseCoordL2 i (transverseVecDerivFromH2 ι j h)) := by
    intro i
    refine inner_scalarLaplacian_eq_neg_sum
      (fun j ↦ hasScalarDeriv_coord (hφ j) i)
      (g := transverseCoordL2 i (transverseH2Embedding h))
      (dg := fun j ↦ transverseCoordL2 i (transverseVecDerivFromH2 ι j h))
      (fun j ↦ hasScalarDeriv_coord
        (transverseVecDerivFromH2_hasFourierDerivative j h) i)
      (fun n ↦ ?_)
    rw [← transverseCoeffCLM_eq_scalarCoeff, ← transverseCoeffCLM_eq_scalarCoeff]
    exact transverseCoeffCLM_transverseLaplacianFromH2 h n i
  rw [Finset.sum_congr rfl (fun i _ ↦ hcoord i), Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact (inner_transverseC3L2_eq_sum_coord _ _).symm

/-! ## Real scalar multipliers are self-adjoint -/

omit [DecidableEq ι] in
/-- Multiplication by a real `L∞` scalar is self-adjoint on vector-valued
transverse `L²`. -/
theorem inner_scalarVectorMulTransverse_real_selfAdjoint
    {a : TransverseScalarLInf} (ha : IsRealTransverseScalarLInf a)
    (f g : TransverseVecL2 ι) :
    inner ℂ f (scalarVectorMulTransverseVec ι a g) =
      inner ℂ (scalarVectorMulTransverseVec ι a f) g := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarVectorMulTransverseVec_coe_ae a g,
    scalarVectorMulTransverseVec_coe_ae a f, ha] with x hg hf hreal
  rw [hg, hf]
  rw [inner_smul_right, inner_smul_left, hreal]

omit [DecidableEq ι] in
/-- The quadratic pairing of a real `L∞` scalar multiplier is real: it is the
integral `∫ a |f|²`. -/
theorem im_inner_scalarVectorMulTransverse_self_eq_zero
    {a : TransverseScalarLInf} (ha : IsRealTransverseScalarLInf a)
    (f : TransverseVecL2 ι) :
    (inner ℂ (scalarVectorMulTransverseVec ι a f) f).im = 0 := by
  have h1 := inner_scalarVectorMulTransverse_real_selfAdjoint ha f f
  have h2 : (starRingEnd ℂ) (inner ℂ (scalarVectorMulTransverseVec ι a f) f) =
      inner ℂ f (scalarVectorMulTransverseVec ι a f) :=
    inner_conj_symm _ _
  rw [h1] at h2
  exact Complex.conj_eq_iff_im.mp h2

omit [DecidableEq ι] in
/-- The same pairing with the multiplier on the right. -/
theorem im_inner_self_scalarVectorMulTransverse_eq_zero
    {a : TransverseScalarLInf} (ha : IsRealTransverseScalarLInf a)
    (f : TransverseVecL2 ι) :
    (inner ℂ f (scalarVectorMulTransverseVec ι a f)).im = 0 := by
  rw [inner_scalarVectorMulTransverse_real_selfAdjoint ha f f]
  exact im_inner_scalarVectorMulTransverse_self_eq_zero ha f

omit [DecidableEq ι] in
/-- The real part of the self-pairing is the squared norm. -/
theorem re_inner_self (f : TransverseVecL2 ι) :
    (inner ℂ f f).re = ‖f‖ ^ 2 := by
  have h : inner ℂ f f = ((‖f‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K f
  rw [h, ← Complex.ofReal_pow, Complex.ofReal_re]

omit [DecidableEq ι] in
/-- The self-pairing is real. -/
theorem im_inner_self (f : TransverseVecL2 ι) :
    (inner ℂ f f).im = 0 := by
  have h : inner ℂ f f = ((‖f‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K f
  rw [h, ← Complex.ofReal_pow, Complex.ofReal_im]

/-! ## The weighted test field `(1 + iβ)h` -/

omit [DecidableEq ι] in
/-- The weighted test field `(1 + iβ)h` used throughout the proof of
`prop:background-resolvent`: it is the test field of `eq:background-testing` and of the
diffusion estimate for `I₁`. -/
def weightedTransverseState (β : TransverseScalarW1Inf) (h : TransverseVecH2 ι) :
    TransverseVecL2 ι :=
  transverseH2Embedding h +
    Complex.I • scalarVectorMulTransverseVec ι β.value (transverseH2Embedding h)

/-- The transverse weak derivative of the weighted test field,
`∂_j((1 + iβ)h) = ∂_j h + i((∂_j β) h + β ∂_j h)`. -/
def weightedTransverseStateDeriv (β : TransverseScalarW1Inf)
    (h : TransverseVecH2 ι) (j : Fin 2) : TransverseVecL2 ι :=
  transverseVecDerivFromH2 ι j h +
    Complex.I •
      (scalarVectorMulTransverseVec ι (β.grad j) (transverseH2Embedding h) +
        scalarVectorMulTransverseVec ι β.value (transverseVecDerivFromH2 ι j h))

/-- **Weak Leibniz rule for the weighted test field.**  `(1 + iβ)h` lies in the
periodic weak-derivative graph with the stated derivative; this is what makes it
an admissible test field in `𝔞_z`. -/
theorem hasTransverseFourierDerivative_weightedTransverseState
    (β : TransverseScalarW1Inf) (h : TransverseVecH2 ι) (j : Fin 2) :
    HasTransverseVecFourierDerivative j (weightedTransverseState β h)
      (weightedTransverseStateDeriv β h j) := by
  refine hasTransverseFourierDerivative_add
    (transverseVecDerivFromH2_hasFourierDerivative j h)
    (hasTransverseFourierDerivative_smul Complex.I ?_)
  exact hasTransverseFourierDerivative_scalarVectorMul (β.hasFourierDeriv j)
    (transverseVecDerivFromH2_hasFourierDerivative j h)

/-! ## The weighted diffusion inequality -/

/-- The transverse gradient energy `‖∇_⊥ h‖₂² = Σ_j ‖∂_j h‖₂²`. -/
def transverseGradientEnergy (h : TransverseVecH2 ι) : ℝ :=
  ∑ j : Fin 2, ‖transverseVecDerivFromH2 ι j h‖ ^ 2

/-- The gradient energy is nonnegative. -/
theorem transverseGradientEnergy_nonneg (h : TransverseVecH2 ι) :
    0 ≤ transverseGradientEnergy h :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/--
The weighted gradient defect `Σ_j ‖(∂_j β) h‖₂ ‖∂_j h‖₂`.

The exact defect produced by the integration by parts is `Σ_j Im ⟨(∂_j β)h,
∂_j h⟩`.  The paper majorises it by `∫_{T²} |∇_⊥ β| |h| |∇_⊥ h| dy`
(estimate of `I₁` in the proof of `prop:background-resolvent`), that is by pointwise
Cauchy–Schwarz over `j` followed by integration; here it is majorised instead by
`Σ_j ‖(∂_j β) h‖₂ ‖∂_j h‖₂`, that is by Cauchy–Schwarz in `L²`, one `j` at a
time.  **The two majorants are incomparable** — either can be the smaller, for
instance when one of `∂_1 β`, `∂_2 h` vanishes identically.  Both are absorbed
by the same Young inequality, which is all §6 uses, so nothing
downstream depends on the choice.
-/
def transverseWeightedGradientDefect (β : TransverseScalarW1Inf)
    (h : TransverseVecH2 ι) : ℝ :=
  ∑ j : Fin 2,
    ‖scalarVectorMulTransverseVec ι (β.grad j) (transverseH2Embedding h)‖ *
      ‖transverseVecDerivFromH2 ι j h‖

omit [DecidableEq ι] in
/-- One direction of the elementary weighted estimate: for `c` the derivative
`∂_j h`, `a` the defect field `(∂_j β) h` and `b` a field whose quadratic
pairing with `c` is real, `Re ⟨c + i(a + b), c⟩ ≥ ‖c‖² - ‖a‖ ‖c‖`. -/
private theorem re_inner_weighted_ge {a b c : TransverseVecL2 ι}
    (hb : (inner ℂ b c).im = 0) :
    ‖c‖ ^ 2 - ‖a‖ * ‖c‖ ≤ (inner ℂ (c + Complex.I • (a + b)) c).re := by
  have hcc : (inner ℂ c c).re = ‖c‖ ^ 2 := re_inner_self c
  have hexp : (inner ℂ (c + Complex.I • (a + b)) c).re =
      (inner ℂ c c).re + (inner ℂ a c).im + (inner ℂ b c).im := by
    simp only [inner_add_left, inner_smul_left, Complex.conj_I]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  have hbound : -(‖a‖ * ‖c‖) ≤ (inner ℂ a c).im := by
    have h1 : |(inner ℂ a c).im| ≤ ‖inner ℂ a c‖ := Complex.abs_im_le_norm _
    have h2 : ‖inner ℂ a c‖ ≤ ‖a‖ * ‖c‖ := norm_inner_le_norm _ _
    have h3 := abs_le.mp (le_trans h1 h2)
    linarith [h3.1]
  rw [hexp, hcc, hb]
  linarith

/-- **The weighted diffusion integration by parts**, the one new analytic
estimate of §6 (estimate of `I₁` in the proof of `prop:background-resolvent`):

`Re ⟨(1 + iβ)h, -Δ_⊥ h⟩ ≥ ‖∇_⊥ h‖₂² - Σ_j ‖(∂_j β) h‖₂ ‖∂_j h‖₂`,

where the subtracted term is the `L²` Cauchy–Schwarz majorant of the exact
defect `Σ_j Im ⟨(∂_j β)h, ∂_j h⟩`; see `transverseWeightedGradientDefect` for
why it is *not* comparable with the paper's `∫ |∇_⊥ β| |h| |∇_⊥ h|`, and
why that is immaterial.  Only the reality of `β` and its `L∞` weak gradient
enter; the estimate is blind to the fibre. -/
theorem re_inner_weightedTransverseState_neg_laplacian_ge
    (β : TransverseScalarW1Inf) (h : TransverseVecH2 ι) :
    transverseGradientEnergy h - transverseWeightedGradientDefect β h ≤
      (inner ℂ (weightedTransverseState β h)
        (-transverseVecLaplacianFromH2 ι h)).re := by
  have hibp := inner_transverseLaplacianFromH2_eq_neg_sum
    (hasTransverseFourierDerivative_weightedTransverseState β h) h
  have hneg : inner ℂ (weightedTransverseState β h)
      (-transverseVecLaplacianFromH2 ι h) =
      ∑ j : Fin 2, inner ℂ (weightedTransverseStateDeriv β h j)
        (transverseVecDerivFromH2 ι j h) := by
    rw [inner_neg_right, hibp, neg_neg]
  rw [hneg, Complex.re_sum]
  rw [transverseGradientEnergy, transverseWeightedGradientDefect,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  exact re_inner_weighted_ge
    (im_inner_scalarVectorMulTransverse_self_eq_zero β.value_isReal
      (transverseVecDerivFromH2 ι j h))

/-! ## Hölder and Young absorption -/

/-- **Young absorption of the diffusion defect**, the Young step of the estimate of `I₁` in the
proof of `prop:background-resolvent`:

`∫ |∇β| |h| |∇h| ≤ (1/4) ‖∇h‖₂² + ‖∇β‖_∞² ‖h‖₂²`. -/
theorem transverseWeightedGradientDefect_young (β : TransverseScalarW1Inf)
    (h : TransverseVecH2 ι) :
    transverseWeightedGradientDefect β h ≤
      transverseGradientEnergy h / 4 +
        β.gradSupNormSq * ‖transverseH2Embedding h‖ ^ 2 := by
  rw [transverseWeightedGradientDefect, transverseGradientEnergy,
    TransverseScalarW1Inf.gradSupNormSq, Finset.sum_div, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hhold : ‖scalarVectorMulTransverseVec ι (β.grad j)
      (transverseH2Embedding h)‖ ≤
      ‖β.grad j‖ * ‖transverseH2Embedding h‖ :=
    norm_scalarVectorMulTransverseVec_apply_le _ _
  have hnn : (0 : ℝ) ≤ ‖scalarVectorMulTransverseVec ι (β.grad j)
      (transverseH2Embedding h)‖ := norm_nonneg _
  have hsq : ‖scalarVectorMulTransverseVec ι (β.grad j)
      (transverseH2Embedding h)‖ ^ 2 ≤
      ‖β.grad j‖ ^ 2 * ‖transverseH2Embedding h‖ ^ 2 := by
    have := mul_self_le_mul_self hnn hhold
    nlinarith [this]
  nlinarith [sq_nonneg (‖transverseVecDerivFromH2 ι j h‖ / 2 -
    ‖scalarVectorMulTransverseVec ι (β.grad j) (transverseH2Embedding h)‖), hsq]

/-- The `ε`-weighted Young absorption used in `eq:background-coercivity`:
`ε ∫ |∇β| |h| |∇h| ≤ (ε/4) ‖∇h‖₂² + ε ‖∇β‖_∞² ‖h‖₂²`. -/
theorem transverseWeightedGradientDefect_young_scaled
    (β : TransverseScalarW1Inf) (h : TransverseVecH2 ι) {ε : ℝ} (hε : 0 ≤ ε) :
    ε * transverseWeightedGradientDefect β h ≤
      ε / 4 * transverseGradientEnergy h +
        ε * (β.gradSupNormSq * ‖transverseH2Embedding h‖ ^ 2) := by
  have h1 := transverseWeightedGradientDefect_young β h
  nlinarith [h1, hε]

/-- **The weighted diffusion estimate after Young absorption.**  Combining the
integration by parts with the Young inequality gives the coercive form used in
`eq:background-coercivity` (the bound `I₁ ≥ (3ε/4) ‖∇_⊥ h‖₂² - …`):

`Re ⟨(1 + iβ)h, -Δ_⊥ h⟩ ≥ (3/4) ‖∇_⊥ h‖₂² - ‖∇_⊥ β‖_∞² ‖h‖₂²`. -/
theorem re_inner_weightedTransverseState_neg_laplacian_ge_young
    (β : TransverseScalarW1Inf) (h : TransverseVecH2 ι) :
    3 / 4 * transverseGradientEnergy h -
        β.gradSupNormSq * ‖transverseH2Embedding h‖ ^ 2 ≤
      (inner ℂ (weightedTransverseState β h)
        (-transverseVecLaplacianFromH2 ι h)).re := by
  have h1 := re_inner_weightedTransverseState_neg_laplacian_ge β h
  have h2 := transverseWeightedGradientDefect_young β h
  linarith

end

end FastDynamo
