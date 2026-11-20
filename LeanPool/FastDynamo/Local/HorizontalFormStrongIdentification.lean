/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.HorizontalFormDelta
public import LeanPool.FastDynamo.Operator.WholePlaneLocalC2
public import LeanPool.FastDynamo.Global.WholePlaneEllipticRegularity

/-!
# The form operator of the horizontal seed is the strong operator on `H²`

The proof of `prop:local-seed` in the paper: *"It remains to identify the operator
domains.  An element of the form-operator domain belongs to `H¹`.  Since `v` is smooth with
bounded derivatives, the lower-order terms belong to `L²`.  The equation therefore gives
`Δ_⊥b ∈ L²`, whence `b ∈ H²`.  The converse follows by integration by parts."*

This module proves both halves for the two-component local model at every diffusivity
`δ ≠ 0`, i.e. it identifies

* the **form** operator `A_{w,δ}` of `Local/HorizontalFormDelta.lean`
  (`HorizontalWeakForm.horizontalFormDeltaOperator N δ w`, whose domain is the maximal graph
  domain of the transport-stretching form `𝔩_{w,δ}` built from `eq:jump-sectorial-form` in
  the proof of `prop:local-seed`), with
* the **strong** operator `𝓛_δ` of `Operator/WholePlaneLocalC2.lean`
  (`horizontalLocalOperator N δ v = wholePlaneC2LocalOperator v δ N`, `eq:local-generator`),
  whose domain is `H²(ℝ²; ℂ²)` by construction.

At `δ = 1` the form is `𝔩_w` (`horizontalWeakFormDelta_one`) and the statements are repeated
for the unit-diffusivity operator `horizontalFormOperator N w` of
`Local/HorizontalFormOperator.lean`, which is what the contour machinery of
`Local/HorizontalModeContour.lean` uses.

The forward inclusion `H² ⊂ D(A_{w,δ})` is the integration by parts.  Three of its five terms are
immediate; the stretching pair
`𝔰_w(b, φ) = ∫ w_⊥·(Div_⊥ b)conj φ + ∫ w_⊥·(b·∇_⊥)conj φ`
needs the `L^∞·H¹` distributional Leibniz rule of
`Analysis/WholePlaneScalarLeibniz.lean` against the `HasWeakGradient` certificate carried by
`WholePlaneVelocityCoefficients`; this is the integration by parts of the stretching term
displayed before `eq:jump-sectorial-form`.

The converse inclusion `D(A_{w,δ}) ⊂ H²` is whole-plane elliptic regularity: the velocity terms
of the form are `L^∞ · H¹ ⊂ L²`, so a weak solution has `δΔ_⊥ b ∈ L²` and is therefore in `H²`
by the Fourier estimate `exists_wholePlaneH2_of_laplacian_eq_l2` (a step the paper leaves
implicit in "whence `b ∈ H²`").

## Contents

* Scalar coordinates of the two-component substrate: `L^∞` coordinates, the coordinate formula
  for `L^∞(ℂ²)·L²(ℂ)` products, the coordinate expansion of the `L²(ℝ²; ℂ²)` inner product,
  coordinate insertion on `H¹`, and coordinates of `C2`-valued tempered distributions.
* The `H¹`-level velocity operators and the stretching integration by parts.
* The identification `⟪𝓛_δ h, φ⟫ = -𝔩_{w,δ}(h, φ)` on `H²` (`horizontalWeakFormDelta_h2ToH1_eq`)
  and the converse inclusion `D(A_{w,δ}) ⊂ H²` (`exists_wholePlaneC2H2_of_horizontalWeak`), at
  general `δ`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

/-! ## Scalar coordinates of the two-component substrate -/

/-- Extract one scalar coordinate from a two-component whole-plane `L∞` field. -/
def wholePlaneC2CoordLInf (i : Fin 2) :
    WholePlaneC2LInf →L[ℂ] WholePlaneScalarLInf :=
  (EuclideanSpace.proj i).compLpL ∞ volume

/-- Almost-everywhere representative of a two-component `L∞` coordinate. -/
theorem wholePlaneC2CoordLInf_coe_ae (i : Fin 2) (a : WholePlaneC2LInf) :
    (wholePlaneC2CoordLInf i a : WholePlane → ℂ) =ᵐ[volume]
      fun x => (EuclideanSpace.proj i) ((a : WholePlane → C2) x) := by
  simpa only [wholePlaneC2CoordLInf] using
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
      (p := ⊤) (μ := (volume : Measure WholePlane)) a

/-- A coordinate of the horizontal projection of a three-component `L∞` coefficient is the
corresponding coordinate of the coefficient itself. -/
theorem wholePlaneC2CoordLInf_horizontalProjLInf (i : Fin 2) (a : WholePlaneC3LInf) :
    wholePlaneC2CoordLInf i (wholePlaneHorizontalProjLInf a) =
      wholePlaneCoordLInf i.castSucc a := by
  apply Lp.ext
  filter_upwards [wholePlaneC2CoordLInf_coe_ae i (wholePlaneHorizontalProjLInf a),
    wholePlaneHorizontalProjLInf_coe_ae a,
    (EuclideanSpace.proj (𝕜 := ℂ) i.castSucc).coeFn_compLpL
      (p := ⊤) (μ := (volume : Measure WholePlane)) a] with x h1 h2 h3
  rw [h1, h2]
  rw [show (wholePlaneCoordLInf i.castSucc a : WholePlane → ℂ) x =
    (EuclideanSpace.proj (𝕜 := ℂ) i.castSucc) ((a : WholePlane → C3) x) from h3]
  simp [horizontalProjPoint_apply]

/-- Taking a scalar coordinate turns multiplication of a two-component `L∞` field by a scalar
`L²` field into scalar multiplication. -/
theorem wholePlaneC2CoordL2_vectorScalarMulL2
    (a : WholePlaneC2LInf) (b : WholePlaneScalarL2) (i : Fin 2) :
    wholePlaneC2CoordL2 i (vectorScalarMulL2 (E := C2) volume a b) =
      scalarVectorMulL2 (E := ℂ) volume (wholePlaneC2CoordLInf i a) b := by
  apply Lp.ext
  have hout :
      ((wholePlaneC2CoordL2 i (vectorScalarMulL2 (E := C2) volume a b) :
          WholePlaneScalarL2) : WholePlane → ℂ) =ᵐ[volume]
        fun x => (EuclideanSpace.proj i)
          ((vectorScalarMulL2 (E := C2) volume a b : WholePlane → C2) x) := by
    simpa only [wholePlaneC2CoordL2] using
      (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
        (p := 2) (μ := (volume : Measure WholePlane))
        (vectorScalarMulL2 (E := C2) volume a b)
  filter_upwards [hout, vectorScalarMulL2_coe_ae (E := C2) volume a b,
    wholePlaneC2CoordLInf_coe_ae i a,
    scalarVectorMulL2_coe_ae (E := ℂ) volume (wholePlaneC2CoordLInf i a) b]
    with x ho hm hai hr
  rw [ho, hm, hr, hai]
  simp [smul_eq_mul, mul_comm]

/-- Coordinate expansion of the two-component whole-plane `L²` inner product. -/
theorem inner_wholePlaneC2L2_eq_sum_coord (u v : WholePlaneC2L2) :
    inner ℂ u v =
      ∑ i : Fin 2, inner ℂ (wholePlaneC2CoordL2 i u) (wholePlaneC2CoordL2 i v) := by
  rw [MeasureTheory.L2.inner_def]
  simp_rw [MeasureTheory.L2.inner_def]
  rw [← integral_finsetSum]
  swap
  · intro i _
    exact L2.integrable_inner (𝕜 := ℂ) (wholePlaneC2CoordL2 i u) (wholePlaneC2CoordL2 i v)
  apply integral_congr_ae
  have hu : ∀ i : Fin 2,
      ((wholePlaneC2CoordL2 i u : WholePlaneScalarL2) : WholePlane → ℂ) =ᵐ[volume]
        fun x => (u x) i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL u
  have hv : ∀ i : Fin 2,
      ((wholePlaneC2CoordL2 i v : WholePlaneScalarL2) : WholePlane → ℂ) =ᵐ[volume]
        fun x => (v x) i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL v
  filter_upwards [ae_all_iff.2 hu, ae_all_iff.2 hv] with x hux hvx
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hux i, hvx i]
  rfl

/-- Pairing a coordinate insertion against a two-component field extracts that coordinate. -/
theorem inner_wholePlaneScalarToC2CoordL2 (i : Fin 2)
    (u : WholePlaneScalarL2) (v : WholePlaneC2L2) :
    inner ℂ (wholePlaneScalarToC2CoordL2 i u) v = inner ℂ u (wholePlaneC2CoordL2 i v) := by
  rw [inner_wholePlaneC2L2_eq_sum_coord]
  simp only [wholePlaneC2CoordL2_scalarToC2CoordL2]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Two `C2`-valued tempered distributions agree as soon as all their scalar coordinates do. -/
theorem wholePlaneC2Tempered_ext_coord {S T : TemperedDistribution WholePlane C2}
    (h : ∀ i : Fin 2, wholePlaneC2CoordTempered i S = wholePlaneC2CoordTempered i T) :
    S = T := by
  ext f i
  exact congrArg (fun U : TemperedDistribution WholePlane ℂ => U f) (h i)

/-- Coordinate extraction commutes with the distributional Laplacian. -/
theorem wholePlaneC2CoordTempered_laplacian (i : Fin 2)
    (T : TemperedDistribution WholePlane C2) :
    wholePlaneC2CoordTempered i (Laplacian.laplacian T) =
      Laplacian.laplacian (wholePlaneC2CoordTempered i T) := by
  rw [TemperedDistribution.laplacian_eq_sum wholePlaneOrthonormalBasis,
    TemperedDistribution.laplacian_eq_sum wholePlaneOrthonormalBasis]
  simp only [map_sum, wholePlaneOrthonormalBasis_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [wholePlaneC2CoordTempered_lineDeriv, wholePlaneC2CoordTempered_lineDeriv]

/-- Coordinates of the tempered distribution attached to a coordinate insertion. -/
theorem wholePlaneC2CoordTempered_scalarToC2CoordL2 (i k : Fin 2) (a : WholePlaneScalarL2) :
    wholePlaneC2CoordTempered k
        (wholePlaneL2ToTempered C2 (wholePlaneScalarToC2CoordL2 i a)) =
      wholePlaneL2ToTempered ℂ (if i = k then a else 0) := by
  rw [wholePlaneC2CoordTempered_l2, wholePlaneC2CoordL2_scalarToC2CoordL2]

/-- Ambient first-order jet obtained by placing a scalar `H¹` jet in coordinate `i`. -/
def wholePlaneScalarToC2CoordH1Ambient (i : Fin 2) :
    WholePlaneScalarH1 →L[ℂ] WholePlaneH1Ambient C2 :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : WholePlaneJet1Index => WholePlaneC2L2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun q => q.elim
      ((wholePlaneScalarToC2CoordL2 i).comp (wholePlaneH1Embedding ℂ))
      (fun j => (wholePlaneScalarToC2CoordL2 i).comp (wholePlaneH1FirstDerivative ℂ j)))

/-- The value slot of the inserted jet. -/
@[simp] theorem wholePlaneScalarToC2CoordH1Ambient_none (i : Fin 2) (u : WholePlaneScalarH1) :
    wholePlaneScalarToC2CoordH1Ambient i u none =
      wholePlaneScalarToC2CoordL2 i (wholePlaneH1Embedding ℂ u) := rfl

/-- The `j`-th derivative slot of the inserted jet. -/
@[simp] theorem wholePlaneScalarToC2CoordH1Ambient_some (i : Fin 2) (u : WholePlaneScalarH1)
    (j : Fin 2) :
    wholePlaneScalarToC2CoordH1Ambient i u (some j) =
      wholePlaneScalarToC2CoordL2 i (wholePlaneH1FirstDerivative ℂ j u) := rfl

/-- Coordinate insertion as a bounded map from scalar weak `H¹` to two-component weak `H¹`. -/
def wholePlaneScalarToC2CoordH1 (i : Fin 2) :
    WholePlaneScalarH1 →L[ℂ] WholePlaneC2H1 :=
  (wholePlaneScalarToC2CoordH1Ambient i).codRestrict (wholePlaneH1Graph C2) (fun u => by
    rw [mem_wholePlaneH1Graph_iff]
    intro j
    simp only [wholePlaneScalarToC2CoordH1Ambient_none, wholePlaneScalarToC2CoordH1Ambient_some]
    apply wholePlaneC2Tempered_ext_coord
    intro k
    rw [wholePlaneC2CoordTempered_lineDeriv,
      wholePlaneC2CoordTempered_scalarToC2CoordL2,
      wholePlaneC2CoordTempered_scalarToC2CoordL2]
    by_cases hik : i = k
    · simp only [hik]
      exact wholePlaneH1_firstDerivative_distribution ℂ u j
    · simp only [ite_eq_right hik, map_zero]
      exact map_zero _)

/-- The `L²` value of an inserted scalar `H¹` field. -/
theorem wholePlaneH1Embedding_scalarToC2CoordH1 (i : Fin 2) (u : WholePlaneScalarH1) :
    wholePlaneH1Embedding C2 (wholePlaneScalarToC2CoordH1 i u) =
      wholePlaneScalarToC2CoordL2 i (wholePlaneH1Embedding ℂ u) := rfl

/-- The weak derivatives of an inserted scalar `H¹` field. -/
theorem wholePlaneH1FirstDerivative_scalarToC2CoordH1 (i j : Fin 2)
    (u : WholePlaneScalarH1) :
    wholePlaneH1FirstDerivative C2 j (wholePlaneScalarToC2CoordH1 i u) =
      wholePlaneScalarToC2CoordL2 i (wholePlaneH1FirstDerivative ℂ j u) := rfl

/-! ## The `H¹`-level velocity operators and the stretching integration by parts -/

namespace HorizontalWeakForm

/-- The axial transport field `iNw₃b` of `eq:local-generator`, as a bounded map on `H¹`. -/
def horizontalAxialTransport (N : ℝ) (w : WholePlaneC3LInf) :
    WholePlaneC2H1 →L[ℂ] WholePlaneC2L2 :=
  (Complex.I * (N : ℂ)) •
    (scalarVectorMulL2 (E := C2) volume (wholePlaneCoordLInf (2 : Fin 3) w)).comp
      (wholePlaneH1Embedding C2)

/-- Value of the axial transport field. -/
theorem horizontalAxialTransport_apply (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) :
    horizontalAxialTransport N w b =
      (Complex.I * (N : ℂ)) • scalarVectorMulL2 (E := C2) volume
        (wholePlaneCoordLInf (2 : Fin 3) w) (wholePlaneH1Embedding C2 b) := rfl

/-- The stretching field `(b·∇_⊥)v_⊥` of `eq:local-generator`, as a bounded map on `H¹`. -/
def horizontalStretching (v : WholePlaneVelocityCoefficients) :
    WholePlaneC2H1 →L[ℂ] WholePlaneC2L2 :=
  ∑ j : Fin 2, (vectorScalarMulL2 (E := C2) volume (v.horizontalDeriv j)).comp
    ((wholePlaneC2CoordL2 j).comp (wholePlaneH1Embedding C2))

/-- Value of the stretching field. -/
theorem horizontalStretching_apply (v : WholePlaneVelocityCoefficients) (b : WholePlaneC2H1) :
    horizontalStretching v b =
      ∑ j : Fin 2, vectorScalarMulL2 (E := C2) volume (v.horizontalDeriv j)
        (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 b)) := by
  simp only [horizontalStretching, sum_apply,
    ContinuousLinearMap.comp_apply]

/-- The transverse divergence expanded as a sum of coordinate derivatives. -/
theorem horizontalDivergence_apply (b : WholePlaneC2H1) :
    horizontalDivergence b =
      ∑ j : Fin 2, wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 j b) := by
  simp only [horizontalDivergence, sum_apply,
    ContinuousLinearMap.comp_apply]

/-- On the `H²` domain the `H¹`-level transport field is the strong transport term. -/
theorem horizontalTransport_h2ToH1 (v : WholePlaneVelocityCoefficients) (h : WholePlaneC2H2) :
    horizontalTransport v.value (wholePlaneC2H2ToH1 h) = wholePlaneC2LocalTransport v h := by
  simp only [horizontalTransport, wholePlaneC2LocalTransport, sum_apply,
    ContinuousLinearMap.comp_apply, wholePlaneH1FirstDerivative_H2ToH1]

/-- On the `H²` domain the `H¹`-level axial transport field is the strong axial term. -/
theorem horizontalAxialTransport_h2ToH1 (N : ℝ) (v : WholePlaneVelocityCoefficients)
    (h : WholePlaneC2H2) :
    horizontalAxialTransport N v.value (wholePlaneC2H2ToH1 h) =
      wholePlaneC2LocalAxialTransport v N h := by
  simp only [horizontalAxialTransport, wholePlaneC2LocalAxialTransport,
    smul_apply, ContinuousLinearMap.comp_apply,
    wholePlaneH1Embedding_H2ToH1]

/-- On the `H²` domain the `H¹`-level stretching field is the strong stretching term. -/
theorem horizontalStretching_h2ToH1 (v : WholePlaneVelocityCoefficients) (h : WholePlaneC2H2) :
    horizontalStretching v (wholePlaneC2H2ToH1 h) = wholePlaneC2LocalStretching v h := by
  simp only [horizontalStretching, wholePlaneC2LocalStretching, sum_apply,
    ContinuousLinearMap.comp_apply, wholePlaneH1Embedding_H2ToH1]

/-- The pairwise whole-plane integration by parts behind the stretching identity.  Both
derivatives are moved off the velocity coefficient by the certified `L^∞·H¹` Leibniz rule of
`Analysis/WholePlaneScalarLeibniz.lean`; this is the integration by parts of the stretching
term displayed before `eq:jump-sectorial-form`. -/
theorem stretch_pair (v : WholePlaneVelocityCoefficients) (hv : v.HasWeakGradient)
    (b phi : WholePlaneC2H1) (i j : Fin 2) :
    inner ℂ (wholePlaneC2CoordL2 i (wholePlaneH1Embedding C2 phi))
        (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf i.castSucc v.value)
          (wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 j b))) +
      inner ℂ (wholePlaneC2CoordL2 i (wholePlaneH1FirstDerivative C2 j phi))
        (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf i.castSucc v.value)
          (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 b))) =
      -inner ℂ (wholePlaneC2CoordL2 i (wholePlaneH1Embedding C2 phi))
        (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneCoordLInf i.castSucc (v.deriv j))
          (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 b))) := by
  have hibp := wholePlaneH1_integrationByParts ℂ (wholePlaneC2CoordH1 i phi)
    (wholePlaneScalarMulH1 (wholePlaneCoordW1InfCertificate v.value v.deriv
      hv.hasWholePlaneLInfWeakGradient i.castSucc) (wholePlaneC2CoordH1 j b)) j
  simp only [wholePlaneH1FirstDerivative_scalarMulH1, wholePlaneH1Embedding_scalarMulH1,
    wholePlaneH1Embedding_c2CoordH1, wholePlaneH1FirstDerivative_c2CoordH1,
    wholePlaneScalarMulL2, inner_add_right] at hibp
  have hval : (wholePlaneCoordW1InfCertificate v.value v.deriv
      hv.hasWholePlaneLInfWeakGradient i.castSucc).value =
      wholePlaneCoordLInf i.castSucc v.value := rfl
  have hder : (wholePlaneCoordW1InfCertificate v.value v.deriv
      hv.hasWholePlaneLInfWeakGradient i.castSucc).deriv j =
      wholePlaneCoordLInf i.castSucc (v.deriv j) := rfl
  simp only [hval, hder] at hibp
  linear_combination hibp

/-- **The stretching integration by parts.**  The two halves of the stretching form add up to
the negative `L²` pairing with the strong stretching field `(b·∇_⊥)v_⊥`. -/
theorem horizontalStretchForms_add_eq (v : WholePlaneVelocityCoefficients)
    (hv : v.HasWeakGradient) (b phi : WholePlaneC2H1) :
    horizontalStretchDivergenceForm v.value b phi +
        horizontalStretchGradientForm v.value b phi =
      -inner ℂ (wholePlaneH1Embedding C2 phi) (horizontalStretching v b) := by
  have hdiv : ∀ i : Fin 2,
      inner ℂ (wholePlaneC2CoordL2 i (wholePlaneH1Embedding C2 phi))
          (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf i.castSucc v.value)
            (horizontalDivergence b)) =
        ∑ j : Fin 2, inner ℂ (wholePlaneC2CoordL2 i (wholePlaneH1Embedding C2 phi))
          (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf i.castSucc v.value)
            (wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 j b))) := by
    intro i
    rw [horizontalDivergence_apply, map_sum, inner_sum]
  have hright :
      inner ℂ (wholePlaneH1Embedding C2 phi) (horizontalStretching v b) =
        ∑ i : Fin 2, ∑ j : Fin 2,
          inner ℂ (wholePlaneC2CoordL2 i (wholePlaneH1Embedding C2 phi))
            (scalarVectorMulL2 (E := ℂ) volume
              (wholePlaneCoordLInf i.castSucc (v.deriv j))
              (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 b))) := by
    simp only [horizontalStretching_apply, inner_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [inner_wholePlaneC2L2_eq_sum_coord]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [wholePlaneC2CoordL2_vectorScalarMulL2,
      WholePlaneVelocityCoefficients.horizontalDeriv_apply,
      wholePlaneC2CoordLInf_horizontalProjLInf]
  simp only [horizontalStretchDivergenceForm_apply, horizontalStretchGradientForm_apply,
    hright, hdiv, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  exact stretch_pair v hv b phi i j

end HorizontalWeakForm

/-! ## The identification of the form operator with the strong operator -/

namespace HorizontalWeakForm

/-- The `L²` datum carried by the velocity and mass terms of `𝔩_{w,δ}`, i.e. everything except
the Dirichlet energy `δ⟨∇_⊥b, ∇_⊥φ⟩`.  For a weak solution it represents `δΔ_⊥ b` up to the
right-hand side. -/
def horizontalLaplacianDatum (N delta : ℝ) (v : WholePlaneVelocityCoefficients) :
    WholePlaneC2H1 →L[ℂ] WholePlaneC2L2 :=
  ((delta : ℂ) * (N : ℂ) ^ 2) • wholePlaneH1Embedding C2 + horizontalTransport v.value +
    horizontalAxialTransport N v.value - horizontalStretching v

/-- Value of the velocity-and-mass datum. -/
theorem horizontalLaplacianDatum_apply (N delta : ℝ) (v : WholePlaneVelocityCoefficients)
    (b : WholePlaneC2H1) :
    horizontalLaplacianDatum N delta v b =
      ((delta : ℂ) * (N : ℂ) ^ 2) • wholePlaneH1Embedding C2 b + horizontalTransport v.value b +
        horizontalAxialTransport N v.value b - horizontalStretching v b := rfl

/-- **The weak form splits into the Dirichlet energy and an `L²` pairing.**  This is the exact
sense in which every term of `𝔩_{w,δ}` except `δ⟨∇_⊥b, ∇_⊥φ⟩` is a bounded `L²` datum. -/
theorem horizontalWeakFormDelta_eq_dirichlet_add (N delta : ℝ)
    (v : WholePlaneVelocityCoefficients) (hv : v.HasWeakGradient) (b phi : WholePlaneC2H1) :
    horizontalWeakFormDelta N delta v.value b phi =
      (delta : ℂ) * (∑ j : Fin 2, inner ℂ (wholePlaneH1FirstDerivative C2 j phi)
          (wholePlaneH1FirstDerivative C2 j b)) +
        inner ℂ (wholePlaneH1Embedding C2 phi) (horizontalLaplacianDatum N delta v b) := by
  have hstretch := horizontalStretchForms_add_eq v hv b phi
  simp only [horizontalWeakFormDelta_apply, horizontalDiffusionForm_apply,
    horizontalTransportForm_apply, horizontalAxialForm_apply, horizontalLaplacianDatum_apply,
    horizontalAxialTransport_apply, inner_sub_right, inner_add_right, inner_smul_right]
  linear_combination hstretch

/-- The local generator `𝓛_δ` of `eq:local-generator`, expanded into its four terms. -/
theorem wholePlaneC2LocalAction_eq_four (v : WholePlaneVelocityCoefficients) (delta N : ℝ)
    (h : WholePlaneC2H2) :
    wholePlaneC2LocalAction v delta N h =
      (delta : ℂ) • wholePlaneC2LocalDiffusion N h - wholePlaneC2LocalTransport v h -
        wholePlaneC2LocalAxialTransport v N h + wholePlaneC2LocalStretching v h := by
  simp only [wholePlaneC2LocalAction, add_apply, sub_apply, smul_apply]

/-- **The forward identification `H² ⊂ D(A_{w,δ})` with `A_{w,δ} = 𝓛_δ`.**  For every strong
field `h ∈ H²(ℝ²; ℂ²)` and every test field `φ ∈ H¹(ℝ²; ℂ²)` the weak form of the seed at
diffusivity `δ` evaluates to the negative `L²` pairing with the strong local generator
(sign convention `𝔩_w(b,φ) = -⟨f,φ⟩` of §2.1, generator `eq:local-generator`). -/
theorem horizontalWeakFormDelta_h2ToH1_eq (N delta : ℝ) (v : WholePlaneVelocityCoefficients)
    (hv : v.HasWeakGradient) (h : WholePlaneC2H2) (phi : WholePlaneC2H1) :
    horizontalWeakFormDelta N delta v.value (wholePlaneC2H2ToH1 h) phi =
      -inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneC2LocalAction v delta N h) := by
  have hdiff := wholePlaneC2LocalDiffusion_integrationByParts N h phi
  have haxial := wholePlaneH2H1_fixedNAxialPairing C2 N h phi
  have hsplit := horizontalWeakFormDelta_eq_dirichlet_add N delta v hv (wholePlaneC2H2ToH1 h) phi
  simp only [hsplit, horizontalLaplacianDatum_apply, horizontalTransport_h2ToH1,
    horizontalAxialTransport_h2ToH1, horizontalStretching_h2ToH1,
    wholePlaneC2LocalAction_eq_four, inner_add_right, inner_sub_right, inner_smul_right,
    wholePlaneH1FirstDerivative_H2ToH1, wholePlaneH1Embedding_H2ToH1]
  rw [haxial] at hdiff
  linear_combination (delta : ℂ) * hdiff

end HorizontalWeakForm

/-! ## Whole-plane elliptic regularity: the converse inclusion `D(A_{w,δ}) ⊂ H²` -/

namespace HorizontalWeakForm

open ConstantCoefficientBackground

/-- An `L²` field orthogonal to every `H¹` field vanishes, `H¹(ℝ²; ℂ²)` being dense. -/
theorem eq_zero_of_inner_h1Embedding_eq_zero {x : WholePlaneC2L2}
    (hx : ∀ phi : WholePlaneC2H1, inner ℂ (wholePlaneH1Embedding C2 phi) x = 0) : x = 0 := by
  have hcont : Continuous fun y : WholePlaneC2L2 => (inner ℂ y x : ℂ) :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  have heq := denseRange_wholePlaneC2H1Embedding.equalizer hcont
    (continuous_const (y := (0 : ℂ))) (funext hx)
  exact inner_self_eq_zero.mp (congrFun heq x)

/-- Each scalar coordinate of a weak solution of the seed equation solves the scalar
constant-coefficient weak equation `-δΔ g = r` with the `L²` datum supplied by the velocity
terms.  This is the "lower-order terms belong to `L²`" step of the proof of
`prop:local-seed`. -/
theorem isConstantCoefficientWeakResolventSolution_coord (N delta : ℝ)
    (v : WholePlaneVelocityCoefficients) (hv : v.HasWeakGradient)
    (b : WholePlaneC2H1) (g : WholePlaneC2L2)
    (hb : ∀ phi : WholePlaneC2H1,
      horizontalWeakFormDelta N delta v.value b phi =
        -inner ℂ (wholePlaneH1Embedding C2 phi) g)
    (i : Fin 2) :
    IsConstantCoefficientWeakResolventSolution delta 0
      (wholePlaneC2CoordL2 i (-(g + horizontalLaplacianDatum N delta v b)))
      (wholePlaneC2CoordH1 i b) := by
  intro psi
  have hsplit := horizontalWeakFormDelta_eq_dirichlet_add N delta v hv b
    (wholePlaneScalarToC2CoordH1 i psi)
  have hweak := hb (wholePlaneScalarToC2CoordH1 i psi)
  rw [hsplit] at hweak
  simp only [wholePlaneH1Embedding_scalarToC2CoordH1,
    wholePlaneH1FirstDerivative_scalarToC2CoordH1, inner_wholePlaneScalarToC2CoordL2] at hweak
  simp only [constantCoefficientWeakForm, map_neg, map_add, inner_neg_right, inner_add_right,
    zero_mul, add_zero]
  simp only [wholePlaneH1FirstDerivative_c2CoordH1]
  linear_combination hweak

/-- **The distributional Laplacian of a weak solution is an `L²` field.**  This is the Fourier
regularity input of the proof of `prop:local-seed`. -/
theorem laplacian_toTempered_of_horizontalWeak (N delta : ℝ) (hdelta : delta ≠ 0)
    (v : WholePlaneVelocityCoefficients) (hv : v.HasWeakGradient)
    (b : WholePlaneC2H1) (g : WholePlaneC2L2)
    (hb : ∀ phi : WholePlaneC2H1,
      horizontalWeakFormDelta N delta v.value b phi =
        -inner ℂ (wholePlaneH1Embedding C2 phi) g) :
    Laplacian.laplacian (wholePlaneL2ToTempered C2 (wholePlaneH1Embedding C2 b)) =
      wholePlaneL2ToTempered C2
        (((delta : ℂ)⁻¹) • (g + horizontalLaplacianDatum N delta v b)) := by
  apply wholePlaneC2Tempered_ext_coord
  intro i
  have hcoord := laplacian_toTempered_eq_of_constantCoefficientWeak hdelta
    (isConstantCoefficientWeakResolventSolution_coord N delta v hv b g hb i)
  have hdatum : constantCoefficientLaplacianDatum delta 0
      (wholePlaneC2CoordL2 i (-(g + horizontalLaplacianDatum N delta v b)))
      (wholePlaneH1Embedding ℂ (wholePlaneC2CoordH1 i b)) =
      wholePlaneC2CoordL2 i (((delta : ℂ)⁻¹) • (g + horizontalLaplacianDatum N delta v b)) := by
    simp [constantCoefficientLaplacianDatum]
  rw [hdatum] at hcoord
  rw [wholePlaneC2CoordTempered_laplacian, wholePlaneC2CoordTempered_l2,
    wholePlaneC2CoordTempered_l2]
  exact hcoord

/-- **The converse inclusion.**  A weak solution of `𝔩_{w,δ}(b, ·) = -⟨f, ·⟩` is the `H¹` trace
of a strong `H²` field solving `𝓛_δ h = f`. -/
theorem exists_wholePlaneC2H2_of_horizontalWeak (N delta : ℝ) (hdelta : delta ≠ 0)
    (v : WholePlaneVelocityCoefficients) (hv : v.HasWeakGradient)
    (b : WholePlaneC2H1) (g : WholePlaneC2L2)
    (hb : ∀ phi : WholePlaneC2H1,
      horizontalWeakFormDelta N delta v.value b phi =
        -inner ℂ (wholePlaneH1Embedding C2 phi) g) :
    ∃ h : WholePlaneC2H2, wholePlaneC2H2ToH1 h = b ∧ wholePlaneC2LocalAction v delta N h = g := by
  obtain ⟨h, hemb, _⟩ := exists_wholePlaneH2_of_laplacian_eq_l2 C2
    (wholePlaneH1Embedding C2 b) (((delta : ℂ)⁻¹) • (g + horizontalLaplacianDatum N delta v b))
    (laplacian_toTempered_of_horizontalWeak N delta hdelta v hv b g hb)
  have htrace : wholePlaneC2H2ToH1 h = b := by
    apply wholePlaneC2H1Embedding_injective
    rw [wholePlaneH1Embedding_H2ToH1]
    exact hemb
  refine ⟨h, htrace, ?_⟩
  have hzero : ∀ phi : WholePlaneC2H1,
      inner ℂ (wholePlaneH1Embedding C2 phi)
        (wholePlaneC2LocalAction v delta N h - g) = (0 : ℂ) := by
    intro phi
    have h1 := horizontalWeakFormDelta_h2ToH1_eq N delta v hv h phi
    rw [htrace, hb phi] at h1
    rw [inner_sub_right]
    linear_combination h1
  have := eq_zero_of_inner_h1Embedding_eq_zero hzero
  exact sub_eq_zero.mp this

end HorizontalWeakForm

end

end FastDynamo
