/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusChartCutoffSupport
public import LeanPool.FastDynamo.Global.TorusPlacedCutoffVelocity
public import LeanPool.FastDynamo.Global.WholePlaneCutoffCommutator

/-!
# The auxiliary output cut-off `auxiliaryCutoff_n` and the locality of the whole-plane commutator

For the selected summand of `eq:Rapp` the paper (§7.1) extends `φ_n f` by zero to `ℝ²`, applies the
resolvent on `ℝ²` for the selected cell and restricts the product with `ψ_n` to the torus.  The Lean
transports the selected resolvent to the torus as `auxiliaryCutoff_n·(R_n(z)φ_n·)`, where
`auxiliaryCutoff_n` is an auxiliary
cut-off identically one on `supp ψ_n` (a device of the formalisation; the paper has no
`auxiliaryCutoff_n`).  The
auxiliary cut-off is realised here as the repository's own output profile at the **enlarged** radius
`3R/2`:

* `outputCutoff p (3R/2)` is identically one on `closedBall(p, R/2) ⊇ supp ψ_n`, since its plateau
is
  `closedBall(p, (3R/2)/3) = closedBall(p, R/2)`;
* it is supported in `closedBall(p, (3R/2)/2) = closedBall(p, 3R/4)`, which lies inside the chart at
  every cell of a placement (the buffer disc has radius `R`).

Two consequences are proved, both purely pointwise in the cut-off profiles and then transported
to `L∞` classes and to bounded multipliers:

1. `ψ_n · auxiliaryCutoff_n = ψ_n` (`eq:parametrix-cutoff-identities` read for the enlarged radius);
2. `ψ_n · ∇auxiliaryCutoff_n = 0` and `ψ_n · D²auxiliaryCutoff_n = 0` pointwise: where `ψ_n ≠ 0`
the auxiliary
   cut-off is *constant*.  Hence `ψ_n` annihilates the whole-plane cut-off commutator
   `[A^{(n)}, auxiliaryCutoff_n]`, whose every term carries a derivative of `auxiliaryCutoff_n`
   (`wholePlaneLocalAction_cutoffCommutator_apply`).

Together these give the *locality* identity `ψ_n·A^{(n)}(auxiliaryCutoff_n b) = ψ_n·A^{(n)} b`,
which is
what lets the selected defect `(z - A_{ε,K_n})ψ_nR_n(z)φ_n - φ_n` of the proof of
`lem:parametrix-error` be rewritten with the torus commutator applied to the transported
field.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set

namespace TorusChartC2Transfer

open ConstantCoefficientBackground
open ParametrixExplicitCutoff
open WholePlaneCutoffCommutator
open TorusChartL2
open TorusPlacedCutoffC2
open TorusSupportedH2Output

/-! ## The auxiliary radius -/

/-- The enlarged radius carrying the auxiliary output cut-off `auxiliaryCutoff_n`. -/
def auxOutputRadius (R : ℝ) : ℝ := 3 * R / 2

/-- The enlarged radius is positive. -/
theorem auxOutputRadius_pos {R : ℝ} (hR : 0 < R) : 0 < auxOutputRadius R := by
  unfold auxOutputRadius
  linarith

/-- The plateau of the auxiliary cut-off is exactly the closed half-ball of the original
radius. -/
theorem auxOutputRadius_div_three (R : ℝ) : auxOutputRadius R / 3 = R / 2 := by
  unfold auxOutputRadius
  ring

/-- The support of the auxiliary cut-off is contained in the closed three-quarter ball. -/
theorem auxOutputRadius_div_two (R : ℝ) : auxOutputRadius R / 2 = 3 * R / 4 := by
  unfold auxOutputRadius
  ring

variable (p : WholePlane) (R : ℝ) (hR : 0 < R)

/-! ## Pointwise identities between `ψ_n` and `auxiliaryCutoff_n` -/

/-- The auxiliary cut-off is one wherever the output cut-off is nonzero. -/
theorem outputCutoff_mul_auxOutputCutoff (x : WholePlane) :
    outputCutoff p R hR x *
        outputCutoff p (auxOutputRadius R) (auxOutputRadius_pos hR) x =
      outputCutoff p R hR x := by
  by_cases hx : dist x p < R / 2
  · rw [outputCutoff_eq_one_of_dist_le p (auxOutputRadius R) (auxOutputRadius_pos hR)
      (by rw [auxOutputRadius_div_three]; exact le_of_lt hx), mul_one]
  · rw [outputCutoff_eq_zero_of_radius_le_dist p R hR (not_lt.mp hx), zero_mul]

/-- Every coordinate derivative of the auxiliary cut-off is annihilated by the output
cut-off. -/
theorem outputCutoff_mul_auxOutputCutoff_deriv (j : Fin 2) (x : WholePlane) :
    outputCutoff p R hR x *
        realProfileCoordinateDerivative
          (outputCutoff p (auxOutputRadius R) (auxOutputRadius_pos hR)) j x = 0 := by
  by_cases hx : dist x p < R / 2
  · rw [realProfileCoordinateDerivative_outputCutoff_eq_zero_of_lt_third p
      (auxOutputRadius R) (auxOutputRadius_pos hR)
      (by rw [auxOutputRadius_div_three]; exact hx) j, mul_zero]
  · rw [outputCutoff_eq_zero_of_radius_le_dist p R hR (not_lt.mp hx), zero_mul]

/-- The auxiliary cut-off is constant on the open plateau, so its ordered second derivatives
vanish there as well. -/
theorem realProfileSecondCoordinateDerivative_outputCutoff_eq_zero_of_lt_third
    (j k : Fin 2) {y : WholePlane} (hy : dist y p < R / 3) :
    realProfileSecondCoordinateDerivative (outputCutoff p R hR) j k y = 0 := by
  have hopen : IsOpen {z : WholePlane | dist z p < R / 3} :=
    isOpen_lt (continuous_id.dist continuous_const) continuous_const
  have hmem : {z : WholePlane | dist z p < R / 3} ∈ nhds y := hopen.mem_nhds hy
  have heq : realProfileCoordinateDerivative (outputCutoff p R hR) j =ᶠ[nhds y] fun _ ↦ 0 := by
    filter_upwards [hmem] with z hz
    exact realProfileCoordinateDerivative_outputCutoff_eq_zero_of_lt_third p R hR hz j
  unfold realProfileSecondCoordinateDerivative
  rw [heq.fderiv_eq (𝕜 := ℝ)]
  simp

/-- Every ordered second derivative of the auxiliary cut-off is annihilated by the output
cut-off. -/
theorem outputCutoff_mul_auxOutputCutoff_secondDeriv (j k : Fin 2) (x : WholePlane) :
    outputCutoff p R hR x *
        realProfileSecondCoordinateDerivative
          (outputCutoff p (auxOutputRadius R) (auxOutputRadius_pos hR)) j k x = 0 := by
  by_cases hx : dist x p < R / 2
  · rw [realProfileSecondCoordinateDerivative_outputCutoff_eq_zero_of_lt_third p
      (auxOutputRadius R) (auxOutputRadius_pos hR) j k
      (by rw [auxOutputRadius_div_three]; exact hx), mul_zero]
  · rw [outputCutoff_eq_zero_of_radius_le_dist p R hR (not_lt.mp hx), zero_mul]

/-! ## The same identities for the bounded `L∞` coefficients -/

/-- The output cut-off class absorbs the auxiliary cut-off class. -/
theorem outputCutoffLInf_mul_auxValue_ae :
    ∀ᵐ x ∂volume, (outputCutoffLInf p R hR : WholePlane → ℂ) x *
        ((outputCutoffW2InfCertificate p (auxOutputRadius R)
          (auxOutputRadius_pos hR)).value : WholePlane → ℂ) x =
      (outputCutoffLInf p R hR : WholePlane → ℂ) x := by
  filter_upwards [outputCutoffLInf_coe_ae p R hR,
    outputCutoffW2InfCertificate_value_coe_ae p (auxOutputRadius R)
      (auxOutputRadius_pos hR)] with x h1 h2
  rw [h1, h2]
  unfold outputCutoffComplex
  rw [← Complex.ofReal_mul, outputCutoff_mul_auxOutputCutoff p R hR x]

/-- The output cut-off class annihilates each stored derivative of the auxiliary cut-off. -/
theorem outputCutoffLInf_mul_auxDeriv_ae (j : Fin 2) :
    ∀ᵐ x ∂volume, (outputCutoffLInf p R hR : WholePlane → ℂ) x *
        ((outputCutoffW2InfCertificate p (auxOutputRadius R)
          (auxOutputRadius_pos hR)).deriv j : WholePlane → ℂ) x = 0 := by
  filter_upwards [outputCutoffLInf_coe_ae p R hR,
    outputCutoffW2InfCertificate_deriv_coe_ae p (auxOutputRadius R)
      (auxOutputRadius_pos hR) j] with x h1 h2
  rw [h1, h2]
  unfold outputCutoffComplex
  rw [← Complex.ofReal_mul, outputCutoff_mul_auxOutputCutoff_deriv p R hR j x]
  norm_num

/-- The output cut-off class annihilates each stored second derivative of the auxiliary
cut-off. -/
theorem outputCutoffLInf_mul_auxSecondDeriv_ae (j k : Fin 2) :
    ∀ᵐ x ∂volume, (outputCutoffLInf p R hR : WholePlane → ℂ) x *
        ((outputCutoffW2InfCertificate p (auxOutputRadius R)
          (auxOutputRadius_pos hR)).secondDeriv j k : WholePlane → ℂ) x = 0 := by
  filter_upwards [outputCutoffLInf_coe_ae p R hR,
    outputCutoffW2InfCertificate_secondDeriv_coe_ae p (auxOutputRadius R)
      (auxOutputRadius_pos hR) j k] with x h1 h2
  rw [h1, h2]
  unfold outputCutoffComplex
  rw [← Complex.ofReal_mul, outputCutoff_mul_auxOutputCutoff_secondDeriv p R hR j k x]
  norm_num

/-! ## Scalar multiplier algebra on whole-plane `L²` -/

/-- Two scalar multipliers whose pointwise product vanishes compose to zero. -/
private theorem scalarMul_scalarMul_eq_zero {a c : WholePlaneScalarLInf} (X : WholePlaneC3L2)
    (h : ∀ᵐ x ∂volume, (a : WholePlane → ℂ) x * (c : WholePlane → ℂ) x = 0) :
    wholePlaneScalarMulC3L2 a (wholePlaneScalarMulC3L2 c X) = 0 := by
  apply Lp.ext
  filter_upwards [scalarVectorMulL2_coe_ae (E := C3) volume a (wholePlaneScalarMulC3L2 c X),
    scalarVectorMulL2_coe_ae (E := C3) volume c X, h,
    Lp.coeFn_zero (E := C3) (p := 2) (μ := (volume : Measure WholePlane))]
      with x h1 h2 h3 h4
  simp only [wholePlaneScalarMulC3L2] at h1 h2 ⊢
  rw [h4, h1, h2, smul_smul, h3, zero_smul]
  rfl

/-- A scalar multiplier sandwiched between two others whose product vanishes gives zero. -/
private theorem scalarMul_scalarMul_scalarMul_eq_zero
    {a d c : WholePlaneScalarLInf} (X : WholePlaneC3L2)
    (h : ∀ᵐ x ∂volume, (a : WholePlane → ℂ) x * (c : WholePlane → ℂ) x = 0) :
    wholePlaneScalarMulC3L2 a
        (wholePlaneScalarMulC3L2 d (wholePlaneScalarMulC3L2 c X)) = 0 := by
  apply Lp.ext
  filter_upwards [scalarVectorMulL2_coe_ae (E := C3) volume a
      (wholePlaneScalarMulC3L2 d (wholePlaneScalarMulC3L2 c X)),
    scalarVectorMulL2_coe_ae (E := C3) volume d (wholePlaneScalarMulC3L2 c X),
    scalarVectorMulL2_coe_ae (E := C3) volume c X, h,
    Lp.coeFn_zero (E := C3) (p := 2) (μ := (volume : Measure WholePlane))]
      with x h1 h2 h3 h4 h5
  simp only [wholePlaneScalarMulC3L2] at h1 h2 h3 ⊢
  rw [h5, h1, h2, h3, smul_smul, smul_smul,
    show (a : WholePlane → ℂ) x * (d : WholePlane → ℂ) x * (c : WholePlane → ℂ) x =
      (d : WholePlane → ℂ) x *
        ((a : WholePlane → ℂ) x * (c : WholePlane → ℂ) x) by ring,
    h4, mul_zero, zero_smul]
  rfl

/-- A scalar multiplier that absorbs a second one may be applied alone. -/
private theorem scalarMul_scalarMul_eq_self {a c : WholePlaneScalarLInf} (X : WholePlaneC3L2)
    (h : ∀ᵐ x ∂volume, (a : WholePlane → ℂ) x * (c : WholePlane → ℂ) x =
      (a : WholePlane → ℂ) x) :
    wholePlaneScalarMulC3L2 a (wholePlaneScalarMulC3L2 c X) =
      wholePlaneScalarMulC3L2 a X := by
  apply Lp.ext
  filter_upwards [scalarVectorMulL2_coe_ae (E := C3) volume a (wholePlaneScalarMulC3L2 c X),
    scalarVectorMulL2_coe_ae (E := C3) volume c X, h,
    scalarVectorMulL2_coe_ae (E := C3) volume a X] with x h1 h2 h3 h4
  simp only [wholePlaneScalarMulC3L2] at h1 h2 h4 ⊢
  rw [h1, h2, h4, smul_smul, h3]

/-- The output cut-off class annihilates the stored Laplacian of the auxiliary cut-off. -/
theorem outputCutoffLInf_mul_auxLaplacian_ae :
    ∀ᵐ x ∂volume, (outputCutoffLInf p R hR : WholePlane → ℂ) x *
        ((outputCutoffW2InfCertificate p (auxOutputRadius R)
          (auxOutputRadius_pos hR)).laplacian : WholePlane → ℂ) x = 0 := by
  have hlap : (outputCutoffW2InfCertificate p (auxOutputRadius R)
        (auxOutputRadius_pos hR)).laplacian =
      (outputCutoffW2InfCertificate p (auxOutputRadius R)
          (auxOutputRadius_pos hR)).secondDeriv 0 0 +
        (outputCutoffW2InfCertificate p (auxOutputRadius R)
          (auxOutputRadius_pos hR)).secondDeriv 1 1 := by
    unfold WholePlaneScalarW2InfCertificate.laplacian
    rw [Fin.sum_univ_two]
  filter_upwards [outputCutoffLInf_mul_auxSecondDeriv_ae p R hR 0 0,
    outputCutoffLInf_mul_auxSecondDeriv_ae p R hR 1 1,
    Lp.coeFn_add ((outputCutoffW2InfCertificate p (auxOutputRadius R)
        (auxOutputRadius_pos hR)).secondDeriv 0 0)
      ((outputCutoffW2InfCertificate p (auxOutputRadius R)
        (auxOutputRadius_pos hR)).secondDeriv 1 1)] with x h0 h1 hadd
  rw [hlap, hadd, Pi.add_apply, mul_add, h0, h1, add_zero]

/-! ## Locality of the selected whole-plane action against the auxiliary cut-off -/

variable (v : WholePlaneVelocityCoefficients) (epsilon : ℝ) (K : ℤ) (shift : ℝ)

/-- The constant axial shift commutes with multiplication by any `W²,∞` scalar cut-off. -/
theorem selectedWholePlaneAxialShift_scalarMulC3H2
    (cert : WholePlaneScalarW2InfCertificate) (X : WholePlaneC3H2) :
    selectedWholePlaneAxialShift K shift (wholePlaneScalarMulC3H2 cert X) =
      wholePlaneScalarMulC3L2 cert.value (selectedWholePlaneAxialShift K shift X) := by
  change (axialMultiplier K * (shift : ℂ)) •
      wholePlaneH2Embedding C3 (wholePlaneScalarMulC3H2 cert X) =
    wholePlaneScalarMulC3L2 cert.value
      ((axialMultiplier K * (shift : ℂ)) • wholePlaneH2Embedding C3 X)
  rw [wholePlaneH2Embedding_scalarMulC3H2, map_smul]

/-- The whole-plane cut-off commutator of the *selected* action coincides with that of the
local action: the constant axial shift commutes with the cut-off. -/
theorem selectedWholePlaneInductionAction_cutoffCommutator_apply
    (cert : WholePlaneScalarW2InfCertificate) (X : WholePlaneC3H2) :
    selectedWholePlaneInductionAction v epsilon K shift (wholePlaneScalarMulC3H2 cert X) -
        wholePlaneScalarMulC3L2 cert.value
          (selectedWholePlaneInductionAction v epsilon K shift X) =
      (epsilon : ℂ) • ((2 : ℂ) • wholePlaneScalarGradientDotC3H2 cert X +
          wholePlaneScalarMulC3L2 cert.laplacian (wholePlaneH2Embedding C3 X)) -
        wholePlaneTransportCutoffInteraction cert v X := by
  have hlocal := wholePlaneLocalAction_cutoffCommutator_apply cert v epsilon
    (wholePlaneAxialWavenumber K) X
  have haxial := selectedWholePlaneAxialShift_scalarMulC3H2 K shift cert X
  have hzero : selectedWholePlaneAxialShift K shift (wholePlaneScalarMulC3H2 cert X) -
      wholePlaneScalarMulC3L2 cert.value (selectedWholePlaneAxialShift K shift X) = 0 :=
    sub_eq_zero_of_eq haxial
  have hm : wholePlaneScalarMulC3L2 cert.value
        (selectedWholePlaneInductionAction v epsilon K shift X) =
      wholePlaneScalarMulC3L2 cert.value
          (wholePlaneLocalAction v epsilon (wholePlaneAxialWavenumber K) X) -
        wholePlaneScalarMulC3L2 cert.value (selectedWholePlaneAxialShift K shift X) :=
    map_sub (wholePlaneScalarMulC3L2 cert.value) _ _
  have hstep : selectedWholePlaneInductionAction v epsilon K shift
          (wholePlaneScalarMulC3H2 cert X) -
        wholePlaneScalarMulC3L2 cert.value
          (selectedWholePlaneInductionAction v epsilon K shift X) =
      (wholePlaneLocalAction v epsilon (wholePlaneAxialWavenumber K)
            (wholePlaneScalarMulC3H2 cert X) -
          wholePlaneScalarMulC3L2 cert.value
            (wholePlaneLocalAction v epsilon (wholePlaneAxialWavenumber K) X)) -
        (selectedWholePlaneAxialShift K shift (wholePlaneScalarMulC3H2 cert X) -
          wholePlaneScalarMulC3L2 cert.value
            (selectedWholePlaneAxialShift K shift X)) := by
    rw [hm]
    change wholePlaneLocalAction v epsilon (wholePlaneAxialWavenumber K)
          (wholePlaneScalarMulC3H2 cert X) -
        selectedWholePlaneAxialShift K shift (wholePlaneScalarMulC3H2 cert X) - _ = _
    abel
  exact hstep.trans ((sub_eq_self.mpr hzero).trans hlocal)

/-- Multiplication by the output cut-off, written with the scalar-multiplier notation of the
Leibniz layer. -/
theorem outputCutoffMulL2_eq_scalarMul :
    outputCutoffMulL2 p R hR = wholePlaneScalarMulC3L2 (outputCutoffLInf p R hR) :=
  rfl

/-- The output cut-off annihilates the cut-off-gradient interaction of the auxiliary cut-off. -/
theorem outputCutoffMulL2_gradientDot_eq_zero (X : WholePlaneC3H2) :
    outputCutoffMulL2 p R hR (wholePlaneScalarGradientDotC3H2
        (outputCutoffW2InfCertificate p (auxOutputRadius R) (auxOutputRadius_pos hR)) X) = 0 := by
  rw [outputCutoffMulL2_eq_scalarMul, wholePlaneScalarGradientDotC3H2, map_sum]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  exact scalarMul_scalarMul_eq_zero _ (outputCutoffLInf_mul_auxDeriv_ae p R hR j)

/-- The output cut-off annihilates the Laplacian term of the auxiliary cut-off. -/
theorem outputCutoffMulL2_laplacianTerm_eq_zero (X : WholePlaneC3H2) :
    outputCutoffMulL2 p R hR (wholePlaneScalarMulC3L2
        (outputCutoffW2InfCertificate p (auxOutputRadius R) (auxOutputRadius_pos hR)).laplacian
        (wholePlaneH2Embedding C3 X)) = 0 := by
  rw [outputCutoffMulL2_eq_scalarMul]
  exact scalarMul_scalarMul_eq_zero _ (outputCutoffLInf_mul_auxLaplacian_ae p R hR)

/-- The output cut-off annihilates the transport cut-off interaction of the auxiliary
cut-off. -/
theorem outputCutoffMulL2_transportCutoffInteraction_eq_zero (X : WholePlaneC3H2) :
    outputCutoffMulL2 p R hR (wholePlaneTransportCutoffInteraction
        (outputCutoffW2InfCertificate p (auxOutputRadius R) (auxOutputRadius_pos hR)) v X) = 0 := by
  rw [outputCutoffMulL2_eq_scalarMul, wholePlaneTransportCutoffInteraction, map_sum]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  exact scalarMul_scalarMul_scalarMul_eq_zero _ (outputCutoffLInf_mul_auxDeriv_ae p R hR j)

/-- **Locality of the selected whole-plane action.**  Inserting the auxiliary cut-off
`auxiliaryCutoff_n`
does not change the selected action once it is multiplied by `ψ_n`: every term of the cut-off
commutator carries a derivative of `auxiliaryCutoff_n`, and those vanish on the support of `ψ_n`.
This is
what makes the transported field `auxiliaryCutoff_n·(R_n(z)φ_n·)` legitimate in the selected
identity of the
proof of `lem:parametrix-error`. -/
theorem outputCutoffMulL2_selectedAction_auxMul (X : WholePlaneC3H2) :
    outputCutoffMulL2 p R hR (selectedWholePlaneInductionAction v epsilon K shift
        (wholePlaneScalarMulC3H2
          (outputCutoffW2InfCertificate p (auxOutputRadius R) (auxOutputRadius_pos hR)) X)) =
      outputCutoffMulL2 p R hR (selectedWholePlaneInductionAction v epsilon K shift X) := by
  have hcomm := selectedWholePlaneInductionAction_cutoffCommutator_apply v epsilon K shift
    (outputCutoffW2InfCertificate p (auxOutputRadius R) (auxOutputRadius_pos hR)) X
  have hsplit : selectedWholePlaneInductionAction v epsilon K shift
        (wholePlaneScalarMulC3H2
          (outputCutoffW2InfCertificate p (auxOutputRadius R) (auxOutputRadius_pos hR)) X) =
      ((epsilon : ℂ) • ((2 : ℂ) • wholePlaneScalarGradientDotC3H2
              (outputCutoffW2InfCertificate p (auxOutputRadius R)
                (auxOutputRadius_pos hR)) X +
            wholePlaneScalarMulC3L2 (outputCutoffW2InfCertificate p (auxOutputRadius R)
                (auxOutputRadius_pos hR)).laplacian (wholePlaneH2Embedding C3 X)) -
          wholePlaneTransportCutoffInteraction
            (outputCutoffW2InfCertificate p (auxOutputRadius R)
              (auxOutputRadius_pos hR)) v X) +
        wholePlaneScalarMulC3L2 (outputCutoffW2InfCertificate p (auxOutputRadius R)
            (auxOutputRadius_pos hR)).value
          (selectedWholePlaneInductionAction v epsilon K shift X) :=
    sub_eq_iff_eq_add.mp hcomm
  have hzeroCmt : outputCutoffMulL2 p R hR
      ((epsilon : ℂ) • ((2 : ℂ) • wholePlaneScalarGradientDotC3H2
              (outputCutoffW2InfCertificate p (auxOutputRadius R)
                (auxOutputRadius_pos hR)) X +
            wholePlaneScalarMulC3L2 (outputCutoffW2InfCertificate p (auxOutputRadius R)
                (auxOutputRadius_pos hR)).laplacian (wholePlaneH2Embedding C3 X)) -
          wholePlaneTransportCutoffInteraction
            (outputCutoffW2InfCertificate p (auxOutputRadius R)
              (auxOutputRadius_pos hR)) v X) = 0 := by
    simp only [map_sub, map_smul, map_add,
      outputCutoffMulL2_gradientDot_eq_zero p R hR X,
      outputCutoffMulL2_laplacianTerm_eq_zero p R hR X,
      outputCutoffMulL2_transportCutoffInteraction_eq_zero p R hR v X,
      smul_zero, add_zero, sub_zero]
  have habsorb : ∀ Y : WholePlaneC3L2,
      outputCutoffMulL2 p R hR (wholePlaneScalarMulC3L2
          (outputCutoffW2InfCertificate p (auxOutputRadius R)
            (auxOutputRadius_pos hR)).value Y) =
        outputCutoffMulL2 p R hR Y :=
    fun Y ↦ scalarMul_scalarMul_eq_self Y (outputCutoffLInf_mul_auxValue_ae p R hR)
  refine (congrArg (fun Y : WholePlaneC3L2 ↦ outputCutoffMulL2 p R hR Y) hsplit).trans ?_
  simp only [map_add, hzeroCmt, habsorb, zero_add]

end TorusChartC2Transfer

end

end FastDynamo
