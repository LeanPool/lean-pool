/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.HorizontalSmoothedVelocity

/-!
# The one form perturbation estimate `eq:form-small`

This module proves the single quantitative estimate on which the proof of `prop:local-seed`
rests:

`‖𝔸_{h,δ}(z) - 𝔸_{0,1}(z)‖_{V→V*} ≤ C(h^{1/4} + |δ-1|)`,   `V = H¹(ℝ²;ℂ²)`,

with a constant independent of `z`, of the smoothing width `h` and of the diffusivity `δ`.

Two structural facts organise the proof.

* The difference of two members of the family is `z`-free: `horizontalPencilFormDelta_sub` of
  `Local/HorizontalFormDelta.lean` splits it as `(K_w - K_{w'}) + (δ-δ')·(diffusion)`, the
  free form `F_z` cancelling.  The `|δ-δ'|` half is then the direct `V × V` bound
  `complexFormOpNorm_smul_horizontalDiffusionForm_le`.
* The velocity half `K_w - K_{w'}` is estimated term by term with the Hölder exponents
  `(4,4,2)` and the two-dimensional embedding `H¹(ℝ²) ↪ L⁴(ℝ²)`.  Writing `d = w - w'` in
  `L⁴(ℝ²;ℂ³)`:
  * the transport term `⟨d_⊥·∇_⊥b, φ⟩` and the divergence half `∫ d_⊥(Div_⊥b)conj φ` of the
    stretching term carry the derivative on `b`, so the coefficient is moved onto the test
    function by the adjointness `⟨u, a v⟩ = ⟨a u, v⟩` of multiplication by a **real** `L∞`
    coefficient, and the pairing is `L⁴ × L⁴ × L²`;
  * the axial term `iN⟨d₃b, φ⟩` and the gradient half `∫ d_⊥(b·∇_⊥)conj φ` carry no derivative on
    `b` or one on `φ`, so the coefficient multiplies `b` directly and the pairing is again
    `L⁴ × L⁴ × L²`.

  The reality hypothesis is used here and is satisfied by the paper's velocities: it is
  `horizontalSmoothingErrorL4_im` for the smoothing error.

The concluding statements, which combine the `h^{1/4}` rate of
`Local/HorizontalSmoothedVelocity.lean` with the form estimate, are in
`Local/HorizontalFormSmallness.lean` (`exists_complexFormOpNorm_horizontalSmoothedPencil_sub_le`).
Nothing about resolvents, Neumann series or Riesz projections is proved here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HorizontalWeakForm

open HorizontalMode

/-! ## `L⁴` coordinate extraction -/

/-- Extract one scalar coordinate from a whole-plane `C3`-valued `L⁴` field. -/
def wholePlaneCoordL4 (i : Fin 3) : WholePlaneC3L4 →L[ℂ] WholePlaneScalarL4 :=
  (EuclideanSpace.proj i).compLpL 4 volume

/-- The coordinate of an `L⁴` field is the pointwise coordinate almost everywhere. -/
theorem wholePlaneCoordL4_coe_ae (i : Fin 3) (f : WholePlaneC3L4) :
    (wholePlaneCoordL4 i f : WholePlane → ℂ) =ᵐ[volume]
      fun y => (f : WholePlane → C3) y i :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := 4)
    (μ := (volume : Measure WholePlane)) f

/-- A scalar coordinate projection is contractive on `C3`-valued `L⁴`. -/
theorem norm_wholePlaneCoordL4_apply_le (i : Fin 3) (f : WholePlaneC3L4) :
    ‖wholePlaneCoordL4 i f‖ ≤ ‖f‖ := by
  have hproj : ‖(EuclideanSpace.proj (𝕜 := ℂ) i)‖ ≤ 1 := by
    refine (EuclideanSpace.proj (𝕜 := ℂ) i).opNorm_le_bound zero_le_one ?_
    intro x
    simpa using PiLp.norm_apply_le x i
  have hcoord : ‖wholePlaneCoordL4 i‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le (EuclideanSpace.proj (𝕜 := ℂ) i)).trans hproj
  calc
    ‖wholePlaneCoordL4 i f‖ ≤ ‖wholePlaneCoordL4 i‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hcoord (norm_nonneg _)
    _ = ‖f‖ := one_mul _

/-! ## Hölder `(4,4,2)` multiplication and its two uses -/

section Holder

variable {X : Type*} [MeasurableSpace X] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]

/-- Pointwise multiplication as a bounded bilinear map `L⁴(ℂ) × L⁴(E) → L²(E)`; this is the
Hölder step with exponents `(4,4,2)` of the proof of `prop:local-seed`. -/
def scalarVectorMulL4 (mu : Measure X) :
    Lp ℂ 4 mu →L[ℂ] Lp E 4 mu →L[ℂ] Lp E 2 mu :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).holderL mu 4 4 2

/-- Almost-everywhere representative of the `(4,4,2)` product. -/
theorem scalarVectorMulL4_coe_ae (mu : Measure X) (a : Lp ℂ 4 mu) (f : Lp E 4 mu) :
    (scalarVectorMulL4 mu a f : X → E) =ᵐ[mu] fun x => a x • f x :=
  ContinuousLinearMap.coeFn_holder _ _ _

/-- Hölder's `(4,4,2)` norm estimate. -/
theorem norm_scalarVectorMulL4_apply_le (mu : Measure X) (a : Lp ℂ 4 mu) (f : Lp E 4 mu) :
    ‖scalarVectorMulL4 mu a f‖ ≤ ‖a‖ * ‖f‖ := by
  calc
    ‖scalarVectorMulL4 mu a f‖ ≤
        ‖(ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E)‖ * ‖a‖ * ‖f‖ :=
      ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ ≤ 1 * ‖a‖ * ‖f‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_lsmul_le
    _ = ‖a‖ * ‖f‖ := by rw [one_mul]

/-- Multiplication is additive in the `L∞` coefficient. -/
theorem scalarVectorMulL2_sub_coeff (mu : Measure X) (a a' : Lp ℂ ∞ mu) (f : Lp E 2 mu) :
    scalarVectorMulL2 mu a f - scalarVectorMulL2 mu a' f = scalarVectorMulL2 mu (a - a') f := by
  rw [map_sub (scalarVectorMulL2 mu)]
  rfl

/-- An `L∞ × L²` product is an `L⁴ × L⁴` product whenever both factors have `L⁴`
representatives.  This is what lets the `L∞` forms of `eq:jump-sectorial-form` be estimated by
Hölder with exponents `(4,4,2)`. -/
theorem scalarVectorMulL2_eq_scalarVectorMulL4 (mu : Measure X) (a : Lp ℂ ∞ mu)
    (f2 : Lp E 2 mu) (g : Lp ℂ 4 mu) (f4 : Lp E 4 mu)
    (hg : (g : X → ℂ) =ᵐ[mu] (a : X → ℂ)) (hf : (f4 : X → E) =ᵐ[mu] (f2 : X → E)) :
    scalarVectorMulL2 mu a f2 = scalarVectorMulL4 mu g f4 := by
  apply Lp.ext
  filter_upwards [scalarVectorMulL2_coe_ae mu a f2, scalarVectorMulL4_coe_ae mu g f4, hg, hf]
    with x h2 h4 hgx hfx
  rw [h2, h4, hgx, hfx]

/-- Multiplication by a real-valued `L∞` coefficient is self-adjoint on `L²`.  It is what moves
the velocity coefficient from the differentiated field onto the test function in the transport
and stretching-divergence terms. -/
theorem inner_scalarVectorMulL2_swap (mu : Measure X) (a : Lp ℂ ∞ mu)
    (ha : ∀ᵐ x ∂mu, ((a : X → ℂ) x).im = 0) (u v : Lp E 2 mu) :
    inner ℂ u (scalarVectorMulL2 mu a v) = inner ℂ (scalarVectorMulL2 mu a u) v := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [scalarVectorMulL2_coe_ae mu a v, scalarVectorMulL2_coe_ae mu a u, ha]
    with x hv hu hre
  rw [hv, hu, inner_smul_right, inner_smul_left, Complex.conj_eq_iff_im.mpr hre]

end Holder

/-! ## The velocity difference as a scalar `L⁴` coefficient -/

section Difference

variable {w w' : WholePlaneC3LInf} {d : WholePlaneC3L4}

/-- The `i`-th coordinate of the bundled `L⁴` velocity difference represents the `i`-th
coordinate of the difference of the two `L∞` coefficients. -/
theorem wholePlaneCoordL4_coe_ae_sub
    (hd : (d : WholePlane → C3) =ᵐ[volume]
      fun y => (w : WholePlane → C3) y - (w' : WholePlane → C3) y) (i : Fin 3) :
    (wholePlaneCoordL4 i d : WholePlane → ℂ) =ᵐ[volume]
      ((wholePlaneCoordLInf i w - wholePlaneCoordLInf i w' : WholePlaneScalarLInf) :
        WholePlane → ℂ) := by
  have hw : ((wholePlaneCoordLInf i w : WholePlaneScalarLInf) : WholePlane → ℂ) =ᵐ[volume]
      fun a => (EuclideanSpace.proj (𝕜 := ℂ) i) ((w : WholePlane → C3) a) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := ∞)
      (μ := (volume : Measure WholePlane)) w
  have hw' : ((wholePlaneCoordLInf i w' : WholePlaneScalarLInf) : WholePlane → ℂ) =ᵐ[volume]
      fun a => (EuclideanSpace.proj (𝕜 := ℂ) i) ((w' : WholePlane → C3) a) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := ∞)
      (μ := (volume : Measure WholePlane)) w'
  filter_upwards [wholePlaneCoordL4_coe_ae i d, hd,
    Lp.coeFn_sub (wholePlaneCoordLInf i w) (wholePlaneCoordLInf i w'), hw, hw']
    with y hy hdy hsub hwy hwy'
  rw [hy, hdy, hsub]
  simp only [Pi.sub_apply]
  rw [hwy, hwy']
  simp

/-- Reality of the `L∞` coefficient difference, inherited from the `L⁴` representative. -/
theorem coordLInf_sub_im
    (hd : (d : WholePlane → C3) =ᵐ[volume]
      fun y => (w : WholePlane → C3) y - (w' : WholePlane → C3) y)
    (hreal : ∀ᵐ y ∂volume, ∀ i : Fin 3, ((d : WholePlane → C3) y i).im = 0) (i : Fin 3) :
    ∀ᵐ y ∂volume,
      (((wholePlaneCoordLInf i w - wholePlaneCoordLInf i w' : WholePlaneScalarLInf) :
        WholePlane → ℂ) y).im = 0 := by
  filter_upwards [(wholePlaneCoordL4_coe_ae_sub hd i).symm, wholePlaneCoordL4_coe_ae i d,
    hreal] with y hy hcoord hr
  rw [hy, hcoord]
  exact hr i

/-- **The Hölder `(4,4,2)` step.**  Multiplication by the velocity-difference coefficient sends
an `L²` field with an `L⁴` representative to `L²` with norm at most `‖d‖₄‖f‖₄`. -/
theorem norm_scalarVectorMulL2_coordLInf_sub_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (hd : (d : WholePlane → C3) =ᵐ[volume]
      fun y => (w : WholePlane → C3) y - (w' : WholePlane → C3) y) (i : Fin 3)
    (f2 : Lp E 2 (volume : Measure WholePlane)) (f4 : Lp E 4 (volume : Measure WholePlane))
    (hf : (f4 : WholePlane → E) =ᵐ[volume] (f2 : WholePlane → E)) :
    ‖scalarVectorMulL2 volume
        (wholePlaneCoordLInf i w - wholePlaneCoordLInf i w') f2‖ ≤ ‖d‖ * ‖f4‖ := by
  rw [scalarVectorMulL2_eq_scalarVectorMulL4 volume _ f2 (wholePlaneCoordL4 i d) f4
    (wholePlaneCoordL4_coe_ae_sub hd i) hf]
  exact (norm_scalarVectorMulL4_apply_le volume _ _).trans
    (mul_le_mul_of_nonneg_right (norm_wholePlaneCoordL4_apply_le i d) (norm_nonneg _))

end Difference

/-! ## Component `L⁴` representatives of an `H¹` field -/

/-- The `L⁴` representative of one component of the value of an `H¹(ℝ²;ℂ²)` field, obtained
from the scalar two-dimensional embedding `H¹(ℝ²) ↪ L⁴(ℝ²)`. -/
def horizontalComponentL4 (i : Fin 2) (b : WholePlaneC2H1) : WholePlaneScalarL4 :=
  wholePlaneScalarH1ToL4 (wholePlaneC2CoordH1 i b)

/-- The component `L⁴` representative agrees almost everywhere with the `L²` component. -/
theorem horizontalComponentL4_coe_ae (i : Fin 2) (b : WholePlaneC2H1) :
    (horizontalComponentL4 i b : WholePlane → ℂ) =ᵐ[volume]
      ((wholePlaneC2CoordL2 i (wholePlaneH1Embedding C2 b) : WholePlaneScalarL2) :
        WholePlane → ℂ) := by
  have h := wholePlaneScalarH1ToL4_coe_ae (wholePlaneC2CoordH1 i b)
  rwa [wholePlaneH1Embedding_c2CoordH1] at h

/-- The scalar `H¹ ↪ L⁴` constant bounds the component `L⁴` representative. -/
theorem norm_horizontalComponentL4_le (i : Fin 2) (b : WholePlaneC2H1) :
    ‖horizontalComponentL4 i b‖ ≤ ‖wholePlaneScalarH1ToL4‖ * ‖b‖ :=
  (wholePlaneScalarH1ToL4.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_wholePlaneC2CoordH1_apply_le i b)
      (ContinuousLinearMap.opNorm_nonneg wholePlaneScalarH1ToL4))

/-- The transverse divergence is bounded by twice the `H¹` norm. -/
theorem norm_horizontalDivergence_le_two (b : WholePlaneC2H1) :
    ‖horizontalDivergence b‖ ≤ 2 * ‖b‖ := by
  refine (norm_horizontalDivergence_apply_le b).trans ?_
  have h0 := norm_wholePlaneH1FirstDerivative_le C2 b 0
  have h1 := norm_wholePlaneH1FirstDerivative_le C2 b 1
  linarith

end HorizontalWeakForm

end

end FastDynamo
