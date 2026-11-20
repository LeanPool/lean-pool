/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalModeH1
public import LeanPool.FastDynamo.Local.PonomarenkoSegmentRoot
public import LeanPool.FastDynamo.Local.HorizontalFormOperator
public import LeanPool.FastDynamo.Operator.WholePlanePivotAntiDual

/-!
# The weak eigenvalue identity for the horizontal Ponomarenko mode

This module assembles the last step of the proof of `lem:jump-horizontal-mode`, for the flow
of `eq:jump-flow`:

* the discontinuous screw flow `V⁰ = 1_{r<1}(Ω r e_θ + U e₃)` at a **free** angular speed `Ω`
  and `U = -Ω/N` (`eq:jump-flow`), as a whole-plane `L∞` coefficient;
* the exact decomposition of the transport-stretching form `𝔩_w(b, ·)` into the repository's
  two pivot functionals, hence its canonical realization as a tempered distribution;
* the resulting equivalence

  `𝔩_{V⁰}(b,φ) = -λ_*⟨b,φ⟩ for all φ ∈ H¹`  ↔  a single distributional identity on `ℝ²`,

  where `λ_* = κ² - N²` (`eq:local-eigenvalue`);
* the deduction, from that identity, that `b` lies in `D(A_{V⁰})` and is an eigenvector with
  eigenvalue `λ_*`, in the repository's `DomainOperator` vocabulary.

The decomposition needs no hypothesis: the two-component form has no curl term and no solenoidal
constraint, so all five of its terms are pivots of the two generic maps
`wholePlaneH1Embedding C2` and `wholePlaneH1FirstDerivative C2 j`.

What is *not* proved here is the distributional identity itself; it is stated verbatim as
`HorizontalModeDistributionalEquation` and carried as a hypothesis, which
`Local/HorizontalModeEigenpair.lean` discharges.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace HorizontalMode

open Complex MeasureTheory Metric Set
open scoped LineDeriv
open HorizontalWeakForm
open PonomarenkoFreeOmegaInterface

/-! ## The free-`Ω` jump velocity -/

/-- The interior value `V_in = Ω r e_θ + U e₃ = (-Ω y₂, Ω y₁, U)` of the screw flow at a free
angular speed `Ω` and axial speed `U` (`eq:jump-flow`). -/
def horizontalJumpInteriorVelocity (Omega U : ℝ) (y : WholePlane) : C3 :=
  WithLp.toLp 2 ![
    -(Omega : ℂ) * (y (1 : Fin 2) : ℂ),
    (Omega : ℂ) * (y (0 : Fin 2) : ℂ),
    (U : ℂ)]

/-- The interior screw value is continuous, being linear plus a constant. -/
theorem horizontalJumpInteriorVelocity_continuous (Omega U : ℝ) :
    Continuous (horizontalJumpInteriorVelocity Omega U) := by
  unfold horizontalJumpInteriorVelocity
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℂ)).comp (continuous_pi ?_)
  intro i
  fin_cases i <;> fun_prop

/-- The free-`Ω` jump velocity, with the interior representative on the closed unit disk and
the zero representative outside. -/
def horizontalJumpVelocity (Omega U : ℝ) (y : WholePlane) : C3 := by
  classical
  exact if y ∈ wholePlaneUnitDisk then horizontalJumpInteriorVelocity Omega U y else 0

/-- Inside the closed unit disk the chosen representative is the interior screw value. -/
@[simp] theorem horizontalJumpVelocity_of_norm_le
    (Omega U : ℝ) {y : WholePlane} (hy : ‖y‖ ≤ 1) :
    horizontalJumpVelocity Omega U y = horizontalJumpInteriorVelocity Omega U y := by
  have hmem : y ∈ wholePlaneUnitDisk := by
    simpa [wholePlaneUnitDisk, mem_closedBall, dist_zero_right] using hy
  simp [horizontalJumpVelocity, hmem]

/-- Outside the closed unit disk the chosen representative vanishes. -/
@[simp] theorem horizontalJumpVelocity_of_one_lt_norm
    (Omega U : ℝ) {y : WholePlane} (hy : 1 < ‖y‖) :
    horizontalJumpVelocity Omega U y = 0 := by
  have hmem : y ∉ wholePlaneUnitDisk := by
    simp only [wholePlaneUnitDisk, mem_closedBall, dist_zero_right]
    exact not_le_of_gt hy
  simp [horizontalJumpVelocity, hmem]

/-- The jump velocity is strongly measurable despite its unit-circle discontinuity. -/
theorem horizontalJumpVelocity_stronglyMeasurable (Omega U : ℝ) :
    StronglyMeasurable (horizontalJumpVelocity Omega U) := by
  classical
  unfold horizontalJumpVelocity
  exact StronglyMeasurable.piecewise measurableSet_wholePlaneUnitDisk
    (horizontalJumpInteriorVelocity_continuous Omega U).stronglyMeasurable
    stronglyMeasurable_const

/-- A global pointwise bound for the jump velocity. -/
theorem exists_forall_norm_horizontalJumpVelocity_le (Omega U : ℝ) :
    ∃ C : ℝ, ∀ y : WholePlane, ‖horizontalJumpVelocity Omega U y‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : WholePlane) 1).bddAbove_image
    (horizontalJumpInteriorVelocity_continuous Omega U).norm.continuousOn
  refine ⟨max C 0, fun y ↦ ?_⟩
  by_cases hy : ‖y‖ ≤ 1
  · rw [horizontalJumpVelocity_of_norm_le Omega U hy]
    refine le_trans (hC ?_) (le_max_left C 0)
    exact mem_image_of_mem _ (by simpa [mem_closedBall, dist_zero_right] using hy)
  · rw [horizontalJumpVelocity_of_one_lt_norm Omega U (lt_of_not_ge hy), norm_zero]
    exact le_max_right C 0

/-- The free-`Ω` jump velocity is essentially bounded. -/
theorem horizontalJumpVelocity_memLp_top (Omega U : ℝ) :
    MemLp (horizontalJumpVelocity Omega U) ⊤ (volume : Measure WholePlane) := by
  obtain ⟨C, hC⟩ := exists_forall_norm_horizontalJumpVelocity_le Omega U
  exact memLp_top_of_bound
    (horizontalJumpVelocity_stronglyMeasurable Omega U).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

/-- The whole-plane `L∞` coefficient represented by the free-`Ω` jump velocity `V⁰`. -/
def horizontalJumpVelocityLInf (Omega U : ℝ) : WholePlaneC3LInf :=
  (horizontalJumpVelocity_memLp_top Omega U).toLp (horizontalJumpVelocity Omega U)

/-- The bundled coefficient has the concrete closed-disk jump field as a representative. -/
theorem horizontalJumpVelocityLInf_coe_ae (Omega U : ℝ) :
    (horizontalJumpVelocityLInf Omega U : WholePlane → C3) =ᵐ[volume]
      horizontalJumpVelocity Omega U :=
  MemLp.coeFn_toLp _

/-- The certified velocity `V⁰ = 1_{r<1}(Ω r e_θ + U e₃)` with the paper's `U = -Ω/N`. -/
def horizontalModeVelocity (N Omega : ℝ) : WholePlaneC3LInf :=
  horizontalJumpVelocityLInf Omega (jumpAxialSpeed N Omega)

/-! ## Coordinate adjointness on two-component `L²` -/

/-- Coordinate insertion is the adjoint of coordinate extraction on `L²(ℝ²;ℂ²)`. -/
theorem inner_wholePlaneScalarToC2CoordL2 (j : Fin 2) (f : WholePlaneC2L2)
    (g : WholePlaneScalarL2) :
    inner ℂ f (wholePlaneScalarToC2CoordL2 j g) =
      inner ℂ (wholePlaneC2CoordL2 j f) g := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    (scalarToVecPoint (ι := Fin 2) j).coeFn_compLpL (p := 2)
      (μ := (volume : Measure WholePlane)) g,
    (EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL (p := 2)
      (μ := (volume : Measure WholePlane)) f] with x hg hf
  have hgx : ((wholePlaneScalarToC2CoordL2 j g : WholePlaneC2L2) : WholePlane → C2) x =
      scalarToVecPoint (ι := Fin 2) j ((g : WholePlane → ℂ) x) := hg
  have hfx : ((wholePlaneC2CoordL2 j f : WholePlaneScalarL2) : WholePlane → ℂ) x =
      ((f : WholePlane → C2) x) j := hf
  rw [hgx, hfx, PiLp.inner_apply]
  fin_cases j <;> simp [scalarToVecPoint, RCLike.inner_apply]

/-! ## The two pivot fields of the weak form -/

/-- The `L²` field paired against `∂_jφ` in `𝔩_w(b,φ)`: the weak derivative `∂_jb` plus the
stretching contribution `w_⊥ b_j` (`eq:jump-sectorial-form`, last line). -/
def horizontalWeakFormDerivativePivot (w : WholePlaneC3LInf) (b : WholePlaneC2H1)
    (j : Fin 2) : WholePlaneC2L2 :=
  wholePlaneH1FirstDerivative C2 j b +
    ∑ i : Fin 2, wholePlaneScalarToC2CoordL2 i
      (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf i.castSucc w)
        (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 b)))

/-- The `L²` field paired against `φ` in `𝔩_w(b,φ)`: the zero-order terms
`N²b + w_⊥·∇_⊥b + iN w₃b + w_⊥(Div_⊥ b)`. -/
def horizontalWeakFormMassPivot (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) :
    WholePlaneC2L2 :=
  ((N : ℂ) ^ 2) • wholePlaneH1Embedding C2 b + horizontalTransport w b +
    (Complex.I * (N : ℂ)) • scalarVectorMulL2 (E := C2) volume (wholePlaneCoordLInf 2 w)
      (wholePlaneH1Embedding C2 b) +
    ∑ i : Fin 2, wholePlaneScalarToC2CoordL2 i
      (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf i.castSucc w)
        (horizontalDivergence b))

/-- Expansion of the derivative pivot pairing. -/
private theorem inner_horizontalWeakFormDerivativePivot (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) (j : Fin 2) :
    inner ℂ (wholePlaneH1FirstDerivative C2 j phi)
        (horizontalWeakFormDerivativePivot w b j) =
      inner ℂ (wholePlaneH1FirstDerivative C2 j phi)
          (wholePlaneH1FirstDerivative C2 j b) +
        ∑ i : Fin 2,
          inner ℂ (wholePlaneC2CoordL2 i (wholePlaneH1FirstDerivative C2 j phi))
            (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf i.castSucc w)
              (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 b))) := by
  simp only [horizontalWeakFormDerivativePivot, inner_add_right, inner_sum,
    inner_wholePlaneScalarToC2CoordL2]

/-- Expansion of the mass pivot pairing. -/
private theorem inner_horizontalWeakFormMassPivot (N : ℝ) (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    inner ℂ (wholePlaneH1Embedding C2 phi) (horizontalWeakFormMassPivot N w b) =
      (N : ℂ) ^ 2 *
          inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneH1Embedding C2 b) +
        inner ℂ (wholePlaneH1Embedding C2 phi) (horizontalTransport w b) +
        Complex.I * (N : ℂ) *
          inner ℂ (wholePlaneH1Embedding C2 phi)
            (scalarVectorMulL2 (E := C2) volume (wholePlaneCoordLInf 2 w)
              (wholePlaneH1Embedding C2 b)) +
        ∑ i : Fin 2,
          inner ℂ (wholePlaneC2CoordL2 i (wholePlaneH1Embedding C2 phi))
            (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf i.castSucc w)
              (horizontalDivergence b)) := by
  simp only [horizontalWeakFormMassPivot, inner_add_right, inner_smul_right, inner_sum,
    inner_wholePlaneScalarToC2CoordL2]

/-- The exact decomposition of `𝔩_w(b, ·)` into the repository's two pivot functionals. -/
theorem horizontalWeakForm_eq_pivot (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) :
    horizontalWeakForm N w b =
      (∑ j : Fin 2, associatedFormPivot (wholePlaneH1FirstDerivative C2 j)
        (horizontalWeakFormDerivativePivot w b j)) +
      associatedFormPivot (wholePlaneH1Embedding C2)
        (horizontalWeakFormMassPivot N w b) := by
  apply ContinuousLinearMap.ext
  intro phi
  simp only [add_apply,
    associatedFormPivot_apply, inner_horizontalWeakFormDerivativePivot,
    inner_horizontalWeakFormMassPivot, horizontalWeakForm_apply,
    horizontalDiffusionForm_apply, horizontalStretchDivergenceForm_apply,
    horizontalStretchGradientForm_apply, horizontalTransportForm_apply,
    horizontalAxialForm_apply, Fin.sum_univ_two]
  ring

/-! ## Tempered realization -/

/-- Elementary regrouping in an additive group, used to move the sign of the distributional
derivative term across the eigenvalue equation. -/
private theorem neg_add_eq_neg_iff {G : Type*} [AddCommGroup G] (A B C : G) :
    (-A + B = -C) ↔ A = B + C := by
  constructor
  · intro h
    have h0 : B + C = A := by
      calc B + C = (-A + B) + C + A := by abel
        _ = -C + C + A := by rw [h]
        _ = A := by abel
    exact h0.symm
  · intro h
    rw [h]
    abel

/-- The canonical tempered-distribution realization of `𝔩_w(b, ·) ∈ H⁻¹(ℝ²;ℂ²)`. -/
theorem wholePlaneH1AntiDualToTempered_horizontalWeakForm
    (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) :
    wholePlaneH1AntiDualToTempered C2 (horizontalWeakForm N w b) =
      -(∑ j : Fin 2, ∂_{wholePlaneBasis j}
        (wholePlaneL2ToTempered C2 (horizontalWeakFormDerivativePivot w b j))) +
      wholePlaneL2ToTempered C2 (horizontalWeakFormMassPivot N w b) := by
  rw [horizontalWeakForm_eq_pivot, map_add, map_sum,
    wholePlaneH1AntiDualToTempered_associatedFormPivot_embedding]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact wholePlaneH1AntiDualToTempered_associatedFormPivot_firstDerivative C2 j _

/-! ## The distributional form of the eigenvalue equation -/

/-- The distributional identity equivalent to the weak eigenvalue equation
`𝔩_w(b,φ) = -λ⟨b,φ⟩` for every `φ ∈ H¹(ℝ²;ℂ²)`.

Unfolding the two pivot fields, this reads

`Σ_j ∂_j(∂_jb + w_⊥ b_j) = N²b + w_⊥·∇_⊥b + iNw₃b + w_⊥(Div_⊥b) + λ b`

in the sense of tempered distributions on `ℝ²`, which after cancelling the `w_⊥(Div_⊥b)` term
is exactly `(Δ_⊥ - N²)b - w_⊥·∇_⊥b - iNw₃b + (b·∇_⊥)w_⊥ = λ b` of
`eq:horizontal-induction`. -/
def HorizontalModeDistributionalEquation (N : ℝ) (w : WholePlaneC3LInf)
    (b : WholePlaneC2H1) (lam : ℂ) : Prop :=
  (∑ j : Fin 2, ∂_{wholePlaneBasis j}
      (wholePlaneL2ToTempered C2 (horizontalWeakFormDerivativePivot w b j))) =
    wholePlaneL2ToTempered C2
      (horizontalWeakFormMassPivot N w b + lam • wholePlaneH1Embedding C2 b)

/-- The weak eigenvalue identity of the paper, `𝔩_w(b,φ) = -λ⟨b,φ⟩` for every `φ`. -/
def HorizontalModeWeakEquation (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1)
    (lam : ℂ) : Prop :=
  ∀ phi : WholePlaneC2H1,
    horizontalWeakForm N w b phi =
      -(lam * inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneH1Embedding C2 b))

/-- The weak eigenvalue identity is exactly the distributional identity.

This is the semantic bridge that turns the remaining interface computation of
`lem:jump-horizontal-mode` into a statement about tempered distributions on `ℝ²`. -/
theorem horizontalModeWeakEquation_iff_distributional
    (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) (lam : ℂ) :
    HorizontalModeWeakEquation N w b lam ↔
      HorizontalModeDistributionalEquation N w b lam := by
  have hpivotIff : HorizontalModeWeakEquation N w b lam ↔
      horizontalWeakForm N w b =
        associatedFormPivot (wholePlaneH1Embedding C2)
          ((-lam) • wholePlaneH1Embedding C2 b) := by
    constructor
    · intro h
      apply ContinuousLinearMap.ext
      intro phi
      rw [h phi, associatedFormPivot_apply, inner_smul_right]
      ring
    · intro h phi
      rw [DFunLike.congr_fun h phi, associatedFormPivot_apply, inner_smul_right]
      ring
  have hsplit : wholePlaneH1AntiDualToTempered C2
        (associatedFormPivot (wholePlaneH1Embedding C2)
          ((-lam) • wholePlaneH1Embedding C2 b)) =
      -(lam • wholePlaneL2ToTempered C2 (wholePlaneH1Embedding C2 b)) := by
    rw [wholePlaneH1AntiDualToTempered_associatedFormPivot_embedding, map_smul, neg_smul]
  have hdist : HorizontalModeDistributionalEquation N w b lam ↔
      (∑ j : Fin 2, ∂_{wholePlaneBasis j}
        (wholePlaneL2ToTempered C2 (horizontalWeakFormDerivativePivot w b j))) =
        wholePlaneL2ToTempered C2 (horizontalWeakFormMassPivot N w b) +
          lam • wholePlaneL2ToTempered C2 (wholePlaneH1Embedding C2 b) := by
    unfold HorizontalModeDistributionalEquation
    rw [map_add, map_smul]
  constructor
  · intro h
    apply hdist.2
    have ht := congrArg (wholePlaneH1AntiDualToTempered C2) (hpivotIff.1 h)
    rw [wholePlaneH1AntiDualToTempered_horizontalWeakForm, hsplit] at ht
    exact (neg_add_eq_neg_iff _ _ _).1 ht
  · intro h
    apply hpivotIff.2
    apply wholePlaneH1AntiDualToTempered_injective C2
    refine Eq.trans (wholePlaneH1AntiDualToTempered_horizontalWeakForm N w b) ?_
    refine Eq.trans ?_ hsplit.symm
    exact (neg_add_eq_neg_iff _ _ _).2 (hdist.1 h)

/-! ## From the weak identity to an eigenpair of `A_w` -/

/-- The weak identity puts `b` in the domain of `A_w` with `A_w b = λ b`. -/
theorem exists_horizontalFormDomain_of_weakEquation
    (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) (lam : ℂ)
    (h : HorizontalModeWeakEquation N w b lam) :
    ∃ u : HorizontalFormDomain N w,
      u.1.1 = b ∧
        (horizontalFormOperator N w).op u = lam • wholePlaneH1Embedding C2 b := by
  apply (horizontalFormOperator_exists_iff N w b (lam • wholePlaneH1Embedding C2 b)).2
  intro phi
  rw [h phi, inner_smul_right]

/-- The weak identity makes `b` an eigenvector of the form operator `A_w` with eigenvalue
`λ`, in the repository's `DomainOperator` vocabulary. -/
theorem isEigenpair_of_weakEquation
    (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) (lam : ℂ)
    (hne : wholePlaneH1Embedding C2 b ≠ 0)
    (h : HorizontalModeWeakEquation N w b lam) :
    ∃ u : HorizontalFormDomain N w,
      u.1.1 = b ∧ (horizontalFormOperator N w).IsEigenpair lam u := by
  obtain ⟨u, hu, hop⟩ := exists_horizontalFormDomain_of_weakEquation N w b lam h
  have hemb : (horizontalFormOperator N w).embedding u = wholePlaneH1Embedding C2 b :=
    (horizontalFormOperator_embedding_apply N w u).trans
      (congrArg (wholePlaneH1Embedding C2) hu)
  refine ⟨u, hu, fun hzero ↦ hne (hemb.symm.trans hzero), ?_⟩
  exact hop.trans (congrArg (fun z : WholePlaneC2L2 ↦ lam • z) hemb).symm

/-! ## The certified mode -/

variable {N Omega : ℝ} {kappa : ℂ}

/-- The two-component eigenmode `b` of `lem:jump-horizontal-mode` attached to certified
free-`Ω` interface data. -/
def horizontalMode (hd : CertifiedInterfaceData N Omega kappa) : WholePlaneC2H1 :=
  horizontalModeH1 kappa hd.kappa_re_pos

/-- The growing eigenvalue `λ_* = κ² - N²` of `eq:local-eigenvalue`, under the name the
two-component chain uses.  It
is **the same definition** as `ponomarenkoLocalEigenvalue` of `Local/PonomarenkoSegmentRoot.lean`
— an `abbrev`, not a copy — so the two cannot drift apart; the coincidence is recorded
explicitly by `horizontalEigenvalue_eq_ponomarenkoLocalEigenvalue`. -/
abbrev horizontalEigenvalue (N : ℝ) (kappa : ℂ) : ℂ :=
  ponomarenkoLocalEigenvalue N kappa

/-- The two names of `λ_* = κ² - N²` denote one value. -/
theorem horizontalEigenvalue_eq_ponomarenkoLocalEigenvalue (N : ℝ) (kappa : ℂ) :
    horizontalEigenvalue N kappa = ponomarenkoLocalEigenvalue N kappa :=
  rfl

/-- The certified eigenvalue has positive real part: this is the paper's
`re λ_* ≥ (7/16)ϱ² - N² > 0`. -/
theorem re_ponomarenkoLocalEigenvalue_pos (hd : CertifiedInterfaceData N Omega kappa) :
    0 < (ponomarenkoLocalEigenvalue N kappa).re :=
  hd.spectral_growth

/-- The certified mode is non-zero in `H¹`. -/
theorem horizontalMode_ne_zero (hd : CertifiedInterfaceData N Omega kappa) :
    horizontalMode hd ≠ 0 :=
  horizontalModeH1_ne_zero hd.kappa_re_pos hd.K0_ne_zero

/-- The `L²` value of the certified mode is non-zero. -/
theorem wholePlaneH1Embedding_horizontalMode_ne_zero
    (hd : CertifiedInterfaceData N Omega kappa) :
    wholePlaneH1Embedding C2 (horizontalMode hd) ≠ 0 :=
  horizontalModeL2_ne_zero hd.kappa_re_pos hd.K0_ne_zero

/-- The weak eigenvalue identity of `lem:jump-horizontal-mode` for the certified data:
`𝔩_{V⁰}(b,φ) = -λ_*⟨b,φ⟩` for every `φ ∈ H¹(ℝ²;ℂ²)`. -/
def HorizontalModeWeakIdentity (hd : CertifiedInterfaceData N Omega kappa) : Prop :=
  HorizontalModeWeakEquation N (horizontalModeVelocity N Omega) (horizontalMode hd)
    (ponomarenkoLocalEigenvalue N kappa)

/-- Granting the weak identity, the certified mode is an eigenvector of the form operator
`A_{V⁰}` with eigenvalue `λ_* = κ² - N²`.  This is the conclusion
`b ∈ D(A_{V⁰})`, `A_{V⁰}b = λ_*b` of the proof of `lem:jump-horizontal-mode`. -/
theorem horizontalMode_isEigenpair (hd : CertifiedInterfaceData N Omega kappa)
    (hweak : HorizontalModeWeakIdentity hd) :
    ∃ u : HorizontalFormDomain N (horizontalModeVelocity N Omega),
      u.1.1 = horizontalMode hd ∧
        (horizontalFormOperator N (horizontalModeVelocity N Omega)).IsEigenpair
          (ponomarenkoLocalEigenvalue N kappa) u :=
  isEigenpair_of_weakEquation N (horizontalModeVelocity N Omega) (horizontalMode hd)
    (ponomarenkoLocalEigenvalue N kappa)
    (wholePlaneH1Embedding_horizontalMode_ne_zero hd) hweak

/-! ## Decay of the certified mode -/

/-- Exponential `L²` tail bound for the certified mode, in the form the witness truncation
`f_* = χ b/‖b‖` of the local-seed step needs. -/
theorem horizontalMode_tail_le (hd : CertifiedInterfaceData N Omega kappa)
    {L : ℝ} (hL : 1 ≤ L) :
    ∫ y in {y : WholePlane | L ≤ ‖y‖}, ‖horizontalModeField kappa y‖ ^ 2 ≤
      horizontalModeTailConstant kappa * Real.exp (-kappa.re * (L - 1)) :=
  integral_sq_norm_horizontalModeField_tail_le hd.kappa_re_pos hL

end HorizontalMode
end FastDynamo
