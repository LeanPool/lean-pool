/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalFormNeumann
public import LeanPool.FastDynamo.Local.HorizontalFormResolvent

/-!
# The resolvent of the perturbed horizontal generator on a spectral set

This module runs the Neumann series of `FastDynamo/Local/HorizontalFormNeumann.lean` on the
horizontal pencil and performs the next step of the proof of `prop:local-seed` in the paper:

> Restricting to `L²` gives the resolvents of `𝓛_{h,δ}` on `Γ`.

Three ingredients are assembled.

* A **uniform bound for `𝔸_w(z)^{-1} : V^* → V`** on a compact set of invertible parameters.
  It is obtained from the factorisation `𝔸_w(z)^{-1} = (1-K(z))^{-1}G_z^{-1}F_1^{-1}` of
  `FastDynamo/Local/HorizontalFormResolvent.lean`: the two variable factors are endomorphisms
  of `V`, whose operator norms *do* synthesise at the concrete form domain and are continuous
  in `z`, and the third is one fixed antidual-valued constant.  This is the constant `B_Γ` of
  the paper's "the inverses `𝔸_{0,1}(z)^{-1}` are uniformly bounded on `Γ`".

* The **perturbed solution map** `S(z)^{-1}𝔸_w(z)^{-1}(pivot ·) : L² → H¹`, where
  `S(z) = 1 + 𝔸_w(z)^{-1}D` is the Neumann factor of the `z`-free form difference
  `D = 𝔸_{w',δ}(z) - 𝔸_w(z)`.  It is holomorphic in `z`, because both factors are.

* The **resolvent** `HasResolventOn (horizontalFormDeltaOperator N δ w') S`, built from that
  solution map through `formPencilHasResolventOn`, together with the resolvent difference
  bound `‖R_{δ,w'}(z) - R_w(z)‖_{L²→L²} ≤ ‖j‖c(1-c)^{-1}C` on the set.

All estimates are `z`-free in the perturbation: `horizontalPencilFormDelta_sub` of
`FastDynamo/Local/HorizontalFormDelta.lean` shows that `D` does not depend on `z`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set

/-- A family continuous on a compact parameter set is uniformly bounded in norm there.  This
is the elementary compactness step behind every uniform constant below.  It is stated for a
generic normed space so that the norm instance is resolved once, generically, rather than at
the concrete operator spaces of the horizontal form layer. -/
theorem exists_bound_norm_of_continuousOn_isCompact {E : Type*} [NormedAddCommGroup E]
    {S : Set ℂ} (hS : IsCompact S) {g : ℂ → E} (hg : ContinuousOn g S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ S, ‖g z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hS.image_of_continuousOn (continuous_norm.comp_continuousOn hg)).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  exact le_trans (hC (Set.mem_image_of_mem _ hz)) (le_max_left _ _)

namespace HorizontalWeakForm

/-- Splitting off the identity from a Neumann inverse composed with a solution map.  It is
proved generically in the form domain because the concrete operator spaces of the horizontal
layer are expensive for `rw` and `simp` to work with. -/
theorem formNeumannFactorInv_comp_sub {V X : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : ComplexAntiDual V →L[ℂ] V) (D : ComplexForm V) (R : X →L[ℂ] V) :
    (formNeumannFactorInv T D).comp R - R = (formNeumannFactorInv T D - 1).comp R := by
  rw [ContinuousLinearMap.sub_comp]
  exact congrArg (fun M : X →L[ℂ] V => (formNeumannFactorInv T D).comp R - M)
    (ContinuousLinearMap.id_comp R).symm

/-! ## A uniform bound for the antidual-valued inverse -/

/-- The factorisation bound `‖𝔸_w(z)^{-1}‖ ≤ ‖(1-K(z))^{-1}‖ (‖G_z^{-1}‖ ‖F_1^{-1}‖)`.  The two
variable factors are endomorphisms of `V`; only the constant `F_1^{-1}` is antidual-valued. -/
theorem complexFormInvNorm_horizontalPencilFormInverse_le (N : ℝ) (w : WholePlaneC3LInf)
    (z : ℂ) :
    complexFormInvNorm (horizontalPencilFormInverse N w z) ≤
      ‖(AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse‖ *
        (‖(freeHorizontalNormalizer N z).inverse‖ *
          complexFormInvNorm (freeHorizontalBaseInverse N)) := by
  refine le_trans (complexFormInvNorm_comp_le _ _) ?_
  refine mul_le_mul_of_nonneg_left ?_
    (ContinuousLinearMap.opNorm_nonneg
      (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse)
  exact complexFormInvNorm_comp_le _ _

/-- Continuity on a set of invertible parameters of the endomorphism `(1-K(z))^{-1}`. -/
theorem continuousOn_compactPencil_inverse (N : ℝ) (w : WholePlaneC3LInf) {S : Set ℂ}
    (hSre : ∀ z ∈ S, 0 < z.re)
    (hSinv : ∀ z ∈ S, (horizontalPencilForm N w z).IsInvertible) :
    ContinuousOn
      (fun z => (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse)
      S := by
  intro z hz
  have hanalytic : AnalyticAt ℂ
      (fun v => (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) v).inverse) z :=
    AnalyticFredholm.analyticAt_inverse
      (AnalyticFredholm.analyticAt_compactPencil
        (analyticAt_horizontalFredholmKernel N w (hSre z hz)))
      ((horizontalPencilForm_isInvertible_iff N w (hSre z hz)).mp (hSinv z hz))
  exact hanalytic.continuousAt.continuousWithinAt

/-- Continuity on the open right half plane of the endomorphism `G_z^{-1}`. -/
theorem continuousOn_freeNormalizer_inverse (N : ℝ) {S : Set ℂ}
    (hSre : ∀ z ∈ S, 0 < z.re) :
    ContinuousOn (fun z => (freeHorizontalNormalizer N z).inverse) S := by
  intro z hz
  have hanalytic : AnalyticAt ℂ (fun v => (freeHorizontalNormalizer N v).inverse) z :=
    AnalyticFredholm.analyticAt_inverse (analyticAt_freeHorizontalNormalizer N z)
      (freeHorizontalNormalizer_isInvertible N (hSre z hz))
  exact hanalytic.continuousAt.continuousWithinAt

/-- **The uniform bound `B` for `𝔸_w(z)^{-1} : V^* → V`** on a compact set of invertible
parameters of the open right half plane.  This is the paper's "the inverses
`𝔸_{0,1}(z)^{-1}` are uniformly bounded on `Γ`" (proof of `prop:local-seed`). -/
theorem exists_bound_complexFormInvNorm_horizontalPencilFormInverse (N : ℝ)
    (w : WholePlaneC3LInf) {S : Set ℂ} (hS : IsCompact S) (hSre : ∀ z ∈ S, 0 < z.re)
    (hSinv : ∀ z ∈ S, (horizontalPencilForm N w z).IsInvertible) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ S, complexFormInvNorm (horizontalPencilFormInverse N w z) ≤ B := by
  obtain ⟨C1, hC10, hC1⟩ :=
    exists_bound_norm_of_continuousOn_isCompact
      (E := WholePlaneC2H1 →L[ℂ] WholePlaneC2H1) hS
      (continuousOn_compactPencil_inverse N w hSre hSinv)
  obtain ⟨C2, hC20, hC2⟩ :=
    exists_bound_norm_of_continuousOn_isCompact
      (E := WholePlaneC2H1 →L[ℂ] WholePlaneC2H1) hS
      (continuousOn_freeNormalizer_inverse N hSre)
  have hbase : 0 ≤ complexFormInvNorm (freeHorizontalBaseInverse N) :=
    complexFormInvNorm_nonneg _
  refine ⟨C1 * (C2 * complexFormInvNorm (freeHorizontalBaseInverse N)),
    mul_nonneg hC10 (mul_nonneg hC20 hbase), fun z hz => ?_⟩
  refine le_trans (complexFormInvNorm_horizontalPencilFormInverse_le N w z) ?_
  refine mul_le_mul (hC1 z hz) ?_
    (mul_nonneg (ContinuousLinearMap.opNorm_nonneg (freeHorizontalNormalizer N z).inverse)
      hbase) hC10
  exact mul_le_mul_of_nonneg_right (hC2 z hz) hbase

/-- **The uniform `L² → H¹` bound for the solution map** on a compact set of invertible
parameters.  Together with the graph relation this is the form-norm half of
`eq:local-continuation-bound`. -/
theorem exists_bound_norm_horizontalFormSolution (N : ℝ) (w : WholePlaneC3LInf) {S : Set ℂ}
    (hS : IsCompact S) (hSre : ∀ z ∈ S, 0 < z.re)
    (hSinv : ∀ z ∈ S, (horizontalPencilForm N w z).IsInvertible) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ S, ‖horizontalFormSolution N w z‖ ≤ C := by
  refine exists_bound_norm_of_continuousOn_isCompact
    (E := WholePlaneC2L2 →L[ℂ] WholePlaneC2H1) hS ?_
  intro z hz
  exact ((analyticAt_horizontalFormSolution N w (hSre z hz)
    (hSinv z hz)).continuousAt).continuousWithinAt

/-! ## The `z`-free form difference -/

/-- The `z`-free difference `𝔸_{w',δ}(z) - 𝔸_w(z)` of `eq:form-small`. -/
def horizontalPencilDifference (N delta : ℝ) (w' w : WholePlaneC3LInf) :
    ComplexForm WholePlaneC2H1 :=
  (horizontalVelocityForm N w' - horizontalVelocityForm N w) +
    ((delta - 1 : ℝ) : ℂ) • horizontalDiffusionForm N

/-- The difference of the two pencils is the `z`-free form `horizontalPencilDifference`. -/
theorem horizontalPencilFormDelta_sub_eq_difference (N delta : ℝ)
    (w' w : WholePlaneC3LInf) (z : ℂ) :
    horizontalPencilFormDelta N delta w' z - horizontalPencilForm N w z =
      horizontalPencilDifference N delta w' w := by
  have h := horizontalPencilFormDelta_sub N delta 1 w' w z
  rw [horizontalPencilFormDelta_one] at h
  exact h

/-- The perturbed pencil is the unperturbed one plus the `z`-free difference. -/
theorem horizontalPencilFormDelta_eq_add_difference (N delta : ℝ)
    (w' w : WholePlaneC3LInf) (z : ℂ) :
    horizontalPencilFormDelta N delta w' z =
      horizontalPencilForm N w z + horizontalPencilDifference N delta w' w := by
  rw [← horizontalPencilFormDelta_sub_eq_difference N delta w' w z]
  abel

/-- The normalised difference `F_1^{-1}(𝔸_{w',δ} - 𝔸_w) : V → V`, a constant endomorphism of
the form domain.  It is what makes the Neumann factor holomorphic in `z`. -/
def horizontalNormalizedDifference (N delta : ℝ) (w' w : WholePlaneC3LInf) :
    WholePlaneC2H1 →L[ℂ] WholePlaneC2H1 :=
  (freeHorizontalBaseInverse N).comp (horizontalPencilDifference N delta w' w)

/-- The Neumann composite `𝔸_w(z)^{-1}D` written through the two variable endomorphism
factors and the constant normalised difference. -/
theorem horizontalPencilFormInverse_comp_difference (N delta : ℝ)
    (w' w : WholePlaneC3LInf) (z : ℂ) :
    (horizontalPencilFormInverse N w z).comp (horizontalPencilDifference N delta w' w) =
      (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse.comp
        ((freeHorizontalNormalizer N z).inverse.comp
          (horizontalNormalizedDifference N delta w' w)) :=
  rfl

/-! ## The perturbed solution map -/

/-- The Neumann smallness quantity `‖𝔸_w(z)^{-1}(𝔸_{w',δ}(z) - 𝔸_w(z))‖_{V→V}` at `z`; the
Neumann series converges exactly when it is `< 1`. -/
def horizontalNeumannSize (N delta : ℝ) (w' w : WholePlaneC3LInf) (z : ℂ) : ℝ :=
  ‖(horizontalPencilFormInverse N w z).comp (horizontalPencilDifference N delta w' w)‖

/-- The Neumann smallness quantity is nonnegative. -/
theorem horizontalNeumannSize_nonneg (N delta : ℝ) (w' w : WholePlaneC3LInf) (z : ℂ) :
    0 ≤ horizontalNeumannSize N delta w' w z :=
  ContinuousLinearMap.opNorm_nonneg ((horizontalPencilFormInverse N w z).comp
    (horizontalPencilDifference N delta w' w))

/-- The Neumann smallness quantity is at most `Bη`, the product of the inverse bound and the
form-perturbation bound of `eq:form-small`. -/
theorem horizontalNeumannSize_le (N delta : ℝ) (w' w : WholePlaneC3LInf) (z : ℂ) {B eta : ℝ}
    (hB : complexFormInvNorm (horizontalPencilFormInverse N w z) ≤ B)
    (heta : complexFormOpNorm (horizontalPencilDifference N delta w' w) ≤ eta) :
    horizontalNeumannSize N delta w' w z ≤ B * eta :=
  norm_comp_le_of_bounds hB heta

/-- The Neumann solution map `S(z)^{-1}𝔸_w(z)^{-1}(pivot ·) : L²(ℝ²;ℂ²) → H¹(ℝ²;ℂ²)` of the
perturbed weak pencil equation, a total function of `z`. -/
def horizontalDeltaSolution (N delta : ℝ) (w' w : WholePlaneC3LInf) (z : ℂ) :
    WholePlaneC2L2 →L[ℂ] WholePlaneC2H1 :=
  (formNeumannFactorInv (horizontalPencilFormInverse N w z)
      (horizontalPencilDifference N delta w' w)).comp (horizontalFormSolution N w z)

/-- **The perturbed pencil equation is solved by `horizontalDeltaSolution`.** -/
theorem horizontalPencilFormDelta_deltaSolution (N delta : ℝ) (w' w : WholePlaneC3LInf)
    {z : ℂ} (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible)
    (hlt : horizontalNeumannSize N delta w' w z < 1) (f : WholePlaneC2L2) :
    horizontalPencilFormDelta N delta w' z (horizontalDeltaSolution N delta w' w z f) =
      associatedFormPivot (wholePlaneH1Embedding C2) f := by
  have hAT := horizontalPencilForm_pencilFormInverse N w hz hinv
  have hfac : horizontalPencilFormDelta N delta w' z =
      horizontalPencilForm N w z + horizontalPencilDifference N delta w' w :=
    horizontalPencilFormDelta_eq_add_difference N delta w' w z
  have key := formNeumannInverse_right_apply (horizontalPencilForm N w z) hAT hlt
    (associatedFormPivot (wholePlaneH1Embedding C2) f)
  calc horizontalPencilFormDelta N delta w' z (horizontalDeltaSolution N delta w' w z f)
      = (horizontalPencilForm N w z + horizontalPencilDifference N delta w' w)
          (horizontalDeltaSolution N delta w' w z f) :=
        congrArg (fun a : ComplexForm WholePlaneC2H1 =>
          a (horizontalDeltaSolution N delta w' w z f)) hfac
    _ = associatedFormPivot (wholePlaneH1Embedding C2) f := key

/-- The weak pencil equation solved by the perturbed solution map, in the shape the generic
resolvent construction of `FastDynamo/Local/HorizontalFormResolvent.lean` asks for. -/
theorem horizontalDeltaSolution_weak (N delta : ℝ) (w' w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible)
    (hlt : horizontalNeumannSize N delta w' w z < 1) (f : WholePlaneC2L2)
    (phi : WholePlaneC2H1) :
    horizontalWeakFormDelta N delta w' (horizontalDeltaSolution N delta w' w z f) phi +
        z * inner ℂ (wholePlaneH1Embedding C2 phi)
          (wholePlaneH1Embedding C2 (horizontalDeltaSolution N delta w' w z f)) =
      inner ℂ (wholePlaneH1Embedding C2 phi) f := by
  have hsol := horizontalPencilFormDelta_deltaSolution N delta w' w hz hinv hlt f
  have happ := congrArg (fun g : ComplexAntiDual WholePlaneC2H1 => g phi) hsol
  have hleft := horizontalPencilFormDelta_apply N delta w' z
    (horizontalDeltaSolution N delta w' w z f) phi
  have hright : associatedFormPivot (wholePlaneH1Embedding C2) f phi =
      inner ℂ (wholePlaneH1Embedding C2 phi) f :=
    associatedFormPivot_apply (wholePlaneH1Embedding C2) f phi
  rw [← hleft, ← hright]
  exact happ

/-- Injectivity of the perturbed pencil form in the weak formulation. -/
theorem horizontalPencilFormDelta_injective_weak (N delta : ℝ) (w' w : WholePlaneC3LInf)
    {z : ℂ} (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible)
    (hlt : horizontalNeumannSize N delta w' w z < 1) (e : WholePlaneC2H1)
    (he : ∀ phi : WholePlaneC2H1,
      horizontalWeakFormDelta N delta w' e phi +
        z * inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneH1Embedding C2 e) = 0) :
    e = 0 := by
  have hzero : horizontalPencilFormDelta N delta w' z e = 0 := by
    refine ContinuousLinearMap.ext fun phi => ?_
    rw [horizontalPencilFormDelta_apply]
    exact he phi
  have hfac : horizontalPencilFormDelta N delta w' z =
      horizontalPencilForm N w z + horizontalPencilDifference N delta w' w :=
    horizontalPencilFormDelta_eq_add_difference N delta w' w z
  have h0 : (horizontalPencilForm N w z + horizontalPencilDifference N delta w' w) e = 0 :=
    (congrArg (fun a : ComplexForm WholePlaneC2H1 => a e) hfac).symm.trans hzero
  exact eq_zero_of_formNeumann_apply_eq_zero (horizontalPencilForm N w z)
    (horizontalPencilForm_pencilFormInverse N w hz hinv)
    (horizontalPencilFormInverse_pencilForm N w hz hinv) hlt h0

/-! ## Holomorphy of the perturbed solution map -/

/-- The Neumann factor of the perturbed pencil is holomorphic in the spectral parameter. -/
theorem analyticAt_horizontalNeumannFactor (N delta : ℝ) (w' w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible) :
    AnalyticAt ℂ (fun v => formNeumannFactor (horizontalPencilFormInverse N w v)
      (horizontalPencilDifference N delta w' w)) z := by
  have hfun : (fun v : ℂ => formNeumannFactor (horizontalPencilFormInverse N w v)
        (horizontalPencilDifference N delta w' w)) =
      fun v : ℂ => 1 +
        (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) v).inverse.comp
          ((freeHorizontalNormalizer N v).inverse.comp
            (horizontalNormalizedDifference N delta w' w)) := by
    funext v
    exact congrArg (fun M : WholePlaneC2H1 →L[ℂ] WholePlaneC2H1 => 1 + M)
      (horizontalPencilFormInverse_comp_difference N delta w' w v)
  rw [hfun]
  have h1 : AnalyticAt ℂ (fun v : ℂ => (freeHorizontalNormalizer N v).inverse) z :=
    AnalyticFredholm.analyticAt_inverse (analyticAt_freeHorizontalNormalizer N z)
      (freeHorizontalNormalizer_isInvertible N hz)
  have h2 : AnalyticAt ℂ
      (fun v : ℂ =>
        (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) v).inverse) z :=
    AnalyticFredholm.analyticAt_inverse
      (AnalyticFredholm.analyticAt_compactPencil (analyticAt_horizontalFredholmKernel N w hz))
      ((horizontalPencilForm_isInvertible_iff N w hz).mp hinv)
  exact analyticAt_const.add (FiniteDimensionalSchur.analyticAt_clm_comp h2
    (analyticAt_clm_comp_const h1 (horizontalNormalizedDifference N delta w' w)))

/-- The inverse of the Neumann factor is holomorphic where the series converges. -/
theorem analyticAt_horizontalNeumannFactorInv (N delta : ℝ) (w' w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible)
    (hlt : horizontalNeumannSize N delta w' w z < 1) :
    AnalyticAt ℂ (fun v => formNeumannFactorInv (horizontalPencilFormInverse N w v)
      (horizontalPencilDifference N delta w' w)) z :=
  AnalyticFredholm.analyticAt_inverse (analyticAt_horizontalNeumannFactor N delta w' w hz hinv)
    (isInvertible_formNeumannFactor hlt)

/-- **The perturbed solution map is holomorphic.** -/
theorem analyticAt_horizontalDeltaSolution (N delta : ℝ) (w' w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible)
    (hlt : horizontalNeumannSize N delta w' w z < 1) :
    AnalyticAt ℂ (horizontalDeltaSolution N delta w' w) z :=
  FiniteDimensionalSchur.analyticAt_clm_comp
    (analyticAt_horizontalNeumannFactorInv N delta w' w hz hinv hlt)
    (analyticAt_horizontalFormSolution N w hz hinv)

/-! ## The resolvent of the perturbed generator -/

/-- **The resolvent of `𝓛_{w',δ}` on a set of Neumann-small parameters.**  This is the
paper's "restricting to `L²` gives the resolvents of `𝓛_{h,δ}` on `Γ`" (proof of
`prop:local-seed`). -/
def horizontalDeltaHasResolventOn (N delta : ℝ) (w' w : WholePlaneC3LInf) (S : Set ℂ)
    (hSre : ∀ z ∈ S, 0 < z.re)
    (hSinv : ∀ z ∈ S, (horizontalPencilForm N w z).IsInvertible)
    (hSlt : ∀ z ∈ S, horizontalNeumannSize N delta w' w z < 1) :
    HasResolventOn (horizontalFormDeltaOperator N delta w') S :=
  formPencilHasResolventOn (wholePlaneH1Embedding C2) wholePlaneC2H1Embedding_injective
    denseRange_wholePlaneC2H1Embedding (horizontalWeakFormDelta N delta w')
    (horizontalDeltaSolution N delta w' w)
    (fun z hz f phi =>
      horizontalDeltaSolution_weak N delta w' w (hSre z hz) (hSinv z hz) (hSlt z hz) f phi)
    (fun z hz e he =>
      horizontalPencilFormDelta_injective_weak N delta w' w (hSre z hz) (hSinv z hz)
        (hSlt z hz) e he)
    (fun z hz =>
      ((analyticAt_horizontalDeltaSolution N delta w' w (hSre z hz) (hSinv z hz)
        (hSlt z hz)).continuousAt).continuousWithinAt)

/-- The ambient state resolvent of `𝓛_{w',δ}` is `j` composed with the perturbed solution
map. -/
theorem horizontalDeltaHasResolventOn_stateResolvent (N delta : ℝ)
    (w' w : WholePlaneC3LInf) (S : Set ℂ) (hSre : ∀ z ∈ S, 0 < z.re)
    (hSinv : ∀ z ∈ S, (horizontalPencilForm N w z).IsInvertible)
    (hSlt : ∀ z ∈ S, horizontalNeumannSize N delta w' w z < 1) {z : ℂ} (hz : z ∈ S) :
    (horizontalDeltaHasResolventOn N delta w' w S hSre hSinv hSlt).stateResolvent z =
      (wholePlaneH1Embedding C2).comp (horizontalDeltaSolution N delta w' w z) :=
  formPencilHasResolventOn_stateResolvent _ _ _ _ _ _ _ _ hz

/-! ## The resolvent difference -/

/-- The perturbed solution map differs from the unperturbed one by `(S(z)^{-1}-1)` applied on
the left. -/
theorem horizontalDeltaSolution_sub (N delta : ℝ) (w' w : WholePlaneC3LInf) (z : ℂ) :
    horizontalDeltaSolution N delta w' w z - horizontalFormSolution N w z =
      (formNeumannFactorInv (horizontalPencilFormInverse N w z)
          (horizontalPencilDifference N delta w' w) - 1).comp
        (horizontalFormSolution N w z) := by
  exact formNeumannFactorInv_comp_sub _ _ _

/-- **The resolvent difference bound on the `L² → H¹` solution maps.** -/
theorem norm_horizontalDeltaSolution_sub_le (N delta : ℝ) (w' w : WholePlaneC3LInf) (z : ℂ)
    {c C : ℝ} (hc : horizontalNeumannSize N delta w' w z ≤ c) (hc1 : c < 1)
    (hC : ‖horizontalFormSolution N w z‖ ≤ C) :
    ‖horizontalDeltaSolution N delta w' w z - horizontalFormSolution N w z‖ ≤
      c * (1 - c)⁻¹ * C := by
  have hc0 : 0 ≤ c := le_trans (horizontalNeumannSize_nonneg N delta w' w z) hc
  have hden : 0 < 1 - c := by linarith
  rw [horizontalDeltaSolution_sub]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  refine mul_le_mul (norm_formNeumannFactorInv_sub_one_le hc hc1) hC
    (ContinuousLinearMap.opNorm_nonneg (horizontalFormSolution N w z))
    (mul_nonneg hc0 (le_of_lt (inv_pos.mpr hden)))

/-- **The `L² → L²` resolvent difference bound on a Neumann-small set.**  This is the
step of the proof of `prop:local-seed` between the Neumann-series bound and the integration
over `Γ` that bounds the Riesz projections. -/
theorem norm_horizontalDeltaStateResolvent_sub_le (N delta : ℝ) (w' w : WholePlaneC3LInf)
    (z : ℂ) {c C : ℝ} (hc : horizontalNeumannSize N delta w' w z ≤ c) (hc1 : c < 1)
    (hC : ‖horizontalFormSolution N w z‖ ≤ C) :
    ‖(wholePlaneH1Embedding C2).comp (horizontalDeltaSolution N delta w' w z) -
        (wholePlaneH1Embedding C2).comp (horizontalFormSolution N w z)‖ ≤
      ‖wholePlaneH1Embedding C2‖ * (c * (1 - c)⁻¹ * C) := by
  rw [← ContinuousLinearMap.comp_sub]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  exact mul_le_mul_of_nonneg_left (norm_horizontalDeltaSolution_sub_le N delta w' w z hc hc1 hC)
    (ContinuousLinearMap.opNorm_nonneg (wholePlaneH1Embedding C2))

end HorizontalWeakForm

end

end FastDynamo
