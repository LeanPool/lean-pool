/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.CoefficientPairing
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ZeroTraceSobolev

/-!
# AlphaShiftedWeakSolution

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Alpha-shifted divergence-form weak solutions

This file proves existence and uniqueness for the scalar-forced weak equation
`(α - div (a grad)) u = f` on the canonical zero-trace value--gradient Hilbert
carrier. It also constructs the canonical bounded linear solution operator and
proves its weak characterization and coercivity norm bound.

The weak predicate depends only on the coefficient field. Ellipticity is used
only in the Lax--Milgram proof.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport
open scoped RealInnerProductSpace

section

variable {d : ℕ} {U : Set (Vec d)}
variable {a : CoeffField d} {lam Lam α : ℝ}

open ZeroTraceSobolev

private theorem memScalarL2_coord_of_memVectorL2
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) (i : Fin d) :
    MemScalarL2 U (fun x => f x i) := by
  let pi : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
  simpa [MemScalarL2, MemVectorL2, volumeMeasureOn] using! pi.comp_memLp' hf

private theorem integrableOn_vecDot
    {f g : Vec d → Vec d} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    MeasureTheory.IntegrableOn (fun x => vecDot (f x) (g x)) U := by
  have hsum :
      MeasureTheory.IntegrableOn (fun x => ∑ i, f x i * g x i) U := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (MeasureTheory.integrable_finsetSum
        (μ := volumeMeasureOn U) Finset.univ
        (fun i _ =>
          (memScalarL2_coord_of_memVectorL2 hf i).integrable_mul
            (memScalarL2_coord_of_memVectorL2 hg i)))
  simpa [vecDot] using hsum

private theorem hilbertVectorL2_eq_ofVecField (F : HilbertVectorL2 U) :
    F = toHilbertVectorL2OfVecField
      (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) F)) := by
  calc
    F = vectorL2ToHilbertVectorL2 (U := U)
        (hilbertVectorL2ToVectorL2 (U := U) F) := by
          symm
          exact vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 (U := U) F
    _ = vectorL2ToHilbertVectorL2 (U := U)
        (toVectorL2 (MeasureTheory.Lp.memLp
          (hilbertVectorL2ToVectorL2 (U := U) F))) := by
          congr 1
          exact (MeasureTheory.Lp.toLp_coeFn
            (hilbertVectorL2ToVectorL2 (U := U) F)
            (MeasureTheory.Lp.memLp
              (hilbertVectorL2ToVectorL2 (U := U) F))).symm
    _ = toHilbertVectorL2OfVecField
        (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) F)) := by
          rfl

private theorem inner_operator_eq_pairing
    (hEll : IsEllipticFieldOn lam Lam U a) (F G : HilbertVectorL2 U) :
    inner ℝ (hilbertCoeffOperator hEll F) G = coefficientPairing a U F G := by
  let f : VectorL2 U := hilbertVectorL2ToVectorL2 (U := U) F
  let g : VectorL2 U := hilbertVectorL2ToVectorL2 (U := U) G
  let hf : MemVectorL2 U (fun x => f x) := MeasureTheory.Lp.memLp f
  let hg : MemVectorL2 U (fun x => g x) := MeasureTheory.Lp.memLp g
  have hF : F = toHilbertVectorL2OfVecField hf := by
    simpa only [f, hf] using hilbertVectorL2_eq_ofVecField (U := U) F
  have hG : G = toHilbertVectorL2OfVecField hg := by
    simpa only [g, hg] using hilbertVectorL2_eq_ofVecField (U := U) G
  calc
    inner ℝ (hilbertCoeffOperator hEll F) G =
        inner ℝ
          (toHilbertVectorL2OfVecField
            (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hf))
          (toHilbertVectorL2OfVecField hg) := by
            rw [hF, hG, hilbertCoeffOperator_toHilbertVectorL2OfVecField hEll hf]
    _ = ∫ x in U, vecDot (matVecMul (a x) (f x)) (g x)
          ∂MeasureTheory.volume :=
      inner_toHilbertVectorL2OfVecField_eq_integral
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hf) hg
    _ = coefficientPairing a U F G := by rfl

private theorem lam_mul_norm_sq_le_pairing
    (hEll : IsEllipticFieldOn lam Lam U a) (F : HilbertVectorL2 U) :
    lam * ‖F‖ ^ 2 ≤ coefficientPairing a U F F := by
  let f : VectorL2 U := hilbertVectorL2ToVectorL2 (U := U) F
  let hf : MemVectorL2 U (fun x => f x) := MeasureTheory.Lp.memLp f
  have hF : F = toHilbertVectorL2OfVecField hf := by
    simpa only [f, hf] using hilbertVectorL2_eq_ofVecField (U := U) F
  have hsqInt : MeasureTheory.IntegrableOn (fun x => vecDot (f x) (f x)) U :=
    integrableOn_vecDot hf hf
  have henergyInt : MeasureTheory.IntegrableOn
      (fun x => vecDot (matVecMul (a x) (f x)) (f x)) U :=
    integrableOn_vecDot
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hf) hf
  have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U :=
    (MeasureTheory.ae_restrict_iff'
      (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun _ hx => hx)
  have hpoint : ∀ᵐ x ∂ volumeMeasureOn U,
      lam * vecDot (f x) (f x) ≤
        vecDot (matVecMul (a x) (f x)) (f x) := by
    filter_upwards [hmem] with x hx
    simpa only [vecNormSq, vecDot_comm] using (hEll.2 x hx).2.2.1 (f x)
  have hnormSq :
      ‖F‖ ^ 2 = ∫ x in U, vecDot (f x) (f x) ∂MeasureTheory.volume := by
    calc
      ‖F‖ ^ 2 = inner ℝ F F := by
        symm
        exact real_inner_self_eq_norm_sq F
      _ = inner ℝ (toHilbertVectorL2OfVecField hf)
          (toHilbertVectorL2OfVecField hf) := by rw [hF]
      _ = ∫ x in U, vecDot (f x) (f x) ∂MeasureTheory.volume :=
        inner_toHilbertVectorL2OfVecField_eq_integral hf hf
  calc
    lam * ‖F‖ ^ 2 =
        ∫ x in U, lam * vecDot (f x) (f x) ∂MeasureTheory.volume := by
          rw [hnormSq, MeasureTheory.integral_const_mul]
    _ ≤ ∫ x in U, vecDot (matVecMul (a x) (f x)) (f x)
          ∂MeasureTheory.volume :=
      MeasureTheory.integral_mono_ae (hsqInt.const_mul lam) henergyInt hpoint
    _ = coefficientPairing a U F F := by rfl

/-- The continuous coefficient-gradient bilinear form on zero-trace Sobolev functions. -/
noncomputable def coefficientBilin
    (hEll : IsEllipticFieldOn lam Lam U a) :
    ZeroTraceSobolev U →L[ℝ] ZeroTraceSobolev U →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    ((hilbertCoeffOperator hEll).comp gradient) gradient

/-- The continuous L² mass bilinear form on zero-trace Sobolev functions. -/
noncomputable def massBilin :
    ZeroTraceSobolev U →L[ℝ] ZeroTraceSobolev U →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap toL2 toL2

/-- The continuous bilinear form for the shifted divergence-form operator. -/
noncomputable def shiftedBilin
    (hEll : IsEllipticFieldOn lam Lam U a) (alpha : ℝ) :
    ZeroTraceSobolev U →L[ℝ] ZeroTraceSobolev U →L[ℝ] ℝ :=
  alpha • massBilin (U := U) + coefficientBilin hEll

private theorem coefficientBilin_apply
    (hEll : IsEllipticFieldOn lam Lam U a) (u v : ZeroTraceSobolev U) :
    coefficientBilin hEll u v =
      inner ℝ (hilbertCoeffOperator hEll (gradient u)) (gradient v) := by
  simp [coefficientBilin, ContinuousLinearMap.bilinearComp_apply]

private theorem massBilin_apply (u v : ZeroTraceSobolev U) :
    massBilin (U := U) u v = inner ℝ (toL2 u) (toL2 v) := by
  simp [massBilin, ContinuousLinearMap.bilinearComp_apply]

/-- Evaluation of the shifted bilinear form in terms of the mass and
coefficient pairings. -/
theorem shiftedBilin_apply
    (hEll : IsEllipticFieldOn lam Lam U a) (alpha : ℝ)
    (u v : ZeroTraceSobolev U) :
    shiftedBilin hEll alpha u v =
      alpha * inner ℝ (toL2 u) (toL2 v) +
        coefficientPairing a U (gradient u) (gradient v) := by
  simp only [shiftedBilin, add_apply,
    smul_apply, smul_eq_mul, massBilin_apply,
    coefficientBilin_apply]
  rw [inner_operator_eq_pairing hEll]

/-- Coercive lower bound for the shifted bilinear form. -/
theorem shiftedBilin_lower_bound
    (hEll : IsEllipticFieldOn lam Lam U a) (u : ZeroTraceSobolev U) :
    min α lam * ‖u‖ * ‖u‖ ≤ shiftedBilin hEll α u u := by
  have hgradient := lam_mul_norm_sq_le_pairing hEll (gradient u)
  calc
    min α lam * ‖u‖ * ‖u‖ = min α lam * ‖u‖ ^ 2 := by ring
    _ = min α lam * (‖toL2 u‖ ^ 2 + ‖gradient u‖ ^ 2) := by
      rw [ZeroTraceSobolev.norm_sq_eq]
    _ = min α lam * ‖toL2 u‖ ^ 2 + min α lam * ‖gradient u‖ ^ 2 := by
      ring
    _ ≤ α * ‖toL2 u‖ ^ 2 + lam * ‖gradient u‖ ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_right (min_le_left α lam) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (min_le_right α lam) (sq_nonneg _))
    _ ≤ α * ‖toL2 u‖ ^ 2 + coefficientPairing a U (gradient u) (gradient u) :=
      add_le_add (le_refl _) hgradient
    _ = shiftedBilin hEll α u u := by
      rw [shiftedBilin_apply, real_inner_self_eq_norm_sq]

/-- The shifted bilinear form is coercive for positive shift and ellipticity
constant. -/
theorem shiftedBilin_coercive
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsCoercive (shiftedBilin hEll α) :=
  ⟨min α lam, lt_min hα hlam, shiftedBilin_lower_bound hEll⟩

/-- The continuous functional induced by an L² forcing term. -/
noncomputable def forcing (f : ScalarL2 U) :
    ZeroTraceSobolev U →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (ScalarL2 U) f).comp toL2

/-- The Riesz representative of the L² forcing functional in zero-trace Sobolev space. -/
noncomputable def forcingRep (f : ScalarL2 U) : ZeroTraceSobolev U :=
  (InnerProductSpace.toDual ℝ (ZeroTraceSobolev U)).symm (forcing f)

private theorem inner_forcingRep (f : ScalarL2 U) (u : ZeroTraceSobolev U) :
    inner ℝ (forcingRep f) u = inner ℝ f (toL2 u) := by
  exact InnerProductSpace.toDual_symm_apply
    (𝕜 := ℝ) (E := ZeroTraceSobolev U) (x := u)
    (y := (forcing f : StrongDual ℝ (ZeroTraceSobolev U)))

/-- The weak equation for `(α - div (a grad)) u = f`. -/
def IsAlphaShiftedWeakSolution (a : CoeffField d) (U : Set (Vec d))
    (α : ℝ) (f : ScalarL2 U) (u : ZeroTraceSobolev U) : Prop :=
  ∀ v : ZeroTraceSobolev U,
    α * inner ℝ (toL2 u) (toL2 v) +
      coefficientPairing a U (gradient u) (gradient v) = inner ℝ f (toL2 v)

/-- Existence and uniqueness for the alpha-shifted divergence-form weak equation. -/
theorem existsUnique_isAlphaShiftedWeakSolution
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U) :
    ∃! u : ZeroTraceSobolev U, IsAlphaShiftedWeakSolution a U α f u := by
  let hB : IsCoercive (shiftedBilin hEll α) := shiftedBilin_coercive hα hlam hEll
  let e : ZeroTraceSobolev U ≃L[ℝ] ZeroTraceSobolev U :=
    hB.continuousLinearEquivOfBilin
  let r : ZeroTraceSobolev U := forcingRep f
  refine ⟨e.symm r, ?_, ?_⟩
  · intro v
    calc
      α * inner ℝ (toL2 (e.symm r)) (toL2 v) +
          coefficientPairing a U (gradient (e.symm r)) (gradient v) =
          shiftedBilin hEll α (e.symm r) v :=
        (shiftedBilin_apply hEll α _ _).symm
      _ = inner ℝ (e (e.symm r)) v := by
        symm
        exact hB.continuousLinearEquivOfBilin_apply (e.symm r) v
      _ = inner ℝ r v := by rw [e.apply_symm_apply]
      _ = inner ℝ f (toL2 v) := inner_forcingRep f v
  · intro u hu
    have huRiesz : r = e u := by
      apply hB.unique_continuousLinearEquivOfBilin
      intro v
      calc
        inner ℝ r v = inner ℝ f (toL2 v) := inner_forcingRep f v
        _ = α * inner ℝ (toL2 u) (toL2 v) +
            coefficientPairing a U (gradient u) (gradient v) := (hu v).symm
        _ = shiftedBilin hEll α u v :=
          (shiftedBilin_apply hEll α _ _).symm
    apply e.injective
    rw [← huRiesz, e.apply_symm_apply]

/-- The canonical bounded linear solution operator for the alpha-shifted weak
equation. -/
noncomputable def alphaShiftedSolution
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    ScalarL2 U →L[ℝ] ZeroTraceSobolev U :=
  let hB : IsCoercive (shiftedBilin hEll α) := shiftedBilin_coercive hα hlam hEll
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.adjoint (ZeroTraceSobolev.toL2 (U := U)))

/-- The canonical operator solves the alpha-shifted weak equation. -/
theorem alphaShiftedSolution_isAlphaShiftedWeakSolution
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U) :
    IsAlphaShiftedWeakSolution a U α f
      (alphaShiftedSolution a hα hlam hEll f) := by
  let hB : IsCoercive (shiftedBilin hEll α) := shiftedBilin_coercive hα hlam hEll
  let e : ZeroTraceSobolev U ≃L[ℝ] ZeroTraceSobolev U :=
    hB.continuousLinearEquivOfBilin
  intro v
  calc
    α * inner ℝ (toL2 (alphaShiftedSolution a hα hlam hEll f)) (toL2 v) +
        coefficientPairing a U
          (gradient (alphaShiftedSolution a hα hlam hEll f)) (gradient v) =
        shiftedBilin hEll α (alphaShiftedSolution a hα hlam hEll f) v :=
      (shiftedBilin_apply hEll α _ _).symm
    _ = inner ℝ (e (alphaShiftedSolution a hα hlam hEll f)) v := by
      symm
      exact hB.continuousLinearEquivOfBilin_apply
        (alphaShiftedSolution a hα hlam hEll f) v
    _ = inner ℝ
        (ContinuousLinearMap.adjoint (ZeroTraceSobolev.toL2 (U := U)) f) v := by
      change inner ℝ
        (e (e.symm
          (ContinuousLinearMap.adjoint (ZeroTraceSobolev.toL2 (U := U)) f))) v = _
      rw [e.apply_symm_apply]
    _ = inner ℝ f (toL2 v) :=
      ContinuousLinearMap.adjoint_inner_left (ZeroTraceSobolev.toL2 (U := U)) v f

/-- A zero-trace Sobolev element solves the weak equation exactly when it is
the value of the canonical solution operator. -/
theorem isAlphaShiftedWeakSolution_iff_eq
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    (u : ZeroTraceSobolev U) :
    IsAlphaShiftedWeakSolution a U α f u ↔
      u = alphaShiftedSolution a hα hlam hEll f := by
  constructor
  · intro hu
    exact (existsUnique_isAlphaShiftedWeakSolution a hα hlam hEll f).unique hu
      (alphaShiftedSolution_isAlphaShiftedWeakSolution a hα hlam hEll f)
  · rintro rfl
    exact alphaShiftedSolution_isAlphaShiftedWeakSolution a hα hlam hEll f

/-- The `L²` resolvent obtained by composing the canonical weak solution with
its value component. -/
noncomputable def alphaShiftedResolvent
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    ScalarL2 U →L[ℝ] ScalarL2 U :=
  ZeroTraceSobolev.toL2.comp (alphaShiftedSolution a hα hlam hEll)

@[simp] theorem alphaShiftedResolvent_apply
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U) :
    alphaShiftedResolvent a hα hlam hEll f =
      ZeroTraceSobolev.toL2 (alphaShiftedSolution a hα hlam hEll f) := by
  rfl

/-- The graph-carrier resolvent identity for two positive shifts. -/
theorem alphaShiftedSolution_resolvent_identity
    (a : CoeffField d) {U : Set (Vec d)} {α β lam Lam : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U) :
    alphaShiftedSolution a hα hlam hEll f -
        alphaShiftedSolution a hβ hlam hEll f =
      (β - α) • alphaShiftedSolution a hα hlam hEll
        (alphaShiftedResolvent a hβ hlam hEll f) := by
  have hαform (v : ZeroTraceSobolev U) :
      shiftedBilin hEll α (alphaShiftedSolution a hα hlam hEll f) v =
        inner ℝ f (toL2 v) := by
    rw [shiftedBilin_apply]
    exact alphaShiftedSolution_isAlphaShiftedWeakSolution
      a hα hlam hEll f v
  have hβweak :=
    alphaShiftedSolution_isAlphaShiftedWeakSolution a hβ hlam hEll f
  have hdiff :
      IsAlphaShiftedWeakSolution a U α
        ((β - α) • alphaShiftedResolvent a hβ hlam hEll f)
        (alphaShiftedSolution a hα hlam hEll f -
          alphaShiftedSolution a hβ hlam hEll f) := by
    intro v
    calc
      α * inner ℝ
            (toL2 (alphaShiftedSolution a hα hlam hEll f -
              alphaShiftedSolution a hβ hlam hEll f)) (toL2 v) +
          coefficientPairing a U
            (gradient (alphaShiftedSolution a hα hlam hEll f -
              alphaShiftedSolution a hβ hlam hEll f)) (gradient v) =
          shiftedBilin hEll α
            (alphaShiftedSolution a hα hlam hEll f -
              alphaShiftedSolution a hβ hlam hEll f) v :=
        (shiftedBilin_apply hEll α _ _).symm
      _ = shiftedBilin hEll α (alphaShiftedSolution a hα hlam hEll f) v -
          shiftedBilin hEll α (alphaShiftedSolution a hβ hlam hEll f) v := by
        rw [map_sub, sub_apply]
      _ = inner ℝ f (toL2 v) -
          (α * inner ℝ
              (toL2 (alphaShiftedSolution a hβ hlam hEll f)) (toL2 v) +
            coefficientPairing a U
              (gradient (alphaShiftedSolution a hβ hlam hEll f))
              (gradient v)) := by
        rw [hαform, shiftedBilin_apply]
      _ = (β - α) *
          inner ℝ (toL2 (alphaShiftedSolution a hβ hlam hEll f))
            (toL2 v) := by
        rw [← hβweak v]
        ring
      _ = inner ℝ ((β - α) • alphaShiftedResolvent a hβ hlam hEll f)
          (toL2 v) := by
        rw [alphaShiftedResolvent_apply, real_inner_smul_left]
  calc
    alphaShiftedSolution a hα hlam hEll f -
        alphaShiftedSolution a hβ hlam hEll f =
      alphaShiftedSolution a hα hlam hEll
        ((β - α) • alphaShiftedResolvent a hβ hlam hEll f) :=
      (isAlphaShiftedWeakSolution_iff_eq a hα hlam hEll _ _).1 hdiff
    _ = (β - α) • alphaShiftedSolution a hα hlam hEll
        (alphaShiftedResolvent a hβ hlam hEll f) := by
      rw [map_smul]

/-- The `L²` operator resolvent identity for two positive shifts. -/
theorem alphaShiftedResolvent_resolvent_identity
    (a : CoeffField d) {U : Set (Vec d)} {α β lam Lam : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    alphaShiftedResolvent a hα hlam hEll -
        alphaShiftedResolvent a hβ hlam hEll =
      (β - α) • ((alphaShiftedResolvent a hα hlam hEll).comp
        (alphaShiftedResolvent a hβ hlam hEll)) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, alphaShiftedResolvent_apply]
  rw [← map_sub,
    alphaShiftedSolution_resolvent_identity a hα hβ hlam hEll f, map_smul]
  rfl

/-- The `L²` resolvent has the sharp pointwise bound supplied by its positive
shift. -/
theorem norm_alphaShiftedResolvent_apply_le
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U) :
    ‖alphaShiftedResolvent a hα hlam hEll f‖ ≤ α⁻¹ * ‖f‖ := by
  let u : ZeroTraceSobolev U := alphaShiftedSolution a hα hlam hEll f
  let r : ScalarL2 U := toL2 u
  change ‖r‖ ≤ α⁻¹ * ‖f‖
  have hpair_nonneg :
      0 ≤ coefficientPairing a U (gradient u) (gradient u) := by
    exact le_trans
      (mul_nonneg (le_of_lt hlam) (sq_nonneg ‖gradient u‖))
      (lam_mul_norm_sq_le_pairing hEll (gradient u))
  have henergy : α * ‖r‖ * ‖r‖ ≤ ‖f‖ * ‖r‖ := by
    calc
      α * ‖r‖ * ‖r‖ = α * ‖r‖ ^ 2 := by ring
      _ ≤ α * ‖r‖ ^ 2 +
          coefficientPairing a U (gradient u) (gradient u) :=
        le_add_of_nonneg_right hpair_nonneg
      _ = inner ℝ f r := by
        change α * ‖toL2 u‖ ^ 2 +
            coefficientPairing a U (gradient u) (gradient u) =
          inner ℝ f (toL2 u)
        rw [← real_inner_self_eq_norm_sq]
        exact alphaShiftedSolution_isAlphaShiftedWeakSolution
          a hα hlam hEll f u
      _ ≤ ‖f‖ * ‖r‖ := real_inner_le_norm f r
  by_cases hr : ‖r‖ = 0
  · rw [hr]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hα)) (norm_nonneg f)
  · have hr_pos : 0 < ‖r‖ :=
      lt_of_le_of_ne (norm_nonneg r) (Ne.symm hr)
    apply (le_inv_mul_iff₀ hα).2
    apply (mul_le_mul_iff_right₀ hr_pos).1
    calc
      ‖r‖ * (α * ‖r‖) = α * ‖r‖ * ‖r‖ := by ac_rfl
      _ ≤ ‖f‖ * ‖r‖ := henergy
      _ = ‖r‖ * ‖f‖ := by ac_rfl

/-- The graph-norm estimate supplied by coercivity of the shifted form. -/
theorem norm_alphaShiftedSolution_apply_le
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U) :
    ‖alphaShiftedSolution a hα hlam hEll f‖ ≤ (min α lam)⁻¹ * ‖f‖ := by
  let u : ZeroTraceSobolev U := alphaShiftedSolution a hα hlam hEll f
  change ‖u‖ ≤ (min α lam)⁻¹ * ‖f‖
  have henergy : min α lam * ‖u‖ * ‖u‖ ≤ ‖f‖ * ‖u‖ := by
    calc
      min α lam * ‖u‖ * ‖u‖ ≤ shiftedBilin hEll α u u :=
        shiftedBilin_lower_bound hEll u
      _ = inner ℝ f (toL2 u) := by
        rw [shiftedBilin_apply]
        exact alphaShiftedSolution_isAlphaShiftedWeakSolution a hα hlam hEll f u
      _ ≤ ‖f‖ * ‖toL2 u‖ := real_inner_le_norm f (toL2 u)
      _ ≤ ‖f‖ * ‖u‖ :=
        mul_le_mul_of_nonneg_left (ZeroTraceSobolev.norm_toL2_le u) (norm_nonneg f)
  by_cases hu : ‖u‖ = 0
  · rw [hu]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt (lt_min hα hlam))) (norm_nonneg f)
  · have hu_pos : 0 < ‖u‖ :=
      lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
    apply (le_inv_mul_iff₀ (lt_min hα hlam)).2
    apply (mul_le_mul_iff_right₀ hu_pos).1
    simpa only [mul_assoc, mul_comm] using henergy

end

end DivergenceFormProcess.Form
