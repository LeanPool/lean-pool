/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.AssociatedForm
public import LeanPool.FastDynamo.Analysis.Holder

/-!
# Moving a bounded scalar coefficient across an `L²` pivot

Every weak formulation in this development pairs a vector field against a test function through
the anti-dual pivot `associatedFormPivot j` of `Operator/AssociatedForm.lean`.  The move the
paper's compactness argument for `K_w` in §2.3 makes when it splits the velocity terms by
whether the derivative falls on the input or on the test function — putting a bounded
coefficient on the other side of the pairing — is the statement that multiplication by a
bounded scalar `L∞` coefficient is adjoint to multiplication by its conjugate.

The three lemmas below are that statement, its `L∞`-support companion, and its operator form.
They are generic in the measure space, in the fibre and in the pivot; the seed's weak form is
their consumer, but nothing here is specific to it.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {Y E : Type*} [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Multiplication by a bounded scalar coefficient crosses the `L²` inner product as
multiplication by the conjugate coefficient: the adjoint of `a ·` is `star a ·`. -/
theorem inner_scalarVectorMulL2_right (mu : Measure Y) (a : Lp ℂ ∞ mu)
    (x y : Lp E 2 mu) :
    inner ℂ x (scalarVectorMulL2 mu a y) =
      inner ℂ (scalarVectorMulL2 mu (star a) x) y := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [scalarVectorMulL2_coe_ae mu a y,
    scalarVectorMulL2_coe_ae mu (star a) x, Lp.coeFn_star a] with t hay hax hstar
  rw [hay, hax, hstar, Pi.star_apply, inner_smul_right, inner_smul_left]
  simp

/-- Conjugation preserves almost-everywhere vanishing outside a set, so a local Rellich
hypothesis transfers from a coefficient to its conjugate. -/
theorem ae_zero_off_star {mu : Measure Y} {s : Set Y} {a : Lp ℂ ∞ mu}
    (ha : ∀ᵐ t ∂mu, t ∉ s → a t = 0) :
    ∀ᵐ t ∂mu, t ∉ s → (star a : Lp ℂ ∞ mu) t = 0 := by
  filter_upwards [ha, Lp.coeFn_star a] with t hat hstar ht
  rw [hstar, Pi.star_apply, hat ht, star_zero]

/-- Moving a bounded scalar coefficient from the pivot vector onto the test slot.  This is the
form in which the compactness argument for `K_w` in §2.3 of the paper moves a coefficient
across the pairing. -/
theorem associatedFormPivot_comp_scalarVectorMulL2 {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (mu : Measure Y) (j : V →L[ℂ] Lp E 2 mu) (a : Lp ℂ ∞ mu) :
    (associatedFormPivot j).comp (scalarVectorMulL2 mu a) =
      associatedFormPivot ((scalarVectorMulL2 mu (star a)).comp j) := by
  refine ContinuousLinearMap.ext fun f => ContinuousLinearMap.ext fun phi => ?_
  change inner ℂ (j phi) (scalarVectorMulL2 mu a f) =
    inner ℂ (scalarVectorMulL2 mu (star a) (j phi)) f
  exact inner_scalarVectorMulL2_right mu a (j phi) f

end

end FastDynamo
