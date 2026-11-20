/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.HorizontalFormOperator

/-!
# The diffusivity-dependent horizontal form family `𝔩_{w,δ}` and `𝔸_{w,δ}(z)`

The proof of `prop:local-seed` in the paper perturbs the velocity *and* the diffusivity on
the fixed form domain `H¹(ℝ²;ℂ²)`:

`𝔩_{h,δ}(b,φ) = 𝔩_{v_h}(b,φ) + (δ-1)(⟨∇_⊥b,∇_⊥φ⟩ + N²⟨b,φ⟩)`

(the paper writes `4π²` for `N²`: its local model uses the axial mode `e^{2πix₃}`, i.e.
`N = 2π`), and writes `𝔸_{h,δ}(z) : V → V*` for the shifted form operator of that form.  The unit
diffusivity form `𝔩_w` and the unit diffusivity pencil `𝔸_w(z) = F_z + K_w` are built in
`Local/HorizontalWeakForm.lean` and `Local/HorizontalFormOperator.lean`; this module adds the
`δ` parameter on top of them.

Because the added term is exactly `(δ-1)` times the diffusion form `horizontalDiffusionForm N`
of `eq:jump-sectorial-form`, the whole `δ`-dependence of the family is an affine one-term
perturbation.  Two consequences are recorded here and consumed by the form-perturbation
estimate `eq:form-small`:

* `horizontalWeakFormDelta_apply` displays the form as `δ·(diffusion) + (velocity terms)`, the
  weak version of the generator `𝓛_δ` of `eq:local-generator`;
* `horizontalPencilFormDelta_sub` splits a difference of two members of the family as
  `(K_w - K_{w'}) + (δ - δ')·(diffusion)`, with **no** `z` left in it: the spectral parameter
  enters both pencils through the same free form `F_z` and cancels.

The associated `L²` operator is obtained from `Operator/AssociatedForm.lean` exactly as at
`δ = 1`; the strong-form counterpart `horizontalLocalOperator N δ w` of
`Operator/WholePlaneLocalC2.lean` is not related to it here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

namespace HorizontalWeakForm

/-! ## The `V → V*` operator norm of a complex form -/

/-- The `V → V*` operator norm of a complex form, i.e. `‖a‖` for `a : V →L[ℂ] V*`.

It is introduced as a definition because instance search does not find
`Norm (ComplexForm V)` at the concrete form domain `H¹(ℝ²;ℂ²)`, the latter being a submodule
of a `PiLp` of `Lp` quotients; stated generically in `V` it elaborates once and instantiates
without search.  This is the norm appearing in `eq:form-small`. -/
noncomputable def complexFormOpNorm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (a : ComplexForm V) : ℝ :=
  ‖a‖

/-- The `V → V*` operator norm of a complex form is nonnegative. -/
theorem complexFormOpNorm_nonneg {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (a : ComplexForm V) :
    0 ≤ complexFormOpNorm a :=
  norm_nonneg a

/-- The `V → V*` operator norm of a complex form is bounded by any uniform bound on its
values.  This is how every instance of `eq:form-small` is discharged. -/
theorem complexFormOpNorm_le_of_apply_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (a : ComplexForm V) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ b phi : V, ‖a b phi‖ ≤ C * ‖b‖ * ‖phi‖) :
    complexFormOpNorm a ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun b => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun phi => ?_
  exact h b phi

/-- The triangle inequality for the `V → V*` operator norm. -/
theorem complexFormOpNorm_add_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (a c : ComplexForm V) :
    complexFormOpNorm (a + c) ≤ complexFormOpNorm a + complexFormOpNorm c :=
  norm_add_le a c

/-- Homogeneity bound for the `V → V*` operator norm under a complex scalar. -/
theorem complexFormOpNorm_smul_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (c : ℂ) (a : ComplexForm V) :
    complexFormOpNorm (c • a) ≤ ‖c‖ * complexFormOpNorm a :=
  ContinuousLinearMap.opNorm_smul_le c a

/-! ## The `δ`-dependent form -/

/-- The diffusivity-`δ` horizontal form
`𝔩_{w,δ}(b,φ) = 𝔩_w(b,φ) + (δ-1)(⟨∇_⊥b,∇_⊥φ⟩ + N²⟨b,φ⟩)`
of the proof of `prop:local-seed`. -/
def horizontalWeakFormDelta (N delta : ℝ) (w : WholePlaneC3LInf) :
    ComplexForm WholePlaneC2H1 :=
  horizontalWeakForm N w + ((delta - 1 : ℝ) : ℂ) • horizontalDiffusionForm N

/-- The diffusivity sits exactly on the diffusion term, as in `eq:local-generator`:
`𝔩_{w,δ}` is `δ(⟨∇_⊥b,∇_⊥φ⟩+N²⟨b,φ⟩)` plus the four
velocity terms. -/
theorem horizontalWeakFormDelta_apply (N delta : ℝ) (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    horizontalWeakFormDelta N delta w b phi =
      (delta : ℂ) * horizontalDiffusionForm N b phi + horizontalTransportForm w b phi +
        horizontalAxialForm N w b phi + horizontalStretchDivergenceForm w b phi +
        horizontalStretchGradientForm w b phi := by
  simp only [horizontalWeakFormDelta, add_apply, smul_apply, smul_eq_mul,
    horizontalWeakForm_apply, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- At unit diffusivity the family is the form `𝔩_w` of `eq:jump-sectorial-form`. -/
@[simp] theorem horizontalWeakFormDelta_one (N : ℝ) (w : WholePlaneC3LInf) :
    horizontalWeakFormDelta N 1 w = horizontalWeakForm N w := by
  ext b phi
  simp only [horizontalWeakFormDelta_apply, horizontalWeakForm_apply, Complex.ofReal_one,
    one_mul]

/-- The `δ`-dependent form splits into `δ` times the diffusion form plus the velocity part
`K_w`. -/
theorem horizontalWeakFormDelta_eq_add_velocityForm (N delta : ℝ) (w : WholePlaneC3LInf) :
    horizontalWeakFormDelta N delta w =
      ((delta : ℝ) : ℂ) • horizontalDiffusionForm N + horizontalVelocityForm N w := by
  ext b phi
  simp only [horizontalWeakFormDelta_apply, horizontalVelocityForm, add_apply, smul_apply,
    smul_eq_mul]
  ring

/-! ## The `δ`-dependent shifted form operator -/

/-- The diffusivity-`δ` shifted form operator `𝔸_{w,δ}(z) : V → V*`
(proof of `prop:local-seed`), namely the pencil `𝔸_w(z) = F_z + K_w` with the
diffusion term multiplied by `δ`. -/
def horizontalPencilFormDelta (N delta : ℝ) (w : WholePlaneC3LInf) (z : ℂ) :
    ComplexForm WholePlaneC2H1 :=
  horizontalPencilForm N w z + ((delta - 1 : ℝ) : ℂ) • horizontalDiffusionForm N

/-- Evaluation of `𝔸_{w,δ}(z)`: the `δ`-form plus the spectral shift `z⟨b,φ⟩`. -/
theorem horizontalPencilFormDelta_apply (N delta : ℝ) (w : WholePlaneC3LInf) (z : ℂ)
    (b phi : WholePlaneC2H1) :
    horizontalPencilFormDelta N delta w z b phi =
      horizontalWeakFormDelta N delta w b phi +
        z * inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneH1Embedding C2 b) := by
  simp only [horizontalPencilFormDelta, horizontalWeakFormDelta, add_apply, smul_apply,
    smul_eq_mul, horizontalPencilForm_apply]
  ring

/-- At unit diffusivity the shifted form operator is the pencil `𝔸_w(z)`. -/
@[simp] theorem horizontalPencilFormDelta_one (N : ℝ) (w : WholePlaneC3LInf) (z : ℂ) :
    horizontalPencilFormDelta N 1 w z = horizontalPencilForm N w z := by
  ext b phi
  simp only [horizontalPencilFormDelta_apply, horizontalPencilForm_apply,
    horizontalWeakFormDelta_one]

/-- The shifted form operator splits as `δ·(diffusion) + K_w + z·(mass)`; the free form `F_z`
of §2.3 of the paper is `1·(diffusion) + z·(mass)`. -/
theorem horizontalPencilFormDelta_eq (N delta : ℝ) (w : WholePlaneC3LInf) (z : ℂ) :
    horizontalPencilFormDelta N delta w z =
      ((delta : ℝ) : ℂ) • horizontalDiffusionForm N + horizontalVelocityForm N w +
        z • horizontalMassForm := by
  ext b phi
  simp only [horizontalPencilFormDelta_apply, horizontalWeakFormDelta_eq_add_velocityForm,
    horizontalMassForm_apply, add_apply, smul_apply, smul_eq_mul]

/-- **The `z`-free splitting of `eq:form-small`.**  The difference of two members of the
family `𝔸_{w,δ}(z)` does not depend on the spectral parameter `z`: it is the velocity-form
difference `K_w - K_{w'}` plus `(δ - δ')` times the diffusion form.  This is what makes the
constant of `eq:form-small` independent of `z`. -/
theorem horizontalPencilFormDelta_sub (N delta delta' : ℝ) (w w' : WholePlaneC3LInf) (z : ℂ) :
    horizontalPencilFormDelta N delta w z - horizontalPencilFormDelta N delta' w' z =
      (horizontalVelocityForm N w - horizontalVelocityForm N w') +
        ((delta - delta' : ℝ) : ℂ) • horizontalDiffusionForm N := by
  ext b phi
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, horizontalPencilFormDelta_eq,
    Complex.ofReal_sub]
  ring

/-! ## The diffusion half of `eq:form-small` -/

/-- Operator-norm bound for the diffusion form: `‖⟨∇_⊥·,∇_⊥·⟩ + N²⟨·,·⟩‖_{V→V*} ≤ 2 + N²`. -/
theorem complexFormOpNorm_horizontalDiffusionForm_le (N : ℝ) :
    complexFormOpNorm (horizontalDiffusionForm N) ≤ 2 + N ^ 2 := by
  refine complexFormOpNorm_le_of_apply_le _ (by positivity) fun b phi => ?_
  refine (norm_horizontalDiffusionForm_apply_le N b phi).trans_eq ?_
  ring

/-- The `|δ - 1|` half of `eq:form-small`: the diffusion difference is bounded directly on
`V × V`, with the explicit constant `2 + N²` (the paper does not name the constant). -/
theorem complexFormOpNorm_smul_horizontalDiffusionForm_le (N delta delta' : ℝ) :
    complexFormOpNorm (((delta - delta' : ℝ) : ℂ) • horizontalDiffusionForm N) ≤
      |delta - delta'| * (2 + N ^ 2) := by
  refine (complexFormOpNorm_smul_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (complexFormOpNorm_horizontalDiffusionForm_le N)
    (abs_nonneg _)

/-! ## The `L²` operator associated with `𝔩_{w,δ}` -/

/-- Maximal graph domain of the negative operator associated with `𝔩_{w,δ}`. -/
abbrev HorizontalFormDeltaDomain (N delta : ℝ) (w : WholePlaneC3LInf) :=
  AssociatedFormProdDomain (wholePlaneH1Embedding C2) (horizontalWeakFormDelta N delta w)

/-- The generator `𝓛_{w,δ}` of `eq:local-generator`, realised as the domain-aware operator
whose negative is associated with `𝔩_{w,δ}`. -/
def horizontalFormDeltaOperator (N delta : ℝ) (w : WholePlaneC3LInf) :
    DomainOperator WholePlaneC2L2 (HorizontalFormDeltaDomain N delta w) :=
  associatedFormProdOperator (wholePlaneH1Embedding C2)
    (wholePlaneC2H1Embedding_injective) denseRange_wholePlaneC2H1Embedding
    (horizontalWeakFormDelta N delta w)

/-- The domain embedding of `𝓛_{w,δ}` is the physical `H¹ → L²` map. -/
@[simp] theorem horizontalFormDeltaOperator_embedding_apply (N delta : ℝ)
    (w : WholePlaneC3LInf) (u : HorizontalFormDeltaDomain N delta w) :
    (horizontalFormDeltaOperator N delta w).embedding u = wholePlaneH1Embedding C2 u.1.1 :=
  rfl

/-- The action of `𝓛_{w,δ}` is the negative of the stored pivot vector. -/
@[simp] theorem horizontalFormDeltaOperator_op_apply (N delta : ℝ) (w : WholePlaneC3LInf)
    (u : HorizontalFormDeltaDomain N delta w) :
    (horizontalFormDeltaOperator N delta w).op u = -u.1.2 :=
  rfl

end HorizontalWeakForm

end

end FastDynamo
