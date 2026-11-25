/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

-- Modifications: adapted documentation and wrapped declarations in the SGPT.Foundations.Analysis
-- namespace.
-- Source: https://github.com/zblore/csd-lean4/blob/c63273eceeb1c36c937eccfdf24795043666204f/CsdLean4/Mathlib/Analysis/InnerProductSpace/KahlerForm.lean

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Complex.Basic

/-!
# The flat Hermitian fundamental form

On a complex inner-product space, this file defines `J u = i • u`,
`g u v = re ⟪u,v⟫`, and `ω u v = im ⟪u,v⟫`. It proves real bilinearity,
alternation, compatibility with `J`, positivity, and invariance under complex
linear isometries. The inner product is conjugate-linear in its first slot.

These are statements about a vector space. No projective manifold, global
Kähler metric, Fubini–Study identification, or volume comparison is constructed.
The upstream declaration names are retained for traceability.
-/

@[expose] public section

namespace SGPT.Foundations.Analysis

namespace Kahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The complex structure `J`**: multiplication by `i`. Squares to `-1`
(`complexStructure_involutive`). -/
def complexStructure (u : E) : E := Complex.I • u

/-- **The Riemannian metric `g`**: the real part of the Hermitian inner product,
    `g u v = re ⟪u, v⟫`.
Symmetric (`metric_comm`) and positive-definite (`metric_self`, `= ‖u‖²`). -/
def metric (u v : E) : ℝ := (inner ℂ u v).re

/-- **The fundamental 2-form `ω`**: the imaginary part of the Hermitian inner product,
`ω u v = im ⟪u, v⟫`. Alternating `ℝ`-bilinear (the pointwise Kähler form). -/
def fundamentalForm (u v : E) : ℝ := (inner ℂ u v).im

@[simp] theorem complexStructure_apply (u : E) : complexStructure u = Complex.I • u := rfl

/-- **`J² = -1`**: the fundamental relation of a complex structure. `J (J u) = i • (i • u) = -u`.
-/
theorem complexStructure_involutive (u : E) :
    complexStructure (complexStructure u) = -u := by
  simp only [complexStructure, smul_smul, Complex.I_mul_I, neg_smul, one_smul]

/-! ### `ω` is an alternating `ℝ`-bilinear form -/

/-- `ω u u = 0`: the fundamental form is alternating (`⟪u,u⟫` is real). -/
@[simp] theorem fundamentalForm_self (u : E) : fundamentalForm u u = 0 := by
  simp only [fundamentalForm, ← RCLike.im_to_complex, inner_self_im]

/-- `ω u v = -ω v u`: antisymmetry, from `⟪v,u⟫ = conj ⟪u,v⟫`. -/
theorem fundamentalForm_antisymm (u v : E) :
    fundamentalForm u v = - fundamentalForm v u := by
  simp only [fundamentalForm, ← RCLike.im_to_complex]
  exact inner_im_symm u v

/-- `ω` is additive in the left argument. -/
theorem fundamentalForm_add_left (u u' v : E) :
    fundamentalForm (u + u') v = fundamentalForm u v + fundamentalForm u' v := by
  simp only [fundamentalForm, inner_add_left, Complex.add_im]

/-- `ω` is `ℝ`-homogeneous in the left argument (`r : ℝ` acting through `ℂ`). With additivity and
antisymmetry this makes `ω` an alternating `ℝ`-bilinear form. -/
theorem fundamentalForm_real_smul_left (r : ℝ) (u v : E) :
    fundamentalForm ((r : ℂ) • u) v = r * fundamentalForm u v := by
  simp only [fundamentalForm, inner_smul_left, Complex.conj_ofReal, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-! ### The Kähler triple: `g`, `ω`, `J` compatibility -/

/-- **J-compatibility `ω u v = g (J u) v`.** The fundamental form is the metric precomposed with
    the
complex structure: `im ⟪u, v⟫ = re ⟪i • u, v⟫`. This is the defining relation tying `ω`, `g`,
    `J`. -/
theorem fundamentalForm_eq_metric_complexStructure (u v : E) :
    fundamentalForm u v = metric (complexStructure u) v := by
  simp only [fundamentalForm, metric, complexStructure, inner_smul_left, Complex.conj_I,
    neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg]

/-- **The metric is recovered from `ω` and `J`: `g u v = ω u (J v)`.** `re ⟪u, v⟫ = im ⟪u, i • v⟫`.
The dual Kähler-triple relation. -/
theorem metric_eq_fundamentalForm_complexStructure (u v : E) :
    metric u v = fundamentalForm u (complexStructure v) := by
  simp only [metric, fundamentalForm, complexStructure, inner_smul_right, Complex.I_mul_im]

/-! ### `J` is an isometry — `ω` is a `(1,1)`-form -/

/-- `J` preserves the Hermitian inner product: `⟪J u, J v⟫ = ⟪u, v⟫` (since `conj i · i = 1`). -/
theorem inner_complexStructure (u v : E) :
    inner ℂ (complexStructure u) (complexStructure v) = inner ℂ u v := by
  change inner ℂ (Complex.I • u) (Complex.I • v) = inner ℂ u v
  rw [inner_smul_left, inner_smul_right, Complex.conj_I, ← mul_assoc, neg_mul,
    Complex.I_mul_I, neg_neg, one_mul]

/-- `J` is a `g`-isometry: `g (J u) (J v) = g u v`. -/
theorem metric_complexStructure (u v : E) :
    metric (complexStructure u) (complexStructure v) = metric u v := by
  simp only [metric, inner_complexStructure]

/-- `ω` is `J`-invariant: `ω (J u) (J v) = ω u v`, i.e. `ω` is a `(1,1)`-form. -/
theorem fundamentalForm_complexStructure (u v : E) :
    fundamentalForm (complexStructure u) (complexStructure v) = fundamentalForm u v := by
  simp only [fundamentalForm, inner_complexStructure]

/-! ### Positivity / taming, and the metric's positive-definiteness -/

/-- `g u u = ‖u‖²`: the metric is positive-definite. -/
@[simp] theorem metric_self (u : E) : metric u u = ‖u‖ ^ 2 := by
  simp only [metric, ← RCLike.re_to_complex]
  exact inner_self_eq_norm_sq u

/-- `g` is symmetric. -/
theorem metric_comm (u v : E) : metric u v = metric v u := by
  simp only [metric, ← RCLike.re_to_complex]
  exact inner_re_symm u v

/-- **Positivity / taming `ω u (J u) = ‖u‖²`.** The fundamental form paired with the complex
    structure
recovers the squared norm — so `(u, v) ↦ ω u (J v) = g u v` is positive-definite,
    the taming condition
that makes `ω` a *positive* `(1,1)`-form (the compatible almost-Kähler structure). -/
theorem fundamentalForm_complexStructure_self (u : E) :
    fundamentalForm u (complexStructure u) = ‖u‖ ^ 2 := by
  simp only [fundamentalForm, complexStructure, inner_smul_right, Complex.I_mul_im,
    ← RCLike.re_to_complex]
  exact inner_self_eq_norm_sq u

/-- `ω u (J u) > 0` for `u ≠ 0`: strict positivity of the taming form. -/
theorem fundamentalForm_complexStructure_self_pos {u : E} (hu : u ≠ 0) :
    0 < fundamentalForm u (complexStructure u) := by
  rw [fundamentalForm_complexStructure_self]
  exact pow_pos (norm_pos_iff.mpr hu) 2

/-! ### The capstone -/

/-- The flat Hermitian triple satisfies the complex-structure, compatibility,
invariance, and squared-norm identities. No projective identification is asserted. -/
theorem fubiniStudy_pointwise_kahler_compatibility (u v : E) :
    complexStructure (complexStructure u) = -u
    ∧ fundamentalForm u v = metric (complexStructure u) v
    ∧ metric u v = fundamentalForm u (complexStructure v)
    ∧ fundamentalForm (complexStructure u) (complexStructure v) = fundamentalForm u v
    ∧ fundamentalForm u (complexStructure u) = ‖u‖ ^ 2 :=
  ⟨complexStructure_involutive u, fundamentalForm_eq_metric_complexStructure u v,
    metric_eq_fundamentalForm_complexStructure u v,
    fundamentalForm_complexStructure u v, fundamentalForm_complexStructure_self u⟩

/-! ### Orthogonal complements are invariant under the complex structure -/

/-- Multiplication by `i` preserves the orthogonal complement of a complex span. -/
theorem complexStructure_mem_orthogonal {ψ v : E}
    (hv : v ∈ (Submodule.span ℂ {ψ})ᗮ) :
    complexStructure v ∈ (Submodule.span ℂ {ψ})ᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  simp only [complexStructure, inner_smul_right, hv u hu, mul_zero]

/-- The orthogonal complement of a complex span is `J`-invariant. -/
theorem tangent_complexStructure_invariant (ψ : E) :
    ∀ v ∈ (Submodule.span ℂ {ψ})ᗮ, complexStructure v ∈ (Submodule.span ℂ {ψ})ᗮ :=
  fun _ hv => complexStructure_mem_orthogonal hv

/-! ### Invariance under complex linear isometries -/

/-- A `ℂ`-linear isometry preserves the metric `g`. -/
theorem metric_linearIsometryEquiv (f : E ≃ₗᵢ[ℂ] E) (u v : E) :
    metric (f u) (f v) = metric u v := by
  simp only [metric, f.inner_map_map]

/-- A `ℂ`-linear isometry preserves the fundamental form `ω`. -/
theorem fundamentalForm_linearIsometryEquiv (f : E ≃ₗᵢ[ℂ] E) (u v : E) :
    fundamentalForm (f u) (f v) = fundamentalForm u v := by
  simp only [fundamentalForm, f.inner_map_map]

/-- A complex linear isometry preserves the real metric and fundamental form. -/
theorem kahler_structure_isometry_invariant (f : E ≃ₗᵢ[ℂ] E) (u v : E) :
    metric (f u) (f v) = metric u v ∧ fundamentalForm (f u) (f v) = fundamentalForm u v :=
  ⟨metric_linearIsometryEquiv f u v, fundamentalForm_linearIsometryEquiv f u v⟩

end Kahler

end SGPT.Foundations.Analysis
