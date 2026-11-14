/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.RankDichotomy
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Field.ZMod

/-!
# Anisotropic conic algebras with vanishing polar form (`GPR 19.4`)

In characteristic two a commutative algebra all of whose squares are scalars — a purely
inseparable extension of exponent at most one, in the field case — is a conic algebra whose norm
is the squaring map. Its polar form vanishes **identically**, so it is not a composition algebra as
soon as it has dimension greater than one, even though the norm may well be anisotropic.

This is the example that certifies two design decisions at once.

* **The polar form is never halved.** `ConicAlgebra.trace` is `n(1, x)`, not `n(1, x) / 2`, and the
  degree-two identity is stated with it. A conic definition needing `2 ∈ kˣ` could not even state
  this example, let alone prove it is a conic algebra.
* **Anisotropic is not the same as non-singular.** Over a field of characteristic other than two, a
  form with identically zero polar form is `2 q(x) = q(x, x) = 0`, hence zero, hence isotropic in
  dimension at least one. Only in characteristic two can a form be anisotropic and have vanishing
  polar form at the same time, and that is exactly the configuration here.

## The construction

Let `F` have characteristic two and let `A` be a commutative `F`-algebra carrying a function
`n : A → F` with `x² = n(x) · 1` for every `x`. Then `n` is a quadratic form with zero polar form —
`(x + y)² = x² + y²` because the cross terms are `2xy = 0` — and it is a conic norm: the trace
`n(1, x)` vanishes, so the degree-two identity `x² = t(x) · x − n(x) · 1` reduces to
`x² = −n(x) · 1`, which is the hypothesis since `−1 = 1`.

Nothing here is an existence statement about purely inseparable extensions; `n` is taken as data,
which is what the field case supplies (`n(x) = x²`, landing in `F` because `A² ⊆ F`).

## Why it is not a composition algebra

Not because of the multiplication — `A` is commutative and associative — but because of the norm.
The polar form is zero, so for `A` of dimension at least one the map `A → A*` it induces kills
everything and cannot be injective; the norm is therefore not regular, and `GPR 19.11` allows a
non-regular composition norm only in dimension one.

## The witness

`ConicAlgebra.dualNumberInseparable` exhibits the configuration over `𝔽₂` with the dual numbers
`𝔽₂[ε]`, `ε² = 0`: dimension two, zero polar form, not a composition algebra.

⚠ The dual numbers are **not** anisotropic — `n(ε) = 0` — so they witness the vanishing polar form
and the failure of composition, but not the sharpness claim about anisotropy. An anisotropic
witness must be a genuine purely inseparable field extension, so it needs an imperfect base such as
`𝔽₂(t)` with `A = 𝔽₂(t)(√t)`. That witness is constructed in
`Composition/InseparableAnisotropic.lean` (`ConicAlgebra.anisotropic_insepSqrtConic`,
`ConicAlgebra.not_isComposition_insepSqrtConic`), by applying the general theorems below.

## Main results

* `ConicAlgebra.inseparableNorm`, `ConicAlgebra.inseparable` : the quadratic form and the conic
  structure.
* `ConicAlgebra.polar_inseparableNorm`, `ConicAlgebra.trace_inseparable` : the polar form and the
  trace vanish identically.
* `ConicAlgebra.anisotropic_inseparable_iff` : the norm is anisotropic exactly when `A` has no
  nonzero square-zero element.
* `ConicAlgebra.not_isComposition_inseparable` : **`GPR 19.4`** — not a composition algebra in
  dimension greater than one.
* `ConicAlgebra.dualNumberInseparable`, `ConicAlgebra.not_isComposition_dualNumberInseparable`,
  `ConicAlgebra.not_anisotropic_dualNumberInseparable` : the concrete witness over `𝔽₂` and what
  it does and does not show.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.4, 19.11.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

section Inseparable

variable {F : Type u} {A : Type v} [Field F] [CommRing A] [Nontrivial A] [Algebra F A]
  (hchar : (2 : F) = 0) (n : A → F) (hn : ∀ x : A, x * x = n x • (1 : A))

/-- Scalars are determined by their action on `1`: `c • 1 = algebraMap c`, and a ring
homomorphism out of a field into a nonzero ring is injective. -/
private theorem smul_one_inj {c d : F} (h : c • (1 : A) = d • (1 : A)) : c = d := by
  simp only [Algebra.smul_def, mul_one] at h
  exact (algebraMap F A).injective h

include hn

theorem inseparable_one : n 1 = 1 :=
  smul_one_inj (A := A) (by rw [← hn 1, mul_one, one_smul])

theorem inseparable_smul (a : F) (x : A) : n (a • x) = a * a * n x :=
  smul_one_inj (A := A) (by rw [← hn (a • x), smul_mul_smul_comm, hn x, smul_smul])

include hchar

/-- **Additivity of the squaring map in characteristic two**: the cross terms of `(x + y)²` are
`2xy = 0`. This is what makes the polar form vanish. -/
private theorem inseparable_add (x y : A) : n (x + y) = n x + n y := by
  have hcross : x * y + y * x = 0 := by
    rw [mul_comm y x, ← two_smul F (x * y), hchar, zero_smul]
  refine smul_one_inj (A := A) ?_
  rw [← hn (x + y), add_smul, ← hn x, ← hn y, mul_add, add_mul, add_mul]
  linear_combination (norm := module) hcross

/-- The squaring map as a quadratic form. Its companion bilinear form is **zero**: in
characteristic two the cross terms of `(x + y)²` are `2xy`. -/
def inseparableNorm : QuadraticForm F A where
  toFun := n
  toFun_smul := inseparable_smul n hn
  exists_companion' := ⟨0, fun x y ↦ by simp [inseparable_add hchar n hn x y]⟩

@[simp] theorem inseparableNorm_apply (x : A) : inseparableNorm hchar n hn x = n x := rfl

/-- **The polar form vanishes identically.** This is the whole point of the example. -/
@[simp] theorem polar_inseparableNorm (x y : A) :
    QuadraticMap.polar (inseparableNorm hchar n hn) x y = 0 := by
  rw [QuadraticMap.polar, inseparableNorm_apply, inseparableNorm_apply, inseparableNorm_apply,
    inseparable_add hchar n hn]
  ring

/-- **`GPR 19.4`: the squaring map is a conic norm.** No hypothesis beyond commutativity,
characteristic two, and `x² ∈ F · 1`. -/
def inseparable : ConicAlgebra F A where
  norm := inseparableNorm hchar n hn
  norm_one := inseparable_one n hn
  mul_self x := by
    rw [polar_inseparableNorm, zero_smul, zero_sub, hn x, inseparableNorm_apply, ← neg_smul]
    congr 1
    rw [eq_neg_iff_add_eq_zero, ← two_mul, hchar, zero_mul]

@[simp] theorem inseparable_norm_apply (x : A) : (inseparable hchar n hn).norm x = n x := rfl

/-- The trace of the example vanishes identically, being a value of the polar form. -/
@[simp] theorem trace_inseparable (x : A) : (inseparable hchar n hn).trace x = 0 := by
  rw [trace_apply]
  exact polar_inseparableNorm hchar n hn 1 x

/-- The conjugation is the **identity**, not merely an involution: `conj x = t(x) · 1 − x = −x = x`.
-/
@[simp] theorem conj_inseparable (x : A) : (inseparable hchar n hn).conj x = x := by
  rw [conj_apply, trace_inseparable, zero_smul, zero_sub, neg_eq_iff_add_eq_zero, ← two_smul F x,
    hchar, zero_smul]

/-- **Anisotropy is exactly the absence of square-zero elements.** For `A` a field extension the
right-hand side is automatic, which is the case `GPR 19.4` is about. -/
theorem anisotropic_inseparable_iff :
    (inseparable hchar n hn).norm.Anisotropic ↔ ∀ x : A, x * x = 0 → x = 0 := by
  constructor
  · intro hani x hx
    refine hani x ?_
    rw [inseparable_norm_apply]
    refine smul_one_inj (A := A) ?_
    rw [← hn x, hx, zero_smul]
  · intro h x hx
    refine h x ?_
    rw [hn x, inseparable_norm_apply] at *
    rw [hx, zero_smul]

/-- **`GPR 19.4`.** In dimension greater than one this is a conic algebra that is **not** a
composition algebra: its polar form vanishes, so its norm is not regular, and `GPR 19.11` permits
a non-regular composition norm only in dimension one. -/
theorem not_isComposition_inseparable [Module.Finite F A] [Module.Projective F A]
    (hdim : 1 < Module.finrank F A) : ¬ (inseparable hchar n hn).IsComposition.{u, v, u} := by
  intro h
  have hnotreg : ¬ (inseparable hchar n hn).norm.IsGPRRegular := by
    intro hreg
    have hone : QuadraticMap.polarBilin (inseparable hchar n hn).norm 1 = 0 := by
      ext y
      rw [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply]
      exact polar_inseparableNorm hchar n hn 1 y
    exact one_ne_zero ((injective_iff_map_eq_zero _).mp hreg.1 1 hone)
  rcases h.isGPRRegular_or_finrank_eq_one with hreg | ⟨hd, -⟩
  · exact hnotreg hreg
  · omega

end Inseparable

/-! ### A witness over `𝔽₂`

The dual numbers `𝔽₂[ε]`, `ε² = 0`, satisfy the hypotheses in dimension two: `(a + bε)² = a²`
because the cross term is `2ab = 0`. They show the configuration is not empty.

⚠ They are **not** anisotropic (`ConicAlgebra.not_anisotropic_dualNumberInseparable`), so they
witness the vanishing polar form and the failure of composition but not the sharpness claim about
anisotropy; that needs a genuine purely inseparable field extension, hence an imperfect base, and
is supplied by `Composition/InseparableAnisotropic.lean`. -/

section DualNumber

/-- The dual numbers over `𝔽₂` are nonzero. -/
instance : Nontrivial (DualNumber (ZMod 2)) :=
  ⟨⟨0, 1, fun h ↦ zero_ne_one (congrArg TrivSqZeroExt.fst h)⟩⟩

/-- `𝔽₂[ε] ≃ 𝔽₂ ⊕ 𝔽₂` as a module. This is what computes the dimension. -/
noncomputable def dualNumberProdEquiv :
    DualNumber (ZMod 2) ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) where
  toFun x := (x.fst, x.snd)
  invFun p := TrivSqZeroExt.inl p.1 + TrivSqZeroExt.inr p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by ext <;> simp
  right_inv p := by ext <;> simp

noncomputable instance : Module.Finite (ZMod 2) (DualNumber (ZMod 2)) :=
  Module.Finite.equiv dualNumberProdEquiv.symm

/-- The dual numbers have dimension two. -/
theorem finrank_dualNumber : Module.finrank (ZMod 2) (DualNumber (ZMod 2)) = 2 := by
  rw [dualNumberProdEquiv.finrank_eq, Module.finrank_prod, Module.finrank_self]

/-- **Every square in `𝔽₂[ε]` is a scalar**: `(a + bε)² = a²`, the cross term `2ab` vanishing. -/
theorem sq_dualNumber (x : DualNumber (ZMod 2)) :
    x * x = algebraMap (ZMod 2) (DualNumber (ZMod 2)) (TrivSqZeroExt.fst x ^ 2) := by
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_mul, sq]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]
    ring_nf
    rw [show (2 : ZMod 2) = 0 from rfl, mul_zero]

/-- `𝔽₂` has characteristic two. -/
theorem dualNumber_char : (2 : ZMod 2) = 0 := by decide

/-- `ConicAlgebra.sq_dualNumber` in the `c • 1` form the construction consumes. -/
theorem dualNumber_sq (x : DualNumber (ZMod 2)) :
    x * x = (TrivSqZeroExt.fst x ^ 2) • (1 : DualNumber (ZMod 2)) := by
  rw [sq_dualNumber x, Algebra.algebraMap_eq_smul_one]

/-- **The witness for `GPR 19.4`**: the dual numbers over `𝔽₂`, a two-dimensional conic algebra
whose norm is the squaring map `a + bε ↦ a²` and whose polar form vanishes identically. -/
noncomputable def dualNumberInseparable : ConicAlgebra (ZMod 2) (DualNumber (ZMod 2)) :=
  inseparable dualNumber_char (fun x : DualNumber (ZMod 2) ↦ TrivSqZeroExt.fst x ^ 2)
    dualNumber_sq

/-- The polar form of the witness vanishes identically — the configuration `GPR 19.4` is about,
in a concrete two-dimensional case. -/
theorem polar_dualNumberInseparable (x y : DualNumber (ZMod 2)) :
    QuadraticMap.polar dualNumberInseparable.norm x y = 0 :=
  polar_inseparableNorm dualNumber_char _ dualNumber_sq x y

/-- **`GPR 19.4` in the concrete case.** The dual numbers over `𝔽₂` are a conic algebra that is
not a composition algebra. -/
theorem not_isComposition_dualNumberInseparable :
    ¬ dualNumberInseparable.IsComposition.{0, 0, 0} :=
  not_isComposition_inseparable dualNumber_char _ dualNumber_sq
    (by rw [finrank_dualNumber]; norm_num)

/-- ⚠ The witness is **not** anisotropic: `ε² = 0` with `ε ≠ 0`. Anisotropy in the presence of a
vanishing polar form — the sharp form of `GPR 19.4` — needs a purely inseparable field extension,
which requires an imperfect base field. That witness is `𝔽₂(t)(√t)`, in
`Composition/InseparableAnisotropic.lean` (`ConicAlgebra.anisotropic_insepSqrtConic`). -/
theorem not_anisotropic_dualNumberInseparable :
    ¬ dualNumberInseparable.norm.Anisotropic := by
  intro hani
  have h := (anisotropic_inseparable_iff dualNumber_char _ dualNumber_sq).mp hani
  have hzero : (TrivSqZeroExt.inr 1 : DualNumber (ZMod 2)) *
      (TrivSqZeroExt.inr 1 : DualNumber (ZMod 2)) = 0 := by
    ext <;> simp
  have := h _ hzero
  exact one_ne_zero (congrArg TrivSqZeroExt.snd this)

end DualNumber

end ConicAlgebra
