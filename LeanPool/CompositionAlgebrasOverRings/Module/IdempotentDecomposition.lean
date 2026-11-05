/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Decomposing a module along a complete orthogonal system of idempotents

A complete orthogonal system of idempotents `(eᵢ)` in a commutative ring `R` decomposes `R` as a
finite product of rings `R ⧸ (1 - eᵢ)` — that is mathlib's
`CompleteOrthogonalIdempotents.bijective_pi`. This file supplies the **module** analogue: the same
system decomposes every `R`-module `M` as `∏ᵢ M ⧸ (1 - eᵢ)M`, compatibly with the ring
decomposition.

Applying this with mathlib's `QuotSMulTop.equivQuotTensor` rewrites the factors as
`(R ⧸ (1 - eᵢ)) ⊗[R] M`, which is the form in which the pieces are modules over the factor rings.

## Main results

* `CompleteOrthogonalIdempotents.bijective_piQuotSMulTop` : the comparison map
  `M → ∏ᵢ M ⧸ (1 - eᵢ)M` is bijective.
* `CompleteOrthogonalIdempotents.linearEquivPiQuotSMulTop` : that map packaged as a linear
  equivalence.
* `CompleteOrthogonalIdempotents.linearEquivPiQuotientTensor` : the same, with the factors
  written as `(R ⧸ (1 - eᵢ)) ⊗[R] M`.

## Implementation notes

This is a statement mathlib is missing, not a competing formulation of one it has: mathlib's
`CompleteOrthogonalIdempotents.bijective_pi` is exactly the case `M = R`, and the proof here is
the same two-line computation carried out with scalars acting on `M`. Both directions are
elementary — injectivity because `x = (∑ᵢ eᵢ) • x` and each `eᵢ • x` vanishes, surjectivity by
assembling `∑ᵢ eᵢ • xᵢ` from lifts of the components.

The factors are `QuotSMulTop (1 - eᵢ) M`, mathlib's abbreviation for `M ⧸ (1 - eᵢ) • ⊤`, rather
than the tensor products `(R ⧸ (1 - eᵢ)) ⊗[R] M`, because the quotient form is what the proof
manipulates. `linearEquivPiQuotientTensor` converts.
-/

@[expose] public section

universe u v w

open scoped Pointwise TensorProduct

variable {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {I : Type w} [Fintype I] {e : I → R}

/-- Membership in `r • ⊤` is just divisibility by `r` in `M`. -/
private theorem mem_smul_top_iff (r : R) (x : M) :
    x ∈ r • (⊤ : Submodule R M) ↔ ∃ y : M, r • y = x := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨y, _, hy⟩ ↦ ⟨y, hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, Submodule.mem_top, hy⟩⟩

variable (e) in
/-- The comparison map `M → ∏ᵢ M ⧸ (1 - eᵢ)M` attached to a family of elements of `R`. -/
def piQuotSMulTop : M →ₗ[R] ∀ i, QuotSMulTop (1 - e i) M :=
  LinearMap.pi fun i ↦ Submodule.mkQ ((1 - e i) • (⊤ : Submodule R M))

omit [Fintype I] in
@[simp]
theorem piQuotSMulTop_apply (x : M) (i : I) :
    piQuotSMulTop M e x i = Submodule.Quotient.mk x :=
  rfl

/-- **A complete orthogonal system of idempotents decomposes every module.** The module analogue
of `CompleteOrthogonalIdempotents.bijective_pi`, which is the case `M = R`. -/
theorem CompleteOrthogonalIdempotents.bijective_piQuotSMulTop
    (he : CompleteOrthogonalIdempotents e) : Function.Bijective (piQuotSMulTop M e) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    -- Each `eᵢ • x` vanishes, and the `eᵢ` sum to `1`.
    have hcomp : ∀ i, e i • x = 0 := by
      intro i
      obtain ⟨y, hy⟩ := (mem_smul_top_iff M _ x).mp
        ((Submodule.Quotient.mk_eq_zero _).mp (congrFun hx i))
      rw [← hy, smul_smul, mul_sub, mul_one, (he.idem i).eq, sub_self, zero_smul]
    calc x = (∑ i, e i) • x := by rw [he.complete, one_smul]
      _ = ∑ i, e i • x := Finset.sum_smul
      _ = 0 := by simp [hcomp]
  · intro m
    choose x hx using fun i ↦ Submodule.Quotient.mk_surjective _ (m i)
    refine ⟨∑ i, e i • x i, funext fun j ↦ ?_⟩
    rw [piQuotSMulTop_apply, ← hx j, Submodule.Quotient.eq]
    -- `∑ᵢ eᵢ • xᵢ - xⱼ` is divisible by `1 - eⱼ`: the `i ≠ j` terms because
    -- `eⱼ eᵢ = 0`, and the
    -- `j`th because `eⱼ - 1 = -(1 - eⱼ)`.
    have hsplit : ∑ i, e i • x i - x j =
        ∑ i ∈ Finset.univ.erase j, e i • x i + (1 - e j) • (-x j) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      module
    rw [hsplit]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i hi ↦ ?_)
      (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
    refine (mem_smul_top_iff M _ _).mpr ⟨e i • x i, ?_⟩
    rw [smul_smul, sub_mul, one_mul, he.ortho (Finset.ne_of_mem_erase hi).symm, sub_zero]

variable (e) in
/-- The decomposition of `M` along a complete orthogonal system of idempotents,
`M ≃ ∏ᵢ M ⧸ (1 - eᵢ)M`. -/
noncomputable def CompleteOrthogonalIdempotents.linearEquivPiQuotSMulTop
    (he : CompleteOrthogonalIdempotents e) : M ≃ₗ[R] ∀ i, QuotSMulTop (1 - e i) M :=
  LinearEquiv.ofBijective _ (he.bijective_piQuotSMulTop M)

@[simp]
theorem CompleteOrthogonalIdempotents.linearEquivPiQuotSMulTop_apply
    (he : CompleteOrthogonalIdempotents e) (x : M) (i : I) :
    he.linearEquivPiQuotSMulTop M e x i = Submodule.Quotient.mk x :=
  rfl

variable (e) in
/-- The decomposition of `M` with the factors written as base changes,
`M ≃ ∏ᵢ (R ⧸ (1 - eᵢ)) ⊗[R] M`. This is the form in which each factor is a module over the
corresponding factor ring of `R`. -/
noncomputable def CompleteOrthogonalIdempotents.linearEquivPiQuotientTensor
    (he : CompleteOrthogonalIdempotents e) :
    M ≃ₗ[R] ∀ i, (R ⧸ Ideal.span {1 - e i}) ⊗[R] M :=
  (he.linearEquivPiQuotSMulTop M e).trans
    (LinearEquiv.piCongrRight fun i ↦ QuotSMulTop.equivQuotTensor (1 - e i) M)

/-- The tensor-product module decomposition sends an element to its pure-tensor image in each
idempotent factor. -/
@[simp]
theorem CompleteOrthogonalIdempotents.linearEquivPiQuotientTensor_apply
    (he : CompleteOrthogonalIdempotents e) (x : M) (i : I) :
    he.linearEquivPiQuotientTensor M e x i = 1 ⊗ₜ[R] x := by
  simp [CompleteOrthogonalIdempotents.linearEquivPiQuotientTensor,
    QuotSMulTop.equivQuotTensor]
