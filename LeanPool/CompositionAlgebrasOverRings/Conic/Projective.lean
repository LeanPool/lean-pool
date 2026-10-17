/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.Basic
public import LeanPool.CompositionAlgebrasOverRings.Module.SelfAnnihilating
public import LeanPool.CompositionAlgebrasOverRings.Module.Unimodular
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.BaseChangeProjective

/-!
# Projective conic algebras: the trace defect vanishes (`GPR 16.7`, `GPR 16.14(b)`)

For an alternative conic algebra whose underlying module is finitely generated projective, the
conjugation **is** an algebra anti-homomorphism. `Conic/Basic.lean` proves this over a field, and
`Conic/TraceDefectCounterexample.lean` shows it is false over an arbitrary base; projectivity is
exactly what separates the two.

## The argument

`ConicAlgebra.traceDefect_smul_eq_smul_one` (alternativity) gives, for every `x`,

  `d(x, y) • x = μ(x, y) • 1`,  where `d` is the trace defect.

Two facts turn this into `d = 0`.

* **`1` is unimodular** (`GPR 16.7`, via `GPR 11.15`). Over a projective module a quadratic form
  is `b(x, x)` for some bilinear `b` (`QuadraticMap.bilinRepr`), and then `λ := b(1, ·)` has
  `λ 1 = n 1 = 1`. Applying `λ` to the displayed identity evaluates `μ(x, y) = d(x, y) λ(x)`, so

    `d(x, y) • (x - λ(x) • 1) = 0`.

  In other words `d(·, y)` **annihilates its own argument** on `N := ker λ`.
* **A self-annihilating functional on a finitely generated projective module vanishes**
  (`LinearMap.eq_zero_of_smul_self_eq_zero`, `Module/SelfAnnihilating.lean`). `N` is a direct
  summand of `A`, hence finitely generated projective, so `d(·, y)` vanishes on `N`; and `A` is
  `k · 1 + N` with `d(1, y) = 0`, so `d` vanishes identically.

This is `GPR 16.14(b)` — flexibility plus projectivity gives norm-associativity — specialized to
what the conjugation needs. Only flexibility is used, which alternativity supplies.

## Main results

* `ConicAlgebra.isUnimodular_one` : **`GPR 16.7`**.
* `ConicAlgebra.norm_eq_of_projective` : uniqueness of a conic norm on a finite projective
  algebra, **`GPR 16.16`**.
* `ConicAlgebra.traceDefect_eq_zero_of_projective` : **`GPR 16.14(b)`** for the trace defect.
* `ConicAlgebra.conj_mul_of_projective` : conjugation is an anti-homomorphism.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.15, 16.7,
  16.14(b), 16.16, 17.6.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] (C : ConicAlgebra k A)

/-! ### The trace defect as a linear form -/

omit [SMulCommClass k A A] [IsScalarTower k A A] in
theorem traceDefect_add_left (x x' y : A) :
    C.traceDefect (x + x') y = C.traceDefect x y + C.traceDefect x' y := by
  simp only [traceDefect, map_add, QuadraticMap.polar_add_left, add_mul]
  ring

variable (y : A) in
omit [SMulCommClass k A A] in
/-- The trace defect as a linear form in its first argument. -/
def traceDefectLeft : A →ₗ[k] k where
  toFun x := C.traceDefect x y
  map_add' x x' := C.traceDefect_add_left x x' y
  map_smul' c x := by simpa using C.traceDefect_smul_left c x y

omit [SMulCommClass k A A] in
@[simp] theorem traceDefectLeft_apply (x y : A) : C.traceDefectLeft y x = C.traceDefect x y := rfl

/-! ### `GPR 16.7`: the unit is unimodular -/

section Projective

variable [Module.Finite k A] [Module.Projective k A]

/-- The linear form `b(1, ·)` for a bilinear form `b` representing the norm. It sends `1` to `1`
(`ConicAlgebra.unitForm_one`), which is what makes the unit unimodular. -/
noncomputable def unitForm : A →ₗ[k] k := QuadraticMap.bilinRepr C.norm 1

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem unitForm_one : C.unitForm (1 : A) = 1 := by
  rw [unitForm, QuadraticMap.bilinRepr_apply_self, C.norm_one]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
include C in
/-- **`GPR 16.7`.** In a conic algebra that is finitely generated projective as a module, the unit
is unimodular. This is `GPR 11.15` for the pointed quadratic module `(A, n, 1)`: over a projective
module the norm is `b(x, x)` for a bilinear `b`, and `b(1, ·)` sends `1` to `n 1 = 1`. -/
theorem isUnimodular_one : Module.IsUnimodular k (1 : A) :=
  Module.isUnimodular_of_apply_eq_one (f := C.unitForm) C.unitForm_one

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **Uniqueness of the conic norm on a finitely generated projective algebra** (`GPR 16.16`).

Multiplicativity and non-degeneracy are not needed: projectivity makes `1` unimodular, which is
the exact module-theoretic input consumed by the proof. -/
theorem norm_eq_of_projective (C D : ConicAlgebra k A) : C.norm = D.norm := by
  let d : A →ₗ[k] k := C.trace - D.trace
  have hd (x : A) : d x • x = (C.norm x - D.norm x) • (1 : A) := by
    change (C.trace x - D.trace x) • x = _
    have hC : C.trace x • x = x * x + C.norm x • (1 : A) := by
      calc
        _ = (C.trace x • x - C.norm x • (1 : A)) + C.norm x • 1 := by module
        _ = _ := by rw [← C.mul_self_eq]
    have hD : D.trace x • x = x * x + D.norm x • (1 : A) := by
      calc
        _ = (D.trace x • x - D.norm x • (1 : A)) + D.norm x • 1 := by module
        _ = _ := by rw [← D.mul_self_eq]
    rw [sub_smul, hC, hD]
    module
  have hdnorm (x : A) : C.norm x - D.norm x = d x * C.unitForm x := by
    have h := congrArg C.unitForm (hd x)
    simp only [map_smul, C.unitForm_one, smul_eq_mul, mul_one] at h
    exact h.symm
  set N : Submodule k A := LinearMap.ker C.unitForm with hN
  set p : A →ₗ[k] N := LinearMap.codRestrict N
    (LinearMap.id - LinearMap.toSpanSingleton k A 1 ∘ₗ C.unitForm) (fun z ↦ by
      simp [hN, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]) with hp
  have hpi : p ∘ₗ N.subtype = LinearMap.id := by
    refine LinearMap.ext fun z ↦ Subtype.ext ?_
    have hz : C.unitForm (z : A) = 0 := z.2
    simp [hp, hz, LinearMap.toSpanSingleton_apply]
  have : Module.Finite k N :=
    Module.Finite.of_surjective p fun z ↦ ⟨(z : A), DFunLike.congr_fun hpi z⟩
  have : Module.Projective k N := Module.Projective.of_split N.subtype p hpi
  have hdN : d.comp N.subtype = 0 := by
    refine LinearMap.eq_zero_of_smul_self_eq_zero _ fun z ↦ ?_
    refine Subtype.ext ?_
    have hz : C.unitForm (z : A) = 0 := z.2
    have h := hd (z : A)
    rw [hdnorm, hz, mul_zero, zero_smul] at h
    simpa using h
  have hd1 : d (1 : A) = 0 := by
    simp [d, ConicAlgebra.trace_one]
  have hd0 : d = 0 := by
    ext x
    have hx : x - C.unitForm x • (1 : A) ∈ N := by
      simp [hN, LinearMap.mem_ker, C.unitForm_one]
    have hker := DFunLike.congr_fun hdN ⟨x - C.unitForm x • (1 : A), hx⟩
    have hsplit : x = (x - C.unitForm x • (1 : A)) + C.unitForm x • (1 : A) := by
      module
    rw [hsplit, map_add, map_smul, hd1, smul_eq_mul, mul_zero, add_zero]
    simpa using hker
  ext x
  have h := hd x
  rw [DFunLike.congr_fun hd0 x] at h
  change (0 : k) • x = _ at h
  rw [zero_smul] at h
  have hform := congrArg C.unitForm h
  have : C.norm x - D.norm x = 0 := by simpa [C.unitForm_one] using hform.symm
  exact sub_eq_zero.mp this

/-! ### `GPR 16.14(b)`: the trace defect vanishes -/

variable [IsAlternative A]

/-- The trace defect annihilates the "traceless part" `x - λ(x) • 1` of its own argument.

Applying `λ = ConicAlgebra.unitForm` to `d(x, y) • x = μ(x, y) • 1`
(`ConicAlgebra.traceDefect_smul_eq_smul_one`) computes the right-hand scalar as
`μ(x, y) = d(x, y) λ(x)`, and the identity becomes this. -/
theorem traceDefect_smul_sub_smul_one (x y : A) :
    C.traceDefect x y • (x - C.unitForm x • (1 : A)) = 0 := by
  have hid := C.traceDefect_smul_eq_smul_one x y
  have hμ := congrArg C.unitForm hid
  rw [map_smul, map_smul, C.unitForm_one, smul_eq_mul, smul_eq_mul, mul_one] at hμ
  rw [smul_sub, hid, ← hμ, smul_smul, sub_self]

/-- **`GPR 16.14(b)`, for the trace defect.** In an alternative conic algebra whose module is
finitely generated projective, the trace defect vanishes: `t(xy) = t(x)t(y) - n(x, y)`.

⚠ Projectivity is essential — see `Conic/TraceDefectCounterexample.lean` for an associative
conic algebra over `ℤ/4`, on a non-projective module, whose trace defect is `2`. -/
theorem traceDefect_eq_zero_of_projective (x y : A) : C.traceDefect x y = 0 := by
  -- the kernel of `λ`, a direct summand of `A` and so finitely generated projective
  set N : Submodule k A := LinearMap.ker C.unitForm with hN
  set p : A →ₗ[k] N := LinearMap.codRestrict N (LinearMap.id - (LinearMap.toSpanSingleton k A 1)
    ∘ₗ C.unitForm) (fun z ↦ by
      simp [hN, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]) with hp
  have hpi : p ∘ₗ N.subtype = LinearMap.id := by
    refine LinearMap.ext fun z ↦ Subtype.ext ?_
    have hz : C.unitForm (z : A) = 0 := z.2
    simp [hp, hz, LinearMap.toSpanSingleton_apply]
  have : Module.Finite k N :=
    Module.Finite.of_surjective p fun z ↦ ⟨(z : A), DFunLike.congr_fun hpi z⟩
  have : Module.Projective k N := Module.Projective.of_split N.subtype p hpi
  -- the trace defect restricted to `N` annihilates its own argument
  have hzero : (C.traceDefectLeft y).comp N.subtype = 0 := by
    refine LinearMap.eq_zero_of_smul_self_eq_zero _ fun z ↦ ?_
    refine Subtype.ext ?_
    have hz : C.unitForm (z : A) = 0 := z.2
    have := C.traceDefect_smul_sub_smul_one (z : A) y
    rw [hz, zero_smul, sub_zero] at this
    simpa using this
  -- and `A = k · 1 + N`
  have hsplit : x - C.unitForm x • (1 : A) ∈ N := by
    simp [hN, LinearMap.mem_ker, C.unitForm_one]
  have hx : C.traceDefect (x - C.unitForm x • (1 : A)) y = 0 := by
    have h := congrArg (fun f ↦ f ⟨x - C.unitForm x • (1 : A), hsplit⟩) hzero
    simpa using h
  have hsum : C.traceDefect x y = C.traceDefect (x - C.unitForm x • (1 : A)) y +
      C.traceDefect (C.unitForm x • (1 : A)) y := by
    rw [← C.traceDefect_add_left]
    congr 1
    abel
  rw [hsum, hx, C.traceDefect_smul_left, C.traceDefect_one_left, mul_zero, add_zero]

/-- The trace is "multiplicative up to the norm": `t(xy) = t(x)t(y) - n(x, y)`. -/
theorem trace_mul_of_projective (x y : A) :
    C.trace (x * y) = C.trace x * C.trace y - QuadraticMap.polar C.norm x y := by
  have h := C.traceDefect_eq_zero_of_projective x y
  rw [traceDefect] at h
  linear_combination -h

/-- **Conjugation is an algebra anti-homomorphism** for an alternative conic algebra that is
finitely generated projective as a module (`GPR 16.14(b)`, `GPR 17.6`). -/
theorem conj_mul_of_projective (x y : A) : C.conj (x * y) = C.conj y * C.conj x :=
  C.conj_mul_of_traceDefect_eq_zero (C.traceDefect_eq_zero_of_projective x y)

/-- The conjugation of an alternative conic algebra on a finitely generated projective module is
an involution (`GPR 16.14(b)`). -/
theorem conjIsInvolution_of_projective : C.ConjIsInvolution := C.conj_mul_of_projective

end Projective

end ConicAlgebra
