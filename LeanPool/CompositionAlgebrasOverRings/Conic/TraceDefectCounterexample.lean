/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.Basic

/-!
# An associative conic algebra whose conjugation is not an anti-homomorphism

Over a **field**, the conjugation of an alternative conic algebra is an algebra anti-homomorphism
(`ConicAlgebra.conj_mul`). This file shows that over a general commutative ring it is not — not
even for an **associative** conic algebra — so that the hypotheses of `ConicAlgebra.conj_mul` are
not decoration and cannot be dropped in the ring-theoretic layers.

## The example

Let `k = ℤ/4`, let `M = (ℤ/2)²` regarded as a `k`-module, and let `β : M × M → k` be the
`k`-bilinear form `β(m, p) = 2 m₁ p₂` (this is well defined because `2 · x` in `ℤ/4` depends only
on `x` mod `2`). On `A = k × M` put

  `(a, m) * (b, p) = (ab + β(m, p), a • p + b • m)`,  `1 = (1, 0)`,
  `n (a, m) = a² - β(m, m)`.

Then:

* `A` is an associative unital `k`-algebra (`TraceDefectCounterexample.Carrier.mul_assoc`) —
  associativity
  of the `M`-component asks `β(m, p) • q = β(p, q) • m`, and both sides lie in `2 · M = 0`;
* `(A, n)` is a conic algebra (`TraceDefectCounterexample.conic`), with trace `t (a, m) = 2a`;
* but `t(xy) ≠ t(x)t(y) - n(x, y)` for `x = m₁`, `y = m₂`
  (`TraceDefectCounterexample.traceDefect_ne_zero`), and therefore
  `conj (xy) ≠ conj y * conj x` (`TraceDefectCounterexample.conj_mul_ne`).

Concretely `m₁ m₂ = 2 · 1` while `m₂ m₁ = 0`, and `conj (m₁ m₂) = 2 · 1` while
`conj m₂ * conj m₁ = m₂ m₁ = 0`.

`A` is finitely generated but **not projective** over `k`, and that is exactly what fails: the
proof of `ConicAlgebra.traceDefect_eq_zero` over a field uses that a vector outside `k · 1`
generates a free direct summand, and `ConicAlgebra.traceDefect_smul_eq_smul_one` — which does hold
here, alternativity being all it needs — is powerless when `traceDefect x y • x` can vanish for a
nonzero scalar. Here `traceDefect m₁ m₂ = -2 = 2` and `2 • m₁ = 0`.

## Relation to the literature

None of this contradicts `GPR`, which is careful about it throughout: `GPR 16.10(a)` states that
the conjugation of a conic algebra is an involution **iff** `t(x, y) - n(x, conj y) ∈ Ann(C)` — the
trace defect up to sign, and `Ann(A) = 0` here — while the theorems that do give an involution,
`GPR 16.14(b)` and `GPR 17.6`, carry a projectivity hypothesis on the module. `GPR 17.4` flags the
tempting false claim in as many words and points at `GPR Exc. 17.8` (due to McCrimmon) for a
counterexample.

That exercise is essentially this example, and this file is a smaller variant of it. There `k` is
the dual numbers `k₀[ε]`, `ε² = 0`, and `C = k ⊕ k₀³` with `(a, u)(b, v) = (ab, a·v + b·u + [u, v])`
and `n_z(a, u) = a² + (a zᵀu)ε`; conditions (i)–(iv) of the exercise say that the conjugation is an
involution iff `zᵀ[u, v] = 0`. Here `ℤ/4` plays the part of `k₀[ε]` with `2` as `ε` and `ℤ/2` that
of `k₀`; rank `2` suffices instead of `3` because the non-symmetric `β` is imposed directly rather
than obtained as a commutator.

## Implementation notes

The axioms are checked in coordinates. The only finite checks about the structure itself concern
`β` on the four-element module `M`: it is additive and `ℤ/4`-linear in each slot, and its values
annihilate `M` (`Carrier.beta_add_left`, …, `Carrier.beta_smul`), each closed by `decide` over at
most `64` cases. Distributivity, associativity, the scalar laws, bilinearity of the companion form
and the quadratic-form axioms then follow by `ring` and `module` on the coordinates, and
alternativity follows from associativity. The degree-two identity and the statements about `m₁`
and `m₂` are closed by `decide`. No `native_decide` (overview §5).

Closing every axiom by `decide` over all `16³` triples of `A` also works, but takes about ten
times as long to elaborate.

The instance `Module (ℤ/4) (ℤ/2)` is `local`: it is needed to build the example and must not
escape into the rest of the development.

## References

* The ⚠ paragraph in `CompositionAlgebras/Conic/Basic.lean`, which this file substantiates.
* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 16.10, 16.14, 17.4,
  17.6, and Exc. 17.8.
* K. McCrimmon, the source of `GPR Exc. 17.8` (`GPR`'s reference [189]).
-/

@[expose] public section

namespace ConicAlgebra

namespace TraceDefectCounterexample

open scoped ZMod

/-- The `ZMod 4`-module structure on `ZMod 2` induced by reduction modulo `2`. -/
local instance : Module (ZMod 4) (ZMod 2) :=
  Module.compHom (ZMod 2) (ZMod.castHom (by norm_num) (ZMod 2))

/-- The carrier `k · 1 ⊕ M` of the counterexample, with `k = ℤ/4` and `M = (ℤ/2)²`. -/
def Carrier := ZMod 4 × ZMod 2 × ZMod 2

namespace Carrier

instance : AddCommGroup Carrier := inferInstanceAs (AddCommGroup (ZMod 4 × ZMod 2 × ZMod 2))
instance : DecidableEq Carrier := inferInstanceAs (DecidableEq (ZMod 4 × ZMod 2 × ZMod 2))
instance : Fintype Carrier := inferInstanceAs (Fintype (ZMod 4 × ZMod 2 × ZMod 2))
instance : Module (ZMod 4) Carrier :=
  inferInstanceAs (Module (ZMod 4) (ZMod 4 × ZMod 2 × ZMod 2))

/-- The `ℤ/4`-bilinear form `β(m, p) = 2 m₁ p₂` on `(ℤ/2)²`. It is *not* symmetric, which is the
whole point: the trace defect of the resulting conic algebra is `β(p, m) - β(m, p)`. -/
def beta (m p : ZMod 2 × ZMod 2) : ZMod 4 := ((2 * m.1.val * p.2.val : ℕ) : ZMod 4)

/-! ### `β` is bilinear, and its values annihilate `M`

These are the only finite checks about the structure; each runs over at most `64` cases. -/

theorem beta_add_left (m m' p : ZMod 2 × ZMod 2) : beta (m + m') p = beta m p + beta m' p := by
  revert m m' p; decide

theorem beta_add_right (m p p' : ZMod 2 × ZMod 2) : beta m (p + p') = beta m p + beta m p' := by
  revert m p p'; decide

theorem beta_smul_left (a : ZMod 4) (m p : ZMod 2 × ZMod 2) : beta (a • m) p = a * beta m p := by
  revert a m p; decide

theorem beta_smul_right (a : ZMod 4) (m p : ZMod 2 × ZMod 2) : beta m (a • p) = a * beta m p := by
  revert a m p; decide

/-- The values of `β` lie in `2 · ℤ/4`, which annihilates `M`. This is what makes the
multiplication associative. -/
theorem beta_smul (m p q : ZMod 2 × ZMod 2) : beta m p • q = 0 := by
  revert m p q; decide

theorem beta_zero_left (p : ZMod 2 × ZMod 2) : beta 0 p = 0 := by revert p; decide

theorem beta_zero_right (m : ZMod 2 × ZMod 2) : beta m 0 = 0 := by revert m; decide

instance : Mul Carrier := ⟨fun x y ↦ (x.1 * y.1 + beta x.2 y.2, x.1 • y.2 + y.1 • x.2)⟩
instance : One Carrier := ⟨(1, 0)⟩

/-! ### Coordinates -/

theorem ext {x y : Carrier} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := Prod.ext h₁ h₂

@[simp] theorem fst_add (x y : Carrier) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem snd_add (x y : Carrier) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem fst_zero : (0 : Carrier).1 = 0 := rfl
@[simp] theorem snd_zero : (0 : Carrier).2 = 0 := rfl
@[simp] theorem fst_one : (1 : Carrier).1 = 1 := rfl
@[simp] theorem snd_one : (1 : Carrier).2 = 0 := rfl
@[simp] theorem fst_smul (a : ZMod 4) (x : Carrier) : (a • x).1 = a * x.1 := rfl
@[simp] theorem snd_smul (a : ZMod 4) (x : Carrier) : (a • x).2 = a • x.2 := rfl
@[simp] theorem fst_mul (x y : Carrier) : (x * y).1 = x.1 * y.1 + beta x.2 y.2 := rfl
@[simp] theorem snd_mul (x y : Carrier) : (x * y).2 = x.1 • y.2 + y.1 • x.2 := rfl

/-! ### The algebra structure -/

instance : NonAssocRing Carrier :=
  { (inferInstance : AddCommGroup Carrier), (inferInstance : Mul Carrier),
    (inferInstance : One Carrier) with
    left_distrib x y z := ext (by simp only [fst_mul, fst_add, snd_add, beta_add_right]; ring)
      (by simp only [snd_mul, fst_add, snd_add]; module)
    right_distrib x y z := ext (by simp only [fst_mul, fst_add, snd_add, beta_add_left]; ring)
      (by simp only [snd_mul, fst_add, snd_add]; module)
    zero_mul x := ext (by simp [beta_zero_left]) (by simp)
    mul_zero x := ext (by simp [beta_zero_right]) (by simp)
    one_mul x := ext (by simp [beta_zero_left]) (by simp)
    mul_one x := ext (by simp [beta_zero_right]) (by simp) }

instance : SMulCommClass (ZMod 4) Carrier Carrier where
  smul_comm a x y := by
    change a • (x * y) = x * (a • y)
    exact ext (by simp only [fst_smul, fst_mul, snd_smul, beta_smul_right]; ring)
      (by simp only [snd_smul, snd_mul, fst_smul]; module)

instance : IsScalarTower (ZMod 4) Carrier Carrier where
  smul_assoc a x y := by
    change (a • x) * y = a • (x * y)
    exact ext (by simp only [fst_smul, fst_mul, snd_smul, beta_smul_left]; ring)
      (by simp only [snd_smul, snd_mul, fst_smul]; module)

/-- The multiplication is **associative**: the two sides of associativity differ only in the
`M`-component, where they are `β(m, p) • q` and `β(p, q) • m`, both in `2 · M = 0`
(`Carrier.beta_smul`). -/
theorem mul_assoc (x y z : Carrier) : x * y * z = x * (y * z) :=
  ext (by
      simp only [fst_mul, snd_mul, beta_add_left, beta_add_right, beta_smul_left, beta_smul_right]
      ring)
    (by
      simp only [fst_mul, snd_mul, add_smul, beta_smul, add_zero]
      module)

instance : IsAlternative Carrier :=
  ⟨fun a b ↦ (mul_assoc a a b).symm, fun a b ↦ mul_assoc b a a⟩

/-- The companion bilinear form of the norm: `n(x, y) = 2 a b - β(m, p) - β(p, m)`. -/
def polarForm : Carrier →ₗ[ZMod 4] Carrier →ₗ[ZMod 4] ZMod 4 :=
  LinearMap.mk₂ (ZMod 4) (fun x y ↦ 2 * x.1 * y.1 - beta x.2 y.2 - beta y.2 x.2)
    (fun x x' y ↦ by simp only [fst_add, snd_add, beta_add_left, beta_add_right]; ring)
    (fun a x y ↦ by
      simp only [fst_smul, snd_smul, beta_smul_left, beta_smul_right, smul_eq_mul]; ring)
    (fun x y y' ↦ by simp only [fst_add, snd_add, beta_add_left, beta_add_right]; ring)
    (fun a x y ↦ by
      simp only [fst_smul, snd_smul, beta_smul_left, beta_smul_right, smul_eq_mul]; ring)

/-- The norm `n (a, m) = a² - β(m, m)`. -/
def norm : QuadraticForm (ZMod 4) Carrier where
  toFun x := x.1 * x.1 - beta x.2 x.2
  toFun_smul a x := by
    simp only [fst_smul, snd_smul, beta_smul_left, beta_smul_right, smul_eq_mul]; ring
  exists_companion' := ⟨polarForm, fun x y ↦ by
    simp only [polarForm, LinearMap.mk₂_apply, fst_add, snd_add, beta_add_left, beta_add_right]
    ring⟩

end Carrier

/-- The conic algebra structure: `n 1 = 1` and `x² = t(x) • x - n(x) • 1`. -/
def conic : ConicAlgebra (ZMod 4) Carrier where
  norm := Carrier.norm
  norm_one := by decide
  mul_self := by decide

/-- The first basis vector of `M`, as an element of the algebra. -/
def m₁ : Carrier := (0, 1, 0)

/-- The second basis vector of `M`, as an element of the algebra. -/
def m₂ : Carrier := (0, 0, 1)

theorem m₁_mul_m₂ : m₁ * m₂ = (2 : ZMod 4) • (1 : Carrier) := by decide

theorem m₂_mul_m₁ : m₂ * m₁ = 0 := by decide

/-- **The trace defect of an associative conic algebra can be nonzero**: here it is `-2 = 2`. -/
theorem traceDefect_eq : conic.traceDefect m₁ m₂ = 2 := by decide

theorem traceDefect_ne_zero : conic.traceDefect m₁ m₂ ≠ 0 := by decide

/-- **Conjugation need not be an anti-homomorphism**, even for an associative conic algebra: over
`ℤ/4`, `conj (m₁ m₂) = 2 · 1` but `conj m₂ * conj m₁ = 0`.

Contrast `ConicAlgebra.conj_mul`, which gives the anti-homomorphism property for alternative conic
algebras over a *field*. -/
theorem conj_mul_ne : conic.conj (m₁ * m₂) ≠ conic.conj m₂ * conic.conj m₁ := by decide

end TraceDefectCounterexample

end ConicAlgebra
