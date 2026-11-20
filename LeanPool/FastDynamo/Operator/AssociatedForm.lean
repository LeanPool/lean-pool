/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.Domain
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Operators associated with complex forms

This file gives a concrete, domain-aware realization of the operator associated
with a bounded complex form.  It is designed for the form used in Section 2 of
the paper, but contains no paper-specific analytic assumption.

Let `V` be a form domain, let `X` be the pivot Hilbert space, and let
`j : V -> X` be a continuous, injective, dense embedding.  A form that is
linear in its first variable and conjugate-linear in its second is represented
as

`a : V ->L[Complex] (V ->Lstar[Complex] Complex)`.

Mathlib's complex inner product is conjugate-linear in its first variable,
whereas the paper declares its inner product linear in the first
variable.  Consequently the paper pairing

`<f, phi>_paper`

is represented in Lean by `inner Complex (j phi) f`.  The pivot map below is
defined with exactly this convention.

The negative operator associated with `a` is characterized by

`a b phi = <f, phi>_paper` for every `phi`, where `f = -A b`.

We bundle the graph pair `(b, f)` in the product `V × X`
(`AssociatedFormProdDomain`).  The form identity is the kernel of a continuous
map, so this graph domain is complete.  Its domain embedding is `b |-> j b`,
while its operator action is `(b, f) |-> -f`.  Density of `j` makes `f` unique
and hence makes the domain embedding injective.

This construction defines the maximal operator associated with the form
directly.  Coercivity, sectoriality, resolvent existence, and PDE regularity
are separate properties, proved in other modules; none is assumed here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped ENNReal

/-! ## The pivot-space realization of anti-dual functionals -/

/-- The continuous complex anti-dual of `V`. -/
abbrev ComplexAntiDual (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace Complex V] :=
  V →L⋆[Complex] Complex

section Pivot

variable {V X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Complex V]
  [NormedAddCommGroup X] [InnerProductSpace Complex X]

/-- Embed a pivot-space vector into the anti-dual of the form domain.

Its value is

`associatedFormPivot j f phi = inner Complex (j phi) f`,

which is the Lean expression for the paper's linear-in-first pairing
`<f, phi>_paper`. -/
def associatedFormPivot (j : V →L[Complex] X) :
    X →L[Complex] ComplexAntiDual V :=
  ((ContinuousLinearMap.compSL V X Complex
      (RingHom.id Complex) (starRingEnd Complex)).flip j).comp
    (innerSLFlip Complex)

/--
The pivot embedding sends `f` to the anti-dual functional `phi ↦ inner ℂ (j phi) f`, which is the
Lean form of the paper's linear-in-the-first-slot pairing `⟨f, phi⟩`.
-/
@[simp] theorem associatedFormPivot_apply
    (j : V →L[Complex] X) (f : X) (phi : V) :
    associatedFormPivot j f phi = inner Complex (j phi) f := by
  rfl

/-- A dense pivot embedding separates pivot-space vectors through the
anti-dual pairing. -/
theorem associatedFormPivot_injective
    (j : V →L[Complex] X) (hj : DenseRange j) :
    Function.Injective (associatedFormPivot j) := by
  intro f g h
  exact hj.eq_of_inner_right (𝕜 := Complex) fun phi =>
    DFunLike.congr_fun h phi

end Pivot

/-! ## Graph realization

A `DomainOperator` only needs a normed domain.  The graph pairs are stored in the
standard product `V × X`, whose norm is the maximum of the two component norms; this is
convenient to specialize when the form and pivot spaces are themselves closed subspaces.
-/

section ProdGraph

variable {V X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Complex V]
  [NormedAddCommGroup X] [InnerProductSpace Complex X]

/-- The defect in the associated-form identity on the ordinary product
`V × X`. -/
def associatedFormProdGraphDefect
    (j : V →L[Complex] X)
    (a : V →L[Complex] ComplexAntiDual V) :
    (V × X) →L[Complex] ComplexAntiDual V :=
  a.comp (ContinuousLinearMap.fst Complex V X) -
    (associatedFormPivot j).comp (ContinuousLinearMap.snd Complex V X)

/-- The associated-form graph as a closed submodule of the ordinary product
`V × X`. -/
def AssociatedFormProdDomain
    (j : V →L[Complex] X)
    (a : V →L[Complex] ComplexAntiDual V) :
    Submodule Complex (V × X) :=
  (associatedFormProdGraphDefect j a).ker

/-- Cache the canonical scalar normed-space structure of the ordinary-product
graph.  Naming this instance prevents expensive reconstruction of the
product/submodule instance chain after specialization. -/
noncomputable instance associatedFormProdDomainNormedSpace
    (j : V →L[Complex] X)
    (a : V →L[Complex] ComplexAntiDual V) :
    NormedSpace Complex (AssociatedFormProdDomain j a) :=
  (AssociatedFormProdDomain j a).normedSpace

/-- Membership in the ordinary-product graph as an anti-dual equality. -/
theorem mem_associatedFormProdDomain_iff
    (j : V →L[Complex] X)
    (a : V →L[Complex] ComplexAntiDual V)
    (u : V × X) :
    u ∈ AssociatedFormProdDomain j a ↔
      a u.1 = associatedFormPivot j u.2 := by
  rw [AssociatedFormProdDomain]
  change a u.1 - associatedFormPivot j u.2 = 0 ↔ _
  exact sub_eq_zero

/-- Pointwise membership characterization, in the paper's
linear-in-first pairing convention. -/
theorem mem_associatedFormProdDomain_iff_forall
    (j : V →L[Complex] X)
    (a : V →L[Complex] ComplexAntiDual V)
    (u : V × X) :
    u ∈ AssociatedFormProdDomain j a ↔
      ∀ phi : V, a u.1 phi = inner Complex (j phi) u.2 := by
  rw [mem_associatedFormProdDomain_iff]
  constructor
  · intro h phi
    rw [h]
    exact associatedFormPivot_apply j u.2 phi
  · intro h
    ext phi
    simpa using h phi

/-- Evaluation of the stored form identity.  Because Mathlib's inner product
is conjugate-linear in its first argument, `inner Complex (j phi) f`
represents the paper pairing `<f, phi>`, which is linear in `f`. -/
theorem associatedFormProdDomain_relation_apply
    (j : V →L[Complex] X)
    (a : V →L[Complex] ComplexAntiDual V)
    (u : AssociatedFormProdDomain j a) (phi : V) :
    a u.1.1 phi = inner Complex (j phi) u.1.2 :=
  (mem_associatedFormProdDomain_iff_forall j a u.1).mp u.2 phi

/-- The physical embedding `(b,f) ↦ j b` from the ordinary-product graph. -/
def associatedFormProdEmbedding
    (j : V →L[Complex] X)
    (a : V →L[Complex] ComplexAntiDual V) :
    AssociatedFormProdDomain j a →L[Complex] X :=
  j.comp ((ContinuousLinearMap.fst Complex V X).comp
    (AssociatedFormProdDomain j a).subtypeL)

/-- The associated operator action `(b,f) ↦ -f`. -/
def associatedFormProdAction
    (j : V →L[Complex] X)
    (a : V →L[Complex] ComplexAntiDual V) :
    AssociatedFormProdDomain j a →L[Complex] X :=
  -(ContinuousLinearMap.snd Complex V X).comp
    (AssociatedFormProdDomain j a).subtypeL

/-- The ordinary-product graph embedding is injective when the form-domain
embedding is injective and dense. -/
theorem associatedFormProdEmbedding_injective
    (j : V →L[Complex] X) (hj : Function.Injective j)
    (hdense : DenseRange j)
    (a : V →L[Complex] ComplexAntiDual V) :
    Function.Injective (associatedFormProdEmbedding j a) := by
  intro u v huv
  have hb : u.1.1 = v.1.1 := by
    apply hj
    simpa [associatedFormProdEmbedding] using huv
  have hu := (mem_associatedFormProdDomain_iff_forall j a u.1).mp u.2
  have hv := (mem_associatedFormProdDomain_iff_forall j a v.1).mp v.2
  have hf : u.1.2 = v.1.2 := by
    apply associatedFormPivot_injective j hdense
    ext phi
    rw [associatedFormPivot_apply, associatedFormPivot_apply,
      ← hu phi, ← hv phi, hb]
  apply Subtype.ext
  exact Prod.ext hb hf

/-- The maximal domain-aware operator associated with `a`, using the
ordinary product norm on its graph domain. -/
def associatedFormProdOperator
    (j : V →L[Complex] X) (hj : Function.Injective j)
    (hdense : DenseRange j)
    (a : V →L[Complex] ComplexAntiDual V) :
    DomainOperator X (AssociatedFormProdDomain j a) where
  embedding := associatedFormProdEmbedding j a
  embedding_injective := associatedFormProdEmbedding_injective j hj hdense a
  op := associatedFormProdAction j a

/-- The domain embedding of the ordinary-product-norm associated operator is `u ↦ j u.1.1`. -/
@[simp] theorem associatedFormProdOperator_embedding_apply
    (j : V →L[Complex] X) (hj : Function.Injective j)
    (hdense : DenseRange j)
    (a : V →L[Complex] ComplexAntiDual V)
    (u : AssociatedFormProdDomain j a) :
    (associatedFormProdOperator j hj hdense a).embedding u =
      j u.1.1 := by
  rfl

/-- The action of the ordinary-product-norm associated operator is `u ↦ -u.1.2`. -/
@[simp] theorem associatedFormProdOperator_op_apply
    (j : V →L[Complex] X) (hj : Function.Injective j)
    (hdense : DenseRange j)
    (a : V →L[Complex] ComplexAntiDual V)
    (u : AssociatedFormProdDomain j a) :
    (associatedFormProdOperator j hj hdense a).op u = -u.1.2 := by
  rfl

end ProdGraph

section ProdComplete

variable {V X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Complex V] [CompleteSpace V]
  [NormedAddCommGroup X] [InnerProductSpace Complex X] [CompleteSpace X]

/-- The ordinary-product associated-form graph is complete because it is the
kernel of a continuous map between Banach spaces. -/
instance associatedFormProdDomainCompleteSpace
    (j : V →L[Complex] X)
    (a : V →L[Complex] ComplexAntiDual V) :
    CompleteSpace (AssociatedFormProdDomain j a) :=
  (associatedFormProdGraphDefect j a).isClosed_ker.completeSpace_coe

end ProdComplete

end

end FastDynamo
