/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Defs
public import LeanPool.CompositionAlgebrasOverRings.Conic.BaseChangeMultiplicative

/-!
# Base change of composition algebras (`GPR 19.7`)

A composition algebra stays one after base change along any `k → S`. This is the property that
`ConicAlgebra.IsComposition` was designed to have, and it is why the definition asks for the norm
to be **non-singular** rather than regular or merely non-degenerate: non-singularity is
base-change stable by construction, while `GPR 19.4` exhibits a conic algebra whose norm is
non-degenerate but whose base change's norm is not (which is also why there is no
`PreCompositionAlgebra` here; see `Composition/Defs.lean`).

## Main results

* `ConicAlgebra.IsComposition.baseChangeOfProjective` : `S ⊗[k] A` is a composition algebra
  over `S`.

## Implementation notes

Both clauses come from elsewhere: multiplicativity from
`ConicAlgebra.IsMultiplicative.baseChangeOfProjective`, non-singularity from
`QuadraticForm.IsGPRNonsingular.baseChangeOfProjective`. Finite projectivity of `S ⊗[k] A` over
`S` is an instance. The only content here is that the norm of the base-changed conic algebra is
the base-changed norm, which is definitional
(`ConicAlgebra.baseChangeOfProjective_norm`).

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.5, 19.7.
-/

@[expose] public section

universe u v w w'

open scoped TensorProduct

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
variable {C : ConicAlgebra k A}

/-- **A composition algebra stays a composition algebra after base change.**

Non-singularity of the norm survives because it is a statement about every field over the base,
and a field over `S` is a field over `k`; multiplicativity survives by
`ConicAlgebra.IsMultiplicative.baseChangeOfProjective`. Nothing is assumed about `2`, about the
rank, or about `S`. -/
theorem IsComposition.baseChangeOfProjective (h : C.IsComposition.{u, v, w'}) (S : Type w)
    [CommRing S] [Algebra k S] :
    (C.baseChangeOfProjective S).IsComposition.{w, max v w, w'} where
  isGPRNonsingular := h.isGPRNonsingular.baseChangeOfProjective S
  isMultiplicative := h.isMultiplicative.baseChangeOfProjective S

end ConicAlgebra
