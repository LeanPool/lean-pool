/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/

module

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteIndexObstruction
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteGodelRE
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcretePiOneCharacterization
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteGeneratedCongruence
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteWeakTotality
public import LeanPool.PointwiseComposition.FailureOfComposition.RangeGodel
public import LeanPool.PointwiseComposition.FailureOfComposition.RangeProductive
public import LeanPool.PointwiseComposition.FailureOfComposition.PartialRecursiveQuotient
public import LeanPool.PointwiseComposition.FailureOfComposition.ManuscriptObstruction

/-!
# Pointwise provable equality and the failure of composition

Source: arxiv:2609.25556, url:https://github.com/flengyel/FailureOfComposition
Authors: Florian Lengyel
Status: verified
Main declarations: `PointwiseComposition.no_quotient_of_enumerable_axioms`
Tags: computability, provability, first-order-arithmetic, quotient-congruences, mathematical-logic
MSC: 03D75, 03F40, 08A30, 18B10
-/

/-!
# Pointwise provable equality and the failure of composition

Ported from Florian Lengyel’s Apache-2.0 formalization at
`506d1f1494d6c05b0ba304edf5fe0bfa6c32864b`. The dependency closure includes the
Formalized Formal Logic Foundation arithmetic library at
`01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d` (Apache-2.0), whose contributors
retain authorship of that infrastructure. The Foundation license notice is
"Copyright 2026 Formalized Formal Logic". Lean proofs in the main development
were produced by AI agents under Florian Lengyel’s direction.
-/

@[expose] public section

namespace PointwiseComposition

/-- No quotient operation respects program composition for a consistent extension of PA
whose axiom codes are recursively enumerable. -/
alias no_quotient_of_enumerable_axioms :=
  FailureOfComposition.ConcreteIndices.no_index_quotient_of_re_axioms

end PointwiseComposition
