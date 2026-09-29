/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
module

public import LeanPool.QuantumQuery.QueryBounds
public import LeanPool.QuantumQuery.Polynomial

/-!
# Adversary bounds and the polynomial method for quantum queries

Source: arxiv:1011.3020v2, url:https://github.com/troyjlee/quantum-query-complexity/tree/517ba85eb211232771429804d8583e3f52b9d541
Authors: Troy Lee
Status: verified
Main declarations: `QuantumQueryComplexity.boundedErrorQQuery_characterized_by_advPM`
Tags: quantum-computing, query-complexity, adversary-method, polynomial-method
MSC: 68Q12, 81P68
-/

/-!
# Quantum query foundations

Adapted from Troy Lee’s Apache-2.0-licensed quantum-query-complexity library,
commit `517ba85eb211232771429804d8583e3f52b9d541`. The selected closure preserves
adversary duality and composition, operational query characterizations,
and the polynomial method. Formalization by Troy Lee with Claude and Codex.

Modifications for Lean Pool: Lean/Mathlib 4.34.0 port, module-system migration,
namespace-preserving import relocation, proof and instance cleanup.

## Sources and scope

* Høyer, Lee, and Špalek, *Negative weights make adversaries stronger*,
  [arXiv:quant-ph/0611054v2](https://arxiv.org/abs/quant-ph/0611054v2):
  the adversary lower bound and composition lower bound.
* Lee, Mittal, Reichardt, Špalek, and Szegedy, *Quantum query complexity of state conversion*,
  [arXiv:1011.3020v2](https://arxiv.org/abs/1011.3020v2), Theorems 3.4 and 4.1:
  Boolean-output duality and the reflection-based extraction architecture.
* Reichardt, *Reflections for quantum query algorithms*,
  [arXiv:1005.1601v1](https://arxiv.org/abs/1005.1601v1), Theorem 1.3:
  the Boolean adversary characterization.
* Belovs and Lee, *The quantum query complexity of composition with a relation*,
  [arXiv:2004.06439v1](https://arxiv.org/abs/2004.06439v1), Theorems 1 and 7:
  total Boolean perfect composition and the all-pairs dual formulation.
* Beals, Buhrman, Cleve, Mosca, and de Wolf, *Quantum Lower Bounds by Polynomials*,
  [arXiv:quant-ph/9802049v3](https://arxiv.org/abs/quant-ph/9802049v3), Lemmas 4.1–4.2:
  amplitude and output-probability degree bounds.

The characterizations here use explicitly padded value and XOR oracles at error `1/3`,
with the constants stated in the project card. Strong duality concerns infimum and
supremum values for real vector families; optimizer attainment and equivalence with
complex optimization are not additional conclusions. The uniform extraction theorem
takes a supplied dual certificate. Polynomial representations are not asserted to be
multilinear. The source papers contain further results outside this imported closure.
-/
