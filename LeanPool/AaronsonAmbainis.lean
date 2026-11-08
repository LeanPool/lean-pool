/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/

module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import LeanPool.AaronsonAmbainis.Main
public import LeanPool.AaronsonAmbainis.Bridge.Instance
public import LeanPool.AaronsonAmbainis.Bridge.Positivity
public import LeanPool.AaronsonAmbainis.Bridge.PaperInequalities
public import LeanPool.AaronsonAmbainis.Bridge.PaperTheorems
public import LeanPool.AaronsonAmbainis.Row.HypothesisCheck
public import LeanPool.AaronsonAmbainis.Dual.Sanity

/-!
# The Aaronson–Ambainis influence conjecture

Source: url:https://github.com/physical-superintelligence/aaronson-ambainis/tree/2a6ceaef872ae993708950f951989134084b851a
Authors: David Turturean
Status: verified
Main declarations: `AaronsonAmbainis.aaronson_ambainis`,
  `AaronsonAmbainis.aaronson_ambainis_explicit`, `AaronsonAmbainis.aaronson_ambainis_pm`
Tags: boolean-functions, influence, fractional-certificates
MSC: 68Q12, 60C05, 05D40
-/

/-!
## Upstream attribution

Adapted for Lean Pool’s module system and pinned dependencies from upstream commit
`2a6ceaef872ae993708950f951989134084b851a`.

The Aaronson–Ambainis conjecture: paper and Lean 4 formalization

Copyright 2026 David Turturean

The Lean source code and the repository documentation are licensed under the
Apache License, Version 2.0. See LICENSE for the full text.

The upstream paper, "A proof of the Aaronson–Ambainis conjecture," is authored
by David Turturean and remains copyright its author.

The conjecture is due to Scott Aaronson and Andris Ambainis, "The need for
structure in quantum speedups," Theory of Computing 10 (2014), 133-166
(arXiv:0911.0996).

The proof builds on ideas from the following works, which are credited in the
paper together with the other sources:

  David Reimer, "Proof of the van den Berg-Kesten conjecture," Combinatorics,
  Probability and Computing 9 (2000), 27-32 (the Butterfly Lemma, which the
  bijection theorem of the paper refines, and the passage from antipodal pairs
  of subcubes to all pairs of points).

  Jeff Kahn, Michael Saks and Clifford Smyth, "The dual BKR inequality and
  Rudich's conjecture," Combinatorics, Probability and Computing 20 (2011),
  257-266 (the proof of the dual inequality, which uses that passage and
  certificates at a point and at its antipode).

  Raghav Kulkarni and Avishay Tal, "On fractional block sensitivity," Chicago
  Journal of Theoretical Computer Science 2016, Article 8 (the lemma on the
  fractional certificates at two points with different values).

  Shachar Lovett and Jiapeng Zhang, "Fractional certificates for bounded
  functions," ITCS 2023 (the use of fractional certificates and of level sets).

  Avantika Agarwal and Shalev Ben-David, "Oracle separations for the
  quantum-classical polynomial hierarchy," arXiv:2410.19062; ITCS 2026 (the
  bound for the fractional block sensitivity of bounded functions of low
  degree, and the method of its proof).

  Yuval Filmus, Hamed Hatami, Nathan Keller and Noam Lifshitz, "On the sum of
  the L1 influences of bounded functions," Israel Journal of Mathematics 214
  (2016), 167-192 (the bound for the sum of the absolute increments at a
  point).

The mathematical statements and Lean formalization were produced by AI models in a
research harness developed by David Turturean at PSI. David Turturean reviewed the
paper and is responsible for its correctness.
-/
