/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/graham-lpt-lean, commit c8ed035b407cc554faf4b68df0cf3edc70058977.
Original MIT notice (retained under the permission to sublicense):

MIT License

Copyright (c) 2026 JD Jones

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GrahamLPT.Contracts
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity.Finset

/-!
# Sharp list-scheduling and longest-processing-time bounds

Source: url:https://github.com/JD-Jones-ASES/graham-lpt-lean/tree/c8ed035b407cc554faf4b68df0cf3edc70058977
Authors: JD Jones
Status: verified
Main declarations: `GrahamLPT.lpt_le_optMakespan`, `GrahamLPT.lpt_eq_bound_iff_graham`
Tags: scheduling, approximation-algorithms, combinatorial-optimization
MSC: 68M20, 90B35, 68W25
-/

/-!
## References and scope

* R. L. Graham, *Bounds for certain multiprocessing anomalies* (1966),
  DOI: 10.1002/j.1538-7305.1966.tb01709.x.
* R. L. Graham, *Bounds on multiprocessing timing anomalies* (1969), Theorem 2,
  DOI: 10.1137/0117039. The bound here also permits zero-length jobs.
* G. Dósa, *Graham's example is the only tight one for P || Cmax* (2004), Theorem 2,
  Annales Univ. Sci. Budapest. Sect. Math. 47, 207–210. The formal characterization
  makes positive scaling, job permutation, nonempty instances and m ≥ 2 explicit.
* F. Della Croce and R. Scatamacchia, *The Longest Processing Time rule for identical
  parallel machines revisited* (2020), arXiv:1801.05489, Propositions 2–4.

The fixed-job-count supremum is a separate proved result. It is not a formalization
of the strict supremum gap asserted in Dósa's Remark 1. Processing-time bounds,
precedence constraints and an executable running-time analysis are outside this development.
-/
