/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
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

public import LeanPool.PersistentSOS.Contracts

/-!
# Persistent failure of quartic sum-of-squares exactness

Source: url:https://github.com/JD-Jones-ASES/persistent-sos
Authors: JD Jones
Status: verified
Main declarations: `PersistentSOS.persistent_failure`, `PersistentSOS.unique_persistent_failure`
Tags: sum-of-squares, polynomial-optimization, exact-certificates
MSC: 90C22, 90C26, 14P10
-/

/-!
## Mathematical context and certificate data

This explicit example addresses the zero-gradient, negative-definite-Hessian case in
Cartis and Zhu, [Remark 2.3](https://arxiv.org/html/2601.20418v2#S2.SS3).
It does not contradict their sufficient conditions with nonzero gradient or
positive-definite Hessian at the origin. Positive curvature in the companion
example is proved at its unique global minimizer.

The analytic construction uses the classical Choi–Lam quartic
([1977](https://doi.org/10.1007/BF01360024)) and a contraction variant of
Tkachev's cubic normal form ([2010](https://doi.org/10.1090/S0002-9939-10-10385-2)).
The polynomial inequalities and exact moment certificate are proved here;
these published results are not assumptions of the Lean theorems.

The eight integer matrix certificates and the sparse moment table were generated
from exact rational data by the upstream `scripts/generate_moments.py` at the
commit recorded in the retained MIT notice. Their proofs check every Schur
identity, positive pivot, basis-coverage identity, and sphere localizer in Lean.
The port only factors repeated large integers and wraps the generated data;
it preserves every matrix entry. Python and numerical optimization are not
part of the formal proof's trusted base.
-/
