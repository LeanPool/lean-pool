/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/

module

public import LeanPool.MovingSofa.Development.Geometry.Applications.Development003
/-!
# Optimality of Gerver's sofa

Source: arxiv:2411.19826, url:https://github.com/deancureton/MovingSofa/tree/4d5569131940815f47a9ccf3e90a4c5043c56127
Authors: Dean Cureton, Dawid Trela, Rado Kirov, Kirill Alkhimov, The Tau Ceti contributors, The Formal Conjectures Authors
Status: verified
Main declarations: `MovingSofa.sofaConstant_eq_volume_gerversSofa`, `MovingSofa.GerversSofa.ABφθSpec.existsUnique`, `MovingSofa.isMovingSofa_gerversSofa`
Tags: convex-geometry, moving-sofa-problem, geometric-optimization, bounded-variation, interval-arithmetic, Jordan-curve-theorem
MSC: 52A40, 52A10, 49Q10
-/

/-!
## Imported sources and provenance

The main formalization is from Dean Cureton's `deancureton/MovingSofa` at
`4d5569131940815f47a9ccf3e90a4c5043c56127` (Apache-2.0). The proofs were produced using
Codex and Claude Code under Cureton's direction. Completion was announced on 20 September 2026.

The coherent dependency closure also contains:

* Dawid Trela's `dawidmtrela-dotcom/GerverSofaLean`, release v1.1.0 (MIT; notice below), including its Part F bridge.
* `alerad/leancert` at `571a228555ae38742448854be81d7b59d994a8e3` (Apache-2.0):
  pure interval arithmetic and its soundness proofs, without the metaprogramming front end.
* Rado Kirov's `rkirov/jordan_pick` at
  `b3c9b7cf7358bf81a077d78ad67e6e8247869ddd` (Apache-2.0): Jordan separation and Brouwer.
* `TauCetiProject/TauCeti` at `c52a81811e4626d2e9769fe9b0c701168c211332` (Apache-2.0):
  variation, filled hulls, and supporting topology.
* `google-deepmind/formal-conjectures` at `ddfbaf90f4482030d88aae5233fe933874296a23`
  (Apache-2.0): the moving-sofa definitions, with its open parameter theorem proved here.

Jonathan Ho's isoperimetric infrastructure is reused from `LeanPool.Isoperimetric`.
-/

/-
The GerverSofa dependency retains its original MIT licence:

MIT License

Copyright (c) 2026 Dawid Trela

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
