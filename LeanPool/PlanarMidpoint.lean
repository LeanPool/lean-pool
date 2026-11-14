/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.PlanarMidpoint.MidpointRigidity
public import LeanPool.PlanarMidpoint.TensorSemantics
public import LeanPool.PlanarMidpoint.FiveDirections

/-!
# Planar Euclidean dual-geodesic midpoint rigidity

Source: arxiv:2609.07551, url:https://github.com/JD-Jones-ASES/PlanarMidpoint/tree/f277b89a3b0db20872101fd61580ecced748e7c1
Authors: JD Jones
Status: verified
Main declarations: `PlanarMidpoint.planar_dual_midpoint_rigidity`
Tags: differential-geometry, ordinary-differential-equations, functional-equations
MSC: 53B12, 39B22
-/

/-! Planar Euclidean midpoint rigidity and its differentiable core. -/

@[expose] public section

/-
Original upstream MIT notice, retained for the Apache-2.0 adaptation:

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
