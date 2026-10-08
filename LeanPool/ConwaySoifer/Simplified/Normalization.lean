/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Normalization
public import LeanPool.ConwaySoifer.Simplified.Geometry.Core
public import LeanPool.ConwaySoifer.Simplified.Geometry.Bridge
public import LeanPool.ConwaySoifer.Simplified.Geometry.Midpoint
import Mathlib.Tactic

/-!
# Normalization

Geometry and verified arithmetic for the Conway–Soifer covering theorem at n = 3.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

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

@[expose] public section

noncomputable section
namespace ConwaySoifer.Simplified

/-- Unconditional geometric normalization for the simplified route. It uses
no `coreChecked`, `bridgeChecked`, or `midForbidChecked` evaluations. -/
theorem exists_canonical (r : ℝ) (T : Configuration) (hside : CommonSide T r)
    (hcover : Covers T) (hr : r < 1) :
    ∃ (c : ContactCase) (U : Configuration) (s : ℝ), Canonical c U r s :=
  ConwaySoifer.exists_canonical_of_geometry core_exclusion bridge_exclusion midpoint_exclusion
    r T hside hcover hr

end ConwaySoifer.Simplified
