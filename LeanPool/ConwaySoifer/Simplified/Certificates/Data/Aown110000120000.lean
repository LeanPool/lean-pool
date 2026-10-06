/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Certificates.Model

/-! Exact certificate data adapted from the upstream public release. -/

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

namespace ConwaySoifer.Simplified.Certificates.Data

open ConwaySoifer.Certificates

/-- Exact interval and proposed forced-point trace for the Aown contact case. -/
def Aown110000120000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 11 100), hi := (mkRat 3 25), den := 9000000000000,
    steps := [
      ⟨0, ([990000000000], [0])⟩,
      ⟨2, ([2025000000000], [6975000000000])⟩,
      ⟨2, ([7755000000000], [750000000000])⟩,
      ⟨4, ([(-8010000000000)], [0])⟩,
      ⟨3, ([(-1860000000000)], [9000000000000])⟩,
      ⟨0, ([468000000000], [6750000000000])⟩,
      ⟨0, ([495000000000], [6750000000000])⟩,
      ⟨0, ([3000000000000], [4680000000000])⟩,
      ⟨0, ([3750000000000], [3960000000000])⟩,
      ⟨0, ([4875000000000], [2805000000000])⟩,
      ⟨0, ([7140000000000], [375000000000])⟩,
      ⟨0, ([7218000000000], [282000000000])⟩,
      ⟨8, ([(-10920000000000)], [9000000000000])⟩,
      ⟨3, ([(-1500000000000)], [7680000000000])⟩,
      ⟨4, ([(-750000000000)], [90000000000])⟩,
      ⟨3, ([(-750000000000)], [660000000000])⟩,
      ⟨0, ([(-8670000000000)], [7500000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
