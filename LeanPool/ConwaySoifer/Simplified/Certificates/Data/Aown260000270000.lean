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
def Aown260000270000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 13 50), hi := (mkRat 27 100), den := 9000000000000,
    steps := [
      ⟨0, ([(-1170000000000)], [375000000000])⟩,
      ⟨0, ([(-1170000000000)], [795000000000])⟩,
      ⟨0, ([(-795000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-375000000000)], [(-795000000000)])⟩,
      ⟨2, ([270000000000], [9000000000000])⟩,
      ⟨0, ([375000000000], [(-1170000000000)])⟩,
      ⟨0, ([795000000000], [(-1170000000000)])⟩,
      ⟨2, ([2340000000000], [6750000000000])⟩,
      ⟨0, ([2685000000000], [0])⟩,
      ⟨2, ([5430000000000], [3570000000000])⟩,
      ⟨2, ([5850000000000], [2625000000000])⟩,
      ⟨1, ([9000000000000], [4788000000000])⟩,
      ⟨7, ([9000000000000], [5490000000000])⟩,
      ⟨3, ([(-5250000000000)], [7830000000000])⟩,
      ⟨0, ([0], [2595000000000])⟩,
      ⟨2, ([2250000000000], [9000000000000])⟩,
      ⟨0, ([4320000000000], [930000000000])⟩,
      ⟨2, ([6000000000000], [2220000000000])⟩,
      ⟨2, ([6180000000000], [2820000000000])⟩,
      ⟨2, ([6375000000000], [2340000000000])⟩,
      ⟨6, ([8850000000000], [(-3000000000000)])⟩,
      ⟨0, ([225000000000], [5625000000000])⟩,
      ⟨0, ([1125000000000], [(-1560000000000)])⟩,
      ⟨0, ([1560000000000], [4815000000000])⟩,
      ⟨0, ([4212000000000], [2163000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
