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

/-- Exact interval and proposed forced-point trace for the Sext contact case. -/
def Sext330000340000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 33 100), hi := (mkRat 17 50), den := 9000000000000,
    steps := [
      ⟨0, ([(-1485000000000)], [735000000000])⟩,
      ⟨0, ([(-1125000000000)], [0])⟩,
      ⟨0, ([(-750000000000)], [(-735000000000)])⟩,
      ⟨0, ([(-750000000000)], [1485000000000])⟩,
      ⟨0, ([0], [1125000000000])⟩,
      ⟨0, ([735000000000], [750000000000])⟩,
      ⟨0, ([5175000000000], [(-5040000000000)])⟩,
      ⟨0, ([5346000000000], [(-4596000000000)])⟩,
      ⟨9, ([6720000000000], [(-11970000000000)])⟩,
      ⟨9, ([9000000000000], [(-11070000000000)])⟩,
      ⟨3, ([(-2760000000000)], [2760000000000])⟩,
      ⟨5, ([3750000000000], [(-8205000000000)])⟩,
      ⟨5, ([4545000000000], [(-9000000000000)])⟩,
      ⟨8, ([(-12285000000000)], [9000000000000])⟩,
      ⟨4, ([(-7515000000000)], [3193875000000])⟩,
      ⟨4, ([(-6750000000000)], [3096000000000])⟩,
      ⟨4, ([(-5625000000000)], [2565000000000])⟩,
      ⟨4, ([(-5595000000000)], [(-3405000000000)])⟩,
      ⟨4, ([(-4710000000000)], [0])⟩,
      ⟨2, ([(-2250000000000)], [5040000000000])⟩,
      ⟨2, ([(-135000000000)], [5175000000000])⟩,
      ⟨8, ([(-13971000000000)], [4971000000000])⟩,
      ⟨4, ([(-9000000000000)], [3375000000000])⟩,
      ⟨3, ([(-9000000000000)], [4830000000000])⟩,
      ⟨3, ([(-5235000000000)], [9000000000000])⟩,
      ⟨5, ([(-3165000000000)], [(-5835000000000)])⟩,
      ⟨0, ([(-1605000000000)], [(-375000000000)])⟩,
      ⟨0, ([5250000000000], [(-5160000000000)])⟩,
      ⟨0, ([(-2730000000000)], [2730000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
