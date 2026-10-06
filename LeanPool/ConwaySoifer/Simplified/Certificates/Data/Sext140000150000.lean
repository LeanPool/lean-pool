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
def Sext140000150000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 7 50), hi := (mkRat 3 20), den := 9000000000000,
    steps := [
      ⟨0, ([(-750000000000)], [330000000000])⟩,
      ⟨0, ([(-420000000000)], [750000000000])⟩,
      ⟨0, ([(-330000000000)], [750000000000])⟩,
      ⟨0, ([330000000000], [420000000000])⟩,
      ⟨0, ([1260000000000], [(-1260000000000)])⟩,
      ⟨9, ([8625000000000], [(-9705000000000)])⟩,
      ⟨9, ([9000000000000], [(-9765000000000)])⟩,
      ⟨5, ([6732000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-5607000000000)], [(-3393000000000)])⟩,
      ⟨0, ([4125000000000], [(-5220000000000)])⟩,
      ⟨0, ([4410000000000], [(-5250000000000)])⟩,
      ⟨0, ([4665000000000], [(-5040000000000)])⟩,
      ⟨8, ([(-14625000000000)], [5625000000000])⟩,
      ⟨3, ([(-8250000000000)], [6732000000000])⟩,
      ⟨3, ([(-6750000000000)], [6330000000000])⟩,
      ⟨4, ([(-5625000000000)], [(-630000000000)])⟩,
      ⟨4, ([(-3585000000000)], [(-5040000000000)])⟩,
      ⟨4, ([(-3495000000000)], [(-5505000000000)])⟩,
      ⟨8, ([(-15750000000000)], [9000000000000])⟩,
      ⟨8, ([(-12540000000000)], [3540000000000])⟩,
      ⟨3, ([(-8025000000000)], [4875000000000])⟩,
      ⟨3, ([(-5805000000000)], [5175000000000])⟩,
      ⟨4, ([(-5580000000000)], [(-420000000000)])⟩,
      ⟨3, ([(-5040000000000)], [4290000000000])⟩,
      ⟨5, ([(-1260000000000)], [(-7365000000000)])⟩,
      ⟨8, ([(-14850000000000)], [9000000000000])⟩,
      ⟨3, ([(-8370000000000)], [4500000000000])⟩,
      ⟨4, ([(-5430000000000)], [0])⟩,
      ⟨2, ([(-525000000000)], [6375000000000])⟩,
      ⟨0, ([(-375000000000)], [(-420000000000)])⟩,
      ⟨0, ([3915000000000], [(-5175000000000)])⟩,
      ⟨0, ([4740000000000], [(-6000000000000)])⟩,
      ⟨0, ([6750000000000], [(-6480000000000)])⟩,
      ⟨8, ([(-14580000000000)], [9000000000000])⟩,
      ⟨3, ([(-8625000000000)], [3960000000000])⟩,
      ⟨3, ([(-4755000000000)], [4125000000000])⟩,
      ⟨2, ([(-3660000000000)], [9000000000000])⟩,
      ⟨4, ([(-2775000000000)], [(-375000000000)])⟩,
      ⟨2, ([(-630000000000)], [5880000000000])⟩,
      ⟨5, ([4995000000000], [(-8370000000000)])⟩,
      ⟨8, ([(-13830000000000)], [9000000000000])⟩,
      ⟨8, ([(-12030000000000)], [3030000000000])⟩,
      ⟨3, ([(-9000000000000)], [3000000000000])⟩,
      ⟨3, ([(-7320000000000)], [2820000000000])⟩,
      ⟨3, ([(-6750000000000)], [2790000000000])⟩,
      ⟨3, ([(-6660000000000)], [7560000000000])⟩,
      ⟨3, ([(-5040000000000)], [2790000000000])⟩,
      ⟨2, ([(-4650000000000)], [9000000000000])⟩,
      ⟨3, ([(-3960000000000)], [2835000000000])⟩,
      ⟨3, ([(-3780000000000)], [2880000000000])⟩,
      ⟨3, ([(-3630000000000)], [3000000000000])⟩,
      ⟨4, ([(-3465000000000)], [(-5535000000000)])⟩,
      ⟨1, ([5625000000000], [1680000000000])⟩,
      ⟨8, ([(-10650000000000)], [7500000000000])⟩,
      ⟨8, ([(-10530000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [2985000000000])⟩,
      ⟨2, ([(-6195000000000)], [9000000000000])⟩,
      ⟨2, ([(-2250000000000)], [5040000000000])⟩,
      ⟨4, ([(-2130000000000)], [0])⟩,
      ⟨2, ([(-1125000000000)], [3960000000000])⟩,
      ⟨2, ([(-630000000000)], [3630000000000])⟩,
      ⟨7, ([4140000000000], [9000000000000])⟩,
      ⟨1, ([4857000000000], [1875000000000])⟩,
      ⟨1, ([4875000000000], [3150000000000])⟩,
      ⟨0, ([7005000000000], [(-6375000000000)])⟩,
      ⟨7, ([9000000000000], [7320000000000])⟩,
      ⟨8, ([(-11775000000000)], [2775000000000])⟩,
      ⟨3, ([(-9000000000000)], [2745000000000])⟩,
      ⟨3, ([(-5250000000000)], [6510000000000])⟩,
      ⟨4, ([(-5175000000000)], [1260000000000])⟩,
      ⟨3, ([(-4500000000000)], [5760000000000])⟩,
      ⟨0, ([(-930000000000)], [0])⟩,
      ⟨0, ([(-420000000000)], [795000000000])⟩,
      ⟨1, ([2790000000000], [2250000000000])⟩,
      ⟨1, ([2790000000000], [5580000000000])⟩,
      ⟨1, ([7500000000000], [(-3960000000000)])⟩],
    last := 1 }

end ConwaySoifer.Simplified.Certificates.Data
