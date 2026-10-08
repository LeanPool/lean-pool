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

/-- Exact interval and proposed forced-point trace for the Sint contact case. -/
def Sint140000150000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 7 50), hi := (mkRat 3 20), den := 9000000000000,
    steps := [
      ⟨4, ([(-7965000000000)], [0])⟩,
      ⟨3, ([(-2268000000000)], [9000000000000])⟩,
      ⟨0, ([(-750000000000)], [330000000000])⟩,
      ⟨0, ([(-420000000000)], [(-330000000000)])⟩,
      ⟨0, ([330000000000], [(-750000000000)])⟩,
      ⟨0, ([420000000000], [(-750000000000)])⟩,
      ⟨0, ([750000000000], [(-420000000000)])⟩,
      ⟨8, ([(-11520000000000)], [8895000000000])⟩,
      ⟨8, ([(-11268000000000)], [9000000000000])⟩,
      ⟨0, ([(-1095000000000)], [5220000000000])⟩,
      ⟨0, ([(-840000000000)], [5250000000000])⟩,
      ⟨0, ([(-375000000000)], [5040000000000])⟩,
      ⟨4, ([(-7875000000000)], [2655000000000])⟩,
      ⟨4, ([(-6375000000000)], [840000000000])⟩,
      ⟨8, ([(-15660000000000)], [6660000000000])⟩,
      ⟨3, ([(-8625000000000)], [7560000000000])⟩,
      ⟨3, ([(-8370000000000)], [7470000000000])⟩,
      ⟨5, ([(-1710000000000)], [(-7290000000000)])⟩,
      ⟨5, ([(-420000000000)], [(-6330000000000)])⟩,
      ⟨4, ([(-9000000000000)], [5505000000000])⟩,
      ⟨4, ([(-8625000000000)], [5040000000000])⟩,
      ⟨4, ([(-6000000000000)], [420000000000])⟩,
      ⟨0, ([(-1125000000000)], [5625000000000])⟩,
      ⟨0, ([(-375000000000)], [5415000000000])⟩,
      ⟨0, ([(-210000000000)], [5250000000000])⟩,
      ⟨6, ([6705000000000], [(-7125000000000)])⟩,
      ⟨6, ([6735000000000], [(-7110000000000)])⟩,
      ⟨8, ([(-15060000000000)], [6060000000000])⟩,
      ⟨3, ([(-8625000000000)], [7365000000000])⟩,
      ⟨4, ([(-5625000000000)], [585000000000])⟩,
      ⟨4, ([(-5625000000000)], [630000000000])⟩,
      ⟨5, ([(-5115000000000)], [(-3885000000000)])⟩,
      ⟨5, ([(-750000000000)], [(-4290000000000)])⟩,
      ⟨9, ([9000000000000], [(-16110000000000)])⟩,
      ⟨5, ([(-5445000000000)], [(-3555000000000)])⟩,
      ⟨4, ([(-5115000000000)], [(-1260000000000)])⟩,
      ⟨4, ([(-4665000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-1260000000000)], [5175000000000])⟩,
      ⟨0, ([(-1260000000000)], [6000000000000])⟩,
      ⟨0, ([(-795000000000)], [420000000000])⟩,
      ⟨0, ([270000000000], [6480000000000])⟩,
      ⟨9, ([3915000000000], [(-12915000000000)])⟩,
      ⟨6, ([3960000000000], [(-8250000000000)])⟩,
      ⟨6, ([4290000000000], [(-5040000000000)])⟩,
      ⟨5, ([(-5505000000000)], [(-3495000000000)])⟩,
      ⟨3, ([(-3375000000000)], [8370000000000])⟩,
      ⟨4, ([(-3150000000000)], [375000000000])⟩,
      ⟨0, ([(-810000000000)], [0])⟩,
      ⟨5, ([(-210000000000)], [(-3750000000000)])⟩,
      ⟨6, ([3660000000000], [(-8160000000000)])⟩,
      ⟨9, ([3705000000000], [(-12705000000000)])⟩,
      ⟨9, ([9000000000000], [(-14205000000000)])⟩,
      ⟨8, ([(-10620000000000)], [1620000000000])⟩,
      ⟨4, ([(-9000000000000)], [5535000000000])⟩,
      ⟨5, ([(-6000000000000)], [(-3000000000000)])⟩,
      ⟨5, ([(-3960000000000)], [(-2790000000000)])⟩,
      ⟨1, ([3000000000000], [4560000000000])⟩,
      ⟨6, ([3495000000000], [(-9000000000000)])⟩,
      ⟨6, ([3495000000000], [(-8370000000000)])⟩,
      ⟨1, ([9000000000000], [(-4320000000000)])⟩],
    last := 1 }

end ConwaySoifer.Simplified.Certificates.Data
