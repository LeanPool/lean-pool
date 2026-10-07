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
def Sint220000230000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 11 50), hi := (mkRat 23 100), den := 9000000000000,
    steps := [
      ⟨3, ([(-3270000000000)], [9000000000000])⟩,
      ⟨0, ([(-1080000000000)], [459000000000])⟩,
      ⟨0, ([(-459000000000)], [(-621000000000)])⟩,
      ⟨0, ([315000000000], [5625000000000])⟩,
      ⟨0, ([540000000000], [(-1080000000000)])⟩,
      ⟨0, ([621000000000], [(-1080000000000)])⟩,
      ⟨0, ([660000000000], [5625000000000])⟩,
      ⟨0, ([1080000000000], [(-540000000000)])⟩,
      ⟨8, ([(-12315000000000)], [9000000000000])⟩,
      ⟨4, ([(-8250000000000)], [3564000000000])⟩,
      ⟨4, ([(-4950000000000)], [900000000000])⟩,
      ⟨4, ([(-4500000000000)], [450000000000])⟩,
      ⟨3, ([(-3564000000000)], [8625000000000])⟩,
      ⟨8, ([(-13815000000000)], [4815000000000])⟩,
      ⟨5, ([(-3480000000000)], [(-5520000000000)])⟩,
      ⟨5, ([(-375000000000)], [(-4950000000000)])⟩,
      ⟨4, ([(-9000000000000)], [4410000000000])⟩,
      ⟨6, ([5175000000000], [(-5835000000000)])⟩,
      ⟨5, ([(-4410000000000)], [(-4590000000000)])⟩,
      ⟨5, ([(-4200000000000)], [(-4050000000000)])⟩,
      ⟨5, ([(-660000000000)], [(-4125000000000)])⟩,
      ⟨9, ([9000000000000], [(-15030000000000)])⟩,
      ⟨4, ([(-4950000000000)], [(-1800000000000)])⟩,
      ⟨4, ([(-4125000000000)], [75000000000])⟩,
      ⟨9, ([4050000000000], [(-13050000000000)])⟩,
      ⟨6, ([4290000000000], [(-5040000000000)])⟩,
      ⟨6, ([4500000000000], [(-4950000000000)])⟩,
      ⟨6, ([4665000000000], [(-8625000000000)])⟩,
      ⟨5, ([(-4905000000000)], [(-4095000000000)])⟩,
      ⟨0, ([(-1080000000000)], [108000000000])⟩,
      ⟨0, ([(-1020000000000)], [0])⟩,
      ⟨0, ([(-660000000000)], [(-465000000000)])⟩,
      ⟨5, ([0], [(-4950000000000)])⟩,
      ⟨1, ([9000000000000], [(-3840000000000)])⟩,
      ⟨4, ([(-4770000000000)], [(-1980000000000)])⟩,
      ⟨3, ([(-2880000000000)], [7380000000000])⟩,
      ⟨0, ([1875000000000], [4950000000000])⟩,
      ⟨0, ([1980000000000], [4770000000000])⟩,
      ⟨8, ([(-11880000000000)], [9000000000000])⟩,
      ⟨8, ([(-11070000000000)], [2070000000000])⟩,
      ⟨4, ([(-9000000000000)], [5115000000000])⟩,
      ⟨3, ([(-5175000000000)], [3195000000000])⟩,
      ⟨3, ([(-1320000000000)], [6570000000000])⟩],
    last := 3 }

end ConwaySoifer.Simplified.Certificates.Data
