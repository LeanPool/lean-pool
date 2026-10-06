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
def Sint310000320000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 31 100), hi := (mkRat 8 25), den := 9000000000000,
    steps := [
      ⟨3, ([(-4440000000000)], [8625000000000])⟩,
      ⟨3, ([(-4230000000000)], [9000000000000])⟩,
      ⟨0, ([(-1395000000000)], [645000000000])⟩,
      ⟨0, ([(-1080000000000)], [0])⟩,
      ⟨0, ([(-645000000000)], [(-750000000000)])⟩,
      ⟨0, ([0], [(-1080000000000)])⟩,
      ⟨0, ([153000000000], [5022000000000])⟩,
      ⟨0, ([645000000000], [(-1395000000000)])⟩,
      ⟨0, ([750000000000], [(-1395000000000)])⟩,
      ⟨0, ([750000000000], [5022000000000])⟩,
      ⟨0, ([930000000000], [4875000000000])⟩,
      ⟨0, ([1395000000000], [(-750000000000)])⟩,
      ⟨0, ([1395000000000], [(-645000000000)])⟩,
      ⟨8, ([(-13245000000000)], [9000000000000])⟩,
      ⟨4, ([(-5022000000000)], [375000000000])⟩,
      ⟨3, ([(-4272000000000)], [8250000000000])⟩,
      ⟨5, ([0], [(-2730000000000)])⟩,
      ⟨8, ([(-14280000000000)], [5280000000000])⟩,
      ⟨4, ([(-8370000000000)], [3000000000000])⟩,
      ⟨3, ([(-8370000000000)], [6000000000000])⟩,
      ⟨4, ([(-6105000000000)], [(-2895000000000)])⟩,
      ⟨4, ([(-4290000000000)], [0])⟩,
      ⟨4, ([(-4125000000000)], [(-2850000000000)])⟩,
      ⟨4, ([(-3585000000000)], [(-2790000000000)])⟩,
      ⟨4, ([(-3000000000000)], [(-2280000000000)])⟩,
      ⟨4, ([(-2790000000000)], [(-2085000000000)])⟩,
      ⟨4, ([(-2730000000000)], [(-1395000000000)])⟩,
      ⟨6, ([2790000000000], [(-4875000000000)])⟩,
      ⟨9, ([3495000000000], [(-12495000000000)])⟩,
      ⟨6, ([4185000000000], [(-4875000000000)])⟩,
      ⟨8, ([(-10860000000000)], [6375000000000])⟩,
      ⟨8, ([(-10560000000000)], [1560000000000])⟩,
      ⟨3, ([(-9000000000000)], [6105000000000])⟩,
      ⟨3, ([(-7875000000000)], [5580000000000])⟩,
      ⟨5, ([(-4380000000000)], [(-4620000000000)])⟩,
      ⟨0, ([(-1500000000000)], [570000000000])⟩,
      ⟨0, ([105000000000], [5175000000000])⟩,
      ⟨5, ([3000000000000], [(-8022000000000)])⟩,
      ⟨9, ([9000000000000], [(-14280000000000)])⟩,
      ⟨4, ([(-9000000000000)], [3603000000000])⟩,
      ⟨5, ([0], [(-2580000000000)])⟩,
      ⟨9, ([1020000000000], [(-10020000000000)])⟩,
      ⟨6, ([2475000000000], [(-4500000000000)])⟩,
      ⟨6, ([3645000000000], [(-9000000000000)])⟩],
    last := 6 }

end ConwaySoifer.Simplified.Certificates.Data
