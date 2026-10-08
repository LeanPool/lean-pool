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
def Sint250000260000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 1 4), hi := (mkRat 13 50), den := 9000000000000,
    steps := [
      ⟨3, ([(-3675000000000)], [9000000000000])⟩,
      ⟨0, ([(-1125000000000)], [375000000000])⟩,
      ⟨0, ([(-1125000000000)], [750000000000])⟩,
      ⟨0, ([(-750000000000)], [(-375000000000)])⟩,
      ⟨0, ([375000000000], [(-1125000000000)])⟩,
      ⟨0, ([375000000000], [5250000000000])⟩,
      ⟨0, ([750000000000], [5250000000000])⟩,
      ⟨0, ([1125000000000], [(-750000000000)])⟩,
      ⟨8, ([(-13050000000000)], [7425000000000])⟩,
      ⟨8, ([(-12675000000000)], [9000000000000])⟩,
      ⟨4, ([(-8250000000000)], [3075000000000])⟩,
      ⟨4, ([(-5625000000000)], [1125000000000])⟩,
      ⟨4, ([(-5175000000000)], [750000000000])⟩,
      ⟨4, ([(-4950000000000)], [495000000000])⟩,
      ⟨3, ([(-3675000000000)], [8625000000000])⟩,
      ⟨8, ([(-14625000000000)], [5625000000000])⟩,
      ⟨8, ([(-11250000000000)], [7500000000000])⟩,
      ⟨5, ([(-300000000000)], [(-4950000000000)])⟩,
      ⟨4, ([(-9000000000000)], [4050000000000])⟩,
      ⟨5, ([(-3075000000000)], [(-5925000000000)])⟩,
      ⟨6, ([5250000000000], [(-5625000000000)])⟩,
      ⟨5, ([(-3825000000000)], [(-5175000000000)])⟩,
      ⟨5, ([(-375000000000)], [(-4575000000000)])⟩,
      ⟨9, ([9000000000000], [(-14850000000000)])⟩,
      ⟨9, ([4875000000000], [(-13875000000000)])⟩,
      ⟨6, ([4950000000000], [(-5250000000000)])⟩,
      ⟨6, ([5175000000000], [(-8550000000000)])⟩,
      ⟨1, ([9000000000000], [(-3075000000000)])⟩,
      ⟨0, ([1125000000000], [5175000000000])⟩,
      ⟨0, ([1425000000000], [4950000000000])⟩,
      ⟨4, ([(-4500000000000)], [450000000000])⟩,
      ⟨5, ([0], [(-2550000000000)])⟩,
      ⟨5, ([(-4050000000000)], [(-4950000000000)])⟩,
      ⟨4, ([(-3750000000000)], [(-2250000000000)])⟩,
      ⟨4, ([(-3600000000000)], [0])⟩,
      ⟨4, ([(-2250000000000)], [(-1500000000000)])⟩,
      ⟨6, ([2587500000000], [(-4500000000000)])⟩,
      ⟨6, ([3750000000000], [(-8250000000000)])⟩,
      ⟨9, ([4050000000000], [(-13050000000000)])⟩,
      ⟨6, ([4125000000000], [(-4500000000000)])⟩,
      ⟨3, ([(-7875000000000)], [6000000000000])⟩,
      ⟨5, ([(-4875000000000)], [(-4125000000000)])⟩,
      ⟨0, ([(-1800000000000)], [0])⟩,
      ⟨5, ([1875000000000], [(-6375000000000)])⟩,
      ⟨6, ([3000000000000], [(-7500000000000)])⟩,
      ⟨6, ([3375000000000], [(-8625000000000)])⟩,
      ⟨1, ([7125000000000], [(-4500000000000)])⟩,
      ⟨1, ([9000000000000], [(-5175000000000)])⟩,
      ⟨0, ([(-750000000000)], [3750000000000])⟩,
      ⟨0, ([225000000000], [(-1125000000000)])⟩,
      ⟨0, ([3375000000000], [3000000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
