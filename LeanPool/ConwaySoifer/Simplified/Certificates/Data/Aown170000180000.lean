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
def Aown170000180000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 17 100), hi := (mkRat 9 50), den := 9000000000000,
    steps := [
      ⟨0, ([(-885000000000)], [375000000000])⟩,
      ⟨0, ([(-885000000000)], [510000000000])⟩,
      ⟨0, ([(-510000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-510000000000)], [885000000000])⟩,
      ⟨0, ([(-375000000000)], [(-510000000000)])⟩,
      ⟨0, ([375000000000], [(-885000000000)])⟩,
      ⟨0, ([510000000000], [(-885000000000)])⟩,
      ⟨0, ([1530000000000], [0])⟩,
      ⟨2, ([3240000000000], [5760000000000])⟩,
      ⟨2, ([6990000000000], [1500000000000])⟩,
      ⟨6, ([9000000000000], [(-5760000000000)])⟩,
      ⟨1, ([9000000000000], [4740000000000])⟩,
      ⟨7, ([9000000000000], [6705000000000])⟩,
      ⟨3, ([(-3240000000000)], [8865000000000])⟩,
      ⟨3, ([(-3000000000000)], [9000000000000])⟩,
      ⟨0, ([0], [1530000000000])⟩,
      ⟨5, ([1485000000000], [(-8235000000000)])⟩,
      ⟨0, ([2880000000000], [1620000000000])⟩,
      ⟨2, ([4860000000000], [4140000000000])⟩,
      ⟨0, ([4875000000000], [1530000000000])⟩,
      ⟨2, ([5871000000000], [3129000000000])⟩,
      ⟨0, ([6000000000000], [510000000000])⟩,
      ⟨0, ([6120000000000], [375000000000])⟩,
      ⟨2, ([7110000000000], [1125000000000])⟩,
      ⟨2, ([7125000000000], [1365000000000])⟩,
      ⟨9, ([8250000000000], [(-15120000000000)])⟩,
      ⟨6, ([9000000000000], [(-3240000000000)])⟩,
      ⟨8, ([(-12060000000000)], [9000000000000])⟩,
      ⟨4, ([(-8100000000000)], [3690000000000])⟩,
      ⟨4, ([(-3825000000000)], [375000000000])⟩,
      ⟨3, ([(-3825000000000)], [4500000000000])⟩,
      ⟨3, ([(-2610000000000)], [9000000000000])⟩,
      ⟨0, ([375000000000], [6120000000000])⟩,
      ⟨0, ([390000000000], [(-900000000000)])⟩,
      ⟨5, ([585000000000], [(-4410000000000)])⟩,
      ⟨0, ([2535000000000], [4590000000000])⟩,
      ⟨0, ([2880000000000], [4245000000000])⟩,
      ⟨5, ([3240000000000], [(-8115000000000)])⟩,
      ⟨0, ([6120000000000], [750000000000])⟩,
      ⟨0, ([6375000000000], [330000000000])⟩,
      ⟨2, ([6855000000000], [1125000000000])⟩,
      ⟨8, ([(-12870000000000)], [3870000000000])⟩,
      ⟨8, ([(-11685000000000)], [9000000000000])⟩,
      ⟨4, ([(-8379000000000)], [5625000000000])⟩,
      ⟨4, ([(-5835000000000)], [(-3165000000000)])⟩,
      ⟨3, ([(-5175000000000)], [4125000000000])⟩,
      ⟨3, ([(-2460000000000)], [9000000000000])⟩,
      ⟨3, ([(-1125000000000)], [765000000000])⟩,
      ⟨3, ([(-1020000000000)], [1125000000000])⟩],
    last := 3 }

end ConwaySoifer.Simplified.Certificates.Data
