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
def Sext130000140000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 13 100), hi := (mkRat 7 50), den := 9000000000000,
    steps := [
      ⟨0, ([0], [540000000000])⟩,
      ⟨0, ([375000000000], [360000000000])⟩,
      ⟨0, ([1170000000000], [(-1170000000000)])⟩,
      ⟨9, ([9000000000000], [(-9735000000000)])⟩,
      ⟨5, ([6840000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-5880000000000)], [(-3120000000000)])⟩,
      ⟨0, ([4365000000000], [(-5490000000000)])⟩,
      ⟨0, ([4875000000000], [(-5265000000000)])⟩,
      ⟨0, ([4875000000000], [(-5235000000000)])⟩,
      ⟨8, ([(-14895000000000)], [5895000000000])⟩,
      ⟨3, ([(-8250000000000)], [6894000000000])⟩,
      ⟨3, ([(-6894000000000)], [6375000000000])⟩,
      ⟨4, ([(-5175000000000)], [(-780000000000)])⟩,
      ⟨4, ([(-3510000000000)], [(-5115000000000)])⟩,
      ⟨4, ([(-3360000000000)], [(-5640000000000)])⟩,
      ⟨8, ([(-15894000000000)], [9000000000000])⟩,
      ⟨8, ([(-12360000000000)], [3360000000000])⟩,
      ⟨3, ([(-7875000000000)], [4320000000000])⟩,
      ⟨3, ([(-4875000000000)], [4095000000000])⟩,
      ⟨5, ([(-1170000000000)], [(-7455000000000)])⟩,
      ⟨8, ([(-14490000000000)], [9000000000000])⟩,
      ⟨3, ([(-8220000000000)], [4095000000000])⟩,
      ⟨4, ([(-5175000000000)], [0])⟩,
      ⟨2, ([(-3255000000000)], [9000000000000])⟩,
      ⟨2, ([(-585000000000)], [6375000000000])⟩,
      ⟨0, ([(-360000000000)], [735000000000])⟩,
      ⟨0, ([4005000000000], [(-5175000000000)])⟩,
      ⟨0, ([4875000000000], [(-6045000000000)])⟩,
      ⟨0, ([5490000000000], [(-5625000000000)])⟩,
      ⟨8, ([(-14145000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [3405000000000])⟩,
      ⟨4, ([(-4875000000000)], [0])⟩,
      ⟨3, ([(-4710000000000)], [4125000000000])⟩,
      ⟨2, ([(-780000000000)], [5955000000000])⟩,
      ⟨8, ([(-11760000000000)], [8250000000000])⟩,
      ⟨3, ([(-9000000000000)], [3360000000000])⟩,
      ⟨2, ([(-5595000000000)], [9000000000000])⟩,
      ⟨3, ([(-4500000000000)], [3915000000000])⟩,
      ⟨2, ([(-1170000000000)], [5175000000000])⟩,
      ⟨2, ([(-780000000000)], [4875000000000])⟩,
      ⟨7, ([5145000000000], [9000000000000])⟩,
      ⟨1, ([5490000000000], [2385000000000])⟩,
      ⟨0, ([7020000000000], [(-6645000000000)])⟩,
      ⟨3, ([(-5955000000000)], [7125000000000])⟩,
      ⟨2, ([(-5640000000000)], [9000000000000])⟩,
      ⟨4, ([(-5625000000000)], [1170000000000])⟩,
      ⟨2, ([(-5250000000000)], [8610000000000])⟩,
      ⟨3, ([(-3540000000000)], [3540000000000])⟩,
      ⟨2, ([(-1560000000000)], [5310000000000])⟩,
      ⟨0, ([(-825000000000)], [0])⟩,
      ⟨1, ([3510000000000], [3990000000000])⟩,
      ⟨7, ([3510000000000], [9000000000000])⟩,
      ⟨1, ([7680000000000], [(-4680000000000)])⟩,
      ⟨0, ([3375000000000], [4680000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
