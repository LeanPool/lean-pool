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
def Sext120000130000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 3 25), hi := (mkRat 13 100), den := 9000000000000,
    steps := [
      ⟨0, ([1080000000000], [(-1080000000000)])⟩,
      ⟨9, ([9000000000000], [(-9660000000000)])⟩,
      ⟨5, ([6990000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-6120000000000)], [(-2880000000000)])⟩,
      ⟨0, ([4500000000000], [(-5580000000000)])⟩,
      ⟨0, ([5085000000000], [(-5625000000000)])⟩,
      ⟨0, ([5175000000000], [(-5535000000000)])⟩,
      ⟨8, ([(-15480000000000)], [6750000000000])⟩,
      ⟨3, ([(-8250000000000)], [7056000000000])⟩,
      ⟨3, ([(-7125000000000)], [6585000000000])⟩,
      ⟨4, ([(-5010000000000)], [(-750000000000)])⟩,
      ⟨4, ([(-3240000000000)], [(-5625000000000)])⟩,
      ⟨4, ([(-3165000000000)], [(-5835000000000)])⟩,
      ⟨8, ([(-16140000000000)], [9000000000000])⟩,
      ⟨8, ([(-12240000000000)], [3375000000000])⟩,
      ⟨8, ([(-12195000000000)], [3195000000000])⟩,
      ⟨3, ([(-7920000000000)], [3960000000000])⟩,
      ⟨3, ([(-5175000000000)], [4095000000000])⟩,
      ⟨3, ([(-5175000000000)], [4320000000000])⟩,
      ⟨5, ([(-1080000000000)], [(-7500000000000)])⟩,
      ⟨8, ([(-14625000000000)], [9000000000000])⟩,
      ⟨3, ([(-8280000000000)], [3750000000000])⟩,
      ⟨4, ([(-5175000000000)], [0])⟩,
      ⟨2, ([(-3600000000000)], [9000000000000])⟩,
      ⟨2, ([(-750000000000)], [6300000000000])⟩,
      ⟨2, ([(-675000000000)], [6300000000000])⟩,
      ⟨0, ([4095000000000], [(-5175000000000)])⟩,
      ⟨0, ([5295000000000], [(-6375000000000)])⟩,
      ⟨0, ([6000000000000], [(-6300000000000)])⟩,
      ⟨8, ([(-14265000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [3180000000000])⟩,
      ⟨3, ([(-7056000000000)], [7875000000000])⟩,
      ⟨3, ([(-4680000000000)], [4125000000000])⟩,
      ⟨2, ([(-4335000000000)], [9000000000000])⟩,
      ⟨4, ([(-4125000000000)], [(-195000000000)])⟩,
      ⟨2, ([(-750000000000)], [5760000000000])⟩,
      ⟨7, ([5580000000000], [9000000000000])⟩,
      ⟨1, ([6000000000000], [1920000000000])⟩,
      ⟨8, ([(-11445000000000)], [7125000000000])⟩,
      ⟨3, ([(-9000000000000)], [3165000000000])⟩,
      ⟨2, ([(-5820000000000)], [9000000000000])⟩,
      ⟨3, ([(-4290000000000)], [3750000000000])⟩,
      ⟨2, ([(-1620000000000)], [5175000000000])⟩,
      ⟨2, ([(-930000000000)], [4680000000000])⟩,
      ⟨7, ([4680000000000], [9000000000000])⟩,
      ⟨1, ([5175000000000], [2700000000000])⟩,
      ⟨0, ([7125000000000], [(-6840000000000)])⟩,
      ⟨2, ([(-5835000000000)], [9000000000000])⟩,
      ⟨3, ([(-5250000000000)], [6330000000000])⟩,
      ⟨4, ([(-5205000000000)], [1080000000000])⟩,
      ⟨0, ([(-825000000000)], [0])⟩,
      ⟨1, ([3195000000000], [4680000000000])⟩,
      ⟨0, ([7500000000000], [(-5340000000000)])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
