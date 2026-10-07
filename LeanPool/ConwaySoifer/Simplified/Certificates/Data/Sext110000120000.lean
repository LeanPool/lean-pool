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
def Sext110000120000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 11 100), hi := (mkRat 3 25), den := 9000000000000,
    steps := [
      ⟨0, ([0], [468000000000])⟩,
      ⟨0, ([990000000000], [(-990000000000)])⟩,
      ⟨9, ([9000000000000], [(-9600000000000)])⟩,
      ⟨5, ([7125000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-6345000000000)], [(-2655000000000)])⟩,
      ⟨0, ([4500000000000], [(-5490000000000)])⟩,
      ⟨0, ([5010000000000], [(-6000000000000)])⟩,
      ⟨0, ([5250000000000], [(-5940000000000)])⟩,
      ⟨0, ([5295000000000], [(-5625000000000)])⟩,
      ⟨8, ([(-15420000000000)], [6420000000000])⟩,
      ⟨3, ([(-8340000000000)], [7215000000000])⟩,
      ⟨3, ([(-7218000000000)], [6750000000000])⟩,
      ⟨4, ([(-5190000000000)], [(-750000000000)])⟩,
      ⟨4, ([(-4875000000000)], [(-990000000000)])⟩,
      ⟨4, ([(-3000000000000)], [(-6000000000000)])⟩,
      ⟨8, ([(-16218000000000)], [9000000000000])⟩,
      ⟨8, ([(-12045000000000)], [3045000000000])⟩,
      ⟨3, ([(-7920000000000)], [3750000000000])⟩,
      ⟨3, ([(-4860000000000)], [3960000000000])⟩,
      ⟨3, ([(-4740000000000)], [3750000000000])⟩,
      ⟨5, ([(-990000000000)], [(-7635000000000)])⟩,
      ⟨8, ([(-13920000000000)], [9000000000000])⟩,
      ⟨3, ([(-8340000000000)], [3465000000000])⟩,
      ⟨4, ([(-4740000000000)], [0])⟩,
      ⟨2, ([(-765000000000)], [5940000000000])⟩,
      ⟨0, ([4125000000000], [(-5115000000000)])⟩,
      ⟨0, ([5385000000000], [(-6375000000000)])⟩,
      ⟨0, ([6045000000000], [(-6375000000000)])⟩,
      ⟨8, ([(-12045000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [3000000000000])⟩,
      ⟨2, ([(-5280000000000)], [9000000000000])⟩,
      ⟨3, ([(-4500000000000)], [4005000000000])⟩,
      ⟨3, ([(-4410000000000)], [3750000000000])⟩,
      ⟨4, ([(-4125000000000)], [0])⟩,
      ⟨2, ([(-990000000000)], [5490000000000])⟩,
      ⟨8, ([(-11460000000000)], [9000000000000])⟩,
      ⟨3, ([(-8340000000000)], [3000000000000])⟩,
      ⟨2, ([(-6000000000000)], [9000000000000])⟩,
      ⟨2, ([(-4920000000000)], [7920000000000])⟩,
      ⟨3, ([(-4335000000000)], [3960000000000])⟩,
      ⟨3, ([(-4125000000000)], [3630000000000])⟩,
      ⟨4, ([(-3870000000000)], [495000000000])⟩,
      ⟨2, ([(-990000000000)], [4740000000000])⟩,
      ⟨2, ([(-900000000000)], [4860000000000])⟩,
      ⟨1, ([4125000000000], [3390000000000])⟩,
      ⟨0, ([7218000000000], [(-6843000000000)])⟩,
      ⟨3, ([(-8010000000000)], [3000000000000])⟩,
      ⟨3, ([(-5010000000000)], [6000000000000])⟩,
      ⟨4, ([(-4740000000000)], [990000000000])⟩,
      ⟨2, ([(-4515000000000)], [7515000000000])⟩,
      ⟨3, ([(-3360000000000)], [3360000000000])⟩,
      ⟨2, ([(-1080000000000)], [4500000000000])⟩,
      ⟨0, ([(-810000000000)], [0])⟩,
      ⟨1, ([3000000000000], [3960000000000])⟩,
      ⟨0, ([7680000000000], [(-5430000000000)])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
