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
def Sext190000200000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 19 100), hi := (mkRat 1 5), den := 9000000000000,
    steps := [
      ⟨0, ([(-945000000000)], [375000000000])⟩,
      ⟨0, ([(-945000000000)], [570000000000])⟩,
      ⟨0, ([(-765000000000)], [765000000000])⟩,
      ⟨0, ([(-570000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-570000000000)], [945000000000])⟩,
      ⟨0, ([(-375000000000)], [945000000000])⟩,
      ⟨0, ([375000000000], [570000000000])⟩,
      ⟨0, ([6375000000000], [(-5805000000000)])⟩,
      ⟨0, ([6435000000000], [(-6060000000000)])⟩,
      ⟨9, ([8625000000000], [(-10140000000000)])⟩,
      ⟨9, ([9000000000000], [(-10065000000000)])⟩,
      ⟨5, ([4725000000000], [(-8100000000000)])⟩,
      ⟨5, ([6105000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-3960000000000)], [(-5040000000000)])⟩,
      ⟨4, ([(-3930000000000)], [(-570000000000)])⟩,
      ⟨4, ([(-3870000000000)], [(-1380000000000)])⟩,
      ⟨8, ([(-12870000000000)], [3870000000000])⟩,
      ⟨3, ([(-8145000000000)], [4020000000000])⟩,
      ⟨3, ([(-5625000000000)], [3870000000000])⟩,
      ⟨3, ([(-4500000000000)], [3930000000000])⟩,
      ⟨5, ([(-1710000000000)], [(-6750000000000)])⟩,
      ⟨8, ([(-13590000000000)], [9000000000000])⟩,
      ⟨3, ([(-8250000000000)], [3870000000000])⟩,
      ⟨2, ([(-4065000000000)], [9000000000000])⟩,
      ⟨4, ([(-3855000000000)], [0])⟩,
      ⟨2, ([(-558000000000)], [5580000000000])⟩,
      ⟨0, ([3465000000000], [(-5175000000000)])⟩,
      ⟨3, ([(-9000000000000)], [3870000000000])⟩,
      ⟨3, ([(-6720000000000)], [8250000000000])⟩,
      ⟨3, ([(-4500000000000)], [3870000000000])⟩,
      ⟨2, ([(-4350000000000)], [9000000000000])⟩,
      ⟨3, ([(-4275000000000)], [3900000000000])⟩,
      ⟨2, ([(-4072500000000)], [8145000000000])⟩,
      ⟨4, ([(-3000000000000)], [(-78000000000)])⟩,
      ⟨5, ([(-1710000000000)], [(-6540000000000)])⟩,
      ⟨1, ([5172000000000], [750000000000])⟩,
      ⟨8, ([(-12375000000000)], [3375000000000])⟩,
      ⟨8, ([(-11280000000000)], [8100000000000])⟩,
      ⟨3, ([(-9000000000000)], [3330000000000])⟩,
      ⟨3, ([(-7875000000000)], [3150000000000])⟩,
      ⟨4, ([(-6000000000000)], [1710000000000])⟩,
      ⟨2, ([(-5130000000000)], [9000000000000])⟩,
      ⟨3, ([(-3420000000000)], [3000000000000])⟩,
      ⟨4, ([(-2295000000000)], [0])⟩,
      ⟨2, ([(-630000000000)], [4500000000000])⟩,
      ⟨0, ([3165000000000], [(-4875000000000)])⟩,
      ⟨0, ([3915000000000], [(-5625000000000)])⟩,
      ⟨7, ([4170000000000], [8250000000000])⟩,
      ⟨1, ([4770000000000], [855000000000])⟩,
      ⟨1, ([5130000000000], [3000000000000])⟩,
      ⟨0, ([6720000000000], [(-5595000000000)])⟩,
      ⟨7, ([9000000000000], [6180000000000])⟩,
      ⟨8, ([(-12045000000000)], [3045000000000])⟩,
      ⟨8, ([(-10440000000000)], [7875000000000])⟩,
      ⟨3, ([(-9000000000000)], [3078000000000])⟩,
      ⟨3, ([(-6750000000000)], [2565000000000])⟩,
      ⟨3, ([(-6000000000000)], [7710000000000])⟩,
      ⟨2, ([(-6000000000000)], [9000000000000])⟩,
      ⟨4, ([(-5835000000000)], [1710000000000])⟩,
      ⟨0, ([(-1080000000000)], [0])⟩,
      ⟨2, ([(-570000000000)], [3570000000000])⟩,
      ⟨1, ([3870000000000], [4755000000000])⟩,
      ⟨1, ([3900000000000], [375000000000])⟩,
      ⟨0, ([6435000000000], [(-3825000000000)])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
