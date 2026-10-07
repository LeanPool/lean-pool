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
def Sext220000230000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 11 50), hi := (mkRat 23 100), den := 9000000000000,
    steps := [
      ⟨0, ([(-1080000000000)], [459000000000])⟩,
      ⟨0, ([(-1080000000000)], [540000000000])⟩,
      ⟨0, ([(-1035000000000)], [660000000000])⟩,
      ⟨0, ([(-660000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-621000000000)], [1080000000000])⟩,
      ⟨0, ([(-540000000000)], [1080000000000])⟩,
      ⟨0, ([(-375000000000)], [1035000000000])⟩,
      ⟨0, ([459000000000], [621000000000])⟩,
      ⟨0, ([540000000000], [540000000000])⟩,
      ⟨0, ([5940000000000], [(-5625000000000)])⟩,
      ⟨0, ([6030000000000], [(-5655000000000)])⟩,
      ⟨0, ([6285000000000], [(-5625000000000)])⟩,
      ⟨9, ([8250000000000], [(-10230000000000)])⟩,
      ⟨9, ([9000000000000], [(-10314000000000)])⟩,
      ⟨5, ([5061000000000], [(-8625000000000)])⟩,
      ⟨5, ([5730000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-4590000000000)], [(-4410000000000)])⟩,
      ⟨4, ([(-4050000000000)], [(-900000000000)])⟩,
      ⟨4, ([(-4050000000000)], [(-450000000000)])⟩,
      ⟨8, ([(-13065000000000)], [4065000000000])⟩,
      ⟨3, ([(-8250000000000)], [4050000000000])⟩,
      ⟨3, ([(-4950000000000)], [4500000000000])⟩,
      ⟨3, ([(-4785000000000)], [4125000000000])⟩,
      ⟨5, ([(-1740000000000)], [(-6360000000000)])⟩,
      ⟨8, ([(-13920000000000)], [9000000000000])⟩,
      ⟨4, ([(-4050000000000)], [(-75000000000)])⟩,
      ⟨2, ([(-4050000000000)], [9000000000000])⟩,
      ⟨2, ([(-375000000000)], [5325000000000])⟩,
      ⟨0, ([3000000000000], [(-4320000000000)])⟩,
      ⟨0, ([3375000000000], [(-4695000000000)])⟩,
      ⟨3, ([(-9000000000000)], [4095000000000])⟩,
      ⟨3, ([(-8625000000000)], [4050000000000])⟩,
      ⟨4, ([(-3564000000000)], [(-186000000000)])⟩,
      ⟨7, ([4950000000000], [9000000000000])⟩,
      ⟨1, ([5175000000000], [2970000000000])⟩,
      ⟨1, ([5190000000000], [3060000000000])⟩,
      ⟨8, ([(-12960000000000)], [3960000000000])⟩,
      ⟨8, ([(-11115000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [3855000000000])⟩,
      ⟨3, ([(-7500000000000)], [3564000000000])⟩,
      ⟨3, ([(-5064000000000)], [3564000000000])⟩,
      ⟨2, ([(-4950000000000)], [9000000000000])⟩,
      ⟨3, ([(-4050000000000)], [3675000000000])⟩,
      ⟨3, ([(-3960000000000)], [3750000000000])⟩,
      ⟨2, ([(-660000000000)], [4875000000000])⟩,
      ⟨0, ([6375000000000], [(-5436000000000)])⟩,
      ⟨0, ([6375000000000], [(-5295000000000)])⟩,
      ⟨4, ([(-6375000000000)], [1980000000000])⟩,
      ⟨2, ([(-5436000000000)], [9000000000000])⟩,
      ⟨3, ([(-4875000000000)], [6855000000000])⟩,
      ⟨4, ([(-3390000000000)], [750000000000])⟩,
      ⟨4, ([(-2385000000000)], [0])⟩,
      ⟨3, ([(-2265000000000)], [2265000000000])⟩,
      ⟨5, ([(-1920000000000)], [(-6000000000000)])⟩,
      ⟨2, ([(-1311000000000)], [4875000000000])⟩,
      ⟨2, ([(-375000000000)], [4335000000000])⟩,
      ⟨7, ([4050000000000], [9000000000000])⟩,
      ⟨8, ([(-11814000000000)], [2814000000000])⟩,
      ⟨8, ([(-10140000000000)], [7500000000000])⟩,
      ⟨3, ([(-9000000000000)], [3540000000000])⟩,
      ⟨2, ([(-5985000000000)], [9000000000000])⟩,
      ⟨3, ([(-4500000000000)], [6480000000000])⟩,
      ⟨4, ([(-3855000000000)], [1980000000000])⟩,
      ⟨0, ([(-1500000000000)], [990000000000])⟩,
      ⟨0, ([(-990000000000)], [(-375000000000)])⟩,
      ⟨1, ([3564000000000], [4686000000000])⟩,
      ⟨5, ([4875000000000], [(-6855000000000)])⟩,
      ⟨0, ([6015000000000], [(-6015000000000)])⟩,
      ⟨0, ([6825000000000], [(-4950000000000)])⟩,
      ⟨0, ([(-1980000000000)], [(-5175000000000)])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
