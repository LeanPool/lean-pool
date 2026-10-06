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
def Sext230000240000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 23 100), hi := (mkRat 6 25), den := 9000000000000,
    steps := [
      ⟨0, ([(-1065000000000)], [375000000000])⟩,
      ⟨0, ([(-1065000000000)], [690000000000])⟩,
      ⟨0, ([(-1035000000000)], [285000000000])⟩,
      ⟨0, ([(-1035000000000)], [750000000000])⟩,
      ⟨0, ([(-900000000000)], [0])⟩,
      ⟨0, ([(-750000000000)], [1035000000000])⟩,
      ⟨0, ([(-690000000000)], [1065000000000])⟩,
      ⟨0, ([(-375000000000)], [1065000000000])⟩,
      ⟨0, ([0], [900000000000])⟩,
      ⟨0, ([375000000000], [690000000000])⟩,
      ⟨0, ([690000000000], [435000000000])⟩,
      ⟨0, ([5895000000000], [(-5625000000000)])⟩,
      ⟨0, ([6240000000000], [(-5490000000000)])⟩,
      ⟨9, ([8280000000000], [(-10155000000000)])⟩,
      ⟨9, ([9000000000000], [(-10320000000000)])⟩,
      ⟨5, ([5175000000000], [(-8625000000000)])⟩,
      ⟨5, ([5640000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-4635000000000)], [(-4365000000000)])⟩,
      ⟨4, ([(-4140000000000)], [(-360000000000)])⟩,
      ⟨4, ([(-4125000000000)], [(-1035000000000)])⟩,
      ⟨8, ([(-13140000000000)], [4140000000000])⟩,
      ⟨3, ([(-8310000000000)], [4125000000000])⟩,
      ⟨3, ([(-5175000000000)], [4275000000000])⟩,
      ⟨3, ([(-4860000000000)], [4374000000000])⟩,
      ⟨5, ([(-1905000000000)], [(-6375000000000)])⟩,
      ⟨0, ([(-690000000000)], [(-435000000000)])⟩,
      ⟨8, ([(-14085000000000)], [9000000000000])⟩,
      ⟨2, ([(-4035000000000)], [9000000000000])⟩,
      ⟨2, ([(-375000000000)], [5274000000000])⟩,
      ⟨0, ([3105000000000], [(-4500000000000)])⟩,
      ⟨9, ([6405000000000], [(-15405000000000)])⟩,
      ⟨3, ([(-8901000000000)], [5175000000000])⟩,
      ⟨3, ([(-6405000000000)], [8280000000000])⟩,
      ⟨4, ([(-3726000000000)], [(-399000000000)])⟩,
      ⟨3, ([(-2385000000000)], [2385000000000])⟩,
      ⟨0, ([(-435000000000)], [1125000000000])⟩,
      ⟨7, ([4905000000000], [9000000000000])⟩,
      ⟨1, ([5145000000000], [3105000000000])⟩,
      ⟨8, ([(-12960000000000)], [3960000000000])⟩,
      ⟨8, ([(-10800000000000)], [9000000000000])⟩,
      ⟨3, ([(-8310000000000)], [3810000000000])⟩,
      ⟨4, ([(-5820000000000)], [2070000000000])⟩,
      ⟨4, ([(-3000000000000)], [1035000000000])⟩,
      ⟨2, ([(-2760000000000)], [5175000000000])⟩,
      ⟨5, ([4500000000000], [(-8226000000000)])⟩,
      ⟨0, ([6375000000000], [(-5340000000000)])⟩,
      ⟨8, ([(-12795000000000)], [3795000000000])⟩,
      ⟨8, ([(-10380000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [3810000000000])⟩,
      ⟨2, ([(-5880000000000)], [9000000000000])⟩,
      ⟨4, ([(-4560000000000)], [(-4440000000000)])⟩,
      ⟨4, ([(-2760000000000)], [1125000000000])⟩,
      ⟨5, ([(-2070000000000)], [(-6000000000000)])⟩,
      ⟨0, ([(-1860000000000)], [0])⟩,
      ⟨1, ([2415000000000], [6210000000000])⟩,
      ⟨1, ([2460000000000], [3750000000000])⟩,
      ⟨0, ([3105000000000], [(-4875000000000)])⟩,
      ⟨0, ([4860000000000], [(-2985000000000)])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
