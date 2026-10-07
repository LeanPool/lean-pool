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
def Sint230000240000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 23 100), hi := (mkRat 6 25), den := 9000000000000,
    steps := [
      ⟨3, ([(-3360000000000)], [9000000000000])⟩,
      ⟨0, ([(-1065000000000)], [375000000000])⟩,
      ⟨0, ([(-1065000000000)], [690000000000])⟩,
      ⟨0, ([(-900000000000)], [0])⟩,
      ⟨0, ([0], [(-900000000000)])⟩,
      ⟨0, ([270000000000], [5625000000000])⟩,
      ⟨0, ([375000000000], [(-1065000000000)])⟩,
      ⟨0, ([690000000000], [(-1065000000000)])⟩,
      ⟨0, ([750000000000], [(-1035000000000)])⟩,
      ⟨0, ([750000000000], [5490000000000])⟩,
      ⟨0, ([1035000000000], [(-750000000000)])⟩,
      ⟨0, ([1125000000000], [(-435000000000)])⟩,
      ⟨8, ([(-12375000000000)], [9000000000000])⟩,
      ⟨4, ([(-8295000000000)], [3420000000000])⟩,
      ⟨4, ([(-5160000000000)], [1035000000000])⟩,
      ⟨4, ([(-4860000000000)], [750000000000])⟩,
      ⟨4, ([(-4500000000000)], [360000000000])⟩,
      ⟨3, ([(-3450000000000)], [8625000000000])⟩,
      ⟨8, ([(-13860000000000)], [4860000000000])⟩,
      ⟨5, ([(-3315000000000)], [(-5685000000000)])⟩,
      ⟨0, ([(-1125000000000)], [435000000000])⟩,
      ⟨5, ([(-375000000000)], [(-4800000000000)])⟩,
      ⟨4, ([(-9000000000000)], [4374000000000])⟩,
      ⟨9, ([4860000000000], [(-13860000000000)])⟩,
      ⟨6, ([5175000000000], [(-5550000000000)])⟩,
      ⟨6, ([5625000000000], [(-8280000000000)])⟩,
      ⟨8, ([(-13530000000000)], [4530000000000])⟩,
      ⟨3, ([(-8280000000000)], [6375000000000])⟩,
      ⟨5, ([(-4374000000000)], [(-4626000000000)])⟩,
      ⟨5, ([(-4185000000000)], [(-4125000000000)])⟩,
      ⟨5, ([0], [(-2385000000000)])⟩,
      ⟨0, ([690000000000], [(-1125000000000)])⟩,
      ⟨9, ([9000000000000], [(-14835000000000)])⟩,
      ⟨4, ([(-3930000000000)], [0])⟩,
      ⟨4, ([(-3750000000000)], [(-2070000000000)])⟩,
      ⟨3, ([(-3726000000000)], [8226000000000])⟩,
      ⟨4, ([(-2370000000000)], [(-1380000000000)])⟩,
      ⟨0, ([(-1395000000000)], [4500000000000])⟩,
      ⟨6, ([2385000000000], [(-5175000000000)])⟩,
      ⟨6, ([2520000000000], [(-5895000000000)])⟩,
      ⟨6, ([2625000000000], [(-4140000000000)])⟩,
      ⟨9, ([3351000000000], [(-12351000000000)])⟩,
      ⟨6, ([3351000000000], [(-8625000000000)])⟩,
      ⟨8, ([(-10851000000000)], [1851000000000])⟩,
      ⟨4, ([(-9000000000000)], [4440000000000])⟩,
      ⟨5, ([(-4899000000000)], [(-4101000000000)])⟩,
      ⟨4, ([(-1875000000000)], [(-1230000000000)])⟩,
      ⟨0, ([(-1710000000000)], [0])⟩,
      ⟨1, ([8625000000000], [(-6240000000000)])⟩,
      ⟨0, ([2070000000000], [4305000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
