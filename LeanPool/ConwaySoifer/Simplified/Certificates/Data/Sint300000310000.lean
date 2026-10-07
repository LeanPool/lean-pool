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
def Sint300000310000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 3 10), hi := (mkRat 31 100), den := 9000000000000,
    steps := [
      ⟨3, ([(-4500000000000)], [8550000000000])⟩,
      ⟨3, ([(-4125000000000)], [8985000000000])⟩,
      ⟨3, ([(-4125000000000)], [9000000000000])⟩,
      ⟨0, ([(-1350000000000)], [600000000000])⟩,
      ⟨0, ([(-1350000000000)], [750000000000])⟩,
      ⟨0, ([(-750000000000)], [(-600000000000)])⟩,
      ⟨0, ([(-600000000000)], [(-750000000000)])⟩,
      ⟨0, ([225000000000], [5175000000000])⟩,
      ⟨0, ([600000000000], [(-1350000000000)])⟩,
      ⟨0, ([750000000000], [(-1350000000000)])⟩,
      ⟨0, ([1050000000000], [4950000000000])⟩,
      ⟨0, ([1350000000000], [(-750000000000)])⟩,
      ⟨8, ([(-13125000000000)], [9000000000000])⟩,
      ⟨4, ([(-8250000000000)], [2700000000000])⟩,
      ⟨5, ([0], [(-2610000000000)])⟩,
      ⟨4, ([(-6150000000000)], [(-2850000000000)])⟩,
      ⟨4, ([(-4050000000000)], [0])⟩,
      ⟨4, ([(-3675000000000)], [(-2700000000000)])⟩,
      ⟨4, ([(-2625000000000)], [(-1800000000000)])⟩,
      ⟨6, ([2625000000000], [(-4425000000000)])⟩,
      ⟨9, ([3525000000000], [(-12525000000000)])⟩,
      ⟨6, ([3750000000000], [(-4650000000000)])⟩,
      ⟨8, ([(-10725000000000)], [1725000000000])⟩,
      ⟨3, ([(-9000000000000)], [6150000000000])⟩,
      ⟨5, ([(-3765000000000)], [(-5235000000000)])⟩,
      ⟨0, ([150000000000], [5250000000000])⟩,
      ⟨5, ([2925000000000], [(-7875000000000)])⟩,
      ⟨5, ([3000000000000], [(-8100000000000)])⟩,
      ⟨4, ([(-9000000000000)], [3450000000000])⟩,
      ⟨4, ([(-5025000000000)], [(-3975000000000)])⟩,
      ⟨4, ([(-3600000000000)], [(-3600000000000)])⟩,
      ⟨4, ([(-3150000000000)], [(-3150000000000)])⟩,
      ⟨4, ([(-1875000000000)], [(-1725000000000)])⟩,
      ⟨8, ([(-9600000000000)], [600000000000])⟩,
      ⟨3, ([(-9000000000000)], [4575000000000])⟩,
      ⟨3, ([(-6375000000000)], [2235000000000])⟩],
    last := 3 }

end ConwaySoifer.Simplified.Certificates.Data
