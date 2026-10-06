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
def Sint330000340000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 33 100), hi := (mkRat 17 50), den := 9000000000000,
    steps := [
      ⟨3, ([(-4500000000000)], [8460000000000])⟩,
      ⟨3, ([(-4455000000000)], [8580000000000])⟩,
      ⟨3, ([(-4455000000000)], [9000000000000])⟩,
      ⟨0, ([(-1485000000000)], [735000000000])⟩,
      ⟨0, ([(-1125000000000)], [0])⟩,
      ⟨0, ([0], [(-1125000000000)])⟩,
      ⟨0, ([210000000000], [5040000000000])⟩,
      ⟨0, ([375000000000], [4971000000000])⟩,
      ⟨0, ([735000000000], [(-1485000000000)])⟩,
      ⟨0, ([750000000000], [4596000000000])⟩,
      ⟨0, ([1485000000000], [(-750000000000)])⟩,
      ⟨8, ([(-13455000000000)], [9000000000000])⟩,
      ⟨4, ([(-5346000000000)], [471000000000])⟩,
      ⟨4, ([(-5040000000000)], [165000000000])⟩,
      ⟨3, ([(-4455000000000)], [8205000000000])⟩,
      ⟨5, ([0], [(-2760000000000)])⟩,
      ⟨8, ([(-14175000000000)], [5175000000000])⟩,
      ⟨4, ([(-8595000000000)], [2970000000000])⟩,
      ⟨4, ([(-5625000000000)], [(-3375000000000)])⟩,
      ⟨4, ([(-4740000000000)], [0])⟩,
      ⟨4, ([(-3960000000000)], [(-3165000000000)])⟩,
      ⟨4, ([(-2790000000000)], [(-2250000000000)])⟩,
      ⟨4, ([(-2625000000000)], [(-1980000000000)])⟩,
      ⟨6, ([2790000000000], [(-5040000000000)])⟩,
      ⟨6, ([2880000000000], [(-4755000000000)])⟩,
      ⟨9, ([3285000000000], [(-12285000000000)])⟩,
      ⟨8, ([(-10710000000000)], [1710000000000])⟩,
      ⟨3, ([(-9000000000000)], [5625000000000])⟩,
      ⟨3, ([(-7845000000000)], [4875000000000])⟩,
      ⟨5, ([(-4110000000000)], [(-4890000000000)])⟩,
      ⟨0, ([(-1575000000000)], [450000000000])⟩,
      ⟨0, ([90000000000], [5160000000000])⟩,
      ⟨5, ([3375000000000], [(-8721000000000)])⟩,
      ⟨4, ([(-9000000000000)], [3405000000000])⟩,
      ⟨4, ([(-3750000000000)], [(-3960000000000)])⟩,
      ⟨4, ([(-2970000000000)], [(-3000000000000)])⟩,
      ⟨0, ([(-2640000000000)], [4125000000000])⟩,
      ⟨5, ([0], [(-2640000000000)])⟩,
      ⟨0, ([750000000000], [(-1575000000000)])⟩,
      ⟨0, ([(-3420000000000)], [0])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
