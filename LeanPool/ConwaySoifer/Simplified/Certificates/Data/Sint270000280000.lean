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
def Sint270000280000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 27 100), hi := (mkRat 7 25), den := 9000000000000,
    steps := [
      ⟨3, ([(-3999000000000)], [8625000000000])⟩,
      ⟨3, ([(-3810000000000)], [9000000000000])⟩,
      ⟨0, ([(-1215000000000)], [465000000000])⟩,
      ⟨0, ([(-1215000000000)], [750000000000])⟩,
      ⟨0, ([(-1005000000000)], [0])⟩,
      ⟨0, ([270000000000], [5355000000000])⟩,
      ⟨0, ([375000000000], [(-1185000000000)])⟩,
      ⟨0, ([375000000000], [5385000000000])⟩,
      ⟨0, ([465000000000], [(-1215000000000)])⟩,
      ⟨0, ([720000000000], [5250000000000])⟩,
      ⟨0, ([750000000000], [(-1215000000000)])⟩,
      ⟨0, ([900000000000], [5175000000000])⟩,
      ⟨0, ([1185000000000], [(-810000000000)])⟩,
      ⟨0, ([1215000000000], [(-750000000000)])⟩,
      ⟨0, ([1215000000000], [(-465000000000)])⟩,
      ⟨8, ([(-12825000000000)], [9000000000000])⟩,
      ⟨4, ([(-8415000000000)], [3240000000000])⟩,
      ⟨4, ([(-4500000000000)], [360000000000])⟩,
      ⟨5, ([0], [(-2520000000000)])⟩,
      ⟨4, ([(-3570000000000)], [(-2430000000000)])⟩,
      ⟨4, ([(-3240000000000)], [(-750000000000)])⟩,
      ⟨5, ([(-3195000000000)], [(-5805000000000)])⟩,
      ⟨6, ([2625000000000], [(-4374000000000)])⟩,
      ⟨6, ([4251000000000], [(-4626000000000)])⟩,
      ⟨8, ([(-10620000000000)], [1620000000000])⟩,
      ⟨4, ([(-9000000000000)], [3855000000000])⟩,
      ⟨5, ([(-4590000000000)], [(-4410000000000)])⟩,
      ⟨4, ([(-2250000000000)], [(-1620000000000)])⟩,
      ⟨0, ([(-1710000000000)], [375000000000])⟩,
      ⟨0, ([(-810000000000)], [(-750000000000)])⟩,
      ⟨5, ([2250000000000], [(-6750000000000)])⟩,
      ⟨6, ([2610000000000], [(-4860000000000)])⟩,
      ⟨9, ([9000000000000], [(-14175000000000)])⟩,
      ⟨3, ([(-8190000000000)], [5940000000000])⟩,
      ⟨5, ([(-4635000000000)], [(-4365000000000)])⟩,
      ⟨3, ([(-2625000000000)], [6270000000000])⟩,
      ⟨4, ([(-2445000000000)], [(-2430000000000)])⟩,
      ⟨0, ([(-1935000000000)], [0])⟩,
      ⟨4, ([(-1875000000000)], [(-2265000000000)])⟩,
      ⟨3, ([(-1710000000000)], [6375000000000])⟩,
      ⟨4, ([(-1215000000000)], [(-1785000000000)])⟩,
      ⟨0, ([(-570000000000)], [(-1140000000000)])⟩,
      ⟨9, ([2790000000000], [(-11790000000000)])⟩,
      ⟨6, ([3435000000000], [(-9000000000000)])⟩,
      ⟨1, ([9000000000000], [(-3765000000000)])⟩,
      ⟨8, ([(-9930000000000)], [9000000000000])⟩,
      ⟨8, ([(-9825000000000)], [825000000000])⟩,
      ⟨4, ([(-9000000000000)], [4980000000000])⟩,
      ⟨3, ([(-7875000000000)], [5445000000000])⟩,
      ⟨0, ([(-7305000000000)], [4875000000000])⟩,
      ⟨5, ([(-4785000000000)], [(-4215000000000)])⟩,
      ⟨2, ([(-2940000000000)], [9000000000000])⟩,
      ⟨0, ([(-1530000000000)], [(-900000000000)])⟩,
      ⟨0, ([1515000000000], [4860000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
