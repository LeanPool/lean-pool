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
def Sint280000290000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 7 25), hi := (mkRat 29 100), den := 9000000000000,
    steps := [
      ⟨3, ([(-3960000000000)], [8625000000000])⟩,
      ⟨3, ([(-3915000000000)], [9000000000000])⟩,
      ⟨0, ([(-1260000000000)], [510000000000])⟩,
      ⟨0, ([(-1260000000000)], [750000000000])⟩,
      ⟨0, ([(-840000000000)], [(-375000000000)])⟩,
      ⟨0, ([210000000000], [5040000000000])⟩,
      ⟨0, ([375000000000], [(-1215000000000)])⟩,
      ⟨0, ([375000000000], [5265000000000])⟩,
      ⟨0, ([840000000000], [(-1215000000000)])⟩,
      ⟨0, ([960000000000], [5040000000000])⟩,
      ⟨0, ([1215000000000], [(-840000000000)])⟩,
      ⟨0, ([1260000000000], [(-750000000000)])⟩,
      ⟨0, ([1260000000000], [(-510000000000)])⟩,
      ⟨8, ([(-12915000000000)], [9000000000000])⟩,
      ⟨4, ([(-8250000000000)], [3030000000000])⟩,
      ⟨4, ([(-5220000000000)], [720000000000])⟩,
      ⟨4, ([(-4875000000000)], [339000000000])⟩,
      ⟨5, ([0], [(-2580000000000)])⟩,
      ⟨8, ([(-14400000000000)], [5400000000000])⟩,
      ⟨3, ([(-7995000000000)], [6120000000000])⟩,
      ⟨4, ([(-4125000000000)], [0])⟩,
      ⟨4, ([(-3750000000000)], [(-2520000000000)])⟩,
      ⟨5, ([(-2880000000000)], [(-6120000000000)])⟩,
      ⟨4, ([(-2640000000000)], [(-1320000000000)])⟩,
      ⟨4, ([(-2625000000000)], [(-1911000000000)])⟩,
      ⟨6, ([2589000000000], [(-4464000000000)])⟩,
      ⟨6, ([2976000000000], [(-4464000000000)])⟩,
      ⟨8, ([(-10770000000000)], [1770000000000])⟩,
      ⟨4, ([(-8625000000000)], [3405000000000])⟩,
      ⟨5, ([(-4515000000000)], [(-4485000000000)])⟩,
      ⟨0, ([(-1680000000000)], [375000000000])⟩,
      ⟨0, ([(-840000000000)], [(-660000000000)])⟩,
      ⟨5, ([2445000000000], [(-7320000000000)])⟩,
      ⟨8, ([(-10665000000000)], [1665000000000])⟩,
      ⟨4, ([(-9000000000000)], [3780000000000])⟩,
      ⟨5, ([(-4536000000000)], [(-4464000000000)])⟩,
      ⟨4, ([(-2625000000000)], [(-2520000000000)])⟩,
      ⟨3, ([(-2250000000000)], [6300000000000])⟩,
      ⟨4, ([(-1875000000000)], [(-1680000000000)])⟩,
      ⟨0, ([(-1875000000000)], [195000000000])⟩,
      ⟨0, ([(-840000000000)], [(-750000000000)])⟩,
      ⟨6, ([3000000000000], [(-7320000000000)])⟩,
      ⟨1, ([9000000000000], [(-3240000000000)])⟩,
      ⟨8, ([(-10260000000000)], [1260000000000])⟩,
      ⟨8, ([(-10125000000000)], [9000000000000])⟩,
      ⟨4, ([(-9000000000000)], [4860000000000])⟩,
      ⟨3, ([(-7875000000000)], [5625000000000])⟩,
      ⟨0, ([(-7125000000000)], [4605000000000])⟩,
      ⟨5, ([(-4605000000000)], [(-4395000000000)])⟩,
      ⟨2, ([(-2835000000000)], [9000000000000])⟩,
      ⟨0, ([(-2520000000000)], [0])⟩,
      ⟨0, ([1425000000000], [4875000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
