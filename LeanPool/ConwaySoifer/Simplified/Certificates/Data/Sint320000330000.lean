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
def Sint320000330000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 8 25), hi := (mkRat 33 100), den := 9000000000000,
    steps := [
      ⟨3, ([(-4500000000000)], [8640000000000])⟩,
      ⟨3, ([(-4320000000000)], [9000000000000])⟩,
      ⟨0, ([(-1440000000000)], [690000000000])⟩,
      ⟨0, ([(-750000000000)], [(-690000000000)])⟩,
      ⟨0, ([195000000000], [4680000000000])⟩,
      ⟨0, ([285000000000], [4875000000000])⟩,
      ⟨0, ([360000000000], [4890000000000])⟩,
      ⟨0, ([690000000000], [(-1440000000000)])⟩,
      ⟨0, ([960000000000], [4875000000000])⟩,
      ⟨0, ([1440000000000], [(-750000000000)])⟩,
      ⟨9, ([6750000000000], [(-13320000000000)])⟩,
      ⟨8, ([(-13320000000000)], [9000000000000])⟩,
      ⟨4, ([(-8505000000000)], [2880000000000])⟩,
      ⟨3, ([(-4410000000000)], [8250000000000])⟩,
      ⟨5, ([0], [(-2835000000000)])⟩,
      ⟨4, ([(-6045000000000)], [(-2955000000000)])⟩,
      ⟨4, ([(-4335000000000)], [0])⟩,
      ⟨4, ([(-3816000000000)], [(-2934000000000)])⟩,
      ⟨4, ([(-2880000000000)], [(-2250000000000)])⟩,
      ⟨4, ([(-2820000000000)], [(-1500000000000)])⟩,
      ⟨6, ([2880000000000], [(-5130000000000)])⟩,
      ⟨6, ([3240000000000], [(-4875000000000)])⟩,
      ⟨9, ([3510000000000], [(-12510000000000)])⟩,
      ⟨6, ([4875000000000], [(-5160000000000)])⟩,
      ⟨6, ([5160000000000], [(-8100000000000)])⟩,
      ⟨8, ([(-10635000000000)], [1635000000000])⟩,
      ⟨4, ([(-9000000000000)], [3495000000000])⟩,
      ⟨3, ([(-9000000000000)], [6045000000000])⟩,
      ⟨3, ([(-8250000000000)], [5760000000000])⟩,
      ⟨0, ([90000000000], [5160000000000])⟩,
      ⟨5, ([3375000000000], [(-8559000000000)])⟩,
      ⟨5, ([3390000000000], [(-8640000000000)])⟩,
      ⟨1, ([9000000000000], [(-2940000000000)])⟩,
      ⟨8, ([(-10515000000000)], [1515000000000])⟩,
      ⟨3, ([(-7875000000000)], [5184000000000])⟩,
      ⟨4, ([(-4500000000000)], [(-4320000000000)])⟩,
      ⟨5, ([(-4380000000000)], [(-4620000000000)])⟩,
      ⟨4, ([(-4185000000000)], [0])⟩,
      ⟨4, ([(-3135000000000)], [(-3240000000000)])⟩,
      ⟨0, ([(-1920000000000)], [375000000000])⟩,
      ⟨5, ([0], [(-2559000000000)])⟩,
      ⟨0, ([66000000000], [5184000000000])⟩,
      ⟨9, ([795000000000], [(-9795000000000)])⟩,
      ⟨6, ([2430000000000], [(-4680000000000)])⟩,
      ⟨5, ([3540000000000], [(-9000000000000)])⟩,
      ⟨0, ([(-4440000000000)], [(-4560000000000)])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
