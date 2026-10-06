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
def Sint150000160000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 3 20), hi := (mkRat 4 25), den := 9000000000000,
    steps := [
      ⟨3, ([(-2400000000000)], [9000000000000])⟩,
      ⟨0, ([825000000000], [(-375000000000)])⟩,
      ⟨8, ([(-11400000000000)], [9000000000000])⟩,
      ⟨0, ([(-900000000000)], [4500000000000])⟩,
      ⟨0, ([(-900000000000)], [4950000000000])⟩,
      ⟨0, ([(-450000000000)], [4575000000000])⟩,
      ⟨0, ([(-375000000000)], [4425000000000])⟩,
      ⟨4, ([(-8100000000000)], [2475000000000])⟩,
      ⟨4, ([(-7650000000000)], [2025000000000])⟩,
      ⟨4, ([(-6570000000000)], [570000000000])⟩,
      ⟨8, ([(-15570000000000)], [6570000000000])⟩,
      ⟨3, ([(-8550000000000)], [7425000000000])⟩,
      ⟨5, ([(-1575000000000)], [(-7425000000000)])⟩,
      ⟨5, ([(-450000000000)], [(-6375000000000)])⟩,
      ⟨4, ([(-9000000000000)], [5325000000000])⟩,
      ⟨0, ([(-1125000000000)], [5175000000000])⟩,
      ⟨0, ([(-450000000000)], [5175000000000])⟩,
      ⟨0, ([(-375000000000)], [(-450000000000)])⟩,
      ⟨6, ([6825000000000], [(-7200000000000)])⟩,
      ⟨4, ([(-6000000000000)], [450000000000])⟩,
      ⟨5, ([(-4350000000000)], [(-4650000000000)])⟩,
      ⟨5, ([(-675000000000)], [(-4500000000000)])⟩,
      ⟨9, ([9000000000000], [(-16200000000000)])⟩,
      ⟨8, ([(-15225000000000)], [6225000000000])⟩,
      ⟨3, ([(-8475000000000)], [7125000000000])⟩,
      ⟨4, ([(-5445000000000)], [0])⟩,
      ⟨5, ([(-4875000000000)], [(-4125000000000)])⟩,
      ⟨0, ([(-1350000000000)], [5250000000000])⟩,
      ⟨0, ([(-1350000000000)], [5850000000000])⟩,
      ⟨0, ([(-225000000000)], [5625000000000])⟩,
      ⟨0, ([0], [5550000000000])⟩,
      ⟨6, ([4650000000000], [(-5400000000000)])⟩,
      ⟨6, ([4695000000000], [(-6570000000000)])⟩,
      ⟨4, ([(-5250000000000)], [0])⟩,
      ⟨5, ([(-5175000000000)], [(-3825000000000)])⟩,
      ⟨4, ([(-4875000000000)], [450000000000])⟩,
      ⟨0, ([(-1350000000000)], [5100000000000])⟩,
      ⟨0, ([(-1350000000000)], [6000000000000])⟩,
      ⟨5, ([(-375000000000)], [(-4050000000000)])⟩,
      ⟨0, ([180000000000], [6570000000000])⟩,
      ⟨0, ([450000000000], [(-825000000000)])⟩,
      ⟨9, ([4125000000000], [(-13050000000000)])⟩,
      ⟨6, ([4275000000000], [(-8100000000000)])⟩,
      ⟨9, ([4425000000000], [(-13050000000000)])⟩,
      ⟨6, ([4500000000000], [(-5625000000000)])⟩,
      ⟨9, ([9000000000000], [(-15225000000000)])⟩,
      ⟨1, ([9000000000000], [(-2805000000000)])⟩,
      ⟨5, ([(-5325000000000)], [(-3675000000000)])⟩,
      ⟨4, ([(-4650000000000)], [(-1350000000000)])⟩,
      ⟨0, ([(-900000000000)], [375000000000])⟩,
      ⟨0, ([1500000000000], [5625000000000])⟩,
      ⟨1, ([3375000000000], [4125000000000])⟩,
      ⟨9, ([3900000000000], [(-12900000000000)])⟩,
      ⟨6, ([3900000000000], [(-7650000000000)])⟩,
      ⟨6, ([4050000000000], [(-8625000000000)])⟩,
      ⟨1, ([9000000000000], [(-3375000000000)])⟩,
      ⟨0, ([1680000000000], [750000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
