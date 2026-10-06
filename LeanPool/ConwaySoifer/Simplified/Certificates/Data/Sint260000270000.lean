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
def Sint260000270000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 13 50), hi := (mkRat 27 100), den := 9000000000000,
    steps := [
      ⟨3, ([(-3750000000000)], [8790000000000])⟩,
      ⟨3, ([(-3690000000000)], [9000000000000])⟩,
      ⟨0, ([(-1170000000000)], [375000000000])⟩,
      ⟨0, ([240000000000], [5250000000000])⟩,
      ⟨0, ([375000000000], [(-1170000000000)])⟩,
      ⟨0, ([375000000000], [5475000000000])⟩,
      ⟨0, ([780000000000], [5250000000000])⟩,
      ⟨0, ([795000000000], [(-1170000000000)])⟩,
      ⟨0, ([1170000000000], [(-795000000000)])⟩,
      ⟨0, ([1170000000000], [(-375000000000)])⟩,
      ⟨8, ([(-12735000000000)], [9000000000000])⟩,
      ⟨4, ([(-8370000000000)], [3120000000000])⟩,
      ⟨4, ([(-8250000000000)], [3150000000000])⟩,
      ⟨4, ([(-4587000000000)], [375000000000])⟩,
      ⟨3, ([(-3837000000000)], [8625000000000])⟩,
      ⟨5, ([0], [(-2505000000000)])⟩,
      ⟨4, ([(-4155000000000)], [0])⟩,
      ⟨4, ([(-3660000000000)], [(-2340000000000)])⟩,
      ⟨5, ([(-3090000000000)], [(-5910000000000)])⟩,
      ⟨4, ([(-2805000000000)], [(-1875000000000)])⟩,
      ⟨6, ([2625000000000], [(-4320000000000)])⟩,
      ⟨6, ([4305000000000], [(-4680000000000)])⟩,
      ⟨8, ([(-10845000000000)], [1845000000000])⟩,
      ⟨4, ([(-9000000000000)], [3990000000000])⟩,
      ⟨5, ([(-4590000000000)], [(-4410000000000)])⟩,
      ⟨0, ([(-1560000000000)], [375000000000])⟩,
      ⟨0, ([(-810000000000)], [(-750000000000)])⟩,
      ⟨5, ([2160000000000], [(-6660000000000)])⟩,
      ⟨5, ([2250000000000], [(-6930000000000)])⟩,
      ⟨9, ([9000000000000], [(-14415000000000)])⟩,
      ⟨3, ([(-8100000000000)], [6120000000000])⟩,
      ⟨5, ([(-4680000000000)], [(-4320000000000)])⟩,
      ⟨4, ([(-2535000000000)], [(-2340000000000)])⟩,
      ⟨3, ([(-2163000000000)], [6375000000000])⟩,
      ⟨4, ([(-2070000000000)], [(-2250000000000)])⟩,
      ⟨0, ([(-1740000000000)], [0])⟩,
      ⟨4, ([(-1560000000000)], [(-1815000000000)])⟩,
      ⟨0, ([(-660000000000)], [(-900000000000)])⟩,
      ⟨9, ([2760000000000], [(-11760000000000)])⟩,
      ⟨6, ([3435000000000], [(-9000000000000)])⟩,
      ⟨1, ([9000000000000], [(-3510000000000)])⟩,
      ⟨8, ([(-10185000000000)], [1185000000000])⟩,
      ⟨8, ([(-9975000000000)], [9000000000000])⟩,
      ⟨4, ([(-9000000000000)], [5055000000000])⟩,
      ⟨3, ([(-7965000000000)], [5625000000000])⟩,
      ⟨0, ([(-7215000000000)], [4875000000000])⟩,
      ⟨5, ([(-4788000000000)], [(-4212000000000)])⟩,
      ⟨2, ([(-2775000000000)], [9000000000000])⟩,
      ⟨0, ([(-1500000000000)], [(-840000000000)])⟩,
      ⟨0, ([1560000000000], [4875000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
