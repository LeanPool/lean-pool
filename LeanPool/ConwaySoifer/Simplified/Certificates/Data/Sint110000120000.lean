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
def Sint110000120000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 11 100), hi := (mkRat 3 25), den := 9000000000000,
    steps := [
      ⟨3, ([(-1875000000000)], [9000000000000])⟩,
      ⟨0, ([0], [990000000000])⟩,
      ⟨4, ([(-8340000000000)], [750000000000])⟩,
      ⟨0, ([(-990000000000)], [5490000000000])⟩,
      ⟨0, ([(-990000000000)], [6000000000000])⟩,
      ⟨0, ([(-690000000000)], [5940000000000])⟩,
      ⟨0, ([(-330000000000)], [5625000000000])⟩,
      ⟨8, ([(-10920000000000)], [9000000000000])⟩,
      ⟨4, ([(-7920000000000)], [3420000000000])⟩,
      ⟨4, ([(-5940000000000)], [750000000000])⟩,
      ⟨4, ([(-5865000000000)], [990000000000])⟩,
      ⟨8, ([(-15420000000000)], [6420000000000])⟩,
      ⟨5, ([(-2625000000000)], [(-6375000000000)])⟩,
      ⟨5, ([(-645000000000)], [(-6375000000000)])⟩,
      ⟨4, ([(-9000000000000)], [6000000000000])⟩,
      ⟨4, ([(-5625000000000)], [660000000000])⟩,
      ⟨9, ([6420000000000], [(-15420000000000)])⟩,
      ⟨6, ([6630000000000], [(-7125000000000)])⟩,
      ⟨6, ([6930000000000], [(-8250000000000)])⟩,
      ⟨8, ([(-13065000000000)], [4065000000000])⟩,
      ⟨3, ([(-8625000000000)], [7635000000000])⟩,
      ⟨5, ([(-6000000000000)], [(-3000000000000)])⟩,
      ⟨5, ([(-990000000000)], [(-3750000000000)])⟩,
      ⟨5, ([(-900000000000)], [(-3960000000000)])⟩,
      ⟨1, ([8250000000000], [(-735000000000)])⟩,
      ⟨9, ([9000000000000], [(-16170000000000)])⟩,
      ⟨1, ([9000000000000], [(-1260000000000)])⟩,
      ⟨4, ([(-5010000000000)], [(-990000000000)])⟩,
      ⟨0, ([(-990000000000)], [5115000000000])⟩,
      ⟨0, ([(-990000000000)], [6375000000000])⟩,
      ⟨0, ([375000000000], [6843000000000])⟩,
      ⟨9, ([3000000000000], [(-11970000000000)])⟩,
      ⟨6, ([3000000000000], [(-8340000000000)])⟩,
      ⟨6, ([3750000000000], [(-4740000000000)])⟩,
      ⟨0, ([(-750000000000)], [90000000000])⟩,
      ⟨5, ([(-330000000000)], [(-3375000000000)])⟩,
      ⟨6, ([3000000000000], [(-7920000000000)])⟩,
      ⟨1, ([9000000000000], [(-5505000000000)])⟩,
      ⟨0, ([2430000000000], [5250000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
