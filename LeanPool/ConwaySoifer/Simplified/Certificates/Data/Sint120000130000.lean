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
def Sint120000130000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 3 25), hi := (mkRat 13 100), den := 9000000000000,
    steps := [
      ⟨4, ([(-8085000000000)], [0])⟩,
      ⟨3, ([(-2010000000000)], [9000000000000])⟩,
      ⟨8, ([(-11070000000000)], [9000000000000])⟩,
      ⟨0, ([(-1080000000000)], [5580000000000])⟩,
      ⟨0, ([(-540000000000)], [5625000000000])⟩,
      ⟨0, ([(-360000000000)], [5535000000000])⟩,
      ⟨4, ([(-7875000000000)], [3240000000000])⟩,
      ⟨4, ([(-5760000000000)], [750000000000])⟩,
      ⟨8, ([(-15300000000000)], [6300000000000])⟩,
      ⟨3, ([(-8640000000000)], [7740000000000])⟩,
      ⟨5, ([(-2430000000000)], [(-6570000000000)])⟩,
      ⟨5, ([(-540000000000)], [(-6210000000000)])⟩,
      ⟨4, ([(-9000000000000)], [5835000000000])⟩,
      ⟨4, ([(-5625000000000)], [540000000000])⟩,
      ⟨0, ([(-375000000000)], [5760000000000])⟩,
      ⟨9, ([6300000000000], [(-15300000000000)])⟩,
      ⟨6, ([6585000000000], [(-7125000000000)])⟩,
      ⟨6, ([6840000000000], [(-8250000000000)])⟩,
      ⟨8, ([(-13320000000000)], [4320000000000])⟩,
      ⟨3, ([(-8580000000000)], [7500000000000])⟩,
      ⟨5, ([(-5769000000000)], [(-3231000000000)])⟩,
      ⟨4, ([(-5595000000000)], [720000000000])⟩,
      ⟨5, ([(-1080000000000)], [(-4095000000000)])⟩,
      ⟨5, ([(-855000000000)], [(-4320000000000)])⟩,
      ⟨9, ([9000000000000], [(-16140000000000)])⟩,
      ⟨1, ([9000000000000], [(-1290000000000)])⟩,
      ⟨5, ([(-5835000000000)], [(-3165000000000)])⟩,
      ⟨4, ([(-5175000000000)], [(-1080000000000)])⟩,
      ⟨0, ([(-1080000000000)], [5175000000000])⟩,
      ⟨0, ([(-1080000000000)], [6375000000000])⟩,
      ⟨0, ([285000000000], [6840000000000])⟩,
      ⟨9, ([3240000000000], [(-12240000000000)])⟩,
      ⟨6, ([3240000000000], [(-8415000000000)])⟩,
      ⟨6, ([4095000000000], [(-5175000000000)])⟩,
      ⟨0, ([(-750000000000)], [30000000000])⟩,
      ⟨1, ([8250000000000], [(-4320000000000)])⟩,
      ⟨0, ([2250000000000], [5310000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
