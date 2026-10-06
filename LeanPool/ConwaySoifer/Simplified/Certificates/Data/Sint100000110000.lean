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
def Sint100000110000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 1 10), hi := (mkRat 11 100), den := 9000000000000,
    steps := [
      ⟨3, ([(-1755000000000)], [9000000000000])⟩,
      ⟨0, ([0], [900000000000])⟩,
      ⟨7, ([8100000000000], [8100000000000])⟩,
      ⟨4, ([(-8100000000000)], [0])⟩,
      ⟨0, ([(-900000000000)], [5400000000000])⟩,
      ⟨0, ([(-900000000000)], [6150000000000])⟩,
      ⟨0, ([(-450000000000)], [6000000000000])⟩,
      ⟨8, ([(-10800000000000)], [9000000000000])⟩,
      ⟨4, ([(-7875000000000)], [3375000000000])⟩,
      ⟨4, ([(-5625000000000)], [900000000000])⟩,
      ⟨8, ([(-15300000000000)], [6300000000000])⟩,
      ⟨5, ([(-2700000000000)], [(-6300000000000)])⟩,
      ⟨5, ([(-600000000000)], [(-6375000000000)])⟩,
      ⟨4, ([(-9000000000000)], [6150000000000])⟩,
      ⟨4, ([(-5400000000000)], [750000000000])⟩,
      ⟨9, ([6300000000000], [(-15300000000000)])⟩,
      ⟨6, ([6750000000000], [(-7650000000000)])⟩,
      ⟨6, ([6750000000000], [(-7350000000000)])⟩,
      ⟨6, ([6900000000000], [(-8250000000000)])⟩,
      ⟨8, ([(-12525000000000)], [3525000000000])⟩,
      ⟨3, ([(-8700000000000)], [7800000000000])⟩,
      ⟨5, ([(-6150000000000)], [(-2850000000000)])⟩,
      ⟨5, ([(-900000000000)], [(-3600000000000)])⟩,
      ⟨1, ([8250000000000], [(-600000000000)])⟩,
      ⟨1, ([8550000000000], [(-855000000000)])⟩,
      ⟨9, ([9000000000000], [(-16380000000000)])⟩,
      ⟨1, ([9000000000000], [(-1125000000000)])⟩,
      ⟨4, ([(-5100000000000)], [(-900000000000)])⟩,
      ⟨0, ([(-900000000000)], [5025000000000])⟩,
      ⟨0, ([(-900000000000)], [6525000000000])⟩,
      ⟨0, ([375000000000], [7005000000000])⟩,
      ⟨6, ([2850000000000], [(-8250000000000)])⟩,
      ⟨6, ([3375000000000], [(-4725000000000)])⟩,
      ⟨0, ([(-630000000000)], [0])⟩,
      ⟨1, ([7500000000000], [(-3900000000000)])⟩,
      ⟨0, ([2550000000000], [5250000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
