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

/-- Exact interval and proposed forced-point trace for the Aown contact case. -/
def Aown120000130000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 3 25), hi := (mkRat 13 100), den := 9000000000000,
    steps := [
      ⟨0, ([0], [510000000000])⟩,
      ⟨0, ([510000000000], [(-510000000000)])⟩,
      ⟨0, ([1080000000000], [0])⟩,
      ⟨2, ([2220000000000], [6780000000000])⟩,
      ⟨2, ([7500000000000], [1080000000000])⟩,
      ⟨6, ([9000000000000], [(-6780000000000)])⟩,
      ⟨4, ([(-7920000000000)], [0])⟩,
      ⟨3, ([(-2295000000000)], [9000000000000])⟩,
      ⟨0, ([0], [1080000000000])⟩,
      ⟨0, ([5295000000000], [1080000000000])⟩,
      ⟨0, ([6156000000000], [900000000000])⟩,
      ⟨0, ([6300000000000], [825000000000])⟩,
      ⟨0, ([6585000000000], [540000000000])⟩,
      ⟨9, ([8640000000000], [(-15765000000000)])⟩,
      ⟨1, ([9000000000000], [4680000000000])⟩,
      ⟨8, ([(-11325000000000)], [9000000000000])⟩,
      ⟨4, ([(-7920000000000)], [4170000000000])⟩,
      ⟨4, ([(-3720000000000)], [720000000000])⟩,
      ⟨3, ([(-3570000000000)], [4320000000000])⟩,
      ⟨6, ([7695000000000], [(-3375000000000)])⟩,
      ⟨6, ([9000000000000], [(-3495000000000)])⟩,
      ⟨8, ([(-11865000000000)], [2865000000000])⟩,
      ⟨4, ([(-8250000000000)], [5760000000000])⟩,
      ⟨5, ([(-5460000000000)], [(-3540000000000)])⟩,
      ⟨5, ([(-5250000000000)], [(-3210000000000)])⟩,
      ⟨5, ([360000000000], [(-4110000000000)])⟩,
      ⟨5, ([3420000000000], [(-7920000000000)])⟩],
    last := 5 }

end ConwaySoifer.Simplified.Certificates.Data
