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

/-- Exact interval and proposed forced-point trace for the Sext contact case. -/
def Sext170000180000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 17 100), hi := (mkRat 9 50), den := 9000000000000,
    steps := [
      ⟨0, ([(-885000000000)], [375000000000])⟩,
      ⟨0, ([(-510000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-510000000000)], [885000000000])⟩,
      ⟨0, ([375000000000], [510000000000])⟩,
      ⟨0, ([6375000000000], [(-5940000000000)])⟩,
      ⟨0, ([6495000000000], [(-6120000000000)])⟩,
      ⟨9, ([8520000000000], [(-10020000000000)])⟩,
      ⟨9, ([9000000000000], [(-9930000000000)])⟩,
      ⟨5, ([6000000000000], [(-8754000000000)])⟩,
      ⟨5, ([6345000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-4110000000000)], [(-765000000000)])⟩,
      ⟨4, ([(-4050000000000)], [(-1125000000000)])⟩,
      ⟨4, ([(-3879000000000)], [(-5121000000000)])⟩,
      ⟨4, ([(-3870000000000)], [(-2250000000000)])⟩,
      ⟨8, ([(-12870000000000)], [3870000000000])⟩,
      ⟨3, ([(-7980000000000)], [3990000000000])⟩,
      ⟨3, ([(-6750000000000)], [3870000000000])⟩,
      ⟨3, ([(-4875000000000)], [4110000000000])⟩,
      ⟨5, ([(-1500000000000)], [(-6990000000000)])⟩,
      ⟨0, ([(-510000000000)], [(-390000000000)])⟩,
      ⟨8, ([(-14115000000000)], [9000000000000])⟩,
      ⟨4, ([(-4125000000000)], [(-180000000000)])⟩,
      ⟨4, ([(-3969000000000)], [(-441000000000)])⟩,
      ⟨2, ([(-3765000000000)], [9000000000000])⟩,
      ⟨2, ([(-510000000000)], [6000000000000])⟩,
      ⟨0, ([3750000000000], [(-5280000000000)])⟩,
      ⟨0, ([6555000000000], [(-6375000000000)])⟩,
      ⟨3, ([(-9000000000000)], [3879000000000])⟩,
      ⟨3, ([(-6960000000000)], [8250000000000])⟩,
      ⟨3, ([(-4410000000000)], [3969000000000])⟩,
      ⟨4, ([(-3060000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-390000000000)], [900000000000])⟩,
      ⟨7, ([5370000000000], [9000000000000])⟩,
      ⟨1, ([7365000000000], [(-4125000000000)])⟩,
      ⟨8, ([(-12375000000000)], [3375000000000])⟩,
      ⟨8, ([(-11379000000000)], [8625000000000])⟩,
      ⟨3, ([(-9000000000000)], [3300000000000])⟩,
      ⟨2, ([(-5121000000000)], [9000000000000])⟩,
      ⟨2, ([(-441000000000)], [4410000000000])⟩,
      ⟨7, ([8379000000000], [3375000000000])⟩,
      ⟨0, ([3879000000000], [5121000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
