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
def Sint290000300000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 29 100), hi := (mkRat 3 10), den := 9000000000000,
    steps := [
      ⟨3, ([(-4302000000000)], [8625000000000])⟩,
      ⟨3, ([(-4020000000000)], [9000000000000])⟩,
      ⟨0, ([(-1305000000000)], [555000000000])⟩,
      ⟨0, ([(-555000000000)], [(-750000000000)])⟩,
      ⟨0, ([270000000000], [5250000000000])⟩,
      ⟨0, ([870000000000], [4875000000000])⟩,
      ⟨0, ([1305000000000], [(-555000000000)])⟩,
      ⟨8, ([(-13065000000000)], [9000000000000])⟩,
      ⟨4, ([(-8250000000000)], [2730000000000])⟩,
      ⟨5, ([0], [(-2595000000000)])⟩,
      ⟨4, ([(-6360000000000)], [(-2640000000000)])⟩,
      ⟨4, ([(-4335000000000)], [0])⟩,
      ⟨4, ([(-3900000000000)], [(-2625000000000)])⟩,
      ⟨4, ([(-3750000000000)], [(-2610000000000)])⟩,
      ⟨4, ([(-3480000000000)], [(-2520000000000)])⟩,
      ⟨4, ([(-3000000000000)], [(-2220000000000)])⟩,
      ⟨5, ([(-2655000000000)], [(-6345000000000)])⟩,
      ⟨4, ([(-2625000000000)], [(-1677000000000)])⟩,
      ⟨6, ([2610000000000], [(-4500000000000)])⟩,
      ⟨6, ([2610000000000], [(-4485000000000)])⟩,
      ⟨6, ([3750000000000], [(-4698000000000)])⟩,
      ⟨8, ([(-10980000000000)], [1980000000000])⟩,
      ⟨4, ([(-8625000000000)], [3105000000000])⟩,
      ⟨5, ([2610000000000], [(-7485000000000)])⟩,
      ⟨9, ([9000000000000], [(-14400000000000)])⟩,
      ⟨8, ([(-10845000000000)], [1845000000000])⟩,
      ⟨4, ([(-9000000000000)], [3585000000000])⟩,
      ⟨4, ([(-6240000000000)], [(-2760000000000)])⟩,
      ⟨5, ([(-4320000000000)], [(-4680000000000)])⟩,
      ⟨4, ([(-2895000000000)], [(-2625000000000)])⟩,
      ⟨4, ([(-2640000000000)], [(-2610000000000)])⟩,
      ⟨0, ([720000000000], [(-1440000000000)])⟩,
      ⟨6, ([2565000000000], [(-5175000000000)])⟩,
      ⟨5, ([(-4395000000000)], [(-4605000000000)])⟩,
      ⟨0, ([(-2655000000000)], [0])⟩,
      ⟨9, ([1650000000000], [(-10650000000000)])⟩,
      ⟨6, ([3645000000000], [(-9000000000000)])⟩,
      ⟨1, ([3915000000000], [2250000000000])⟩,
      ⟨1, ([7260000000000], [(-5010000000000)])⟩,
      ⟨1, ([9000000000000], [(-5985000000000)])⟩],
    last := 1 }

end ConwaySoifer.Simplified.Certificates.Data
