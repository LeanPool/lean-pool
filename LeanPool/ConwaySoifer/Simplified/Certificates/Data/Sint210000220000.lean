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
def Sint210000220000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 21 100), hi := (mkRat 11 50), den := 9000000000000,
    steps := [
      ⟨3, ([(-3135000000000)], [9000000000000])⟩,
      ⟨0, ([(-1005000000000)], [375000000000])⟩,
      ⟨0, ([330000000000], [5670000000000])⟩,
      ⟨0, ([375000000000], [5790000000000])⟩,
      ⟨0, ([630000000000], [(-1005000000000)])⟩,
      ⟨0, ([705000000000], [5670000000000])⟩,
      ⟨0, ([1005000000000], [(-630000000000)])⟩,
      ⟨8, ([(-12225000000000)], [9000000000000])⟩,
      ⟨4, ([(-8100000000000)], [3375000000000])⟩,
      ⟨4, ([(-8055000000000)], [3423375000000])⟩,
      ⟨4, ([(-4875000000000)], [945000000000])⟩,
      ⟨4, ([(-4500000000000)], [630000000000])⟩,
      ⟨3, ([(-3402000000000)], [8652000000000])⟩,
      ⟨8, ([(-13920000000000)], [4920000000000])⟩,
      ⟨5, ([(-3270000000000)], [(-5730000000000)])⟩,
      ⟨5, ([(-495000000000)], [(-5175000000000)])⟩,
      ⟨4, ([(-9000000000000)], [4530000000000])⟩,
      ⟨4, ([(-6555000000000)], [(-1500000000000)])⟩,
      ⟨4, ([(-4275000000000)], [375000000000])⟩,
      ⟨9, ([5220000000000], [(-14220000000000)])⟩,
      ⟨6, ([5598000000000], [(-6000000000000)])⟩,
      ⟨8, ([(-11475000000000)], [2475000000000])⟩,
      ⟨3, ([(-8250000000000)], [6480000000000])⟩,
      ⟨5, ([(-5055000000000)], [(-3945000000000)])⟩,
      ⟨5, ([(-4725000000000)], [(-3900000000000)])⟩,
      ⟨5, ([(-2250000000000)], [(-3915000000000)])⟩,
      ⟨5, ([(-750000000000)], [(-3975000000000)])⟩,
      ⟨5, ([(-375000000000)], [(-4350000000000)])⟩,
      ⟨9, ([9000000000000], [(-15060000000000)])⟩,
      ⟨0, ([(-1545000000000)], [4875000000000])⟩,
      ⟨6, ([3900000000000], [(-8625000000000)])⟩,
      ⟨6, ([4125000000000], [(-4725000000000)])⟩,
      ⟨4, ([(-3375000000000)], [45000000000])⟩,
      ⟨5, ([1650000000000], [(-6375000000000)])⟩,
      ⟨1, ([8850000000000], [(-4725000000000)])⟩,
      ⟨5, ([(-5280000000000)], [(-3720000000000)])⟩,
      ⟨4, ([(-2985000000000)], [(-1890000000000)])⟩,
      ⟨0, ([2250000000000], [4725000000000])⟩,
      ⟨0, ([(-1890000000000)], [0])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
