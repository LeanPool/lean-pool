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
def Aown210000220000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 21 100), hi := (mkRat 11 50), den := 9000000000000,
    steps := [
      ⟨0, ([(-1005000000000)], [375000000000])⟩,
      ⟨0, ([(-1005000000000)], [630000000000])⟩,
      ⟨0, ([(-630000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-630000000000)], [1005000000000])⟩,
      ⟨0, ([(-375000000000)], [(-630000000000)])⟩,
      ⟨0, ([375000000000], [(-1005000000000)])⟩,
      ⟨0, ([630000000000], [(-1005000000000)])⟩,
      ⟨0, ([1890000000000], [0])⟩,
      ⟨2, ([6165000000000], [2460000000000])⟩,
      ⟨6, ([9000000000000], [(-3402000000000)])⟩,
      ⟨1, ([9000000000000], [4725000000000])⟩,
      ⟨7, ([9000000000000], [6090000000000])⟩,
      ⟨3, ([(-4110000000000)], [9000000000000])⟩,
      ⟨0, ([(-495000000000)], [1125000000000])⟩,
      ⟨5, ([0], [(-7305000000000)])⟩,
      ⟨0, ([0], [1275000000000])⟩,
      ⟨2, ([600000000000], [9000000000000])⟩,
      ⟨0, ([1260000000000], [1500000000000])⟩,
      ⟨5, ([2055000000000], [(-8055000000000)])⟩,
      ⟨0, ([3285000000000], [1890000000000])⟩,
      ⟨0, ([4275000000000], [600000000000])⟩,
      ⟨2, ([4500000000000], [4725000000000])⟩,
      ⟨2, ([6750000000000], [1620000000000])⟩,
      ⟨2, ([6750000000000], [1890000000000])⟩,
      ⟨1, ([7365000000000], [375000000000])⟩,
      ⟨9, ([8250000000000], [(-11652000000000)])⟩,
      ⟨6, ([8670000000000], [(-3000000000000)])⟩,
      ⟨6, ([9000000000000], [(-3135000000000)])⟩,
      ⟨8, ([(-13170000000000)], [9000000000000])⟩,
      ⟨4, ([(-8055000000000)], [2625000000000])⟩,
      ⟨3, ([(-5670000000000)], [6000000000000])⟩,
      ⟨4, ([(-4725000000000)], [225000000000])⟩,
      ⟨3, ([(-3180000000000)], [9000000000000])⟩,
      ⟨0, ([330000000000], [5670000000000])⟩,
      ⟨5, ([600000000000], [(-4875000000000)])⟩,
      ⟨0, ([2250000000000], [4500000000000])⟩,
      ⟨0, ([2970000000000], [3780000000000])⟩,
      ⟨5, ([3780000000000], [(-8250000000000)])⟩,
      ⟨0, ([5670000000000], [330000000000])⟩,
      ⟨0, ([5670000000000], [900000000000])⟩,
      ⟨2, ([6480000000000], [1770000000000])⟩,
      ⟨8, ([(-14598000000000)], [5598000000000])⟩,
      ⟨8, ([(-12225000000000)], [9000000000000])⟩,
      ⟨4, ([(-8250000000000)], [3975000000000])⟩,
      ⟨4, ([(-5415000000000)], [(-3585000000000)])⟩,
      ⟨4, ([(-3375000000000)], [45000000000])⟩,
      ⟨3, ([(-3135000000000)], [9000000000000])⟩,
      ⟨5, ([(-2598000000000)], [(-6402000000000)])⟩,
      ⟨4, ([(-1320000000000)], [0])⟩],
    last := 4 }

end ConwaySoifer.Simplified.Certificates.Data
