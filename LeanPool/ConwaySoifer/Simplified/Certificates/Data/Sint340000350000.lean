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
def Sint340000350000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 17 50), hi := (mkRat 7 20), den := 9000000000000,
    steps := [
      ⟨3, ([(-4545000000000)], [8625000000000])⟩,
      ⟨3, ([(-4530000000000)], [9000000000000])⟩,
      ⟨0, ([(-1530000000000)], [750000000000])⟩,
      ⟨0, ([(-780000000000)], [(-750000000000)])⟩,
      ⟨0, ([180000000000], [4875000000000])⟩,
      ⟨0, ([330000000000], [4920000000000])⟩,
      ⟨0, ([633000000000], [4875000000000])⟩,
      ⟨0, ([750000000000], [(-1530000000000)])⟩,
      ⟨0, ([750000000000], [4758000000000])⟩,
      ⟨0, ([1530000000000], [(-780000000000)])⟩,
      ⟨0, ([1530000000000], [(-750000000000)])⟩,
      ⟨8, ([(-13590000000000)], [9000000000000])⟩,
      ⟨4, ([(-5055000000000)], [180000000000])⟩,
      ⟨3, ([(-4590000000000)], [8250000000000])⟩,
      ⟨5, ([0], [(-2835000000000)])⟩,
      ⟨8, ([(-14220000000000)], [5220000000000])⟩,
      ⟨4, ([(-8625000000000)], [2880000000000])⟩,
      ⟨4, ([(-5508000000000)], [(-3492000000000)])⟩,
      ⟨4, ([(-4665000000000)], [0])⟩,
      ⟨4, ([(-3750000000000)], [(-3240000000000)])⟩,
      ⟨4, ([(-3000000000000)], [(-2508000000000)])⟩,
      ⟨4, ([(-2880000000000)], [(-2370000000000)])⟩,
      ⟨4, ([(-2880000000000)], [(-1620000000000)])⟩,
      ⟨6, ([2835000000000], [(-4875000000000)])⟩,
      ⟨9, ([3330000000000], [(-12330000000000)])⟩,
      ⟨8, ([(-10560000000000)], [1560000000000])⟩,
      ⟨3, ([(-7740000000000)], [4500000000000])⟩,
      ⟨3, ([(-7650000000000)], [4500000000000])⟩,
      ⟨5, ([(-4080000000000)], [(-4920000000000)])⟩,
      ⟨5, ([3240000000000], [(-8415000000000)])⟩,
      ⟨5, ([3375000000000], [(-8883000000000)])⟩,
      ⟨4, ([(-9000000000000)], [3480000000000])⟩,
      ⟨4, ([(-3750000000000)], [(-3900000000000)])⟩,
      ⟨4, ([(-3492000000000)], [(-3633000000000)])⟩,
      ⟨0, ([(-3240000000000)], [4365000000000])⟩,
      ⟨0, ([(-3465000000000)], [0])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
