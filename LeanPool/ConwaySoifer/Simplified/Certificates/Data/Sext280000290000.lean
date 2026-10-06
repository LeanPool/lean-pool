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
def Sext280000290000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 7 25), hi := (mkRat 29 100), den := 9000000000000,
    steps := [
      ⟨0, ([(-1260000000000)], [510000000000])⟩,
      ⟨0, ([(-1260000000000)], [750000000000])⟩,
      ⟨0, ([(-1215000000000)], [840000000000])⟩,
      ⟨0, ([(-840000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-750000000000)], [(-510000000000)])⟩,
      ⟨0, ([(-750000000000)], [1260000000000])⟩,
      ⟨0, ([375000000000], [840000000000])⟩,
      ⟨0, ([750000000000], [510000000000])⟩,
      ⟨0, ([5250000000000], [(-5040000000000)])⟩,
      ⟨0, ([5640000000000], [(-5265000000000)])⟩,
      ⟨0, ([6000000000000], [(-5040000000000)])⟩,
      ⟨9, ([7875000000000], [(-10395000000000)])⟩,
      ⟨9, ([9000000000000], [(-10665000000000)])⟩,
      ⟨3, ([(-2580000000000)], [2580000000000])⟩,
      ⟨5, ([4665000000000], [(-8625000000000)])⟩,
      ⟨5, ([5070000000000], [(-9000000000000)])⟩,
      ⟨8, ([(-12675000000000)], [9000000000000])⟩,
      ⟨4, ([(-6270000000000)], [2520000000000])⟩,
      ⟨4, ([(-5220000000000)], [(-3780000000000)])⟩,
      ⟨4, ([(-4536000000000)], [1911000000000])⟩,
      ⟨4, ([(-4125000000000)], [0])⟩,
      ⟨2, ([(-1911000000000)], [4536000000000])⟩,
      ⟨2, ([(-1875000000000)], [4464000000000])⟩,
      ⟨2, ([(-1488000000000)], [4464000000000])⟩,
      ⟨8, ([(-13425000000000)], [4425000000000])⟩,
      ⟨3, ([(-9000000000000)], [6300000000000])⟩,
      ⟨3, ([(-8250000000000)], [4290000000000])⟩,
      ⟨3, ([(-4875000000000)], [7320000000000])⟩,
      ⟨0, ([(-1839000000000)], [0])⟩,
      ⟨8, ([(-9810000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [4410000000000])⟩,
      ⟨4, ([(-3555000000000)], [1680000000000])⟩,
      ⟨2, ([(-3360000000000)], [5985000000000])⟩,
      ⟨0, ([(-828000000000)], [1440000000000])⟩,
      ⟨5, ([3780000000000], [(-6000000000000)])⟩,
      ⟨8, ([(-9735000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [4395000000000])⟩,
      ⟨2, ([(-5535000000000)], [9000000000000])⟩,
      ⟨4, ([(-4875000000000)], [2520000000000])⟩,
      ⟨4, ([(-4089000000000)], [(-4911000000000)])⟩,
      ⟨0, ([(-2520000000000)], [(-4605000000000)])⟩,
      ⟨0, ([(-2520000000000)], [0])⟩,
      ⟨0, ([0], [2286000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
