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
def Sext260000270000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 13 50), hi := (mkRat 27 100), den := 9000000000000,
    steps := [
      ⟨0, ([(-1170000000000)], [375000000000])⟩,
      ⟨0, ([(-1170000000000)], [795000000000])⟩,
      ⟨0, ([(-795000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-795000000000)], [1170000000000])⟩,
      ⟨0, ([(-375000000000)], [(-795000000000)])⟩,
      ⟨0, ([(-375000000000)], [1170000000000])⟩,
      ⟨0, ([375000000000], [795000000000])⟩,
      ⟨0, ([795000000000], [375000000000])⟩,
      ⟨0, ([5490000000000], [(-5250000000000)])⟩,
      ⟨0, ([5850000000000], [(-5475000000000)])⟩,
      ⟨0, ([6030000000000], [(-5250000000000)])⟩,
      ⟨9, ([8250000000000], [(-10560000000000)])⟩,
      ⟨9, ([9000000000000], [(-10560000000000)])⟩,
      ⟨3, ([(-2505000000000)], [2505000000000])⟩,
      ⟨5, ([4788000000000], [(-8625000000000)])⟩,
      ⟨5, ([5310000000000], [(-9000000000000)])⟩,
      ⟨8, ([(-12837000000000)], [9000000000000])⟩,
      ⟨4, ([(-6000000000000)], [2340000000000])⟩,
      ⟨4, ([(-5010000000000)], [(-3990000000000)])⟩,
      ⟨4, ([(-4680000000000)], [1875000000000])⟩,
      ⟨4, ([(-4212000000000)], [(-375000000000)])⟩,
      ⟨2, ([(-1695000000000)], [4320000000000])⟩,
      ⟨2, ([(-375000000000)], [4680000000000])⟩,
      ⟨8, ([(-13320000000000)], [4320000000000])⟩,
      ⟨3, ([(-8337000000000)], [4212000000000])⟩,
      ⟨3, ([(-4680000000000)], [6930000000000])⟩,
      ⟨3, ([(-4500000000000)], [6660000000000])⟩,
      ⟨0, ([(-1740000000000)], [0])⟩,
      ⟨8, ([(-9810000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [4320000000000])⟩,
      ⟨4, ([(-4875000000000)], [2340000000000])⟩,
      ⟨0, ([(-1170000000000)], [1125000000000])⟩,
      ⟨5, ([2625000000000], [(-6135000000000)])⟩,
      ⟨5, ([4395000000000], [(-6375000000000)])⟩,
      ⟨1, ([6375000000000], [(-2340000000000)])⟩,
      ⟨4, ([(-3945000000000)], [(-5055000000000)])⟩,
      ⟨0, ([(-2340000000000)], [(-4875000000000)])⟩,
      ⟨0, ([2340000000000], [0])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
