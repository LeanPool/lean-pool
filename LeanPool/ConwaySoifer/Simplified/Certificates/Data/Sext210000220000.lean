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
def Sext210000220000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 21 100), hi := (mkRat 11 50), den := 9000000000000,
    steps := [
      ⟨0, ([(-1005000000000)], [375000000000])⟩,
      ⟨0, ([(-1005000000000)], [630000000000])⟩,
      ⟨0, ([(-630000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-630000000000)], [1005000000000])⟩,
      ⟨0, ([(-375000000000)], [1005000000000])⟩,
      ⟨0, ([375000000000], [630000000000])⟩,
      ⟨0, ([6000000000000], [(-5670000000000)])⟩,
      ⟨0, ([6165000000000], [(-5790000000000)])⟩,
      ⟨0, ([6375000000000], [(-5670000000000)])⟩,
      ⟨9, ([8250000000000], [(-10140000000000)])⟩,
      ⟨9, ([9000000000000], [(-10185000000000)])⟩,
      ⟨5, ([5250000000000], [(-8652000000000)])⟩,
      ⟨5, ([5865000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-4455000000000)], [(-4545000000000)])⟩,
      ⟨4, ([(-3870000000000)], [(-630000000000)])⟩,
      ⟨8, ([(-12975000000000)], [3975000000000])⟩,
      ⟨3, ([(-8250000000000)], [3975000000000])⟩,
      ⟨3, ([(-4725000000000)], [3975000000000])⟩,
      ⟨5, ([(-1770000000000)], [(-6480000000000)])⟩,
      ⟨8, ([(-13920000000000)], [9000000000000])⟩,
      ⟨2, ([(-4155000000000)], [9000000000000])⟩,
      ⟨4, ([(-4125000000000)], [(-150000000000)])⟩,
      ⟨2, ([(-750000000000)], [5670000000000])⟩,
      ⟨0, ([3330000000000], [(-4875000000000)])⟩,
      ⟨0, ([6165000000000], [(-6000000000000)])⟩,
      ⟨3, ([(-9000000000000)], [3945000000000])⟩,
      ⟨4, ([(-3750000000000)], [(-630000000000)])⟩,
      ⟨3, ([(-2115000000000)], [2115000000000])⟩,
      ⟨7, ([4875000000000], [8850000000000])⟩,
      ⟨1, ([5175000000000], [2835000000000])⟩,
      ⟨1, ([5220000000000], [1530000000000])⟩,
      ⟨8, ([(-10545000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [3855000000000])⟩,
      ⟨2, ([(-5895000000000)], [9000000000000])⟩,
      ⟨4, ([(-5625000000000)], [1890000000000])⟩,
      ⟨2, ([(-3001500000000)], [5220000000000])⟩,
      ⟨4, ([(-2835000000000)], [1125000000000])⟩,
      ⟨4, ([(-2223000000000)], [0])⟩,
      ⟨2, ([(-1890000000000)], [4125000000000])⟩,
      ⟨0, ([6480000000000], [(-5580000000000)])⟩,
      ⟨7, ([9000000000000], [6750000000000])⟩,
      ⟨8, ([(-11502000000000)], [2502000000000])⟩,
      ⟨8, ([(-10440000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [3402000000000])⟩,
      ⟨2, ([(-6030000000000)], [9000000000000])⟩,
      ⟨3, ([(-4485000000000)], [6375000000000])⟩,
      ⟨0, ([(-1773000000000)], [0])⟩,
      ⟨0, ([(-1530000000000)], [630000000000])⟩,
      ⟨1, ([2220000000000], [3780000000000])⟩,
      ⟨7, ([2250000000000], [9000000000000])⟩,
      ⟨1, ([2340000000000], [6375000000000])⟩,
      ⟨0, ([4725000000000], [(-2625000000000)])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
