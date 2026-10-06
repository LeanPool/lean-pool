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
def Aown160000170000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 4 25), hi := (mkRat 17 100), den := 9000000000000,
    steps := [
      ⟨0, ([(-660000000000)], [0])⟩,
      ⟨0, ([(-660000000000)], [660000000000])⟩,
      ⟨0, ([0], [(-660000000000)])⟩,
      ⟨0, ([0], [660000000000])⟩,
      ⟨0, ([660000000000], [(-660000000000)])⟩,
      ⟨0, ([1440000000000], [0])⟩,
      ⟨2, ([3000000000000], [6000000000000])⟩,
      ⟨2, ([7125000000000], [1395000000000])⟩,
      ⟨6, ([9000000000000], [(-5985000000000)])⟩,
      ⟨1, ([9000000000000], [4680000000000])⟩,
      ⟨7, ([9000000000000], [6840000000000])⟩,
      ⟨3, ([(-2820000000000)], [9000000000000])⟩,
      ⟨0, ([0], [1440000000000])⟩,
      ⟨5, ([1170000000000], [(-8250000000000)])⟩,
      ⟨0, ([2592000000000], [1533000000000])⟩,
      ⟨2, ([3285000000000], [5715000000000])⟩,
      ⟨0, ([4320000000000], [1500000000000])⟩,
      ⟨0, ([5310000000000], [1440000000000])⟩,
      ⟨2, ([5790000000000], [3210000000000])⟩,
      ⟨0, ([6390000000000], [360000000000])⟩,
      ⟨2, ([7125000000000], [1440000000000])⟩,
      ⟨9, ([8385000000000], [(-14760000000000)])⟩,
      ⟨6, ([9000000000000], [(-5715000000000)])⟩,
      ⟨8, ([(-11820000000000)], [9000000000000])⟩,
      ⟨4, ([(-8040000000000)], [3825000000000])⟩,
      ⟨4, ([(-3750000000000)], [480000000000])⟩,
      ⟨3, ([(-2805000000000)], [9000000000000])⟩,
      ⟨3, ([(-2250000000000)], [2970000000000])⟩,
      ⟨5, ([342000000000], [(-6750000000000)])⟩,
      ⟨0, ([495000000000], [5625000000000])⟩,
      ⟨5, ([1530000000000], [(-8280000000000)])⟩,
      ⟨0, ([2955000000000], [4125000000000])⟩,
      ⟨2, ([5250000000000], [2520000000000])⟩,
      ⟨6, ([6840000000000], [(-3090000000000)])⟩,
      ⟨2, ([6915000000000], [1125000000000])⟩,
      ⟨6, ([9000000000000], [(-3315000000000)])⟩,
      ⟨8, ([(-12135000000000)], [3135000000000])⟩,
      ⟨8, ([(-11445000000000)], [9000000000000])⟩,
      ⟨4, ([(-8385000000000)], [5760000000000])⟩,
      ⟨4, ([(-7470000000000)], [(-1530000000000)])⟩,
      ⟨3, ([(-5400000000000)], [4275000000000])⟩,
      ⟨5, ([(-4380000000000)], [(-4620000000000)])⟩,
      ⟨3, ([(-2460000000000)], [9000000000000])⟩,
      ⟨0, ([(-1440000000000)], [5625000000000])⟩,
      ⟨0, ([(-1185000000000)], [7560000000000])⟩,
      ⟨5, ([0], [(-1335000000000)])⟩,
      ⟨6, ([1275000000000], [(-1275000000000)])⟩,
      ⟨5, ([4125000000000], [(-8040000000000)])⟩],
    last := 5 }

end ConwaySoifer.Simplified.Certificates.Data
