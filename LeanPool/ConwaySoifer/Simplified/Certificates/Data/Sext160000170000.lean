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
def Sext160000170000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 4 25), hi := (mkRat 17 100), den := 9000000000000,
    steps := [
      ⟨0, ([(-660000000000)], [0])⟩,
      ⟨0, ([(-660000000000)], [660000000000])⟩,
      ⟨0, ([0], [660000000000])⟩,
      ⟨0, ([480000000000], [375000000000])⟩,
      ⟨0, ([6750000000000], [(-6270000000000)])⟩,
      ⟨9, ([8625000000000], [(-9960000000000)])⟩,
      ⟨9, ([9000000000000], [(-9885000000000)])⟩,
      ⟨3, ([(-7560000000000)], [7560000000000])⟩,
      ⟨5, ([4530000000000], [(-8280000000000)])⟩,
      ⟨5, ([6465000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-3825000000000)], [(-5175000000000)])⟩,
      ⟨4, ([(-3750000000000)], [(-570000000000)])⟩,
      ⟨0, ([3750000000000], [(-4710000000000)])⟩,
      ⟨8, ([(-12765000000000)], [3765000000000])⟩,
      ⟨8, ([(-12600000000000)], [3825000000000])⟩,
      ⟨3, ([(-8070000000000)], [3750000000000])⟩,
      ⟨3, ([(-4320000000000)], [3750000000000])⟩,
      ⟨4, ([(-3600000000000)], [(-750000000000)])⟩,
      ⟨5, ([(-1440000000000)], [(-7125000000000)])⟩,
      ⟨0, ([(-480000000000)], [(-375000000000)])⟩,
      ⟨8, ([(-11640000000000)], [9000000000000])⟩,
      ⟨3, ([(-8100000000000)], [3600000000000])⟩,
      ⟨4, ([(-5400000000000)], [1125000000000])⟩,
      ⟨2, ([(-4590000000000)], [9000000000000])⟩,
      ⟨3, ([(-4350000000000)], [3600000000000])⟩,
      ⟨4, ([(-3255000000000)], [0])⟩,
      ⟨2, ([(-720000000000)], [5595000000000])⟩,
      ⟨0, ([3735000000000], [(-5175000000000)])⟩,
      ⟨5, ([5040000000000], [(-8040000000000)])⟩,
      ⟨8, ([(-12420000000000)], [3420000000000])⟩,
      ⟨8, ([(-11385000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [3420000000000])⟩,
      ⟨3, ([(-8520000000000)], [3375000000000])⟩,
      ⟨3, ([(-7185000000000)], [8625000000000])⟩,
      ⟨3, ([(-6750000000000)], [8040000000000])⟩,
      ⟨2, ([(-5400000000000)], [9000000000000])⟩,
      ⟨4, ([(-3750000000000)], [(-5250000000000)])⟩,
      ⟨3, ([(-3750000000000)], [3270000000000])⟩,
      ⟨4, ([(-3465000000000)], [(-5535000000000)])⟩,
      ⟨4, ([(-2565000000000)], [0])⟩,
      ⟨0, ([(-960000000000)], [375000000000])⟩,
      ⟨0, ([(-885000000000)], [0])⟩,
      ⟨0, ([(-750000000000)], [(-210000000000)])⟩,
      ⟨0, ([(-375000000000)], [855000000000])⟩,
      ⟨1, ([4665000000000], [960000000000])⟩,
      ⟨8, ([(-12015000000000)], [3015000000000])⟩,
      ⟨8, ([(-10920000000000)], [7545000000000])⟩,
      ⟨3, ([(-9000000000000)], [2910000000000])⟩,
      ⟨3, ([(-6750000000000)], [2592000000000])⟩,
      ⟨2, ([(-5745000000000)], [9000000000000])⟩,
      ⟨2, ([(-1920000000000)], [5175000000000])⟩,
      ⟨7, ([3600000000000], [8625000000000])⟩,
      ⟨1, ([3750000000000], [4290000000000])⟩,
      ⟨0, ([7080000000000], [(-5580000000000)])⟩,
      ⟨1, ([7125000000000], [(-4245000000000)])⟩,
      ⟨0, ([2160000000000], [0])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
