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
def Sint190000200000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 19 100), hi := (mkRat 1 5), den := 9000000000000,
    steps := [
      ⟨3, ([(-2895000000000)], [9000000000000])⟩,
      ⟨0, ([(-945000000000)], [375000000000])⟩,
      ⟨0, ([375000000000], [(-945000000000)])⟩,
      ⟨0, ([375000000000], [6060000000000])⟩,
      ⟨0, ([435000000000], [6000000000000])⟩,
      ⟨0, ([570000000000], [(-945000000000)])⟩,
      ⟨0, ([570000000000], [5805000000000])⟩,
      ⟨0, ([945000000000], [(-570000000000)])⟩,
      ⟨8, ([(-12015000000000)], [9000000000000])⟩,
      ⟨4, ([(-8145000000000)], [3825000000000])⟩,
      ⟨4, ([(-5250000000000)], [1380000000000])⟩,
      ⟨4, ([(-4875000000000)], [1005000000000])⟩,
      ⟨4, ([(-4500000000000)], [570000000000])⟩,
      ⟨3, ([(-3420000000000)], [8250000000000])⟩,
      ⟨8, ([(-13680000000000)], [4680000000000])⟩,
      ⟨5, ([(-3735000000000)], [(-5265000000000)])⟩,
      ⟨5, ([(-750000000000)], [(-5130000000000)])⟩,
      ⟨5, ([(-495000000000)], [(-5130000000000)])⟩,
      ⟨4, ([(-9000000000000)], [4953000000000])⟩,
      ⟨4, ([(-4275000000000)], [375000000000])⟩,
      ⟨6, ([5329800000000], [(-5922000000000)])⟩,
      ⟨8, ([(-11250000000000)], [2250000000000])⟩,
      ⟨3, ([(-8460000000000)], [6750000000000])⟩,
      ⟨5, ([(-5130000000000)], [(-3870000000000)])⟩,
      ⟨5, ([(-1005000000000)], [(-3870000000000)])⟩,
      ⟨5, ([(-570000000000)], [(-3930000000000)])⟩,
      ⟨9, ([9000000000000], [(-15180000000000)])⟩,
      ⟨4, ([(-4665000000000)], [(-1710000000000)])⟩,
      ⟨0, ([(-1710000000000)], [5175000000000])⟩,
      ⟨9, ([3870000000000], [(-12870000000000)])⟩,
      ⟨6, ([3870000000000], [(-8625000000000)])⟩,
      ⟨6, ([3870000000000], [(-5250000000000)])⟩,
      ⟨6, ([3930000000000], [(-4500000000000)])⟩,
      ⟨0, ([(-1230000000000)], [375000000000])⟩,
      ⟨0, ([(-855000000000)], [(-270000000000)])⟩,
      ⟨1, ([9000000000000], [(-5130000000000)])⟩,
      ⟨0, ([2715000000000], [4125000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
