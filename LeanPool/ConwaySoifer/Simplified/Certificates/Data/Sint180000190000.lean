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
def Sint180000190000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 9 50), hi := (mkRat 19 100), den := 9000000000000,
    steps := [
      ⟨3, ([(-2916000000000)], [8916000000000])⟩,
      ⟨3, ([(-2790000000000)], [9000000000000])⟩,
      ⟨0, ([(-915000000000)], [375000000000])⟩,
      ⟨0, ([(-540000000000)], [(-375000000000)])⟩,
      ⟨0, ([375000000000], [(-915000000000)])⟩,
      ⟨0, ([375000000000], [6105000000000])⟩,
      ⟨0, ([540000000000], [(-915000000000)])⟩,
      ⟨0, ([570000000000], [6000000000000])⟩,
      ⟨0, ([915000000000], [(-540000000000)])⟩,
      ⟨8, ([(-11865000000000)], [9000000000000])⟩,
      ⟨4, ([(-7920000000000)], [3420000000000])⟩,
      ⟨4, ([(-4860000000000)], [1125000000000])⟩,
      ⟨4, ([(-4290000000000)], [540000000000])⟩,
      ⟨3, ([(-3240000000000)], [8115000000000])⟩,
      ⟨8, ([(-13710000000000)], [4710000000000])⟩,
      ⟨4, ([(-8175000000000)], [4125000000000])⟩,
      ⟨5, ([(-3330000000000)], [(-5670000000000)])⟩,
      ⟨5, ([(-510000000000)], [(-5250000000000)])⟩,
      ⟨8, ([(-13335000000000)], [4335000000000])⟩,
      ⟨4, ([(-9000000000000)], [5184000000000])⟩,
      ⟨4, ([(-4140000000000)], [414000000000])⟩,
      ⟨5, ([(-4080000000000)], [(-4920000000000)])⟩,
      ⟨6, ([5460000000000], [(-6000000000000)])⟩,
      ⟨8, ([(-11160000000000)], [2160000000000])⟩,
      ⟨3, ([(-8250000000000)], [6630000000000])⟩,
      ⟨5, ([(-5250000000000)], [(-3750000000000)])⟩,
      ⟨5, ([(-4140000000000)], [(-3735000000000)])⟩,
      ⟨5, ([(-540000000000)], [(-3750000000000)])⟩,
      ⟨9, ([4710000000000], [(-12960000000000)])⟩,
      ⟨6, ([5010000000000], [(-5760000000000)])⟩,
      ⟨6, ([5085000000000], [(-5625000000000)])⟩,
      ⟨9, ([8625000000000], [(-15105000000000)])⟩,
      ⟨9, ([9000000000000], [(-15345000000000)])⟩,
      ⟨4, ([(-3240000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-1620000000000)], [4875000000000])⟩,
      ⟨5, ([(-414000000000)], [(-3726000000000)])⟩,
      ⟨9, ([3735000000000], [(-12735000000000)])⟩,
      ⟨6, ([3735000000000], [(-7875000000000)])⟩,
      ⟨6, ([3750000000000], [(-8610000000000)])⟩,
      ⟨6, ([3750000000000], [(-4290000000000)])⟩,
      ⟨6, ([3765000000000], [(-8625000000000)])⟩,
      ⟨1, ([9000000000000], [(-2370000000000)])⟩,
      ⟨5, ([(-5334000000000)], [(-3666000000000)])⟩,
      ⟨4, ([(-4500000000000)], [(-1620000000000)])⟩,
      ⟨0, ([(-1185000000000)], [375000000000])⟩,
      ⟨0, ([(-810000000000)], [(-315000000000)])⟩,
      ⟨0, ([990000000000], [5760000000000])⟩,
      ⟨1, ([4845000000000], [(-720000000000)])⟩,
      ⟨1, ([9000000000000], [(-5250000000000)])⟩,
      ⟨0, ([2625000000000], [3855000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
