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
def Aown180000190000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 9 50), hi := (mkRat 19 100), den := 9000000000000,
    steps := [
      ⟨0, ([(-915000000000)], [375000000000])⟩,
      ⟨0, ([(-915000000000)], [540000000000])⟩,
      ⟨0, ([(-540000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-540000000000)], [915000000000])⟩,
      ⟨0, ([(-375000000000)], [(-540000000000)])⟩,
      ⟨0, ([0], [(-735000000000)])⟩,
      ⟨0, ([375000000000], [(-915000000000)])⟩,
      ⟨0, ([540000000000], [(-915000000000)])⟩,
      ⟨0, ([1620000000000], [0])⟩,
      ⟨2, ([3459000000000], [5541000000000])⟩,
      ⟨2, ([6960000000000], [1500000000000])⟩,
      ⟨6, ([9000000000000], [(-5541000000000)])⟩,
      ⟨1, ([9000000000000], [4710000000000])⟩,
      ⟨7, ([9000000000000], [6570000000000])⟩,
      ⟨3, ([(-3240000000000)], [8865000000000])⟩,
      ⟨3, ([(-3045000000000)], [9000000000000])⟩,
      ⟨0, ([180000000000], [2250000000000])⟩,
      ⟨5, ([1620000000000], [(-8250000000000)])⟩,
      ⟨0, ([3000000000000], [1950000000000])⟩,
      ⟨2, ([4860000000000], [4140000000000])⟩,
      ⟨0, ([4875000000000], [1695000000000])⟩,
      ⟨2, ([5925000000000], [3075000000000])⟩,
      ⟨0, ([6195000000000], [375000000000])⟩,
      ⟨2, ([6750000000000], [1620000000000])⟩,
      ⟨1, ([7500000000000], [420000000000])⟩,
      ⟨9, ([8250000000000], [(-14730000000000)])⟩,
      ⟨6, ([8865000000000], [(-3240000000000)])⟩,
      ⟨6, ([9000000000000], [(-3210000000000)])⟩,
      ⟨8, ([(-12105000000000)], [9000000000000])⟩,
      ⟨4, ([(-7920000000000)], [3420000000000])⟩,
      ⟨4, ([(-4050000000000)], [300000000000])⟩,
      ⟨3, ([(-3000000000000)], [9000000000000])⟩,
      ⟨3, ([(-2250000000000)], [2430000000000])⟩,
      ⟨5, ([540000000000], [(-4290000000000)])⟩,
      ⟨0, ([2250000000000], [4500000000000])⟩,
      ⟨0, ([2625000000000], [4215000000000])⟩,
      ⟨5, ([3240000000000], [(-8115000000000)])⟩,
      ⟨0, ([3840000000000], [3000000000000])⟩,
      ⟨8, ([(-13335000000000)], [4335000000000])⟩,
      ⟨8, ([(-11541000000000)], [9000000000000])⟩,
      ⟨4, ([(-8460000000000)], [5835000000000])⟩,
      ⟨4, ([(-5805000000000)], [(-3195000000000)])⟩,
      ⟨5, ([(-3330000000000)], [(-5670000000000)])⟩,
      ⟨3, ([(-1620000000000)], [1620000000000])⟩,
      ⟨0, ([(-1620000000000)], [5625000000000])⟩,
      ⟨6, ([1305000000000], [(-1305000000000)])⟩,
      ⟨0, ([5460000000000], [(-1500000000000)])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
