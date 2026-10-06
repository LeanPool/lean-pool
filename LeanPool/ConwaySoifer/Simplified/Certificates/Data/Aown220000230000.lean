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
def Aown220000230000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 11 50), hi := (mkRat 23 100), den := 9000000000000,
    steps := [
      ⟨0, ([(-1080000000000)], [459000000000])⟩,
      ⟨0, ([(-1035000000000)], [660000000000])⟩,
      ⟨0, ([(-855000000000)], [0])⟩,
      ⟨0, ([(-855000000000)], [855000000000])⟩,
      ⟨0, ([(-660000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-621000000000)], [1080000000000])⟩,
      ⟨0, ([(-540000000000)], [(-540000000000)])⟩,
      ⟨0, ([0], [(-855000000000)])⟩,
      ⟨0, ([375000000000], [(-1035000000000)])⟩,
      ⟨0, ([540000000000], [(-1080000000000)])⟩,
      ⟨0, ([621000000000], [(-1080000000000)])⟩,
      ⟨0, ([1980000000000], [0])⟩,
      ⟨2, ([5385000000000], [3615000000000])⟩,
      ⟨2, ([6030000000000], [2595000000000])⟩,
      ⟨1, ([7215000000000], [660000000000])⟩,
      ⟨6, ([9000000000000], [(-3390000000000)])⟩,
      ⟨1, ([9000000000000], [4755000000000])⟩,
      ⟨7, ([9000000000000], [6030000000000])⟩,
      ⟨3, ([(-6000000000000)], [7920000000000])⟩,
      ⟨0, ([(-465000000000)], [1125000000000])⟩,
      ⟨5, ([0], [(-7260000000000)])⟩,
      ⟨0, ([0], [1290000000000])⟩,
      ⟨2, ([855000000000], [9000000000000])⟩,
      ⟨0, ([4215000000000], [660000000000])⟩,
      ⟨2, ([6360000000000], [1890000000000])⟩,
      ⟨2, ([6645000000000], [1980000000000])⟩,
      ⟨9, ([8130000000000], [(-11880000000000)])⟩,
      ⟨6, ([8595000000000], [(-2970000000000)])⟩,
      ⟨6, ([9000000000000], [(-3090000000000)])⟩,
      ⟨0, ([315000000000], [5625000000000])⟩,
      ⟨5, ([450000000000], [(-4950000000000)])⟩,
      ⟨0, ([2880000000000], [3750000000000])⟩,
      ⟨5, ([3564000000000], [(-8250000000000)])⟩,
      ⟨0, ([4125000000000], [(-1155000000000)])⟩,
      ⟨0, ([5175000000000], [1320000000000])⟩,
      ⟨4, ([(-5655000000000)], [(-3345000000000)])⟩,
      ⟨3, ([(-1320000000000)], [900000000000])⟩,
      ⟨3, ([(-1320000000000)], [6570000000000])⟩],
    last := 3 }

end ConwaySoifer.Simplified.Certificates.Data
