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
def Aown230000240000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 23 100), hi := (mkRat 6 25), den := 9000000000000,
    steps := [
      ⟨0, ([(-1065000000000)], [375000000000])⟩,
      ⟨0, ([(-1065000000000)], [690000000000])⟩,
      ⟨0, ([(-900000000000)], [900000000000])⟩,
      ⟨0, ([(-750000000000)], [(-285000000000)])⟩,
      ⟨0, ([(-375000000000)], [(-690000000000)])⟩,
      ⟨0, ([0], [(-900000000000)])⟩,
      ⟨0, ([285000000000], [(-1035000000000)])⟩,
      ⟨0, ([375000000000], [(-1065000000000)])⟩,
      ⟨0, ([690000000000], [(-1065000000000)])⟩,
      ⟨2, ([5385000000000], [3615000000000])⟩,
      ⟨2, ([6210000000000], [2415000000000])⟩,
      ⟨2, ([6375000000000], [2070000000000])⟩,
      ⟨1, ([9000000000000], [4800000000000])⟩,
      ⟨7, ([9000000000000], [5835000000000])⟩,
      ⟨2, ([351000000000], [9000000000000])⟩,
      ⟨0, ([360000000000], [4500000000000])⟩,
      ⟨2, ([1335000000000], [9000000000000])⟩,
      ⟨0, ([2490000000000], [3750000000000])⟩,
      ⟨0, ([5175000000000], [750000000000])⟩,
      ⟨0, ([5274000000000], [351000000000])⟩,
      ⟨2, ([6405000000000], [1875000000000])⟩,
      ⟨2, ([6555000000000], [2070000000000])⟩,
      ⟨3, ([(-3399000000000)], [9000000000000])⟩,
      ⟨4, ([(-2010000000000)], [0])⟩,
      ⟨3, ([(-1995000000000)], [1995000000000])⟩,
      ⟨0, ([270000000000], [5625000000000])⟩,
      ⟨0, ([2760000000000], [3750000000000])⟩,
      ⟨0, ([(-6000000000000)], [3930000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
