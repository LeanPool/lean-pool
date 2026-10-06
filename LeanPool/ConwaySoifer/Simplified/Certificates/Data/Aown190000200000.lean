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
def Aown190000200000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 19 100), hi := (mkRat 1 5), den := 9000000000000,
    steps := [
      ⟨0, ([(-945000000000)], [375000000000])⟩,
      ⟨0, ([(-945000000000)], [570000000000])⟩,
      ⟨0, ([(-765000000000)], [765000000000])⟩,
      ⟨0, ([(-570000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-375000000000)], [(-570000000000)])⟩,
      ⟨0, ([0], [(-765000000000)])⟩,
      ⟨0, ([375000000000], [(-945000000000)])⟩,
      ⟨0, ([570000000000], [(-945000000000)])⟩,
      ⟨0, ([1710000000000], [0])⟩,
      ⟨2, ([5310000000000], [3690000000000])⟩,
      ⟨2, ([6930000000000], [1500000000000])⟩,
      ⟨1, ([9000000000000], [4755000000000])⟩,
      ⟨7, ([9000000000000], [6435000000000])⟩,
      ⟨3, ([(-3060000000000)], [9000000000000])⟩,
      ⟨0, ([420000000000], [5580000000000])⟩,
      ⟨0, ([2625000000000], [4275000000000])⟩,
      ⟨0, ([3840000000000], [3000000000000])⟩,
      ⟨0, ([5250000000000], [1470000000000])⟩,
      ⟨0, ([6060000000000], [375000000000])⟩,
      ⟨2, ([6840000000000], [1410000000000])⟩,
      ⟨2, ([6915000000000], [1710000000000])⟩,
      ⟨8, ([(-12078000000000)], [9000000000000])⟩,
      ⟨3, ([(-2895000000000)], [9000000000000])⟩,
      ⟨3, ([(-1335000000000)], [1710000000000])⟩,
      ⟨4, ([(-1260000000000)], [0])⟩,
      ⟨0, ([(-8625000000000)], [6465000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
