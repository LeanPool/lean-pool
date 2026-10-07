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
def Aown130000135000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 13 100), hi := (mkRat 27 200), den := 9000000000000,
    steps := [
      ⟨0, ([540000000000], [(-540000000000)])⟩,
      ⟨0, ([1170000000000], [0])⟩,
      ⟨2, ([7573500000000], [841500000000])⟩,
      ⟨4, ([(-7830000000000)], [0])⟩,
      ⟨3, ([(-2085000000000)], [9000000000000])⟩,
      ⟨0, ([519000000000], [6375000000000])⟩,
      ⟨0, ([645000000000], [6375000000000])⟩,
      ⟨0, ([1500000000000], [5745000000000])⟩,
      ⟨0, ([2820000000000], [4680000000000])⟩,
      ⟨0, ([4680000000000], [2820000000000])⟩,
      ⟨0, ([6870000000000], [375000000000])⟩,
      ⟨8, ([(-11106000000000)], [8856000000000])⟩,
      ⟨3, ([(-1875000000000)], [8220000000000])⟩,
      ⟨4, ([(-900000000000)], [120000000000])⟩,
      ⟨3, ([(-900000000000)], [1290000000000])⟩,
      ⟨0, ([(-8625000000000)], [7245000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
