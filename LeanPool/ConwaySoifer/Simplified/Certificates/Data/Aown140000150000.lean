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
def Aown140000150000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 7 50), hi := (mkRat 3 20), den := 9000000000000,
    steps := [
      ⟨0, ([(-750000000000)], [330000000000])⟩,
      ⟨0, ([(-750000000000)], [420000000000])⟩,
      ⟨0, ([(-420000000000)], [(-330000000000)])⟩,
      ⟨0, ([(-420000000000)], [750000000000])⟩,
      ⟨0, ([(-330000000000)], [750000000000])⟩,
      ⟨2, ([0], [7965000000000])⟩,
      ⟨0, ([330000000000], [(-750000000000)])⟩,
      ⟨0, ([420000000000], [(-750000000000)])⟩,
      ⟨2, ([2610000000000], [6390000000000])⟩,
      ⟨6, ([9000000000000], [(-6390000000000)])⟩,
      ⟨1, ([9000000000000], [4665000000000])⟩,
      ⟨7, ([9000000000000], [7080000000000])⟩,
      ⟨0, ([1410000000000], [0])⟩,
      ⟨2, ([2895000000000], [6105000000000])⟩,
      ⟨2, ([7185000000000], [1440000000000])⟩,
      ⟨2, ([7455000000000], [1125000000000])⟩,
      ⟨0, ([420000000000], [6330000000000])⟩,
      ⟨0, ([2625000000000], [4695000000000])⟩,
      ⟨0, ([5250000000000], [2070000000000])⟩,
      ⟨0, ([6000000000000], [1260000000000])⟩,
      ⟨0, ([6750000000000], [420000000000])⟩,
      ⟨6, ([930000000000], [(-930000000000)])⟩,
      ⟨6, ([5010000000000], [(-1260000000000)])⟩,
      ⟨6, ([6375000000000], [(-1440000000000)])⟩],
    last := 6 }

end ConwaySoifer.Simplified.Certificates.Data
