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
def Aown135000140000 : CertData :=
  { case := Case.Aown,
    lo := (mkRat 27 200), hi := (mkRat 7 50), den := 9000000000000,
    steps := [
      ⟨0, ([570000000000], [(-570000000000)])⟩,
      ⟨2, ([2535000000000], [6465000000000])⟩,
      ⟨2, ([7553250000000], [839250000000])⟩,
      ⟨1, ([9000000000000], [4665000000000])⟩,
      ⟨0, ([438000000000], [6375000000000])⟩,
      ⟨0, ([3037500000000], [4462500000000])⟩,
      ⟨0, ([4462500000000], [3037500000000])⟩,
      ⟨0, ([4860000000000], [2625000000000])⟩,
      ⟨0, ([7005000000000], [375000000000])⟩,
      ⟨6, ([750000000000], [(-810000000000)])⟩,
      ⟨6, ([3087000000000], [(-900000000000)])⟩],
    last := 6 }

end ConwaySoifer.Simplified.Certificates.Data
