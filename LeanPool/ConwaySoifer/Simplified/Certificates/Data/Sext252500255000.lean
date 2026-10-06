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
def Sext252500255000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 101 400), hi := (mkRat 51 200), den := 9000000000000,
    steps := [
      ⟨0, ([(-1136250000000)], [375000000000])⟩,
      ⟨0, ([(-1136250000000)], [761250000000])⟩,
      ⟨0, ([(-761250000000)], [(-375000000000)])⟩,
      ⟨0, ([(-761250000000)], [1136250000000])⟩,
      ⟨0, ([(-375000000000)], [(-761250000000)])⟩,
      ⟨0, ([(-375000000000)], [1136250000000])⟩,
      ⟨0, ([375000000000], [761250000000])⟩,
      ⟨0, ([761250000000], [375000000000])⟩,
      ⟨0, ([5970000000000], [(-5625000000000)])⟩,
      ⟨0, ([6007500000000], [(-5250000000000)])⟩,
      ⟨9, ([8250000000000], [(-10515000000000)])⟩,
      ⟨9, ([9000000000000], [(-10465500000000)])⟩,
      ⟨3, ([(-2415000000000)], [2415000000000])⟩,
      ⟨5, ([4909500000000], [(-8625000000000)])⟩,
      ⟨5, ([5445000000000], [(-9000000000000)])⟩,
      ⟨8, ([(-12715500000000)], [9000000000000])⟩,
      ⟨4, ([(-6000000000000)], [2272500000000])⟩,
      ⟨4, ([(-4909500000000)], [1909500000000])⟩,
      ⟨4, ([(-4860000000000)], [(-4140000000000)])⟩,
      ⟨4, ([(-4159500000000)], [(-750000000000)])⟩,
      ⟨4, ([(-4090500000000)], [715500000000])⟩,
      ⟨2, ([(-1515000000000)], [4125000000000])⟩,
      ⟨2, ([(-409500000000)], [4500000000000])⟩,
      ⟨8, ([(-13215000000000)], [4215000000000])⟩,
      ⟨3, ([(-8242500000000)], [4117500000000])⟩,
      ⟨3, ([(-4567500000000)], [6750000000000])⟩,
      ⟨0, ([(-1657500000000)], [0])⟩,
      ⟨8, ([(-9757500000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [4455000000000])⟩,
      ⟨4, ([(-4875000000000)], [2272500000000])⟩,
      ⟨0, ([(-1140000000000)], [1140000000000])⟩,
      ⟨5, ([4090500000000], [(-6340500000000)])⟩,
      ⟨1, ([6375000000000], [(-1920000000000)])⟩,
      ⟨4, ([(-3761250000000)], [(-5238750000000)])⟩,
      ⟨0, ([(-2272500000000)], [(-4875000000000)])⟩,
      ⟨0, ([(-2272500000000)], [900000000000])⟩,
      ⟨0, ([1125000000000], [390000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
