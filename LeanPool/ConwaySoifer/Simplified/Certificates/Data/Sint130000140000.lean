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
def Sint130000140000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 13 100), hi := (mkRat 7 50), den := 9000000000000,
    steps := [
      ⟨4, ([(-8040000000000)], [0])⟩,
      ⟨3, ([(-2160000000000)], [9000000000000])⟩,
      ⟨0, ([735000000000], [(-360000000000)])⟩,
      ⟨8, ([(-11175000000000)], [9000000000000])⟩,
      ⟨0, ([(-1125000000000)], [5490000000000])⟩,
      ⟨0, ([(-390000000000)], [5265000000000])⟩,
      ⟨0, ([(-360000000000)], [5235000000000])⟩,
      ⟨4, ([(-7830000000000)], [3000000000000])⟩,
      ⟨4, ([(-5955000000000)], [780000000000])⟩,
      ⟨8, ([(-15645000000000)], [6645000000000])⟩,
      ⟨3, ([(-8415000000000)], [7573500000000])⟩,
      ⟨5, ([(-2115000000000)], [(-6885000000000)])⟩,
      ⟨5, ([(-645000000000)], [(-6375000000000)])⟩,
      ⟨5, ([(-519000000000)], [(-6375000000000)])⟩,
      ⟨4, ([(-9000000000000)], [5640000000000])⟩,
      ⟨4, ([(-5835000000000)], [585000000000])⟩,
      ⟨0, ([(-1170000000000)], [5670000000000])⟩,
      ⟨0, ([(-585000000000)], [5625000000000])⟩,
      ⟨0, ([(-240000000000)], [5490000000000])⟩,
      ⟨6, ([6735000000000], [(-7125000000000)])⟩,
      ⟨6, ([6750000000000], [(-7110000000000)])⟩,
      ⟨6, ([7020000000000], [(-8145000000000)])⟩,
      ⟨8, ([(-14895000000000)], [5895000000000])⟩,
      ⟨3, ([(-8625000000000)], [7455000000000])⟩,
      ⟨4, ([(-5490000000000)], [615000000000])⟩,
      ⟨5, ([(-5460000000000)], [(-3540000000000)])⟩,
      ⟨5, ([(-780000000000)], [(-4095000000000)])⟩,
      ⟨0, ([375000000000], [(-735000000000)])⟩,
      ⟨9, ([9000000000000], [(-16110000000000)])⟩,
      ⟨5, ([(-5625000000000)], [(-3375000000000)])⟩,
      ⟨4, ([(-5175000000000)], [(-1170000000000)])⟩,
      ⟨4, ([(-4395000000000)], [(-780000000000)])⟩,
      ⟨0, ([(-1170000000000)], [5175000000000])⟩,
      ⟨0, ([(-1170000000000)], [6045000000000])⟩,
      ⟨0, ([(-360000000000)], [5985000000000])⟩,
      ⟨9, ([3555000000000], [(-12555000000000)])⟩,
      ⟨6, ([3570000000000], [(-8250000000000)])⟩,
      ⟨6, ([4005000000000], [(-5175000000000)])⟩,
      ⟨6, ([4095000000000], [(-4875000000000)])⟩,
      ⟨5, ([(-5640000000000)], [(-3360000000000)])⟩,
      ⟨0, ([(-780000000000)], [0])⟩,
      ⟨5, ([(-390000000000)], [(-3735000000000)])⟩,
      ⟨9, ([3375000000000], [(-12375000000000)])⟩,
      ⟨6, ([3375000000000], [(-8415000000000)])⟩,
      ⟨1, ([7440000000000], [(-2625000000000)])⟩,
      ⟨1, ([9000000000000], [(-4620000000000)])⟩,
      ⟨0, ([375000000000], [6645000000000])⟩,
      ⟨0, ([3000000000000], [4440000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
