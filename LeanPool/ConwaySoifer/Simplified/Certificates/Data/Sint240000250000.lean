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
def Sint240000250000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 6 25), hi := (mkRat 1 4), den := 9000000000000,
    steps := [
      ⟨3, ([(-3495000000000)], [9000000000000])⟩,
      ⟨0, ([(-1125000000000)], [405000000000])⟩,
      ⟨0, ([360000000000], [5640000000000])⟩,
      ⟨0, ([405000000000], [(-1125000000000)])⟩,
      ⟨0, ([750000000000], [5400000000000])⟩,
      ⟨0, ([930000000000], [(-930000000000)])⟩,
      ⟨0, ([1125000000000], [(-720000000000)])⟩,
      ⟨8, ([(-12513000000000)], [9000000000000])⟩,
      ⟨4, ([(-8280000000000)], [3375000000000])⟩,
      ⟨4, ([(-4845000000000)], [720000000000])⟩,
      ⟨4, ([(-4500000000000)], [360000000000])⟩,
      ⟨3, ([(-3600000000000)], [8625000000000])⟩,
      ⟨8, ([(-13890000000000)], [4890000000000])⟩,
      ⟨3, ([(-8250000000000)], [6480000000000])⟩,
      ⟨5, ([(-375000000000)], [(-4737000000000)])⟩,
      ⟨4, ([(-9000000000000)], [4215000000000])⟩,
      ⟨4, ([(-4320000000000)], [195000000000])⟩,
      ⟨5, ([(-3330000000000)], [(-5670000000000)])⟩,
      ⟨0, ([225000000000], [5400000000000])⟩,
      ⟨9, ([4860000000000], [(-13860000000000)])⟩,
      ⟨9, ([5400000000000], [(-13650000000000)])⟩,
      ⟨6, ([5625000000000], [(-8280000000000)])⟩,
      ⟨5, ([(-4215000000000)], [(-4785000000000)])⟩,
      ⟨5, ([(-4125000000000)], [(-4155000000000)])⟩,
      ⟨5, ([0], [(-2385000000000)])⟩,
      ⟨6, ([4890000000000], [(-5250000000000)])⟩,
      ⟨9, ([7875000000000], [(-14355000000000)])⟩,
      ⟨9, ([9000000000000], [(-14760000000000)])⟩,
      ⟨4, ([(-3750000000000)], [(-2160000000000)])⟩,
      ⟨4, ([(-2520000000000)], [(-1605000000000)])⟩,
      ⟨6, ([2385000000000], [(-5625000000000)])⟩,
      ⟨6, ([2520000000000], [(-4125000000000)])⟩,
      ⟨6, ([2625000000000], [(-6513000000000)])⟩,
      ⟨6, ([3240000000000], [(-8490000000000)])⟩,
      ⟨9, ([3375000000000], [(-12375000000000)])⟩,
      ⟨6, ([3375000000000], [(-8775000000000)])⟩,
      ⟨5, ([(-4830000000000)], [(-4170000000000)])⟩,
      ⟨0, ([(-1815000000000)], [0])⟩,
      ⟨1, ([9000000000000], [(-6615000000000)])⟩,
      ⟨0, ([3375000000000], [3240000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
