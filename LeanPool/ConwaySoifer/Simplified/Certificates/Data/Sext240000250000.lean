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
def Sext240000250000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 6 25), hi := (mkRat 1 4), den := 9000000000000,
    steps := [
      ⟨0, ([(-1125000000000)], [405000000000])⟩,
      ⟨0, ([(-1125000000000)], [720000000000])⟩,
      ⟨0, ([(-720000000000)], [(-405000000000)])⟩,
      ⟨0, ([(-720000000000)], [1125000000000])⟩,
      ⟨0, ([(-405000000000)], [(-720000000000)])⟩,
      ⟨0, ([(-405000000000)], [1125000000000])⟩,
      ⟨0, ([405000000000], [720000000000])⟩,
      ⟨0, ([720000000000], [405000000000])⟩,
      ⟨0, ([6000000000000], [(-5640000000000)])⟩,
      ⟨0, ([6150000000000], [(-5400000000000)])⟩,
      ⟨9, ([8190000000000], [(-10440000000000)])⟩,
      ⟨9, ([9000000000000], [(-10365000000000)])⟩,
      ⟨5, ([5025000000000], [(-8625000000000)])⟩,
      ⟨5, ([5505000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-4785000000000)], [(-4215000000000)])⟩,
      ⟨4, ([(-4140000000000)], [(-360000000000)])⟩,
      ⟨4, ([(-4125000000000)], [(-720000000000)])⟩,
      ⟨8, ([(-13320000000000)], [5820000000000])⟩,
      ⟨8, ([(-13230000000000)], [4230000000000])⟩,
      ⟨3, ([(-8250000000000)], [4320000000000])⟩,
      ⟨3, ([(-8085000000000)], [4125000000000])⟩,
      ⟨3, ([(-4680000000000)], [4212000000000])⟩,
      ⟨5, ([(-1905000000000)], [(-6375000000000)])⟩,
      ⟨8, ([(-13815000000000)], [9000000000000])⟩,
      ⟨4, ([(-4125000000000)], [(-195000000000)])⟩,
      ⟨2, ([(-3810000000000)], [9000000000000])⟩,
      ⟨0, ([5625000000000], [(-5400000000000)])⟩,
      ⟨3, ([(-9000000000000)], [6240000000000])⟩,
      ⟨3, ([(-8445000000000)], [4320000000000])⟩,
      ⟨3, ([(-8280000000000)], [4155000000000])⟩,
      ⟨3, ([(-2385000000000)], [2385000000000])⟩,
      ⟨8, ([(-10755000000000)], [9000000000000])⟩,
      ⟨4, ([(-5910000000000)], [2160000000000])⟩,
      ⟨2, ([(-5625000000000)], [9000000000000])⟩,
      ⟨4, ([(-4125000000000)], [1605000000000])⟩,
      ⟨2, ([(-3888000000000)], [6513000000000])⟩,
      ⟨2, ([(-3240000000000)], [5625000000000])⟩,
      ⟨2, ([(-1875000000000)], [4320000000000])⟩,
      ⟨3, ([(-9000000000000)], [4170000000000])⟩,
      ⟨0, ([(-1815000000000)], [0])⟩,
      ⟨1, ([2385000000000], [5175000000000])⟩,
      ⟨7, ([2388000000000], [9000000000000])⟩,
      ⟨1, ([2505000000000], [6120000000000])⟩,
      ⟨0, ([6615000000000], [(-3240000000000)])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
