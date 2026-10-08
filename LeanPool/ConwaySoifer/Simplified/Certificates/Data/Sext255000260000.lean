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
def Sext255000260000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 51 200), hi := (mkRat 13 50), den := 9000000000000,
    steps := [
      ⟨0, ([(-1147500000000)], [375000000000])⟩,
      ⟨0, ([(-1147500000000)], [772500000000])⟩,
      ⟨0, ([(-772500000000)], [(-375000000000)])⟩,
      ⟨0, ([(-772500000000)], [1147500000000])⟩,
      ⟨0, ([(-375000000000)], [(-772500000000)])⟩,
      ⟨0, ([(-375000000000)], [1147500000000])⟩,
      ⟨0, ([375000000000], [772500000000])⟩,
      ⟨0, ([772500000000], [375000000000])⟩,
      ⟨0, ([5940000000000], [(-5565000000000)])⟩,
      ⟨0, ([6015000000000], [(-5250000000000)])⟩,
      ⟨9, ([8250000000000], [(-10530000000000)])⟩,
      ⟨9, ([9000000000000], [(-10506000000000)])⟩,
      ⟨3, ([(-2430000000000)], [2430000000000])⟩,
      ⟨5, ([4770000000000], [(-8520000000000)])⟩,
      ⟨5, ([5340000000000], [(-9000000000000)])⟩,
      ⟨8, ([(-12756000000000)], [9000000000000])⟩,
      ⟨4, ([(-6000000000000)], [2295000000000])⟩,
      ⟨4, ([(-5625000000000)], [2182500000000])⟩,
      ⟨4, ([(-4920000000000)], [(-4080000000000)])⟩,
      ⟨4, ([(-4869000000000)], [1875000000000])⟩,
      ⟨4, ([(-4215000000000)], [(-375000000000)])⟩,
      ⟨4, ([(-4131000000000)], [375000000000])⟩,
      ⟨8, ([(-13305000000000)], [4305000000000])⟩,
      ⟨3, ([(-7881000000000)], [4131000000000])⟩,
      ⟨0, ([(-1590000000000)], [0])⟩,
      ⟨0, ([(-1500000000000)], [(-180000000000)])⟩,
      ⟨8, ([(-10881000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [4410000000000])⟩,
      ⟨2, ([(-3442500000000)], [6000000000000])⟩,
      ⟨5, ([3442500000000], [(-6375000000000)])⟩,
      ⟨5, ([4125000000000], [(-6420000000000)])⟩,
      ⟨1, ([6375000000000], [(-2295000000000)])⟩,
      ⟨4, ([(-3969000000000)], [(-5031000000000)])⟩,
      ⟨0, ([(-2295000000000)], [(-4875000000000)])⟩,
      ⟨0, ([2295000000000], [0])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
