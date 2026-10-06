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
def Sext180000190000 : CertData :=
  { case := Case.Sext,
    lo := (mkRat 9 50), hi := (mkRat 19 100), den := 9000000000000,
    steps := [
      ⟨0, ([(-915000000000)], [375000000000])⟩,
      ⟨0, ([(-915000000000)], [540000000000])⟩,
      ⟨0, ([(-735000000000)], [735000000000])⟩,
      ⟨0, ([(-540000000000)], [(-375000000000)])⟩,
      ⟨0, ([(-540000000000)], [915000000000])⟩,
      ⟨0, ([(-375000000000)], [915000000000])⟩,
      ⟨0, ([0], [735000000000])⟩,
      ⟨0, ([375000000000], [540000000000])⟩,
      ⟨0, ([6480000000000], [(-6105000000000)])⟩,
      ⟨0, ([6570000000000], [(-6000000000000)])⟩,
      ⟨9, ([8580000000000], [(-10080000000000)])⟩,
      ⟨9, ([9000000000000], [(-9990000000000)])⟩,
      ⟨5, ([4875000000000], [(-8115000000000)])⟩,
      ⟨5, ([6210000000000], [(-9000000000000)])⟩,
      ⟨4, ([(-3825000000000)], [(-5175000000000)])⟩,
      ⟨4, ([(-3750000000000)], [(-540000000000)])⟩,
      ⟨4, ([(-3735000000000)], [(-1125000000000)])⟩,
      ⟨8, ([(-12735000000000)], [3735000000000])⟩,
      ⟨3, ([(-8175000000000)], [4050000000000])⟩,
      ⟨3, ([(-7875000000000)], [3735000000000])⟩,
      ⟨3, ([(-4860000000000)], [3735000000000])⟩,
      ⟨3, ([(-4290000000000)], [3750000000000])⟩,
      ⟨5, ([(-1620000000000)], [(-6630000000000)])⟩,
      ⟨8, ([(-13335000000000)], [9000000000000])⟩,
      ⟨3, ([(-8190000000000)], [3750000000000])⟩,
      ⟨2, ([(-4140000000000)], [9000000000000])⟩,
      ⟨4, ([(-3675000000000)], [0])⟩,
      ⟨2, ([(-810000000000)], [5625000000000])⟩,
      ⟨2, ([(-540000000000)], [5415000000000])⟩,
      ⟨0, ([3255000000000], [(-4875000000000)])⟩,
      ⟨0, ([4125000000000], [(-5745000000000)])⟩,
      ⟨8, ([(-12720000000000)], [3720000000000])⟩,
      ⟨8, ([(-11220000000000)], [9000000000000])⟩,
      ⟨3, ([(-9000000000000)], [3705000000000])⟩,
      ⟨3, ([(-6750000000000)], [8190000000000])⟩,
      ⟨2, ([(-5250000000000)], [9000000000000])⟩,
      ⟨3, ([(-4050000000000)], [3675000000000])⟩,
      ⟨4, ([(-2430000000000)], [0])⟩,
      ⟨2, ([(-540000000000)], [5250000000000])⟩,
      ⟨1, ([5010000000000], [750000000000])⟩,
      ⟨1, ([5184000000000], [576000000000])⟩,
      ⟨8, ([(-12105000000000)], [3105000000000])⟩,
      ⟨8, ([(-11115000000000)], [7875000000000])⟩,
      ⟨3, ([(-9000000000000)], [3045000000000])⟩,
      ⟨3, ([(-6630000000000)], [8250000000000])⟩,
      ⟨3, ([(-6000000000000)], [2430000000000])⟩,
      ⟨4, ([(-5745000000000)], [1620000000000])⟩,
      ⟨2, ([(-5310000000000)], [9000000000000])⟩,
      ⟨3, ([(-5130000000000)], [6750000000000])⟩,
      ⟨4, ([(-2250000000000)], [0])⟩,
      ⟨0, ([(-810000000000)], [(-375000000000)])⟩,
      ⟨2, ([(-375000000000)], [4050000000000])⟩,
      ⟨7, ([3750000000000], [8166000000000])⟩,
      ⟨1, ([4365000000000], [810000000000])⟩,
      ⟨7, ([9000000000000], [6210000000000])⟩,
      ⟨8, ([(-11865000000000)], [2865000000000])⟩,
      ⟨8, ([(-9810000000000)], [7125000000000])⟩,
      ⟨3, ([(-9000000000000)], [3000000000000])⟩,
      ⟨2, ([(-6570000000000)], [9000000000000])⟩,
      ⟨3, ([(-5760000000000)], [2250000000000])⟩,
      ⟨3, ([(-4380000000000)], [6000000000000])⟩,
      ⟨4, ([(-3375000000000)], [1620000000000])⟩,
      ⟨0, ([(-1290000000000)], [750000000000])⟩,
      ⟨2, ([(-1125000000000)], [3555000000000])⟩,
      ⟨0, ([(-1110000000000)], [1110000000000])⟩,
      ⟨1, ([2610000000000], [0])⟩,
      ⟨1, ([3750000000000], [4860000000000])⟩,
      ⟨1, ([5175000000000], [(-2745000000000)])⟩],
    last := 1 }

end ConwaySoifer.Simplified.Certificates.Data
