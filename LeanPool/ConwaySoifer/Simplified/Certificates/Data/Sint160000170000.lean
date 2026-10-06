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
def Sint160000170000 : CertData :=
  { case := Case.Sint,
    lo := (mkRat 4 25), hi := (mkRat 17 100), den := 9000000000000,
    steps := [
      ⟨3, ([(-2592000000000)], [8967000000000])⟩,
      ⟨3, ([(-2535000000000)], [9000000000000])⟩,
      ⟨0, ([(-660000000000)], [0])⟩,
      ⟨0, ([480000000000], [6270000000000])⟩,
      ⟨0, ([660000000000], [(-660000000000)])⟩,
      ⟨0, ([855000000000], [(-375000000000)])⟩,
      ⟨8, ([(-11592000000000)], [9000000000000])⟩,
      ⟨4, ([(-8040000000000)], [4020000000000])⟩,
      ⟨4, ([(-4320000000000)], [570000000000])⟩,
      ⟨0, ([(-960000000000)], [4710000000000])⟩,
      ⟨8, ([(-13395000000000)], [4395000000000])⟩,
      ⟨4, ([(-4350000000000)], [750000000000])⟩,
      ⟨5, ([(-3975000000000)], [(-5025000000000)])⟩,
      ⟨0, ([(-855000000000)], [375000000000])⟩,
      ⟨5, ([(-750000000000)], [(-5010000000000)])⟩,
      ⟨4, ([(-9000000000000)], [5160000000000])⟩,
      ⟨4, ([(-4125000000000)], [480000000000])⟩,
      ⟨4, ([(-4125000000000)], [525000000000])⟩,
      ⟨3, ([(-3000000000000)], [8040000000000])⟩,
      ⟨9, ([5010000000000], [(-14010000000000)])⟩,
      ⟨6, ([5175000000000], [(-5895000000000)])⟩,
      ⟨6, ([5175000000000], [(-5760000000000)])⟩,
      ⟨6, ([5360000000000], [(-8040000000000)])⟩,
      ⟨8, ([(-11385000000000)], [2385000000000])⟩,
      ⟨4, ([(-9000000000000)], [5535000000000])⟩,
      ⟨3, ([(-8565000000000)], [7125000000000])⟩,
      ⟨5, ([(-5370000000000)], [(-3630000000000)])⟩,
      ⟨5, ([(-525000000000)], [(-3600000000000)])⟩,
      ⟨5, ([(-480000000000)], [(-3645000000000)])⟩,
      ⟨0, ([480000000000], [(-855000000000)])⟩,
      ⟨9, ([9000000000000], [(-15390000000000)])⟩,
      ⟨5, ([(-5535000000000)], [(-3465000000000)])⟩,
      ⟨4, ([(-4500000000000)], [(-1440000000000)])⟩,
      ⟨4, ([(-3000000000000)], [(-240000000000)])⟩,
      ⟨3, ([(-2520000000000)], [7695000000000])⟩,
      ⟨0, ([(-1440000000000)], [5175000000000])⟩,
      ⟨9, ([3600000000000], [(-12600000000000)])⟩,
      ⟨6, ([3600000000000], [(-8625000000000)])⟩,
      ⟨6, ([3750000000000], [(-4320000000000)])⟩,
      ⟨8, ([(-11520000000000)], [9000000000000])⟩,
      ⟨8, ([(-10842000000000)], [1842000000000])⟩,
      ⟨4, ([(-9000000000000)], [5835000000000])⟩,
      ⟨5, ([(-5685000000000)], [(-3315000000000)])⟩,
      ⟨0, ([(-975000000000)], [0])⟩,
      ⟨5, ([0], [(-2565000000000)])⟩,
      ⟨6, ([3465000000000], [(-8640000000000)])⟩,
      ⟨6, ([3495000000000], [(-6375000000000)])⟩,
      ⟨1, ([9000000000000], [(-5400000000000)])⟩,
      ⟨0, ([2580000000000], [4500000000000])⟩],
    last := 0 }

end ConwaySoifer.Simplified.Certificates.Data
