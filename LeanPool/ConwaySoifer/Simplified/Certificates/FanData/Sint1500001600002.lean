/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Certificates.Witness

/-! Exact fan data for Sint1500001600002. -/

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

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint150000160000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part0 : FanWitness := (.next ([1206000000000, 5040000000000], [5172000000000,
    -2520000000000]) (some (6, 6, 5)) (some (6, 6, 5)) (.next ([900000000000], [4725000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([825000000000], [6000000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([306000000000, 5040000000000], [4797000000000, -2520000000000]) (some
    (6, 3, 5)) (some (6, 3, 5)) (.next ([72000000000, -2520000000000], [5172000000000,
    -2520000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([0], [675000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([-75000000000], [5625000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-75000000000], [1275000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-369000000000, 5040000000000], [4797000000000, -2520000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-750000000000], [5625000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-828000000000, -2520000000000], [5931000000000, 5040000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-1275000000000], [5550000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-1503000000000, -2520000000000], [5931000000000, 5040000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-1950000000000], [5550000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-4725000000000], [10275000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-381000000000,
    -5040000000000], [828000000000, 2520000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-4725000000000], [9600000000000]) (some (6, 3, 5)) (some (6, 4, 5)) (.next ([-828000000000,
    -2520000000000], [1581000000000, 5040000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-447000000000, 2520000000000], [753000000000, 2520000000000]) (some (6, 4, 5)) (some (6, 4,
    5)) (.next ([-5172000000000, 2520000000000], [6378000000000, 2520000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-4725000000000], [5625000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-6000000000000], [6825000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-4797000000000, 2520000000000], [5103000000000, 2520000000000]) (some (6, 4, 5)) (some (6, 4,
    5)) (.next ([-5172000000000, 2520000000000], [5244000000000, -5040000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.terminal (some (6, 4, 5)) (some (6, 4, 0)) (some (6, 4,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part1 : FanWitness := (.next ([1206000000000, 5040000000000], [5172000000000,
    -2520000000000]) (some (6, 6, 5)) (some (6, 6, 5)) (.next ([900000000000], [4725000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([825000000000], [6000000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([306000000000, 5040000000000], [4797000000000, -2520000000000]) (some
    (6, 3, 5)) (some (6, 3, 5)) (.next ([72000000000, -2520000000000], [5172000000000,
    -2520000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([0], [675000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([-75000000000], [5625000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-75000000000], [1275000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-369000000000, 5040000000000], [4797000000000, -2520000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-750000000000], [5625000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-828000000000, -2520000000000], [5931000000000, 5040000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-1275000000000], [5550000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-1503000000000, -2520000000000], [5931000000000, 5040000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-1950000000000], [5550000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-4725000000000], [10275000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-4725000000000],
    [9600000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-381000000000, -5040000000000],
    [828000000000, 2520000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-828000000000,
    -2520000000000], [1581000000000, 5040000000000]) (some (6, 3, 5)) (some (6, 4, 5)) (.next
    ([-447000000000, 2520000000000], [753000000000, 2520000000000]) (some (6, 4, 5)) (some (6, 4,
    5)) (.next ([-5172000000000, 2520000000000], [6378000000000, 2520000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-4725000000000], [5625000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-6000000000000], [6825000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-4797000000000, 2520000000000], [5103000000000, 2520000000000]) (some (6, 4, 5)) (some (6, 4,
    5)) (.next ([-5172000000000, 2520000000000], [5244000000000, -5040000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.terminal (some (6, 4, 5)) (some (6, 4, 0)) (some (6, 4,
    5)))))))))))))))))))))))))))

end Sint150000160000
end ConwaySoifer.Simplified.Certificates
