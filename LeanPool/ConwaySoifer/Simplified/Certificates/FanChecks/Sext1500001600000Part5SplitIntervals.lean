/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1500001600000
import LeanPool.ConwaySoifer.Certificates.FanCertificate  -- shake: keep

/-! Kernel checks for the subintervals of Sext1500001600000Part5. -/

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

public section

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sext150000160000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext150000160000

/-- The supplied orientation witness passes on this subinterval. -/
theorem checkedWitnessForExcluded5_0Leaf1 :
    ExclusionHint.check
      (model5.B 0 ++ [step5.q])
      9000000000000
      (model5.caps 0)
      (model5.ord
    0)
      12
      (.witnessedFan (.next ([1056000000000,
      5040000000000], [72000000000, -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next
      ([1728000000000, 2520000000000], [378000000000, 2520000000000]) (some (4, 6, 2)) (some (4, 6,
      2)) (.next ([6750000000000], [2250000000000]) (some (4, 6, 2)) (some (5, 6, 2)) (.next
      ([5022000000000, -2520000000000], [3222000000000, -2520000000000]) (some (5, 6, 2)) (some (5,
      6, 2)) (.next ([5850000000000], [3975000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([972000000000, -2520000000000], [756000000000, 5040000000000]) (some (5, 6, 2)) (some (5, 6,
      2)) (.next ([4644000000000, -5040000000000], [3978000000000, 2520000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([5022000000000, -2520000000000], [4356000000000, 5040000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4950000000000], [4350000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([828000000000, 2520000000000], [753000000000, 2520000000000]) (some
      (5, 6, 2)) (some (6, 6, 2)) (.next ([378000000000, 2520000000000], [378000000000,
      2520000000000]) (some (6, 6, 2)) (some (6, 6, 2)) fan5Owner0Part0))))))))))))
      (0) (10) (2100) = true := by
  certify_fan

/-- The supplied orientation witness passes on this subinterval. -/
theorem checkedWitnessForExcluded5_0Leaf2 :
    ExclusionHint.check
      (model5.B 0 ++ [step5.q])
      9000000000000
      (model5.caps 0)
      (model5.ord
    0)
      12
      (.witnessedFan (.next ([1056000000000, 5040000000000], [72000000000,
      -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([1728000000000, 2520000000000],
      [378000000000, 2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([6750000000000],
      [2250000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5022000000000, -2520000000000],
      [3222000000000, -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5850000000000],
      [3975000000000]) (some (4, 6, 2)) (some (5, 6, 2)) (.next ([972000000000, -2520000000000],
      [756000000000, 5040000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4644000000000,
      -5040000000000], [3978000000000, 2520000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([5022000000000, -2520000000000], [4356000000000, 5040000000000]) (some (5, 6, 2)) (some (5,
      6, 2)) (.next ([4950000000000], [4350000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([828000000000, 2520000000000], [753000000000, 2520000000000]) (some (5, 6, 2)) (some (6, 6,
      2)) (.next ([378000000000, 2520000000000], [378000000000, 2520000000000]) (some (6, 6, 2))
      (some (6, 6, 2)) (.next ([381000000000, 5040000000000], [447000000000, -2520000000000]) (some
      (6, 6, 2)) (some (6, 6, 2)) (.next ([306000000000, 5040000000000], [372000000000,
      -2520000000000]) (some (6, 6, 2)) (some (6, 6, 2)) fan5Owner0Part1))))))))))))))
      (170) (270) (35700) = true := by
  certify_fan

/-- The supplied orientation witness passes on this subinterval. -/
theorem checkedWitnessForExcluded5_0Leaf3 :
    ExclusionHint.check
      (model5.B 0 ++ [step5.q])
      9000000000000
      (model5.caps 0)
      (model5.ord
    0)
      12
      (.witnessedFan (.next ([1056000000000, 5040000000000], [72000000000, -2520000000000]) (some
      (4, 6, 2)) (some (4, 6, 2)) (.next ([1728000000000, 2520000000000], [378000000000,
      2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([6750000000000], [2250000000000])
      (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5022000000000, -2520000000000], [3222000000000,
      -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5850000000000], [3975000000000])
      (some (4, 6, 2)) (some (4, 6, 2)) (.next ([972000000000, -2520000000000], [756000000000,
      5040000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([4644000000000, -5040000000000],
      [3978000000000, 2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) fan5Owner0Part2))))))))
      (270) (357) (35700) = true := by
  certify_fan

end Sext150000160000
end ConwaySoifer.Simplified.Certificates
