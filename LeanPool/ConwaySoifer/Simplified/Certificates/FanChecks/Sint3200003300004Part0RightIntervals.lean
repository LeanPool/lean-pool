/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint3200003300004
import LeanPool.ConwaySoifer.Certificates.FanCertificate  -- shake: keep

/-! Kernel checks for the right-hand subintervals of Sint3200003300004Part0. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sint320000330000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint320000330000

/-- The supplied orientation witness passes on this subinterval. -/
theorem checkedWitnessForExcluded32_6RightLeaf1 :
    ExclusionHint.check
      (model32.B 6 ++ [step32.q])
      9000000000000
      (model32.caps 6)
      (model32.ord 6)
      12
      (.witnessedFan (.next
      ([900000000000, 0], [60000000000, -9000000000000]) (some (7, 1, 3)) (some (7, 1, 7))
      fan32Owner6Part2))
      (21546) (28994) (4349100) = true := by
  certify_fan

/-- The supplied orientation witness passes on this subinterval. -/
theorem checkedWitnessForExcluded32_6RightLeaf2 :
    ExclusionHint.check
      (model32.B 6 ++ [step32.q])
      9000000000000
      (model32.caps 6)
      (model32.ord 6)
      12
      (.witnessedFan (.next ([3840000000000], [285000000000]) (some (7, 2, 3))
      (some (7, 2, 7)) fan32Owner6Part4))
      (28994) (35534) (4349100) = true := by
  certify_fan

/-- The supplied orientation witness passes on this subinterval. -/
theorem checkedWitnessForExcluded32_6RightLeaf3 :
    ExclusionHint.check
      (model32.B 6 ++ [step32.q])
      9000000000000
      (model32.caps 6)
      (model32.ord 6)
      12
      (.witnessedFan (.next ([3840000000000], [285000000000])
      (some (7, 2, 3)) (some (7, 2, 7)) (.next ([2655000000000], [285000000000]) (some (7, 2, 7))
      (some (7, 2, 7)) (.next ([5760000000000], [1935000000000]) (some (7, 2, 7)) (some (7, 2, 7))
      (.next ([6120000000000], [2190000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([4125000000000], [1635000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([2595000000000,
      9000000000000], [1245000000000, -9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([3840000000000], [1980000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([3870000000000], [2250000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([360000000000],
      [255000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([2880000000000, 9000000000000],
      [2880000000000, 9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([3840000000000],
      [5160000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1305000000000], [1920000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([2880000000000, 9000000000000], [6060000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1245000000000, 9000000000000], [2880000000000,
      -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([900000000000], [2940000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([690000000000], [2280000000000]) (some (0, 2, 7))
      (some (0, 2, 7)) (.next ([960000000000, -9000000000000], [3165000000000, 9000000000000]) (some
      (0, 2, 7)) (some (0, 2, 7)) (.next ([1245000000000, -9000000000000], [4515000000000,
      9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([630000000000, 9000000000000],
      [3240000000000, -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([285000000000],
      [1350000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([990000000000, -9000000000000],
      [5130000000000, 9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-60000000000,
      9000000000000], [960000000000, -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
      ([30000000000], [1965000000000]) (some (0, 2, 7)) (some (0, 2, 7))
      fan32Owner6Part5))))))))))))))))))))))))
      (35534) (43491) (4349100) = true := by
  certify_fan

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
