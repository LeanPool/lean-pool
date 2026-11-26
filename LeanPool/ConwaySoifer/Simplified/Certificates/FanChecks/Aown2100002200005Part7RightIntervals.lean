/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown2100002200005
import LeanPool.ConwaySoifer.Certificates.FanCertificate  -- shake: keep

/-! Kernel check for subinterval 2 of Aown2100002200005Part7. -/

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Aown210000220000.model0

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Aown210000220000

/-- The supplied orientation witness passes on this subinterval. -/
theorem checkedWitnessForExcluded46_2RightLeaf1 :
    ExclusionHint.check
      (model46.B 2 ++ [step46.q])
      9000000000000
      (model46.caps 2)
      (model46.ord 2)
      12
      (.witnessedFan
      (.next ([7230000000000, 0], [1140000000000, 9000000000000]) (some (0, 6, 2)) (some (6, 6, 3))
      (.next ([7380000000000, 0], [1260000000000, 9000000000000]) (some (6, 6, 3)) (some (6, 6, 3))
      (.next ([7110000000000, 0], [1530000000000, 9000000000000]) (some (6, 6, 3)) (some (6, 6, 3))
      (.next ([7110000000000, -9000000000000], [1890000000000, 9000000000000]) (some (6, 6, 3))
      (some (6, 6, 3)) (.next ([630000000000, -9000000000000], [120000000000, 9000000000000]) (some
      (6, 6, 3)) (some (6, 6, 3)) (.next ([7230000000000], [2385000000000]) (some (6, 6, 3)) (some
      (6, 6, 3)) (.next ([7380000000000], [2505000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([7110000000000], [2775000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([7110000000000,
      -9000000000000], [3135000000000, 0]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4275000000000,
      0], [2115000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4275000000000],
      [3360000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([150000000000], [120000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([360000000000, -9000000000000], [270000000000,
      9000000000000]) (some (6, 1, 3)) (some (6, 2, 3)) (.next ([975000000000], [1980000000000])
      (some (6, 2, 3)) (some (6, 2, 3)) (.next ([855000000000], [2250000000000]) (some (6, 2, 3))
      (some (6, 2, 3)) (.next ([585000000000], [2250000000000]) (some (6, 2, 3)) (some (6, 2, 3))
      (.next ([1350000000000], [5880000000000]) (some (6, 2, 3)) (some (6, 2, 4)) (.next
      ([1230000000000], [6150000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([960000000000],
      [6150000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([375000000000], [3900000000000])
      (some (6, 2, 4)) (some (6, 2, 4)) (.next ([600000000000, 0], [6510000000000, -9000000000000])
      (some (6, 2, 4)) (some (6, 2, 5)) fan46Owner2Part1))))))))))))))))))))))
      (9615) (15521) (2115300) = true := by
  decide +kernel

/-- The supplied orientation witness passes on this subinterval. -/
theorem checkedWitnessForExcluded46_2RightLeaf2 :
    ExclusionHint.check
      (model46.B 2 ++ [step46.q])
      9000000000000
      (model46.caps 2)
      (model46.ord 2)
      12
      (.witnessedFan (.next ([7230000000000, 0], [1140000000000,
      9000000000000]) (some (0, 6, 2)) (some (6, 6, 3)) (.next ([7380000000000, 0], [1260000000000,
      9000000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([7110000000000, 0], [1530000000000,
      9000000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([360000000000, -9000000000000], [0,
      9000000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([7110000000000, -9000000000000],
      [1890000000000, 9000000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([7230000000000],
      [2385000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([7380000000000], [2505000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([7110000000000], [2775000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([270000000000], [120000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([7110000000000, -9000000000000], [3135000000000, 0]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([4275000000000, 0], [2115000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([4275000000000], [3360000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([150000000000], [120000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([360000000000,
      -9000000000000], [270000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 2, 3)) (.next
      ([975000000000], [1980000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([855000000000],
      [2250000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([585000000000], [2250000000000])
      (some (6, 2, 3)) (some (6, 2, 3)) (.next ([1350000000000], [5880000000000]) (some (6, 2, 3))
      (some (6, 2, 4)) (.next ([1230000000000], [6150000000000]) (some (6, 2, 4)) (some (6, 2, 4))
      (.next ([960000000000], [6150000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([375000000000], [3900000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([600000000000, 0],
      [6510000000000, -9000000000000]) (some (6, 2, 4)) (some (6, 2, 5)) (.next ([225000000000, 0],
      [2610000000000, -9000000000000]) (some (6, 2, 5)) (some (6, 2, 5))
      fan46Owner2Part2))))))))))))))))))))))))
      (124168) (148071) (16922400) = true := by
  certify_fan

/-- The supplied orientation witness passes on this subinterval. -/
theorem checkedWitnessForExcluded46_2RightLeaf3 :
    ExclusionHint.check
      (model46.B 2 ++ [step46.q])
      9000000000000
      (model46.caps 2)
      (model46.ord 2)
      12
      (.witnessedFan (.next ([7230000000000, 0], [1140000000000, 9000000000000]) (some (0, 6, 2))
      (some (6, 6, 3)) fan46Owner2Part4))
      (148071) (167904) (16922400) = true := by
  certify_fan

/-- The supplied orientation witness passes on this subinterval. -/
theorem checkedWitnessForExcluded46_2RightLeaf4 :
    ExclusionHint.check
      (model46.B 2 ++ [step46.q])
      9000000000000
      (model46.caps 2)
      (model46.ord 2)
      12
      (.witnessedFan (.next ([7230000000000, 0], [1140000000000,
      9000000000000]) (some (0, 6, 2)) (some (6, 6, 3)) fan46Owner2Part6))
      (167904) (169224) (16922400) = true := by
  certify_fan

end Aown210000220000
end ConwaySoifer.Simplified.Certificates
