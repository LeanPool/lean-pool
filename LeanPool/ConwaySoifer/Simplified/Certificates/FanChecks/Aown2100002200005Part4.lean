/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown2100002200005
import LeanPool.ConwaySoifer.Certificates.FanCertificate

/-! Kernel-checked fan certificates for Aown2100002200005Part4. -/

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

theorem checkedWitnessForExcluded43_6 :
    ExclusionHint.check
      (model43.B 6 ++ [step43.q])
      9000000000000
      (model43.caps 6)
      (model43.ord 6)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded43_7 :
    ExclusionHint.check
      (model43.B 7 ++ [step43.q])
      9000000000000
      (model43.caps 7)
      (model43.ord 7)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded43_8 :
    ExclusionHint.check
      (model43.B 8 ++ [step43.q])
      9000000000000
      (model43.caps 8)
      (model43.ord 8)
      12
      (.witnessedFan (.next ([5025000000000], [4725000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([2373000000000], [3402000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1623000000000], [4725000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1050000000000], [3975000000000]) (some (0, 1, 3)) (some (0, 3, 3)) (.next ([0],
      [3402000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-4725000000000], [9750000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-3402000000000], [5775000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-4725000000000], [6348000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3975000000000], [5025000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2)))))))))))))
      0
      1
      100 = true := by
  certify_fan

theorem checkedWitnessForExcluded43_9 :
    ExclusionHint.check
      (model43.B 9 ++ [step43.q])
      9000000000000
      (model43.caps 9)
      (model43.ord 9)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded44_0 :
    ExclusionHint.check
      (model44.B 0 ++ [step44.q])
      9000000000000
      (model44.caps 0)
      (model44.ord 0)
      12
      (.pair 5 11)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded44_1 :
    ExclusionHint.check
      (model44.B 1 ++ [step44.q])
      9000000000000
      (model44.caps 1)
      (model44.ord 1)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded44_2 :
    ExclusionHint.check
      (model44.B 2 ++ [step44.q])
      9000000000000
      (model44.caps 2)
      (model44.ord 2)
      12
      (.pair 0 6)
      0
      1
      100 = true := by
  decide +kernel

theorem checkedWitnessForExcluded44_3 :
    ExclusionHint.check
      (model44.B 3 ++ [step44.q])
      9000000000000
      (model44.caps 3)
      (model44.ord 3)
      12
      (.pair 0 4)
      0
      1
      100 = true := by
  decide +kernel

end Aown210000220000
end ConwaySoifer.Simplified.Certificates
