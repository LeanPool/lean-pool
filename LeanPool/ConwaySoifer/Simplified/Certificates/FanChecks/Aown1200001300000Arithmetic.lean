/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1200001300000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown120000130000

/-! Kernel checks for the orientation-fan tails in Aown1200001300000. -/

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

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Aown120000130000

/-- The checker accepts this shared orientation-fan tail. -/
theorem checkedFan3Owner0Part0Arithmetic :
    fan3Owner0Part0.check (model3.B 0 ++ [step3.q]) 9000000000000
      (model3.caps 0) 0 1 100 12
      ([313200000000, 2610000000000], [313200000000, 2610000000000]) = true := by
  decide +kernel

/-- The checker accepts this shared orientation-fan tail. -/
theorem checkedFan4Owner0Part0Arithmetic :
    fan4Owner0Part0.check (model4.B 0 ++ [step4.q]) 9000000000000
      (model4.caps 0) 0 1 100 12
      ([7186800000000, -2610000000000], [1706400000000, 5220000000000]) = true := by
  decide +kernel

/-- The checker accepts this shared orientation-fan tail. -/
theorem checkedFan5Owner0Part0Arithmetic :
    fan5Owner0Part0.check (model5.B 0 ++ [step5.q]) 9000000000000
      (model5.caps 0) 0 1 100 12
      ([7093200000000, 2610000000000], [2533200000000, 2610000000000]) = true := by
  decide +kernel

/-- The checker accepts this shared orientation-fan tail. -/
theorem checkedFan7Owner0Part0Arithmetic :
    fan7Owner0Part0.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 0 3836 15494700 12
      ([116400000000, 5220000000000], [196800000000, -2610000000000]) = true := by
  decide +kernel

/-- The checker accepts this shared orientation-fan tail. -/
theorem checkedFan7Owner0Part1Arithmetic :
    fan7Owner0Part1.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 3836 60106 15494700 12
      ([626400000000, 5220000000000], [766800000000, -2610000000000]) = true := by
  decide +kernel

/-- The checker accepts this shared orientation-fan tail. -/
theorem checkedFan7Owner0Part2Arithmetic :
    fan7Owner0Part2.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 60106 116376 15494700 12
      ([626400000000, 5220000000000], [766800000000, -2610000000000]) = true := by
  decide +kernel

/-- The checker accepts this shared orientation-fan tail. -/
theorem checkedFan7Owner0Part3Arithmetic :
    fan7Owner0Part3.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 2984 3973 397300 12
      ([6705000000000], [2805000000000]) = true := by
  decide +kernel

end Aown120000130000
end ConwaySoifer.Simplified.Certificates
