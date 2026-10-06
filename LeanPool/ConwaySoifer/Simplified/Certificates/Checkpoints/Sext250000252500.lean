/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Data.Sext250000252500
public import LeanPool.ConwaySoifer.Certificates.KernelReplay

/-!
# Sext 250000 252500

Shared exact checkpoint data; all transitions are verified by kernel proofs.
-/

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

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext250000252500

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point0 : IPoint := ([(-1125000000000)], [375000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point1 : IPoint := ([(-1125000000000)], [750000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point2 : IPoint := ([(-750000000000)], [(-375000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point3 : IPoint := ([(-750000000000)], [1125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point4 : IPoint := ([(-375000000000)], [(-750000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point5 : IPoint := ([(-375000000000)], [1125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point6 : IPoint := ([375000000000], [750000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point7 : IPoint := ([750000000000], [375000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point8 : IPoint := ([6000000000000], [(-5625000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point9 : IPoint := ([6000000000000], [(-5250000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point10 : IPoint := ([8250000000000], [(-10500000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point11 : IPoint := ([9000000000000], [(-10425000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point12 : IPoint := ([(-2400000000000)], [2400000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point13 : IPoint := ([4950000000000], [(-8625000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point14 : IPoint := ([5400000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point15 : IPoint := ([(-12675000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point16 : IPoint := ([(-6000000000000)], [2250000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point17 : IPoint := ([(-4950000000000)], [(-4050000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point18 : IPoint := ([(-4200000000000)], [(-750000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point19 : IPoint := ([(-4050000000000)], [1050000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point20 : IPoint := ([(-1875000000000)], [4875000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point21 : IPoint := ([(-1500000000000)], [4125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point22 : IPoint := ([(-375000000000)], [4500000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point23 : IPoint := ([(-13500000000000)], [4500000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point24 : IPoint := ([(-8175000000000)], [4125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point25 : IPoint := ([(-4500000000000)], [6375000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point26 : IPoint := ([(-1125000000000)], [(-375000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point27 : IPoint := ([3300000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point28 : IPoint := ([(-10050000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point29 : IPoint := ([(-9000000000000)], [4425000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point30 : IPoint := ([(-5625000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point31 : IPoint := ([(-3375000000000)], [6000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point32 : IPoint := ([(-2475000000000)], [4950000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point33 : IPoint := ([6675000000000], [(-2625000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point34 : IPoint := ([2475000000000], [5625000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point35 : IPoint := ([2475000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point36 : IPoint := ([9000000000000], [4050000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point37 : IPoint := ([2625000000000], [6375000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point38 : IPoint := ([(-1121250000000), (-4485000000000)], [560625000000, 2242500000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point39 : IPoint := ([(-560625000000), (-2242500000000)], [(-560625000000), (-2242500000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point40 : IPoint := ([560625000000, 2242500000000], [(-1121250000000), (-4485000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point41 : IPoint := ([1121250000000, 4485000000000], [(-560625000000), (-2242500000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point42 : IPoint := ([560625000000, 2242500000000], [560625000000, 2242500000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point43 : IPoint := ([(-560625000000), (-2242500000000)], [1121250000000, 4485000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point44 : IPoint := ([6750000000000, (-9000000000000)], [2250000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point45 : IPoint := ([9000000000000], [(-2250000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point46 : IPoint := ([9000000000000], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point47 : IPoint := ([(-2250000000000), (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point48 : IPoint := ([2250000000000, 9000000000000], [6750000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point49 : IPoint := ([0], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point50 : IPoint := ([(-9000000000000)], [6750000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point51 : IPoint := ([(-6750000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point52 : IPoint := ([(-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point53 : IPoint := ([(-9000000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point54 : IPoint := ([(-6750000000000), 9000000000000], [(-2250000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point55 : IPoint := ([(-9000000000000)], [2250000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point56 : IPoint := ([(-2250000000000), (-9000000000000)], [(-6750000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point57 : IPoint := ([0], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point58 : IPoint := ([2250000000000, 9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point59 : IPoint := ([6750000000000, (-9000000000000)], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point60 : IPoint := ([9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point61 : IPoint := ([6750000000000, (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point62 : IPoint := ([9000000000000], [6750000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point63 : IPoint := ([9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point64 : IPoint := ([(-18000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point65 : IPoint := ([(-15750000000000), 9000000000000], [6750000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point66 : IPoint := ([(-15750000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point67 : IPoint := ([6750000000000, (-9000000000000)], [(-15750000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point68 : IPoint := ([9000000000000], [(-18000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point69 : IPoint := ([9000000000000], [(-15750000000000), 9000000000000])

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet0 : List IPoint := [point38, point39, point40, point41, point42, point43]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet1 : List IPoint := [point44, point45, point46]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet2 : List IPoint := [point47, point48, point49]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet3 : List IPoint := [point50, point51, point52]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet4 : List IPoint := [point53, point54, point55]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet5 : List IPoint := [point56, point57, point58]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet6 : List IPoint := [point59, point60, point45]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet7 : List IPoint := [point61, point62, point63]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet8 : List IPoint := [point64, point65, point66]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet9 : List IPoint := [point67, point68, point69]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet10 : List IPoint := [point0, point39, point40, point41, point42, point43, point38]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet11 : List IPoint := [point0, point39, point40, point41, point42, point43, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet12 : List IPoint := [point0, point2, point39, point40, point41, point42, point43,
    point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet13 : List IPoint := [point0, point2, point39, point40, point41, point42, point43,
    point3, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet14 : List IPoint := [point0, point2, point4, point40, point41, point42, point43, point3,
    point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet15 : List IPoint := [point0, point2, point4, point40, point41, point42, point5, point3,
    point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet16 : List IPoint := [point0, point2, point4, point40, point41, point42, point6, point5,
    point3, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet17 : List IPoint := [point0, point2, point4, point40, point41, point7, point6, point5,
    point3, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet18 : List IPoint := [point0, point2, point4, point8, point7, point6, point5, point3,
    point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet19 : List IPoint := [point0, point2, point4, point8, point9, point7, point6, point5,
    point3, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet20 : List IPoint := [point67, point68, point69, point10]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet21 : List IPoint := [point67, point68, point11, point10]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet22 : List IPoint := [point50, point12, point51, point52]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet23 : List IPoint := [point56, point57, point58, point13]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet24 : List IPoint := [point56, point57, point14, point13]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet25 : List IPoint := [point64, point65, point15]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet26 : List IPoint := [point53, point54, point16, point55]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet27 : List IPoint := [point53, point17, point16, point55]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet28 : List IPoint := [point53, point17, point18, point16, point55]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet29 : List IPoint := [point53, point17, point18, point19, point16, point55]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet30 : List IPoint := [point47, point20, point48, point49]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet31 : List IPoint := [point47, point20, point21, point48, point49]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet32 : List IPoint := [point47, point20, point21, point22, point48, point49]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet33 : List IPoint := [point64, point23, point15]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet34 : List IPoint := [point50, point24, point12, point51, point52]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet35 : List IPoint := [point50, point24, point12, point25, point51, point52]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet36 : List IPoint := [point26, point8, point9, point7, point6, point5, point3, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet37 : List IPoint := [point27, point62, point63]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet38 : List IPoint := [point64, point23, point28]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet39 : List IPoint := [point29, point24, point12, point25, point51, point52]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet40 : List IPoint := [point30, point21, point22, point48, point49]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet41 : List IPoint := [point30, point31, point21, point22, point48, point49]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet42 : List IPoint := [point30, point31, point32, point21, point22, point48, point49]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet43 : List IPoint := [point33, point45, point46, point44]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet44 : List IPoint := [point34, point33, point45, point46, point44]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet45 : List IPoint := [point35, point62, point63]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet46 : List IPoint := [point35, point36, point63]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet47 : List IPoint := [point26, point8, point9, point37, point1]

/-- Contact constraints shared by every state in this certificate trace. -/
def capsConstraints : Fin 10 → List Cap :=
  fun j =>
    match j.val with
    | 0 => []
    | 1 => [⟨point45, point57, false⟩]
    | 2 => []
    | 3 => []
    | 4 => []
    | 5 => []
    | 6 => []
    | 7 => []
    | 8 => []
    | _ => []

/-- Side-owner restrictions shared by every state in this certificate trace. -/
def ownerFlags : Fin 10 → Option (Fin 6) :=
  fun j =>
    match j.val with
    | 0 => none
    | 1 => none
    | 2 => none
    | 3 => none
    | 4 => none
    | 5 => none
    | 6 => none
    | 7 => none
    | 8 => none
    | _ => none

/-- Proposed owner constraints after 0 forced-point assignments. -/
def model0 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet0
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 0. -/
def step0 : Step := ⟨0, point0⟩
/-- Proposed owner constraints after 1 forced-point assignments. -/
def model1 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet10
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 1. -/
def step1 : Step := ⟨0, point1⟩
/-- Proposed owner constraints after 2 forced-point assignments. -/
def model2 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet11
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 2. -/
def step2 : Step := ⟨0, point2⟩
/-- Proposed owner constraints after 3 forced-point assignments. -/
def model3 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 3. -/
def step3 : Step := ⟨0, point3⟩
/-- Proposed owner constraints after 4 forced-point assignments. -/
def model4 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet13
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 4. -/
def step4 : Step := ⟨0, point4⟩
/-- Proposed owner constraints after 5 forced-point assignments. -/
def model5 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet14
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 5. -/
def step5 : Step := ⟨0, point5⟩
/-- Proposed owner constraints after 6 forced-point assignments. -/
def model6 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 6. -/
def step6 : Step := ⟨0, point6⟩
/-- Proposed owner constraints after 7 forced-point assignments. -/
def model7 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet16
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 7. -/
def step7 : Step := ⟨0, point7⟩
/-- Proposed owner constraints after 8 forced-point assignments. -/
def model8 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet17
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 8. -/
def step8 : Step := ⟨0, point8⟩
/-- Proposed owner constraints after 9 forced-point assignments. -/
def model9 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 9. -/
def step9 : Step := ⟨0, point9⟩
/-- Proposed owner constraints after 10 forced-point assignments. -/
def model10 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 10. -/
def step10 : Step := ⟨9, point10⟩
/-- Proposed owner constraints after 11 forced-point assignments. -/
def model11 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet20), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 11. -/
def step11 : Step := ⟨9, point11⟩
/-- Proposed owner constraints after 12 forced-point assignments. -/
def model12 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 12. -/
def step12 : Step := ⟨3, point12⟩
/-- Proposed owner constraints after 13 forced-point assignments. -/
def model13 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet22
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 13. -/
def step13 : Step := ⟨5, point13⟩
/-- Proposed owner constraints after 14 forced-point assignments. -/
def model14 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet22
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 14. -/
def step14 : Step := ⟨5, point14⟩
/-- Proposed owner constraints after 15 forced-point assignments. -/
def model15 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet22
    | 4 => pointSet4
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 15. -/
def step15 : Step := ⟨8, point15⟩
/-- Proposed owner constraints after 16 forced-point assignments. -/
def model16 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet22
    | 4 => pointSet4
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 16. -/
def step16 : Step := ⟨4, point16⟩
/-- Proposed owner constraints after 17 forced-point assignments. -/
def model17 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet22
    | 4 => pointSet26
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 17. -/
def step17 : Step := ⟨4, point17⟩
/-- Proposed owner constraints after 18 forced-point assignments. -/
def model18 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet22
    | 4 => pointSet27
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 18. -/
def step18 : Step := ⟨4, point18⟩
/-- Proposed owner constraints after 19 forced-point assignments. -/
def model19 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet22
    | 4 => pointSet28
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 19. -/
def step19 : Step := ⟨4, point19⟩
/-- Proposed owner constraints after 20 forced-point assignments. -/
def model20 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet22
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 20. -/
def step20 : Step := ⟨2, point20⟩
/-- Proposed owner constraints after 21 forced-point assignments. -/
def model21 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet30
    | 3 => pointSet22
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 21. -/
def step21 : Step := ⟨2, point21⟩
/-- Proposed owner constraints after 22 forced-point assignments. -/
def model22 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet31
    | 3 => pointSet22
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 22. -/
def step22 : Step := ⟨2, point22⟩
/-- Proposed owner constraints after 23 forced-point assignments. -/
def model23 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet32
    | 3 => pointSet22
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 23. -/
def step23 : Step := ⟨8, point23⟩
/-- Proposed owner constraints after 24 forced-point assignments. -/
def model24 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet32
    | 3 => pointSet22
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 24. -/
def step24 : Step := ⟨3, point24⟩
/-- Proposed owner constraints after 25 forced-point assignments. -/
def model25 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet32
    | 3 => pointSet34
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 25. -/
def step25 : Step := ⟨3, point25⟩
/-- Proposed owner constraints after 26 forced-point assignments. -/
def model26 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet32
    | 3 => pointSet35
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 26. -/
def step26 : Step := ⟨0, point26⟩
/-- Proposed owner constraints after 27 forced-point assignments. -/
def model27 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet1
    | 2 => pointSet32
    | 3 => pointSet35
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 27. -/
def step27 : Step := ⟨7, point27⟩
/-- Proposed owner constraints after 28 forced-point assignments. -/
def model28 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet1
    | 2 => pointSet32
    | 3 => pointSet35
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet37
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 28. -/
def step28 : Step := ⟨8, point28⟩
/-- Proposed owner constraints after 29 forced-point assignments. -/
def model29 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet1
    | 2 => pointSet32
    | 3 => pointSet35
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet37
    | 8 => pointSet38
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 29. -/
def step29 : Step := ⟨3, point29⟩
/-- Proposed owner constraints after 30 forced-point assignments. -/
def model30 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet1
    | 2 => pointSet32
    | 3 => pointSet39
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet37
    | 8 => pointSet38
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 30. -/
def step30 : Step := ⟨2, point30⟩
/-- Proposed owner constraints after 31 forced-point assignments. -/
def model31 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet1
    | 2 => pointSet40
    | 3 => pointSet39
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet37
    | 8 => pointSet38
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 31. -/
def step31 : Step := ⟨2, point31⟩
/-- Proposed owner constraints after 32 forced-point assignments. -/
def model32 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet1
    | 2 => pointSet41
    | 3 => pointSet39
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet37
    | 8 => pointSet38
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 32. -/
def step32 : Step := ⟨2, point32⟩
/-- Proposed owner constraints after 33 forced-point assignments. -/
def model33 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet1
    | 2 => pointSet42
    | 3 => pointSet39
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet37
    | 8 => pointSet38
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 33. -/
def step33 : Step := ⟨1, point33⟩
/-- Proposed owner constraints after 34 forced-point assignments. -/
def model34 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet43
    | 2 => pointSet42
    | 3 => pointSet39
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet37
    | 8 => pointSet38
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 34. -/
def step34 : Step := ⟨1, point34⟩
/-- Proposed owner constraints after 35 forced-point assignments. -/
def model35 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet44
    | 2 => pointSet42
    | 3 => pointSet39
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet37
    | 8 => pointSet38
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 35. -/
def step35 : Step := ⟨7, point35⟩
/-- Proposed owner constraints after 36 forced-point assignments. -/
def model36 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet44
    | 2 => pointSet42
    | 3 => pointSet39
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet45
    | 8 => pointSet38
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 36. -/
def step36 : Step := ⟨7, point36⟩
/-- Proposed owner constraints after 37 forced-point assignments. -/
def model37 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet44
    | 2 => pointSet42
    | 3 => pointSet39
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet46
    | 8 => pointSet38
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 37. -/
def step37 : Step := ⟨0, point37⟩
/-- Proposed owner constraints after 38 forced-point assignments. -/
def model38 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet47
    | 1 => pointSet44
    | 2 => pointSet42
    | 3 => pointSet39
    | 4 => pointSet29
    | 5 => pointSet24
    | 6 => pointSet6
    | 7 => pointSet46
    | 8 => pointSet38
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The shared step constants reproduce the original certificate trace exactly. -/
theorem trace_steps : [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10,
    step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22,
    step23, step24, step25, step26, step27, step28, step29, step30, step31, step32, step33, step34,
    step35, step36, step37] = Data.Sext250000252500.steps := by
  rfl

end Sext250000252500
end ConwaySoifer.Simplified.Certificates
