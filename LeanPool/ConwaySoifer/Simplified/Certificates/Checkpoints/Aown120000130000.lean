/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Data.Aown120000130000
public import LeanPool.ConwaySoifer.Certificates.KernelReplay

/-!
# Aown 120000 130000

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
namespace Aown120000130000

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point0 : IPoint := ([0], [510000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point1 : IPoint := ([510000000000], [(-510000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point2 : IPoint := ([1080000000000], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point3 : IPoint := ([2220000000000], [6780000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point4 : IPoint := ([7500000000000], [1080000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point5 : IPoint := ([9000000000000], [(-6780000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point6 : IPoint := ([(-7920000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point7 : IPoint := ([(-2295000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point8 : IPoint := ([0], [1080000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point9 : IPoint := ([5295000000000], [1080000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point10 : IPoint := ([6156000000000], [900000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point11 : IPoint := ([6300000000000], [825000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point12 : IPoint := ([6585000000000], [540000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point13 : IPoint := ([8640000000000], [(-15765000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point14 : IPoint := ([9000000000000], [4680000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point15 : IPoint := ([(-11325000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point16 : IPoint := ([(-7920000000000)], [4170000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point17 : IPoint := ([(-3720000000000)], [720000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point18 : IPoint := ([(-3570000000000)], [4320000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point19 : IPoint := ([7695000000000], [(-3375000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point20 : IPoint := ([9000000000000], [(-3495000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point21 : IPoint := ([(-11865000000000)], [2865000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point22 : IPoint := ([(-8250000000000)], [5760000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point23 : IPoint := ([(-5460000000000)], [(-3540000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point24 : IPoint := ([(-5250000000000)], [(-3210000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point25 : IPoint := ([360000000000], [(-4110000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point26 : IPoint := ([3420000000000], [(-7920000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point27 : IPoint := ([(-626400000000), (-5220000000000)], [313200000000, 2610000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point28 : IPoint := ([(-313200000000), (-2610000000000)], [(-313200000000), (-2610000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point29 : IPoint := ([313200000000, 2610000000000], [(-626400000000), (-5220000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point30 : IPoint := ([626400000000, 5220000000000], [(-313200000000), (-2610000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point31 : IPoint := ([313200000000, 2610000000000], [313200000000, 2610000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point32 : IPoint := ([(-313200000000), (-2610000000000)], [626400000000, 5220000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point33 : IPoint := ([7920000000000, (-9000000000000)], [1080000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point34 : IPoint := ([9000000000000], [(-1080000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point35 : IPoint := ([9000000000000], [4500000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point36 : IPoint := ([(-1080000000000), (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point37 : IPoint := ([1080000000000, 9000000000000], [7920000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point38 : IPoint := ([0], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point39 : IPoint := ([(-9000000000000)], [7920000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point40 : IPoint := ([(-7920000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point41 : IPoint := ([(-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point42 : IPoint := ([(-9000000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point43 : IPoint := ([(-7920000000000), 9000000000000], [(-1080000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point44 : IPoint := ([(-9000000000000)], [1080000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point45 : IPoint := ([(-1080000000000), (-9000000000000)], [(-7920000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point46 : IPoint := ([0], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point47 : IPoint := ([1080000000000, 9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point48 : IPoint := ([7920000000000, (-9000000000000)], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point49 : IPoint := ([9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point50 : IPoint := ([9000000000000], [(-7920000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point51 : IPoint := ([9000000000000], [7920000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point52 : IPoint := ([9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point53 : IPoint := ([7920000000000, (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point54 : IPoint := ([(-18000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point55 : IPoint := ([(-16920000000000), 9000000000000], [7920000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point56 : IPoint := ([(-16920000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point57 : IPoint := ([7920000000000, (-9000000000000)], [(-16920000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point58 : IPoint := ([9000000000000], [(-18000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point59 : IPoint := ([9000000000000], [(-16920000000000), 9000000000000])

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet0 : List IPoint := [point27, point28, point29, point30, point31, point32]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet1 : List IPoint := [point33, point34, point35]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet2 : List IPoint := [point36, point37, point38]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet3 : List IPoint := [point39, point40, point41]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet4 : List IPoint := [point42, point43, point44]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet5 : List IPoint := [point45, point46, point47]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet6 : List IPoint := [point48, point49, point50]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet7 : List IPoint := [point33, point51, point52, point53]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet8 : List IPoint := [point54, point55, point56]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet9 : List IPoint := [point57, point58, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet10 : List IPoint := [point27, point28, point29, point30, point31, point0, point32]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet11 : List IPoint := [point27, point28, point29, point1, point30, point31, point0,
    point32]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet12 : List IPoint := [point27, point28, point29, point1, point2, point0, point32]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet13 : List IPoint := [point36, point3, point38]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet14 : List IPoint := [point36, point4, point3, point38]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet15 : List IPoint := [point48, point49, point5]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet16 : List IPoint := [point42, point43, point6, point44]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet17 : List IPoint := [point39, point7, point41]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet18 : List IPoint := [point27, point28, point29, point1, point2, point8]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet19 : List IPoint := [point27, point28, point29, point9, point8]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet20 : List IPoint := [point27, point28, point29, point10, point9, point8]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet21 : List IPoint := [point27, point28, point29, point11, point10, point9, point8]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet22 : List IPoint := [point27, point28, point29, point12, point11, point10, point9,
    point8]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet23 : List IPoint := [point57, point58, point59, point13]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet24 : List IPoint := [point33, point34, point14]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet25 : List IPoint := [point54, point55, point15]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet26 : List IPoint := [point42, point43, point16, point44]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet27 : List IPoint := [point42, point43, point17, point16, point44]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet28 : List IPoint := [point39, point18, point7, point41]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet29 : List IPoint := [point19, point48, point49, point5]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet30 : List IPoint := [point19, point48, point49, point20]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet31 : List IPoint := [point54, point21, point15]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet32 : List IPoint := [point42, point43, point17, point22, point44]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet33 : List IPoint := [point23, point46, point47]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet34 : List IPoint := [point23, point46, point47, point24]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet35 : List IPoint := [point23, point46, point47, point25, point24]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet36 : List IPoint := [point23, point46, point47, point26, point25, point24]

/-- Contact constraints shared by every state in this certificate trace. -/
def capsConstraints : Fin 10 → List Cap :=
  fun j =>
    match j.val with
    | 0 => []
    | 1 => [⟨point33, point41, false⟩]
    | 2 => [⟨point33, point49, true⟩]
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
def step3 : Step := ⟨2, point3⟩
/-- Proposed owner constraints after 4 forced-point assignments. -/
def model4 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet1
    | 2 => pointSet13
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 4. -/
def step4 : Step := ⟨2, point4⟩
/-- Proposed owner constraints after 5 forced-point assignments. -/
def model5 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet1
    | 2 => pointSet14
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 5. -/
def step5 : Step := ⟨6, point5⟩
/-- Proposed owner constraints after 6 forced-point assignments. -/
def model6 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet1
    | 2 => pointSet14
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 6. -/
def step6 : Step := ⟨4, point6⟩
/-- Proposed owner constraints after 7 forced-point assignments. -/
def model7 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet1
    | 2 => pointSet14
    | 3 => pointSet3
    | 4 => pointSet16
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 7. -/
def step7 : Step := ⟨3, point7⟩
/-- Proposed owner constraints after 8 forced-point assignments. -/
def model8 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet1
    | 2 => pointSet14
    | 3 => pointSet17
    | 4 => pointSet16
    | 5 => pointSet5
    | 6 => pointSet15
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
    | 2 => pointSet14
    | 3 => pointSet17
    | 4 => pointSet16
    | 5 => pointSet5
    | 6 => pointSet15
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
    | 2 => pointSet14
    | 3 => pointSet17
    | 4 => pointSet16
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 10. -/
def step10 : Step := ⟨0, point10⟩
/-- Proposed owner constraints after 11 forced-point assignments. -/
def model11 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet20
    | 1 => pointSet1
    | 2 => pointSet14
    | 3 => pointSet17
    | 4 => pointSet16
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 11. -/
def step11 : Step := ⟨0, point11⟩
/-- Proposed owner constraints after 12 forced-point assignments. -/
def model12 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet14
    | 3 => pointSet17
    | 4 => pointSet16
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 12. -/
def step12 : Step := ⟨0, point12⟩
/-- Proposed owner constraints after 13 forced-point assignments. -/
def model13 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet1
    | 2 => pointSet14
    | 3 => pointSet17
    | 4 => pointSet16
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 13. -/
def step13 : Step := ⟨9, point13⟩
/-- Proposed owner constraints after 14 forced-point assignments. -/
def model14 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet1
    | 2 => pointSet14
    | 3 => pointSet17
    | 4 => pointSet16
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 14. -/
def step14 : Step := ⟨1, point14⟩
/-- Proposed owner constraints after 15 forced-point assignments. -/
def model15 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet17
    | 4 => pointSet16
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 15. -/
def step15 : Step := ⟨8, point15⟩
/-- Proposed owner constraints after 16 forced-point assignments. -/
def model16 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet17
    | 4 => pointSet16
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 16. -/
def step16 : Step := ⟨4, point16⟩
/-- Proposed owner constraints after 17 forced-point assignments. -/
def model17 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet17
    | 4 => pointSet26
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 17. -/
def step17 : Step := ⟨4, point17⟩
/-- Proposed owner constraints after 18 forced-point assignments. -/
def model18 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet17
    | 4 => pointSet27
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 18. -/
def step18 : Step := ⟨3, point18⟩
/-- Proposed owner constraints after 19 forced-point assignments. -/
def model19 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet28
    | 4 => pointSet27
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 19. -/
def step19 : Step := ⟨6, point19⟩
/-- Proposed owner constraints after 20 forced-point assignments. -/
def model20 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet28
    | 4 => pointSet27
    | 5 => pointSet5
    | 6 => pointSet29
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 20. -/
def step20 : Step := ⟨6, point20⟩
/-- Proposed owner constraints after 21 forced-point assignments. -/
def model21 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet28
    | 4 => pointSet27
    | 5 => pointSet5
    | 6 => pointSet30
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 21. -/
def step21 : Step := ⟨8, point21⟩
/-- Proposed owner constraints after 22 forced-point assignments. -/
def model22 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet28
    | 4 => pointSet27
    | 5 => pointSet5
    | 6 => pointSet30
    | 7 => pointSet7
    | 8 => pointSet31
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 22. -/
def step22 : Step := ⟨4, point22⟩
/-- Proposed owner constraints after 23 forced-point assignments. -/
def model23 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet28
    | 4 => pointSet32
    | 5 => pointSet5
    | 6 => pointSet30
    | 7 => pointSet7
    | 8 => pointSet31
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 23. -/
def step23 : Step := ⟨5, point23⟩
/-- Proposed owner constraints after 24 forced-point assignments. -/
def model24 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet28
    | 4 => pointSet32
    | 5 => pointSet33
    | 6 => pointSet30
    | 7 => pointSet7
    | 8 => pointSet31
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 24. -/
def step24 : Step := ⟨5, point24⟩
/-- Proposed owner constraints after 25 forced-point assignments. -/
def model25 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet28
    | 4 => pointSet32
    | 5 => pointSet34
    | 6 => pointSet30
    | 7 => pointSet7
    | 8 => pointSet31
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 25. -/
def step25 : Step := ⟨5, point25⟩
/-- Proposed owner constraints after 26 forced-point assignments. -/
def model26 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet28
    | 4 => pointSet32
    | 5 => pointSet35
    | 6 => pointSet30
    | 7 => pointSet7
    | 8 => pointSet31
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 26. -/
def step26 : Step := ⟨5, point26⟩
/-- Proposed owner constraints after 27 forced-point assignments. -/
def model27 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet24
    | 2 => pointSet14
    | 3 => pointSet28
    | 4 => pointSet32
    | 5 => pointSet36
    | 6 => pointSet30
    | 7 => pointSet7
    | 8 => pointSet31
    | _ => pointSet23), capsConstraints, ownerFlags⟩

/-- The shared step constants reproduce the original certificate trace exactly. -/
theorem trace_steps : [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10,
    step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22,
    step23, step24, step25, step26] = Data.Aown120000130000.steps := by
  rfl

end Aown120000130000
end ConwaySoifer.Simplified.Certificates
