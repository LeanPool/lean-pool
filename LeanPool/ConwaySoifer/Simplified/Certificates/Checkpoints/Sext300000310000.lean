/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Data.Sext300000310000
public import LeanPool.ConwaySoifer.Certificates.KernelReplay

/-!
# Sext 300000 310000

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
namespace Sext300000310000

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point0 : IPoint := ([(-1350000000000)], [600000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point1 : IPoint := ([(-1350000000000)], [750000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point2 : IPoint := ([(-750000000000)], [1350000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point3 : IPoint := ([600000000000], [750000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point4 : IPoint := ([5400000000000], [(-5175000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point5 : IPoint := ([6000000000000], [(-4950000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point6 : IPoint := ([9000000000000], [(-10800000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point7 : IPoint := ([(-2610000000000)], [2610000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point8 : IPoint := ([4860000000000], [(-8985000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point9 : IPoint := ([4875000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point10 : IPoint := ([(-12525000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point11 : IPoint := ([(-6375000000000)], [2700000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point12 : IPoint := ([(-5550000000000)], [(-3450000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point13 : IPoint := ([(-5175000000000)], [2250000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point14 : IPoint := ([(-4050000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point15 : IPoint := ([(-1800000000000)], [4425000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point16 : IPoint := ([(-13425000000000)], [4425000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point17 : IPoint := ([(-9000000000000)], [4575000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point18 : IPoint := ([(-5400000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point19 : IPoint := ([(-4140000000000)], [7125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point20 : IPoint := ([(-1242000000000), (-4140000000000)], [621000000000, 2070000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point21 : IPoint := ([(-621000000000), (-2070000000000)], [(-621000000000), (-2070000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point22 : IPoint := ([621000000000, 2070000000000], [(-1242000000000), (-4140000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point23 : IPoint := ([1242000000000, 4140000000000], [(-621000000000), (-2070000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point24 : IPoint := ([621000000000, 2070000000000], [621000000000, 2070000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point25 : IPoint := ([(-621000000000), (-2070000000000)], [1242000000000, 4140000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point26 : IPoint := ([6300000000000, (-9000000000000)], [2700000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point27 : IPoint := ([9000000000000], [(-2700000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point28 : IPoint := ([9000000000000], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point29 : IPoint := ([(-2700000000000), (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point30 : IPoint := ([2700000000000, 9000000000000], [6300000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point31 : IPoint := ([0], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point32 : IPoint := ([(-9000000000000)], [6300000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point33 : IPoint := ([(-6300000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point34 : IPoint := ([(-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point35 : IPoint := ([(-9000000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point36 : IPoint := ([(-6300000000000), 9000000000000], [(-2700000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point37 : IPoint := ([(-9000000000000)], [2700000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point38 : IPoint := ([(-2700000000000), (-9000000000000)], [(-6300000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point39 : IPoint := ([0], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point40 : IPoint := ([2700000000000, 9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point41 : IPoint := ([6300000000000, (-9000000000000)], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point42 : IPoint := ([9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point43 : IPoint := ([6300000000000, (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point44 : IPoint := ([9000000000000], [6300000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point45 : IPoint := ([9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point46 : IPoint := ([(-18000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point47 : IPoint := ([(-15300000000000), 9000000000000], [6300000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point48 : IPoint := ([(-15300000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point49 : IPoint := ([6300000000000, (-9000000000000)], [(-15300000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point50 : IPoint := ([9000000000000], [(-18000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point51 : IPoint := ([9000000000000], [(-15300000000000), 9000000000000])

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet0 : List IPoint := [point20, point21, point22, point23, point24, point25]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet1 : List IPoint := [point26, point27, point28]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet2 : List IPoint := [point29, point30, point31]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet3 : List IPoint := [point32, point33, point34]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet4 : List IPoint := [point35, point36, point37]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet5 : List IPoint := [point38, point39, point40]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet6 : List IPoint := [point41, point42, point27]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet7 : List IPoint := [point43, point44, point45]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet8 : List IPoint := [point46, point47, point48]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet9 : List IPoint := [point49, point50, point51]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet10 : List IPoint := [point0, point21, point22, point23, point24, point25]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet11 : List IPoint := [point0, point21, point22, point23, point24, point25, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet12 : List IPoint := [point0, point21, point22, point23, point24, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet13 : List IPoint := [point0, point21, point22, point23, point3, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet14 : List IPoint := [point0, point21, point4, point3, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet15 : List IPoint := [point0, point21, point4, point5, point3, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet16 : List IPoint := [point49, point50, point6]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet17 : List IPoint := [point32, point7, point33, point34]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet18 : List IPoint := [point38, point39, point40, point8]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet19 : List IPoint := [point38, point39, point9, point8]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet20 : List IPoint := [point46, point47, point10]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet21 : List IPoint := [point35, point36, point11, point37]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet22 : List IPoint := [point35, point12, point11, point37]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet23 : List IPoint := [point35, point12, point13, point11, point37]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet24 : List IPoint := [point35, point12, point14, point13, point11, point37]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet25 : List IPoint := [point29, point15, point30, point31]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet26 : List IPoint := [point46, point16, point10]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet27 : List IPoint := [point17, point7, point33, point34]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet28 : List IPoint := [point18, point15, point30, point31]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet29 : List IPoint := [point18, point19, point15, point30, point31]

/-- Contact constraints shared by every state in this certificate trace. -/
def capsConstraints : Fin 10 → List Cap :=
  fun j =>
    match j.val with
    | 0 => []
    | 1 => [⟨point27, point39, false⟩]
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
def step6 : Step := ⟨9, point6⟩
/-- Proposed owner constraints after 7 forced-point assignments. -/
def model7 : Model :=
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
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 7. -/
def step7 : Step := ⟨3, point7⟩
/-- Proposed owner constraints after 8 forced-point assignments. -/
def model8 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet17
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 8. -/
def step8 : Step := ⟨5, point8⟩
/-- Proposed owner constraints after 9 forced-point assignments. -/
def model9 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet17
    | 4 => pointSet4
    | 5 => pointSet18
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 9. -/
def step9 : Step := ⟨5, point9⟩
/-- Proposed owner constraints after 10 forced-point assignments. -/
def model10 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet17
    | 4 => pointSet4
    | 5 => pointSet19
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 10. -/
def step10 : Step := ⟨8, point10⟩
/-- Proposed owner constraints after 11 forced-point assignments. -/
def model11 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet17
    | 4 => pointSet4
    | 5 => pointSet19
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet20
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 11. -/
def step11 : Step := ⟨4, point11⟩
/-- Proposed owner constraints after 12 forced-point assignments. -/
def model12 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet17
    | 4 => pointSet21
    | 5 => pointSet19
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet20
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 12. -/
def step12 : Step := ⟨4, point12⟩
/-- Proposed owner constraints after 13 forced-point assignments. -/
def model13 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet17
    | 4 => pointSet22
    | 5 => pointSet19
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet20
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 13. -/
def step13 : Step := ⟨4, point13⟩
/-- Proposed owner constraints after 14 forced-point assignments. -/
def model14 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet17
    | 4 => pointSet23
    | 5 => pointSet19
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet20
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 14. -/
def step14 : Step := ⟨4, point14⟩
/-- Proposed owner constraints after 15 forced-point assignments. -/
def model15 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet17
    | 4 => pointSet24
    | 5 => pointSet19
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet20
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 15. -/
def step15 : Step := ⟨2, point15⟩
/-- Proposed owner constraints after 16 forced-point assignments. -/
def model16 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet25
    | 3 => pointSet17
    | 4 => pointSet24
    | 5 => pointSet19
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet20
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 16. -/
def step16 : Step := ⟨8, point16⟩
/-- Proposed owner constraints after 17 forced-point assignments. -/
def model17 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet25
    | 3 => pointSet17
    | 4 => pointSet24
    | 5 => pointSet19
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet26
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 17. -/
def step17 : Step := ⟨3, point17⟩
/-- Proposed owner constraints after 18 forced-point assignments. -/
def model18 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet25
    | 3 => pointSet27
    | 4 => pointSet24
    | 5 => pointSet19
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet26
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 18. -/
def step18 : Step := ⟨2, point18⟩
/-- Proposed owner constraints after 19 forced-point assignments. -/
def model19 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet28
    | 3 => pointSet27
    | 4 => pointSet24
    | 5 => pointSet19
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet26
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 19. -/
def step19 : Step := ⟨2, point19⟩
/-- Proposed owner constraints after 20 forced-point assignments. -/
def model20 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet29
    | 3 => pointSet27
    | 4 => pointSet24
    | 5 => pointSet19
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet26
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The shared step constants reproduce the original certificate trace exactly. -/
theorem trace_steps : [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10,
    step11, step12, step13, step14, step15, step16, step17, step18, step19] =
    Data.Sext300000310000.steps := by
  rfl

end Sext300000310000
end ConwaySoifer.Simplified.Certificates
