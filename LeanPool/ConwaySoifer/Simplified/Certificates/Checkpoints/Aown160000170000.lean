/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Data.Aown160000170000
public import LeanPool.ConwaySoifer.Certificates.KernelReplay

/-!
# Aown 160000 170000

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
namespace Aown160000170000

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point0 : IPoint := ([(-660000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point1 : IPoint := ([(-660000000000)], [660000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point2 : IPoint := ([0], [(-660000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point3 : IPoint := ([0], [660000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point4 : IPoint := ([660000000000], [(-660000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point5 : IPoint := ([1440000000000], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point6 : IPoint := ([3000000000000], [6000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point7 : IPoint := ([7125000000000], [1395000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point8 : IPoint := ([9000000000000], [(-5985000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point9 : IPoint := ([9000000000000], [4680000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point10 : IPoint := ([9000000000000], [6840000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point11 : IPoint := ([(-2820000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point12 : IPoint := ([0], [1440000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point13 : IPoint := ([1170000000000], [(-8250000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point14 : IPoint := ([2592000000000], [1533000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point15 : IPoint := ([3285000000000], [5715000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point16 : IPoint := ([4320000000000], [1500000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point17 : IPoint := ([5310000000000], [1440000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point18 : IPoint := ([5790000000000], [3210000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point19 : IPoint := ([6390000000000], [360000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point20 : IPoint := ([7125000000000], [1440000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point21 : IPoint := ([8385000000000], [(-14760000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point22 : IPoint := ([9000000000000], [(-5715000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point23 : IPoint := ([(-11820000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point24 : IPoint := ([(-8040000000000)], [3825000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point25 : IPoint := ([(-3750000000000)], [480000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point26 : IPoint := ([(-2805000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point27 : IPoint := ([(-2250000000000)], [2970000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point28 : IPoint := ([342000000000], [(-6750000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point29 : IPoint := ([495000000000], [5625000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point30 : IPoint := ([1530000000000], [(-8280000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point31 : IPoint := ([2955000000000], [4125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point32 : IPoint := ([5250000000000], [2520000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point33 : IPoint := ([6840000000000], [(-3090000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point34 : IPoint := ([6915000000000], [1125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point35 : IPoint := ([9000000000000], [(-3315000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point36 : IPoint := ([(-12135000000000)], [3135000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point37 : IPoint := ([(-11445000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point38 : IPoint := ([(-8385000000000)], [5760000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point39 : IPoint := ([(-7470000000000)], [(-1530000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point40 : IPoint := ([(-5400000000000)], [4275000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point41 : IPoint := ([(-4380000000000)], [(-4620000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point42 : IPoint := ([(-2460000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point43 : IPoint := ([(-1440000000000)], [5625000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point44 : IPoint := ([(-1185000000000)], [7560000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point45 : IPoint := ([0], [(-1335000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point46 : IPoint := ([1275000000000], [(-1275000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point47 : IPoint := ([4125000000000], [(-8040000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point48 : IPoint := ([(-796800000000), (-4980000000000)], [398400000000, 2490000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point49 : IPoint := ([(-398400000000), (-2490000000000)], [(-398400000000), (-2490000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point50 : IPoint := ([398400000000, 2490000000000], [(-796800000000), (-4980000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point51 : IPoint := ([796800000000, 4980000000000], [(-398400000000), (-2490000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point52 : IPoint := ([398400000000, 2490000000000], [398400000000, 2490000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point53 : IPoint := ([(-398400000000), (-2490000000000)], [796800000000, 4980000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point54 : IPoint := ([7560000000000, (-9000000000000)], [1440000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point55 : IPoint := ([9000000000000], [(-1440000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point56 : IPoint := ([9000000000000], [4500000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point57 : IPoint := ([(-1440000000000), (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point58 : IPoint := ([1440000000000, 9000000000000], [7560000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point59 : IPoint := ([0], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point60 : IPoint := ([(-9000000000000)], [7560000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point61 : IPoint := ([(-7560000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point62 : IPoint := ([(-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point63 : IPoint := ([(-9000000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point64 : IPoint := ([(-7560000000000), 9000000000000], [(-1440000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point65 : IPoint := ([(-9000000000000)], [1440000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point66 : IPoint := ([(-1440000000000), (-9000000000000)], [(-7560000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point67 : IPoint := ([0], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point68 : IPoint := ([1440000000000, 9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point69 : IPoint := ([7560000000000, (-9000000000000)], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point70 : IPoint := ([9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point71 : IPoint := ([9000000000000], [(-7560000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point72 : IPoint := ([9000000000000], [7560000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point73 : IPoint := ([9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point74 : IPoint := ([7560000000000, (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point75 : IPoint := ([(-18000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point76 : IPoint := ([(-16560000000000), 9000000000000], [7560000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point77 : IPoint := ([(-16560000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point78 : IPoint := ([7560000000000, (-9000000000000)], [(-16560000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point79 : IPoint := ([9000000000000], [(-18000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point80 : IPoint := ([9000000000000], [(-16560000000000), 9000000000000])

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet0 : List IPoint := [point48, point49, point50, point51, point52, point53]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet1 : List IPoint := [point54, point55, point56]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet2 : List IPoint := [point57, point58, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet3 : List IPoint := [point60, point61, point62]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet4 : List IPoint := [point63, point64, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet5 : List IPoint := [point66, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet6 : List IPoint := [point69, point70, point71]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet7 : List IPoint := [point54, point72, point73, point74]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet8 : List IPoint := [point75, point76, point77]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet9 : List IPoint := [point78, point79, point80]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet10 : List IPoint := [point48, point0, point49, point50, point51, point52, point53]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet11 : List IPoint := [point48, point0, point49, point50, point51, point52, point53,
    point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet12 : List IPoint := [point48, point0, point49, point2, point50, point51, point52,
    point53, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet13 : List IPoint := [point48, point0, point49, point2, point50, point51, point52,
    point3, point53, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet14 : List IPoint := [point48, point0, point49, point2, point50, point4, point51,
    point52, point3, point53, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet15 : List IPoint := [point48, point0, point49, point2, point50, point4, point5, point3,
    point53, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet16 : List IPoint := [point57, point6, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet17 : List IPoint := [point57, point7, point6, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet18 : List IPoint := [point69, point70, point8]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet19 : List IPoint := [point54, point55, point9]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet20 : List IPoint := [point54, point10, point73, point74]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet21 : List IPoint := [point60, point11, point62]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet22 : List IPoint := [point48, point0, point49, point2, point50, point4, point5, point12,
    point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet23 : List IPoint := [point66, point67, point68, point13]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet24 : List IPoint := [point48, point0, point49, point2, point50, point4, point5, point14,
    point12, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet25 : List IPoint := [point57, point7, point15, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet26 : List IPoint := [point48, point0, point49, point2, point50, point4, point16,
    point14, point12, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet27 : List IPoint := [point48, point0, point49, point2, point50, point17, point16,
    point14, point12, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet28 : List IPoint := [point57, point7, point18, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet29 : List IPoint := [point48, point0, point49, point2, point50, point19, point17,
    point16, point14, point12, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet30 : List IPoint := [point57, point7, point20, point18, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet31 : List IPoint := [point78, point79, point80, point21]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet32 : List IPoint := [point69, point70, point22]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet33 : List IPoint := [point75, point76, point23]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet34 : List IPoint := [point63, point64, point24, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet35 : List IPoint := [point63, point64, point25, point24, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet36 : List IPoint := [point60, point26, point62]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet37 : List IPoint := [point60, point27, point26, point62]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet38 : List IPoint := [point66, point67, point68, point13, point28]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet39 : List IPoint := [point48, point0, point49, point2, point50, point19, point17,
    point29]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet40 : List IPoint := [point66, point67, point68, point30, point28]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet41 : List IPoint := [point48, point0, point49, point2, point50, point19, point31,
    point29]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet42 : List IPoint := [point57, point32, point7, point20, point18, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet43 : List IPoint := [point33, point69, point70, point22]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet44 : List IPoint := [point57, point32, point34, point7, point20, point18, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet45 : List IPoint := [point33, point69, point70, point35]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet46 : List IPoint := [point75, point36, point23]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet47 : List IPoint := [point75, point36, point37]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet48 : List IPoint := [point63, point64, point25, point38, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet49 : List IPoint := [point63, point39, point25, point38, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet50 : List IPoint := [point60, point40, point27, point26, point62]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet51 : List IPoint := [point41, point67, point68, point30, point28]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet52 : List IPoint := [point60, point40, point27, point42, point62]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet53 : List IPoint := [point43, point48, point0, point49, point2, point50, point19,
    point31, point29]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet54 : List IPoint := [point43, point48, point0, point49, point2, point50, point19,
    point31, point44]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet55 : List IPoint := [point41, point67, point68, point30, point45]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet56 : List IPoint := [point46, point69, point70, point35]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet57 : List IPoint := [point41, point67, point68, point47, point45]

/-- Contact constraints shared by every state in this certificate trace. -/
def capsConstraints : Fin 10 → List Cap :=
  fun j =>
    match j.val with
    | 0 => []
    | 1 => [⟨point54, point62, false⟩]
    | 2 => [⟨point54, point70, true⟩]
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
def step6 : Step := ⟨2, point6⟩
/-- Proposed owner constraints after 7 forced-point assignments. -/
def model7 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet16
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 7. -/
def step7 : Step := ⟨2, point7⟩
/-- Proposed owner constraints after 8 forced-point assignments. -/
def model8 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet17
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 8. -/
def step8 : Step := ⟨6, point8⟩
/-- Proposed owner constraints after 9 forced-point assignments. -/
def model9 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet1
    | 2 => pointSet17
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet18
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 9. -/
def step9 : Step := ⟨1, point9⟩
/-- Proposed owner constraints after 10 forced-point assignments. -/
def model10 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet19
    | 2 => pointSet17
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet18
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 10. -/
def step10 : Step := ⟨7, point10⟩
/-- Proposed owner constraints after 11 forced-point assignments. -/
def model11 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet19
    | 2 => pointSet17
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 11. -/
def step11 : Step := ⟨3, point11⟩
/-- Proposed owner constraints after 12 forced-point assignments. -/
def model12 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet15
    | 1 => pointSet19
    | 2 => pointSet17
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 12. -/
def step12 : Step := ⟨0, point12⟩
/-- Proposed owner constraints after 13 forced-point assignments. -/
def model13 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet19
    | 2 => pointSet17
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 13. -/
def step13 : Step := ⟨5, point13⟩
/-- Proposed owner constraints after 14 forced-point assignments. -/
def model14 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet19
    | 2 => pointSet17
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 14. -/
def step14 : Step := ⟨0, point14⟩
/-- Proposed owner constraints after 15 forced-point assignments. -/
def model15 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet24
    | 1 => pointSet19
    | 2 => pointSet17
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 15. -/
def step15 : Step := ⟨2, point15⟩
/-- Proposed owner constraints after 16 forced-point assignments. -/
def model16 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet24
    | 1 => pointSet19
    | 2 => pointSet25
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 16. -/
def step16 : Step := ⟨0, point16⟩
/-- Proposed owner constraints after 17 forced-point assignments. -/
def model17 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet26
    | 1 => pointSet19
    | 2 => pointSet25
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 17. -/
def step17 : Step := ⟨0, point17⟩
/-- Proposed owner constraints after 18 forced-point assignments. -/
def model18 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet27
    | 1 => pointSet19
    | 2 => pointSet25
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 18. -/
def step18 : Step := ⟨2, point18⟩
/-- Proposed owner constraints after 19 forced-point assignments. -/
def model19 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet27
    | 1 => pointSet19
    | 2 => pointSet28
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 19. -/
def step19 : Step := ⟨0, point19⟩
/-- Proposed owner constraints after 20 forced-point assignments. -/
def model20 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet29
    | 1 => pointSet19
    | 2 => pointSet28
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 20. -/
def step20 : Step := ⟨2, point20⟩
/-- Proposed owner constraints after 21 forced-point assignments. -/
def model21 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet29
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 21. -/
def step21 : Step := ⟨9, point21⟩
/-- Proposed owner constraints after 22 forced-point assignments. -/
def model22 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet29
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet18
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 22. -/
def step22 : Step := ⟨6, point22⟩
/-- Proposed owner constraints after 23 forced-point assignments. -/
def model23 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet29
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet32
    | 7 => pointSet20
    | 8 => pointSet8
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 23. -/
def step23 : Step := ⟨8, point23⟩
/-- Proposed owner constraints after 24 forced-point assignments. -/
def model24 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet29
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet21
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet32
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 24. -/
def step24 : Step := ⟨4, point24⟩
/-- Proposed owner constraints after 25 forced-point assignments. -/
def model25 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet29
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet21
    | 4 => pointSet34
    | 5 => pointSet23
    | 6 => pointSet32
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 25. -/
def step25 : Step := ⟨4, point25⟩
/-- Proposed owner constraints after 26 forced-point assignments. -/
def model26 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet29
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet21
    | 4 => pointSet35
    | 5 => pointSet23
    | 6 => pointSet32
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 26. -/
def step26 : Step := ⟨3, point26⟩
/-- Proposed owner constraints after 27 forced-point assignments. -/
def model27 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet29
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet36
    | 4 => pointSet35
    | 5 => pointSet23
    | 6 => pointSet32
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 27. -/
def step27 : Step := ⟨3, point27⟩
/-- Proposed owner constraints after 28 forced-point assignments. -/
def model28 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet29
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet37
    | 4 => pointSet35
    | 5 => pointSet23
    | 6 => pointSet32
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 28. -/
def step28 : Step := ⟨5, point28⟩
/-- Proposed owner constraints after 29 forced-point assignments. -/
def model29 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet29
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet37
    | 4 => pointSet35
    | 5 => pointSet38
    | 6 => pointSet32
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 29. -/
def step29 : Step := ⟨0, point29⟩
/-- Proposed owner constraints after 30 forced-point assignments. -/
def model30 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet39
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet37
    | 4 => pointSet35
    | 5 => pointSet38
    | 6 => pointSet32
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 30. -/
def step30 : Step := ⟨5, point30⟩
/-- Proposed owner constraints after 31 forced-point assignments. -/
def model31 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet39
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet37
    | 4 => pointSet35
    | 5 => pointSet40
    | 6 => pointSet32
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 31. -/
def step31 : Step := ⟨0, point31⟩
/-- Proposed owner constraints after 32 forced-point assignments. -/
def model32 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet30
    | 3 => pointSet37
    | 4 => pointSet35
    | 5 => pointSet40
    | 6 => pointSet32
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 32. -/
def step32 : Step := ⟨2, point32⟩
/-- Proposed owner constraints after 33 forced-point assignments. -/
def model33 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet42
    | 3 => pointSet37
    | 4 => pointSet35
    | 5 => pointSet40
    | 6 => pointSet32
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 33. -/
def step33 : Step := ⟨6, point33⟩
/-- Proposed owner constraints after 34 forced-point assignments. -/
def model34 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet42
    | 3 => pointSet37
    | 4 => pointSet35
    | 5 => pointSet40
    | 6 => pointSet43
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 34. -/
def step34 : Step := ⟨2, point34⟩
/-- Proposed owner constraints after 35 forced-point assignments. -/
def model35 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet37
    | 4 => pointSet35
    | 5 => pointSet40
    | 6 => pointSet43
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 35. -/
def step35 : Step := ⟨6, point35⟩
/-- Proposed owner constraints after 36 forced-point assignments. -/
def model36 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet37
    | 4 => pointSet35
    | 5 => pointSet40
    | 6 => pointSet45
    | 7 => pointSet20
    | 8 => pointSet33
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 36. -/
def step36 : Step := ⟨8, point36⟩
/-- Proposed owner constraints after 37 forced-point assignments. -/
def model37 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet37
    | 4 => pointSet35
    | 5 => pointSet40
    | 6 => pointSet45
    | 7 => pointSet20
    | 8 => pointSet46
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 37. -/
def step37 : Step := ⟨8, point37⟩
/-- Proposed owner constraints after 38 forced-point assignments. -/
def model38 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet37
    | 4 => pointSet35
    | 5 => pointSet40
    | 6 => pointSet45
    | 7 => pointSet20
    | 8 => pointSet47
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 38. -/
def step38 : Step := ⟨4, point38⟩
/-- Proposed owner constraints after 39 forced-point assignments. -/
def model39 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet37
    | 4 => pointSet48
    | 5 => pointSet40
    | 6 => pointSet45
    | 7 => pointSet20
    | 8 => pointSet47
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 39. -/
def step39 : Step := ⟨4, point39⟩
/-- Proposed owner constraints after 40 forced-point assignments. -/
def model40 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet37
    | 4 => pointSet49
    | 5 => pointSet40
    | 6 => pointSet45
    | 7 => pointSet20
    | 8 => pointSet47
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 40. -/
def step40 : Step := ⟨3, point40⟩
/-- Proposed owner constraints after 41 forced-point assignments. -/
def model41 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet50
    | 4 => pointSet49
    | 5 => pointSet40
    | 6 => pointSet45
    | 7 => pointSet20
    | 8 => pointSet47
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 41. -/
def step41 : Step := ⟨5, point41⟩
/-- Proposed owner constraints after 42 forced-point assignments. -/
def model42 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet50
    | 4 => pointSet49
    | 5 => pointSet51
    | 6 => pointSet45
    | 7 => pointSet20
    | 8 => pointSet47
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 42. -/
def step42 : Step := ⟨3, point42⟩
/-- Proposed owner constraints after 43 forced-point assignments. -/
def model43 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet52
    | 4 => pointSet49
    | 5 => pointSet51
    | 6 => pointSet45
    | 7 => pointSet20
    | 8 => pointSet47
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 43. -/
def step43 : Step := ⟨0, point43⟩
/-- Proposed owner constraints after 44 forced-point assignments. -/
def model44 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet53
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet52
    | 4 => pointSet49
    | 5 => pointSet51
    | 6 => pointSet45
    | 7 => pointSet20
    | 8 => pointSet47
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 44. -/
def step44 : Step := ⟨0, point44⟩
/-- Proposed owner constraints after 45 forced-point assignments. -/
def model45 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet54
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet52
    | 4 => pointSet49
    | 5 => pointSet51
    | 6 => pointSet45
    | 7 => pointSet20
    | 8 => pointSet47
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 45. -/
def step45 : Step := ⟨5, point45⟩
/-- Proposed owner constraints after 46 forced-point assignments. -/
def model46 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet54
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet52
    | 4 => pointSet49
    | 5 => pointSet55
    | 6 => pointSet45
    | 7 => pointSet20
    | 8 => pointSet47
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 46. -/
def step46 : Step := ⟨6, point46⟩
/-- Proposed owner constraints after 47 forced-point assignments. -/
def model47 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet54
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet52
    | 4 => pointSet49
    | 5 => pointSet55
    | 6 => pointSet56
    | 7 => pointSet20
    | 8 => pointSet47
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 47. -/
def step47 : Step := ⟨5, point47⟩
/-- Proposed owner constraints after 48 forced-point assignments. -/
def model48 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet54
    | 1 => pointSet19
    | 2 => pointSet44
    | 3 => pointSet52
    | 4 => pointSet49
    | 5 => pointSet57
    | 6 => pointSet56
    | 7 => pointSet20
    | 8 => pointSet47
    | _ => pointSet31), capsConstraints, ownerFlags⟩

/-- The shared step constants reproduce the original certificate trace exactly. -/
theorem trace_steps : [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10,
    step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22,
    step23, step24, step25, step26, step27, step28, step29, step30, step31, step32, step33, step34,
    step35, step36, step37, step38, step39, step40, step41, step42, step43, step44, step45, step46,
    step47] = Data.Aown160000170000.steps := by
  rfl

end Aown160000170000
end ConwaySoifer.Simplified.Certificates
