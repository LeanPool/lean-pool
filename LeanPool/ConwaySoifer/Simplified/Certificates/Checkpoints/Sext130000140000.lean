/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Data.Sext130000140000
public import LeanPool.ConwaySoifer.Certificates.KernelReplay

/-!
# Sext 130000 140000

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
namespace Sext130000140000

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point0 : IPoint := ([0], [540000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point1 : IPoint := ([375000000000], [360000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point2 : IPoint := ([1170000000000], [(-1170000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point3 : IPoint := ([9000000000000], [(-9735000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point4 : IPoint := ([6840000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point5 : IPoint := ([(-5880000000000)], [(-3120000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point6 : IPoint := ([4365000000000], [(-5490000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point7 : IPoint := ([4875000000000], [(-5265000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point8 : IPoint := ([4875000000000], [(-5235000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point9 : IPoint := ([(-14895000000000)], [5895000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point10 : IPoint := ([(-8250000000000)], [6894000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point11 : IPoint := ([(-6894000000000)], [6375000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point12 : IPoint := ([(-5175000000000)], [(-780000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point13 : IPoint := ([(-3510000000000)], [(-5115000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point14 : IPoint := ([(-3360000000000)], [(-5640000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point15 : IPoint := ([(-15894000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point16 : IPoint := ([(-12360000000000)], [3360000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point17 : IPoint := ([(-7875000000000)], [4320000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point18 : IPoint := ([(-4875000000000)], [4095000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point19 : IPoint := ([(-1170000000000)], [(-7455000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point20 : IPoint := ([(-14490000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point21 : IPoint := ([(-8220000000000)], [4095000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point22 : IPoint := ([(-5175000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point23 : IPoint := ([(-3255000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point24 : IPoint := ([(-585000000000)], [6375000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point25 : IPoint := ([(-360000000000)], [735000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point26 : IPoint := ([4005000000000], [(-5175000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point27 : IPoint := ([4875000000000], [(-6045000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point28 : IPoint := ([5490000000000], [(-5625000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point29 : IPoint := ([(-14145000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point30 : IPoint := ([(-9000000000000)], [3405000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point31 : IPoint := ([(-4875000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point32 : IPoint := ([(-4710000000000)], [4125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point33 : IPoint := ([(-780000000000)], [5955000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point34 : IPoint := ([(-11760000000000)], [8250000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point35 : IPoint := ([(-9000000000000)], [3360000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point36 : IPoint := ([(-5595000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point37 : IPoint := ([(-4500000000000)], [3915000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point38 : IPoint := ([(-1170000000000)], [5175000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point39 : IPoint := ([(-780000000000)], [4875000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point40 : IPoint := ([5145000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point41 : IPoint := ([5490000000000], [2385000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point42 : IPoint := ([7020000000000], [(-6645000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point43 : IPoint := ([(-5955000000000)], [7125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point44 : IPoint := ([(-5640000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point45 : IPoint := ([(-5625000000000)], [1170000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point46 : IPoint := ([(-5250000000000)], [8610000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point47 : IPoint := ([(-3540000000000)], [3540000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point48 : IPoint := ([(-1560000000000)], [5310000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point49 : IPoint := ([(-825000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point50 : IPoint := ([3510000000000], [3990000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point51 : IPoint := ([3510000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point52 : IPoint := ([7680000000000], [(-4680000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point53 : IPoint := ([3375000000000], [4680000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point54 : IPoint := ([(-670800000000), (-5160000000000)], [335400000000, 2580000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point55 : IPoint := ([(-335400000000), (-2580000000000)], [(-335400000000), (-2580000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point56 : IPoint := ([335400000000, 2580000000000], [(-670800000000), (-5160000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point57 : IPoint := ([670800000000, 5160000000000], [(-335400000000), (-2580000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point58 : IPoint := ([335400000000, 2580000000000], [335400000000, 2580000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point59 : IPoint := ([(-335400000000), (-2580000000000)], [670800000000, 5160000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point60 : IPoint := ([7830000000000, (-9000000000000)], [1170000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point61 : IPoint := ([9000000000000], [(-1170000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point62 : IPoint := ([9000000000000], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point63 : IPoint := ([(-1170000000000), (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point64 : IPoint := ([1170000000000, 9000000000000], [7830000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point65 : IPoint := ([0], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point66 : IPoint := ([(-9000000000000)], [7830000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point67 : IPoint := ([(-7830000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point68 : IPoint := ([(-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point69 : IPoint := ([(-9000000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point70 : IPoint := ([(-7830000000000), 9000000000000], [(-1170000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point71 : IPoint := ([(-9000000000000)], [1170000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point72 : IPoint := ([(-1170000000000), (-9000000000000)], [(-7830000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point73 : IPoint := ([0], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point74 : IPoint := ([1170000000000, 9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point75 : IPoint := ([7830000000000, (-9000000000000)], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point76 : IPoint := ([9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point77 : IPoint := ([7830000000000, (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point78 : IPoint := ([9000000000000], [7830000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point79 : IPoint := ([9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point80 : IPoint := ([(-18000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point81 : IPoint := ([(-16830000000000), 9000000000000], [7830000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point82 : IPoint := ([(-16830000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point83 : IPoint := ([7830000000000, (-9000000000000)], [(-16830000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point84 : IPoint := ([9000000000000], [(-18000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point85 : IPoint := ([9000000000000], [(-16830000000000), 9000000000000])

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet0 : List IPoint := [point54, point55, point56, point57, point58, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet1 : List IPoint := [point60, point61, point62]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet2 : List IPoint := [point63, point64, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet3 : List IPoint := [point66, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet4 : List IPoint := [point69, point70, point71]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet5 : List IPoint := [point72, point73, point74]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet6 : List IPoint := [point75, point76, point61]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet7 : List IPoint := [point77, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet8 : List IPoint := [point80, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet9 : List IPoint := [point83, point84, point85]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet10 : List IPoint := [point54, point55, point56, point57, point58, point0, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet11 : List IPoint := [point54, point55, point56, point57, point1, point0, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet12 : List IPoint := [point54, point55, point2, point1, point0, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet13 : List IPoint := [point83, point84, point3]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet14 : List IPoint := [point72, point73, point4]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet15 : List IPoint := [point69, point5, point71]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet16 : List IPoint := [point54, point55, point6, point1, point0, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet17 : List IPoint := [point54, point55, point6, point7, point1, point0, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet18 : List IPoint := [point54, point55, point6, point7, point8, point1, point0, point59]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet19 : List IPoint := [point80, point9, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet20 : List IPoint := [point66, point10, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet21 : List IPoint := [point66, point10, point11, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet22 : List IPoint := [point69, point5, point12, point71]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet23 : List IPoint := [point69, point5, point13, point12, point71]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet24 : List IPoint := [point69, point14, point13, point12, point71]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet25 : List IPoint := [point80, point9, point15]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet26 : List IPoint := [point80, point16, point15]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet27 : List IPoint := [point66, point17, point11, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet28 : List IPoint := [point66, point17, point18, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet29 : List IPoint := [point72, point73, point4, point19]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet30 : List IPoint := [point80, point16, point20]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet31 : List IPoint := [point66, point21, point18, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet32 : List IPoint := [point69, point14, point13, point22, point71]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet33 : List IPoint := [point23, point64, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet34 : List IPoint := [point23, point24, point64, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet35 : List IPoint := [point54, point55, point6, point7, point8, point1, point25]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet36 : List IPoint := [point54, point55, point26, point6, point7, point8, point1, point25]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet37 : List IPoint := [point54, point55, point26, point27, point8, point1, point25]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet38 : List IPoint := [point54, point55, point26, point27, point28, point1, point25]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet39 : List IPoint := [point80, point16, point29]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet40 : List IPoint := [point30, point18, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet41 : List IPoint := [point69, point14, point31, point71]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet42 : List IPoint := [point30, point18, point32, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet43 : List IPoint := [point23, point33, point64, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet44 : List IPoint := [point80, point16, point34, point29]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet45 : List IPoint := [point35, point18, point32, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet46 : List IPoint := [point36, point33, point64, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet47 : List IPoint := [point35, point37, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet48 : List IPoint := [point36, point38, point64, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet49 : List IPoint := [point36, point38, point39, point64, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet50 : List IPoint := [point40, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet51 : List IPoint := [point41, point61, point62, point60]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet52 : List IPoint := [point54, point55, point26, point27, point42, point1, point25]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet53 : List IPoint := [point35, point37, point43, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet54 : List IPoint := [point44, point38, point39, point64, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet55 : List IPoint := [point69, point14, point31, point45, point71]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet56 : List IPoint := [point44, point46, point38, point39, point64, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet57 : List IPoint := [point35, point47, point43, point67, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet58 : List IPoint := [point44, point46, point48, point39, point64, point65]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet59 : List IPoint := [point49, point26, point27, point42, point1, point25, point54]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet60 : List IPoint := [point50, point61, point62, point60]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet61 : List IPoint := [point51, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet62 : List IPoint := [point50, point52, point61, point62, point60]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet63 : List IPoint := [point49, point26, point27, point42, point53, point25, point54]

/-- Contact constraints shared by every state in this certificate trace. -/
def capsConstraints : Fin 10 → List Cap :=
  fun j =>
    match j.val with
    | 0 => []
    | 1 => [⟨point61, point73, false⟩]
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
def step3 : Step := ⟨9, point3⟩
/-- Proposed owner constraints after 4 forced-point assignments. -/
def model4 : Model :=
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
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 4. -/
def step4 : Step := ⟨5, point4⟩
/-- Proposed owner constraints after 5 forced-point assignments. -/
def model5 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 5. -/
def step5 : Step := ⟨4, point5⟩
/-- Proposed owner constraints after 6 forced-point assignments. -/
def model6 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet15
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 6. -/
def step6 : Step := ⟨0, point6⟩
/-- Proposed owner constraints after 7 forced-point assignments. -/
def model7 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet16
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet15
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 7. -/
def step7 : Step := ⟨0, point7⟩
/-- Proposed owner constraints after 8 forced-point assignments. -/
def model8 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet17
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet15
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 8. -/
def step8 : Step := ⟨0, point8⟩
/-- Proposed owner constraints after 9 forced-point assignments. -/
def model9 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet15
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 9. -/
def step9 : Step := ⟨8, point9⟩
/-- Proposed owner constraints after 10 forced-point assignments. -/
def model10 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet15
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet19
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 10. -/
def step10 : Step := ⟨3, point10⟩
/-- Proposed owner constraints after 11 forced-point assignments. -/
def model11 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet20
    | 4 => pointSet15
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet19
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 11. -/
def step11 : Step := ⟨3, point11⟩
/-- Proposed owner constraints after 12 forced-point assignments. -/
def model12 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet21
    | 4 => pointSet15
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet19
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 12. -/
def step12 : Step := ⟨4, point12⟩
/-- Proposed owner constraints after 13 forced-point assignments. -/
def model13 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet21
    | 4 => pointSet22
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet19
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 13. -/
def step13 : Step := ⟨4, point13⟩
/-- Proposed owner constraints after 14 forced-point assignments. -/
def model14 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet21
    | 4 => pointSet23
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet19
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 14. -/
def step14 : Step := ⟨4, point14⟩
/-- Proposed owner constraints after 15 forced-point assignments. -/
def model15 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet21
    | 4 => pointSet24
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet19
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 15. -/
def step15 : Step := ⟨8, point15⟩
/-- Proposed owner constraints after 16 forced-point assignments. -/
def model16 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet21
    | 4 => pointSet24
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet25
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 16. -/
def step16 : Step := ⟨8, point16⟩
/-- Proposed owner constraints after 17 forced-point assignments. -/
def model17 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet21
    | 4 => pointSet24
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet26
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 17. -/
def step17 : Step := ⟨3, point17⟩
/-- Proposed owner constraints after 18 forced-point assignments. -/
def model18 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet27
    | 4 => pointSet24
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet26
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 18. -/
def step18 : Step := ⟨3, point18⟩
/-- Proposed owner constraints after 19 forced-point assignments. -/
def model19 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet28
    | 4 => pointSet24
    | 5 => pointSet14
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet26
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 19. -/
def step19 : Step := ⟨5, point19⟩
/-- Proposed owner constraints after 20 forced-point assignments. -/
def model20 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet28
    | 4 => pointSet24
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet26
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 20. -/
def step20 : Step := ⟨8, point20⟩
/-- Proposed owner constraints after 21 forced-point assignments. -/
def model21 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet28
    | 4 => pointSet24
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet30
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 21. -/
def step21 : Step := ⟨3, point21⟩
/-- Proposed owner constraints after 22 forced-point assignments. -/
def model22 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet31
    | 4 => pointSet24
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet30
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 22. -/
def step22 : Step := ⟨4, point22⟩
/-- Proposed owner constraints after 23 forced-point assignments. -/
def model23 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet31
    | 4 => pointSet32
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet30
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 23. -/
def step23 : Step := ⟨2, point23⟩
/-- Proposed owner constraints after 24 forced-point assignments. -/
def model24 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet33
    | 3 => pointSet31
    | 4 => pointSet32
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet30
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 24. -/
def step24 : Step := ⟨2, point24⟩
/-- Proposed owner constraints after 25 forced-point assignments. -/
def model25 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet18
    | 1 => pointSet1
    | 2 => pointSet34
    | 3 => pointSet31
    | 4 => pointSet32
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet30
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 25. -/
def step25 : Step := ⟨0, point25⟩
/-- Proposed owner constraints after 26 forced-point assignments. -/
def model26 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet35
    | 1 => pointSet1
    | 2 => pointSet34
    | 3 => pointSet31
    | 4 => pointSet32
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet30
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 26. -/
def step26 : Step := ⟨0, point26⟩
/-- Proposed owner constraints after 27 forced-point assignments. -/
def model27 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet36
    | 1 => pointSet1
    | 2 => pointSet34
    | 3 => pointSet31
    | 4 => pointSet32
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet30
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 27. -/
def step27 : Step := ⟨0, point27⟩
/-- Proposed owner constraints after 28 forced-point assignments. -/
def model28 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet37
    | 1 => pointSet1
    | 2 => pointSet34
    | 3 => pointSet31
    | 4 => pointSet32
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet30
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 28. -/
def step28 : Step := ⟨0, point28⟩
/-- Proposed owner constraints after 29 forced-point assignments. -/
def model29 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet34
    | 3 => pointSet31
    | 4 => pointSet32
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet30
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 29. -/
def step29 : Step := ⟨8, point29⟩
/-- Proposed owner constraints after 30 forced-point assignments. -/
def model30 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet34
    | 3 => pointSet31
    | 4 => pointSet32
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet39
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 30. -/
def step30 : Step := ⟨3, point30⟩
/-- Proposed owner constraints after 31 forced-point assignments. -/
def model31 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet34
    | 3 => pointSet40
    | 4 => pointSet32
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet39
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 31. -/
def step31 : Step := ⟨4, point31⟩
/-- Proposed owner constraints after 32 forced-point assignments. -/
def model32 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet34
    | 3 => pointSet40
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet39
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 32. -/
def step32 : Step := ⟨3, point32⟩
/-- Proposed owner constraints after 33 forced-point assignments. -/
def model33 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet34
    | 3 => pointSet42
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet39
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 33. -/
def step33 : Step := ⟨2, point33⟩
/-- Proposed owner constraints after 34 forced-point assignments. -/
def model34 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet43
    | 3 => pointSet42
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet39
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 34. -/
def step34 : Step := ⟨8, point34⟩
/-- Proposed owner constraints after 35 forced-point assignments. -/
def model35 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet43
    | 3 => pointSet42
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 35. -/
def step35 : Step := ⟨3, point35⟩
/-- Proposed owner constraints after 36 forced-point assignments. -/
def model36 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet43
    | 3 => pointSet45
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 36. -/
def step36 : Step := ⟨2, point36⟩
/-- Proposed owner constraints after 37 forced-point assignments. -/
def model37 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet46
    | 3 => pointSet45
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 37. -/
def step37 : Step := ⟨3, point37⟩
/-- Proposed owner constraints after 38 forced-point assignments. -/
def model38 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet46
    | 3 => pointSet47
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 38. -/
def step38 : Step := ⟨2, point38⟩
/-- Proposed owner constraints after 39 forced-point assignments. -/
def model39 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet48
    | 3 => pointSet47
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 39. -/
def step39 : Step := ⟨2, point39⟩
/-- Proposed owner constraints after 40 forced-point assignments. -/
def model40 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet49
    | 3 => pointSet47
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 40. -/
def step40 : Step := ⟨7, point40⟩
/-- Proposed owner constraints after 41 forced-point assignments. -/
def model41 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet1
    | 2 => pointSet49
    | 3 => pointSet47
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet50
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 41. -/
def step41 : Step := ⟨1, point41⟩
/-- Proposed owner constraints after 42 forced-point assignments. -/
def model42 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet38
    | 1 => pointSet51
    | 2 => pointSet49
    | 3 => pointSet47
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet50
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 42. -/
def step42 : Step := ⟨0, point42⟩
/-- Proposed owner constraints after 43 forced-point assignments. -/
def model43 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet52
    | 1 => pointSet51
    | 2 => pointSet49
    | 3 => pointSet47
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet50
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 43. -/
def step43 : Step := ⟨3, point43⟩
/-- Proposed owner constraints after 44 forced-point assignments. -/
def model44 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet52
    | 1 => pointSet51
    | 2 => pointSet49
    | 3 => pointSet53
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet50
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 44. -/
def step44 : Step := ⟨2, point44⟩
/-- Proposed owner constraints after 45 forced-point assignments. -/
def model45 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet52
    | 1 => pointSet51
    | 2 => pointSet54
    | 3 => pointSet53
    | 4 => pointSet41
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet50
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 45. -/
def step45 : Step := ⟨4, point45⟩
/-- Proposed owner constraints after 46 forced-point assignments. -/
def model46 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet52
    | 1 => pointSet51
    | 2 => pointSet54
    | 3 => pointSet53
    | 4 => pointSet55
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet50
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 46. -/
def step46 : Step := ⟨2, point46⟩
/-- Proposed owner constraints after 47 forced-point assignments. -/
def model47 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet52
    | 1 => pointSet51
    | 2 => pointSet56
    | 3 => pointSet53
    | 4 => pointSet55
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet50
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 47. -/
def step47 : Step := ⟨3, point47⟩
/-- Proposed owner constraints after 48 forced-point assignments. -/
def model48 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet52
    | 1 => pointSet51
    | 2 => pointSet56
    | 3 => pointSet57
    | 4 => pointSet55
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet50
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 48. -/
def step48 : Step := ⟨2, point48⟩
/-- Proposed owner constraints after 49 forced-point assignments. -/
def model49 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet52
    | 1 => pointSet51
    | 2 => pointSet58
    | 3 => pointSet57
    | 4 => pointSet55
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet50
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 49. -/
def step49 : Step := ⟨0, point49⟩
/-- Proposed owner constraints after 50 forced-point assignments. -/
def model50 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet59
    | 1 => pointSet51
    | 2 => pointSet58
    | 3 => pointSet57
    | 4 => pointSet55
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet50
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 50. -/
def step50 : Step := ⟨1, point50⟩
/-- Proposed owner constraints after 51 forced-point assignments. -/
def model51 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet59
    | 1 => pointSet60
    | 2 => pointSet58
    | 3 => pointSet57
    | 4 => pointSet55
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet50
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 51. -/
def step51 : Step := ⟨7, point51⟩
/-- Proposed owner constraints after 52 forced-point assignments. -/
def model52 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet59
    | 1 => pointSet60
    | 2 => pointSet58
    | 3 => pointSet57
    | 4 => pointSet55
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet61
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 52. -/
def step52 : Step := ⟨1, point52⟩
/-- Proposed owner constraints after 53 forced-point assignments. -/
def model53 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet59
    | 1 => pointSet62
    | 2 => pointSet58
    | 3 => pointSet57
    | 4 => pointSet55
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet61
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 53. -/
def step53 : Step := ⟨0, point53⟩
/-- Proposed owner constraints after 54 forced-point assignments. -/
def model54 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet63
    | 1 => pointSet62
    | 2 => pointSet58
    | 3 => pointSet57
    | 4 => pointSet55
    | 5 => pointSet29
    | 6 => pointSet6
    | 7 => pointSet61
    | 8 => pointSet44
    | _ => pointSet13), capsConstraints, ownerFlags⟩

/-- The shared step constants reproduce the original certificate trace exactly. -/
theorem trace_steps : [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10,
    step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22,
    step23, step24, step25, step26, step27, step28, step29, step30, step31, step32, step33, step34,
    step35, step36, step37, step38, step39, step40, step41, step42, step43, step44, step45, step46,
    step47, step48, step49, step50, step51, step52, step53] = Data.Sext130000140000.steps := by
  rfl

end Sext130000140000
end ConwaySoifer.Simplified.Certificates
