/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Data.Aown320000330000
public import LeanPool.ConwaySoifer.Certificates.KernelReplay

/-!
# Aown 320000 330000

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
namespace Aown320000330000

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point0 : IPoint := ([(-1440000000000)], [690000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point1 : IPoint := ([(-750000000000)], [(-690000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point2 : IPoint := ([(-750000000000)], [1440000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point3 : IPoint := ([1965000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point4 : IPoint := ([5415000000000], [3585000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point5 : IPoint := ([5760000000000], [2865000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point6 : IPoint := ([8625000000000], [(-3240000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point7 : IPoint := ([9000000000000], [4770000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point8 : IPoint := ([9000000000000], [4950000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point9 : IPoint := ([195000000000], [4680000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point10 : IPoint := ([2670000000000], [(-2670000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point11 : IPoint := ([3309000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point12 : IPoint := ([3375000000000], [2385000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point13 : IPoint := ([(-1286400000000), (-4020000000000)], [643200000000, 2010000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point14 : IPoint := ([(-643200000000), (-2010000000000)], [(-643200000000), (-2010000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point15 : IPoint := ([643200000000, 2010000000000], [(-1286400000000), (-4020000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point16 : IPoint := ([1286400000000, 4020000000000], [(-643200000000), (-2010000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point17 : IPoint := ([643200000000, 2010000000000], [643200000000, 2010000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point18 : IPoint := ([(-643200000000), (-2010000000000)], [1286400000000, 4020000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point19 : IPoint := ([6120000000000, (-9000000000000)], [2880000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point20 : IPoint := ([9000000000000], [(-2880000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point21 : IPoint := ([9000000000000], [4500000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point22 : IPoint := ([(-2880000000000), (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point23 : IPoint := ([2880000000000, 9000000000000], [6120000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point24 : IPoint := ([0], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point25 : IPoint := ([(-9000000000000)], [6120000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point26 : IPoint := ([(-6120000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point27 : IPoint := ([(-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point28 : IPoint := ([(-9000000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point29 : IPoint := ([(-6120000000000), 9000000000000], [(-2880000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point30 : IPoint := ([(-9000000000000)], [2880000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point31 : IPoint := ([(-2880000000000), (-9000000000000)], [(-6120000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point32 : IPoint := ([0], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point33 : IPoint := ([2880000000000, 9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point34 : IPoint := ([6120000000000, (-9000000000000)], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point35 : IPoint := ([9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point36 : IPoint := ([9000000000000], [(-6120000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point37 : IPoint := ([9000000000000], [6120000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point38 : IPoint := ([9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point39 : IPoint := ([6120000000000, (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point40 : IPoint := ([(-18000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point41 : IPoint := ([(-15120000000000), 9000000000000], [6120000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point42 : IPoint := ([(-15120000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point43 : IPoint := ([6120000000000, (-9000000000000)], [(-15120000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point44 : IPoint := ([9000000000000], [(-18000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point45 : IPoint := ([9000000000000], [(-15120000000000), 9000000000000])

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet0 : List IPoint := [point13, point14, point15, point16, point17, point18]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet1 : List IPoint := [point19, point20, point21]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet2 : List IPoint := [point22, point23, point24]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet3 : List IPoint := [point25, point26, point27]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet4 : List IPoint := [point28, point29, point30]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet5 : List IPoint := [point31, point32, point33]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet6 : List IPoint := [point34, point35, point36]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet7 : List IPoint := [point19, point37, point38, point39]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet8 : List IPoint := [point40, point41, point42]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet9 : List IPoint := [point43, point44, point45]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet10 : List IPoint := [point0, point14, point15, point16, point17, point18]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet11 : List IPoint := [point0, point1, point15, point16, point17, point18]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet12 : List IPoint := [point0, point1, point15, point16, point17, point2]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet13 : List IPoint := [point22, point23, point3]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet14 : List IPoint := [point22, point4, point3]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet15 : List IPoint := [point22, point5, point4, point3]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet16 : List IPoint := [point34, point35, point36, point6]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet17 : List IPoint := [point19, point20, point7]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet18 : List IPoint := [point19, point8, point38, point39]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet19 : List IPoint := [point0, point1, point15, point16, point9]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet20 : List IPoint := [point0, point1, point10, point9]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet21 : List IPoint := [point22, point5, point11]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet22 : List IPoint := [point0, point1, point10, point12, point9]

/-- Contact constraints shared by every state in this certificate trace. -/
def capsConstraints : Fin 10 → List Cap :=
  fun j =>
    match j.val with
    | 0 => []
    | 1 => [⟨point19, point27, false⟩]
    | 2 => [⟨point19, point35, true⟩]
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
def step5 : Step := ⟨2, point5⟩
/-- Proposed owner constraints after 6 forced-point assignments. -/
def model6 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet1
    | 2 => pointSet15
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 6. -/
def step6 : Step := ⟨6, point6⟩
/-- Proposed owner constraints after 7 forced-point assignments. -/
def model7 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet1
    | 2 => pointSet15
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet16
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 7. -/
def step7 : Step := ⟨1, point7⟩
/-- Proposed owner constraints after 8 forced-point assignments. -/
def model8 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet17
    | 2 => pointSet15
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet16
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 8. -/
def step8 : Step := ⟨7, point8⟩
/-- Proposed owner constraints after 9 forced-point assignments. -/
def model9 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet17
    | 2 => pointSet15
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet16
    | 7 => pointSet18
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 9. -/
def step9 : Step := ⟨0, point9⟩
/-- Proposed owner constraints after 10 forced-point assignments. -/
def model10 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet17
    | 2 => pointSet15
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet16
    | 7 => pointSet18
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 10. -/
def step10 : Step := ⟨0, point10⟩
/-- Proposed owner constraints after 11 forced-point assignments. -/
def model11 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet20
    | 1 => pointSet17
    | 2 => pointSet15
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet16
    | 7 => pointSet18
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 11. -/
def step11 : Step := ⟨2, point11⟩
/-- Proposed owner constraints after 12 forced-point assignments. -/
def model12 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet20
    | 1 => pointSet17
    | 2 => pointSet21
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet16
    | 7 => pointSet18
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 12. -/
def step12 : Step := ⟨0, point12⟩
/-- Proposed owner constraints after 13 forced-point assignments. -/
def model13 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet22
    | 1 => pointSet17
    | 2 => pointSet21
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet16
    | 7 => pointSet18
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The shared step constants reproduce the original certificate trace exactly. -/
theorem trace_steps : [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10,
    step11, step12] = Data.Aown320000330000.steps := by
  rfl

end Aown320000330000
end ConwaySoifer.Simplified.Certificates
