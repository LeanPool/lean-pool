/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Data.Across012500017500
public import LeanPool.ConwaySoifer.Certificates.KernelReplay

/-!
# Across 012500 017500

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
namespace Across012500017500

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point0 : IPoint := ([8325000000000], [1125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point1 : IPoint := ([9000000000000], [1125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point2 : IPoint := ([8250000000000], [675000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point3 : IPoint := ([8625000000000], [150000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point4 : IPoint := ([375000000000], [(-225000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point5 : IPoint := ([3000000000000], [(-37500000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point6 : IPoint := ([(-73687500000), (-5895000000000)], [36843750000, 2947500000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point7 : IPoint := ([(-36843750000), (-2947500000000)], [(-36843750000), (-2947500000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point8 : IPoint := ([36843750000, 2947500000000], [(-73687500000), (-5895000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point9 : IPoint := ([73687500000, 5895000000000], [(-36843750000), (-2947500000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point10 : IPoint := ([36843750000, 2947500000000], [36843750000, 2947500000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point11 : IPoint := ([(-36843750000), (-2947500000000)], [73687500000, 5895000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point12 : IPoint := ([8887500000000, (-9000000000000)], [112500000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point13 : IPoint := ([9000000000000], [(-112500000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point14 : IPoint := ([9000000000000], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point15 : IPoint := ([(-112500000000), (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point16 : IPoint := ([112500000000, 9000000000000], [8887500000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point17 : IPoint := ([9000000000000], [4500000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point18 : IPoint := ([0], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point19 : IPoint := ([(-9000000000000)], [8887500000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point20 : IPoint := ([(-8887500000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point21 : IPoint := ([(-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point22 : IPoint := ([(-9000000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point23 : IPoint := ([(-8887500000000), 9000000000000], [(-112500000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point24 : IPoint := ([(-9000000000000)], [112500000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point25 : IPoint := ([(-112500000000), (-9000000000000)], [(-8887500000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point26 : IPoint := ([0], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point27 : IPoint := ([112500000000, 9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point28 : IPoint := ([8887500000000, (-9000000000000)], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point29 : IPoint := ([9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point30 : IPoint := ([9000000000000], [(-8887500000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point31 : IPoint := ([9000000000000], [8887500000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point32 : IPoint := ([9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point33 : IPoint := ([8887500000000, (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point34 : IPoint := ([(-18000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point35 : IPoint := ([(-17887500000000), 9000000000000], [8887500000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point36 : IPoint := ([(-17887500000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point37 : IPoint := ([8887500000000, (-9000000000000)], [(-17887500000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point38 : IPoint := ([9000000000000], [(-18000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point39 : IPoint := ([9000000000000], [(-17887500000000), 9000000000000])

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet0 : List IPoint := [point6, point7, point8, point9, point10, point11]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet1 : List IPoint := [point12, point13, point14]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet2 : List IPoint := [point15, point16, point17, point18]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet3 : List IPoint := [point19, point20, point21]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet4 : List IPoint := [point22, point23, point24]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet5 : List IPoint := [point25, point26, point27]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet6 : List IPoint := [point28, point29, point30]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet7 : List IPoint := [point12, point31, point32, point33]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet8 : List IPoint := [point34, point35, point36]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet9 : List IPoint := [point37, point38, point39]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet10 : List IPoint := [point0, point12, point31, point32, point33]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet11 : List IPoint := [point12, point13, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet12 : List IPoint := [point6, point7, point8, point2, point11]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet13 : List IPoint := [point6, point7, point8, point3, point2, point11]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet14 : List IPoint := [point4, point28, point29, point30]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet15 : List IPoint := [point4, point28, point29, point30, point5]

/-- Contact constraints shared by every state in this certificate trace. -/
def capsConstraints : Fin 10 → List Cap :=
  fun j =>
    match j.val with
    | 0 => []
    | 1 => [⟨point12, point21, false⟩]
    | 2 => [⟨point12, point29, true⟩]
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
def step0 : Step := ⟨7, point0⟩
/-- Proposed owner constraints after 1 forced-point assignments. -/
def model1 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet0
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet10
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 1. -/
def step1 : Step := ⟨1, point1⟩
/-- Proposed owner constraints after 2 forced-point assignments. -/
def model2 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet0
    | 1 => pointSet11
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet10
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 2. -/
def step2 : Step := ⟨0, point2⟩
/-- Proposed owner constraints after 3 forced-point assignments. -/
def model3 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet12
    | 1 => pointSet11
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet10
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 3. -/
def step3 : Step := ⟨0, point3⟩
/-- Proposed owner constraints after 4 forced-point assignments. -/
def model4 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet13
    | 1 => pointSet11
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet6
    | 7 => pointSet10
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 4. -/
def step4 : Step := ⟨6, point4⟩
/-- Proposed owner constraints after 5 forced-point assignments. -/
def model5 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet13
    | 1 => pointSet11
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet14
    | 7 => pointSet10
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 5. -/
def step5 : Step := ⟨6, point5⟩
/-- Proposed owner constraints after 6 forced-point assignments. -/
def model6 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet13
    | 1 => pointSet11
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet5
    | 6 => pointSet15
    | 7 => pointSet10
    | 8 => pointSet8
    | _ => pointSet9), capsConstraints, ownerFlags⟩

/-- The shared step constants reproduce the original certificate trace exactly. -/
theorem trace_steps : [step0, step1, step2, step3, step4, step5] = Data.Across012500017500.steps
    := by
  rfl

end Across012500017500
end ConwaySoifer.Simplified.Certificates
