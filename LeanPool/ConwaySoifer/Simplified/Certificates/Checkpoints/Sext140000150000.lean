/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Data.Sext140000150000
public import LeanPool.ConwaySoifer.Certificates.KernelReplay

/-!
# Sext 140000 150000

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
namespace Sext140000150000

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point0 : IPoint := ([(-750000000000)], [330000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point1 : IPoint := ([(-420000000000)], [750000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point2 : IPoint := ([(-330000000000)], [750000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point3 : IPoint := ([330000000000], [420000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point4 : IPoint := ([1260000000000], [(-1260000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point5 : IPoint := ([8625000000000], [(-9705000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point6 : IPoint := ([9000000000000], [(-9765000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point7 : IPoint := ([6732000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point8 : IPoint := ([(-5607000000000)], [(-3393000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point9 : IPoint := ([4125000000000], [(-5220000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point10 : IPoint := ([4410000000000], [(-5250000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point11 : IPoint := ([4665000000000], [(-5040000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point12 : IPoint := ([(-14625000000000)], [5625000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point13 : IPoint := ([(-8250000000000)], [6732000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point14 : IPoint := ([(-6750000000000)], [6330000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point15 : IPoint := ([(-5625000000000)], [(-630000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point16 : IPoint := ([(-3585000000000)], [(-5040000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point17 : IPoint := ([(-3495000000000)], [(-5505000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point18 : IPoint := ([(-15750000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point19 : IPoint := ([(-12540000000000)], [3540000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point20 : IPoint := ([(-8025000000000)], [4875000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point21 : IPoint := ([(-5805000000000)], [5175000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point22 : IPoint := ([(-5580000000000)], [(-420000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point23 : IPoint := ([(-5040000000000)], [4290000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point24 : IPoint := ([(-1260000000000)], [(-7365000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point25 : IPoint := ([(-14850000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point26 : IPoint := ([(-8370000000000)], [4500000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point27 : IPoint := ([(-5430000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point28 : IPoint := ([(-525000000000)], [6375000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point29 : IPoint := ([(-375000000000)], [(-420000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point30 : IPoint := ([3915000000000], [(-5175000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point31 : IPoint := ([4740000000000], [(-6000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point32 : IPoint := ([6750000000000], [(-6480000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point33 : IPoint := ([(-14580000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point34 : IPoint := ([(-8625000000000)], [3960000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point35 : IPoint := ([(-4755000000000)], [4125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point36 : IPoint := ([(-3660000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point37 : IPoint := ([(-2775000000000)], [(-375000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point38 : IPoint := ([(-630000000000)], [5880000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point39 : IPoint := ([4995000000000], [(-8370000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point40 : IPoint := ([(-13830000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point41 : IPoint := ([(-12030000000000)], [3030000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point42 : IPoint := ([(-9000000000000)], [3000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point43 : IPoint := ([(-7320000000000)], [2820000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point44 : IPoint := ([(-6750000000000)], [2790000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point45 : IPoint := ([(-6660000000000)], [7560000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point46 : IPoint := ([(-5040000000000)], [2790000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point47 : IPoint := ([(-4650000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point48 : IPoint := ([(-3960000000000)], [2835000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point49 : IPoint := ([(-3780000000000)], [2880000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point50 : IPoint := ([(-3630000000000)], [3000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point51 : IPoint := ([(-3465000000000)], [(-5535000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point52 : IPoint := ([5625000000000], [1680000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point53 : IPoint := ([(-10650000000000)], [7500000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point54 : IPoint := ([(-10530000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point55 : IPoint := ([(-9000000000000)], [2985000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point56 : IPoint := ([(-6195000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point57 : IPoint := ([(-2250000000000)], [5040000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point58 : IPoint := ([(-2130000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point59 : IPoint := ([(-1125000000000)], [3960000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point60 : IPoint := ([(-630000000000)], [3630000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point61 : IPoint := ([4140000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point62 : IPoint := ([4857000000000], [1875000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point63 : IPoint := ([4875000000000], [3150000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point64 : IPoint := ([7005000000000], [(-6375000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point65 : IPoint := ([9000000000000], [7320000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point66 : IPoint := ([(-11775000000000)], [2775000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point67 : IPoint := ([(-9000000000000)], [2745000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point68 : IPoint := ([(-5250000000000)], [6510000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point69 : IPoint := ([(-5175000000000)], [1260000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point70 : IPoint := ([(-4500000000000)], [5760000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point71 : IPoint := ([(-930000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point72 : IPoint := ([(-420000000000)], [795000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point73 : IPoint := ([2790000000000], [2250000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point74 : IPoint := ([2790000000000], [5580000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point75 : IPoint := ([7500000000000], [(-3960000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point76 : IPoint := ([(-714000000000), (-5100000000000)], [357000000000, 2550000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point77 : IPoint := ([(-357000000000), (-2550000000000)], [(-357000000000), (-2550000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point78 : IPoint := ([357000000000, 2550000000000], [(-714000000000), (-5100000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point79 : IPoint := ([714000000000, 5100000000000], [(-357000000000), (-2550000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point80 : IPoint := ([357000000000, 2550000000000], [357000000000, 2550000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point81 : IPoint := ([(-357000000000), (-2550000000000)], [714000000000, 5100000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point82 : IPoint := ([7740000000000, (-9000000000000)], [1260000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point83 : IPoint := ([9000000000000], [(-1260000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point84 : IPoint := ([9000000000000], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point85 : IPoint := ([(-1260000000000), (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point86 : IPoint := ([1260000000000, 9000000000000], [7740000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point87 : IPoint := ([0], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point88 : IPoint := ([(-9000000000000)], [7740000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point89 : IPoint := ([(-7740000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point90 : IPoint := ([(-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point91 : IPoint := ([(-9000000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point92 : IPoint := ([(-7740000000000), 9000000000000], [(-1260000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point93 : IPoint := ([(-9000000000000)], [1260000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point94 : IPoint := ([(-1260000000000), (-9000000000000)], [(-7740000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point95 : IPoint := ([0], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point96 : IPoint := ([1260000000000, 9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point97 : IPoint := ([7740000000000, (-9000000000000)], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point98 : IPoint := ([9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point99 : IPoint := ([7740000000000, (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point100 : IPoint := ([9000000000000], [7740000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point101 : IPoint := ([9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point102 : IPoint := ([(-18000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point103 : IPoint := ([(-16740000000000), 9000000000000], [7740000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point104 : IPoint := ([(-16740000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point105 : IPoint := ([7740000000000, (-9000000000000)], [(-16740000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point106 : IPoint := ([9000000000000], [(-18000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point107 : IPoint := ([9000000000000], [(-16740000000000), 9000000000000])

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet0 : List IPoint := [point76, point77, point78, point79, point80, point81]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet1 : List IPoint := [point82, point83, point84]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet2 : List IPoint := [point85, point86, point87]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet3 : List IPoint := [point88, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet4 : List IPoint := [point91, point92, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet5 : List IPoint := [point94, point95, point96]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet6 : List IPoint := [point97, point98, point83]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet7 : List IPoint := [point99, point100, point101]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet8 : List IPoint := [point102, point103, point104]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet9 : List IPoint := [point105, point106, point107]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet10 : List IPoint := [point0, point77, point78, point79, point80, point81]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet11 : List IPoint := [point0, point77, point78, point79, point80, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet12 : List IPoint := [point0, point77, point78, point79, point80, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet13 : List IPoint := [point0, point77, point78, point79, point3, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet14 : List IPoint := [point0, point77, point4, point3, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet15 : List IPoint := [point105, point106, point107, point5]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet16 : List IPoint := [point105, point106, point6, point5]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet17 : List IPoint := [point94, point95, point7]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet18 : List IPoint := [point91, point8, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet19 : List IPoint := [point0, point77, point9, point3, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet20 : List IPoint := [point0, point77, point9, point10, point3, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet21 : List IPoint := [point0, point77, point9, point10, point11, point3, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet22 : List IPoint := [point102, point12, point104]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet23 : List IPoint := [point88, point13, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet24 : List IPoint := [point88, point13, point14, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet25 : List IPoint := [point91, point8, point15, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet26 : List IPoint := [point91, point8, point16, point15, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet27 : List IPoint := [point91, point17, point16, point15, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet28 : List IPoint := [point102, point12, point18]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet29 : List IPoint := [point102, point19, point18]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet30 : List IPoint := [point88, point20, point14, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet31 : List IPoint := [point88, point20, point21, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet32 : List IPoint := [point91, point17, point16, point22, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet33 : List IPoint := [point88, point20, point23, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet34 : List IPoint := [point94, point95, point7, point24]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet35 : List IPoint := [point102, point19, point25]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet36 : List IPoint := [point88, point26, point23, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet37 : List IPoint := [point91, point17, point16, point27, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet38 : List IPoint := [point85, point28, point86, point87]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet39 : List IPoint := [point0, point29, point9, point10, point11, point3, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet40 : List IPoint := [point0, point29, point30, point9, point10, point11, point3, point2,
    point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet41 : List IPoint := [point0, point29, point30, point31, point11, point3, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet42 : List IPoint := [point0, point29, point30, point31, point32, point3, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet43 : List IPoint := [point102, point19, point33]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet44 : List IPoint := [point88, point34, point23, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet45 : List IPoint := [point88, point34, point35, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet46 : List IPoint := [point36, point28, point86, point87]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet47 : List IPoint := [point91, point17, point37, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet48 : List IPoint := [point36, point38, point86, point87]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet49 : List IPoint := [point94, point95, point7, point39, point24]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet50 : List IPoint := [point102, point19, point40]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet51 : List IPoint := [point102, point41, point40]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet52 : List IPoint := [point42, point35, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet53 : List IPoint := [point42, point43, point35, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet54 : List IPoint := [point42, point43, point44, point35, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet55 : List IPoint := [point42, point43, point44, point35, point45, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet56 : List IPoint := [point42, point43, point44, point46, point35, point45, point89,
    point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet57 : List IPoint := [point47, point38, point86, point87]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet58 : List IPoint := [point42, point43, point44, point46, point48, point45, point89,
    point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet59 : List IPoint := [point42, point43, point44, point46, point48, point49, point45,
    point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet60 : List IPoint := [point42, point43, point44, point46, point48, point49, point50,
    point45, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet61 : List IPoint := [point91, point51, point37, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet62 : List IPoint := [point52, point83, point84, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet63 : List IPoint := [point102, point41, point53, point40]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet64 : List IPoint := [point102, point41, point53, point54]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet65 : List IPoint := [point55, point43, point44, point46, point48, point49, point50,
    point45, point89, point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet66 : List IPoint := [point56, point38, point86, point87]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet67 : List IPoint := [point56, point57, point38, point86, point87]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet68 : List IPoint := [point91, point51, point58, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet69 : List IPoint := [point56, point57, point59, point86, point87]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet70 : List IPoint := [point56, point57, point59, point60, point86, point87]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet71 : List IPoint := [point61, point100, point101]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet72 : List IPoint := [point62, point83, point84, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet73 : List IPoint := [point62, point83, point84, point82, point63]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet74 : List IPoint := [point0, point29, point30, point31, point32, point64, point3,
    point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet75 : List IPoint := [point61, point65, point101]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet76 : List IPoint := [point102, point66, point53, point54]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet77 : List IPoint := [point67, point46, point48, point49, point50, point45, point89,
    point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet78 : List IPoint := [point67, point46, point48, point49, point50, point68, point89,
    point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet79 : List IPoint := [point91, point51, point58, point69, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet80 : List IPoint := [point67, point46, point48, point49, point50, point70, point89,
    point90]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet81 : List IPoint := [point71, point30, point31, point32, point64, point3, point2,
    point1, point0]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet82 : List IPoint := [point71, point30, point31, point32, point64, point3, point72,
    point0]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet83 : List IPoint := [point73, point83, point84, point82, point63]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet84 : List IPoint := [point73, point83, point84, point82, point74]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet85 : List IPoint := [point73, point75, point83, point84, point82, point74]

/-- Contact constraints shared by every state in this certificate trace. -/
def capsConstraints : Fin 10 → List Cap :=
  fun j =>
    match j.val with
    | 0 => []
    | 1 => [⟨point83, point95, false⟩]
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
def step5 : Step := ⟨9, point5⟩
/-- Proposed owner constraints after 6 forced-point assignments. -/
def model6 : Model :=
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
    | _ => pointSet15), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 6. -/
def step6 : Step := ⟨9, point6⟩
/-- Proposed owner constraints after 7 forced-point assignments. -/
def model7 : Model :=
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
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 7. -/
def step7 : Step := ⟨5, point7⟩
/-- Proposed owner constraints after 8 forced-point assignments. -/
def model8 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet14
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 8. -/
def step8 : Step := ⟨4, point8⟩
/-- Proposed owner constraints after 9 forced-point assignments. -/
def model9 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet14
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet18
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 9. -/
def step9 : Step := ⟨0, point9⟩
/-- Proposed owner constraints after 10 forced-point assignments. -/
def model10 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet18
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 10. -/
def step10 : Step := ⟨0, point10⟩
/-- Proposed owner constraints after 11 forced-point assignments. -/
def model11 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet20
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet18
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 11. -/
def step11 : Step := ⟨0, point11⟩
/-- Proposed owner constraints after 12 forced-point assignments. -/
def model12 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet18
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 12. -/
def step12 : Step := ⟨8, point12⟩
/-- Proposed owner constraints after 13 forced-point assignments. -/
def model13 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet18
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet22
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 13. -/
def step13 : Step := ⟨3, point13⟩
/-- Proposed owner constraints after 14 forced-point assignments. -/
def model14 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet23
    | 4 => pointSet18
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet22
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 14. -/
def step14 : Step := ⟨3, point14⟩
/-- Proposed owner constraints after 15 forced-point assignments. -/
def model15 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet24
    | 4 => pointSet18
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet22
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 15. -/
def step15 : Step := ⟨4, point15⟩
/-- Proposed owner constraints after 16 forced-point assignments. -/
def model16 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet24
    | 4 => pointSet25
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet22
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 16. -/
def step16 : Step := ⟨4, point16⟩
/-- Proposed owner constraints after 17 forced-point assignments. -/
def model17 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet24
    | 4 => pointSet26
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet22
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 17. -/
def step17 : Step := ⟨4, point17⟩
/-- Proposed owner constraints after 18 forced-point assignments. -/
def model18 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet24
    | 4 => pointSet27
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet22
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 18. -/
def step18 : Step := ⟨8, point18⟩
/-- Proposed owner constraints after 19 forced-point assignments. -/
def model19 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet24
    | 4 => pointSet27
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet28
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 19. -/
def step19 : Step := ⟨8, point19⟩
/-- Proposed owner constraints after 20 forced-point assignments. -/
def model20 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet24
    | 4 => pointSet27
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet29
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 20. -/
def step20 : Step := ⟨3, point20⟩
/-- Proposed owner constraints after 21 forced-point assignments. -/
def model21 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet30
    | 4 => pointSet27
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet29
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 21. -/
def step21 : Step := ⟨3, point21⟩
/-- Proposed owner constraints after 22 forced-point assignments. -/
def model22 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet31
    | 4 => pointSet27
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet29
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 22. -/
def step22 : Step := ⟨4, point22⟩
/-- Proposed owner constraints after 23 forced-point assignments. -/
def model23 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet31
    | 4 => pointSet32
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet29
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 23. -/
def step23 : Step := ⟨3, point23⟩
/-- Proposed owner constraints after 24 forced-point assignments. -/
def model24 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet33
    | 4 => pointSet32
    | 5 => pointSet17
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet29
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 24. -/
def step24 : Step := ⟨5, point24⟩
/-- Proposed owner constraints after 25 forced-point assignments. -/
def model25 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet33
    | 4 => pointSet32
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet29
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 25. -/
def step25 : Step := ⟨8, point25⟩
/-- Proposed owner constraints after 26 forced-point assignments. -/
def model26 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet33
    | 4 => pointSet32
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet35
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 26. -/
def step26 : Step := ⟨3, point26⟩
/-- Proposed owner constraints after 27 forced-point assignments. -/
def model27 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet36
    | 4 => pointSet32
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet35
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 27. -/
def step27 : Step := ⟨4, point27⟩
/-- Proposed owner constraints after 28 forced-point assignments. -/
def model28 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet36
    | 4 => pointSet37
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet35
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 28. -/
def step28 : Step := ⟨2, point28⟩
/-- Proposed owner constraints after 29 forced-point assignments. -/
def model29 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet21
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet36
    | 4 => pointSet37
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet35
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 29. -/
def step29 : Step := ⟨0, point29⟩
/-- Proposed owner constraints after 30 forced-point assignments. -/
def model30 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet39
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet36
    | 4 => pointSet37
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet35
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 30. -/
def step30 : Step := ⟨0, point30⟩
/-- Proposed owner constraints after 31 forced-point assignments. -/
def model31 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet36
    | 4 => pointSet37
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet35
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 31. -/
def step31 : Step := ⟨0, point31⟩
/-- Proposed owner constraints after 32 forced-point assignments. -/
def model32 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet41
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet36
    | 4 => pointSet37
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet35
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 32. -/
def step32 : Step := ⟨0, point32⟩
/-- Proposed owner constraints after 33 forced-point assignments. -/
def model33 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet36
    | 4 => pointSet37
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet35
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 33. -/
def step33 : Step := ⟨8, point33⟩
/-- Proposed owner constraints after 34 forced-point assignments. -/
def model34 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet36
    | 4 => pointSet37
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet43
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 34. -/
def step34 : Step := ⟨3, point34⟩
/-- Proposed owner constraints after 35 forced-point assignments. -/
def model35 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet44
    | 4 => pointSet37
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet43
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 35. -/
def step35 : Step := ⟨3, point35⟩
/-- Proposed owner constraints after 36 forced-point assignments. -/
def model36 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet45
    | 4 => pointSet37
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet43
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 36. -/
def step36 : Step := ⟨2, point36⟩
/-- Proposed owner constraints after 37 forced-point assignments. -/
def model37 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet46
    | 3 => pointSet45
    | 4 => pointSet37
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet43
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 37. -/
def step37 : Step := ⟨4, point37⟩
/-- Proposed owner constraints after 38 forced-point assignments. -/
def model38 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet46
    | 3 => pointSet45
    | 4 => pointSet47
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet43
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 38. -/
def step38 : Step := ⟨2, point38⟩
/-- Proposed owner constraints after 39 forced-point assignments. -/
def model39 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet48
    | 3 => pointSet45
    | 4 => pointSet47
    | 5 => pointSet34
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet43
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 39. -/
def step39 : Step := ⟨5, point39⟩
/-- Proposed owner constraints after 40 forced-point assignments. -/
def model40 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet48
    | 3 => pointSet45
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet43
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 40. -/
def step40 : Step := ⟨8, point40⟩
/-- Proposed owner constraints after 41 forced-point assignments. -/
def model41 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet48
    | 3 => pointSet45
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet50
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 41. -/
def step41 : Step := ⟨8, point41⟩
/-- Proposed owner constraints after 42 forced-point assignments. -/
def model42 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet48
    | 3 => pointSet45
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 42. -/
def step42 : Step := ⟨3, point42⟩
/-- Proposed owner constraints after 43 forced-point assignments. -/
def model43 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet48
    | 3 => pointSet52
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 43. -/
def step43 : Step := ⟨3, point43⟩
/-- Proposed owner constraints after 44 forced-point assignments. -/
def model44 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet48
    | 3 => pointSet53
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 44. -/
def step44 : Step := ⟨3, point44⟩
/-- Proposed owner constraints after 45 forced-point assignments. -/
def model45 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet48
    | 3 => pointSet54
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 45. -/
def step45 : Step := ⟨3, point45⟩
/-- Proposed owner constraints after 46 forced-point assignments. -/
def model46 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet48
    | 3 => pointSet55
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 46. -/
def step46 : Step := ⟨3, point46⟩
/-- Proposed owner constraints after 47 forced-point assignments. -/
def model47 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet48
    | 3 => pointSet56
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 47. -/
def step47 : Step := ⟨2, point47⟩
/-- Proposed owner constraints after 48 forced-point assignments. -/
def model48 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet57
    | 3 => pointSet56
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 48. -/
def step48 : Step := ⟨3, point48⟩
/-- Proposed owner constraints after 49 forced-point assignments. -/
def model49 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet57
    | 3 => pointSet58
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 49. -/
def step49 : Step := ⟨3, point49⟩
/-- Proposed owner constraints after 50 forced-point assignments. -/
def model50 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet57
    | 3 => pointSet59
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 50. -/
def step50 : Step := ⟨3, point50⟩
/-- Proposed owner constraints after 51 forced-point assignments. -/
def model51 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet57
    | 3 => pointSet60
    | 4 => pointSet47
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 51. -/
def step51 : Step := ⟨4, point51⟩
/-- Proposed owner constraints after 52 forced-point assignments. -/
def model52 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet1
    | 2 => pointSet57
    | 3 => pointSet60
    | 4 => pointSet61
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 52. -/
def step52 : Step := ⟨1, point52⟩
/-- Proposed owner constraints after 53 forced-point assignments. -/
def model53 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet62
    | 2 => pointSet57
    | 3 => pointSet60
    | 4 => pointSet61
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 53. -/
def step53 : Step := ⟨8, point53⟩
/-- Proposed owner constraints after 54 forced-point assignments. -/
def model54 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet62
    | 2 => pointSet57
    | 3 => pointSet60
    | 4 => pointSet61
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet63
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 54. -/
def step54 : Step := ⟨8, point54⟩
/-- Proposed owner constraints after 55 forced-point assignments. -/
def model55 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet62
    | 2 => pointSet57
    | 3 => pointSet60
    | 4 => pointSet61
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 55. -/
def step55 : Step := ⟨3, point55⟩
/-- Proposed owner constraints after 56 forced-point assignments. -/
def model56 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet62
    | 2 => pointSet57
    | 3 => pointSet65
    | 4 => pointSet61
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 56. -/
def step56 : Step := ⟨2, point56⟩
/-- Proposed owner constraints after 57 forced-point assignments. -/
def model57 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet62
    | 2 => pointSet66
    | 3 => pointSet65
    | 4 => pointSet61
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 57. -/
def step57 : Step := ⟨2, point57⟩
/-- Proposed owner constraints after 58 forced-point assignments. -/
def model58 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet62
    | 2 => pointSet67
    | 3 => pointSet65
    | 4 => pointSet61
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 58. -/
def step58 : Step := ⟨4, point58⟩
/-- Proposed owner constraints after 59 forced-point assignments. -/
def model59 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet62
    | 2 => pointSet67
    | 3 => pointSet65
    | 4 => pointSet68
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 59. -/
def step59 : Step := ⟨2, point59⟩
/-- Proposed owner constraints after 60 forced-point assignments. -/
def model60 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet62
    | 2 => pointSet69
    | 3 => pointSet65
    | 4 => pointSet68
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 60. -/
def step60 : Step := ⟨2, point60⟩
/-- Proposed owner constraints after 61 forced-point assignments. -/
def model61 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet62
    | 2 => pointSet70
    | 3 => pointSet65
    | 4 => pointSet68
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 61. -/
def step61 : Step := ⟨7, point61⟩
/-- Proposed owner constraints after 62 forced-point assignments. -/
def model62 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet62
    | 2 => pointSet70
    | 3 => pointSet65
    | 4 => pointSet68
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet71
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 62. -/
def step62 : Step := ⟨1, point62⟩
/-- Proposed owner constraints after 63 forced-point assignments. -/
def model63 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet72
    | 2 => pointSet70
    | 3 => pointSet65
    | 4 => pointSet68
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet71
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 63. -/
def step63 : Step := ⟨1, point63⟩
/-- Proposed owner constraints after 64 forced-point assignments. -/
def model64 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet42
    | 1 => pointSet73
    | 2 => pointSet70
    | 3 => pointSet65
    | 4 => pointSet68
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet71
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 64. -/
def step64 : Step := ⟨0, point64⟩
/-- Proposed owner constraints after 65 forced-point assignments. -/
def model65 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet74
    | 1 => pointSet73
    | 2 => pointSet70
    | 3 => pointSet65
    | 4 => pointSet68
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet71
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 65. -/
def step65 : Step := ⟨7, point65⟩
/-- Proposed owner constraints after 66 forced-point assignments. -/
def model66 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet74
    | 1 => pointSet73
    | 2 => pointSet70
    | 3 => pointSet65
    | 4 => pointSet68
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet75
    | 8 => pointSet64
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 66. -/
def step66 : Step := ⟨8, point66⟩
/-- Proposed owner constraints after 67 forced-point assignments. -/
def model67 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet74
    | 1 => pointSet73
    | 2 => pointSet70
    | 3 => pointSet65
    | 4 => pointSet68
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet75
    | 8 => pointSet76
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 67. -/
def step67 : Step := ⟨3, point67⟩
/-- Proposed owner constraints after 68 forced-point assignments. -/
def model68 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet74
    | 1 => pointSet73
    | 2 => pointSet70
    | 3 => pointSet77
    | 4 => pointSet68
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet75
    | 8 => pointSet76
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 68. -/
def step68 : Step := ⟨3, point68⟩
/-- Proposed owner constraints after 69 forced-point assignments. -/
def model69 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet74
    | 1 => pointSet73
    | 2 => pointSet70
    | 3 => pointSet78
    | 4 => pointSet68
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet75
    | 8 => pointSet76
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 69. -/
def step69 : Step := ⟨4, point69⟩
/-- Proposed owner constraints after 70 forced-point assignments. -/
def model70 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet74
    | 1 => pointSet73
    | 2 => pointSet70
    | 3 => pointSet78
    | 4 => pointSet79
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet75
    | 8 => pointSet76
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 70. -/
def step70 : Step := ⟨3, point70⟩
/-- Proposed owner constraints after 71 forced-point assignments. -/
def model71 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet74
    | 1 => pointSet73
    | 2 => pointSet70
    | 3 => pointSet80
    | 4 => pointSet79
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet75
    | 8 => pointSet76
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 71. -/
def step71 : Step := ⟨0, point71⟩
/-- Proposed owner constraints after 72 forced-point assignments. -/
def model72 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet81
    | 1 => pointSet73
    | 2 => pointSet70
    | 3 => pointSet80
    | 4 => pointSet79
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet75
    | 8 => pointSet76
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 72. -/
def step72 : Step := ⟨0, point72⟩
/-- Proposed owner constraints after 73 forced-point assignments. -/
def model73 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet82
    | 1 => pointSet73
    | 2 => pointSet70
    | 3 => pointSet80
    | 4 => pointSet79
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet75
    | 8 => pointSet76
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 73. -/
def step73 : Step := ⟨1, point73⟩
/-- Proposed owner constraints after 74 forced-point assignments. -/
def model74 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet82
    | 1 => pointSet83
    | 2 => pointSet70
    | 3 => pointSet80
    | 4 => pointSet79
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet75
    | 8 => pointSet76
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 74. -/
def step74 : Step := ⟨1, point74⟩
/-- Proposed owner constraints after 75 forced-point assignments. -/
def model75 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet82
    | 1 => pointSet84
    | 2 => pointSet70
    | 3 => pointSet80
    | 4 => pointSet79
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet75
    | 8 => pointSet76
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 75. -/
def step75 : Step := ⟨1, point75⟩
/-- Proposed owner constraints after 76 forced-point assignments. -/
def model76 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet82
    | 1 => pointSet85
    | 2 => pointSet70
    | 3 => pointSet80
    | 4 => pointSet79
    | 5 => pointSet49
    | 6 => pointSet6
    | 7 => pointSet75
    | 8 => pointSet76
    | _ => pointSet16), capsConstraints, ownerFlags⟩

/-- The shared step constants reproduce the original certificate trace exactly. -/
theorem trace_steps : [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10,
    step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22,
    step23, step24, step25, step26, step27, step28, step29, step30, step31, step32, step33, step34,
    step35, step36, step37, step38, step39, step40, step41, step42, step43, step44, step45, step46,
    step47, step48, step49, step50, step51, step52, step53, step54, step55, step56, step57, step58,
    step59, step60, step61, step62, step63, step64, step65, step66, step67, step68, step69, step70,
    step71, step72, step73, step74, step75] = Data.Sext140000150000.steps := by
  rfl

end Sext140000150000
end ConwaySoifer.Simplified.Certificates
