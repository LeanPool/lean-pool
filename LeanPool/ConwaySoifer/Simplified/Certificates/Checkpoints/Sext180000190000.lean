/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Data.Sext180000190000
public import LeanPool.ConwaySoifer.Certificates.KernelReplay

/-!
# Sext 180000 190000

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
namespace Sext180000190000

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point0 : IPoint := ([(-915000000000)], [375000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point1 : IPoint := ([(-915000000000)], [540000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point2 : IPoint := ([(-735000000000)], [735000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point3 : IPoint := ([(-540000000000)], [(-375000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point4 : IPoint := ([(-540000000000)], [915000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point5 : IPoint := ([(-375000000000)], [915000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point6 : IPoint := ([0], [735000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point7 : IPoint := ([375000000000], [540000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point8 : IPoint := ([6480000000000], [(-6105000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point9 : IPoint := ([6570000000000], [(-6000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point10 : IPoint := ([8580000000000], [(-10080000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point11 : IPoint := ([9000000000000], [(-9990000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point12 : IPoint := ([4875000000000], [(-8115000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point13 : IPoint := ([6210000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point14 : IPoint := ([(-3825000000000)], [(-5175000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point15 : IPoint := ([(-3750000000000)], [(-540000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point16 : IPoint := ([(-3735000000000)], [(-1125000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point17 : IPoint := ([(-12735000000000)], [3735000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point18 : IPoint := ([(-8175000000000)], [4050000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point19 : IPoint := ([(-7875000000000)], [3735000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point20 : IPoint := ([(-4860000000000)], [3735000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point21 : IPoint := ([(-4290000000000)], [3750000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point22 : IPoint := ([(-1620000000000)], [(-6630000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point23 : IPoint := ([(-13335000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point24 : IPoint := ([(-8190000000000)], [3750000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point25 : IPoint := ([(-4140000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point26 : IPoint := ([(-3675000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point27 : IPoint := ([(-810000000000)], [5625000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point28 : IPoint := ([(-540000000000)], [5415000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point29 : IPoint := ([3255000000000], [(-4875000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point30 : IPoint := ([4125000000000], [(-5745000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point31 : IPoint := ([(-12720000000000)], [3720000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point32 : IPoint := ([(-11220000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point33 : IPoint := ([(-9000000000000)], [3705000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point34 : IPoint := ([(-6750000000000)], [8190000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point35 : IPoint := ([(-5250000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point36 : IPoint := ([(-4050000000000)], [3675000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point37 : IPoint := ([(-2430000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point38 : IPoint := ([(-540000000000)], [5250000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point39 : IPoint := ([5010000000000], [750000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point40 : IPoint := ([5184000000000], [576000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point41 : IPoint := ([(-12105000000000)], [3105000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point42 : IPoint := ([(-11115000000000)], [7875000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point43 : IPoint := ([(-9000000000000)], [3045000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point44 : IPoint := ([(-6630000000000)], [8250000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point45 : IPoint := ([(-6000000000000)], [2430000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point46 : IPoint := ([(-5745000000000)], [1620000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point47 : IPoint := ([(-5310000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point48 : IPoint := ([(-5130000000000)], [6750000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point49 : IPoint := ([(-2250000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point50 : IPoint := ([(-810000000000)], [(-375000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point51 : IPoint := ([(-375000000000)], [4050000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point52 : IPoint := ([3750000000000], [8166000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point53 : IPoint := ([4365000000000], [810000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point54 : IPoint := ([9000000000000], [6210000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point55 : IPoint := ([(-11865000000000)], [2865000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point56 : IPoint := ([(-9810000000000)], [7125000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point57 : IPoint := ([(-9000000000000)], [3000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point58 : IPoint := ([(-6570000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point59 : IPoint := ([(-5760000000000)], [2250000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point60 : IPoint := ([(-4380000000000)], [6000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point61 : IPoint := ([(-3375000000000)], [1620000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point62 : IPoint := ([(-1290000000000)], [750000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point63 : IPoint := ([(-1125000000000)], [3555000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point64 : IPoint := ([(-1110000000000)], [1110000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point65 : IPoint := ([2610000000000], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point66 : IPoint := ([3750000000000], [4860000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point67 : IPoint := ([5175000000000], [(-2745000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point68 : IPoint := ([(-874800000000), (-4860000000000)], [437400000000, 2430000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point69 : IPoint := ([(-437400000000), (-2430000000000)], [(-437400000000), (-2430000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point70 : IPoint := ([437400000000, 2430000000000], [(-874800000000), (-4860000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point71 : IPoint := ([874800000000, 4860000000000], [(-437400000000), (-2430000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point72 : IPoint := ([437400000000, 2430000000000], [437400000000, 2430000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point73 : IPoint := ([(-437400000000), (-2430000000000)], [874800000000, 4860000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point74 : IPoint := ([7380000000000, (-9000000000000)], [1620000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point75 : IPoint := ([9000000000000], [(-1620000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point76 : IPoint := ([9000000000000], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point77 : IPoint := ([(-1620000000000), (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point78 : IPoint := ([1620000000000, 9000000000000], [7380000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point79 : IPoint := ([0], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point80 : IPoint := ([(-9000000000000)], [7380000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point81 : IPoint := ([(-7380000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point82 : IPoint := ([(-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point83 : IPoint := ([(-9000000000000)], [0])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point84 : IPoint := ([(-7380000000000), 9000000000000], [(-1620000000000), (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point85 : IPoint := ([(-9000000000000)], [1620000000000, 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point86 : IPoint := ([(-1620000000000), (-9000000000000)], [(-7380000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point87 : IPoint := ([0], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point88 : IPoint := ([1620000000000, 9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point89 : IPoint := ([7380000000000, (-9000000000000)], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point90 : IPoint := ([9000000000000], [(-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point91 : IPoint := ([7380000000000, (-9000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point92 : IPoint := ([9000000000000], [7380000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point93 : IPoint := ([9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point94 : IPoint := ([(-18000000000000)], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point95 : IPoint := ([(-16380000000000), 9000000000000], [7380000000000, (-9000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point96 : IPoint := ([(-16380000000000), 9000000000000], [9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point97 : IPoint := ([7380000000000, (-9000000000000)], [(-16380000000000), 9000000000000])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point98 : IPoint := ([9000000000000], [(-18000000000000)])

/-- Shared exact polynomial coordinates, scaled by the certificate denominator. -/
def point99 : IPoint := ([9000000000000], [(-16380000000000), 9000000000000])

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet0 : List IPoint := [point68, point69, point70, point71, point72, point73]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet1 : List IPoint := [point74, point75, point76]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet2 : List IPoint := [point77, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet3 : List IPoint := [point80, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet4 : List IPoint := [point83, point84, point85]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet5 : List IPoint := [point86, point87, point88]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet6 : List IPoint := [point89, point90, point75]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet7 : List IPoint := [point91, point92, point93]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet8 : List IPoint := [point94, point95, point96]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet9 : List IPoint := [point97, point98, point99]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet10 : List IPoint := [point0, point69, point70, point71, point72, point73, point68]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet11 : List IPoint := [point0, point69, point70, point71, point72, point73, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet12 : List IPoint := [point0, point69, point70, point71, point72, point73, point2,
    point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet13 : List IPoint := [point0, point3, point69, point70, point71, point72, point73,
    point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet14 : List IPoint := [point0, point3, point69, point70, point71, point72, point73,
    point4, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet15 : List IPoint := [point0, point3, point69, point70, point71, point72, point5, point4,
    point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet16 : List IPoint := [point0, point3, point69, point70, point71, point72, point6, point5,
    point4, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet17 : List IPoint := [point0, point3, point69, point70, point71, point72, point7, point6,
    point5, point4, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet18 : List IPoint := [point0, point3, point8, point7, point6, point5, point4, point2,
    point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet19 : List IPoint := [point0, point3, point8, point9, point7, point6, point5, point4,
    point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet20 : List IPoint := [point97, point98, point99, point10]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet21 : List IPoint := [point97, point98, point11, point10]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet22 : List IPoint := [point86, point87, point88, point12]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet23 : List IPoint := [point86, point87, point13, point12]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet24 : List IPoint := [point83, point14, point85]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet25 : List IPoint := [point83, point14, point15, point85]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet26 : List IPoint := [point83, point14, point16, point15, point85]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet27 : List IPoint := [point94, point17, point96]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet28 : List IPoint := [point80, point18, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet29 : List IPoint := [point80, point18, point19, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet30 : List IPoint := [point80, point18, point19, point20, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet31 : List IPoint := [point80, point18, point19, point20, point21, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet32 : List IPoint := [point86, point87, point13, point12, point22]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet33 : List IPoint := [point94, point17, point23]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet34 : List IPoint := [point80, point24, point19, point20, point21, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet35 : List IPoint := [point25, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet36 : List IPoint := [point83, point14, point26, point85]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet37 : List IPoint := [point25, point27, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet38 : List IPoint := [point25, point27, point28, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet39 : List IPoint := [point0, point3, point29, point8, point9, point7, point6, point5,
    point4, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet40 : List IPoint := [point0, point3, point29, point30, point8, point9, point7, point6,
    point5, point4, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet41 : List IPoint := [point94, point31, point23]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet42 : List IPoint := [point94, point31, point32]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet43 : List IPoint := [point33, point20, point21, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet44 : List IPoint := [point33, point20, point21, point34, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet45 : List IPoint := [point35, point28, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet46 : List IPoint := [point33, point36, point34, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet47 : List IPoint := [point83, point14, point37, point85]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet48 : List IPoint := [point35, point38, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet49 : List IPoint := [point39, point75, point76, point74]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet50 : List IPoint := [point39, point40, point75, point76, point74]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet51 : List IPoint := [point94, point41, point32]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet52 : List IPoint := [point94, point41, point42, point32]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet53 : List IPoint := [point43, point36, point34, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet54 : List IPoint := [point43, point36, point44, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet55 : List IPoint := [point43, point45, point36, point44, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet56 : List IPoint := [point83, point14, point37, point46, point85]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet57 : List IPoint := [point47, point38, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet58 : List IPoint := [point43, point45, point36, point48, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet59 : List IPoint := [point83, point14, point49, point46, point85]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet60 : List IPoint := [point0, point50, point29, point30, point8, point9, point7, point6,
    point5, point4, point2, point1]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet61 : List IPoint := [point47, point51, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet62 : List IPoint := [point52, point92, point93, point91]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet63 : List IPoint := [point53, point75, point76, point74]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet64 : List IPoint := [point52, point54, point93, point91]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet65 : List IPoint := [point94, point55, point42, point32]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet66 : List IPoint := [point94, point55, point56, point32]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet67 : List IPoint := [point57, point45, point36, point48, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet68 : List IPoint := [point58, point51, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet69 : List IPoint := [point57, point59, point36, point48, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet70 : List IPoint := [point57, point59, point36, point60, point81, point82]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet71 : List IPoint := [point83, point14, point49, point61, point85]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet72 : List IPoint := [point62, point50, point29, point30, point8, point9, point7, point6,
    point5, point4]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet73 : List IPoint := [point58, point63, point51, point78, point79]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet74 : List IPoint := [point62, point50, point29, point30, point8, point9, point7, point6,
    point5, point64]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet75 : List IPoint := [point65, point75, point76, point74, point53]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet76 : List IPoint := [point65, point75, point76, point74, point66]

/-- Shared mandatory-point list for one proposed owner state. -/
def pointSet77 : List IPoint := [point65, point67, point75, point76, point74, point66]

/-- Contact constraints shared by every state in this certificate trace. -/
def capsConstraints : Fin 10 → List Cap :=
  fun j =>
    match j.val with
    | 0 => []
    | 1 => [⟨point75, point87, false⟩]
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
def step12 : Step := ⟨5, point12⟩
/-- Proposed owner constraints after 13 forced-point assignments. -/
def model13 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet22
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
    | 3 => pointSet3
    | 4 => pointSet4
    | 5 => pointSet23
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 14. -/
def step14 : Step := ⟨4, point14⟩
/-- Proposed owner constraints after 15 forced-point assignments. -/
def model15 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet24
    | 5 => pointSet23
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 15. -/
def step15 : Step := ⟨4, point15⟩
/-- Proposed owner constraints after 16 forced-point assignments. -/
def model16 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet25
    | 5 => pointSet23
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 16. -/
def step16 : Step := ⟨4, point16⟩
/-- Proposed owner constraints after 17 forced-point assignments. -/
def model17 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet26
    | 5 => pointSet23
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet8
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 17. -/
def step17 : Step := ⟨8, point17⟩
/-- Proposed owner constraints after 18 forced-point assignments. -/
def model18 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet3
    | 4 => pointSet26
    | 5 => pointSet23
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet27
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 18. -/
def step18 : Step := ⟨3, point18⟩
/-- Proposed owner constraints after 19 forced-point assignments. -/
def model19 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet28
    | 4 => pointSet26
    | 5 => pointSet23
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet27
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 19. -/
def step19 : Step := ⟨3, point19⟩
/-- Proposed owner constraints after 20 forced-point assignments. -/
def model20 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet29
    | 4 => pointSet26
    | 5 => pointSet23
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet27
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 20. -/
def step20 : Step := ⟨3, point20⟩
/-- Proposed owner constraints after 21 forced-point assignments. -/
def model21 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet30
    | 4 => pointSet26
    | 5 => pointSet23
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet27
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 21. -/
def step21 : Step := ⟨3, point21⟩
/-- Proposed owner constraints after 22 forced-point assignments. -/
def model22 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet31
    | 4 => pointSet26
    | 5 => pointSet23
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet27
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 22. -/
def step22 : Step := ⟨5, point22⟩
/-- Proposed owner constraints after 23 forced-point assignments. -/
def model23 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet31
    | 4 => pointSet26
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet27
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 23. -/
def step23 : Step := ⟨8, point23⟩
/-- Proposed owner constraints after 24 forced-point assignments. -/
def model24 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet2
    | 3 => pointSet31
    | 4 => pointSet26
    | 5 => pointSet32
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
    | 2 => pointSet2
    | 3 => pointSet34
    | 4 => pointSet26
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 25. -/
def step25 : Step := ⟨2, point25⟩
/-- Proposed owner constraints after 26 forced-point assignments. -/
def model26 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet35
    | 3 => pointSet34
    | 4 => pointSet26
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 26. -/
def step26 : Step := ⟨4, point26⟩
/-- Proposed owner constraints after 27 forced-point assignments. -/
def model27 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet35
    | 3 => pointSet34
    | 4 => pointSet36
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 27. -/
def step27 : Step := ⟨2, point27⟩
/-- Proposed owner constraints after 28 forced-point assignments. -/
def model28 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet37
    | 3 => pointSet34
    | 4 => pointSet36
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 28. -/
def step28 : Step := ⟨2, point28⟩
/-- Proposed owner constraints after 29 forced-point assignments. -/
def model29 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet19
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet34
    | 4 => pointSet36
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 29. -/
def step29 : Step := ⟨0, point29⟩
/-- Proposed owner constraints after 30 forced-point assignments. -/
def model30 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet39
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet34
    | 4 => pointSet36
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 30. -/
def step30 : Step := ⟨0, point30⟩
/-- Proposed owner constraints after 31 forced-point assignments. -/
def model31 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet34
    | 4 => pointSet36
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet33
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 31. -/
def step31 : Step := ⟨8, point31⟩
/-- Proposed owner constraints after 32 forced-point assignments. -/
def model32 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet34
    | 4 => pointSet36
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet41
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 32. -/
def step32 : Step := ⟨8, point32⟩
/-- Proposed owner constraints after 33 forced-point assignments. -/
def model33 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet34
    | 4 => pointSet36
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet42
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 33. -/
def step33 : Step := ⟨3, point33⟩
/-- Proposed owner constraints after 34 forced-point assignments. -/
def model34 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet43
    | 4 => pointSet36
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet42
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 34. -/
def step34 : Step := ⟨3, point34⟩
/-- Proposed owner constraints after 35 forced-point assignments. -/
def model35 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet1
    | 2 => pointSet38
    | 3 => pointSet44
    | 4 => pointSet36
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet42
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 35. -/
def step35 : Step := ⟨2, point35⟩
/-- Proposed owner constraints after 36 forced-point assignments. -/
def model36 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet1
    | 2 => pointSet45
    | 3 => pointSet44
    | 4 => pointSet36
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet42
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 36. -/
def step36 : Step := ⟨3, point36⟩
/-- Proposed owner constraints after 37 forced-point assignments. -/
def model37 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet1
    | 2 => pointSet45
    | 3 => pointSet46
    | 4 => pointSet36
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet42
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 37. -/
def step37 : Step := ⟨4, point37⟩
/-- Proposed owner constraints after 38 forced-point assignments. -/
def model38 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet1
    | 2 => pointSet45
    | 3 => pointSet46
    | 4 => pointSet47
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet42
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 38. -/
def step38 : Step := ⟨2, point38⟩
/-- Proposed owner constraints after 39 forced-point assignments. -/
def model39 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet1
    | 2 => pointSet48
    | 3 => pointSet46
    | 4 => pointSet47
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet42
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 39. -/
def step39 : Step := ⟨1, point39⟩
/-- Proposed owner constraints after 40 forced-point assignments. -/
def model40 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet49
    | 2 => pointSet48
    | 3 => pointSet46
    | 4 => pointSet47
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet42
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 40. -/
def step40 : Step := ⟨1, point40⟩
/-- Proposed owner constraints after 41 forced-point assignments. -/
def model41 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet50
    | 2 => pointSet48
    | 3 => pointSet46
    | 4 => pointSet47
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet42
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 41. -/
def step41 : Step := ⟨8, point41⟩
/-- Proposed owner constraints after 42 forced-point assignments. -/
def model42 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet50
    | 2 => pointSet48
    | 3 => pointSet46
    | 4 => pointSet47
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet51
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 42. -/
def step42 : Step := ⟨8, point42⟩
/-- Proposed owner constraints after 43 forced-point assignments. -/
def model43 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet50
    | 2 => pointSet48
    | 3 => pointSet46
    | 4 => pointSet47
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 43. -/
def step43 : Step := ⟨3, point43⟩
/-- Proposed owner constraints after 44 forced-point assignments. -/
def model44 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet50
    | 2 => pointSet48
    | 3 => pointSet53
    | 4 => pointSet47
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 44. -/
def step44 : Step := ⟨3, point44⟩
/-- Proposed owner constraints after 45 forced-point assignments. -/
def model45 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet50
    | 2 => pointSet48
    | 3 => pointSet54
    | 4 => pointSet47
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 45. -/
def step45 : Step := ⟨3, point45⟩
/-- Proposed owner constraints after 46 forced-point assignments. -/
def model46 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet50
    | 2 => pointSet48
    | 3 => pointSet55
    | 4 => pointSet47
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 46. -/
def step46 : Step := ⟨4, point46⟩
/-- Proposed owner constraints after 47 forced-point assignments. -/
def model47 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet50
    | 2 => pointSet48
    | 3 => pointSet55
    | 4 => pointSet56
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 47. -/
def step47 : Step := ⟨2, point47⟩
/-- Proposed owner constraints after 48 forced-point assignments. -/
def model48 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet50
    | 2 => pointSet57
    | 3 => pointSet55
    | 4 => pointSet56
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 48. -/
def step48 : Step := ⟨3, point48⟩
/-- Proposed owner constraints after 49 forced-point assignments. -/
def model49 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet50
    | 2 => pointSet57
    | 3 => pointSet58
    | 4 => pointSet56
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 49. -/
def step49 : Step := ⟨4, point49⟩
/-- Proposed owner constraints after 50 forced-point assignments. -/
def model50 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet40
    | 1 => pointSet50
    | 2 => pointSet57
    | 3 => pointSet58
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 50. -/
def step50 : Step := ⟨0, point50⟩
/-- Proposed owner constraints after 51 forced-point assignments. -/
def model51 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet50
    | 2 => pointSet57
    | 3 => pointSet58
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 51. -/
def step51 : Step := ⟨2, point51⟩
/-- Proposed owner constraints after 52 forced-point assignments. -/
def model52 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet50
    | 2 => pointSet61
    | 3 => pointSet58
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet7
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 52. -/
def step52 : Step := ⟨7, point52⟩
/-- Proposed owner constraints after 53 forced-point assignments. -/
def model53 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet50
    | 2 => pointSet61
    | 3 => pointSet58
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet62
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 53. -/
def step53 : Step := ⟨1, point53⟩
/-- Proposed owner constraints after 54 forced-point assignments. -/
def model54 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet63
    | 2 => pointSet61
    | 3 => pointSet58
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet62
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 54. -/
def step54 : Step := ⟨7, point54⟩
/-- Proposed owner constraints after 55 forced-point assignments. -/
def model55 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet63
    | 2 => pointSet61
    | 3 => pointSet58
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet52
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 55. -/
def step55 : Step := ⟨8, point55⟩
/-- Proposed owner constraints after 56 forced-point assignments. -/
def model56 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet63
    | 2 => pointSet61
    | 3 => pointSet58
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet65
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 56. -/
def step56 : Step := ⟨8, point56⟩
/-- Proposed owner constraints after 57 forced-point assignments. -/
def model57 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet63
    | 2 => pointSet61
    | 3 => pointSet58
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 57. -/
def step57 : Step := ⟨3, point57⟩
/-- Proposed owner constraints after 58 forced-point assignments. -/
def model58 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet63
    | 2 => pointSet61
    | 3 => pointSet67
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 58. -/
def step58 : Step := ⟨2, point58⟩
/-- Proposed owner constraints after 59 forced-point assignments. -/
def model59 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet63
    | 2 => pointSet68
    | 3 => pointSet67
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 59. -/
def step59 : Step := ⟨3, point59⟩
/-- Proposed owner constraints after 60 forced-point assignments. -/
def model60 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet63
    | 2 => pointSet68
    | 3 => pointSet69
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 60. -/
def step60 : Step := ⟨3, point60⟩
/-- Proposed owner constraints after 61 forced-point assignments. -/
def model61 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet63
    | 2 => pointSet68
    | 3 => pointSet70
    | 4 => pointSet59
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 61. -/
def step61 : Step := ⟨4, point61⟩
/-- Proposed owner constraints after 62 forced-point assignments. -/
def model62 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet60
    | 1 => pointSet63
    | 2 => pointSet68
    | 3 => pointSet70
    | 4 => pointSet71
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 62. -/
def step62 : Step := ⟨0, point62⟩
/-- Proposed owner constraints after 63 forced-point assignments. -/
def model63 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet72
    | 1 => pointSet63
    | 2 => pointSet68
    | 3 => pointSet70
    | 4 => pointSet71
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 63. -/
def step63 : Step := ⟨2, point63⟩
/-- Proposed owner constraints after 64 forced-point assignments. -/
def model64 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet72
    | 1 => pointSet63
    | 2 => pointSet73
    | 3 => pointSet70
    | 4 => pointSet71
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 64. -/
def step64 : Step := ⟨0, point64⟩
/-- Proposed owner constraints after 65 forced-point assignments. -/
def model65 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet74
    | 1 => pointSet63
    | 2 => pointSet73
    | 3 => pointSet70
    | 4 => pointSet71
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 65. -/
def step65 : Step := ⟨1, point65⟩
/-- Proposed owner constraints after 66 forced-point assignments. -/
def model66 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet74
    | 1 => pointSet75
    | 2 => pointSet73
    | 3 => pointSet70
    | 4 => pointSet71
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 66. -/
def step66 : Step := ⟨1, point66⟩
/-- Proposed owner constraints after 67 forced-point assignments. -/
def model67 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet74
    | 1 => pointSet76
    | 2 => pointSet73
    | 3 => pointSet70
    | 4 => pointSet71
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The forced-point assignment at trace index 67. -/
def step67 : Step := ⟨1, point67⟩
/-- Proposed owner constraints after 68 forced-point assignments. -/
def model68 : Model :=
  ⟨(fun j => match j.val with
    | 0 => pointSet74
    | 1 => pointSet77
    | 2 => pointSet73
    | 3 => pointSet70
    | 4 => pointSet71
    | 5 => pointSet32
    | 6 => pointSet6
    | 7 => pointSet64
    | 8 => pointSet66
    | _ => pointSet21), capsConstraints, ownerFlags⟩

/-- The shared step constants reproduce the original certificate trace exactly. -/
theorem trace_steps : [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10,
    step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22,
    step23, step24, step25, step26, step27, step28, step29, step30, step31, step32, step33, step34,
    step35, step36, step37, step38, step39, step40, step41, step42, step43, step44, step45, step46,
    step47, step48, step49, step50, step51, step52, step53, step54, step55, step56, step57, step58,
    step59, step60, step61, step62, step63, step64, step65, step66, step67] =
    Data.Sext180000190000.steps := by
  rfl

end Sext180000190000
end ConwaySoifer.Simplified.Certificates
