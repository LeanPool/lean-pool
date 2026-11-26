/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C2.Defs

/-! The values of the generated certificate are paired with kernel checks. -/

@[expose] public section

namespace RACert.S2N2.C2

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (3, 1), (4, 4), (5, 4), (6, 4), (7, 4), (12, 2), (13, 2), (14, 2), (15, 2), (20,
    2), (21, 4), (23, 2), (24, 2), (25, 4), (27, 2), (28, 4), (29, 4), (30, 4), (31, 4), (60, 1),
    (61, 2), (63, 1), (64, 4), (65, 8), (67, 4), (68, 8), (69, 8), (70, 8), (71, 8), (72, 8), (73,
    8), (74, 8), (75, 8), (76, 8), (77, 8), (78, 8), (79, 8), (84, 8), (85, 8), (86, 8), (87, 8),
    (88, 4), (89, 8), (91, 4), (92, 8), (93, 8), (94, 8), (95, 8), (100, 4), (101, 8), (103, 4),
    (108, 8), (109, 8), (110, 8), (111, 8), (124, 4), (125, 8), (127, 4), (192, 2), (193, 4), (195,
    2), (196, 8), (197, 8), (198, 8), (199, 8), (204, 4), (205, 4), (206, 4), (207, 4), (212, 4),
    (213, 8), (215, 4), (216, 4), (217, 8), (219, 4), (220, 8), (221, 8), (222, 8), (223, 8), (252,
    2), (253, 4), (255, 2), (320, 2), (321, 4), (323, 2), (324, 4), (325, 4), (326, 4), (327, 4),
    (328, 4), (329, 4), (330, 4), (331, 4), (332, 4), (333, 4), (334, 4), (335, 4), (340, 4), (341,
    4), (342, 4), (343, 4), (344, 2), (345, 4), (347, 2), (348, 4), (349, 4), (350, 4), (351, 4),
    (356, 2), (357, 4), (359, 2), (364, 4), (365, 4), (366, 4), (367, 4), (380, 2), (381, 4), (383,
    2), (384, 2), (385, 4), (387, 2), (388, 8), (389, 8), (390, 8), (391, 8), (396, 4), (397, 4),
    (398, 4), (399, 4), (404, 4), (405, 8), (407, 4), (408, 4), (409, 8), (411, 4), (412, 8), (413,
    8), (414, 8), (415, 8), (444, 2), (445, 4), (447, 2), (448, 4), (449, 8), (451, 4), (452, 8),
    (453, 8), (454, 8), (455, 8), (456, 8), (457, 8), (458, 8), (459, 8), (460, 8), (461, 8), (462,
    8), (463, 8), (468, 8), (469, 8), (470, 8), (471, 8), (472, 4), (473, 8), (475, 4), (476, 8),
    (477, 8), (478, 8), (479, 8), (484, 4), (485, 8)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := [0, 0, 0, 0, 0, 72, 72, 0, 0, 0, 0, 0, 0, 0, 0, 74, 74, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 72, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 72, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  72, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 72]

private def checkedCount0 :
    { total : ℕ // P.sumEvE 20 2 qt ow qmFlat seg0 ev0 0 total = true } :=
  ⟨66297691, by decide +kernel⟩

theorem sumOK0 :
    P.sumEvE 20 2 qt ow qmFlat seg0 ev0 0 66297691 = true := checkedCount0.property

/-- Orbit minima `(α, orbit size)`, part 1. -/
def seg1 : List (ℕ × ℕ) :=
  [(487, 4), (492, 8), (493, 8), (494, 8), (495, 8), (508, 4), (509, 8), (511, 4), (960, 1), (961,
    2), (963, 1), (964, 4), (965, 4), (966, 4), (967, 4), (972, 2), (973, 2), (974, 2), (975, 2),
    (980, 2), (981, 4), (983, 2), (984, 2), (985, 4), (987, 2), (988, 4), (989, 4), (990, 4), (991,
    4), (1020, 1), (1021, 2), (1023, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev1 : List ℕ := []

private def checkedCount1 :
    { total : ℕ // P.sumEvE 20 2 qt ow qmFlat seg1 ev1 0 total = true } :=
  ⟨39582419, by decide +kernel⟩

theorem sumOK1 :
    P.sumEvE 20 2 qt ow qmFlat seg1 ev1 0 39582419 = true := checkedCount1.property

/-- All orbit minima of this file. -/
def seg : List (ℕ × ℕ) := seg0 ++ (seg1)

theorem segOK : checkSeg 10 perms 0 1024 seg = true := by decide +kernel

theorem total : OrbitSeg 10 perms (P.leaf (20 + 2)) 0 1024 1024 105880110 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    ((sumEvE_sum check rows elimOK flatOK sumOK0).append (sumEvE_sum check rows elimOK flatOK
      sumOK1))
    (by decide +kernel)

end S0

end RACert.S2N2.C2
