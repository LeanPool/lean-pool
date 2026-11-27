/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C3.Defs

/-! The values of the generated certificate are paired with kernel checks. -/

@[expose] public section

namespace RACert.S4N1.C3

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
private noncomputable def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (3, 1), (4, 2), (5, 4), (7, 2), (12, 1), (13, 2), (15, 1), (16, 1), (17, 2), (19,
    1), (20, 2), (21, 4), (23, 2), (28, 1), (29, 2), (31, 1), (32, 4), (33, 4), (34, 4), (35, 4),
    (36, 4), (37, 4), (38, 4), (39, 4), (40, 4), (41, 4), (42, 4), (43, 4), (44, 4), (45, 4), (46,
    4), (47, 4), (48, 4), (49, 4), (50, 4), (51, 4), (52, 4), (53, 4), (54, 4), (55, 4), (56, 4),
    (57, 4), (58, 4), (59, 4), (60, 4), (61, 4), (62, 4), (63, 4), (96, 2), (97, 2), (98, 2), (99,
    2), (100, 4), (101, 4), (102, 4), (103, 4), (108, 2), (109, 2), (110, 2), (111, 2), (112, 2),
    (113, 2), (114, 2), (115, 2), (116, 4), (117, 4), (118, 4), (119, 4), (124, 2), (125, 2), (126,
    2), (127, 2), (160, 2), (161, 4), (163, 2), (164, 2), (165, 4), (167, 2), (168, 2), (169, 4),
    (171, 2), (172, 2), (173, 4), (175, 2), (176, 2), (177, 4), (179, 2), (180, 2), (181, 4), (183,
    2), (184, 2), (185, 4), (187, 2), (188, 2), (189, 4), (191, 2), (192, 2), (193, 4), (195, 2),
    (196, 4), (197, 4), (198, 4), (199, 4), (204, 2), (205, 4), (207, 2), (208, 2), (209, 4), (211,
    2), (212, 4), (213, 4), (214, 4), (215, 4), (220, 2), (221, 4), (223, 2), (224, 4), (225, 4),
    (226, 4), (227, 4), (228, 4), (229, 4), (230, 4), (231, 4), (232, 4), (233, 4), (234, 4), (235,
    4), (236, 4), (237, 4), (238, 4), (239, 4), (240, 4), (241, 4), (242, 4)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
private noncomputable def ev0 : List ℕ := []

private def checkedCount0 :
    { total : ℕ // P.sumEvE 20 3 qt ow qmFlat seg0 ev0 0 total = true } :=
  ⟨39888835, by decide +kernel⟩

private theorem sumOK0 :
    P.sumEvE 20 3 qt ow qmFlat seg0 ev0 0 39888835 = true := checkedCount0.property

/-- Orbit minima `(α, orbit size)`, part 1. -/
private noncomputable def seg1 : List (ℕ × ℕ) :=
  [(243, 4), (244, 4), (245, 4), (246, 4), (247, 4), (248, 4), (249, 4), (250, 4), (251, 4), (252,
    4), (253, 4), (254, 4), (255, 4), (480, 1), (481, 2), (483, 1), (484, 2), (485, 4), (487, 2),
    (492, 1), (493, 2), (495, 1), (496, 1), (497, 2), (499, 1), (500, 2), (501, 4), (503, 2), (508,
    1), (509, 2), (511, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
private noncomputable def ev1 : List ℕ := []

private def checkedCount1 :
    { total : ℕ // P.sumEvE 20 3 qt ow qmFlat seg1 ev1 0 total = true } :=
  ⟨51388427, by decide +kernel⟩

private theorem sumOK1 :
    P.sumEvE 20 3 qt ow qmFlat seg1 ev1 0 51388427 = true := checkedCount1.property

/-- All orbit minima of this file. -/
private noncomputable def seg : List (ℕ × ℕ) := seg0 ++ (seg1)

private theorem segOK : checkSeg 9 perms 0 512 seg = true := by decide +kernel

theorem total : OrbitSeg 9 perms (P.leaf (20 + 3)) 0 512 512 91277262 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    ((sumEvE_sum check rows elimOK flatOK sumOK0).append (sumEvE_sum check rows elimOK flatOK
      sumOK1))
    (by decide +kernel)

end S0

end RACert.S4N1.C3
