/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

/-! Exact polynomial certificates for the planar obstruction kernel. -/

@[expose] public section
namespace PlanarMidpoint.Algebra

/-- The ten quartic coefficient equations, in immutable derivative order
`(aₓ,bₓ,cₓ,dₓ,aᵧ,bᵧ,cᵧ,dᵧ)`. -/
def Kernel (a b c d : ℝ) (z : Fin 8 → ℝ) : Prop :=
  3 * a * z 0 - 2 * b * z 1 + 5 * b * z 4 = 0 ∧
  4 * b * z 0 + 8 * b * z 5 + z 1 * (10 * a - 6 * c) + z 4 * (-2 * a + 10 * c) = 0 ∧
  2 * b * z 3 + 5 * b * z 6 + c * z 0 + 14 * c * z 5 + z 1 * (16 * b - 4 * d) + z 2 * (7 * a - 4 *
      c) + z 4 * (-6 * b + 5 * d) = 0 ∧
  2 * b * z 7 + 6 * c * z 1 + 2 * c * z 3 - 4 * c * z 4 + z 2 * (12 * b - 4 * d) + z 5 * (-4 * b +
      6 * d) + z 6 * (2 * a + 6 * c) = 0 ∧
  5 * c * z 2 - 4 * c * z 5 + 2 * c * z 7 + z 6 * (2 * b + d) = 0 ∧
  2 * b * z 0 - 4 * b * z 2 + 5 * b * z 5 + z 1 * (a + 2 * c) = 0 ∧
  -4 * b * z 3 + 2 * b * z 4 + 6 * b * z 6 + 2 * c * z 0 + z 1 * (6 * b + 2 * d) + z 2 * (6 * a -
      4 * c) + z 5 * (-4 * a + 12 * c) = 0 ∧
  14 * b * z 2 + b * z 7 + 5 * c * z 1 + 2 * c * z 4 + z 3 * (5 * a - 6 * c) + z 5 * (-4 * b + 7 *
      d) + z 6 * (-4 * a + 16 * c) = 0 ∧
  8 * c * z 2 + 4 * c * z 7 + z 3 * (10 * b - 2 * d) + z 6 * (-6 * b + 10 * d) = 0 ∧
  5 * c * z 3 - 2 * c * z 6 + 3 * d * z 7 = 0


theorem tracefree_0 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (-a) (-b) z) : (a ^ 2 + b ^ 2) ^ 2 * z 0 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 36 * ((a ^ 2 + b ^ 2) ^ 2 * z 0) = 0 := by
    linear_combination (12 * a ^ 3 - 4 * a * b ^ 2) * h0 + (5 * a ^ 2 * b - 3 * b ^ 3) * h1 + (-8
        * b ^ 3) * h3 + (16 * a * b ^ 2) * h4 + (56 * a ^ 2 * b + 24 * b ^ 3) * h5 + (24 * a * b ^
        2) * h6 + (16 * b ^ 3) * h7 + (-8 * a * b ^ 2) * h8
  linarith only [he]

theorem tracefree_1 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (-a) (-b) z) : (a ^ 2 + b ^ 2) ^ 2 * z 1 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 36 * ((a ^ 2 + b ^ 2) ^ 2 * z 1) = 0 := by
    linear_combination (20 * a ^ 2 * b + 4 * b ^ 3) * h0 + (16 * a * b ^ 2) * h1 + (-14 * a ^ 2 *
        b + 2 * b ^ 3) * h2 + (-16 * a * b ^ 2) * h3 + (-16 * b ^ 3) * h4 + (-36 * a ^ 3 - 36 * a
        * b ^ 2) * h5 + (a ^ 2 * b + b ^ 3) * h6
  linarith only [he]

theorem tracefree_2 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (-a) (-b) z) : (a ^ 2 + b ^ 2) ^ 2 * z 2 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 252 * ((a ^ 2 + b ^ 2) ^ 2 * z 2) = 0 := by
    linear_combination (-28 * a ^ 3 + 84 * a * b ^ 2) * h0 + (-78 * a ^ 2 * b + 42 * b ^ 3) * h1 +
        (112 * a ^ 3 - 16 * a * b ^ 2) * h2 + (143 * a ^ 2 * b + 7 * b ^ 3) * h3 + (144 * a * b ^
        2) * h4 + (-52 * a ^ 2 * b - 84 * b ^ 3) * h5 + (-98 * a ^ 3 - 74 * a * b ^ 2) * h6 + (-30
        * a ^ 2 * b - 14 * b ^ 3) * h7 + (-8 * a * b ^ 2) * h8
  linarith only [he]

theorem tracefree_3 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (-a) (-b) z) : (a ^ 2 + b ^ 2) ^ 2 * z 3 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 5292 * ((a ^ 2 + b ^ 2) ^ 2 * z 3) = 0 := by
    linear_combination (182 * a ^ 2 * b + 2534 * b ^ 3) * h0 + (-462 * a ^ 3 - 3278 * a * b ^ 2) *
        h1 + (4004 * a ^ 2 * b + 724 * b ^ 3) * h2 + (-1260 * a ^ 3 + 2484 * a * b ^ 2) * h3 +
        (-1134 * a ^ 2 * b + 3074 * b ^ 3) * h4 + (-1092 * a ^ 3 + 764 * a * b ^ 2) * h5 + (-3745
        * a ^ 2 * b - 2353 * b ^ 3) * h6 + (252 * a ^ 3 - 676 * a * b ^ 2) * h7 + (-464 * b ^ 3) *
        h8
  linarith only [he]

theorem tracefree_4 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (-a) (-b) z) : (a ^ 2 + b ^ 2) ^ 2 * z 4 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 252 * ((a ^ 2 + b ^ 2) ^ 2 * z 4) = 0 := by
    linear_combination (196 * a ^ 2 * b + 84 * b ^ 3) * h0 + (-21 * a ^ 3 + 83 * a * b ^ 2) * h1 +
        (-84 * a ^ 2 * b + 12 * b ^ 3) * h2 + (-88 * a * b ^ 2) * h3 + (-80 * b ^ 3) * h4 + (-336
        * a ^ 3 - 304 * a * b ^ 2) * h5 + (-42 * a ^ 2 * b - 18 * b ^ 3) * h6 + (-16 * a * b ^ 2)
        * h7 + (-8 * b ^ 3) * h8
  linarith only [he]

theorem tracefree_5 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (-a) (-b) z) : (a ^ 2 + b ^ 2) ^ 2 * z 5 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 252 * ((a ^ 2 + b ^ 2) ^ 2 * z 5) = 0 := by
    linear_combination (-28 * a ^ 3 + 84 * a * b ^ 2) * h0 + (-54 * a ^ 2 * b + 42 * b ^ 3) * h1 +
        (70 * a ^ 3 - 10 * a * b ^ 2) * h2 + (92 * a ^ 2 * b + 28 * b ^ 3) * h3 + (48 * a * b ^ 2)
        * h4 + (-148 * a ^ 2 * b - 84 * b ^ 3) * h5 + (-77 * a ^ 3 - 125 * a * b ^ 2) * h6 + (-24
        * a ^ 2 * b - 56 * b ^ 3) * h7 + (16 * a * b ^ 2) * h8
  linarith only [he]

theorem tracefree_6 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (-a) (-b) z) : (a ^ 2 + b ^ 2) ^ 2 * z 6 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 5292 * ((a ^ 2 + b ^ 2) ^ 2 * z 6) = 0 := by
    linear_combination (-1120 * a ^ 2 * b + 1232 * b ^ 3) * h0 + (-210 * a ^ 3 - 3002 * a * b ^ 2)
        * h1 + (3584 * a ^ 2 * b + 352 * b ^ 3) * h2 + (-693 * a ^ 3 + 2979 * a * b ^ 2) * h3 +
        (-756 * a ^ 2 * b + 3356 * b ^ 3) * h4 + (1428 * a ^ 3 + 3188 * a * b ^ 2) * h5 + (-2464 *
        a ^ 2 * b - 1144 * b ^ 3) * h6 + (-126 * a ^ 3 - 1006 * a * b ^ 2) * h7 + (-440 * b ^ 3) *
        h8
  linarith only [he]

theorem tracefree_7 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (-a) (-b) z) : (a ^ 2 + b ^ 2) ^ 2 * z 7 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 252 * ((a ^ 2 + b ^ 2) ^ 2 * z 7) = 0 := by
    linear_combination (14 * a ^ 3 - 98 * a * b ^ 2) * h0 + (82 * a ^ 2 * b - 126 * b ^ 3) * h1 +
        (-140 * a ^ 3 + 164 * a * b ^ 2) * h2 + (-190 * a ^ 2 * b + 210 * b ^ 3) * h3 + (-126 * a
        ^ 3 - 622 * a * b ^ 2) * h4 + (-132 * a ^ 2 * b + 252 * b ^ 3) * h5 + (91 * a ^ 3 - 197 *
        a * b ^ 2) * h6 + (24 * a ^ 2 * b - 168 * b ^ 3) * h7 + (96 * a * b ^ 2) * h8
  linarith only [he]

theorem normalized_0 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (1 - a) (-b) z) : b * z 0 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 10420830 * (b * z 0) = 0 := by
    linear_combination (-360225648 * a ^ 4 * b + 1681735992 * a ^ 3 * b - 943939296 * a ^ 2 * b ^
        3 - 2882847528 * a ^ 2 * b + 1644487992 * a * b ^ 3 + 2157916062 * a * b - 583713648 * b ^
        5 - 658865376 * b ^ 3 - 593105268 * b) * h0 + (-1050840 * a ^ 5 + 6246660 * a ^ 4 -
        337333680 * a ^ 3 * b ^ 2 - 14419860 * a ^ 3 + 1113246252 * a ^ 2 * b ^ 2 + 16288020 * a ^
        2 - 336282840 * a * b ^ 4 - 1272694320 * a * b ^ 2 - 9048900 * a + 231671592 * b ^ 4 +
        505465773 * b ^ 2 + 1984920) * h1 + (727176672 * a ^ 4 * b - 2787241872 * a ^ 3 * b +
        560401344 * a ^ 2 * b ^ 3 + 3595718828 * a ^ 2 * b - 1073833872 * a * b ^ 3 - 1734384818 *
        a * b - 166775328 * b ^ 5 + 534384060 * b ^ 3 + 198731190 * b) * h2 + (-2732184 * a ^ 5 +
        15587460 * a ^ 4 + 1447207632 * a ^ 3 * b ^ 2 - 34280736 * a ^ 3 - 4237691892 * a ^ 2 * b
        ^ 2 + 36697668 * a ^ 2 + 1449939816 * a * b ^ 4 + 2961506340 * a * b ^ 2 - 19242048 * a -
        1701791352 * b ^ 4 - 159155379 * b ^ 2 + 3969840) * h3 + (-1094127696 * a ^ 4 * b +
        2924299752 * a ^ 3 * b - 176863392 * a ^ 2 * b ^ 3 - 1602110688 * a ^ 2 * b - 465268248 *
        a * b ^ 3 - 636203578 * a * b + 917264304 * b ^ 5 - 149375304 * b ^ 3 + 402424680 * b) *
        h4 + (-4623696 * a ^ 5 + 17560704 * a ^ 4 + 2002144608 * a ^ 3 * b ^ 2 - 23947476 * a ^ 3
        - 3549022632 * a ^ 2 * b ^ 2 + 12715164 * a ^ 2 + 2006768304 * a * b ^ 4 + 1427467716 * a
        * b ^ 2 - 712236 * a - 921975336 * b ^ 4 + 39517278 * b ^ 2 - 992460) * h5 + (-910652184 *
        a ^ 4 * b + 3399215100 * a ^ 3 * b - 368632368 * a ^ 2 * b ^ 3 - 4169323738 * a ^ 2 * b +
        1592687100 * a * b ^ 3 + 1777893382 * a * b + 542019816 * b ^ 5 - 1317640854 * b ^ 3 -
        97132560 * b) * h6 + (840672 * a ^ 5 - 5254200 * a ^ 4 - 892270656 * a ^ 3 * b ^ 2 +
        12761868 * a ^ 3 + 2305169760 * a ^ 2 * b ^ 2 - 15108744 * a ^ 2 - 893111328 * a * b ^ 4 -
        1246932708 * a * b ^ 2 + 8745324 * a + 1341975960 * b ^ 4 - 172722348 * b ^ 2 - 1984920) *
        h7 + (543701160 * a ^ 4 * b - 1446317220 * a ^ 3 * b + 752170320 * a ^ 2 * b ^ 3 +
        774906942 * a ^ 2 * b - 1315949220 * a * b ^ 3 + 336202508 * a * b + 208469160 * b ^ 5 +
        342064674 * b ^ 3 - 205678410 * b) * h8 + (2942352 * a ^ 5 - 16953552 * a ^ 4 - 217603296
        * a ^ 3 * b ^ 2 + 37374876 * a ^ 3 + 893024616 * a ^ 2 * b ^ 2 - 39569964 * a ^ 2 -
        220545648 * a * b ^ 4 - 862587164 * a * b ^ 2 + 20176128 * a + 202266168 * b ^ 4 +
        192824994 * b ^ 2 - 3969840) * h9
  linarith only [he]

theorem normalized_1 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (1 - a) (-b) z) : b * z 1 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 212670 * (b * z 1) = 0 := by
    linear_combination (1778496 * a ^ 4 - 7659228 * a ^ 3 + 3185664 * a ^ 2 * b ^ 2 + 12228498 * a
        ^ 2 - 5603868 * a * b ^ 2 - 8593296 * a + 1407168 * b ^ 4 + 2276424 * b ^ 2 + 2245530) *
        h0 + (2165184 * a ^ 3 * b - 6039690 * a ^ 2 * b + 2165184 * a * b ^ 3 + 5669859 * a * b -
        1293546 * b ^ 3 - 1795353 * b) * h1 + (-3556992 * a ^ 4 + 12354296 * a ^ 3 - 3154944 * a ^
        2 * b ^ 2 - 14655776 * a ^ 2 + 4917368 * a * b ^ 2 + 6606982 * a + 402048 * b ^ 4 -
        2001716 * b ^ 2 - 748510) * h2 + (-5752896 * a ^ 3 * b + 15455334 * a ^ 2 * b - 5752896 *
        a * b ^ 3 - 10140309 * a * b + 5327622 * b ^ 3 + 821100 * b) * h3 + (5335488 * a ^ 4 -
        12306708 * a ^ 3 + 3124224 * a ^ 2 * b ^ 2 + 5550926 * a ^ 2 + 511788 * a * b ^ 2 +
        2734824 * a - 2211264 * b ^ 4 - 207808 * b ^ 2 - 1497020) * h4 + (-7546752 * a ^ 3 * b +
        13514484 * a ^ 2 * b - 7546752 * a * b ^ 3 - 5708958 * a * b + 3692724 * b ^ 3 - 46104 *
        b) * h5 + (4446240 * a ^ 4 - 14998246 * a ^ 3 + 3139584 * a ^ 2 * b ^ 2 + 16849537 * a ^ 2
        - 7867270 * a * b ^ 2 - 6671786 * a - 1306656 * b ^ 4 + 4637668 * b ^ 2 + 374255) * h6 +
        (3959040 * a ^ 3 * b - 8655384 * a ^ 2 * b + 3959040 * a * b ^ 3 + 3963276 * a * b -
        4215192 * b ^ 3 + 514080 * b) * h7 + (-2667744 * a ^ 4 + 6153354 * a ^ 3 - 3170304 * a ^ 2
        * b ^ 2 - 2775463 * a ^ 2 + 4403946 * a * b ^ 2 - 1367412 * a - 502560 * b ^ 4 - 1117036 *
        b ^ 2 + 748510) * h8 + (-371328 * a ^ 3 * b - 938948 * a ^ 2 * b - 371328 * a * b ^ 3 +
        2401926 * a * b + 2428 * b ^ 3 - 909160 * b) * h9
  linarith only [he]

theorem normalized_2 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (1 - a) (-b) z) : b * z 2 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 3473610 * (b * z 2) = 0 := by
    linear_combination (69353568 * a ^ 4 * b - 313823472 * a ^ 3 * b + 180179136 * a ^ 2 * b ^ 3 +
        521835968 * a ^ 2 * b - 306911472 * a * b ^ 3 - 379450382 * a * b + 110825568 * b ^ 5 +
        118792656 * b ^ 3 + 102084318 * b) * h0 + (-700560 * a ^ 5 + 4164440 * a ^ 4 + 60806880 *
        a ^ 3 * b ^ 2 - 9613240 * a ^ 3 - 186179032 * a ^ 2 * b ^ 2 + 10858680 * a ^ 2 + 61507440
        * a * b ^ 4 + 200597200 * a * b ^ 2 - 6032600 * a - 27911472 * b ^ 4 - 77954313 * b ^ 2 +
        1323280) * h1 + (-134223552 * a ^ 4 * b + 495960352 * a ^ 3 * b - 102559104 * a ^ 2 * b ^
        3 - 614528088 * a ^ 2 * b + 178008352 * a * b ^ 3 + 282769768 * a * b + 31664448 * b ^ 5 -
        83358520 * b ^ 3 - 29482250 * b) * h2 + (-1821456 * a ^ 5 + 10391640 * a ^ 4 - 273210912 *
        a ^ 3 * b ^ 2 - 22853824 * a ^ 3 + 780180072 * a ^ 2 * b ^ 2 + 24465112 * a ^ 2 -
        271389456 * a * b ^ 4 - 528230520 * a * b ^ 2 - 12828032 * a + 296316432 * b ^ 4 +
        31363599 * b ^ 2 + 2646560) * h3 + (199093536 * a ^ 4 * b - 498385232 * a ^ 3 * b +
        24939072 * a ^ 2 * b ^ 3 + 232444368 * a ^ 2 * b + 130606768 * a * b ^ 3 + 127289598 * a *
        b - 174154464 * b ^ 5 + 27036544 * b ^ 3 - 66077130 * b) * h4 + (-3082464 * a ^ 5 +
        11707136 * a ^ 4 - 379412928 * a ^ 3 * b ^ 2 - 15964984 * a ^ 3 + 645359312 * a ^ 2 * b ^
        2 + 8476776 * a ^ 2 - 376330464 * a * b ^ 4 - 236070536 * a * b ^ 2 - 474824 * a +
        142900176 * b ^ 4 - 12507798 * b ^ 2 - 661640) * h5 + (166658544 * a ^ 4 * b - 599132600 *
        a ^ 3 * b + 63749088 * a ^ 2 * b ^ 3 + 703674108 * a ^ 2 * b - 263900600 * a * b ^ 3 -
        283956257 * a * b - 102909456 * b ^ 5 + 210095684 * b ^ 3 + 12756205 * b) * h6 + (560448 *
        a ^ 5 - 3502800 * a ^ 4 + 167008896 * a ^ 3 * b ^ 2 + 8507912 * a ^ 3 - 416573760 * a ^ 2
        * b ^ 2 - 10072496 * a ^ 2 + 166448448 * a * b ^ 4 + 220295208 * a * b ^ 2 + 5830216 * a -
        233358960 * b ^ 4 + 22379388 * b ^ 2 - 1323280) * h7 + (-101788560 * a ^ 4 * b + 259747720
        * a ^ 3 * b - 141369120 * a ^ 2 * b ^ 3 - 133654452 * a ^ 2 * b + 235555720 * a * b ^ 3 -
        51577653 * a * b - 39580560 * b ^ 5 - 61674284 * b ^ 3 + 30061185 * b) * h8 + (1961568 * a
        ^ 5 - 11302368 * a ^ 4 + 45395136 * a ^ 3 * b ^ 2 + 24916584 * a ^ 3 - 191749456 * a ^ 2 *
        b ^ 2 - 26379976 * a ^ 2 + 43433568 * a * b ^ 4 + 186631544 * a * b ^ 2 + 13450752 * a -
        49119088 * b ^ 4 - 35839154 * b ^ 2 - 2646560) * h9
  linarith only [he]

theorem normalized_3 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (1 - a) (-b) z) : b * z 3 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 4466070 * (b * z 3) = 0 := by
    linear_combination (-41654016 * a ^ 4 + 182198868 * a ^ 3 - 78159744 * a ^ 2 * b ^ 2 -
        294510078 * a ^ 2 + 138594708 * a * b ^ 2 + 209039616 * a - 36505728 * b ^ 4 - 60434964 *
        b ^ 2 - 55074390) * h0 + (-49443264 * a ^ 3 * b + 141836910 * a ^ 2 * b - 49443264 * a * b
        ^ 3 - 135043059 * a * b + 31790286 * b ^ 3 + 42649413 * b) * h1 + (83308032 * a ^ 4 -
        294974376 * a ^ 3 + 72877824 * a ^ 2 * b ^ 2 + 354778736 * a ^ 2 - 118485288 * a * b ^ 2 -
        161470522 * a - 10430208 * b ^ 4 + 49347396 * b ^ 2 + 18358130) * h2 + (138033216 * a ^ 3
        * b - 378198114 * a ^ 2 * b + 138033216 * a * b ^ 3 + 254209029 * a * b - 135266562 * b ^
        3 - 22853610 * b) * h3 + (-124962048 * a ^ 4 + 296672508 * a ^ 3 - 67595904 * a ^ 2 * b ^
        2 - 137453826 * a ^ 2 - 12701508 * a * b ^ 2 - 65927224 * a + 57366144 * b ^ 4 + 8791788 *
        b ^ 2 + 36716260) * h4 + (182328192 * a ^ 3 * b - 329874204 * a ^ 2 * b + 182328192 * a *
        b ^ 3 + 143535678 * a * b - 92263644 * b ^ 3 + 4010334 * b) * h5 + (-104135040 * a ^ 4 +
        358304466 * a ^ 3 - 70236864 * a ^ 2 * b ^ 2 - 408337207 * a ^ 2 + 187136370 * a * b ^ 2 +
        163346846 * a + 33898176 * b ^ 4 - 113982858 * b ^ 2 - 9179065) * h6 + (-93738240 * a ^ 3
        * b + 211722024 * a ^ 2 * b - 93738240 * a * b ^ 3 - 99916236 * a * b + 106996392 * b ^ 3
        - 11119530 * b) * h7 + (62481024 * a ^ 4 - 148336254 * a ^ 3 + 75518784 * a ^ 2 * b ^ 2 +
        68726913 * a ^ 2 - 110053086 * a * b ^ 2 + 32963612 * a + 13037760 * b ^ 4 + 29358966 * b
        ^ 2 - 18358130) * h8 + (5148288 * a ^ 3 * b + 29274828 * a ^ 2 * b + 5148288 * a * b ^ 3 -
        64044326 * a * b + 1115532 * b ^ 3 + 26064230 * b) * h9
  linarith only [he]

theorem normalized_4 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (1 - a) (-b) z) : b * z 4 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 1488690 * (b * z 4) = 0 := by
    linear_combination (37852512 * a ^ 4 - 172463856 * a ^ 3 + 88738368 * a ^ 2 * b ^ 2 +
        289936026 * a ^ 2 - 155470896 * a * b ^ 2 - 213890532 * a + 50885856 * b ^ 4 + 62762688 *
        b ^ 2 + 58565850) * h0 + (38605248 * a ^ 3 * b - 120079440 * a ^ 2 * b + 38605248 * a * b
        ^ 3 + 129183723 * a * b - 25628592 * b ^ 3 - 48453876 * b) * h1 + (-75705024 * a ^ 4 +
        281840192 * a ^ 3 - 61166208 * a ^ 2 * b ^ 2 - 355519812 * a ^ 2 + 109931456 * a * b ^ 2 +
        168906594 * a + 14538816 * b ^ 4 - 51789752 * b ^ 2 - 19521950) * h2 + (-141882432 * a ^ 3
        * b + 406776048 * a ^ 2 * b - 141882432 * a * b ^ 3 - 281084493 * a * b + 157409424 * b ^
        3 + 17859180 * b) * h3 + (113557536 * a ^ 4 - 290276496 * a ^ 3 + 33594048 * a ^ 2 * b ^ 2
        + 150462542 * a ^ 2 + 36548016 * a * b ^ 2 + 64505888 * a - 79963488 * b ^ 4 + 8447504 * b
        ^ 2 - 39043900) * h4 + (-193521024 * a ^ 3 * b + 344977488 * a ^ 2 * b - 193521024 * a * b
        ^ 3 - 141372846 * a * b + 91238928 * b ^ 3 - 2640168 * b) * h5 + (94631280 * a ^ 4 -
        342837112 * a ^ 3 + 47380128 * a ^ 2 * b ^ 2 + 410746929 * a ^ 2 - 166556440 * a * b ^ 2 -
        172302072 * a - 47251152 * b ^ 4 + 125442796 * b ^ 2 + 9760975) * h6 + (90243840 * a ^ 3 *
        b - 223054128 * a ^ 2 * b + 90243840 * a * b ^ 3 + 116671212 * a * b - 124231344 * b ^ 3 +
        15185760 * b) * h7 + (-56778768 * a ^ 4 + 145138248 * a ^ 3 - 74952288 * a ^ 2 * b ^ 2 -
        75231271 * a ^ 2 + 123773352 * a * b ^ 2 - 32252944 * a - 18173520 * b ^ 4 - 32066692 * b
        ^ 2 + 19521950) * h8 + (13033344 * a ^ 3 * b - 70104176 * a ^ 2 * b + 13033344 * a * b ^ 3
        + 78021142 * a * b - 14011184 * b ^ 3 - 20155880 * b) * h9
  linarith only [he]

theorem normalized_5 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (1 - a) (-b) z) : b * z 5 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 20841660 * (b * z 5) = 0 := by
    linear_combination (1167326352 * a ^ 4 * b - 5486644488 * a ^ 3 * b + 3051196704 * a ^ 2 * b ^
        3 + 9472188072 * a ^ 2 * b - 5367220488 * a * b ^ 3 - 7155733008 * a * b + 1883870352 * b
        ^ 5 + 2202883344 * b ^ 3 + 2002863072 * b) * h0 + (-1050840 * a ^ 5 + 6246660 * a ^ 4 +
        1072714320 * a ^ 3 * b ^ 2 - 14419860 * a ^ 3 - 3597660468 * a ^ 2 * b ^ 2 + 16288020 * a
        ^ 2 + 1073765160 * a * b ^ 4 + 4155921120 * a * b ^ 2 - 9048900 * a - 797443128 * b ^ 4 -
        1660748772 * b ^ 2 + 1984920) * h1 + (-2327927328 * a ^ 4 * b + 9003599088 * a ^ 3 * b -
        1789678656 * a ^ 2 * b ^ 3 - 11712971572 * a ^ 2 * b + 3510095088 * a * b ^ 3 + 5702568122
        * a * b + 538248672 * b ^ 5 - 1764410340 * b ^ 3 - 660802240 * b) * h2 + (-2732184 * a ^ 5
        + 15587460 * a ^ 4 - 4663000368 * a ^ 3 * b ^ 2 - 34280736 * a ^ 3 + 13771387308 * a ^ 2 *
        b ^ 2 + 36697668 * a ^ 2 - 4660268184 * a * b ^ 4 - 9769958220 * a * b ^ 2 - 19242048 * a
        + 5575255848 * b ^ 4 + 594610596 * b ^ 2 + 3969840) * h3 + (3488528304 * a ^ 4 * b -
        9415529688 * a ^ 3 * b + 528160608 * a ^ 2 * b ^ 3 + 5182313232 * a ^ 2 * b + 1452054312 *
        a * b ^ 3 + 2110446812 * a * b - 2960367696 * b ^ 5 + 396671496 * b ^ 3 - 1337483840 * b)
        * h4 + (-4623696 * a ^ 5 + 17560704 * a ^ 4 - 6458143392 * a ^ 3 * b ^ 2 - 23947476 * a ^
        3 + 11571734808 * a ^ 2 * b ^ 2 + 12715164 * a ^ 2 - 6453519696 * a * b ^ 4 - 4764364764 *
        a * b ^ 2 - 712236 * a + 3075070104 * b ^ 4 - 119968392 * b ^ 2 - 992460) * h5 +
        (2908227816 * a ^ 4 * b - 10957448100 * a ^ 3 * b + 1158919632 * a ^ 2 * b ^ 3 +
        13556332142 * a ^ 2 * b - 5165384100 * a * b ^ 3 - 5839746013 * a * b - 1749308184 * b ^ 5
        + 4323671106 * b ^ 3 + 327423740 * b) * h6 + (840672 * a ^ 5 - 5254200 * a ^ 4 +
        2867857344 * a ^ 3 * b ^ 2 + 12761868 * a ^ 3 - 7507687200 * a ^ 2 * b ^ 2 - 15108744 * a
        ^ 2 + 2867016672 * a * b ^ 4 + 4143938652 * a * b ^ 2 + 8745324 * a - 4397409000 * b ^ 4 +
        523971312 * b ^ 2 - 1984920) * h7 + (-1747626840 * a ^ 4 * b + 4723597500 * a ^ 3 * b -
        2420437680 * a ^ 2 * b ^ 3 - 2617305018 * a ^ 2 * b + 4305613500 * a * b ^ 3 - 1037122687
        * a * b - 672810840 * b ^ 5 - 1134444486 * b ^ 3 + 664275850 * b) * h8 + (2942352 * a ^ 5
        - 16953552 * a ^ 4 + 722428704 * a ^ 3 * b ^ 2 + 37374876 * a ^ 3 - 2905634904 * a ^ 2 * b
        ^ 2 - 39569964 * a ^ 2 + 719486352 * a * b ^ 4 + 2825006596 * a * b ^ 2 + 20176128 * a -
        619625352 * b ^ 4 - 677080816 * b ^ 2 - 3969840) * h9
  linarith only [he]

theorem normalized_6 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (1 - a) (-b) z) : b * z 6 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 4466070 * (b * z 6) = 0 := by
    linear_combination (-28007136 * a ^ 4 + 116376648 * a ^ 3 - 42467904 * a ^ 2 * b ^ 2 -
        178359318 * a ^ 2 + 74172168 * a * b ^ 2 + 119617236 * a - 14460768 * b ^ 4 - 31704264 * b
        ^ 2 - 29627430) * h0 + (-36846144 * a ^ 3 * b + 97078740 * a ^ 2 * b - 36846144 * a * b ^
        3 - 82153569 * a * b + 19924596 * b ^ 3 + 21920973 * b) * h1 + (56014272 * a ^ 4 -
        186074736 * a ^ 3 + 51882624 * a ^ 2 * b ^ 2 + 209436116 * a ^ 2 - 73970928 * a * b ^ 2 -
        89251462 * a - 4131648 * b ^ 4 + 26406576 * b ^ 2 + 9875810) * h2 + (83445696 * a ^ 3 * b
        - 212855244 * a ^ 2 * b + 83445696 * a * b ^ 3 + 132512199 * a * b - 65801772 * b ^ 3 -
        14235885 * b) * h3 + (-84021408 * a ^ 4 + 181087128 * a ^ 3 - 61297344 * a ^ 2 * b ^ 2 -
        70210866 * a ^ 2 - 916008 * a * b ^ 2 - 40241584 * a + 22724064 * b ^ 4 + 10563528 * b ^ 2
        + 19751620) * h4 + (106745472 * a ^ 3 * b - 189444504 * a ^ 2 * b + 106745472 * a * b ^ 3
        + 80855178 * a * b - 51211224 * b ^ 3 + 1843854 * b) * h5 + (-70017840 * a ^ 4 + 225591636
        * a ^ 3 - 56589984 * a ^ 2 * b ^ 2 - 239702767 * a ^ 2 + 122308020 * a * b ^ 2 + 89066876
        * a + 13427856 * b ^ 4 - 58889088 * b ^ 2 - 4937905) * h6 + (-60145920 * a ^ 3 * b +
        120493344 * a ^ 2 * b - 60145920 * a * b ^ 3 - 47956356 * a * b + 52159392 * b ^ 3 -
        4753200 * b) * h7 + (42010704 * a ^ 4 - 90543564 * a ^ 3 + 47175264 * a ^ 2 * b ^ 2 +
        35105433 * a ^ 2 - 57159276 * a * b ^ 2 + 20120792 * a + 5164560 * b ^ 4 + 14868336 * b ^
        2 - 9875810) * h8 + (13546368 * a ^ 3 * b - 2880552 * a ^ 2 * b + 13546368 * a * b ^ 3 -
        31333826 * a * b - 4445928 * b ^ 3 + 15791810 * b) * h9
  linarith only [he]

theorem normalized_7 (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (1 - a) (-b) z) : b * z 7 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 20841660 * (b * z 7) = 0 := by
    linear_combination (566065296 * a ^ 4 * b - 3474665256 * a ^ 3 * b + 1710434592 * a ^ 2 * b ^
        3 + 7173706128 * a ^ 2 * b - 3378281256 * a * b ^ 3 - 6187677672 * a * b + 1144369296 * b
        ^ 5 + 1667846664 * b ^ 3 + 1922571504 * b) * h0 + (133456680 * a ^ 5 - 668275860 * a ^ 4 +
        1134369360 * a ^ 3 * b ^ 2 + 1213019640 * a ^ 3 - 4276249620 * a ^ 2 * b ^ 2 - 970917780 *
        a ^ 2 + 1000912680 * a * b ^ 4 + 5143100916 * a * b ^ 2 + 308596680 * a - 1342949760 * b ^
        4 - 2001220656 * b ^ 2 - 15879360) * h1 + (-1986253344 * a ^ 4 * b + 8272106544 * a ^ 3 *
        b - 1659290688 * a ^ 2 * b ^ 3 - 11559403732 * a ^ 2 * b + 3838442544 * a * b ^ 3 +
        6106744502 * a * b + 326962656 * b ^ 5 - 2040556644 * b ^ 3 - 833193970 * b) * h2 +
        (346987368 * a ^ 5 - 1654477524 * a ^ 4 - 3065001264 * a ^ 3 * b ^ 2 + 2823875628 * a ^ 3
        + 9765448140 * a ^ 2 * b ^ 2 - 2110974096 * a ^ 2 - 3411988632 * a * b ^ 4 - 7448473272 *
        a * b ^ 2 + 626347344 * a + 4817621664 * b ^ 4 + 334854252 * b ^ 2 - 31758720) * h3 +
        (3406441392 * a ^ 4 * b - 10563563832 * a ^ 3 * b + 1608146784 * a ^ 2 * b ^ 3 +
        7525107432 * a ^ 2 * b - 1792619832 * a * b ^ 3 + 1445268380 * a * b - 1798294608 * b ^ 5
        + 322488720 * b ^ 3 - 1581036380 * b) * h4 + (587209392 * a ^ 5 - 1679989584 * a ^ 4 -
        4030317216 * a ^ 3 * b ^ 2 + 1501825500 * a ^ 3 + 8748321240 * a ^ 2 * b ^ 2 - 304580136 *
        a ^ 2 - 4617526608 * a * b ^ 4 - 4967458044 * a * b ^ 2 - 112404852 * a + 3585046824 * b ^
        4 + 249454020 * b ^ 2 + 7939680) * h5 + (2696347368 * a ^ 4 * b - 10661371764 * a ^ 3 * b
        + 1633718736 * a ^ 2 * b ^ 3 + 13942807346 * a ^ 2 * b - 5986747764 * a * b ^ 3 -
        6418198975 * a * b - 1062628632 * b ^ 5 + 4773265614 * b ^ 3 + 440416025 * b) * h6 +
        (-106765344 * a ^ 5 + 567243432 * a ^ 4 + 2099685312 * a ^ 3 * b ^ 2 - 1095547404 * a ^ 3
        - 5754692256 * a ^ 2 * b ^ 2 + 925358028 * a ^ 2 + 2206450656 * a * b ^ 4 + 3031404516 * a
        * b ^ 2 - 306168072 * a - 3815951688 * b ^ 4 + 846400164 * b ^ 2 + 15879360) * h7 +
        (-1276159320 * a ^ 4 * b + 3671194476 * a ^ 3 * b - 1684862640 * a ^ 2 * b ^ 3 -
        1925632854 * a ^ 2 * b + 3333850476 * a * b ^ 3 - 1393691857 * a * b - 408703320 * b ^ 5 -
        861382746 * b ^ 3 + 831457165 * b) * h8 + (-373678704 * a ^ 5 + 1802961216 * a ^ 4 -
        169053408 * a ^ 3 * b ^ 2 - 3079276452 * a ^ 3 + 167628264 * a ^ 2 * b ^ 2 + 2245107984 *
        a ^ 2 + 204625296 * a * b ^ 4 + 228391252 * a * b ^ 2 - 633819984 * a + 195963048 * b ^ 4
        - 428148292 * b ^ 2 + 31758720) * h9
  linarith only [he]

theorem even_0 (a c : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a 0 c 0 z) : a * c ^ 1 * z 0 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 3 * (a * c ^ 1 * z 0) = 0 := by
    linear_combination (c) * h0
  linarith only [he]

theorem even_1 (a c : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a 0 c 0 z) : a * c ^ 3 * z 1 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 867 * (a * c ^ 3 * z 1) = 0 := by
    linear_combination (-10 * a * c ^ 2 + 170 * c ^ 3) * h1 + (10 * a ^ 2 * c - 118 * a * c ^ 2 +
        340 * c ^ 3) * h3 + (-10 * a * c ^ 2 - 85 * c ^ 3) * h5 + (10 * a ^ 2 * c - 16 * a * c ^ 2
        - 170 * c ^ 3) * h7 + (-10 * a ^ 3 + 24 * a ^ 2 * c + 198 * a * c ^ 2 - 340 * c ^ 3) * h9
  linarith only [he]

theorem even_2 (a c : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a 0 c 0 z) : a * c ^ 1 * z 2 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 18 * (a * c ^ 1 * z 2) = 0 := by
    linear_combination (4 * c) * h2 + (2 * a + 8 * c) * h4 + (-2 * c) * h6 + (-a - 4 * c) * h8
  linarith only [he]

theorem even_3 (a c : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a 0 c 0 z) : a * c ^ 3 * z 3 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 10404 * (a * c ^ 3 * z 3) = 0 := by
    linear_combination (5 * a * c ^ 2 - 374 * c ^ 3) * h1 + (-5 * a ^ 2 * c + 348 * a * c ^ 2 -
        748 * c ^ 3) * h3 + (5 * a * c ^ 2 + 187 * c ^ 3) * h5 + (-5 * a ^ 2 * c + 297 * a * c ^ 2
        + 374 * c ^ 3) * h7 + (5 * a ^ 3 - 301 * a ^ 2 * c + 1924 * a * c ^ 2 + 748 * c ^ 3) * h9
  linarith only [he]

theorem even_4 (a c : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a 0 c 0 z) : a * c ^ 3 * z 4 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 6936 * (a * c ^ 3 * z 4) = 0 := by
    linear_combination (-355 * a * c ^ 2 + 1122 * c ^ 3) * h1 + (355 * a ^ 2 * c - 2744 * a * c ^
        2 + 2244 * c ^ 3) * h3 + (-355 * a * c ^ 2 - 561 * c ^ 3) * h5 + (355 * a ^ 2 * c + 877 *
        a * c ^ 2 - 1122 * c ^ 3) * h7 + (-355 * a ^ 3 - 593 * a ^ 2 * c + 3272 * a * c ^ 2 - 2244
        * c ^ 3) * h9
  linarith only [he]

theorem even_5 (a c : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a 0 c 0 z) : a * c ^ 1 * z 5 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 36 * (a * c ^ 1 * z 5) = 0 := by
    linear_combination (2 * c) * h2 + (-8 * a + 4 * c) * h4 + (-c) * h6 + (4 * a - 2 * c) * h8
  linarith only [he]

theorem even_6 (a c : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a 0 c 0 z) : a * c ^ 3 * z 6 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 20808 * (a * c ^ 3 * z 6) = 0 := by
    linear_combination (25 * a * c ^ 2 - 1870 * c ^ 3) * h1 + (-25 * a ^ 2 * c + 1740 * a * c ^ 2
        - 3740 * c ^ 3) * h3 + (25 * a * c ^ 2 + 935 * c ^ 3) * h5 + (-25 * a ^ 2 * c + 1485 * a *
        c ^ 2 + 1870 * c ^ 3) * h7 + (25 * a ^ 3 - 1505 * a ^ 2 * c - 784 * a * c ^ 2 + 3740 * c ^
        3) * h9
  linarith only [he]

theorem even_7 (a c : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a 0 c 0 z) : a * c ^ 1 * z 7 = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have he : 36 * (a * c ^ 1 * z 7) = 0 := by
    linear_combination (-16 * c) * h2 + (-8 * a - 32 * c) * h4 + (8 * c) * h6 + (13 * a + 16 * c)
        * h8
  linarith only [he]


/-- Every nonzero tracefree cubic has injective obstruction matrix. -/
theorem tracefree_injective (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (-a) (-b) z) (hab : a ≠ 0 ∨ b ≠ 0) : z = 0 := by
  have hn : a ^ 2 + b ^ 2 ≠ 0 := by
    rcases hab with ha | hb
    · exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg b))
    · exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg a) (sq_pos_of_ne_zero hb))
  funext i
  change z i = 0
  have hm : (a ^ 2 + b ^ 2) ^ 2 * z i = 0 := by
    fin_cases i
    · exact tracefree_0 a b z h
    · exact tracefree_1 a b z h
    · exact tracefree_2 a b z h
    · exact tracefree_3 a b z h
    · exact tracefree_4 a b z h
    · exact tracefree_5 a b z h
    · exact tracefree_6 a b z h
    · exact tracefree_7 a b z h
  exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero 2 hn)

/-- The even slice has injective obstruction matrix away from its two axes. -/
theorem even_injective (a c : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a 0 c 0 z) (ha : a ≠ 0) (hc : c ≠ 0) : z = 0 := by
  funext i
  change z i = 0
  fin_cases i
  · exact (mul_eq_zero.mp (even_0 a c z h)).resolve_left (mul_ne_zero ha (pow_ne_zero 1 hc))
  · exact (mul_eq_zero.mp (even_1 a c z h)).resolve_left (mul_ne_zero ha (pow_ne_zero 3 hc))
  · exact (mul_eq_zero.mp (even_2 a c z h)).resolve_left (mul_ne_zero ha (pow_ne_zero 1 hc))
  · exact (mul_eq_zero.mp (even_3 a c z h)).resolve_left (mul_ne_zero ha (pow_ne_zero 3 hc))
  · exact (mul_eq_zero.mp (even_4 a c z h)).resolve_left (mul_ne_zero ha (pow_ne_zero 3 hc))
  · exact (mul_eq_zero.mp (even_5 a c z h)).resolve_left (mul_ne_zero ha (pow_ne_zero 1 hc))
  · exact (mul_eq_zero.mp (even_6 a c z h)).resolve_left (mul_ne_zero ha (pow_ne_zero 3 hc))
  · exact (mul_eq_zero.mp (even_7 a c z h)).resolve_left (mul_ne_zero ha (pow_ne_zero 1 hc))

/-- The trace-normalized slice has exactly the two possible rank exceptions. -/
theorem normalized_classification (a b : ℝ) (z : Fin 8 → ℝ)
    (h : Kernel a b (1 - a) (-b) z) (hz : z ≠ 0) : b = 0 ∧ (a = 0 ∨ a = 1) := by
  have hb : b = 0 := by
    by_contra hb
    apply hz
    funext i
    change z i = 0
    have hm : b * z i = 0 := by
      fin_cases i
      · exact normalized_0 a b z h
      · exact normalized_1 a b z h
      · exact normalized_2 a b z h
      · exact normalized_3 a b z h
      · exact normalized_4 a b z h
      · exact normalized_5 a b z h
      · exact normalized_6 a b z h
      · exact normalized_7 a b z h
    exact (mul_eq_zero.mp hm).resolve_left hb
  refine ⟨hb, ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    by_contra hane
    have hc : 1 - a ≠ 0 := by intro he; apply hane; linarith
    have hk : Kernel a 0 (1 - a) 0 z := by simpa only [hb, neg_zero] using h
    exact hz (even_injective a (1 - a) z hk ha hc)

/-- At the pure-cube representative, the kernel has only its final coordinate. -/
theorem pure_kernel (z : Fin 8 → ℝ) (h : Kernel 1 0 0 0 z) :
    ∀ i : Fin 8, i ≠ 7 → z i = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  intro i hi
  fin_cases i <;> norm_num at * <;> linarith

/-- At the mixed representative, every kernel vector has the stated ratios. -/
theorem mixed_kernel (z : Fin 8 → ℝ) (h : Kernel 0 0 1 0 z) :
    z 1 = 0 ∧ z 3 = 0 ∧ z 4 = 0 ∧ z 6 = 0 ∧
      z 0 = 2 * z 5 ∧ z 2 = 4 * z 5 ∧ z 7 = -8 * z 5 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  norm_num at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Tangency to the pure-cube graph removes its remaining kernel direction. -/
theorem pure_tangent_injective (z : Fin 8 → ℝ) (h : Kernel 1 0 0 0 z)
    (ht : z 7 = 0) : z = 0 := by
  funext i
  change z i = 0
  by_cases hi : i = 7
  · simpa only [hi] using ht
  · exact pure_kernel z h i hi

/-- Tangency to the mixed-cube graph removes its remaining kernel direction. -/
theorem mixed_tangent_injective (z : Fin 8 → ℝ) (h : Kernel 0 0 1 0 z)
    (ht : z 0 = 0) : z = 0 := by
  rcases mixed_kernel z h with ⟨h1, h3, h4, h6, h0, h2, h7⟩
  funext i
  change z i = 0
  fin_cases i <;> norm_num at * <;> linarith
end PlanarMidpoint.Algebra
