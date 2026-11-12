/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceVertices

-- [TABLET NODE: P4733T1EdgeRow]

/-!
# P4733T1EdgeRow

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Write $X_{m,n}$ for a periodic vertex with label $X$ and coordinates
$(m,n)$, and use the same subscripts for faces. An omitted subscript
means $(0,0)$. For $0\leq r<18$, define the ordered edge and its ordered
incident faces $(a_r,b_r;f_r,g_r)$ by the following table.
$$
\begin{array}{r|cc|cc}
r&a_r&b_r&f_r&g_r\\\hline
0&A&B&I_1&I_2\\
1&A&B_{0,1}&J_1&J_2\\
2&A&B_{1,1}&J_3&J_4\\
3&A&C&I_1&I_3\\
4&A&C_{1,1}&J_3&J_5\\
5&A&D&I_2&J_4\\
6&A&E_{0,1}&J_1&J_5\\
7&A&F&I_3&J_2\\
8&B&C&I_1&(J_3)_{-1,-1}\\
9&B&D_{-1,-1}&(J_4)_{-1,-1}&J_6\\
10&B&D&I_2&I_4\\
11&B&E&I_4&(J_1)_{0,-1}\\
12&B&F_{0,-1}&(J_2)_{0,-1}&J_6\\
13&C&D_{-1,0}&J_7&J_8\\
14&C&E_{-1,0}&(J_5)_{-1,-1}&J_7\\
15&C&F&I_3&J_8\\
16&D&E&I_4&(J_7)_{1,0}\\
17&D&F_{1,0}&(J_6)_{1,1}&(J_8)_{1,0}
\end{array}
$$
The value is stored as $((a_r,b_r),(f_r,g_r))$.
-/
def P4733T1EdgeRow (r : Fin 18) :
    (PeriodicSubtileIndex × PeriodicSubtileIndex) ×
      (PeriodicSubtileFaceIndex × PeriodicSubtileFaceIndex) :=
-- BODY
  match r with
  | 0 => ((⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩), (⟨.I1, 0, 0⟩, ⟨.I2, 0, 0⟩))
  | 1 => ((⟨.A, 0, 0⟩, ⟨.B, 0, 1⟩), (⟨.J1, 0, 0⟩, ⟨.J2, 0, 0⟩))
  | 2 => ((⟨.A, 0, 0⟩, ⟨.B, 1, 1⟩), (⟨.J3, 0, 0⟩, ⟨.J4, 0, 0⟩))
  | 3 => ((⟨.A, 0, 0⟩, ⟨.C, 0, 0⟩), (⟨.I1, 0, 0⟩, ⟨.I3, 0, 0⟩))
  | 4 => ((⟨.A, 0, 0⟩, ⟨.C, 1, 1⟩), (⟨.J3, 0, 0⟩, ⟨.J5, 0, 0⟩))
  | 5 => ((⟨.A, 0, 0⟩, ⟨.D, 0, 0⟩), (⟨.I2, 0, 0⟩, ⟨.J4, 0, 0⟩))
  | 6 => ((⟨.A, 0, 0⟩, ⟨.E, 0, 1⟩), (⟨.J1, 0, 0⟩, ⟨.J5, 0, 0⟩))
  | 7 => ((⟨.A, 0, 0⟩, ⟨.F, 0, 0⟩), (⟨.I3, 0, 0⟩, ⟨.J2, 0, 0⟩))
  | 8 => ((⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩), (⟨.I1, 0, 0⟩, ⟨.J3, -1, -1⟩))
  | 9 => ((⟨.B, 0, 0⟩, ⟨.D, -1, -1⟩), (⟨.J4, -1, -1⟩, ⟨.J6, 0, 0⟩))
  | 10 => ((⟨.B, 0, 0⟩, ⟨.D, 0, 0⟩), (⟨.I2, 0, 0⟩, ⟨.I4, 0, 0⟩))
  | 11 => ((⟨.B, 0, 0⟩, ⟨.E, 0, 0⟩), (⟨.I4, 0, 0⟩, ⟨.J1, 0, -1⟩))
  | 12 => ((⟨.B, 0, 0⟩, ⟨.F, 0, -1⟩), (⟨.J2, 0, -1⟩, ⟨.J6, 0, 0⟩))
  | 13 => ((⟨.C, 0, 0⟩, ⟨.D, -1, 0⟩), (⟨.J7, 0, 0⟩, ⟨.J8, 0, 0⟩))
  | 14 => ((⟨.C, 0, 0⟩, ⟨.E, -1, 0⟩), (⟨.J5, -1, -1⟩, ⟨.J7, 0, 0⟩))
  | 15 => ((⟨.C, 0, 0⟩, ⟨.F, 0, 0⟩), (⟨.I3, 0, 0⟩, ⟨.J8, 0, 0⟩))
  | 16 => ((⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩), (⟨.I4, 0, 0⟩, ⟨.J7, 1, 0⟩))
  | _ => ((⟨.D, 0, 0⟩, ⟨.F, 1, 0⟩), (⟨.J6, 1, 1⟩, ⟨.J8, 1, 0⟩))

end ApollonianSuperharmonic

end
