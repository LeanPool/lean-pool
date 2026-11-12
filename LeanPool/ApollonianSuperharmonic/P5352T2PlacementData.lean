/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

-- [TABLET NODE: P5352T2PlacementData]

/-!
# P5352T2PlacementData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $n=k$, let the right displacement and affine coefficient pairs
$(\rho_j,\beta_j)$ be
$$
 ((-k,k+1),(1,-k)),\quad ((-k,-k-1),(-k,0)),\quad ((2k,0),(k-1,k))
$$
for parent indices $j=1,2,3$.  For each $j$, the four triples
$(d_{js},a_{js},r_{js})$, ordered by $s=0,1,2,3$, are
$$
\begin{array}{c|c|c|c|c}
j&s&d_{js}&a_{js}&r_{js}\\\hline
1&0&(0,2k)&(k,-k)&(-k,k+1)\\
1&1&(-k-1,k)&(0,-k-1)&(-k,k+1)\\
1&2&(-1,-1)&(-1,-1)&(k,-k-1)\\
1&3&(k,k-1)&(k-1,0)&(k,-k-1)\\
2&0&(-k-1,k-1)&(0,-k)&(-k,-k-1)\\
2&1&(0,-1)&(0,0)&(-k,-k-1)\\
2&2&(k,k)&(k,0)&(k,k+1)\\
2&3&(-1,2k)&(k,-k)&(k,k+1)\\
3&0&(k,1-k)&(0,k-1)&(2k,0)\\
3&1&(k,k+1)&(k,0)&(2k,0)\\
3&2&(-k,k+1)&(1,-k)&(-2k,0)\\
3&3&(-k,1-k)&(1-k,-1)&(-2k,0).
\end{array}
$$
The Lean index $i$ is $j-1$; the first component of the data is
$(\rho_j,\beta_j)$ and its second component is the four-entry triple table.
-/
def P5352T2PlacementData (k : Nat) (i : Fin 3) :
    (GaussianInt × GaussianInt) × (Fin 4 → GaussianInt × GaussianInt × GaussianInt) :=
-- BODY
  let n : Int := k
  ![((⟨-n, n+1⟩, ⟨1, -n⟩),
      ![(⟨0, 2*n⟩, ⟨n, -n⟩, ⟨-n, n+1⟩),
        (⟨-n-1, n⟩, ⟨0, -n-1⟩, ⟨-n, n+1⟩),
        (⟨-1, -1⟩, ⟨-1, -1⟩, ⟨n, -n-1⟩),
        (⟨n, n-1⟩, ⟨n-1, 0⟩, ⟨n, -n-1⟩)]),
    ((⟨-n, -n-1⟩, ⟨-n, 0⟩),
      ![(⟨-n-1, n-1⟩, ⟨0, -n⟩, ⟨-n, -n-1⟩),
        (⟨0, -1⟩, ⟨0, 0⟩, ⟨-n, -n-1⟩),
        (⟨n, n⟩, ⟨n, 0⟩, ⟨n, n+1⟩),
        (⟨-1, 2*n⟩, ⟨n, -n⟩, ⟨n, n+1⟩)]),
    ((⟨2*n, 0⟩, ⟨n-1, n⟩),
      ![(⟨n, 1-n⟩, ⟨0, n-1⟩, ⟨2*n, 0⟩),
        (⟨n, n+1⟩, ⟨n, 0⟩, ⟨2*n, 0⟩),
        (⟨-n, n+1⟩, ⟨1, -n⟩, ⟨-2*n, 0⟩),
        (⟨-n, 1-n⟩, ⟨1-n, -1⟩, ⟨-2*n, 0⟩)])] i

end ApollonianSuperharmonic

end
