/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development001

/-!
# Numerical inputs for the Gerver area certificate

This module defines the interval operations, grid, and sums shared by the cap
and niche certificates. The two certificate modules verify the subtotals, and
`Development004` proves the soundness of the interval calculations.

After an intentional change to the numerical inputs, copy the following into
a temporary Lean file and run `lake env lean <file>` from the repository root.
The cap output gives the start index, length, and subtotal of each block. The
niche output gives the row index and subtotal. Update the certificate splits
as well if the grid size or number of rows changes.

```lean
import LeanPool.MovingSofa.Development.Geometry.Foundations.AreaCertificateInputs

open MovingSofa.GerverAreaCert

#eval
  let edgeCount := fanCount - 1
  (List.range ((edgeCount + NN - 1) / NN)).map fun block =>
    let start := block * NN
    let length := min NN (edgeCount - start)
    (start, length, ((List.range' start length).map fun i => (crossZ i).lo).sum)

#eval (List.range 7).map fun row => (row, rowSumZ row)
```
-/

@[expose] public section

namespace MovingSofa.GerverAreaCert

/-- The common denominator of every interval endpoint. -/
def M : ℤ := 10 ^ 30

/-- `⟨lo, hi⟩` denotes the real interval `[lo / M, hi / M]`. -/
structure SI where
  /-- The scaled integer lower endpoint. -/
  lo : ℤ
  /-- The scaled integer upper endpoint. -/
  hi : ℤ
  deriving DecidableEq

namespace SI

/-- Kernel-cheap `min` on `ℤ`. -/
def imin (a b : ℤ) : ℤ := if a ≤ b then a else b
/-- Kernel-cheap `max` on `ℤ`. -/
def imax (a b : ℤ) : ℤ := if a ≤ b then b else a

/-- Outward enclosure of `a / b` for `0 < b`. -/
def ratI (a b : ℤ) : SI := ⟨(a * M) / b, -((-(a * M)) / b)⟩

/-- The exact interval `[0, 0]`. -/
def zero : SI := ⟨0, 0⟩
/-- The exact interval `[1, 1]`. -/
def one : SI := ⟨M, M⟩

/-- Interval addition. -/
def add (x y : SI) : SI := ⟨x.lo + y.lo, x.hi + y.hi⟩
/-- Interval negation. -/
def neg (x : SI) : SI := ⟨-x.hi, -x.lo⟩
/-- Interval subtraction. -/
def sub (x y : SI) : SI := ⟨x.lo - y.hi, x.hi - y.lo⟩

/-- Interval multiplication: the extreme endpoint products, rounded outward. -/
def mul (x y : SI) : SI :=
  let p₁ := x.lo * y.lo
  let p₂ := x.lo * y.hi
  let p₃ := x.hi * y.lo
  let p₄ := x.hi * y.hi
  ⟨imin (imin p₁ p₂) (imin p₃ p₄) / M,
    -((-(imax (imax p₁ p₂) (imax p₃ p₄))) / M)⟩

/-- Division by a positive integer. -/
def divn (x : SI) (b : ℤ) : SI := ⟨x.lo / b, -((-x.hi) / b)⟩

/-- Multiplication by an integer. -/
def imul (k : ℤ) (x : SI) : SI :=
  ⟨imin (k * x.lo) (k * x.hi), imax (k * x.lo) (k * x.hi)⟩

end SI

open SI

/-! ### Certified enclosures of the twenty-two parameters and of `π` -/

/-- Enclosure of the direct parameter `k₁₁`. -/
def k11Z : SI := ⟨-210322422072688751416285718490, -210322422072688751416085718490⟩
/-- Enclosure of the direct parameter `k₁₂`. -/
def k12Z : SI := ⟨249999999999999999999900000000, 250000000000000000000100000000⟩
/-- Enclosure of the direct parameter `k₂₁`. -/
def k21Z : SI := ⟨-919179292771593322274796102890, -919179292771593322274596102890⟩
/-- Enclosure of the direct parameter `k₂₂`. -/
def k22Z : SI := ⟨472406619750805465181660762512, 472406619750805465181860762512⟩
/-- Enclosure of the direct parameter `k₃₁`. -/
def k31Z : SI := ⟨-613763229430251668555014291320, -613763229430251668554814291320⟩
/-- Enclosure of the direct parameter `k₃₂`. -/
def k32Z : SI := ⟨889626479003221860726943050050, 889626479003221860727143050050⟩
/-- Enclosure of the direct parameter `k₄₁`. -/
def k41Z : SI := ⟨-308347166088910014835232479740, -308347166088910014835032479740⟩
/-- Enclosure of the direct parameter `k₄₂`. -/
def k42Z : SI := ⟨472406619750805465181660762512, 472406619750805465181860762512⟩
/-- Enclosure of the direct parameter `k₅₁`. -/
def k51Z : SI := ⟨-1017204036787814585693742864150, -1017204036787814585693542864150⟩
/-- Enclosure of the direct parameter `k₅₂`. -/
def k52Z : SI := ⟨249999999999999999999900000000, 250000000000000000000100000000⟩
/-- Enclosure of the direct parameter `a₁`. -/
def a1Z : SI := ⟨1210322422072688751416085718500, 1210322422072688751416285718500⟩
/-- Enclosure of the direct parameter `a₂`. -/
def a2Z : SI := ⟨-250000000000000000000100000000, -249999999999999999999900000000⟩
/-- Enclosure of the direct parameter `b₁`. -/
def b1Z : SI := ⟨-527624598026784624160603809370, -527624598026784624160403809370⟩
/-- Enclosure of the direct parameter `b₂`. -/
def b2Z : SI := ⟨920258385160637622893605795010, 920258385160637622893805795010⟩
/-- Enclosure of the direct parameter `c₁`. -/
def c1Z : SI := ⟨626045522848465867552229310386, 626045522848465867552429310386⟩
/-- Enclosure of the direct parameter `c₂`. -/
def c2Z : SI := ⟨-944750803946430751679092381250, -944750803946430751678892381250⟩
/-- Enclosure of the direct parameter `d₁`. -/
def d1Z : SI := ⟨1313022761424232933776064655200, 1313022761424232933776264655200⟩
/-- Enclosure of the direct parameter `d₂`. -/
def d2Z : SI := ⟨-525382670414554437202936294305, -525382670414554437202736294305⟩
/-- Enclosure of the direct parameter `e₁`. -/
def e1Z : SI := ⟨1210322422072688751416085718500, 1210322422072688751416285718500⟩
/-- Enclosure of the direct parameter `e₂`. -/
def e2Z : SI := ⟨249999999999999999999900000000, 250000000000000000000100000000⟩
/-- Enclosure of the first stage angle `φ`. -/
def phiZ : SI := ⟨39177364790083641863217874980, 39177364790083641863217875500⟩
/-- Enclosure of the second stage angle `θ`. -/
def thetaZ : SI := ⟨681301509382724894473855754540, 681301509382724894473855759660⟩

/-- The integer enclosure of `π`, from the certified Machin arctangent sums. -/
def piZ : SI := ⟨3141592653589793238462643383279, 3141592653589793238462643383280⟩

/-- The integer enclosure of `π / 2`. -/
def piHalfZ : SI := divn piZ 2

/-! ### Sine and cosine by the degree-41/40 Taylor recurrence -/

/-- `trigIter z t n = (Sₙ, Cₙ, ∑_{k ≤ n} Sₖ, ∑_{k ≤ n} Cₖ)` where `Sₖ` and `Cₖ` enclose the
`k`-th signed sine and cosine Taylor terms and `z` encloses `t ^ 2`. -/
def trigIter (z t : SI) : ℕ → SI × SI × SI × SI
  | 0 => (t, one, t, one)
  | n + 1 =>
    let st := trigIter z t n
    let sterm := neg (divn (mul st.1 z) (((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ))
    let cterm := neg (divn (mul st.2.1 z) (((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ))
    (sterm, cterm, add st.2.2.1 sterm, add st.2.2.2 cterm)

/-- Sine and cosine enclosures of every real number in the argument interval.
Valid for arguments in `[0, 2]`. -/
def trigZ (t : SI) : SI × SI :=
  let st := trigIter (mul t t) t 20
  (⟨st.2.2.1.lo - 1, st.2.2.1.hi + 1⟩, ⟨st.2.2.2.lo - 1, st.2.2.2.hi + 1⟩)

/-! ### Stage endpoints and the uniform grid -/

/-- Number of subintervals per analytic stage. -/
def NN : ℕ := 64

/-- Integer enclosures of the six stage endpoints `0, φ, θ, η, τ, π / 2`, constant past `5`. -/
def endZ : ℕ → SI
  | 0 => zero
  | 1 => phiZ
  | 2 => thetaZ
  | 3 => sub piHalfZ thetaZ
  | 4 => sub piHalfZ phiZ
  | _ => piHalfZ

/-- The `m`-th grid angle, `0 ≤ m ≤ 5 * NN`. -/
def ttZ (m : ℕ) : SI :=
  divn (add (imul ((NN - m % NN : ℕ) : ℤ) (endZ (m / NN)))
    (imul ((m % NN : ℕ) : ℤ) (endZ (m / NN + 1)))) (NN : ℤ)

/-- The analytic branch that the piecewise definitions select at the `m`-th grid angle. -/
def stageOf (m : ℕ) : ℕ := if m % NN = 0 then max 1 (m / NN) else m / NN + 1

/-! ### The five phase formulas and the four contact curves -/

/-- `kind`: `0` the path, `1` `A`, `2` `B`, `3` `C`, `4` `D`. -/
def evalZ (stage : ℕ) (t : SI) (kind : ℕ) : SI × SI :=
  let sc := trigZ t
  let s := sc.1
  let c := sc.2
  let data : SI × SI × SI × SI × SI × SI :=
    if stage = 1 then
      (add (add (mul a1Z c) (mul a2Z s)) (ratI (-1) 1),
        add (add (mul (neg a2Z) c) (mul a1Z s)) (ratI (-1) 2),
        add (add (mul (imul (-2) a1Z) s) (mul (imul 2 a2Z) c)) (ratI 1 2),
        add (add (mul (imul 2 a1Z) c) (mul (imul 2 a2Z) s)) (ratI (-1) 1),
        k11Z, k12Z)
    else if stage = 2 then
      let f := add (add (divn (neg (mul t t)) 4) (mul b1Z t)) b2Z
      (f, add (add (divn t 2) (neg b1Z)) (ratI (-1) 1),
        add (add (ratI 1 1) (imul 2 b1Z)) (neg t),
        add f (ratI 1 2), k21Z, k22Z)
    else if stage = 3 then
      let f := sub c1Z t
      let g := add c2Z t
      (f, g, add (ratI (-1) 1) (neg g), add (ratI 1 1) f, k31Z, k32Z)
    else if stage = 4 then
      let g := add (add (divn (neg (mul t t)) 4) (mul d1Z t)) d2Z
      (add (add (neg (divn t 2)) d1Z) (ratI (-1) 1), g,
        add (neg g) (ratI (-1) 2),
        add (add (imul 2 d1Z) (ratI (-1) 1)) (neg t), k41Z, k42Z)
    else
      (add (add (mul e1Z c) (mul e2Z s)) (ratI (-1) 2),
        add (add (mul (neg e2Z) c) (mul e1Z s)) (ratI (-1) 1),
        add (add (ratI 1 1) (mul (imul (-2) e1Z) s)) (mul (imul 2 e2Z) c),
        add (add (mul (imul 2 e1Z) c) (mul (imul 2 e2Z) s)) (ratI (-1) 2),
        k51Z, k52Z)
  let f := data.1
  let g := data.2.1
  let al := data.2.2.1
  let be := data.2.2.2.1
  let kx := data.2.2.2.2.1
  let ky := data.2.2.2.2.2
  let x0 := add (sub (mul c f) (mul s g)) kx
  let y0 := add (add (mul s f) (mul c g)) ky
  let x1 := if kind = 1 ∨ kind = 2 then sub x0 (mul al s) else x0
  let y1 := if kind = 1 ∨ kind = 2 then add y0 (mul al c) else y0
  let x2 := if kind = 1 then add x1 c else x1
  let y2 := if kind = 1 then add y1 s else y1
  let x3 := if kind = 3 ∨ kind = 4 then sub x2 (mul be c) else x2
  let y3 := if kind = 3 ∨ kind = 4 then sub y2 (mul be s) else y2
  (if kind = 3 then sub x3 s else x3, if kind = 3 then add y3 c else y3)

/-- The contact point at grid index `m`, evaluated on the branch the definitions select. -/
def contactZ (m kind : ℕ) : SI × SI := evalZ (stageOf m) (ttZ m) kind

/-! ### Cap: the ordered support contacts and their fan shoelace sum -/

/-- Number of listed support contacts feeding the fan, excluding the anchor. -/
def fanCount : ℕ := 10 * NN

/-- Contact kind at fan position `i`: `A` for `i ≤ 5 * NN`, otherwise `C`. -/
def fanKind (i : ℕ) : ℕ := if i ≤ 5 * NN then 1 else 3

/-- Grid index at fan position `i`. -/
def fanIdx (i : ℕ) : ℕ := if i ≤ 5 * NN then i else i - 5 * NN

/-- Both coordinates of the contact listed at fan position `i`. -/
def fanZ (i : ℕ) : SI × SI := contactZ (fanIdx i) (fanKind i)

/-- The fan anchor `L = C (π / 2)`. -/
def anchorZ : SI × SI := contactZ (5 * NN) 3

/-- The `i`-th fan determinant over the anchor. -/
def crossZ (i : ℕ) : SI :=
  sub (mul (sub (fanZ i).1 anchorZ.1) (sub (fanZ (i + 1)).2 anchorZ.2))
    (mul (sub (fanZ i).2 anchorZ.2) (sub (fanZ (i + 1)).1 anchorZ.1))

/-- Twice the signed area of the fan polygon: the shoelace sum of the listed contacts over
the anchor. -/
def capDoubledZ : SI :=
  (List.range (fanCount - 1)).foldl (fun acc i => add acc (crossZ i)) zero

/-! ### Niche: the seven roof pieces and their covering rectangles -/

/-- The seven roof pieces as `(kind, stage, traversed forwards?)`. -/
def rowData : ℕ → ℕ × ℕ × Bool
  | 0 => (4, 1, true)
  | 1 => (4, 2, true)
  | 2 => (0, 4, false)
  | 3 => (0, 3, false)
  | 4 => (0, 2, false)
  | 5 => (2, 4, true)
  | _ => (2, 5, true)

/-- Contact kind traced by roof piece `r`. -/
def rowKind (r : ℕ) : ℕ := (rowData r).1
/-- Analytic stage traced by roof piece `r`. -/
def rowStage (r : ℕ) : ℕ := (rowData r).2.1
/-- Whether roof piece `r` is traversed in increasing time. -/
def rowFwd (r : ℕ) : Bool := (rowData r).2.2

/-- Grid index of the left end of the `j`-th subinterval of row `r`. -/
def rowBase (r j : ℕ) : ℕ := (rowStage r - 1) * NN + j

/-- Left horizontal bound of the covering rectangle of `(r, j)`. -/
def rectLoZ (r j : ℕ) : ℤ :=
  if rowFwd r then (contactZ (rowBase r j) (rowKind r)).1.lo
  else (contactZ (rowBase r j + 1) (rowKind r)).1.lo

/-- Right horizontal bound of the covering rectangle of `(r, j)`. -/
def rectHiZ (r j : ℕ) : ℤ :=
  if rowFwd r then (contactZ (rowBase r j + 1) (rowKind r)).1.hi
  else (contactZ (rowBase r j) (rowKind r)).1.hi

/-- Height bound of the covering rectangle of `(r, j)`: the branch evaluation over the
whole subinterval, widened to cover the left endpoint, which sits on the previous branch. -/
def rectHZ (r j : ℕ) : ℤ :=
  imax (evalZ (stageOf (rowBase r j + 1))
      ⟨(ttZ (rowBase r j)).lo, (ttZ (rowBase r j + 1)).hi⟩ (rowKind r)).2.hi
    (contactZ (rowBase r j) (rowKind r)).2.hi

/-- Area of the covering rectangle of `(r, j)`, in units of `1 / M ^ 2`. -/
def rectAreaZ (r j : ℕ) : ℤ :=
  imax 0 (rectHiZ r j - rectLoZ r j) * imax 0 (rectHZ r j)

/-- Total covering area of row `r`, in units of `1 / M ^ 2`. -/
def rowSumZ (r : ℕ) : ℤ := (List.range NN).foldl (fun acc j => acc + rectAreaZ r j) 0

/-- Total covering area of the `7 * NN` rectangles, in units of `1 / M ^ 2`. -/
def nicheSumZ : ℤ := (List.range 7).foldl (fun acc r => acc + rowSumZ r) 0

/-! ### The two decidable numeric conclusions -/

/-- The closed numeric cap check: `2 * 28609 / 10000 ≤ capDoubledZ.lo / M`. -/
def capOK : Bool := 2 * 28609 * M ≤ 10000 * capDoubledZ.lo
/-- The closed numeric niche check: `nicheSumZ / M ^ 2 ≤ 3301 / 5000`. -/
def nicheOK : Bool := 5000 * nicheSumZ ≤ 3301 * M * M

end MovingSofa.GerverAreaCert
