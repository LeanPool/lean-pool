/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Certificates.IntPoly
public import Mathlib.Data.Int.Sqrt
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# The contact-sensitive exclusion checker (computable part)

All data are integer polynomials in one real parameter `x` (the offset `s - lo` of the covering
parameter from the left end of a certificate interval), lowest degree first.  A point `P : IPoint`
denotes the real point `(1/den) • (P.1(x), P.2(x))`.  A `Cap` records a contact constraint: the
real point `p/den` is a full ray endpoint with exit direction `dv` (`strict = false`) or a
forbidden point on a positive ray from a mandatory point (`strict = true`).

`excluded Ps den caps ord a b d fuel depth` decides, for the parameter piece `[a/d, b/d]`,
whether no equilateral triangle of side `< 1` can contain all points of `Ps` while satisfying
the caps and (for `ord = some i`) the non-overfull condition of side owner `i`.  Its structure
mirrors `tools/proto_checker.py` (the untrusted Python reference model):

* `ordinaryExclusion`: segments between mandatory points cross the two boundary rays of
  `vertex i` and give lower bounds whose sum reaches `1`;
* a pair of mandatory points at distance `≥ 1`;
* `fanCheck`: the closed 120-degree cone from `east = (1, 0)` to `rot east = (-1, 1)` (which
  contains one of the three outward edge directions of every triangle) is cut by a list of
  candidate directions into consecutive cones; every node and every cone is certified either by
  a support triple (side `≥ 1`) or by the impossibility of every cap on all three faces;
* on failure the parameter piece is split at a rational knot and both halves are checked.

Only the leaf tests (`nonnegOn`, `posOn`) and the chain structure are used by the soundness
proofs in `CheckerSound.lean`; everything else (choice of nodes, triples, knots) is untrusted
search executed inside the checker.
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

namespace ConwaySoifer.Certificates
open IPoly

/-- A point whose two coordinates are integer polynomials in the interval parameter. -/
abbrev IPoint := IPoly × IPoly
/-- Indices of the three mandatory points used by a support bound. -/
abbrev Triple := Nat × Nat × Nat

/-- An endpoint or forbidden-point constraint, with an exit direction and strictness flag. -/
structure Cap where
  /-- The polynomial contact point. -/
  p : IPoint
  /-- The positive exit direction at the contact point. -/
  dv : IPoint
  /-- Whether the contact point is forbidden rather than a closed endpoint. -/
  strict : Bool
  deriving Repr, DecidableEq

/-! ## Polynomial geometry -/

/-- The determinant polynomial of two polynomial points. -/
def detP (u v : IPoint) : IPoly := sub (mul u.1 v.2) (mul u.2 v.1)
/-- The squared Euclidean norm polynomial in triangular coordinates. -/
def normP (u : IPoint) : IPoly := add (add (mul u.1 u.1) (mul u.1 u.2)) (mul u.2 u.2)
/-- Rotation through 120 degrees in polynomial triangular coordinates. -/
def rotP (u : IPoint) : IPoint := (sub (smul (-1) u.1) u.2, u.1)
/-- Negation of both polynomial coordinates. -/
def negP (u : IPoint) : IPoint := (smul (-1) u.1, smul (-1) u.2)
/-- Coordinatewise subtraction of polynomial points. -/
def psub (p q : IPoint) : IPoint := (sub p.1 q.1, sub p.2 q.2)
/-- Coordinatewise addition of polynomial points. -/
def padd (p q : IPoint) : IPoint := (add p.1 q.1, add p.2 q.2)
/-- The constant east direction in polynomial coordinates. -/
def eastP : IPoint := ([1], [0])
/-- The constant direction obtained by rotating east through 120 degrees. -/
def rotEastP : IPoint := ([-1], [1])

/-- The sum of support determinants for three successive orientation normals. -/
def supportNumP (u P₀ P₁ P₂ : IPoint) : IPoly :=
  add (add (detP u P₀) (detP (rotP u) P₁)) (detP (rotP (rotP u)) P₂)

/-- `N² - den² |u|²`: nonnegative together with `N ≥ 0` iff the side bound is at least one. -/
def gapP (den : Int) (u P₀ P₁ P₂ : IPoint) : IPoly :=
  let n := supportNumP u P₀ P₁ P₂
  sub (mul n n) (smul (den * den) (normP u))

/-- A structural, optional lookup used by the verified support checker. -/
def nth {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => nth l n

/-! ## Trusted leaf tests -/

/-- Check a supplied support triple over the complete rational parameter interval. -/
def supportOK (Ps : List IPoint) (den : Int) (u : IPoint) (T : Triple) (a b d : Int)
    (fuel : Nat) : Bool :=
  match nth Ps T.1, nth Ps T.2.1, nth Ps T.2.2 with
  | some P₀, some P₁, some P₂ =>
      nonnegOn (supportNumP u P₀ P₁ P₂) a b d fuel && nonnegOn (gapP den u P₀ P₁ P₂) a b d fuel
  | _, _, _ => false

/-- Face `e` cannot be the contact face of cap `c` anywhere on the piece. -/
def badFace (Ps : List IPoint) (e : IPoint) (c : Cap) (a b d : Int) (fuel : Nat) : Bool :=
  nonnegOn (smul (-1) (detP e c.dv)) a b d fuel ||
    Ps.any fun q =>
      let f := smul (-1) (detP e (psub c.p q))
      if c.strict then nonnegOn f a b d fuel else posOn f a b d fuel

/-- Faces `a • eu + b • ev` (`a, b > 0`) cannot be the contact face of cap `c`. -/
def badFaceCone (Ps : List IPoint) (eu ev : IPoint) (c : Cap) (a b d : Int) (fuel : Nat) :
    Bool :=
  (nonnegOn (smul (-1) (detP eu c.dv)) a b d fuel &&
      nonnegOn (smul (-1) (detP ev c.dv)) a b d fuel) ||
    Ps.any fun q =>
      let fu := smul (-1) (detP eu (psub c.p q))
      let fv := smul (-1) (detP ev (psub c.p q))
      nonnegOn fu a b d fuel && nonnegOn fv a b d fuel &&
        (c.strict || posOn (add (mul fu fu) (mul fv fv)) a b d fuel)

/-- Check that one cap rejects all three contact faces at one orientation direction. -/
def capNode (Ps : List IPoint) (caps : List Cap) (u : IPoint) (a b d : Int) (fuel : Nat) : Bool :=
  caps.any fun c =>
    badFace Ps u c a b d fuel && badFace Ps (rotP u) c a b d fuel &&
      badFace Ps (rotP (rotP u)) c a b d fuel

/-- Check that one cap rejects all contact faces throughout a positive orientation cone. -/
def capCone (Ps : List IPoint) (caps : List Cap) (u v : IPoint) (a b d : Int) (fuel : Nat) :
    Bool :=
  caps.any fun c =>
    badFaceCone Ps u v c a b d fuel && badFaceCone Ps (rotP u) (rotP v) c a b d fuel &&
      badFaceCone Ps (rotP (rotP u)) (rotP (rotP v)) c a b d fuel

/-! ## Untrusted search helpers -/

/-- The maximum coefficient-list length among all polynomial point coordinates. -/
def maxLen : List IPoint → Nat
  | [] => 0
  | P :: Ps => max (max P.1.length P.2.length) (maxLen Ps)

/-- Track the first largest value while scanning values with their indices. -/
def argmaxAux : List Int → Nat → Nat → Int → Nat
  | [], _, best, _ => best
  | v :: vs, i, best, bv =>
    if bv < v then argmaxAux vs (i + 1) i v else argmaxAux vs (i + 1) best bv

/-- The first index attaining the largest value, or zero for an empty list. -/
def argmax : List Int → Nat
  | [] => 0
  | v :: vs => argmaxAux vs 1 0 v

/-- Select a point with the largest exact support determinant at a rational parameter. -/
def maxIndex (Ps : List IPoint) (l : IPoint) (num den : Int) (N2 : Nat) : Nat :=
  argmax (Ps.map fun P => evalScaledN (detP l P) num den N2)

/-- The maximising triple for direction `u` at the parameter `num/den`. -/
def tripleAt (Ps : List IPoint) (N : Nat) (u : IPoint) (num den : Int) : Triple :=
  let N2 := N + N
  (maxIndex Ps u num den N2, maxIndex Ps (rotP u) num den N2, maxIndex Ps (rotP (rotP u)) num den
      N2)

/-- Try support triples selected at the midpoint and endpoints of one interval. -/
def supportNode (Ps : List IPoint) (den : Int) (N : Nat) (u : IPoint) (a b d : Int)
    (fuel : Nat) : Bool :=
  supportOK Ps den u (tripleAt Ps N u (a + b) (2 * d)) a b d fuel ||
    supportOK Ps den u (tripleAt Ps N u a d) a b d fuel ||
    supportOK Ps den u (tripleAt Ps N u b d) a b d fuel

/-- Try one common support triple at both endpoints of an orientation cone. -/
def supportCone (Ps : List IPoint) (den : Int) (N : Nat) (u v : IPoint) (a b d : Int)
    (fuel : Nat) : Bool :=
  let w := padd u v
  let tries : List Triple :=
    [tripleAt Ps N w (a + b) (2 * d), tripleAt Ps N w a d, tripleAt Ps N w b d,
     tripleAt Ps N u (a + b) (2 * d), tripleAt Ps N u a d, tripleAt Ps N u b d,
     tripleAt Ps N v (a + b) (2 * d), tripleAt Ps N v a d, tripleAt Ps N v b d]
  tries.any fun T => supportOK Ps den u T a b d fuel && supportOK Ps den v T a b d fuel

/-- Reject a direction using either a support bound or a cap. -/
def nodeCheck (Ps : List IPoint) (den : Int) (caps : List Cap) (N : Nat) (u : IPoint)
    (a b d : Int) (fuel : Nat) : Bool :=
  supportNode Ps den N u a b d fuel || capNode Ps caps u a b d fuel

/-- Reject a positive orientation cone using a common support triple or a cap. -/
def coneCheck (Ps : List IPoint) (den : Int) (caps : List Cap) (N : Nat) (u v : IPoint)
    (a b d : Int) (fuel : Nat) : Bool :=
  supportCone Ps den N u v a b d fuel || capCone Ps caps u v a b d fuel

/-- A node must be nonzero and lie in the closed cone from `east` to `rot east` on the piece. -/
def nodeCond (u : IPoint) (a b d : Int) (fuel : Nat) : Bool :=
  nonnegOn (detP eastP u) a b d fuel && nonnegOn (detP u rotEastP) a b d fuel &&
    posOn (normP u) a b d fuel

/-- `nodesOK … u ns`: the consecutive cones `(u, v₁), (v₁, v₂), …` up to `rot east` all pass,
consecutive determinants are nonnegative on the piece, and every intermediate node satisfies
`nodeCond`. -/
def nodesOK (Ps : List IPoint) (den : Int) (caps : List Cap) (N : Nat) (a b d : Int)
    (fuel : Nat) : IPoint → List IPoint → Bool
  | _, [] => false
  | u, [v] =>
      nodeCheck Ps den caps N u a b d fuel && coneCheck Ps den caps N u v a b d fuel &&
        nonnegOn (detP u v) a b d fuel && decide (v = rotEastP) &&
        nodeCheck Ps den caps N v a b d fuel
  | u, v :: w :: rest =>
      nodeCheck Ps den caps N u a b d fuel && coneCheck Ps den caps N u v a b d fuel &&
        nonnegOn (detP u v) a b d fuel && nodeCond v a b d fuel &&
        nodesOK Ps den caps N a b d fuel v (w :: rest)

/-! ### Candidate nodes (untrusted) -/

/-- The six rotations and opposite rays generated by a polynomial direction. -/
def sixDirs (e : IPoint) : List IPoint :=
  [e, rotP e, rotP (rotP e), negP e, rotP (negP e), rotP (rotP (negP e))]

/-- Differences of every unordered pair of mandatory polynomial points. -/
def pairDirs : List IPoint → List IPoint
  | [] => []
  | P :: Ps => (Ps.map fun Q => psub Q P) ++ pairDirs Ps

/-- Candidate fan directions obtained from point differences and cap constraints. -/
def candidateDirs (Ps : List IPoint) (caps : List Cap) : List IPoint :=
  let base := pairDirs Ps ++ (caps.flatMap fun c => (Ps.map fun q => psub c.p q) ++ [c.dv])
  base.flatMap sixDirs

/-- A polynomial direction paired with its exact integer evaluation. -/
abbrev RayV := IPoint × (Int × Int)

/-- Pair a polynomial ray with its scaled rational-coordinate evaluation. -/
def evalRay (num den : Int) (N : Nat) (r : IPoint) : RayV :=
  (r, (evalScaledN r.1 num den N, evalScaledN r.2 num den N))

/-- The determinant of two integer coordinate vectors. -/
def det2 (u v : Int × Int) : Int := u.1 * v.2 - u.2 * v.1

/-- Fuel-bounded merge of two lists using a Boolean ordering test. -/
def merge {α : Type} (lt : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
      if lt y x then y :: merge lt fuel (x :: xs) ys else x :: merge lt fuel xs (y :: ys)

/-- Fuel-bounded merge sort used only to propose certificate data. -/
def msort {α : Type} (lt : α → α → Bool) : Nat → List α → List α
  | 0, xs => xs
  | fuel + 1, xs =>
      match xs with
      | [] => []
      | [x] => [x]
      | _ =>
          let n := xs.length / 2
          merge lt xs.length (msort lt fuel (xs.take n)) (msort lt fuel (xs.drop n))

/-- Remove consecutive parallel evaluated directions. -/
def dedupe (prev : Int × Int) : List RayV → List RayV
  | [] => []
  | rv :: rest => if det2 prev rv.2 = 0 then dedupe prev rest else rv :: dedupe rv.2 rest

/-- Keep a node only when the trusted conditions with the previously kept node hold. -/
def robustFilter (a b d : Int) (fuel : Nat) : IPoint → List IPoint → List IPoint
  | _, [] => []
  | last, n :: rest =>
      if nonnegOn (detP last n) a b d fuel && nodeCond n a b d fuel then
        n :: robustFilter a b d fuel n rest
      else robustFilter a b d fuel last rest

/-- Propose ordered fan nodes from exact midpoint evaluations and interval tests. -/
def quadNodes (Ps : List IPoint) (caps : List Cap) (N : Nat) (a b d : Int) (fuel : Nat) :
    List IPoint :=
  let num := a + b
  let den := 2 * d
  let evald := (candidateDirs Ps caps).map (evalRay num den N)
  let inside := evald.filter fun rv => decide (0 < rv.2.2) && decide (0 < rv.2.1 + rv.2.2)
  let sorted := msort (fun u v => decide (0 < det2 u.2 v.2)) (inside.length + 1) inside
  let kept := dedupe (1, 0) sorted
  robustFilter a b d fuel eastP (kept.map Prod.fst)

/-- Check the proposed fan across the closed 120-degree orientation arc. -/
def fanCheck (Ps : List IPoint) (den : Int) (caps : List Cap) (a b d : Int) (fuel : Nat) :
    Bool :=
  let N := maxLen Ps
  nodesOK Ps den caps N a b d fuel eastP (quadNodes Ps caps N a b d fuel ++ [rotEastP])

/-! ### Non-overfull owners -/

/-- `den • vertex i`. -/
def vertexP (den : Int) : Fin 6 → IPoint :=
  ![([den], [0]), ([0], [den]), ([-den], [den]), ([-den], [0]), ([0], [-den]), ([den], [-den])]

/-- The segment `[A, B]` crosses the ray from `v` in direction `dvec` (all conditions on the
piece): `dd > 0`, `0 ≤ mu ≤ dd` (crossing parameter inside the segment) and `nm ≥ 0` (nonnegative
ray parameter `nm/dd`). -/
def crossesRay (v dvec A B : IPoint) (a b d : Int) (fuel : Nat) : Bool :=
  let e := psub B A
  let dd := detP e dvec
  let mu := detP (psub v A) dvec
  let nm := detP e (psub A v)
  posOn dd a b d fuel && nonnegOn mu a b d fuel && nonnegOn (sub dd mu) a b d fuel &&
    nonnegOn nm a b d fuel

/-- Candidate crossing pairs (untrusted pruning; everything is re-verified in
`rayBoundsSum`). -/
def rayBounds (Ps : List IPoint) (v dvec : IPoint) (a b d : Int) (fuel : Nat) :
    List (IPoint × IPoint) :=
  (Ps.flatMap fun A => Ps.map fun B => (A, B)).filter fun AB => crossesRay v dvec AB.1 AB.2 a b d
      fuel

/-- Trusted: two crossing pairs (points of `Ps`) whose lower bounds `nm₁/dd₁ + nm₂/dd₂` reach
`1` on the whole piece. -/
def rayBoundsSum (Ps : List IPoint) (v dv₁ dv₂ : IPoint) (L R : List (IPoint × IPoint))
    (a b d : Int) (fuel : Nat) : Bool :=
  L.any fun x => R.any fun y =>
    decide (x.1 ∈ Ps) && decide (x.2 ∈ Ps) && decide (y.1 ∈ Ps) && decide (y.2 ∈ Ps) &&
    crossesRay v dv₁ x.1 x.2 a b d fuel && crossesRay v dv₂ y.1 y.2 a b d fuel &&
    (let nm₁ := detP (psub x.2 x.1) (psub x.1 v)
     let dd₁ := detP (psub x.2 x.1) dv₁
     let nm₂ := detP (psub y.2 y.1) (psub y.1 v)
     let dd₂ := detP (psub y.2 y.1) dv₂
     nonnegOn (sub (add (mul nm₁ dd₂) (mul nm₂ dd₁)) (mul dd₁ dd₂)) a b d fuel)

/-- Best four pairs by the value of the bound at the midpoint (untrusted pruning). -/
def bestBounds (v dvec : IPoint) (bs : List (IPoint × IPoint)) (num dd : Int) (N2 : Nat) :
    List (IPoint × IPoint) :=
  let key : IPoint × IPoint → Int × Int := fun x =>
    let e := psub x.2 x.1
    (evalScaledN (detP e (psub x.1 v)) num dd N2, evalScaledN (detP e dvec) num dd N2)
  let lt : IPoint × IPoint → IPoint × IPoint → Bool := fun x y =>
    let kx := key x
    let ky := key y
    decide (ky.1 * kx.2 < kx.1 * ky.2)
  (msort lt (bs.length + 1) bs).take 4

/-- Check an exclusion using the side-owner non-overfull condition. -/
def ordinaryExclusion (Ps : List IPoint) (den : Int) (i : Fin 6) (a b d : Int) (fuel : Nat) :
    Bool :=
  let v := vertexP den i
  let dv₁ := psub (vertexP den (i + 5)) v
  let dv₂ := psub (vertexP den (i + 1)) v
  let N2 := maxLen Ps + maxLen Ps
  let L := rayBounds Ps v dv₁ a b d fuel
  let R := rayBounds Ps v dv₂ a b d fuel
  rayBoundsSum Ps v dv₁ dv₂ (bestBounds v dv₁ L (a + b) (2 * d) N2)
    (bestBounds v dv₂ R (a + b) (2 * d) N2) a b d fuel

/-- Apply the non-overfull exclusion when an owner flag is present. -/
def ordinaryCheck (Ps : List IPoint) (den : Int) (ord : Option (Fin 6)) (a b d : Int)
    (fuel : Nat) : Bool :=
  match ord with
  | none => false
  | some i => ordinaryExclusion Ps den i a b d fuel

/-! ### Diameter -/

/-- Search for a pair whose certified separation excludes a subunit triangle. -/
def diamCheck (Ps : List IPoint) (den : Int) (a b d : Int) (fuel : Nat) : Bool :=
  (pairDirs Ps).any fun e => nonnegOn (sub (normP e) [den * den]) a b d fuel

/-! ### Rational split points (untrusted) -/

/-- A rational as a pair with positive denominator. -/
def mkIRat (n m : Int) : IRat := if m < 0 then (-n, -m) else (n, m)

/-- Remove trailing zero coefficients from an integer polynomial. -/
def trimP : IPoly → IPoly
  | [] => []
  | c :: p =>
      match trimP p with
      | [] => if c = 0 then [] else [c]
      | q => c :: q

/-- Differentiate successive coefficients starting at a specified degree. -/
def derivAux : Nat → IPoly → IPoly
  | _, [] => []
  | k, c :: p => (k : Int) * c :: derivAux (k + 1) p

/-- Differentiate an integer coefficient list. -/
def derivP : IPoly → IPoly
  | [] => []
  | _ :: p => derivAux 1 p

/-- Remove trailing zeros from a rational coefficient list. -/
def qtrim : List Rat → List Rat
  | [] => []
  | c :: p =>
      match qtrim p with
      | [] => if c = 0 then [] else [c]
      | q => c :: q

/-- One Euclidean step `a - c x ^ k b` where `c = lead a / lead b`, `k = deg a - deg b`. -/
def qstep (a b : List Rat) : List Rat :=
  match a.getLast?, b.getLast? with
  | some la, some lb =>
      let c := la / lb
      let k := a.length - b.length
      let sh : List Rat := List.replicate k 0 ++ b.map (fun z => c * z)
      qtrim ((List.zipWith (fun x y => x - y) a sh).take (a.length - 1))
  | _, _ => []

/-- Fuel-bounded polynomial remainder calculation over rational coefficients. -/
def qremAux : Nat → List Rat → List Rat → List Rat
  | 0, a, _ => a
  | k + 1, a, b => if a.length < b.length then a else qremAux k (qstep a b) b

/-- A proposed rational polynomial remainder, with a degree-based fuel bound. -/
def qrem (a b : List Rat) : List Rat := qtrim (qremAux (a.length + 1) (qtrim a) (qtrim b))

/-- Fuel-bounded rational polynomial Euclidean algorithm used by the untrusted search. -/
def qgcd : Nat → List Rat → List Rat → List Rat
  | 0, a, _ => a
  | k + 1, a, b =>
      match qtrim b with
      | [] => qtrim a
      | b' => qgcd k b' (qrem a b')

/-- All rational roots of a polynomial of degree at most two (integer square root test), and
the rational roots of `gcd(p, p')` for higher degrees (double roots).  Fuel-bounded. -/
def ratRootsAux : Nat → IPoly → List IRat
  | 0, _ => []
  | k + 1, p =>
      match trimP p with
      | [] => []
      | [_] => []
      | [c, b] => [mkIRat (-c) b]
      | [c, b, a] =>
          let disc := b * b - 4 * a * c
          if disc < 0 then []
          else
            let z := Int.sqrt disc
            if z * z = disc then [mkIRat (-b - z) (2 * a), mkIRat (-b + z) (2 * a)] else []
      | p' =>
          let g := qgcd (p'.length + 1) (p'.map (fun c => (c : Rat)))
            ((derivP p').map (fun c => (c : Rat)))
          if g.length ≤ 1 then []
          else
            let m : Int := g.foldl (fun acc q => acc * (q.den : Int) / Int.gcd acc q.den) 1
            ratRootsAux k (g.map fun q => (q * (m : Rat)).num)

/-- Propose rational roots using a degree-based recursion budget. -/
def ratRoots (p : IPoly) : List IRat := ratRootsAux p.length p

/-- Rational comparison `n₁/m₁ < n₂/m₂` for positive denominators. -/
def iratLt (x y : IRat) : Bool := decide (x.1 * y.2 < y.1 * x.2)

/-- Compare rational pairs by cross multiplication; denominators are assumed positive. -/
def iratEq (x y : IRat) : Bool := decide (x.1 * y.2 = y.1 * x.2)

/-- Roots strictly inside `(a/d, b/d)`. -/
def rootsInside (p : IPoly) (a b d : Int) : List IRat :=
  (ratRoots p).filter fun r => iratLt (a, d) r && iratLt r (b, d)

/-- Keep the first occurrence of each cross-multiplication equivalence class. -/
def dedupeRats (l : List IRat) : List IRat :=
  l.foldl (fun acc r => if acc.any (iratEq r) then acc else acc ++ [r]) []

/-- Candidate knots: switch parameters of support values, sign changes of contact polynomials
and crossings of candidate directions. -/
def knots (Ps : List IPoint) (caps : List Cap) (a b d : Int) : List IRat :=
  let base := pairDirs Ps ++ (caps.flatMap fun c => (Ps.map fun q => psub c.p q) ++ [c.dv])
  let pd := pairDirs Ps
  let polys : List IPoly :=
    (base.flatMap fun e =>
      [e, rotP e, rotP (rotP e)].flatMap fun f =>
        (pd.map fun w => detP f w) ++
          (caps.flatMap fun c => detP f c.dv :: Ps.map fun q => detP f (psub c.p q))) ++
    (base.flatMap fun e => base.flatMap fun f => [detP e f, detP e (rotP f), detP e (rotP (rotP
        f))])
  dedupeRats (polys.flatMap fun pl => rootsInside pl a b d)

/-- Split point: the knot closest to the midpoint, else the midpoint. -/
def splitPoint (Ps : List IPoint) (caps : List Cap) (a b d : Int) : IRat :=
  let mid : IRat := (a + b, 2 * d)
  let ks := knots Ps caps a b d
  let dist : IRat → Int × Int := fun r =>
    let n := r.1 * mid.2 - mid.1 * r.2
    (if n < 0 then -n else n, r.2 * mid.2)
  let better : IRat → IRat → Bool := fun r s =>
    let dr := dist r
    let ds := dist s
    decide (dr.1 * ds.2 < ds.1 * dr.2)
  match ks with
  | [] => mid
  | k :: rest => rest.foldl (fun best r => if better r best then r else best) k

/-! ## The exclusion decision -/

/-- Split `[a/d, b/d]` at `n/m` (with `a/d < n/m < b/d`) into two pieces. -/
def splitPieces (a b d : Int) (r : IRat) : List (Int × Int × Int) := piecesOf a b d [r]

/-- Try geometric exclusions and recursively proposed rational interval splits. -/
def excluded (Ps : List IPoint) (den : Int) (caps : List Cap) (ord : Option (Fin 6))
    (fuel : Nat) : Nat → Int → Int → Int → Bool
  | depth, a, b, d =>
      ordinaryCheck Ps den ord a b d fuel || diamCheck Ps den a b d fuel ||
        fanCheck Ps den caps a b d fuel ||
        (match depth with
         | 0 => false
         | depth' + 1 =>
             chainCheck (fun a' b' d' => excluded Ps den caps ord fuel depth' a' b' d') (b, d) (a,
                 d)
               (splitPieces a b d (splitPoint Ps caps a b d)))

/-! ## Point sets: the ordered-field thinning of the reference verifier -/

/-- The sign of the first nonzero coefficient, or zero for a zero coefficient list. -/
def firstSign : IPoly → Int
  | [] => 0
  | c :: p => if 0 < c then 1 else if c < 0 then -1 else firstSign p

/-- Compare polynomial points lexicographically by the first nonzero coefficient difference. -/
def cmpPt (x y : IPoint) : Int :=
  let s := firstSign (sub x.1 y.1)
  if s ≠ 0 then s else firstSign (sub x.2 y.2)

/-- Sort polynomial points using their coefficient comparison. -/
def sortPts (Ps : List IPoint) : List IPoint :=
  msort (fun x y => decide (cmpPt x y < 0)) (Ps.length + 1) Ps

/-- Retain the first point in each coefficient-comparison equivalence class. -/
def dedupePts (l : List IPoint) : List IPoint :=
  l.foldl (fun acc P => if acc.any (fun Q => decide (cmpPt P Q = 0)) then acc else acc ++ [P]) []

/-- Stack scan with a structural recursion budget. Each transition decreases
`out.length + 2 * rest.length`, so that measure suffices for the complete scan. -/
def halfHullAux : Nat → List IPoint → List IPoint → List IPoint
  | 0, out, _ => out
  | _ + 1, out, [] => out
  | fuel + 1, out, q :: rest =>
      match out with
      | o₁ :: o₂ :: out' =>
          if firstSign (detP (psub o₁ o₂) (psub q o₁)) ≤ 0 then
            halfHullAux fuel (o₂ :: out') (q :: rest)
          else halfHullAux fuel (q :: o₁ :: o₂ :: out') rest
      | _ => halfHullAux fuel (q :: out) rest

/-- Complete half-hull scan; the budget bounds stack transitions, not input size. -/
def halfHull (out rest : List IPoint) : List IPoint :=
  halfHullAux (out.length + 2 * rest.length) out rest

/-- The subset selection of `exact_polynomials.thin_hull` (a weakening; never a hull claim). -/
def thinHull (Ps : List IPoint) : List IPoint :=
  let P := dedupePts (sortPts Ps)
  if P.length ≤ 2 then P
  else
    let lower := (halfHull [] P).reverse
    let upper := (halfHull [] P.reverse).reverse
    lower.dropLast ++ upper.dropLast

/-! ## Certificate replay -/

/-- One forced step: point `q` (scaled by the common denominator) is forced into owner `owner`. -/
structure Step where
  /-- The owner forced to contain the new point. -/
  owner : Fin 10
  /-- The newly assigned polynomial point. -/
  q : IPoint
  deriving Repr

/-- The replay state: mandatory point lists, caps and ordinary flags per owner. -/
structure Model where
  /-- The mandatory polynomial points for each owner. -/
  B : Fin 10 → List IPoint
  /-- The contact constraints for each owner. -/
  caps : Fin 10 → List Cap
  /-- Optional non-overfull side-owner indices. -/
  ord : Fin 10 → Option (Fin 6)

/-- `q` lies in the target triangle `a ≤ 1, b ≤ 1, -1 ≤ a + b` (scaled by `den`). -/
def inTarget (q : IPoint) (den a b d : Int) (fuel : Nat) : Bool :=
  nonnegOn (sub [den] q.1) a b d fuel && nonnegOn (sub [den] q.2) a b d fuel &&
    nonnegOn (add [den] (add q.1 q.2)) a b d fuel

/-- Check target membership and exclusion from every owner except the proposed owner. -/
def stepCheck (M : Model) (den : Int) (st : Step) (a b d : Int) (fuel depth : Nat) : Bool :=
  inTarget st.q den a b d fuel &&
    (List.finRange 10).all fun j =>
      j = st.owner ||
        excluded (M.B j ++ [st.q]) den (M.caps j) (M.ord j) fuel depth a b d

/-- The thinned list, filtered to elements of the original list (so that membership is a
syntactic fact and no property of the hull heuristic is needed). -/
def thinHullChecked (L : List IPoint) : List IPoint :=
  (thinHull L).filter fun P => decide (P ∈ L)

/-- Insert a forced point into its owner set and retain only a checked hull subset. -/
def Model.insert (M : Model) (st : Step) : Model :=
  { M with B := fun j => if j = st.owner then thinHullChecked (M.B j ++ [st.q]) else M.B j }

/-- Check the forced assignments in order and a final owner contradiction. -/
def replay (M : Model) (den : Int) (a b d : Int) (fuel depth : Nat) : List Step → Fin 10 → Bool
  | [], last => excluded (M.B last) den (M.caps last) (M.ord last) fuel depth a b d
  | st :: rest, last =>
      stepCheck M den st a b d fuel depth && replay (M.insert st) den a b d fuel depth rest last

end ConwaySoifer.Certificates
