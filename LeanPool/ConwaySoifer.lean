/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Theorem
import Mathlib.Tactic

/-!
# Conway–Soifer covering conjecture for n = 3

Source: doi:10.5281/zenodo.22712658, url:https://github.com/AnanasClassic/conway-soifer-n3-lean/tree/b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6
Authors: Vladislav Kuznetsov
Status: verified
Main declarations: `ConwaySoifer.ten_triangle_cover_lower_bound`
Tags: discrete-geometry, triangle-covering, conway-soifer, bernstein-polynomials
MSC: 52C15, 51M16
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

/-!
# Certificate regeneration

The immutable public input is AnanasClassic/conway-soifer-n3-lean commit
b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (MIT; the Lean data match public release v1.0.0). Its
Simplified/Certificates/Data, Checkpoints, Steps and Checked modules retain all 100
certificates, 3,188 assignments and original orientation directions. Its data/certificates.json
is only a build inventory. The historical search/export pipeline is not public; this recipe
reproduces the retained certificate values and arithmetic witnesses, not that unpublished search
or a new proof for changed geometry.

This port uses Lean v4.35.0-rc3 and Mathlib c55e6e786f49471c72fbddbec5415808896aec1e. Keep
lean-toolchain and lake-manifest.json pinned; do not run lake update. The relevant arithmetic is
in Certificates/Checker, Model, IntPoly, Witness and WitnessedArithmetic. Integer point
coefficients are in increasing powers of x, scaled by the positive CertData.den; x is the offset
from CertData.lo. Preserve the rational endpoints and denominators exactly.

1. Build the pinned import with lake build LeanPool.ConwaySoifer.Imports. Save the complete
program below as RegenerateConway.lean outside the checkout (on this VM, under
$CODEX_SCRATCH_ROOT). From the repository root run lake env lean -j 1 --run
"$CODEX_SCRATCH_ROOT/RegenerateConway.lean" and retain its output. This untrusted executable
emits the complete rational data, every initial/intermediate/final state, and one example
diameter witness.

2. State generation is deterministic: initModel C.case C.lo C.hi C.den, followed by Model.insert
along C.steps. Model.insert uses thinHullChecked; do not substitute an unchecked hull heuristic
or round coordinates. Emit all ten owners' point lists, caps and optional flags. Sharing
repeated exact points/lists and copying caps/flags is a presentation change only. Emit stepK
from the corresponding C.steps element; keep all trace steps in order. Compare every generated
state field with the retained checkpoint values.

3. For every Steps/Checked exclusion, call emitProposal with its actual points, caps, flag,
positive denominator, fuel and integer interval a/b/d. The example uses
Sint100000110000.excluded0_1. For all 100 certificates, replace the two Data/Checkpoints
imports, opened certificate namespace and C value, then batch the actual exclusion contexts from
that certificate. For forced steps the points are modelK.B j ++ [stepK.q], for each of the other
nine owners; the terminal rejection uses modelLast.B j. Use the bounds of each split branch
rather than the outer interval.

4. Diameter proposals enumerate i < j in list order. Node support candidates use tripleAt at the
midpoint and both rational endpoints; cone candidates use u+v, u and v and require the same
triple at both endpoints. A failed triple search may use the cap checker. Fan directions come
from the retained .fan list or fanDirections of a retained .witnessedFan; recurse through every
boundary and terminate at rotEastP. The program emits explicit .pair/.witnessedFan/.split terms.
It preserves .ordinary checks and never treats native output as a proof. A failed check or
missing witness stops regeneration; changed geometry may require a genuinely new search, not an
assumption or a skipped transition.

5. Insert proposals into ExclusionHint.sound calls and require the existing decide +kernel
acceptance proofs, initialization, all owner exclusions, Model.insert equalities, backward
replay and interval coverage. Share long fan tails from the right in blocks of 24 next nodes
(fanKOwnerJPartN); preserve their expanded value. Rebuild the complete aggregate, regenerate
indexes with lake exe mk_all --module, and run Mathlib linters, style and repository
quality/trust checks. No option override, extra axiom or native proof result is permitted. The
acceptance proofs, not the producer, establish correctness.

The program was executed on this port: all 37 states of Sint100000110000 match the retained
checkpoint fields; its diameter witness is .pair 0 3. Supplying the pinned original excluded0_0
fan also reproduces its long explicit support witness. These are reproduction tests, separate
from the kernel proofs that validate every certificate.

```lean
module
public import LeanPool.ConwaySoifer.Simplified.Certificates.Data.Sint100000110000
public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint100000110000
public import LeanPool.ConwaySoifer.Certificates.Witness
import all LeanPool.ConwaySoifer.Simplified.Certificates.Data.Sint100000110000
import all LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint100000110000
import all LeanPool.ConwaySoifer.Certificates.Checker
import all LeanPool.ConwaySoifer.Certificates.Model
import all LeanPool.ConwaySoifer.Certificates.IntPoly
import all LeanPool.ConwaySoifer.Certificates.Witness

@[expose] public section

open ConwaySoifer.Certificates ConwaySoifer.Certificates.IPoly

def quotePoint (p : IPoint) : String :=
  let coefficients (xs : List Int) := "[" ++ String.intercalate ", " (xs.map toString) ++ "]"
  "(" ++ coefficients p.1 ++ ", " ++ coefficients p.2 ++ ")"

def quoteBound : Option Triple → String
  | none => "none"
  | some (i, j, k) => s!"(some ({i}, {j}, {k}))"

def proposeNode (Ps : List IPoint) (den : Int) (caps : List Cap) (u : IPoint)
    (a b d : Int) (fuel : Nat) : Option (Option Triple) :=
  let N := maxLen Ps
  let candidates := [tripleAt Ps N u (a + b) (2 * d), tripleAt Ps N u a d,
    tripleAt Ps N u b d]
  match candidates.find? (fun T => supportOK Ps den u T a b d fuel) with
  | some T => some (some T)
  | none => if capNode Ps caps u a b d fuel then some none else none

def proposeCone (Ps : List IPoint) (den : Int) (caps : List Cap) (u v : IPoint)
    (a b d : Int) (fuel : Nat) : Option (Option Triple) :=
  let N := maxLen Ps
  let directions := [padd u v, u, v]
  let candidates := directions.flatMap fun e =>
    [tripleAt Ps N e (a + b) (2 * d), tripleAt Ps N e a d, tripleAt Ps N e b d]
  match candidates.find? (fun T =>
      supportOK Ps den u T a b d fuel && supportOK Ps den v T a b d fuel) with
  | some T => some (some T)
  | none => if capCone Ps caps u v a b d fuel then some none else none

def proposeFan (Ps : List IPoint) (den : Int) (caps : List Cap)
    (a b d : Int) (fuel : Nat) : IPoint → List IPoint → Option String
  | _, [] => none
  | u, [v] => do
      if v != rotEastP then none else do
        let nu ← proposeNode Ps den caps u a b d fuel
        let nv ← proposeNode Ps den caps v a b d fuel
        let cone ← proposeCone Ps den caps u v a b d fuel
        pure s!"(.terminal {quoteBound nu} {quoteBound nv} {quoteBound cone})"
  | u, v :: w :: rest => do
      let node ← proposeNode Ps den caps u a b d fuel
      let cone ← proposeCone Ps den caps u v a b d fuel
      let tail ← proposeFan Ps den caps a b d fuel v (w :: rest)
      pure s!"(.next {quotePoint v} {quoteBound node} {quoteBound cone} {tail})"

def proposePair (Ps : List IPoint) (den : Int) (a b d : Int) (fuel : Nat) : Option String := do
  let pairs := (List.range Ps.length).flatMap fun i =>
    (List.range Ps.length).filterMap fun j => if i < j then some (i, j) else none
  let (i, j) ← pairs.find? fun (i, j) =>
    match nth Ps i, nth Ps j with
    | some P, some Q => nonnegOn (sub (normP (psub Q P)) [den * den]) a b d fuel
    | _, _ => false
  pure s!"(.pair {i} {j})"

def fanDirections : FanWitness → List IPoint
  | .terminal _ _ _ => [rotEastP]
  | .next direction _ _ rest => direction :: fanDirections rest

def proposeHint (hint : ExclusionHint) (Ps : List IPoint) (den : Int)
    (caps : List Cap) (ord : Option (Fin 6)) (fuel : Nat) : Int → Int → Int → Option String :=
  match hint with
  | .ordinary => fun _ _ _ => some ".ordinary"
  | .pair _ _ => fun a b d => proposePair Ps den a b d fuel
  | .witnessedFan w => fun a b d => do
      let fan ← proposeFan Ps den caps a b d fuel eastP (fanDirections w)
      pure s!"(.witnessedFan {fan})"
  | .diameter => fun a b d => proposePair Ps den a b d fuel
  | .fan nodes => fun a b d => do
      let fan ← proposeFan Ps den caps a b d fuel eastP nodes
      pure s!"(.witnessedFan {fan})"
  | .split aa mid bb dd left right => fun _ _ _ => do
      let hl ← proposeHint left Ps den caps ord fuel aa mid dd
      let hr ← proposeHint right Ps den caps ord fuel mid bb dd
      pure s!"(.split ({aa}) ({mid}) ({bb}) ({dd}) {hl} {hr})"

def emitProposal (key : String) (hint : ExclusionHint) (Ps : List IPoint) (den : Int)
    (caps : List Cap) (ord : Option (Fin 6)) (a b d : Int) (fuel : Nat) : IO Unit := do
  unless hint.check Ps den caps ord fuel a b d do
    throw (IO.userError s!"Original arithmetic check failed: {key}")
  match proposeHint hint Ps den caps ord fuel a b d with
  | none => throw (IO.userError s!"No explicit arithmetic witness: {key}")
  | some result => IO.println s!"{key}\t{result}"

open ConwaySoifer.Simplified.Certificates
open Sint100000110000

def stateFields (M : Model) :=
  (List.finRange 10).map fun j => (j.val, M.B j, M.caps j, (M.ord j).map Fin.val)

def main : IO Unit := do
  let C := Data.Sint100000110000
  let some initial := initModel C.case C.lo C.hi C.den
    | throw (IO.userError "Initialization failed")
  let mut state := initial
  IO.println s!"Pinned rational data: {repr C}"
  for (step, index) in C.steps.zipIdx do
    IO.println s!"model{index}: {repr (stateFields state)}"
    IO.println s!"step{index}: {repr step}"
    state := state.insert step
  IO.println s!"final: {repr (stateFields state)}"
  emitProposal "excluded0_1" .diameter (model0.B 1 ++ [step0.q]) C.den
    (model0.caps 1) (model0.ord 1) 0 1 100 12
```
-/

@[expose] public section

namespace ConwaySoifer
open scoped Pointwise

/-- Any ten congruent closed equilateral triangles covering the side-three target
have common side at least one, with arbitrary positions and orientations. -/
theorem ten_triangle_cover_lower_bound : LowerBound := lowerBound_simplified

/-- Ten unit equilateral triangles cannot cover the target of side `3 + ε`. -/
theorem no_ten_unit_triangle_cover (ε : ℝ) (hε : 0 < ε) (T : Configuration)
    (hs : ∀ i, (T i).side = 1)
    (hcover : ∀ p ∈ (1 + ε / 3) • target, ∃ i, p ∈ (T i).carrier) : False :=
  no_ten_unit_triangle_cover_simplified ε hε T hs hcover

end ConwaySoifer
