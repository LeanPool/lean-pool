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

## Complete retained-corpus emission

Save the Python program below as RegenerateConwayCorpus.py outside the checkout. Build the
pinned aggregate first, then run from the repository root:

```sh
lake build LeanPool.ConwaySoifer.Imports
python3 "$CODEX_SCRATCH_ROOT/RegenerateConwayCorpus.py" --repository "$PWD" \
  --output "$CODEX_SCRATCH_ROOT/conway-regenerated" --workers 4
```

The driver discovers all 100 Data modules and every corresponding Steps/Checked consumer;
no certificate list, exclusion context, split branch or module output is entered manually.
It generates a standalone Lean executable per certificate using the preceding proposal code.
Each executable recomputes initModel and every Model.insert directly from the exact public
CertData trace, compares all ten owners' points/caps/flags and every step with the retained
checkpoint declarations, and emits the complete state payload and every exclusion proposal.
Pairs and support triples are searched again. Retained orientation directions, split intervals
and hint modes are seeds; they are not proof assumptions.

The output contains 100 unchanged Data inputs and 639 adapted checkpoint/replay consumers.
Checkpoint point literals, point lists, caps, flags and steps are rendered from the fresh
payload; exclusion terms and all 24-node shared fan tails are rendered from fresh proposals.
The retained files supply declaration names, layout and kernel-proof scaffolding. This is
intentional template-based regeneration of the public certificate cache, not recovery of the
unpublished search/export pipeline and not a generator of proofs for changed geometry.
Changing a checker interface still requires an ordinary port of its soundness proofs and
shared templates. Regeneration fails rather than assuming a missing state, exclusion or
successful acceptance check.

Every emitted file is compared byte-for-byte against its source template. The final
round-trip.json records counts, per-certificate timings and SHA-256 for every emitted file;
it is written only after every process, state/step comparison, witness expansion and file
comparison succeeds. Runtime files and logs remain in the external output directory. The
driver never edits the checkout. Reports count only the files emitted by the current run;
older files in a reused output directory are ignored. The sampled --certificate option is
for diagnosis; the default run covers the complete corpus. Regeneration evidence does not replace
the kernel acceptance/replay proofs or the complete build, linters, style and quality/trust gates.

The exact embedded driver was executed with four workers: all 100 certificates, 3,288 states,
3,188 steps, 28,792 exclusions and 739 emitted files passed the complete comparison in
384.64 seconds in a reused output directory. Its sorted file/hash record has SHA-256
1879985340d4368caa2aba8695f22d6a8336def34cac0d49cc7e884602dbbf2a.
This is a corpus reproduction measurement, not a controlled compile-time comparison.

The retained generated corpus is a sizeable certificate cache. Its maintenance tradeoff is
accepted here because the underlying research theorem, shared geometric interfaces and verified
interval checker are substantive, the consumer schema is small, the complete cache has a
reproducible round trip, and measured witness/state sharing reduced controlled compilation by
48.78%. Keeping exact rational inputs and checked replay makes the result independently
inspectable even when the historical search software is unavailable. No source-size exception,
trusted native result or relaxed gate is needed.

```python
"""Recompute the retained corpus and emit its verified source templates."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
from typing import Any


def arguments(source: str) -> list[str]:
    values, depth, start = [], 0, 0
    for index, character in enumerate(source):
        if character in '([{⟨':
            depth += 1
        elif character in ')]}⟩':
            depth -= 1
        elif character.isspace() and depth == 0:
            if source[start:index].strip():
                values.append(source[start:index].strip())
            start = index + 1
    if source[start:].strip():
        values.append(source[start:].strip())
    assert depth == 0
    return values


def compact(source: str) -> str:
    return re.sub(r'\((-?\d+)\)', r'\1', re.sub(r'\s+', '', source))


def expand_fans(source: str) -> dict[str, str]:
    aliases = {}
    pattern = r'^def (fan\d+Owner\d+Part\d+) : FanWitness := (.*?)\n\n'
    for match in re.finditer(pattern, source, re.M | re.S):
        value = match[2]
        for name, previous in aliases.items():
            value = re.sub(r'\b' + name + r'\b', lambda _: previous, value)
        aliases[match[1]] = value
    return aliases


def exclusion_rows(path: Path) -> tuple[str, list[dict[str, Any]]]:
    source = path.read_text()
    aliases = expand_fans(source)
    pattern = (r'^theorem (excluded\d+_\d+)\s*:\s*ExcludedOn (.*?) := by\n'
               r'  apply ExclusionHint.sound (.*?)\s+\(den\s*:=.*?\)\s+'
               r'\(fuel\s*:=\s*(\d+)\)')
    matches = list(re.finditer(pattern, source, re.M | re.S))
    assert len(matches) == source.count('  apply ExclusionHint.sound '), path
    rows = []
    for match in matches:
        values = arguments(match[2])
        assert len(values) == 7, (path, match[1])
        hint = match[3]
        for name in reversed(aliases):
            hint = re.sub(r'\b' + name + r'\b', lambda _: aliases[name], hint)
        rows.append({'name': match[1], 'arguments': values, 'hint': hint,
                     'fuel': int(match[4]), 'span': match.span(3), 'layout': match[3]})
    return source, rows



def render_layout(template: str, value: str) -> str:
    assert compact(template) == compact(value), (template[:80], value[:80])
    integer = r'(?<![\w])-?\d+\b'
    numbers = iter(re.findall(integer, value))
    rendered = re.sub(integer, lambda _: next(numbers), template)
    assert next(numbers, None) is None
    return rendered


def share_hint(value: str, declaration: str) -> tuple[str, dict[str, str]]:
    state, owner = re.fullmatch(r'excluded(\d+)_(\d+)', declaration).groups()
    definitions = {}

    def fan(term: str) -> tuple[str, int]:
        fields = arguments(term[1:-1])
        if fields[0] == '.terminal':
            return term, 0
        assert fields[0] == '.next' and len(fields) == 5
        tail, count = fan(fields[4])
        current = '(.next ' + ' '.join(fields[1:4]) + ' ' + tail + ')'
        count += 1
        if count == 24:
            alias = f'fan{state}Owner{owner}Part{len(definitions)}'
            definitions[alias] = current
            return alias, 0
        return current, count

    def hint(term: str) -> str:
        if term.startswith('(.witnessedFan '):
            tree, _ = fan(term[len('(.witnessedFan '):-1])
            return '(.witnessedFan ' + tree + ')'
        if term.startswith('(.split '):
            fields = arguments(term[1:-1])
            assert len(fields) == 7
            return ('(.split ' + ' '.join(fields[1:5]) + ' ' + hint(fields[5])
                    + ' ' + hint(fields[6]) + ')')
        return term

    return hint(value), definitions


def emit_checkpoint(template: str, payload: dict[str, str]) -> str:
    point_pattern = r'\(\[[^\]]*\],\s*\[[^\]]*\]\)'
    point_definitions = list(re.finditer(
        r'^def (point\d+) : IPoint := (.*?)\n\n', template, re.M | re.S))
    points = {match[1]: compact(match[2]) for match in point_definitions}
    fresh_points = {}
    for key, value in payload.items():
        if key.startswith(('B', 'caps', 'Q')):
            for match in re.finditer(point_pattern, value):
                fresh_points[compact(match[0])] = match[0]
    edits = []
    for match in point_definitions:
        assert points[match[1]] in fresh_points, match[1]
        edits.append((*match.span(2), render_layout(match[2], fresh_points[points[match[1]]])))
    point_sets = {}
    model_pattern = r'^def model(\d+) : Model :=\s*(.*?)(?=\n\n|\n/\-\-)'
    for match in re.finditer(model_pattern, template, re.M | re.S):
        cases = re.findall(r'\| (\d+|_) => (pointSet\d+)', match[2])
        assert len(cases) == 10, match[1]
        for owner, alias in cases:
            value = payload[f'B{match[1]}:{9 if owner == "_" else owner}']
            if alias in point_sets:
                assert compact(value) == compact(point_sets[alias]), alias
            point_sets[alias] = value
    set_pattern = r'^def (pointSet\d+) : List IPoint := (.*?)\n\n'
    for match in re.finditer(set_pattern, template, re.M | re.S):
        names = re.findall(r'\bpoint\d+\b', match[2])
        actual = re.findall(point_pattern, point_sets[match[1]])
        assert len(names) == len(actual), match[1]
        for alias, point in zip(names, actual, strict=True):
            assert points[alias] == compact(point), alias
        value = '[' + ', '.join(names) + ']'
        edits.append((*match.span(2), render_layout(match[2], value)))
    for field, prefix in [('capsConstraints', 'caps'), ('ownerFlags', 'ord')]:
        match = re.search(r'^def ' + field + r' : .*? :=\n(.*?)\n\n',
                          template, re.M | re.S)
        assert match, field
        cases = list(re.finditer(r'\| (\d+|_) => (.*?)(?=\n\s*\||$)',
                                 match[1], re.S))
        assert len(cases) == 10, field
        for case in cases:
            owner = 9 if case[1] == '_' else int(case[1])
            value = payload[f'{prefix}0:{owner}']
            aliases = iter(re.findall(r'\bpoint\d+\b', case[2]))

            def point_alias(current: re.Match[str]) -> str:
                alias = next(aliases)
                assert points[alias] == compact(current[0])
                return alias

            value = re.sub(point_pattern, point_alias, value)
            assert next(aliases, None) is None
            rendered = render_layout(case[2], value)
            offset = match.start(1)
            edits.append((offset + case.start(2), offset + case.end(2), rendered))
    for match in re.finditer(r'^def step(\d+) : Step := (.*?)\n', template, re.M):
        aliases = re.findall(r'\bpoint\d+\b', match[2])
        assert len(aliases) == 1
        assert points[aliases[0]] == compact(payload['Q' + match[1]])
        value = '⟨' + payload['owner' + match[1]] + ', ' + aliases[0] + '⟩'
        edits.append((*match.span(2), render_layout(match[2], value)))
    for start, end, replacement in sorted(edits, reverse=True):
        template = template[:start] + replacement + template[end:]
    return template


def program(root: Path, name: str, rows: list[dict[str, Any]]) -> tuple[str, int, int]:
    documentation = (root / 'LeanPool/ConwaySoifer.lean').read_text()
    sample = re.search(r'```lean\n(.*?)\n```', documentation, re.S)[1]
    core = sample.split('\nopen ConwaySoifer.Simplified.Certificates\n')[0]
    core = core.replace('Sint100000110000', name)
    core = core.replace('@[expose] public section',
                        'import all LeanPool.ConwaySoifer.Certificates.WitnessedArithmetic\n\n'
                        '@[expose] public section', 1)
    checkpoint = root / f'LeanPool/ConwaySoifer/Simplified/Certificates/Checkpoints/{name}.lean'
    source = checkpoint.read_text()
    indices = [int(value) for value in re.findall(r'^def model(\d+) : Model', source, re.M)]
    assert indices == list(range(len(indices))), name
    count = len(indices) - 1
    core += f'\nopen ConwaySoifer.Simplified.Certificates\nopen {name}\n'
    core += '\ninstance : Inhabited Model := ⟨⟨fun _ => [], fun _ => [], fun _ => none⟩⟩\n'
    core += 'instance : Inhabited Step := ⟨⟨0, ([0], [0])⟩⟩\n'
    core += '\ndef fields (M : Model) :=\n'
    core += '  (List.finRange 10).map fun j => (j.val, M.B j, M.caps j, (M.ord j).map Fin.val)\n'
    core += '\ndef quotePoints (Ps : List IPoint) :=\n'
    core += '  "[" ++ String.intercalate ", " (Ps.map quotePoint) ++ "]"\n'
    core += '\ndef quoteCaps (caps : List Cap) :=\n'
    core += '  "[" ++ String.intercalate ", " (caps.map fun c =>\n'
    core += '    s!"⟨{quotePoint c.p}, {quotePoint c.dv}, {c.strict}⟩") ++ "]"\n'
    core += '\ndef quoteOwner (owner : Option (Fin 6)) :=\n'
    core += '  match owner with\n  | none => "none"\n  | some j => s!"(some {j.val})"\n'
    core += '\ndef freshStates : Array Model := Id.run do\n'
    core += f'  let C := Data.{name}\n'
    core += '  let mut M := (initModel C.case C.lo C.hi C.den).get!\n'
    core += '  let mut states := #[M]\n  for step in C.steps do\n'
    core += '    M := M.insert step\n    states := states.push M\n  return states\n'
    core += '\ndef verifyStates : IO Unit := do\n'
    core += (f'  unless (initModel Data.{name}.case Data.{name}.lo '
             f'Data.{name}.hi Data.{name}.den).isSome do\n')
    core += '    throw (IO.userError \"Initialization failed\")\n'
    core += f'  unless freshStates.size == {count + 1} do\n'
    core += '    throw (IO.userError "State count mismatch")\n'
    for index in indices:
        core += (f'  unless reprStr (fields freshStates[{index}]!) == '
                 f'reprStr (fields model{index}) do\n')
        core += f'    throw (IO.userError "State mismatch: {index}")\n'
    for index in range(count):
        core += f'  unless reprStr Data.{name}.steps[{index}]! == reprStr step{index} do\n'
        core += f'    throw (IO.userError "Step mismatch: {index}")\n'
    for index, row in enumerate(rows):
        values = ' '.join(row['arguments'])
        values = re.sub(r'\bmodel(\d+)\b', lambda m: f'(freshStates[{m[1]}]!)', values)
        values = re.sub(r'\bstep(\d+)\b', lambda m: f'(Data.{name}.steps[{m[1]}]!)', values)
        core += f'\ndef task{index} : IO Unit :=\n'
        core += f'  emitProposal "{row["name"]}" {row["hint"]} {values} {row["fuel"]}\n'
    batches = list(range(0, len(rows), 80))
    for batch, start in enumerate(batches):
        core += f'\ndef batch{batch} : IO Unit := do\n'
        core += ''.join(f'  task{index}\n' for index in range(start, min(start + 80, len(rows))))
    core += '\ndef emitStates : IO Unit := do\n'
    core += '  for index in List.range freshStates.size do\n'
    core += '    let M := freshStates[index]!\n'
    core += '    for j in List.finRange 10 do\n'
    core += '      IO.println s!"B{index}:{j.val}\\t{quotePoints (M.B j)}"\n'
    core += '      IO.println s!"caps{index}:{j.val}\\t{quoteCaps (M.caps j)}"\n'
    core += '      IO.println s!"ord{index}:{j.val}\\t{quoteOwner (M.ord j)}"\n'
    core += f'  for (step, index) in Data.{name}.steps.zipIdx do\n'
    core += '    IO.println s!"Q{index}\\t{quotePoint step.q}"\n'
    core += '    IO.println s!"owner{index}\\t{step.owner.val}"\n'
    core += '\ndef main : IO Unit := do\n  verifyStates\n  emitStates\n'
    core += ''.join(f'  batch{batch}\n' for batch in range(len(batches)))
    return core, len(indices), count


def regenerate(root: Path, output: Path, name: str) -> dict[str, Any]:
    certificates = root / 'LeanPool/ConwaySoifer/Simplified/Certificates'
    paths = []
    for path in sorted((certificates / 'Steps').glob('*.lean')):
        if f'Certificates.Checkpoints.{name}\n' in path.read_text():
            paths.append(path)
    paths.append(certificates / 'Checked' / f'{name}.lean')
    templates, rows = {}, []
    for path in paths:
        source, current = exclusion_rows(path)
        templates[path] = (source, current)
        rows.extend(current)
    source, states, steps = program(root, name, rows)
    runtime = output / 'runtime'
    runtime.mkdir(exist_ok=True)
    executable = runtime / f'{name}.lean'
    executable.write_text(source)
    environment = os.environ.copy()
    environment['LEAN_NUM_THREADS'] = '1'
    started = time.monotonic()
    with executable.with_suffix('.log').open('w') as stream:
        result = subprocess.run(['lake', 'env', 'lean', '-j', '1', '--run', str(executable)],
                                cwd=root, env=environment, stdout=stream,
                                stderr=subprocess.STDOUT, check=False)
    assert result.returncode == 0, executable.with_suffix('.log')
    proposals = {}
    for line in executable.with_suffix('.log').read_text().splitlines():
        if '\t' in line:
            key, value = line.split('\t', 1)
            assert key not in proposals, key
            proposals[key] = value
    assert ({key for key in proposals if key.startswith('excluded')}
            == {row['name'] for row in rows}), name
    for path, (template, current) in templates.items():
        edits, definitions = [], {}
        for row in current:
            proposed = proposals[row['name']]
            assert compact(proposed) == compact(row['hint']), (path, row['name'])
            fresh, shared = share_hint(proposed, row['name'])
            definitions.update(shared)
            edits.append((*row['span'], render_layout(row['layout'], fresh)))
        matches = list(re.finditer(
            r'^def (fan\d+Owner\d+Part\d+) : FanWitness := (.*?)\n\n',
            template, re.M | re.S))
        assert set(definitions) == {match[1] for match in matches}
        for match in matches:
            edits.append((*match.span(2), render_layout(match[2], definitions[match[1]])))
        rendered = template
        for start, end, replacement in sorted(edits, reverse=True):
            rendered = rendered[:start] + replacement + rendered[end:]
        relative = path.relative_to(root)
        destination = output / 'corpus' / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(rendered)
    for category in ['Data', 'Checkpoints']:
        path = certificates / category / f'{name}.lean'
        destination = output / 'corpus' / path.relative_to(root)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(emit_checkpoint(path.read_text(), proposals)
                               if category == 'Checkpoints' else path.read_text())
    emitted = paths + [certificates / category / f'{name}.lean'
                       for category in ['Data', 'Checkpoints']]
    return {'certificate': name, 'states': states, 'steps': steps,
            'exclusions': len(rows), 'files': len(emitted),
            'emitted_files': [str(path.relative_to(root)) for path in emitted],
            'wall_seconds': time.monotonic() - started}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--repository', type=Path, default=Path.cwd())
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--certificate')
    options = parser.parse_args()
    root, output = options.repository.resolve(), options.output.resolve()
    assert root not in output.parents and output != root, 'Output must be outside checkout'
    output.mkdir(parents=True, exist_ok=True)
    (output / 'round-trip.json').unlink(missing_ok=True)
    names = sorted(path.stem for path in
                   (root / 'LeanPool/ConwaySoifer/Simplified/Certificates/Data').glob('*.lean'))
    assert len(names) == 100
    if options.certificate:
        assert options.certificate in names
        names = [options.certificate]
    started = time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(max_workers=options.workers) as executor:
        results = list(executor.map(lambda name: regenerate(root, output, name), names))
    emitted = [relative for row in results for relative in row['emitted_files']]
    assert len(emitted) == len(set(emitted)) == sum(row['files'] for row in results)
    hashes = []
    for relative in sorted(emitted):
        expected = (root / relative).read_bytes()
        assert (output / 'corpus' / relative).read_bytes() == expected, relative
        hashes.append({'file': relative, 'sha256': hashlib.sha256(expected).hexdigest()})
    report = {'certificates': len(results), 'states': sum(row['states'] for row in results),
              'steps': sum(row['steps'] for row in results),
              'exclusions': sum(row['exclusions'] for row in results), 'files': len(hashes),
              'wall_seconds': time.monotonic() - started, 'results': results, 'hashes': hashes}
    (output / 'round-trip.json').write_text(json.dumps(report, indent=2))
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ['results', 'hashes']}))


if __name__ == '__main__':
    main()
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
