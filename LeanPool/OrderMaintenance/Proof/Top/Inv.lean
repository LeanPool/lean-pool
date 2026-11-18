/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Sorted


/-!
# M5: the top structure's invariant `TopInv`

* `Shape` (§4.5.1), for the state with the running job's path copy completed (`finS`);
* `Timing`: stored versus true weights (F1), and the drain timing of Lemma T3;
* `Room`: label room in every table (our replacement for Lemma T5's histories: a potential
  argument with a per-table count of insertion events);
* the running job's position.

Constants (`docs/PROOF.md` §4.5.2), for `h ≥ 1`: `W_h = 2aʰ`, `K_h = ⌊(W_h+2)/(s-2)⌋ + 1`,
`Π_h = W_h + 2 + 2K_h`, `τ_1 = a + 1`, `τ_h = aʰ + 1 + Π_{h-1}`, `λ_1 = a`,
`λ_h = aʰ + 1 - Π_{h-1}`, `γ_h = W_h + 1 - τ_h`.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### Constants -/

section consts
variable (P : Params)

/-- Weight threshold for starting a drain at the given height. -/
def Wd (h : Nat) : Nat := 2 * P.a ^ h
/-- Number of drain steps allowed by the height-dependent sweep budget. -/
def Kd (h : Nat) : Nat := (Wd P h + 2) / (P.s - 2) + 1
/-- Potential allowance for insertions during a node drain. -/
def Pid (h : Nat) : Nat := Wd P h + 2 + 2 * Kd P h
/-- Upper weight threshold for a live node at the given height. -/
def taud : Nat → Nat
  | 0 => 0
  | 1 => P.a + 1
  | h + 2 => P.a ^ (h + 2) + 1 + Pid P (h + 1)
/-- Lower weight threshold for a released drain target. -/
def lamd : Nat → Nat
  | 0 => 0
  | 1 => P.a
  | h + 2 => P.a ^ (h + 2) + 1 - Pid P (h + 1)
/-- Weight slack freed by completing a drain at the given height. -/
def gamd (h : Nat) : Nat := Wd P h + 1 - taud P h

/-- Entries of a fresh table of height `h`: children plus the ghosts between them
(T4's counting). -/
def n0max (h : Nat) : Nat :=
  if h ≤ 1 then P.a + 1 else
    (1 + (taud P h - 1) / lamd P (h - 1)) + (1 + (taud P h - 1) / lamd P (h - 1)) / 2

/-- Insertion events a table of height `h` can see (from the potential of `Room`). -/
def Dmax (h : Nat) : Nat :=
  if h ≤ 1 then Pid P 1 / 2 else n0max P h + Pid P h / gamd P (h - 1) + 1

end consts

/-! ### Conditions on the parameters -/

/-- What the top structure's timing and label room need of the parameters (`docs/PROOF.md`
§4.5.3–4.5.5); `topParams_proof` checks them for the proof parameters. -/
structure TopParams (P : Params) : Prop where
  s3 : 3 ≤ P.s
  /-- A released target fits under the drain threshold (I6, in the form `λ_h ≥ 2 + 2K_h`). -/
  lamK : ∀ h, 1 ≤ h → 2 + 2 * Kd P h ≤ lamd P h
  /-- Labels have room for every insertion event (our form of I7). -/
  room : ∀ h, 1 ≤ h → 2 ^ Dmax P h * (n0max P h + 1) ≤ 2 ^ P.beta
  /-- A drain's targets weigh less than a node about to drain at the height above
  (`Π_{h-1} ≤ W_h`). -/
  piW : ∀ h, 2 ≤ h → Pid P (h - 1) ≤ Wd P h
  /-- Draining one level down frees room: `γ_h ≥ 1`. -/
  gam1 : ∀ h, 1 ≤ h → 1 ≤ gamd P h
  /-- Tables stay short: at most 160 entries (the machine's per-node list capacity). -/
  tab : ∀ h, 1 ≤ h → n0max P h + 2 * Dmax P h ≤ 160

/-! ### The copy phase -/

/-- One step of the path copy (`jobStep`, `.copy l`), as a state update. -/
def copyS (s : TS) (j : Job) (l : Nat) : TS :=
  let v := pth s j.x l
  let s1 := { s with path := s.path.setX j.y ((s.path.getX j.y).setX l v) }
  let s2 := { s1 with path := s1.path.setX j.z ((s1.path.getX j.z).setX l v) }
  let V := nd s2 v
  let s3 := if V.first == j.x then
    { s2 with nodes := s2.nodes.modify v fun n => { n with first := j.y } } else s2
  if V.last == j.x then
    { s3 with nodes := s3.nodes.modify v fun n => { n with last := j.z } } else s3

/-- The state after the remaining copy steps `l, l+1, …, H`. -/
def copyRest (j : Job) (H : Nat) (s : TS) (l : Nat) : TS :=
  if l ≤ H then copyRest j H (copyS s j l) (l + 1) else s
termination_by H + 1 - l

/-- The state with the path copy of the running job `oj` completed. -/
def finS (s : TS) (oj : Option Job) : TS :=
  match oj with
  | some j => match j.pc with
    | .copy l => copyRest j s.P.H s l
    | _ => s
  | none => s

/-! ### The running job -/

/-- The nodes up from `v` along live parents. -/
def upChain (s : TS) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, v => if v = NIL then [] else v :: upChain s f (nd s v).livePar

/-- Where the job's weight increments resume. -/
def wStart (s : TS) (j : Job) : Nat :=
  match j.pc with
  | .copy _ => lpr s j.y
  | .walk none => lpr s j.y
  | .walk (some v) => v
  | .afterDrain _ up => up
  | .fund _ up _ _ => up

/-- Live nodes whose stored weight lags its true weight by 2, when job `oj` runs. -/
def pend (s : TS) (oj : Option Job) : List Nat :=
  match oj with
  | some j => upChain s (s.P.H + 1) (wStart s j)
  | none => []

/-- Ghost `v` is funded by the running job: a target of `v` is on the job's path. -/
def funded (s : TS) (oj : Option Job) (v : Nat) : Prop :=
  match oj with
  | some j => anc s j.y (ht s v) = (nd s v).t1 ∨ anc s j.y (ht s v) = (nd s v).t2
  | none => False

instance (s : TS) (oj : Option Job) (v : Nat) : Decidable (funded s oj v) := by
  unfold funded; split <;> infer_instance

/-- The lowest height at which the running job has sweeps left (`H + 1`: none). -/
def curH (s : TS) (j : Job) : Nat :=
  match j.pc with
  | .copy _ => 1
  | .walk none => 1
  | .walk (some v) => if v = NIL then s.P.H + 1 else ht s v
  | .afterDrain v _ => ht s v + 1
  | .fund v _ _ _ => ht s v + 1

/-- The sweeps the running job still owes ghost `v`. -/
def slack (s : TS) (oj : Option Job) (v : Nat) : Nat :=
  match oj with
  | none => 0
  | some j =>
    if anc s j.y (ht s v) = (nd s v).t1 ∨ anc s j.y (ht s v) = (nd s v).t2 then
      if curH s j ≤ ht s v then s.P.s
      else match j.pc with
        | .fund _ _ src k => if src = v then s.P.s - k else 0
        | _ => 0
    else 0

/-! ### Weights and drain timing -/

/-- `w(v⁻) + w(v⁺)` for a ghost, `w(v)` for a live node: the weight the table of `v` serves. -/
def ew (s : TS) (cl : List Nat) (v : Nat) : Nat :=
  if (nd s v).draining then tw s cl (nd s v).t1 + tw s cl (nd s v).t2 else tw s cl v

/-- Funding jobs of ghost `v` so far. -/
def fundOf (s : TS) (cl : List Nat) (v : Nat) : Nat := (ew s cl v - (nd s v).weight) / 2

/-- Weight and progress inequalities ensuring scheduled drains finish in time. -/
structure Timing (s : TS) (cl : List Nat) (oj : Option Job) : Prop where
  /-- (F1) stored weights. -/
  wts : ∀ v, liveN s v → (nd s v).weight + (if v ∈ pend s oj then 2 else 0) = tw s cl v
  /-- T3 (a). -/
  wA : ∀ v, liveN s v → (nd s v).livePar ≠ NIL → srcOf s v = NIL → (nd s v).weight ≤ Wd s.P (ht s v)
  /-- T3 (b): the frozen start weight of a drain. -/
  wB : ∀ v, ghostN s v → Wd s.P (ht s v) + 1 ≤ (nd s v).weight ∧ (nd s v).weight ≤ Wd s.P (ht s
    v) + 2
  /-- Each funding job adds 2. -/
  wF : ∀ v, ghostN s v → (nd s v).weight ≤ ew s cl v ∧ (ew s cl v - (nd s v).weight) % 2 = 0
  /-- T3 (c). -/
  wC : ∀ v, ghostN s v →
    (rng s cl v).length + (s.P.s - 2) * fundOf s cl v ≤ (nd s v).weight + slack s oj v
  wC' : ∀ v, ghostN s v →
    (s.P.s - 2) * (fundOf s cl v - (if funded s oj v then 1 else 0)) ≤ (nd s v).weight
  /-- Fresh targets are heavy (T0), and weights never decrease. -/
  wD : ∀ v, liveN s v → s.P.H < v → lamd s.P (ht s v) ≤ tw s cl v
  /-- Targets are not chain nodes. -/
  big : ∀ t, liveN s t → srcOf s t ≠ NIL → s.P.H < t
  /-- The chain nodes of the initial structure: node `u ≤ H` has height `u`. -/
  chain : ∀ u, isN s u → u ≤ s.P.H → ht s u = u
  /-- Every live node has a chunk below it. -/
  tw1 : ∀ u, liveN s u → 1 ≤ tw s cl u

/-! ### Label room -/

/-- The gap bound of a table created with `n` entries after `d` insertion events. -/
def gapB (β n d : Nat) : Nat := 2 ^ β / (n + 1) / 2 ^ d

/-- Live entries of `X` created after `X` (`X < e`), and their growth beyond `τ`. -/
def growth (s : TS) (cl : List Nat) (X : Nat) : Nat :=
  ((order s X).filter fun e => decide (liveN s e) && decide (X < e)).foldr
    (fun e acc => acc + (tw s cl e - taud s.P (ht s X - 1))) 0

/-- Live entries of `X` present when `X` was created (`e < X`). -/
def oldLive (s : TS) (X : Nat) : Nat :=
  ((order s X).filter fun e => decide (liveN s e) && decide (e < X)).length

/-- Label-gap potential sufficient for every insertion before a table is replaced. -/
structure Room (s : TS) (cl : List Nat) (dr n0 : Nat → Nat) : Prop where
  gaps : ∀ X, isN s X → GapsGe s.P.beta (gapB s.P.beta (n0 X) (dr X)) (labs s X)
  n0le : ∀ X, isN s X → n0 X ≤ n0max s.P (ht s X)
  pot1 : ∀ X, isN s X → ht s X = 1 →
    2 * dr X + (if s.P.H < X then lamd s.P 1 else 1) ≤ ew s cl X
  pot2 : ∀ X, isN s X → 2 ≤ ht s X →
    gamd s.P (ht s X - 1) * dr X + growth s cl X + (if s.P.H < X then lamd s.P (ht s X) else 1) +
      gamd s.P (ht s X - 1) * oldLive s X ≤ ew s cl X + gamd s.P (ht s X - 1) * n0 X

/-- **Table lengths.** A table holds at most two entries per insertion event beyond its initial
ones, and so does its side list; and `n0 + 2·dr ≤ 160` (so every table and side list, dead ones
included, has at most 160 entries: the machine's per-node list capacity). -/
def TabLen (s : TS) (dr n0 : Nat → Nat) : Prop :=
  ∀ X, (order s X).length ≤ n0 X + 2 * dr X ∧ (nd s X).side.length ≤ n0 X + 2 * dr X ∧
    n0 X + 2 * dr X ≤ 160

/-- Lists that do not grow keep the bound (with the same `dr`, `n0`). -/
theorem TabLen.mono {s s' : TS} {dr n0 : Nat → Nat} (h : TabLen s dr n0)
    (hl : ∀ X, (order s' X).length ≤ (order s X).length ∧ (nd s' X).side.length ≤ (nd s
      X).side.length) :
    TabLen s' dr n0 := fun X => by
  obtain ⟨a, b, c⟩ := h X; obtain ⟨d, e⟩ := hl X; exact ⟨by omega, by omega, c⟩

theorem TabLen.congr {s s' : TS} {dr n0 : Nat → Nat} (h : TabLen s dr n0)
    (hl : ∀ X, order s' X = order s X ∧ (nd s' X).side = (nd s X).side) : TabLen s' dr n0 :=
  h.mono fun X => by rw [(hl X).1, (hl X).2]; exact ⟨le_rfl, le_rfl⟩

/-! ### The running job's position -/

/-- Where the running job is, in the state with its path copied. -/
def JobAt (s : TS) (j : Job) : Prop :=
  match j.pc with
  | .copy l => 1 ≤ l ∧ l ≤ s.P.H ∧ lpr s j.y = lpr s j.x ∧ lpr s j.z = lpr s j.x
  | .walk none => lpr s j.y = lpr s j.x ∧ lpr s j.z = lpr s j.x
  | .walk (some v) => v = NIL ∨ (liveN s v ∧ v = anc s j.y (ht s v))
  | .afterDrain v up => ghostN s v ∧
      (anc s j.y (ht s v) = (nd s v).t1 ∨ anc s j.y (ht s v) = (nd s v).t2) ∧
      up = anc s j.y (ht s v + 1)
  | .fund v up src k => liveN s v ∧ v = anc s j.y (ht s v) ∧ up = anc s j.y (ht s v + 1) ∧
      ghostN s src ∧ srcOf s v = src ∧ k ≤ s.P.s

/-- Consistency of the suspended reservation job with its copied paths and weight walk. -/
structure JobOK (s : TS) (cl : List Nat) (j : Job) : Prop where
  pos : ∃ A B, cl = A ++ j.y :: j.x :: j.z :: B
  at_ : JobAt s j

/-! ### The invariant -/

/-- The invariant of a top structure running job `oj`, whose path copy is complete. -/
structure InvJ (s : TS) (cl : List Nat) (ord : Nat → List Nat) (dr n0 : Nat → Nat)
    (oj : Option Job) : Prop where
  shape : Shape s cl ord
  time : Timing s cl oj
  room : Room s cl dr n0
  job : ∀ j, oj = some j → JobOK s cl j
  /-- Room for the chunks (the contract's capacity): nodes of height `H - 1` never drain. -/
  cap : cl.length + 2 ≤ Wd s.P (s.P.H - 1)
  len : TabLen s dr n0

/-- **The top structure's invariant** (M5's `TI`). -/
def TopInv (s : Core) : Prop :=
  TopParams s.P ∧ ∃ cl ord dr n0, LList (cN s) (cP s) s.firstChunk cl ∧
    (∀ c, c ∈ cl ↔ 1 ≤ c ∧ c < s.C.size) ∧ InvJ (finS (ts s) s.resJob) cl ord dr n0 s.resJob

/-! ### The job measure -/

/-- Steps left for a walk that has heights `h, h+1, …, H` to visit. -/
def walkLeft (P : Params) (h : Nat) : Nat := (P.H + 1 - h) * (P.s + 1) + 1

/-- Steps left in job `j`. -/
def jobLeft (s : TS) (j : Job) : Nat :=
  match j.pc with
  | .copy l => (s.P.H + 1 - l) + walkLeft s.P 1
  | .walk none => walkLeft s.P 1
  | .walk (some v) => if v = NIL then 1 else walkLeft s.P (ht s v)
  | .afterDrain v _ => walkLeft s.P (ht s v + 1) + 1
  | .fund v _ _ k => walkLeft s.P (ht s v + 1) + (s.P.s - k) + 1

/-- **The job measure** (M5's `μ`). -/
def topMu (s : Core) : Nat :=
  match s.resJob with
  | some j => jobLeft (ts s) j
  | none => 0

/-- The job length bound (M5's `J`). -/
def topJ (P : Params) : Nat := (P.H + 1) + walkLeft P 1

theorem _root_.OrderMaintenance.Proof.TopSame.topInv {s s' : Core} (h : TopSame s s') (hI :
  TopInv s) : TopInv s' := by
  obtain ⟨hTP, cl, ord, dr, n0, hL, hC, hI⟩ := hI
  refine ⟨by rw [h.P]; exact hTP, cl, ord, dr, n0, ?_, fun c => by rw [h.Csize]; exact hC c,
    by rw [h.ts, h.top.2.2.2.2.1]; exact hI⟩
  have e1 : cN s' = cN s := funext fun c => (h.links c).1
  have e2 : cP s' = cP s := funext fun c => (h.links c).2.1
  rw [e1, e2, h.top.2.2.2.2.2.2.2]; exact hL

theorem _root_.OrderMaintenance.Proof.TopSame.topMu {s s' : Core} (h : TopSame s s') : topMu s'
  = topMu s := by
  unfold OrderMaintenance.Proof.Top.topMu
  rw [h.ts, h.top.2.2.2.2.1]

end OrderMaintenance.Proof.Top
