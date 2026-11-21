/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduction.StrongConfluenceE

/-!
# One normal form, one length (pages 73-74)

Lafont 1997, pages 73-74, right after Proposition 1: "This strong confluence property has the
following consequence: if a net `N` reduces to an irreducible net `P` in `n` steps, then any
reduction starting from `N` eventually reaches `P` in `n` steps."

Nets are graphs, so one step is `StepE` and equality of nets is `Equiv`. The proof follows the
paper: induction on the length, with Proposition 1 for reduction of graphs
(`StepE.strong_confluence`) at each step.

Contents, in the order of the file:

1. Definition: `StepE.Normal I N`, `N` is irreducible: no `StepE` starts from it.
2. Auxiliary lemmas: `StepE.Normal.of_equiv`, irreducibility depends only on the graph;
   `StepE.Normal.of_not_hasCut`, a net without a cut is irreducible; `StepE.Normal.stepsEN_eq`,
   an irreducible net reduces only to itself; `StepsEN.head` and `StepsEN.linear`;
   `StepsEN.normal_of_step`, one step `N → M` against a reduction of `N` in `n` steps to a
   normal `P`: `n ≥ 1`, and `M` reduces in `n - 1` steps to `P`, up to wires;
   `StepsEN.normal_of_stepsEN`, the consequence of Proposition 1 in the paper's form: any
   reduction of `N` in `k` steps has `k ≤ n` and goes on in `n - k` steps to `P`, up to wires;
   `StepsEN.le_of_normal`.
3. Main result: `StepsEN.normal_unique`, two reductions of a linear net to normal forms have the
   same length and the same result, up to wires.
-/

@[expose] public section

namespace INet

variable {S : Signature}

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- **An irreducible net** (Lafont 1997, page 73: "an irreducible net `P`"). `N` is irreducible,
or in normal form, when no interaction up to wires starts from it. -/
def StepE.Normal
    -- the interaction system
    (I : System S)
    -- the net
    (N : Net S ℕ) :
    Prop :=
  ∀ M, ¬ StepE I N M

-- ============================================================================================
-- 2. Auxiliary lemmas: irreducible nets, and one step against a reduction to a normal form
-- ============================================================================================

namespace StepE.Normal

variable {I : System S} {N K : Net S ℕ}

/-- **Irreducibility is a property of the graph** (Lafont 1997, pages 72-73: nets are graphs). If
`N` is irreducible and `K` is the same graph as `N`, then `K` is irreducible. -/
theorem of_equiv
    -- `N` is irreducible
    (h : StepE.Normal I N)
    -- `K` is the same graph as `N`
    (hE : Equiv N K) :
    StepE.Normal I K :=
  fun M hs => h M (StepE.of_equiv hE hs)

/-- **A net without a cut is irreducible** (Lafont 1997, page 73: an interaction rewrites a cut;
page 77: the definition of a cut). -/
theorem of_not_hasCut
    -- the net has no cut
    (h : ¬ N.HasCut) :
    StepE.Normal I N :=
  fun _ hs => h hs.hasCut

/-- **An irreducible net reduces only to itself** (Lafont 1997, page 73). A counted reduction
from an irreducible net has length `0` and ends at the net itself. -/
theorem stepsEN_eq
    -- `N` is irreducible
    (h : StepE.Normal I N)
    -- a reduction of `N` to `K` in `n` steps, up to wires
    {n : ℕ}
    (hs : StepsEN I n N K) :
    -- it has no step,
    n = 0
      -- and ends at `N` itself
      ∧ N = K := by
  rcases hs.cases_head with hK | ⟨K', m, -, h1, -⟩
  · exact hK
  · exact absurd h1 (h K')

end StepE.Normal

namespace StepsEN

variable {I : System S}

/-- One interaction up to wires, then a counted reduction: the lengths add up. -/
theorem head
    -- the nets and the length of the reduction
    {n : ℕ}
    {N K M : Net S ℕ}
    -- one step from `N` to `K`, then `n` steps from `K` to `M`, up to wires
    (h₁ : StepE I N K)
    (h₂ : StepsEN I n K M) :
    StepsEN I (n + 1) N M := by
  have := (StepsEN.single h₁).trans h₂
  rwa [Nat.add_comm] at this

/-- A counted reduction keeps linearity (Lafont 1997, page 71). -/
theorem linear
    -- the system is well formed
    (hI : I.WellFormed)
    -- a reduction of `N` to `M` in `n` steps, up to wires
    {n : ℕ}
    {N M : Net S ℕ}
    (h : StepsEN I n N M)
    -- `N` is linear
    (hN : N.Linear) :
    M.Linear :=
  h.stepsE.linear hI.linear hN

/-- **One step against a reduction to a normal form** (Lafont 1997, pages 73-74, the consequence
of Proposition 1, for one step). Let `N` be linear in a well-formed system, reduce in `n` steps up
to wires to an irreducible `P`, and in one step up to wires to `M`. Then `n = m + 1` for some `m`,
and `M` reduces in `m` steps up to wires to a net that is the same graph as `P`. -/
theorem normal_of_step
    -- the system is well formed
    (hI : I.WellFormed)
    -- the nets and the length of the reduction; `N` is linear
    {n : ℕ}
    {N M P : Net S ℕ}
    (hN : N.Linear)
    -- `N` reduces in `n` steps up to wires to an irreducible `P`
    (hP : StepE.Normal I P)
    (hs : StepsEN I n N P)
    -- `N` reduces in one step up to wires to `M`
    (h : StepE I N M) :
    -- there is an `m` such that
    ∃ m,
      -- the reduction to `P` has `m + 1` steps,
      n = m + 1
      -- and `M` reduces in `m` steps up to wires to a net `P'` that is the same graph as `P`
      ∧ ∃ P', StepsEN I m M P' ∧ Equiv P' P := by
  induction n using Nat.strong_induction_on generalizing N M with
  | _ n ih =>
    rcases hs.cases_head with ⟨rfl, rfl⟩ | ⟨K, m, rfl, hK, hKP⟩
    · exact absurd h (hP M)
    · refine ⟨m, rfl, ?_⟩
      rcases StepE.strong_confluence hI hN h hK with E | ⟨P₁, P₂, u₁, u₂, EP⟩
      · exact StepsEN.of_equiv E hKP
      · obtain ⟨m', rfl, P'', h₂, E₂⟩ :=
          ih m (Nat.lt_succ_self m) (hK.linear hI.linear hN) hKP u₂
        obtain ⟨X, hX, EX⟩ := StepsEN.of_equiv EP h₂
        exact ⟨X, head u₁ hX, EX.trans E₂⟩

/-- **Any reduction reaches the normal form in the same number of steps** (Lafont 1997,
pages 73-74: "if a net `N` reduces to an irreducible net `P` in `n` steps, then any reduction
starting from `N` eventually reaches `P` in `n` steps"). Let `N` be linear in a well-formed
system and reduce in `n` steps up to wires to an irreducible `P`. If `N` reduces in `k` steps up to
wires to `Q`, then `k ≤ n`, and `Q` reduces in `n - k` steps up to wires to a net that is the same
graph as `P`. -/
theorem normal_of_stepsEN
    -- the system is well formed
    (hI : I.WellFormed)
    -- the nets and the lengths of the reductions; `N` is linear
    {n k : ℕ}
    {N P Q : Net S ℕ}
    (hN : N.Linear)
    -- `N` reduces in `n` steps up to wires to an irreducible `P`
    (hP : StepE.Normal I P)
    (hs : StepsEN I n N P)
    -- `N` reduces in `k` steps up to wires to `Q`
    (hk : StepsEN I k N Q) :
    -- the second reduction is not longer than the first,
    k ≤ n
      -- and `Q` reduces in `n - k` steps up to wires to a net `P'` that is the same graph as `P`
      ∧ ∃ P', StepsEN I (n - k) Q P' ∧ Equiv P' P := by
  induction hk with
  | refl => exact ⟨Nat.zero_le _, P, by simpa using hs, Equiv.refl _⟩
  | @tail k _ K Q hNK hKQ ih =>
    obtain ⟨hk, P', hKP, E⟩ := ih hN hs
    obtain ⟨m, hm, P'', hQP, E'⟩ :=
      normal_of_step hI (hNK.linear hI hN) (hP.of_equiv E.symm) hKP hKQ
    refine ⟨by omega, P'', ?_, E'.trans E⟩
    rwa [show n - (k + 1) = m by omega]

/-- **No reduction is longer than a reduction to a normal form** (Lafont 1997, pages 73-74). If a
linear net `N` of a well-formed system reduces in `n` steps up to wires to an irreducible net, then
every reduction of `N` up to wires has at most `n` steps. -/
theorem le_of_normal
    -- the system is well formed
    (hI : I.WellFormed)
    -- the nets and the lengths of the reductions; `N` is linear
    {n k : ℕ}
    {N P Q : Net S ℕ}
    (hN : N.Linear)
    -- `N` reduces in `n` steps up to wires to an irreducible `P`
    (hP : StepE.Normal I P)
    (hs : StepsEN I n N P)
    -- `N` reduces in `k` steps up to wires to `Q`
    (hk : StepsEN I k N Q) :
    k ≤ n :=
  (normal_of_stepsEN hI hN hP hs hk).1

-- ============================================================================================
-- 3. Main result: one normal form, one length
-- ============================================================================================

/-- **One normal form, one length** (Lafont 1997, pages 73-74). If a linear net `N` of a
well-formed system reduces in `n` steps up to wires to an irreducible `P` and in `m` steps up to
wires to an irreducible `Q`, then `m = n` and `P` and `Q` are the same graph. -/
theorem normal_unique
    -- the system is well formed
    (hI : I.WellFormed)
    -- the nets and the lengths of the reductions; `N` is linear
    {n m : ℕ}
    {N P Q : Net S ℕ}
    (hN : N.Linear)
    -- `P` and `Q` are irreducible
    (hP : StepE.Normal I P)
    (hQ : StepE.Normal I Q)
    -- `N` reduces in `n` steps to `P` and in `m` steps to `Q`, up to wires
    (hs : StepsEN I n N P)
    (ht : StepsEN I m N Q) :
    -- the two reductions have the same length,
    m = n
      -- and the two normal forms are the same graph
      ∧ Equiv P Q := by
  obtain ⟨hmn, P', hQP, E⟩ := normal_of_stepsEN hI hN hP hs ht
  have hnm := le_of_normal hI hN hQ ht hs
  obtain ⟨-, rfl⟩ := hQ.stepsEN_eq hQP
  exact ⟨by omega, E.symm⟩

end StepsEN

end INet
