/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.Simulation

/-!
# Proposition 4 with the lengths of the reductions

Lafont 1997, page 81: "let `L` (resp. `M`) be the minimal (resp. maximal) length of all those
reductions", the reductions of the translations of the rules. Proposition 4: "If `Θ` … reduces in
`n` steps to `Θ'`, then `Φ(Θ)` reduces in `n'` steps to `Φ(Θ')`, with `L n ≤ n' ≤ M n`."

`Steps` and `StepsE` are reflexive transitive closures and carry no length. Here:

* `StepsN I n N M` and `StepsEN I n N M` — `N` reduces to `M` in exactly `n` steps of `Step`, of
  `StepE`, with the closure lemmas of `StepsE` keeping `n` (`StepsEN.add_right`,
  `StepsEN.of_equiv`, `StepsEN.bind_var`).
* `Translation.CompatibleWithin Φ I I' L M` — `Φ` is compatible, and the reduction of every rule
  has a length between `L` and `M`.
* `Translation.CompatibleWithin.steps` — Proposition 4 with the bounds.

The proof of one step is `Translation.CompatibleBy.step` of `Simulation.lean`, applied to the
reduction "in `k` steps, `L ≤ k ≤ M`".

Contents, in the order of the file:

1. Definitions: `StepsN` and `StepsEN`, reduction in exactly `n` interactions, literal and up to
   wires; `Translation.CompatibleWithin`, a translation whose rules are simulated in `k`
   interactions, `L ≤ k ≤ M`.
2. Auxiliary lemmas, counted reductions: `StepsN.steps`, `StepsN.stepsEN`,
   `Steps.exists_stepsN`, `StepsE.exists_stepsEN`, `StepE.bind_var`, `StepsEN.stepsE`,
   `StepsEN.single`, `StepsEN.trans`, `StepsEN.bind_var`, `StepsEN.of_equiv`,
   `StepsEN.add_right`.
3. Auxiliary lemmas, compatibility with bounded lengths: `Translation.CompatibleWithin.compatible`,
   `Translation.id_compatibleWithin` (the identity, with `L = M = 1`),
   `Translation.CompatibleWithin.step` (one interaction).
4. Main result: `Translation.CompatibleWithin.steps`, Proposition 4 (page 81).
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- `N` reduces to `M` in exactly `n` interactions (Lafont 1997, page 81: "reduces in `n`
steps"). -/
inductive StepsN
    -- the interaction system
    (I : System S) :
    ℕ → Net S ℕ → Net S ℕ → Prop
  -- no interaction
  | refl (N : Net S ℕ) : StepsN I 0 N N
  -- `n` interactions from `N` to `K`, then one from `K` to `M`
  | tail {n : ℕ} {N K M : Net S ℕ} : StepsN I n N K → Step I K M → StepsN I (n + 1) N M

/-- `N` reduces up to wires to `M` in exactly `n` interactions (Lafont 1997, page 81: "reduces in
`n'` steps"; Section 1.1, page 71: a net is a graph; Section 1.2, page 73: reduction). -/
inductive StepsEN
    -- the interaction system
    (I : System S) :
    ℕ → Net S ℕ → Net S ℕ → Prop
  -- no interaction
  | refl (N : Net S ℕ) : StepsEN I 0 N N
  -- `n` interactions from `N` to `K`, then one, up to wires, from `K` to `M`
  | tail {n : ℕ} {N K M : Net S ℕ} : StepsEN I n N K → StepE I K M → StepsEN I (n + 1) N M

namespace Translation

/-- **A translation with the lengths of its rules between `L` and `M`** (Lafont 1997, page 81:
"let `L` (resp. `M`) be the minimal (resp. maximal) length of all those reductions"). For every
rule, the translations of the two cells reduce up to wires to a translation of the right-hand side
in `k` interactions, `L ≤ k ≤ M`. -/
def CompatibleWithin
    -- the translation, from the system `I` to the system `I'`
    (Φ : Translation S S')
    (I : System S)
    (I' : System S')
    -- the bounds on the lengths
    (L M : ℕ) :
    Prop :=
  Φ.CompatibleBy I fun N K => ∃ k, L ≤ k ∧ k ≤ M ∧ StepsEN I' k N K

end Translation

-- ============================================================================================
-- 2. Auxiliary lemmas: counted reductions
-- ============================================================================================

namespace StepsN

-- the system, the length, the two ends of the reduction
variable {I : System S} {n : ℕ} {N M : Net S ℕ}

/-- A reduction in `n` interactions is a reduction (Lafont 1997, Section 1.2, page 73). -/
theorem steps
    (h : StepsN I n N M) :
    Steps I N M := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail hs

/-- A reduction in `n` interactions is a reduction up to wires in `n` interactions (Lafont 1997,
Section 1.2, page 73). -/
theorem stepsEN
    (h : StepsN I n N M) :
    StepsEN I n N M := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact ih.tail hs.stepE

end StepsN

/-- Every reduction has a length (Lafont 1997, page 81). -/
theorem Steps.exists_stepsN
    -- a reduction from `N` to `M` in the system `I`
    {I : System S}
    {N M : Net S ℕ}
    (h : Steps I N M) :
    -- it takes some number `n` of interactions
    ∃ n, StepsN I n N M := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | tail _ hs ih =>
    obtain ⟨n, h⟩ := ih
    exact ⟨n + 1, h.tail hs⟩

/-- Every reduction up to wires has a length (Lafont 1997, page 81). -/
theorem StepsE.exists_stepsEN
    -- a reduction up to wires from `N` to `M` in the system `I`
    {I : System S}
    {N M : Net S ℕ}
    (h : StepsE I N M) :
    -- it takes some number `n` of interactions
    ∃ n, StepsEN I n N M := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | tail _ hs ih =>
    obtain ⟨n, h⟩ := ih
    exact ⟨n + 1, h.tail hs⟩

/-- One interaction up to wires, renamed by an injective function, is one interaction up to
wires (Lafont 1997, Section 1.2, page 73: reduction does not depend on names). -/
theorem StepE.bind_var
    -- the system
    {I : System S}
    -- the renaming, injective
    (f : ℕ → ℕ)
    (hf : Function.Injective f)
    -- one interaction up to wires from `N` to `M`
    {N M : Net S ℕ}
    (h : StepE I N M) :
    -- the renamed `N` reduces in one interaction up to wires to the renamed `M`
    StepE I (N.bind fun y => Term.var (f y)) (M.bind fun y => Term.var (f y)) := by
  obtain ⟨K, hE, hS⟩ := h
  exact ⟨_, hE.bind_var f hf, hS.bind_var f hf⟩

namespace StepsEN

-- the system, the lengths, the nets
variable {I : System S} {n m : ℕ} {N K M : Net S ℕ}

/-- A reduction up to wires in `n` interactions is a reduction up to wires. -/
theorem stepsE
    (h : StepsEN I n N M) :
    StepsE I N M := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail hs

/-- One interaction up to wires is a reduction in one interaction. -/
theorem single
    (h : StepE I N M) :
    StepsEN I 1 N M := (StepsEN.refl N).tail h

/-- The lengths of two reductions, one after the other, add up (Lafont 1997, page 81). -/
theorem trans
    -- `N` reduces to `K` in `n` interactions
    (h₁ : StepsEN I n N K)
    -- `K` reduces to `M` in `m` interactions
    (h₂ : StepsEN I m K M) :
    -- `N` reduces to `M` in `n + m` interactions
    StepsEN I (n + m) N M := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact (ih h₁).tail hs

/-- **A counted reduction, renamed.** Renaming every name by an injective function keeps a
reduction up to wires and its length (Lafont 1997, Section 1.2, page 73). -/
theorem bind_var
    -- the renaming, injective
    (f : ℕ → ℕ)
    (hf : Function.Injective f)
    -- a reduction in `n` interactions from `N` to `M`
    (h : StepsEN I n N M) :
    -- the renamed `N` reduces in `n` interactions to the renamed `M`
    StepsEN I n (N.bind fun y => Term.var (f y)) (M.bind fun y => Term.var (f y)) := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact ih.tail (hs.bind_var f hf)

/-- **An equivalence, then a counted reduction.** If `N` is the same graph as `K` and `K` reduces
in `n` interactions to `M`, then `N` reduces in `n` interactions to a net that is the same graph
as `M` (Lafont 1997, Section 1.1, page 71: a net is a graph; Section 1.2, page 73). -/
theorem of_equiv
    -- `N` is the same graph as `K`
    (hE : Equiv N K)
    -- `K` reduces in `n` interactions to `M`
    (h : StepsEN I n K M) :
    -- there is a net `M'` such that
    ∃ M',
      -- `N` reduces to `M'` in `n` interactions,
      StepsEN I n N M'
      -- and `M'` is the same graph as `M`
      ∧ Equiv M' M := by
  induction h with
  | refl => exact ⟨N, .refl _, hE⟩
  | tail _ hs ih =>
    obtain ⟨M', h1, h2⟩ := ih hE
    exact ⟨_, h1.tail (StepE.of_equiv h2 hs), Equiv.refl _⟩

/-- **A counted reduction inside a larger net.** If `N` reduces in `n` interactions to `M` and
`N + Γ` is linear, then `N + Γ` reduces in `n` interactions to `M' + Γ`, with `M'` the same graph
as `M` (Lafont 1997, Section 1.2, page 73: a rule is applied inside a net). -/
theorem add_right
    -- the rules of the system are linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- the rest of the net
    (Γ : Net S ℕ)
    -- `N` reduces in `n` interactions to `M`
    (h : StepsEN I n N M)
    -- the net one starts from, `N` and `Γ`, is linear
    (hN : (N + Γ).Linear) :
    -- there is a net `M'` such that
    ∃ M',
      -- `N + Γ` reduces to `M' + Γ` in `n` interactions,
      StepsEN I n (N + Γ) (M' + Γ)
      -- `M'` is the same graph as `M`,
      ∧ Equiv M' M
      -- and `M' + Γ` is linear
      ∧ (M' + Γ).Linear := by
  induction h with
  | refl => exact ⟨_, .refl _, Equiv.refl _, hN⟩
  | tail _ hstep ih =>
    obtain ⟨M₁, hs, hE, hl⟩ := ih hN
    obtain ⟨M₂, hs₂, hE₂, hl₂⟩ := (StepE.of_equiv hE hstep).add_right hI Γ hl
    exact ⟨M₂, hs.tail hs₂, hE₂, hl₂⟩

end StepsEN

-- ============================================================================================
-- 3. Auxiliary lemmas: compatibility with bounded lengths
-- ============================================================================================

namespace Translation

/-- A translation with bounded lengths is a translation of interaction systems (Lafont 1997,
Section 1.7, page 80). -/
theorem CompatibleWithin.compatible
    -- a translation from `I` to `I'` whose rules are simulated in `L` to `M` interactions
    {Φ : Translation S S'}
    {I : System S}
    {I' : System S'}
    {L M : ℕ}
    (h : Φ.CompatibleWithin I I' L M) :
    -- it is compatible with reduction
    Φ.Compatible I I' := by
  intro α β r hr xs ys f g hlin
  obtain ⟨M₁, N', h', ⟨k, -, -, hk⟩, hE, hT⟩ := h α β r hr xs ys f g hlin
  exact ⟨M₁, N', h', hk.stepsE, hE, hT⟩

/-- The identity translation of a well-formed system simulates each rule by itself, in one
interaction: `L = M = 1` (Lafont 1997, page 81). -/
theorem id_compatibleWithin
    -- a well-formed system
    (I : System S)
    (hI : I.WellFormed) :
    -- the identity simulates every rule in exactly one interaction
    (Translation.id S).CompatibleWithin I I 1 1 := by
  intro α β r hr xs ys f g hlin
  let L : Sym2 (Term S ℕ) := s(.app α fun i => .var (xs i), .app β fun j => .var (ys j))
  let k : ℕ := (Net.vars ({L} : Net S ℕ)).sup + 1
  have hstep : Step I (L ::ₘ 0)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (fun w => k + w) + 0) :=
    Step.mk α β r hr _ _ 0 (fun w => k + w)
      (fun a b hab => Fin.ext (by simpa using hab))
      (fun w hw => by
        have hle : k + w ≤ (Net.vars ({L} : Net S ℕ)).sup :=
          Multiset.le_sup (show k + (w : ℕ) ∈ Net.vars ({L} : Net S ℕ) from hw)
        omega)
  have hstep' : Step I ({L} : Net S ℕ)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (fun w => k + w)) := by
    simpa using hstep
  refine ⟨_, _, fun w => k + w, ⟨1, le_rfl, le_rfl, StepsEN.single hstep'.stepE⟩,
    Equiv.refl _, ?_, ?_⟩
  · exact Multiset.rel_refl_of_refl_on fun e _ => eqTr_id e
  · exact hstep'.linear hI.linear hlin

/-- **One interaction is simulated in `k` interactions, `L ≤ k ≤ M`** (Lafont 1997,
Proposition 4, page 81, the case of one step). The rules of `I` and of `I'` are linear. -/
theorem CompatibleWithin.step
    -- the two systems, with linear rules
    {I : System S}
    {I' : System S'}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- a translation whose rules are simulated in `L` to `M` interactions
    {Φ : Translation S S'}
    {L M : ℕ}
    (hΦ : Φ.CompatibleWithin I I' L M)
    -- one interaction from `N` to `M₀`, and a translation `N'` of `N`
    {N M₀ : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Step I N M₀)
    (hT : Φ.NetTr N N') :
    -- there are a length `k` and nets `M₁`, `M'` such that
    ∃ k M₁ M',
      -- `N'` reduces up to wires to `M₁` in `k` interactions,
      StepsEN I' k N' M₁
      -- with `L ≤ k ≤ M`,
      ∧ L ≤ k
      ∧ k ≤ M
      -- `M₁` is the same graph as `M'`,
      ∧ Equiv M₁ M'
      -- and `M'` is a translation of `M₀`
      ∧ Φ.NetTr M₀ M' := by
  obtain ⟨M₁, M', ⟨k, hL, hM, hk⟩, hE, hT'⟩ := CompatibleBy.step
    (R := fun N K => ∃ k, L ≤ k ∧ k ≤ M ∧ StepsEN I' k N K) hI hI'
    (fun Γ ⟨k, hL, hM, hk⟩ hl => by
      obtain ⟨M', h1, h2, h3⟩ := hk.add_right hI' Γ hl
      exact ⟨M', ⟨k, hL, hM, h1⟩, h2, h3⟩)
    (fun hE ⟨k, hL, hM, hk⟩ => by
      obtain ⟨M', h1, h2⟩ := hk.of_equiv hE
      exact ⟨M', ⟨k, hL, hM, h1⟩, h2⟩)
    (fun ⟨_, _, _, hk⟩ => hk.stepsE) hΦ h hT
  exact ⟨k, M₁, M', hk, hL, hM, hE, hT'⟩

-- ============================================================================================
-- 4. Main result: Proposition 4
-- ============================================================================================

/-- **Proposition 4** (Lafont 1997, page 81): "If `Θ` is a net built with symbols of `Σ` which
reduces in `n` steps to `Θ'`, then `Φ(Θ)` reduces in `n'` steps to `Φ(Θ')`, with
`L n ≤ n' ≤ M n`." Here `Φ(Θ')` is reached up to equivalence: `N'` reduces up to wires in `n'`
interactions to a net that is the same graph as a translation of `M₀`. The rules of `I` and of
`I'` are linear. -/
theorem CompatibleWithin.steps
    -- the two systems, with linear rules
    {I : System S}
    {I' : System S'}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- a translation whose rules are simulated in `L` to `M` interactions
    {Φ : Translation S S'}
    {L M : ℕ}
    (hΦ : Φ.CompatibleWithin I I' L M)
    -- a reduction in `n` interactions from `N` to `M₀`, and a translation `N'` of `N`
    {n : ℕ}
    {N M₀ : Net S ℕ}
    {N' : Net S' ℕ}
    (h : StepsN I n N M₀)
    (hT : Φ.NetTr N N') :
    -- there are a length `n'` and nets `M₁`, `M'` such that
    ∃ n' M₁ M',
      -- `N'` reduces up to wires to `M₁` in `n'` interactions,
      StepsEN I' n' N' M₁
      -- with `L n ≤ n' ≤ M n`,
      ∧ L * n ≤ n'
      ∧ n' ≤ M * n
      -- `M₁` is the same graph as `M'`,
      ∧ Equiv M₁ M'
      -- and `M'` is a translation of `M₀`
      ∧ Φ.NetTr M₀ M' := by
  induction h with
  | refl => exact ⟨0, N', N', .refl _, by simp, by simp, Equiv.refl _, hT⟩
  | tail _ hs ih =>
    obtain ⟨n', M₁, M', h1, hL1, hM1, e1, t1⟩ := ih hT
    obtain ⟨k, M₂, M'', h2, hL2, hM2, e2, t2⟩ := hΦ.step hI hI' hs t1
    obtain ⟨X, hX, eX⟩ := StepsEN.of_equiv e1 h2
    refine ⟨n' + k, X, M'', h1.trans hX, ?_, ?_, eX.trans e2, t2⟩
    · rw [Nat.mul_succ]; omega
    · rw [Nat.mul_succ]; omega

end Translation

end INet
