/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduction.NormalFormE

/-!
# If a transpositor `T_σ` exists, σ is involutive (page 84)

Lafont 1997, page 84 (PDF page 16), after the property of `T_σ`: "Note that conversely, if such a
`T_σ` exists, the permutation σ is necessarily involutive. This is a consequence of the symmetry
condition."

Two copies of a principal net `p` with `n` ports are plugged by their roots: the ports of the first
copy are the names `0, …, n - 1`, those of the second copy the names `n, …, 2n - 1`. If this net
reduces up to wires to the wiring that joins port `i` of the first copy to port `σ i` of the
second, then σ is involutive (`involutive_of_transpositor`).

The proof is the symmetry of the paper. An equation is unordered, so exchanging the two copies,
that is renaming `i ↔ n + i` and the internal wires of one copy to those of the other
(`swapNames`), gives back the same net. The renaming is injective, so the net also reduces to the
wiring renamed, which is the wiring of `σ⁻¹`. A wiring has no cell, so it is irreducible; the
normal form is unique up to wires (`StepsEN.normal_unique`, pages 73-74), so the wirings of σ and
of `σ⁻¹` are the same graph. Two wirings that are the same graph are equal (`eq_of_equiv_wiring`,
by the solutions where every cell is `true` of `PairStepE`), so `σ = σ⁻¹`.

The statement holds in any well-formed interaction system, the combinators included.

Contents, in the order of the file:

1. Definitions: `wiring`, the wiring σ of page 84; `swapNames`, the renaming that exchanges the
   two copies.
2. Auxiliary lemmas on wirings: `sum_ite_add`, `count_vars_wiring` (every name below `2n` occurs
   once), `eq_of_equiv_wiring` (two wirings that are the same graph are equal), `normal_wiring`
   (a wiring is irreducible), `wiring_bind` (the wiring σ, copies exchanged, is the wiring `σ⁻¹`).
3. Auxiliary lemmas on exchanging the two copies: `swapNames_lt`, `swapNames_add`,
   `swapNames_f`, `swapNames_g`, `swapNames_involutive`.
4. Auxiliary lemmas on the names of an instance: `mem_vars_inst_port`, `mem_vars_inst_wire`,
   `inst_bind_var`.
5. Main result: `involutive_of_transpositor`, the converse of page 84.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

namespace TranspositorConverse

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- The wiring σ of page 84: the name `i` (port `i` of the first copy) joined to the name
`n + σ i` (port `σ i` of the second copy). -/
def wiring
    -- the number of ports of each copy
    (n : ℕ)
    -- the permutation
    (σ : Equiv.Perm (Fin n)) :
    Net S ℕ :=
  Finset.univ.val.map fun i : Fin n => s(var (i : ℕ), var (n + (σ i : ℕ)))

open Classical in
/-- Exchanging the two copies of page 84: the port `i` of the first copy with the port `n + i` of
the second, and the internal wire `f w` of the first copy with the internal wire `g w` of the
second. Every other name is fixed. -/
noncomputable def swapNames
    -- the number of ports of each copy
    (n : ℕ)
    -- the names of the internal wires of the first copy (`f`) and of the second (`g`)
    {k : ℕ}
    (f g : Fin k → ℕ)
    -- the name to rename
    (x : ℕ) :
    ℕ :=
  if x < n then n + x else if x < 2 * n then x - n else
    if h : ∃ w, f w = x then g h.choose else if h : ∃ w, g w = x then f h.choose else x

-- ============================================================================================
-- 2. Auxiliary lemmas: wirings
-- ============================================================================================

/-- Among the names `k + i`, `i < n`, the name `z` occurs once if `k ≤ z < k + n`, else never. -/
theorem sum_ite_add
    -- the number of names
    {n : ℕ}
    -- the first name `k`, and the name `z` counted
    (k z : ℕ) :
    (∑ i : Fin n, if z = k + (i : ℕ) then 1 else 0)
      = if k ≤ z ∧ z < k + n then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨z - k, by omega⟩]
    · simp only [ite_eq_left_iff]
      omega
    · intro b _ hb
      refine ite_eq_right_iff.2 fun e => absurd (Fin.ext ?_) hb
      simp only
      omega
    · simp
  · exact Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun e => by omega

/-- Every name below `2n` occurs once in the wiring σ, and no other name occurs. -/
theorem count_vars_wiring
    -- the permutation
    {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    -- the name counted
    (z : ℕ) :
    (wiring (S := S) n σ).vars.count z = if z < 2 * n then 1 else 0 := by
  unfold wiring Net.vars
  rw [Multiset.bind_map, Multiset.count_bind]
  change ∑ i : Fin n, _ = _
  simp only [eqVars_mk, Term.vars_var, Multiset.count_add, Multiset.count_singleton]
  rw [Finset.sum_add_distrib,
    Equiv.sum_comp σ (fun i : Fin n => if z = n + (i : ℕ) then 1 else 0)]
  have h0 := sum_ite_add (n := n) 0 z
  simp only [zero_add] at h0
  rw [h0, sum_ite_add]
  split_ifs <;> omega

/-- **Two wirings that are the same graph are equal.** If the wirings of σ and τ (page 84) are
`Equiv`, then `σ = τ`. Each name below `2n` is a free port of both, and `Equiv` keeps the values on
the free names that extend to a solution where every cell is `true` (`PairStepE.BlindSol`): giving
the value `true` exactly to `i` and `n + σ i` solves the wiring σ, so it solves the wiring τ, whose
wire from `i` ends at `n + τ i`. -/
theorem eq_of_equiv_wiring
    -- the two permutations
    {n : ℕ}
    {σ τ : Equiv.Perm (Fin n)}
    -- their wirings are the same graph
    (h : Equiv (wiring (S := S) n σ) (wiring n τ)) :
    σ = τ := by
  ext i
  let s : ℕ → Bool := fun y => decide (y = i ∨ y = n + σ i)
  have hsol : PairStepE.BlindSol (wiring (S := S) n σ) s := by
    refine ⟨s, fun a b hab => ?_, fun _ _ => rfl⟩
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hab
    have key : s j = s (n + σ j) := by
      simp only [s, decide_eq_decide]
      constructor
      · rintro (e | e)
        · obtain rfl : j = i := Fin.ext e
          exact Or.inr rfl
        · omega
      · rintro (e | e)
        · omega
        · have : σ j = σ i := Fin.ext (by omega)
          exact Or.inl (by rw [σ.injective this])
    rcases Sym2.eq_iff.1 hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key
    · exact key.symm
  obtain ⟨ρ, hs, hp⟩ := (PairStepE.Equiv.blindSol_iff h s).1 hsol
  have hmem : s(var (i : ℕ), var (n + (τ i : ℕ))) ∈ (wiring (S := S) n τ) :=
    Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩
  have e := hs _ _ hmem
  rw [PairStepE.blind_var, PairStepE.blind_var,
    hp _ (by rw [count_vars_wiring, ite_eq_left_iff.2 fun h => absurd (by omega) h]),
    hp _ (by rw [count_vars_wiring, ite_eq_left_iff.2 fun h => absurd (by omega) h])] at e
  simp only [s, true_or, decide_true, Nat.add_left_cancel_iff, Fin.val_inj] at e
  symm at e
  simp only [decide_eq_true_eq] at e
  rcases e with e | e
  · omega
  · rw [e]

/-- **A wiring is irreducible** (page 73). A wiring has no cell, and an interaction needs two. -/
theorem normal_wiring
    -- the interaction system
    (I : System S)
    -- the permutation
    {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    StepE.Normal I (wiring (S := S) n σ) := by
  rintro M ⟨N', hE, hs⟩
  have hc := hE.cells_eq
  have h0 : Net.cells (wiring (S := S) n σ) = 0 := by
    refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
    obtain ⟨e, he, hx⟩ := Multiset.mem_bind.1 hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 he
    simp at hx
  obtain ⟨α, β, r, hr, as, bs, Δ, f, hf, hfresh⟩ := hs
  rw [h0, Net.cells_cons, eqCells_mk, Term.cells_app] at hc
  simp at hc

/-- The wiring σ renamed by exchanging `i` and `n + i` is the wiring `σ⁻¹`. -/
theorem wiring_bind
    -- the permutation
    {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    -- a renaming that exchanges the port `i` of the first copy and the port `n + i` of the second
    (π : ℕ → ℕ)
    (h1 : ∀ i < n, π i = n + i)
    (h2 : ∀ i < n, π (n + i) = i) :
    (wiring (S := S) n σ).bind (fun y => var (π y)) = wiring n σ⁻¹ := by
  unfold wiring Net.bind
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_univ_val_equiv σ, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  have hσ : σ⁻¹ (σ i) = i := by simp
  simp only [Function.comp_apply, Sym2.map_mk, Term.bind, h1 i i.2, h2 _ (σ i).2, hσ]
  exact Sym2.eq_swap

-- ============================================================================================
-- 3. Auxiliary lemmas: exchanging the two copies
-- ============================================================================================

section swapNames

variable
    -- the number of ports of each copy, and the names of the internal wires of the two copies
    {n k : ℕ}
    {f g : Fin k → ℕ}

/-- A port of the first copy goes to the same port of the second. -/
theorem swapNames_lt
    -- a port of the first copy
    {x : ℕ}
    (hx : x < n) :
    swapNames n f g x = n + x := by
  simp [swapNames, hx]

/-- A port of the second copy goes to the same port of the first. -/
theorem swapNames_add
    -- a port of the second copy
    {i : ℕ}
    (hi : i < n) :
    swapNames n f g (n + i) = i := by
  unfold swapNames
  split_ifs <;> omega

variable
    -- the names of the internal wires of each copy are distinct,
    (hf : Function.Injective f)
    (hg : Function.Injective g)
    -- they are not ports,
    (hf2 : ∀ w, 2 * n ≤ f w)
    (hg2 : ∀ w, 2 * n ≤ g w)
    -- and the two copies have no internal wire in common
    (hfg : ∀ w w', f w ≠ g w')

include hf hf2 in
/-- The internal wire `f w` of the first copy goes to the wire `g w` of the second. -/
theorem swapNames_f
    -- an internal wire
    (w : Fin k) :
    swapNames n f g (f w) = g w := by
  have := hf2 w
  unfold swapNames
  split_ifs with h1 h2 h3
  · omega
  · omega
  · exact congrArg g (hf h3.choose_spec)
  · exact absurd ⟨w, rfl⟩ h3
  · exact absurd ⟨w, rfl⟩ h3

include hg hg2 hfg in
/-- The internal wire `g w` of the second copy goes to the wire `f w` of the first. -/
theorem swapNames_g
    -- an internal wire
    (w : Fin k) :
    swapNames n f g (g w) = f w := by
  have := hg2 w
  unfold swapNames
  split_ifs with h1 h2 h3 h4
  · omega
  · omega
  · exact absurd h3.choose_spec (hfg _ w)
  · exact congrArg f (hg h4.choose_spec)
  · exact absurd ⟨w, rfl⟩ h4

include hf hg hf2 hg2 hfg in
/-- Exchanging the two copies twice changes nothing. -/
theorem swapNames_involutive :
    Function.Involutive (swapNames n f g) := by
  intro x
  by_cases h1 : x < n
  · rw [swapNames_lt h1, swapNames_add h1]
  by_cases h2 : x < 2 * n
  · have e : x = n + (x - n) := by omega
    conv_lhs => rw [e]
    rw [swapNames_add (by omega), swapNames_lt (by omega)]
    omega
  by_cases h3 : ∃ w, f w = x
  · obtain ⟨w, rfl⟩ := h3
    rw [swapNames_f hf hf2, swapNames_g hg hg2 hfg]
  by_cases h4 : ∃ w, g w = x
  · obtain ⟨w, rfl⟩ := h4
    rw [swapNames_g hg hg2 hfg, swapNames_f hf hf2]
  have e : swapNames n f g x = x := by
    unfold swapNames
    split_ifs
    omega
  rw [e, e]

end swapNames

-- ============================================================================================
-- 4. Auxiliary lemmas: the names of an instance
-- ============================================================================================

/-- The names of a tree plugged into a port of an instance are names of the instance. -/
theorem mem_vars_inst_port
    -- the principal net, the trees on its ports and the names of its internal wires
    {n : ℕ}
    (p : PNet S n)
    (args : Fin n → Term S ℕ)
    (F : Fin p.internal → ℕ)
    -- a name of the tree on the port `i`
    (i : Fin n)
    {y : ℕ}
    (hy : y ∈ (args i).vars) :
    y ∈ (p.inst args F).vars := by
  rw [PNet.inst, Term.vars_bind]
  exact Multiset.mem_bind.2 ⟨.inl i, Multiset.count_pos.1 (by rw [p.port_count]; omega), hy⟩

/-- Every internal wire of an instance is a name of the instance. -/
theorem mem_vars_inst_wire
    -- the principal net, the trees on its ports and the names of its internal wires
    {n : ℕ}
    (p : PNet S n)
    (args : Fin n → Term S ℕ)
    (F : Fin p.internal → ℕ)
    -- an internal wire
    (w : Fin p.internal) :
    F w ∈ (p.inst args F).vars := by
  rw [PNet.inst, Term.vars_bind]
  exact Multiset.mem_bind.2 ⟨.inr w, Multiset.count_pos.1 (by rw [p.internal_count]; omega),
    by simp⟩

/-- An instance of a principal net with names on its ports, renamed. -/
theorem inst_bind_var
    -- the principal net, the names on its ports and the names of its internal wires
    {n : ℕ}
    (p : PNet S n)
    (xs : Fin n → ℕ)
    (F : Fin p.internal → ℕ)
    -- the renaming
    (π : ℕ → ℕ) :
    -- renaming the instance is renaming the names on its ports and of its internal wires
    (p.inst (fun i => var (xs i)) F).bind (fun y => var (π y))
      = p.inst (fun i => var (π (xs i))) (fun w => π (F w)) := by
  rw [PNet.inst, PNet.inst, Term.bind_bind]
  congr 1
  funext q
  cases q <;> rfl

end TranspositorConverse

open TranspositorConverse

-- ============================================================================================
-- 5. Main result: the converse of page 84
-- ============================================================================================

/-- **Conversely, if a transpositor `T_σ` exists, σ is involutive** (Lafont 1997, page 84: "Note
that conversely, if such a `T_σ` exists, the permutation σ is necessarily involutive. This is a
consequence of the symmetry condition."). Let `I` be a well-formed interaction system and `p` a
principal net with `n` ports. Take two copies of `p` plugged by their roots, the ports of the
first copy named `0, …, n - 1`, those of the second `n, …, 2n - 1`, and the internal wires named by
`f` and `g` so that the net is linear. If this net reduces up to wires to a net that is the same
graph as the wiring joining port `i` of the first copy to port `σ i` of the second, then σ is
involutive. -/
theorem involutive_of_transpositor
    -- a well-formed interaction system
    {I : System S}
    (hI : I.WellFormed)
    -- the principal net `p` with `n` ports, and the permutation σ
    {n : ℕ}
    (p : PNet S n)
    (σ : _root_.Equiv.Perm (Fin n))
    -- the names of the internal wires of the first copy (`f`) and of the second (`g`)
    (f g : Fin p.internal → ℕ)
    -- the two copies plugged by their roots form a linear net
    (hlin : Net.Linear
      (s(p.inst (fun i => var (i : ℕ)) f, p.inst (fun i => var (n + (i : ℕ))) g) ::ₘ 0))
    -- the two copies reduce, up to wires, to a net `M` that is the same graph as the wiring σ
    (h : ∃ M, StepsE I
        (s(p.inst (fun i => var (i : ℕ)) f, p.inst (fun i => var (n + (i : ℕ))) g) ::ₘ 0) M ∧
      Equiv M (Finset.univ.val.map fun i : Fin n => s(var (i : ℕ), var (n + (σ i : ℕ))))) :
    -- σ is involutive
    Function.Involutive σ := by
  set A := p.inst (fun i => var (i : ℕ)) f with hA
  set B := p.inst (fun i => var (n + (i : ℕ))) g with hB
  -- The names of the internal wires are distinct and are not ports.
  obtain ⟨hg, hgA⟩ := PNet.facts_of_linear (r := A) hlin
  have hlin' : Net.Linear (s(B, A) ::ₘ 0) := by rwa [Sym2.eq_swap]
  obtain ⟨hf, hfB⟩ := PNet.facts_of_linear (r := B) hlin'
  have hf2 : ∀ w, 2 * n ≤ f w := by
    intro w
    by_contra hlt
    by_cases h1 : f w < n
    · exact (hfB w).2.1 ⟨f w, h1⟩ (by simp)
    · refine (hfB w).1 (mem_vars_inst_port p _ g ⟨f w - n, by omega⟩ ?_)
      simp only [Term.vars_var, Multiset.mem_singleton]
      omega
  have hg2 : ∀ w, 2 * n ≤ g w := by
    intro w
    by_contra hlt
    by_cases h1 : f w < n ∨ g w < n
    · rcases h1 with h1 | h1
      · exact absurd (hf2 w) (by omega)
      · exact (hgA w).1 (mem_vars_inst_port p _ f ⟨g w, h1⟩ (by simp))
    · refine (hgA w).2.1 ⟨g w - n, by omega⟩ ?_
      simp only [Term.vars_var, Multiset.mem_singleton]
      omega
  have hfg : ∀ w w', f w ≠ g w' := fun w w' e =>
    (hfB w).1 (e ▸ mem_vars_inst_wire p _ g w')
  -- Exchanging the two copies gives back the same net.
  set π := swapNames n f g with hπ
  have hinj : Function.Injective π := (swapNames_involutive hf hg hf2 hg2 hfg).injective
  have hbind : Net.bind (fun y => var (π y)) (s(A, B) ::ₘ 0) = s(A, B) ::ₘ 0 := by
    rw [Net.bind_cons, hA, hB, inst_bind_var p (fun i => (i : ℕ)) f π,
      inst_bind_var p (fun i => n + (i : ℕ)) g π]
    have e1 : (fun i : Fin n => var (π i)) = fun i : Fin n => (var (n + (i : ℕ)) : Term S ℕ) := by
      funext i
      rw [hπ, swapNames_lt i.2]
    have e2 : (fun i : Fin n => var (π (n + i))) = fun i : Fin n => (var (i : ℕ) : Term S ℕ) := by
      funext i
      rw [hπ, swapNames_add i.2]
    have e3 : (fun w => π (f w)) = g := funext fun w => by rw [hπ, swapNames_f hf hf2]
    have e4 : (fun w => π (g w)) = f := funext fun w => by
      rw [hπ, swapNames_g hg hg2 hfg]
    rw [e1, e2, e3, e4, Sym2.eq_swap]
    rfl
  -- Both reductions end at a wiring, which is irreducible.
  obtain ⟨M, hs, hE⟩ := h
  change Equiv M (wiring n σ) at hE
  obtain ⟨k, hk⟩ := hs.exists_stepsEN
  have hk' := hk.bind_var π hinj
  rw [hbind] at hk'
  have hE' := hE.bind_var π hinj
  rw [wiring_bind σ π (fun i hi => swapNames_lt hi) (fun i hi => swapNames_add hi)] at hE'
  have hM := (normal_wiring I σ).of_equiv hE.symm
  have hM' := (normal_wiring I σ⁻¹).of_equiv hE'.symm
  obtain ⟨-, hMM⟩ := StepsEN.normal_unique hI hlin hM hM' hk hk'
  have hσ := eq_of_equiv_wiring (hE.symm.trans (hMM.trans hE'))
  intro i
  have h2 := DFunLike.congr_fun hσ (σ i)
  rw [h2]
  simp

end INet
