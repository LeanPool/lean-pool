/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.RecursionFree
public import LeanPool.InteractionCombinators.Reduction.RuleInstances
public import LeanPool.InteractionCombinators.Text.NetTrWire

/-!
# A translation of an instance of `Rule.plug φ ψ σ` is a translation of an instance of `r`

Lafont 1997, page 85: the right-hand side of the rule `r` for `α_i`, `α_j` is the net `φ_{i,j}`
plugged to `ψ_{i,j}` through `σ_{i,j}`; page 80: a translation of interaction systems asks that
the translations of the two cells reduce to a translation of the right-hand side.

`mux_gamma_mux_gamma_netTr` (`PlugTr.lean`) ends Fig. 7 with a translation of an instance of
`Rule.plug φ ψ σ`, while `Translation.Compatible` asks for a translation of an instance of `r`.
`Decomposition.Plugs` links the two: an injective renaming `ι` of the internal wires of `r` and an
`Equiv` of the two right-hand sides. This file moves the translation along that link.

Contents, in the order of the file:

1. Auxiliary lemma: `Rule.equiv_inst_of_equiv_rename`, equivalent right-hand sides give
   equivalent instances.
2. Auxiliary lemma: `Translation.NetTr.inst_of_equiv_rename`, a `NetTr` moves along the `Equiv`.
3. Main results: `Decomposition.Plugs.netTr_inst`, the same for a decomposition that plugs into
   `r`, and `Decomposition.Plugs.netTr_inst_of_sides`, with the linearity of the plugged rule
   obtained from that of its two sides.
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemma: equivalent right-hand sides give equivalent instances
-- ============================================================================================

namespace Rule

variable {a b : ℕ}

/-- **Equivalent right-hand sides give equivalent instances** (Lafont 1997, pages 80 and 85: a
right-hand side is a graph, plugged into the net by its ports). If the net of `P` is equivalent to
the net of `r` with its internal wires renamed by `ι`, then the instance of `P` with names `xs`,
`ys` on the ports and `h` on the internal wires is equivalent to the instance of `r` with the same
ports and `h ∘ ι` on the internal wires, provided the instance of `P` is linear. -/
theorem equiv_inst_of_equiv_rename
    -- two rules with the same ports; `P` is linear
    (P r : Rule S a b)
    (hP : P.Linear)
    -- a renaming of the internal wires of `r` into those of `P`, under which the nets of the
    -- two rules are equivalent
    (ι : Fin r.internal → Fin P.internal)
    (hE : Equiv P.net (r.net.bind fun x => var (Sum.map id (Sum.map id ι) x)))
    -- the names of the ports and of the internal wires of `P`
    (xs : Fin a → ℕ)
    (ys : Fin b → ℕ)
    (h : Fin P.internal → ℕ)
    -- the instance of `P` with these names is linear
    (hlin : (P.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h).Linear) :
    -- the instance of `P` is equivalent to the instance of `r` with the same ports and `h ∘ ι`
    -- on the internal wires
    Equiv (P.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (h ∘ ι)) := by
  have hL : ∀ y, ∑ i, (Term.var (S := S) (xs i)).vars.count y +
      ∑ j, (Term.var (S := S) (ys j)).vars.count y +
      2 * (∑ w, if y = h w then 1 else 0) + (0 : Net S ℕ).vars.count y ≤ 2 := by
    intro y
    have := hlin y
    rw [count_vars_inst P hP] at this
    simpa using this
  have E := equiv_bind_args hE (portShape_net P hP) (fun i => .var (xs i))
    (fun j => .var (ys j)) h 0 hL
  simp only [add_zero] at E
  refine E.trans (Equiv.of_eq ?_)
  rw [Net.bind_bind]
  change r.net.bind _ = r.net.bind _
  congr 1
  funext x
  rcases x with i | j | w <;> rfl

end Rule

-- ============================================================================================
-- 2. Auxiliary lemma: a translation moves along equivalent right-hand sides
-- ============================================================================================

namespace Translation

variable {Φ : Translation S S'}

/-- **A translation moves along equivalent right-hand sides** (Lafont 1997, pages 80 and 85). If
the net of `P` is equivalent to the net of `r` with its internal wires renamed by `ι`,
then a translation `N'` of an instance of `P` is equivalent to a translation of an instance of `r`
with the same names on the ports. -/
theorem NetTr.inst_of_equiv_rename
    -- two rules with the same ports; `P` is linear
    {a b : ℕ}
    (P r : Rule S a b)
    (hP : P.Linear)
    -- a renaming of the internal wires of `r` into those of `P`, under which the nets of the
    -- two rules are equivalent
    (ι : Fin r.internal → Fin P.internal)
    (hE : Equiv P.net (r.net.bind fun x => var (Sum.map id (Sum.map id ι) x)))
    -- the names of the ports and of the internal wires of `P`
    (xs : Fin a → ℕ)
    (ys : Fin b → ℕ)
    (h : Fin P.internal → ℕ)
    -- a translation `N'` of the instance of `P` with these names
    {N' : Net S' ℕ}
    (hN : Φ.NetTr (P.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N') :
    -- there are names `h'` for the internal wires of `r` and a net `N''`
    ∃ (h' : Fin r.internal → ℕ) (N'' : Net S' ℕ),
      -- `N''` is a translation of the instance of `r` with the same ports
      Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h') N''
      -- and is equivalent to `N'`
      ∧ Equiv N' N'' := by
  have E := Rule.equiv_inst_of_equiv_rename P r hP ι hE xs ys h hN.linear_source
  obtain ⟨N'', hN'', e⟩ := hN.of_equiv E
  exact ⟨h ∘ ι, N'', hN'', e⟩

end Translation

-- ============================================================================================
-- 3. Main results: a translation of the plugged sides is a translation of the rule
-- ============================================================================================

namespace Decomposition

variable {a b : ℕ}

/-- **A translation of an instance of the plugged sides is a translation of an instance of the
rule** (Lafont 1997, page 85: the right-hand side of `r` is `φ` plugged to `ψ` through `σ`; page
80: the translation of interaction systems). If `D` plugs into `r` and the plugged rule is linear,
a translation `N'` of an instance of `Rule.plug D.φ D.ψ D.σ` is equivalent to a translation of an
instance of `r` with the same names on the ports. -/
theorem Plugs.netTr_inst
    -- a decomposition `D` that plugs into the rule `r`
    {D : Decomposition S a b}
    {r : Rule S a b}
    (hD : D.Plugs r)
    -- the plugged rule is linear
    (hP : (Rule.plug D.φ D.ψ D.σ).Linear)
    -- a translation, and the names of the ports and of the internal wires of the plugged rule
    {Φ : Translation S S'}
    (xs : Fin a → ℕ)
    (ys : Fin b → ℕ)
    (h : Fin (Rule.plug D.φ D.ψ D.σ).internal → ℕ)
    -- a translation `N'` of the instance of the plugged rule with these names
    {N' : Net S' ℕ}
    (hN : Φ.NetTr
      ((Rule.plug D.φ D.ψ D.σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N') :
    -- there are names `h'` for the internal wires of `r` and a net `N''`
    ∃ (h' : Fin r.internal → ℕ) (N'' : Net S' ℕ),
      -- `N''` is a translation of the instance of `r` with the same ports
      Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h') N''
      -- and is equivalent to `N'`
      ∧ Equiv N' N'' := by
  obtain ⟨ι, -, hE⟩ := hD
  exact Translation.NetTr.inst_of_equiv_rename _ r hP ι hE xs ys h hN

/-- `Plugs.netTr_inst` with the linearity of the plugged rule obtained from that of the two sides
(`Rule.plug_linear`), as `System.RecursionFreeData.linear` supplies it (Lafont 1997, pages 85 and
80). -/
theorem Plugs.netTr_inst_of_sides
    -- a decomposition `D` that plugs into the rule `r`
    {D : Decomposition S a b}
    {r : Rule S a b}
    (hD : D.Plugs r)
    -- the two sides of `D` are linear
    (hφ : D.φ.Linear)
    (hψ : D.ψ.Linear)
    -- a translation, and the names of the ports and of the internal wires of the plugged rule
    {Φ : Translation S S'}
    (xs : Fin a → ℕ)
    (ys : Fin b → ℕ)
    (h : Fin (Rule.plug D.φ D.ψ D.σ).internal → ℕ)
    -- a translation `N'` of the instance of the plugged rule with these names
    {N' : Net S' ℕ}
    (hN : Φ.NetTr
      ((Rule.plug D.φ D.ψ D.σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N') :
    -- there are names `h'` for the internal wires of `r` and a net `N''`
    ∃ (h' : Fin r.internal → ℕ) (N'' : Net S' ℕ),
      -- `N''` is a translation of the instance of `r` with the same ports
      Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h') N''
      -- and is equivalent to `N'`
      ∧ Equiv N' N'' :=
  hD.netTr_inst (Rule.plug_linear D.σ hφ hψ) xs ys h hN

end Decomposition

end INet
