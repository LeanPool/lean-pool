/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.SimulationCount
public import LeanPool.InteractionCombinators.Reduced.CutChain

/-!
# A strict translation simulates every interaction in at least one step

Lafont 1997, page 81, after Proposition 4: "`L > 0` if `Φ` is strict". The left member of a rule
is a cut, and a strict translation keeps it a cut. The right member has no cut, and a
translation of a net without a cut has none (Proposition 3, page 80). So the two translations
are not the same graph, and the reduction from one to the other is not empty.

The definition of `Translation.Compatible` lets the names `xs`, `ys` on the ports of the two
cells be equal. Then the second point fails: with the identity translation and the rule
`α β ↦ {x₀ = α(w), y₀ = β(w)}`, the net `α(z) = β(z)` (`xs 0 = ys 0 = z`) is already the same
graph as the right member. The paper has distinct names, and `not_equiv_pair_of_strict` assumes
them. `CompatibleWithin.pos` holds for all names, because Proposition 4 only uses the rule with
fresh distinct names (`Translation.CompatibleByDistinct.step`), and a pair with equal names is
simulated through one with distinct names.

Contents, in the order of the file:

1. Auxiliary lemmas, the right member of a rule has no cut: `Rule.Reduced.mem_inst` (every
   equation of an instance has a port name on one side), `Rule.count_inst_port` (the port names
   occur once), `Rule.not_hasCut_inst` (an instance of a linear reduced rule, with distinct names
   on the ports, has no cut).
2. Auxiliary lemmas, a strict translation keeps the cut: `Translation.hasCut_pair` (the
   translations of two cells by a strict `Φ`, plugged by their roots, form a cut),
   `Translation.not_equiv_pair_of_strict` (they are not the same graph as a translation of the
   right member: a simulating reduction is never empty),
   `Translation.CompatibleWithin.distinct_pos` (`L` can be raised to `max L 1` for distinct names).
3. Main result: `Translation.CompatibleWithin.pos`, `L` can be raised to `max L 1` (page 81).
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term

namespace Rule

variable {a b : ℕ}

-- ============================================================================================
-- 1. Auxiliary lemmas: the right member of a rule has no cut
-- ============================================================================================

/-- **An equation of an instance of a reduced rule** has, on one side, one of the names put on
the ports (Lafont 1997, page 79: the right member is a reduced net). -/
theorem Reduced.mem_inst
    -- a reduced rule
    {r : Rule S a b}
    (hr : r.Reduced)
    -- the names on the ports, the names of the internal wires, and an equation of the instance
    {xs : Fin a → ℕ}
    {ys : Fin b → ℕ}
    {h : Fin r.internal → ℕ}
    {e : Sym2 (Term S ℕ)}
    (he : e ∈ r.inst (fun i => var (xs i)) (fun j => var (ys j)) h) :
    -- the equation is `p = t`, where `p` is the name on one of the ports
    ∃ p t, e = s(var p, t) ∧ ((∃ i, p = xs i) ∨ ∃ j, p = ys j) := by
  rw [Rule.inst, Net.bind, Multiset.mem_map] at he
  obtain ⟨e₀, he₀, rfl⟩ := he
  obtain ⟨p, t, rfl, hp⟩ := hr e₀ he₀
  rcases p with i | j | w
  · exact ⟨xs i, _, rfl, Or.inl ⟨i, rfl⟩⟩
  · exact ⟨ys j, _, rfl, Or.inr ⟨j, rfl⟩⟩
  · exact absurd rfl (hp w)

/-- **The ports of an instance are free** (Lafont 1997, page 73). In a linear instance of a
linear rule, with distinct names on the ports, each of these names occurs once. -/
theorem count_inst_port
    -- a linear rule
    {r : Rule S a b}
    (hrl : r.Linear)
    -- distinct names on the ports
    {xs : Fin a → ℕ}
    {ys : Fin b → ℕ}
    (hx : Function.Injective xs)
    (hy : Function.Injective ys)
    (hxy : ∀ i j, xs i ≠ ys j)
    -- the names of the internal wires, such that the instance is linear
    {h : Fin r.internal → ℕ}
    (hl : (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).Linear)
    -- the name on one of the ports
    {p : ℕ}
    (hp : (∃ i, p = xs i) ∨ ∃ j, p = ys j) :
    -- it occurs at most once in the instance
    (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).vars.count p ≤ 1 := by
  have h2 := hl p
  rw [count_vars_inst r hrl] at h2 ⊢
  simp only [vars_var, Multiset.count_singleton] at h2 ⊢
  rcases hp with ⟨i₀, rfl⟩ | ⟨j₀, rfl⟩
  · have e1 : (∑ i, if xs i₀ = xs i then 1 else 0) = 1 := by
      simp only [hx.eq_iff, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have e2 : (∑ j, if xs i₀ = ys j then 1 else 0) = 0 := by simp [hxy]
    omega
  · have e1 : (∑ j, if ys j₀ = ys j then 1 else 0) = 1 := by
      simp only [hy.eq_iff, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have e2 : (∑ i, if ys j₀ = xs i then 1 else 0) = 0 := by
      simp [fun i => (hxy i j₀).symm]
    omega

/-- **The right member of a rule has no cut** (Lafont 1997, page 79: it is a reduced net). An
instance of a linear reduced rule, linear, with distinct names on the ports, has no cut: a cut
would be a chain of wires `a = z₁, …, zₖ = b` between two cells, and every equation of the
instance has a free port on one side, which can be neither a cell nor a link `zᵢ` of the
chain. -/
theorem not_hasCut_inst
    -- a linear reduced rule
    {r : Rule S a b}
    (hrl : r.Linear)
    (hr : r.Reduced)
    -- distinct names on the ports
    {xs : Fin a → ℕ}
    {ys : Fin b → ℕ}
    (hx : Function.Injective xs)
    (hy : Function.Injective ys)
    (hxy : ∀ i j, xs i ≠ ys j)
    -- the names of the internal wires, such that the instance is linear
    {h : Fin r.internal → ℕ}
    (hl : (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).Linear) :
    -- the instance has no cut
    ¬ (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).HasCut := by
  intro hc
  obtain ⟨A, B, zs, D, hA, hB, hN⟩ := hc.chainCut
  cases zs with
  | nil =>
    have hm : s(A, B) ∈ r.inst (fun i => var (xs i)) (fun j => var (ys j)) h := by
      rw [hN]; simp
    obtain ⟨p, t, he, -⟩ := hr.mem_inst hm
    rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact Cut.not_isCell_var p hA
    · exact Cut.not_isCell_var p hB
  | cons z zs =>
    have hm : s(A, var z) ∈ r.inst (fun i => var (xs i)) (fun j => var (ys j)) h := by
      rw [hN]; simp
    obtain ⟨p, t, he, hp⟩ := hr.mem_inst hm
    rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨-, hz⟩
    · exact Cut.not_isCell_var p hA
    · cases hz
      have h1 := count_inst_port hrl hx hy hxy hl hp
      rw [hN, Net.vars_add, Multiset.count_add, Cut.count_vars_chain] at h1
      simp only [List.count_cons_self] at h1
      omega

end Rule

namespace Translation

variable {Φ : Translation S S'}

-- ============================================================================================
-- 2. Auxiliary lemmas: a strict translation keeps the cut
-- ============================================================================================

/-- **The translation of a cut by a strict translation is a cut** (Lafont 1997, page 80, second
point of the proof of Proposition 3, for the left member of a rule): the translations of two
cells by a strict `Φ`, plugged by their roots, have a cell on each side. -/
theorem hasCut_pair
    -- a strict translation
    (hΦ : Φ.Strict)
    -- two symbols, and the names on their auxiliary ports
    (α β : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (ys : Fin (S.arity β) → ℕ)
    -- the names of the internal wires of the two translations
    (f : Fin (Φ.net α).internal → ℕ)
    (g : Fin (Φ.net β).internal → ℕ) :
    -- the two translations, plugged by their roots, form a cut
    Net.HasCut ({s((Φ.net α).inst (fun i => .var (xs i)) f,
      (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) := by
  obtain ⟨γ, us, hγ⟩ := (hΦ α).inst_eq_app (fun i => .var (xs i)) f
  obtain ⟨δ, vs, hδ⟩ := (hΦ β).inst_eq_app (fun j => .var (ys j)) g
  rw [hγ, hδ]
  exact Net.hasCut_of_mem (Multiset.mem_singleton_self _)

/-- **A strict translation never simulates an interaction by an empty reduction** (Lafont 1997,
page 81: "`L > 0` if `Φ` is strict"). Let `Φ` be strict and `I` well-formed, `r` the rule of
`α`, `β`, and `xs`, `ys` distinct names. The translations of the two cells, plugged by their
roots, are not the same graph as a translation `N'` of the right member of `r`: the first net
has a cut (`hasCut_pair`), and `N'` has none, since the right member has none
(`Rule.not_hasCut_inst`) and a translation reflects cuts (Proposition 3, page 80). -/
theorem not_equiv_pair_of_strict
    -- a strict translation of a well-formed system
    {I : System S}
    (hΦ : Φ.Strict)
    (hI : I.WellFormed)
    -- the rule of `α` and `β`
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (hr : I.rule α β = some r)
    -- distinct names on the auxiliary ports
    {xs : Fin (S.arity α) → ℕ}
    {ys : Fin (S.arity β) → ℕ}
    (hx : Function.Injective xs)
    (hy : Function.Injective ys)
    (hxy : ∀ i j, xs i ≠ ys j)
    -- the names of the internal wires of the two translations
    (f : Fin (Φ.net α).internal → ℕ)
    (g : Fin (Φ.net β).internal → ℕ)
    -- a translation `N'` of an instance of the right member of `r`
    {h : Fin r.internal → ℕ}
    {N' : Net S' ℕ}
    (hT : Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N') :
    -- the two translations, plugged by their roots, are not the same graph as `N'`
    ¬ Equiv ({s((Φ.net α).inst (fun i => .var (xs i)) f,
      (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) N' := fun e =>
  Rule.not_hasCut_inst (hI.linear _ _ _ hr) (hI.reduced _ _ _ hr) hx hy hxy hT.linear_source
    (hT.hasCut_reflect ((hasCut_pair hΦ α β xs ys f g).of_equiv e))

/-- With distinct names on the ports, a strict translation compatible within `L` and `M` is
compatible within `max L 1` and `M`: the reduction of length `0` is excluded by
`not_equiv_pair_of_strict` (Lafont 1997, page 81). -/
theorem CompatibleWithin.distinct_pos
    -- the two systems and the bounds
    {I : System S}
    {I' : System S'}
    {L M : ℕ}
    -- `Φ` is strict, `I` is well-formed, and `Φ` simulates every rule in `L` to `M` interactions
    (hΦ : Φ.Strict)
    (hI : I.WellFormed)
    (h : Φ.CompatibleWithin I I' L M) :
    -- for distinct names on the ports, every rule is simulated in `max L 1` to `M` interactions
    Φ.CompatibleByDistinct I fun N K => ∃ k, max L 1 ≤ k ∧ k ≤ M ∧ StepsEN I' k N K := by
  intro α β r hr xs ys f g hx hy hxy hl
  obtain ⟨M₁, N', h₁, ⟨k, hL, hM, hk⟩, hE, hT⟩ := h α β r hr xs ys f g hl
  refine ⟨M₁, N', h₁, ⟨k, max_le hL ?_, hM, hk⟩, hE, hT⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · cases hk
    exact absurd hE (not_equiv_pair_of_strict hΦ hI hr hx hy hxy f g hT)
  · exact hk0

-- ============================================================================================
-- 3. Main result: `L > 0` if `Φ` is strict
-- ============================================================================================

/-- **`L > 0` if `Φ` is strict** (Lafont 1997, page 81). If a strict translation `Φ` of a
well-formed system `I` simulates every rule in `k` interactions, `L ≤ k ≤ M`, it simulates every
rule in `k` interactions, `max L 1 ≤ k ≤ M`: every simulating reduction has length at least `1`.
The rules of `I'` are linear, as Lafont's rules are (page 73), as in Proposition 4.

For distinct names on the ports this is `CompatibleWithin.distinct_pos`. For names that are
equal, the pair `α(xs) = β(ys)` interacts in `I`, and the simulation of that interaction
(`CompatibleByDistinct.step`, the proof of Proposition 4) only uses the rule with fresh distinct
names. -/
theorem CompatibleWithin.pos
    -- the two systems and the bounds
    {I : System S}
    {I' : System S'}
    {L M : ℕ}
    -- `Φ` is strict, `I` is well-formed, and the rules of `I'` are linear
    (hΦ : Φ.Strict)
    (hI : I.WellFormed)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- `Φ` simulates every rule in `L` to `M` interactions
    (h : Φ.CompatibleWithin I I' L M) :
    -- `Φ` simulates every rule in `max L 1` to `M` interactions
    Φ.CompatibleWithin I I' (max L 1) M := by
  intro α β r hr xs ys f g hlin
  let A : Sym2 (Term S ℕ) := s(.app α fun i => .var (xs i), .app β fun j => .var (ys j))
  let k : ℕ := (Net.vars ({A} : Net S ℕ)).sup + 1
  have hstep : Step I (A ::ₘ 0)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (fun w => k + w) + 0) :=
    Step.mk α β r hr _ _ 0 (fun w => k + w)
      (fun a b hab => Fin.ext (by simpa using hab))
      (fun w hw => by
        have hle : k + w ≤ (Net.vars ({A} : Net S ℕ)).sup :=
          Multiset.le_sup (show k + (w : ℕ) ∈ Net.vars ({A} : Net S ℕ) from hw)
        omega)
  have hT : Φ.NetTr (A ::ₘ 0) (s((Φ.net α).inst (fun i => .var (xs i)) f,
      (Φ.net β).inst (fun j => .var (ys j)) g) ::ₘ 0) :=
    ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl,
      TermTr.app α _ _ f fun i => TermTr.var _, TermTr.app β _ _ g fun j => TermTr.var _⟩
      Multiset.Rel.zero, hlin⟩
  obtain ⟨M₁, M', hR, hE, hT'⟩ := CompatibleByDistinct.step
    (R := fun N K => ∃ k, max L 1 ≤ k ∧ k ≤ M ∧ StepsEN I' k N K) hI.linear hI'
    (fun Γ ⟨k, hL, hM, hk⟩ hl => by
      obtain ⟨M', h1, h2, h3⟩ := hk.add_right hI' Γ hl
      exact ⟨M', ⟨k, hL, hM, h1⟩, h2, h3⟩)
    (fun hE ⟨k, hL, hM, hk⟩ => by
      obtain ⟨M', h1, h2⟩ := hk.of_equiv hE
      exact ⟨M', ⟨k, hL, hM, h1⟩, h2⟩)
    (fun ⟨_, _, _, hk⟩ => hk.stepsE) (h.distinct_pos hΦ hI) hstep hT
  rw [add_zero] at hT'
  exact ⟨M₁, M', fun w => k + w, hR, hE, hT'⟩

end Translation

end INet
