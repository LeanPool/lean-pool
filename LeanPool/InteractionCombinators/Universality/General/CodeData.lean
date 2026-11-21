/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RuleSides
public import LeanPool.InteractionCombinators.Universality.RecursionFree.DecompositionAbsorb

/-!
# Normalized decompositions for the general translation

Lafont’s general translation in Fig. 10 uses the normalized decompositions of pages 85–86.
Every well-formed system has these decompositions. The general and recursion-free cases use
the same side selection and expansion.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

namespace System.WellFormed

-- the interaction system
variable {I : System S}

open Classical in
/-- The normalised decomposition of a rule of a well-formed system (page 86): the symmetric
decomposition for a rule `α`–`α`, the canonical decomposition (page 85) with `σ` moved into `φ`
for `α ≠ β`. -/
noncomputable def normDecomp
    -- the system is well-formed
    (hI : I.WellFormed)
    -- the two symbols
    (α β : S.Sym) :
    -- every rule `α`–`β` of the system, to a decomposition
    ∀ r : Rule S (S.arity α) (S.arity β), I.rule α β = some r →
      Decomposition S (S.arity α) (S.arity β) :=
  if hab : α = β then hab ▸ fun r h => hI.symmDec α r h
  else fun r _ => r.decompose.absorb

/-- For a rule `α`–`α`, the normalised decomposition is the symmetric one (page 86). -/
theorem normDecomp_self
    -- the system is well-formed
    (hI : I.WellFormed)
    -- the symbol
    (α : S.Sym) :
    hI.normDecomp α α = fun r h => hI.symmDec α r h := by
  unfold normDecomp
  split_ifs with hab
  · rfl
  · exact absurd rfl hab

/-- For a rule `α`–`β` with `α ≠ β`, the normalised decomposition is the canonical one with `σ`
moved into `φ` (pages 85–86). -/
theorem normDecomp_ne
    -- the system is well-formed
    (hI : I.WellFormed)
    -- two different symbols
    {α β : S.Sym}
    (hab : α ≠ β) :
    hI.normDecomp α β = fun r _ => r.decompose.absorb := by
  unfold normDecomp
  split_ifs with h
  · exact absurd h hab
  · rfl

-- ============================================================================================
-- 5. Main result: every well-formed system has decomposition data (pages 85–86, 90)
-- ============================================================================================

/-- **Page 86, "one can assume", without an order (page 90).** Every well-formed system has
normalised decomposition data: the symmetric decomposition
(`Rule.exists_symm_decomposition_of_symmPerm`) of a rule `α`–`α`, and the canonical decomposition
`Rule.decompose` with `σ` moved into `φ` (`Decomposition.absorb`) of a rule `α`–`β` with `α ≠ β`. -/
noncomputable def decData
    -- the system is well-formed
    (hI : I.WellFormed) :
    I.DecData where
  dec := hI.normDecomp
  plug α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDecomp_self]
      exact (hI.symmDec_spec α r h).2.2.2.2
    · rw [normDecomp_ne hI hab]
      exact r.decompose.absorb_plugs (r.plug_decompose (hI.linear α β r h))
  linear α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDecomp_self]
      obtain ⟨hψ, -, hl, -, -⟩ := hI.symmDec_spec α r h
      change (hI.symmDec α r h).φ.Linear ∧ (hI.symmDec α r h).ψ.Linear
      rw [hψ]
      exact ⟨hl, hl⟩
    · rw [normDecomp_ne hI hab]
      have hd := r.decompose_linear (hI.linear α β r h)
      exact ⟨r.decompose.absorb_linear hd.1, hd.2⟩
  reduced α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDecomp_self]
      obtain ⟨hψ, -, -, hr, -⟩ := hI.symmDec_spec α r h
      change (hI.symmDec α r h).φ.Reduced ∧ (hI.symmDec α r h).ψ.Reduced
      rw [hψ]
      exact ⟨hr, hr⟩
    · rw [normDecomp_ne hI hab]
      have hd := r.decompose_reduced (hI.reduced α β r h)
      exact ⟨r.decompose.absorb_reduced hd.1, hd.2⟩
  involutive α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDecomp_self]
      exact (hI.symmDec_spec α r h).2.1
    · rw [normDecomp_ne hI hab]
      exact fun _ => rfl
  self α r h := by
    rw [normDecomp_self]
    exact (hI.symmDec_spec α r h).1
  ne α β r h hne := by
    rw [normDecomp_ne hI hne]
    rfl

end System.WellFormed

/-- **Pages 86 and 90.** Every well-formed interaction system has normalised decomposition data,
with no order on its alphabet and no recursion-freeness. -/
theorem System.exists_decData
    -- a well-formed interaction system
    {I : System S}
    (hI : I.WellFormed) :
    -- it has decomposition data, without an order
    Nonempty I.DecData :=
  ⟨hI.decData⟩

end INet
