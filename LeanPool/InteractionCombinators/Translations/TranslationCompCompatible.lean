/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.TranslationCompTr
public import LeanPool.InteractionCombinators.Translations.SimulationE

/-!
# The composite of two translations of interaction systems is one (page 80)

Lafont 1997, Section 1.7, journal page 80, last paragraph: "Composition of translations is defined
in the obvious way", and page 81: a translation compatible with reduction is a *translation of
interaction systems*. The paper composes such translations without comment. This file shows that
the composite `Ψ ∘ Φ` (`Translation.comp`) of two translations of interaction systems is one.

Contents, in the order of the file:

1. Auxiliary lemmas: `PNet.inst_var_eq_natTree_bind`, an instance of a principal net whose
   arguments are wires is its tree over `ℕ` renamed; `Translation.inst_comp_inv`, an instance of
   `Ψ(Φ(α))` is a `Ψ`-translation of an instance of `Φ(α)`, whose internal wires are named as the
   first block of internal wires of `Ψ(Φ(α))`.
2. Main result: `Translation.Compatible.comp`, the composite of two compatible translations is
   compatible.
-/

@[expose] public section

namespace INet

variable {S S' S'' : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas: instances of a composite
-- ============================================================================================

/-- **An instance with wires as arguments is the tree over `ℕ` renamed** (principal nets,
page 79). If `φ` sends the name `i` of the port `i` to `xs i` and the name `n + w` of the internal
wire `w` to `g w`, the instance of `q` on the wires `xs` with internal wires `g` is `q.natTree`
renamed by `φ`. -/
theorem PNet.inst_var_eq_natTree_bind
    -- the principal net of arity `n`
    {n : ℕ}
    (q : PNet S n)
    -- the wires on its ports and the names of its internal wires
    (xs : Fin n → ℕ)
    (g : Fin q.internal → ℕ)
    -- a renaming that sends the port `i` to `xs i` and the internal wire `w`, named `n + w`,
    -- to `g w`
    (φ : ℕ → ℕ)
    (hx : ∀ i : Fin n, φ i = xs i)
    (hg : ∀ w : Fin q.internal, φ (n + w) = g w) :
    q.inst (fun i => .var (xs i)) g = q.natTree.bind fun y => .var (φ y) := by
  unfold PNet.inst PNet.natTree
  rw [Term.bind_bind]
  refine Term.bind_congr fun x _ => ?_
  cases x with
  | inl i =>
    change Term.var (xs i) = Term.var (φ i)
    rw [hx]
  | inr w =>
    change Term.var (g w) = Term.var (φ (n + w))
    rw [hg]

namespace Translation

/-- **An instance of `Ψ(Φ(α))` is a `Ψ`-translation of an instance of `Φ(α)`** (page 80,
"composition of translations is defined in the obvious way"; the converse of `TermTr.comp` for
one instance). The auxiliary ports are the wires `xs`. The instance of `Φ(α)` names its internal
wire `w` as `f` names the internal wire `w` of `Ψ(Φ(α))`: the first block of internal wires of
`Ψ(Φ(α))` is that of `Φ(α)` (`trPNet`), the rest belongs to the instances of the `Ψ(β)`. -/
theorem inst_comp_inv
    -- the two translations, `Φ` first, and the symbol `α`
    (Φ : Translation S S')
    (Ψ : Translation S' S'')
    (α : S.Sym)
    -- the wires on the auxiliary ports and the names of the internal wires of `Ψ(Φ(α))`
    (xs : Fin (S.arity α) → ℕ)
    (f : Fin ((Ψ.comp Φ).net α).internal → ℕ) :
    -- there are names `f₁` for the internal wires of `Φ(α)` such that
    ∃ f₁ : Fin (Φ.net α).internal → ℕ,
      -- the internal wire `w` of `Φ(α)` is named as the internal wire `w` of `Ψ(Φ(α))`,
      (∀ w : Fin (Φ.net α).internal,
        ∃ w' : Fin ((Ψ.comp Φ).net α).internal, (w : ℕ) = w' ∧ f₁ w = f w') ∧
      -- and the instance of `Ψ(Φ(α))` is a `Ψ`-translation of the instance of `Φ(α)`
      Ψ.TermTr ((Φ.net α).inst (fun i => .var (xs i)) f₁)
        (((Ψ.comp Φ).net α).inst (fun i => .var (xs i)) f) := by
  classical
  let n := S.arity α
  let p := Φ.net α
  have hM : ((Ψ.comp Φ).net α).internal = p.internal + Ψ.size p.natTree := rfl
  let φ : ℕ → ℕ := fun x =>
    if hx : x < n then xs ⟨x, hx⟩
    else if hw : x - n < ((Ψ.comp Φ).net α).internal then f ⟨x - n, hw⟩
    else x
  have hlt : ∀ w : Fin p.internal, (w : ℕ) < ((Ψ.comp Φ).net α).internal := fun w => by
    rw [hM]; exact Nat.lt_of_lt_of_le w.isLt (Nat.le_add_right _ _)
  let f₁ : Fin p.internal → ℕ := fun w => f ⟨w, hlt w⟩
  refine ⟨f₁, fun w => ⟨⟨w, hlt w⟩, rfl, rfl⟩, ?_⟩
  have h1 : p.inst (fun i => .var (xs i)) f₁ = p.natTree.bind fun y => .var (φ y) := by
    refine PNet.inst_var_eq_natTree_bind p xs f₁ φ (fun i => ?_) (fun w => ?_)
    · simp [φ, n, i.isLt]
    · simp [φ, n, hlt w, f₁]
  have h2 : ((Ψ.comp Φ).net α).inst (fun i => .var (xs i)) f =
      ((Ψ.comp Φ).net α).natTree.bind fun y => .var (φ y) := by
    refine PNet.inst_var_eq_natTree_bind _ xs f φ (fun i => ?_) (fun w => ?_)
    · simp [φ, n, i.isLt]
    · simp [φ, n, w.isLt]
  have h3 : ((Ψ.comp Φ).net α).natTree = Ψ.trTerm (n + p.internal) p.natTree :=
    natTree_trPNet Ψ p
  rw [h1, h2, h3]
  exact (Ψ.termTr_trTerm _ _).bind_var φ

-- ============================================================================================
-- 2. Main result: the composite of compatible translations is compatible
-- ============================================================================================

/-- **The composite of two translations of interaction systems is one** (page 80, "composition of
translations is defined in the obvious way"; page 81, translations of interaction systems). If
`Φ` is compatible from `I` to `I'` and `Ψ` from `I'` to `I''`, then `Ψ ∘ Φ` is compatible from `I`
to `I''`. The rules of `I'` and of `I''` are linear; nothing is assumed on the rules of `I`.

The pair `Ψ(Φ(α)) — Ψ(Φ(β))` is a `Ψ`-translation of a pair `Φ(α) — Φ(β)` (`inst_comp_inv`),
which is linear (`NetTr.linear_source`). `Φ` reduces that pair to a net equivalent to a
`Φ`-translation of the right-hand side; `Ψ` simulates the reduction (`Compatible.stepsE`), the
`Ψ`-translation follows the equivalence (`NetTr.of_equiv`), and the two translations compose
(`NetTr.comp`). -/
theorem Compatible.comp
    -- the three interaction systems; the rules of `I'` and of `I''` are linear
    {I : System S}
    {I' : System S'}
    {I'' : System S''}
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    (hI'' : ∀ α β r, I''.rule α β = some r → r.Linear)
    -- `Φ` is compatible from `I` to `I'`, and `Ψ` from `I'` to `I''`
    {Φ : Translation S S'}
    {Ψ : Translation S' S''}
    (hΦ : Φ.Compatible I I')
    (hΨ : Ψ.Compatible I' I'') :
    (Ψ.comp Φ).Compatible I I'' := by
  intro α β r hr xs ys f g hlin
  obtain ⟨f₁, -, hf⟩ := inst_comp_inv Φ Ψ α xs f
  obtain ⟨g₁, -, hg⟩ := inst_comp_inv Φ Ψ β ys g
  have hT : Ψ.NetTr (s((Φ.net α).inst (fun i => .var (xs i)) f₁,
      (Φ.net β).inst (fun j => .var (ys j)) g₁) ::ₘ 0)
      (s(((Ψ.comp Φ).net α).inst (fun i => .var (xs i)) f,
        ((Ψ.comp Φ).net β).inst (fun j => .var (ys j)) g) ::ₘ 0) :=
    ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, hf, hg⟩ Multiset.Rel.zero, hlin⟩
  obtain ⟨M, N', h, hs, he, ht⟩ := hΦ α β r hr xs ys f₁ g₁ hT.linear_source
  obtain ⟨M₁, M'', hs'', he'', ht''⟩ := hΨ.stepsE hI' hI'' hs hT
  obtain ⟨N'', htN, heN⟩ := NetTr.of_equiv he ht''
  exact ⟨M₁, N'', h, hs'', he''.trans heN, ht.comp htN⟩

end Translation

end INet
