/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.General.CodeTermExtract

/-!
# Inside `Γ_{i,j}`: `C_p` against `!Γ`, then each `⟨φ⟩` port becomes `[φ]` (Fig. 10, pages 89–90)

Lafont 1997, Fig. 10 (journal page 89, PDF page 21) and the text of page 90: "`C_{p_{i,j}}` makes
`p_{i,j}` copies of `!Γ`", one for each cell of `⟨φ_{i,j}⟩`, and each `⟨α_k⟩` with its copy becomes
`[α_k]`, "and we get the translation of `φ_{i,j}`".

The statement starts from the pieces that opening `Γ_{i,j}` by `mux_muxStar` leaves: the copier
`C_p` on the extra ports of the cells of `⟨φ⟩` (`codeGammaExtras`), facing a renamed copy of `!Γ`,
and the trees `⟨φ⟩` at the ports (`codePort`), each facing an arbitrary partner `P p`.

The proof has three steps.

1. The copier makes one copy of `!Γ` per extra port (`copier_package`, the renamed `!Γ` is still a
   package without `dup`).
2. The copies are split port by port (`codeCopies_flatten_ofFn`).
3. Each port, with its own copies, reduces to `P p = [t_p]` (`codeTerm_extract`), beside the
   others (`stepsE_jobs_gen`).

The linearity hypothesis of the statement holds for fresh partners and a code renamed above
everything else: `codeGamma_extract_hyps`, in `Checks/Universality/General/CodeGammaExtractCheck`.

Contents, in the order of the file:

1. Auxiliary lemmas: reducing parts one after the other, and sums over a finite type.
   * `stepsE_jobs_gen` — `stepsE_jobs` with any trees in place of the wires `z i`, over any finite
     index type.
   * `sum_singleton_univ`, `sum_map_cons_univ_gen` — sums of equations over a finite type.
   * `zipWith_bind_var_comp` — the copies of a renamed tree are copies of the tree.
2. Main result for any numbering `e` of the symbols: `codeGamma_extractE`.
3. Main result: `codeGamma_extract`, the same at `e := symEnum S`.
-/

@[expose] public section

namespace INet.Comb

open Term Translation Simulation

-- ============================================================================================
-- 1. Auxiliary lemmas: reducing parts one after the other, sums over a finite type
-- ============================================================================================

/-- **Reducing several parts of a net one after the other** (as `stepsE_jobs`, page 90). If each
part `J i`, in any context, reduces to a net `Equiv` to one equation `Z i = t` (with `R i t`), then
the sum of the parts does, to the equations `Z i = t i`. Here `Z i` is any tree, and the parts
are indexed by any type. -/
theorem stepsE_jobs_gen
    -- the index type of the parts
    {ι : Type}
    -- the parts, the tree `Z i` each one ends on, and the property `R i` of its result
    (J : ι → CNet)
    (Z : ι → Term sig ℕ)
    (R : ι → Term sig ℕ → Prop)
    -- each part `J i`, beside any `Δ`, if linear, reduces to `Z i = t` beside `Δ`, with `R i t`
    (hJ : ∀ (i : ι) (Δ : CNet), Net.Linear (J i + Δ) →
      ∃ M t, StepsE system (J i + Δ) M ∧
        Equiv M (s(Z i, t) ::ₘ Δ) ∧
        R i t) :
    -- for every multiset `L` of indices without repetition,
    ∀ (L : Multiset ι), L.Nodup →
      -- and every rest of the net `Δ`, if the parts of `L` beside `Δ` form a linear net,
      ∀ Δ : CNet, Net.Linear ((L.map J).sum + Δ) →
        -- there are a net `M` and trees `t i` such that
        ∃ (M : CNet) (t : ι → Term sig ℕ),
          -- the parts beside `Δ` reduce, up to wires, to `M`,
          StepsE system ((L.map J).sum + Δ) M ∧
          -- `M` is the same graph as the equations `Z i = t i` beside `Δ`,
          Equiv M (L.map (fun i => s(Z i, t i)) + Δ) ∧
          -- and each `t i` has the property `R i`
          ∀ i ∈ L, R i (t i) := by
  classical
  intro L
  induction L using Multiset.induction_on with
  | empty =>
    intro _ Δ _
    exact ⟨_, fun _ => var 0, .refl, by simpa using Equiv.refl Δ, by simp⟩
  | cons i L ih =>
    intro hnd Δ hlin
    have hi : i ∉ L := (Multiset.nodup_cons.1 hnd).1
    rw [Multiset.map_cons, Multiset.sum_cons, add_assoc] at hlin ⊢
    obtain ⟨M₁, t₁, hS₁, hE₁, hR₁⟩ := hJ i _ hlin
    have L₁ := hE₁.linear (hS₁.linear system_wellFormed.linear hlin)
    have e : s(Z i, t₁) ::ₘ ((L.map J).sum + Δ) =
        (L.map J).sum + (s(Z i, t₁) ::ₘ Δ) := by rw [Multiset.add_cons]
    rw [e] at L₁ hE₁
    obtain ⟨M₂, t₂, hS₂, hE₂, hR₂⟩ := ih (Multiset.nodup_cons.1 hnd).2 _ L₁
    obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv hE₁ hS₂
    have hup : ∀ j ∈ L, Function.update t₂ i t₁ j = t₂ j := fun j hj =>
      Function.update_of_ne (fun h : j = i => hi (h ▸ hj)) _ _
    have hm : L.map (fun j => s(Z j, Function.update t₂ i t₁ j)) =
        L.map (fun j => s(Z j, t₂ j)) := Multiset.map_congr rfl fun j hj => by rw [hup j hj]
    refine ⟨M', Function.update t₂ i t₁, hS₁.trans hS', hE'.trans (hE₂.trans (Equiv.of_eq ?_)), ?_⟩
    · rw [Multiset.map_cons, Function.update_self, hm, Multiset.add_cons, Multiset.cons_add]
    · intro j hj
      rcases Multiset.mem_cons.1 hj with rfl | hj
      · simpa using hR₁
      · rw [hup j hj]
        exact hR₂ j hj

/-- A sum of singletons over a finite type is the map of the whole type. -/
theorem sum_singleton_univ
    -- one equation `e i` for each element of a finite type
    {ι : Type}
    [Fintype ι]
    (e : ι → Sym2 (Term sig ℕ)) :
    (∑ i, ({e i} : CNet)) = Finset.univ.val.map e := by
  rw [Finset.sum_eq_multiset_sum,
    show (fun i => ({e i} : CNet)) = (fun a => {a}) ∘ e from rfl, ← Multiset.map_map,
    Multiset.sum_map_singleton]

/-- The parts `e i, A i`, summed over any finite type, are the equations `e i` and the sum of the
`A i` (as `sum_map_cons_univ`). -/
theorem sum_map_cons_univ_gen
    -- for each element of a finite type, one equation `e i` and a net `A i`
    {ι : Type}
    [Fintype ι]
    (e : ι → Sym2 (Term sig ℕ))
    (A : ι → CNet) :
    (Finset.univ.val.map fun i => e i ::ₘ A i).sum
      = Finset.univ.val.map e + ∑ i, A i := by
  have h : (fun i => e i ::ₘ A i) = fun i => {e i} + A i :=
    funext fun i => (Multiset.singleton_add _ _).symm
  rw [h, Multiset.sum_map_add, ← sum_singleton_univ, Finset.sum_eq_multiset_sum,
    Finset.sum_eq_multiset_sum]

/-- The copies left by `copier_package` on a renamed `C` are the copies of `C` renamed by the
composite renamings. -/
theorem zipWith_bind_var_comp
    -- the tree and its renaming `g`
    (C : Term sig ℕ)
    (g : ℕ → ℕ)
    -- the trees the copies face, and the renamings of the copies
    (us : List (Term sig ℕ))
    (fs : List (ℕ → ℕ)) :
    -- the copies by `fs` of `C` renamed by `g` are the copies of `C` by the composites `f ∘ g`
    List.zipWith (fun u f => s(u, (C.bind fun x => var (g x)).bind fun x => var (f x))) us fs
      = List.zipWith (fun e f => s(e, C.bind fun x => var (f x))) us
          (fs.map fun f x => f (g x)) := by
  rw [List.zipWith_map_right]
  congr 1
  funext u f
  rw [Term.bind_bind]
  rfl

section Enum

-- the numbering `e` of the `n` symbols of the signature, and the expanded sides of the rules
variable {S : Signature} {n : ℕ} (e : S.Sym ≃ Fin n)
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

-- ============================================================================================
-- 2. Main result for any numbering of the symbols
-- ============================================================================================

/-- **Inside `Γ_{i,j}`, `C_p` against `!Γ` and the trees `⟨φ⟩` reduce to `[φ]`, for any numbering
`e` of the symbols** (Lafont 1997, Fig. 10, pages 89–90; page 90: no order on the symbols is
needed). This is `codeGamma_extract` with the `n` symbols numbered by any `e : S.Sym ≃ Fin n`:
`Γ = codeMenusE e side B`, `!Γ = code K Γ` with `K` above the names of `Γ`, renamed by `g`
injective on its names; the copier on the extra ports of the cells of `⟨φ⟩` (`codeGammaExtras`,
base `k₀`, the cells selecting the menu `e α` among `n`) against that copy of `!Γ`, the equations
`P p = ⟨φ⟩_p` (`codePort`) for every port `p : Fin a ⊕ Fin k` of `φ`, and any context `Δ`, if
linear, reduce to a net `Equiv` to the equations `P p = t' p` beside `Δ`, where each `t' p` is a
translation of `gammaTree φ k₀ p` by `codeTranslationE e side`. -/
theorem codeGamma_extractE
    -- the side `φ`, with `a` ports and `k` middle wires
    {a k : ℕ}
    (φ : Rule S a k)
    -- the base `k₀` of the names of `⟨φ⟩`, the base `B` of `Γ`, the base `K` of the cut names
    -- of `!Γ`, above the names of `Γ`
    (k₀ B K : ℕ)
    (hK : B + ∑ i, codeMenuSizesE e side i ≤ K)
    -- the renaming of `!Γ`, injective on its names
    (g : ℕ → ℕ)
    (hg : Set.InjOn g {x | x ∈ (code K (menu (codeMenusE e side B))).vars})
    -- the partners of the ports of `⟨φ⟩`
    (P : Fin a ⊕ Fin k → Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the copier against the renamed `!Γ`, the ports of `⟨φ⟩`
    -- against their partners, and `Δ`
    (hlin : Net.Linear
      (s(copier (codeGammaExtras n (fun α => (e α : ℕ)) φ k₀),
          (code K (menu (codeMenusE e side B))).bind fun x => var (g x))
        ::ₘ ((∑ q, {s(P q, codePort n (fun α => (e α : ℕ)) φ k₀ q)}) + Δ))) :
    -- there are a net `M` and trees `t' q` such that
    ∃ (M : CNet) (t' : Fin a ⊕ Fin k → Term sig ℕ),
      -- the net reduces, up to wires, to `M`,
      StepsE system
        (s(copier (codeGammaExtras n (fun α => (e α : ℕ)) φ k₀),
            (code K (menu (codeMenusE e side B))).bind fun x => var (g x))
          ::ₘ ((∑ q, {s(P q, codePort n (fun α => (e α : ℕ)) φ k₀ q)}) + Δ))
        M ∧
      -- `M` is the same graph as the equations `P q = t' q` beside `Δ`,
      Equiv M ((∑ q, {s(P q, t' q)}) + Δ) ∧
      -- and each `t' q` is a translation of the tree of `φ` at `q`
      ∀ q, (codeTranslationE e side).TermTr (gammaTree φ k₀ q) (t' q) := by
  set idx : S.Sym → ℕ := fun α => (e α : ℕ)
  set C := code K (menu (codeMenusE e side B)) with hC
  have hb : (menu (codeMenusE e side B)).Below K := fun x hx =>
    (menu_codeMenusE_below e side B x hx).trans_le hK
  have hCp : C.IsPackage := code_isPackage K _ (menu_codeMenusE_isPackage e side B) hb
  set Δ' : CNet := (∑ q, {s(P q, codePort n idx φ k₀ q)}) + Δ with hΔ'
  -- 1. the copier makes one copy of `!Γ` per extra port
  obtain ⟨fs, N, hlen, hinj, hS₁, hE₁⟩ := copier_package _ (IsPackage.bind_var hCp g hg)
    ((code_dupFree K _).bind_var g) (codeGammaExtras n idx φ k₀) Δ' hlin
  rw [zipWith_bind_var_comp] at hE₁
  set fs' := fs.map fun f x => f (g x) with hfs'
  have hinj' : ∀ f ∈ fs', Set.InjOn f {x | x ∈ C.vars} := fun f hf => by
    obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.1 hf
    exact injOn_comp_bind_var hg (hinj f₀ hf₀)
  -- 2. the copies, port by port
  set E : Fin (a + k) → List (Term sig ℕ) :=
    fun q => codePortExtras n idx φ k₀ (finSumFinEquiv.symm q) with hE
  have hlen' : fs'.length = ∑ q, (E q).length := by
    rw [hfs', List.length_map, hlen, codeGammaExtras, List.length_flatten, List.map_ofFn,
      List.sum_ofFn]
    rfl
  obtain ⟨fss, hfl, hfm, hsplit⟩ := codeCopies_flatten_ofFn C E fs' hlen'
  have hcop : (List.zipWith (fun e f => s(e, C.bind fun x => var (f x)))
      (codeGammaExtras n idx φ k₀) fs' : CNet) =
      ∑ p : Fin a ⊕ Fin k, codeCopies C (codePortExtras n idx φ k₀ p) (fss (finSumFinEquiv p)) := by
    have : (List.zipWith (fun e f => s(e, C.bind fun x => var (f x)))
        (codeGammaExtras n idx φ k₀) fs' : CNet) = codeCopies C (List.ofFn E).flatten fs' := rfl
    rw [this, hsplit, ← Equiv.sum_comp finSumFinEquiv]
    simp only [hE, Equiv.symm_apply_apply]
  rw [hcop] at hE₁
  -- 3. each port reduces, beside the others
  set J : Fin a ⊕ Fin k → CNet := fun p =>
    s(P p, codePort n idx φ k₀ p) ::ₘ
      codeCopies C (codePortExtras n idx φ k₀ p) (fss (finSumFinEquiv p)) with hJ
  have eJ : (∑ p, codeCopies C (codePortExtras n idx φ k₀ p) (fss (finSumFinEquiv p))) + Δ' =
      (Finset.univ.val.map J).sum + Δ := by
    rw [hJ, sum_map_cons_univ_gen (fun p => s(P p, codePort n idx φ k₀ p))
      (fun p => codeCopies C (codePortExtras n idx φ k₀ p) (fss (finSumFinEquiv p))), hΔ',
      sum_singleton_univ]
    abel
  rw [eJ] at hE₁
  have hlin₁ := hE₁.linear (hS₁.linear system_wellFormed.linear hlin)
  obtain ⟨M₂, t', hS₂, hE₂, hR₂⟩ := stepsE_jobs_gen J P
    (fun p t => (codeTranslationE e side).TermTr (gammaTree φ k₀ p) t)
    (fun p Δ'' hl => by
      have e' : J p + Δ'' = s(P p, codeTerm n idx (codeBase φ k₀ p) (gammaTree φ k₀ p)) ::ₘ
          (codeCopies C (codeExtras n idx (codeBase φ k₀ p) (gammaTree φ k₀ p))
            (fss (finSumFinEquiv p)) + Δ'') := Multiset.cons_add _ _ _
      rw [e'] at hl ⊢
      refine codeTerm_extractE e side B K hK (gammaTree φ k₀ p) (codeBase φ k₀ p) (P p)
        (fss (finSumFinEquiv p)) Δ'' ?_ (fun f hf => hinj' f (hfm _ f hf)) hl
      rw [hfl]
      simp [hE, codePortExtras]
      rfl)
    Finset.univ.val Finset.univ.nodup Δ hlin₁
  obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv hE₁ hS₂
  refine ⟨M', t', hS₁.trans hS', hE'.trans (hE₂.trans (Equiv.of_eq ?_)),
    fun q => hR₂ q (Finset.mem_univ q)⟩
  rw [sum_singleton_univ]

end Enum

-- ============================================================================================
-- 3. Main result: the symbols numbered by `symEnum S`
-- ============================================================================================

-- a signature with finitely many symbols, and the expanded sides of the rules
variable {S : Signature} [Finite S.Sym]
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **Inside `Γ_{i,j}`, `C_p` against `!Γ` and the trees `⟨φ⟩` reduce to `[φ]`** (Lafont 1997,
Fig. 10, pages 89–90: "`C_{p_{i,j}}` makes `p_{i,j}` copies of `!Γ`" and each `⟨α_k⟩` with its copy
becomes `[α_k]`, "and we get the translation of `φ_{i,j}`"). Let `Γ = codeMenus side B` and
`!Γ = code K Γ` with `K` above the names of `Γ`, renamed by `g` injective on its names. The net
made of the copier `C_p` on the extra ports of the cells of `⟨φ⟩` (`codeGammaExtras`, base `k₀`)
against that copy of `!Γ`, the equations `P p = ⟨φ⟩_p` (`codePort`) for every port
`p : Fin a ⊕ Fin k` of `φ` (the sum is over `Fin a ⊕ Fin k`), with arbitrary partners `P p`, and
any context `Δ`, if linear, reduces to a net `Equiv` to the equations `P p = t' p` beside `Δ`, where
each `t' p` is a translation of the tree `gammaTree φ k₀ p` of `φ` at `p` by `codeTranslation side`.
No hypothesis on `φ` is needed: the expanded linear form only matters for the linearity
hypothesis (`codeGamma_extract_hyps`). -/
theorem codeGamma_extract
    -- the side `φ`, with `a` ports and `k` middle wires
    {a k : ℕ}
    (φ : Rule S a k)
    -- the base `k₀` of the names of `⟨φ⟩`, the base `B` of `Γ`, the base `K` of the cut names
    -- of `!Γ`, above the names of `Γ`
    (k₀ B K : ℕ)
    (hK : B + ∑ i, codeMenuSizes side i ≤ K)
    -- the renaming of `!Γ`, injective on its names
    (g : ℕ → ℕ)
    (hg : Set.InjOn g {x | x ∈ (code K (menu (codeMenus side B))).vars})
    -- the partners of the ports of `⟨φ⟩`
    (P : Fin a ⊕ Fin k → Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the copier against the renamed `!Γ`, the ports of `⟨φ⟩`
    -- against their partners, and `Δ`
    (hlin : Net.Linear
      (s(copier (codeGammaExtras (Nat.card S.Sym) (fun α => symEnum S α) φ k₀),
          (code K (menu (codeMenus side B))).bind fun x => var (g x))
        ::ₘ ((∑ q, {s(P q, codePort (Nat.card S.Sym) (fun α => symEnum S α) φ k₀ q)}) + Δ))) :
    -- there are a net `M` and trees `t' q` such that
    ∃ (M : CNet) (t' : Fin a ⊕ Fin k → Term sig ℕ),
      -- the net reduces, up to wires, to `M`,
      StepsE system
        (s(copier (codeGammaExtras (Nat.card S.Sym) (fun α => symEnum S α) φ k₀),
            (code K (menu (codeMenus side B))).bind fun x => var (g x))
          ::ₘ ((∑ q, {s(P q, codePort (Nat.card S.Sym) (fun α => symEnum S α) φ k₀ q)}) + Δ))
        M ∧
      -- `M` is the same graph as the equations `P q = t' q` beside `Δ`,
      Equiv M ((∑ q, {s(P q, t' q)}) + Δ) ∧
      -- and each `t' q` is a translation of the tree of `φ` at `q`
      ∀ q, (codeTranslation side).TermTr (gammaTree φ k₀ q) (t' q) :=
  codeGamma_extractE (symEnum S) side φ k₀ B K hK g hg P Δ hlin

end INet.Comb
