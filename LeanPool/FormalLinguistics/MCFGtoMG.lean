/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.MG
public import LeanPool.FormalLinguistics.BinMCFG

/-!
  Harkema (2001) / Michaelis (2001) — Direction 2: `MCFG → MG`

  Every finite Linear Non-Erasing Multiple Context-Free Grammar (LCFRS / MCFG)
  has a weakly equivalent chain-based Minimalist Grammar (Stabler & Keenan 2003).

  The architecture follows Michaelis (2001), Sect. 4: three families of licensees
  (one for the components being assembled, one for each of the two arguments), with
  every mover carrying a single licensee so that it moves exactly once. The details
  are adapted to the chain-based setting.

  Architecture:
  1. First binarize any arbitrary-rank LCFRS `G` into a rank-≤-2 LCFRS `G' = BinMCFG.binarizeMCFG G`.
  2. Compile any rank-≤-2 LCFRS `G` into a Minimalist Grammar `binMCFGToMG G` using a
     3-bank mover architecture (`Bank.L`, `Bank.R`, `Bank.O`) where every mover carries
     a single licensee feature `[licensee (bank, idx)]` (so `Move2` never fires):
       • Each MCFG nonterminal `A` of dimension `d` is realized on two target banks
         `Side.L` and `Side.R`:
           `⟨false, ⟨ε, [cat (nt A side)]⟩, {(side, j) ↦ tup[j] | 0 ≤ j < d}⟩`.
       • Each rule `(r, rid)` loads its 0, 1, or 2 RHS tuples into disjoint banks `L` and `R`,
         builds output components `k = 0 .. dim(lhs)-1` by scanning `r.yield[k]` in reverse
         (left-prepending via `Move1` for variables and `Merge2` for terminal literals) and
         parking each finished component into bank `O` via `Merge3`, then copies bank `O`
         to target bank `side ∈ {L, R}` (`Move1` + `Merge3`).
       • A top-level start head selects `(nt G.start L)` and lands `(L, 0)` via `Move1`.
  3. Prove Completeness (`MCFG.Yield → MG.Derives`) and Soundness (`MG.Derives → MGInv`)
     via an exact finite-map mover invariant `ExactMap`, then compose with `BinMCFG`.
-/

@[expose] public section

namespace FormalLinguistics
namespace MCFGtoMG

variable {N T : Type}

/-! ### Part 1: Types, Indexing, and 3-Bank Lexicon Construction -/

/-- Three disjoint mover banks: left RHS input (`L`), right RHS input (`R`),
    and output accumulator (`O`). -/
inductive Bank where
  | L
  | R
  | O
  deriving DecidableEq, Repr

/-- Target input bank for a derived nonterminal tuple. -/
inductive Side where
  | L
  | R
  deriving DecidableEq, Repr

/-- Assign a child in a binary production to the corresponding storage bank. -/
def Side.toBank : Side → Bank
  | Side.L => Bank.L
  | Side.R => Bank.R

theorem Side.toBank_ne_O (s : Side) : s.toBank ≠ Bank.O := by
  cases s <;> decide

/-- Movement feature keys: `(bank, componentIndex)`. -/
abbrev MGLic := Bank × Nat

/-- Disjoint base syntactic categories for the compiled Minimalist Grammar. -/
inductive MGBase (N T : Type) where
  | start : MGBase N T
  | nt (A : N) (s : Side) : MGBase N T
  | lit (a : T) : MGBase N T
  | stage (rid : Nat) (k : Nat) : MGBase N T
  | built (rid : Nat) (k : Nat) : MGBase N T
  | copyStage (rid : Nat) (s : Side) (k : Nat) : MGBase N T
  | copied (rid : Nat) (s : Side) (k : Nat) : MGBase N T
  deriving DecidableEq, Repr

/-- Index list elements starting at `k`, yielding `(idx, elem)` pairs. -/
def indexFrom {α : Type} (k : Nat) : List α → List (Nat × α)
  | [] => []
  | a :: t => (k, a) :: indexFrom (k + 1) t

theorem mem_indexFrom_iff {α : Type} (L : List α) (k idx : Nat) (x : α) :
    (idx, x) ∈ indexFrom k L ↔ k ≤ idx ∧ L[idx - k]? = some x := by
  induction L generalizing k with
  | nil => simp [indexFrom]
  | cons a t ih =>
    simp only [indexFrom, List.mem_cons, Prod.mk.injEq, ih (k + 1)]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨hle, hget⟩)
      · exact ⟨Nat.le_refl _, by simp⟩
      · refine ⟨by omega, ?_⟩
        have hpos : idx - k = (idx - (k + 1)) + 1 := by omega
        rw [hpos]
        simpa using hget
    · rintro ⟨hle, hget⟩
      by_cases heq : idx = k
      · subst heq
        simp at hget
        left; exact ⟨rfl, hget.symm⟩
      · right
        have hpos : idx - k = (idx - (k + 1)) + 1 := by omega
        rw [hpos] at hget
        exact ⟨by omega, by simpa using hget⟩

theorem mem_indexFrom_zero_iff {α : Type} (L : List α) (idx : Nat) (x : α) :
    (idx, x) ∈ indexFrom 0 L ↔ L[idx]? = some x := by
  rw [mem_indexFrom_iff]
  simp

/-- Translate an MCFG yield atom into an MG feature that prepends its contribution on the left:
    • `tm a`    ↦ `=lit(a)` (left-prepends `[a]` via `Merge2`)
    • `var 0 j` ↦ `+(L, j)` (left-prepends `x_j` via `Move1`)
    • `var 1 j` ↦ `+(R, j)` (left-prepends `y_j` via `Move1`). -/
def atomToFeat : MCFGAtom T → MGFeature (MGBase N T) MGLic
  | MCFGAtom.tm a => MGFeature.sel (MGBase.lit a)
  | MCFGAtom.var 0 j => MGFeature.licensor (Bank.L, j)
  | MCFGAtom.var _ j => MGFeature.licensor (Bank.R, j)

/-- Collect all terminals occurring in the yield templates of `G`. -/
def allTerminals (G : MCFG N T) : List T :=
  G.rules.flatMap fun r =>
    r.yield.flatMap fun comp =>
      comp.filterMap fun
        | MCFGAtom.tm a => some a
        | MCFGAtom.var _ _ => none

/-- Emit all lexical entries for a single rank-≤-2 rule `(rid, r)`. -/
def ruleLexicon (G : MCFG N T) (rid : Nat) (r : MCFGRule N T) :
    List (List T × List (MGFeature (MGBase N T) MGLic)) :=
  let initLex : List (List T × List (MGFeature (MGBase N T) MGLic)) :=
    match r.rhs with
    | [] => [([], [MGFeature.cat (MGBase.stage rid 0)])]
    | [B] => [([], [MGFeature.sel (MGBase.nt B Side.L), MGFeature.cat (MGBase.stage rid 0)])]
    | [B, C] => [([], [MGFeature.sel (MGBase.nt B Side.L), MGFeature.sel (MGBase.nt C Side.R),
                       MGFeature.cat (MGBase.stage rid 0)])]
    | _ => []
  let buildLex : List (List T × List (MGFeature (MGBase N T) MGLic)) :=
    (indexFrom 0 r.yield).flatMap fun (k, comp) =>
      [ ([], MGFeature.sel (MGBase.stage rid k) ::
              comp.reverse.map (atomToFeat (N := N)) ++
              [MGFeature.cat (MGBase.built rid k), MGFeature.licensee (Bank.O, k)]),
        ([], [MGFeature.sel (MGBase.built rid k), MGFeature.cat (MGBase.stage rid (k + 1))]) ]
  let copyLex : List (List T × List (MGFeature (MGBase N T) MGLic)) :=
    [Side.L, Side.R].flatMap fun side =>
      ([], [MGFeature.sel (MGBase.stage rid r.yield.length),
            MGFeature.cat (MGBase.copyStage rid side 0)]) ::
      (List.range (G.dim r.lhs)).flatMap fun k =>
        let nextCat :=
          if k + 1 < G.dim r.lhs then MGBase.copyStage rid side (k + 1)
          else MGBase.nt r.lhs side
        [ ([], [MGFeature.sel (MGBase.copyStage rid side k),
                MGFeature.licensor (Bank.O, k),
                MGFeature.cat (MGBase.copied rid side k),
                MGFeature.licensee (side.toBank, k)]),
          ([], [MGFeature.sel (MGBase.copied rid side k), MGFeature.cat nextCat]) ]
  initLex ++ buildLex ++ copyLex

/-- Full lexicon of the compiled Minimalist Grammar for a rank-≤-2 MCFG `G`. -/
def buildLexicon (G : MCFG N T) : List (List T × List (MGFeature (MGBase N T) MGLic)) :=
  let startLex : List T × List (MGFeature (MGBase N T) MGLic) :=
    ([], [MGFeature.sel (MGBase.nt G.start Side.L),
          MGFeature.licensor (Bank.L, 0),
          MGFeature.cat MGBase.start])
  let litLex : List (List T × List (MGFeature (MGBase N T) MGLic)) :=
    (allTerminals G).map fun a => ([a], [MGFeature.cat (MGBase.lit a)])
  let rulesLex : List (List T × List (MGFeature (MGBase N T) MGLic)) :=
    (indexFrom 0 G.rules).flatMap fun (rid, r) => ruleLexicon G rid r
  startLex :: (litLex ++ rulesLex)

theorem buildLexicon_nonempty (G : MCFG N T) :
    ∀ entry, entry ∈ buildLexicon G → entry.2 ≠ [] := by
  intro entry hentry
  unfold buildLexicon at hentry
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap] at hentry
  rcases hentry with rfl | ⟨a, _, rfl⟩ | ⟨⟨rid, r⟩, _, hrl⟩
  · simp
  · simp
  · unfold ruleLexicon at hrl
    simp only [List.mem_append] at hrl
    rcases hrl with (hinit | hbuild) | hcopy
    · cases hrhs : r.rhs with
      | nil => simp [hrhs] at hinit; subst hinit; simp
      | cons B rest =>
        cases rest with
        | nil => simp [hrhs] at hinit; subst hinit; simp
        | cons C rest' =>
          cases rest' with
          | nil => simp [hrhs] at hinit; subst hinit; simp
          | cons _ _ => simp [hrhs] at hinit
    · simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hbuild
      obtain ⟨⟨k, comp⟩, _, h1 | h2⟩ := hbuild <;> (subst entry; simp)
    · simp only [List.mem_flatMap, List.mem_cons] at hcopy
      obtain ⟨side, _, hbr | hcp⟩ := hcopy
      · subst hbr; simp
      · simp only [List.not_mem_nil, or_false] at hcp
        obtain ⟨k, _, h1 | h2⟩ := hcp <;> (subst entry; simp)

/-- The Minimalist Grammar compiled from a rank-≤-2 MCFG `G`. -/
def binMCFGToMG (G : MCFG N T) : MG (MGBase N T) MGLic T where
  start := MGBase.start
  lexicon := buildLexicon G
  lex_nonempty := buildLexicon_nonempty G

/-! ### Part 2: ExactMap Mover Invariant & Algebra -/

/-- Exact finite-map invariant for single-feature movers:
    `ms` satisfies SMC, every chain in `ms` is `⟨val k, [licensee k]⟩` for some `k` in `dom`,
    and every `k` in `dom` is present in `ms` with value `val k`. -/
def ExactMap (ms : List (MGChain (MGBase N T) MGLic T))
    (dom : MGLic → Prop) (val : MGLic → List T) : Prop :=
  SMC ms ∧
  (∀ c, c ∈ ms → ∃ k, dom k ∧ c = ⟨val k, [MGFeature.licensee k]⟩) ∧
  (∀ k, dom k → ⟨val k, [MGFeature.licensee k]⟩ ∈ ms)

theorem exactMap_nil (val : MGLic → List T) :
    ExactMap (N := N) [] (fun _ => False) val := by
  refine ⟨⟨by intro c hc; simp at hc, List.nodup_nil⟩, ?_, ?_⟩
  · intro c hc; simp at hc
  · intro k hk; exact False.elim hk

theorem exactMap_ext {ms : List (MGChain (MGBase N T) MGLic T)}
    {dom1 dom2 : MGLic → Prop} {val1 val2 : MGLic → List T}
    (h : ExactMap ms dom1 val1)
    (hdom : ∀ k, dom1 k ↔ dom2 k)
    (hval : ∀ k, dom1 k → val1 k = val2 k) :
    ExactMap ms dom2 val2 := by
  obtain ⟨hsmc, hf, hb⟩ := h
  refine ⟨hsmc, ?_, ?_⟩
  · intro c hc
    obtain ⟨k, hk, rfl⟩ := hf c hc
    exact ⟨k, (hdom k).mp hk, by rw [hval k hk]⟩
  · intro k hk2
    have hk1 := (hdom k).mpr hk2
    rw [← hval k hk1]
    exact hb k hk1

theorem exactMap_empty_eq_nil {ms : List (MGChain (MGBase N T) MGLic T)}
    {dom : MGLic → Prop} {val : MGLic → List T}
    (h : ExactMap ms dom val) (hempty : ∀ k, ¬dom k) : ms = [] := by
  cases ms with
  | nil => rfl
  | cons c t =>
    obtain ⟨k, hk, _⟩ := h.2.1 c (List.mem_cons_self ..)
    exact False.elim (hempty k hk)

theorem exactMap_disjoint_append {ms1 ms2 : List (MGChain (MGBase N T) MGLic T)}
    {dom1 dom2 : MGLic → Prop} {val : MGLic → List T}
    (h1 : ExactMap ms1 dom1 val) (h2 : ExactMap ms2 dom2 val)
    (hdisj : ∀ k, dom1 k → ¬dom2 k) :
    ExactMap (ms1 ++ ms2) (fun k => dom1 k ∨ dom2 k) val := by
  obtain ⟨hsmc1, hf1, hb1⟩ := h1
  obtain ⟨hsmc2, hf2, hb2⟩ := h2
  have hsmc : SMC (ms1 ++ ms2) := by
    refine ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_append.mp hc with hm1 | hm2
      · exact hsmc1.1 c hm1
      · exact hsmc2.1 c hm2
    · rw [List.filterMap_append, List.nodup_append]
      refine ⟨hsmc1.2, hsmc2.2, ?_⟩
      intro k1 hk1 k2 hk2 heq
      subst heq
      obtain ⟨c1, hc1, hl1⟩ := List.mem_filterMap.mp hk1
      obtain ⟨c2, hc2, hl2⟩ := List.mem_filterMap.mp hk2
      obtain ⟨j1, hj1, rfl⟩ := hf1 c1 hc1
      obtain ⟨j2, hj2, rfl⟩ := hf2 c2 hc2
      simp [MGChain.headLic] at hl1 hl2
      rw [← hl1] at hl2
      exact hdisj j1 hj1 (hl2 ▸ hj2)
  refine ⟨hsmc, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hm1 | hm2
    · obtain ⟨k, hk, rfl⟩ := hf1 c hm1; exact ⟨k, Or.inl hk, rfl⟩
    · obtain ⟨k, hk, rfl⟩ := hf2 c hm2; exact ⟨k, Or.inr hk, rfl⟩
  · intro k hk
    rcases hk with hk1 | hk2
    · exact List.mem_append_left _ (hb1 k hk1)
    · exact List.mem_append_right _ (hb2 k hk2)

theorem exactMap_cons_fresh {ms : List (MGChain (MGBase N T) MGLic T)}
    {dom : MGLic → Prop} {val : MGLic → List T}
    {k0 : MGLic} {u : List T}
    (h : ExactMap ms dom val) (hfresh : ¬dom k0) (hval0 : val k0 = u) :
    ExactMap (⟨u, [MGFeature.licensee k0]⟩ :: ms) (fun k => k = k0 ∨ dom k) val := by
  obtain ⟨hsmc, hf, hb⟩ := h
  have hsmc' : SMC (⟨u, [MGFeature.licensee k0]⟩ :: ms) := by
    refine ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hm
      · exact ⟨k0, [], rfl⟩
      · exact hsmc.1 c hm
    · simp only [List.filterMap_cons, MGChain.headLic, List.nodup_cons]
      refine ⟨?_, hsmc.2⟩
      intro hmem
      obtain ⟨c, hc, hl⟩ := List.mem_filterMap.mp hmem
      obtain ⟨k, hk, rfl⟩ := hf c hc
      simp [MGChain.headLic] at hl
      subst hl
      exact hfresh hk
  refine ⟨hsmc', ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hm
    · exact ⟨k0, Or.inl rfl, by rw [hval0]⟩
    · obtain ⟨k, hk, rfl⟩ := hf c hm
      exact ⟨k, Or.inr hk, rfl⟩
  · intro k hk
    rcases hk with rfl | hk'
    · rw [hval0]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hb k hk')

theorem exactMap_remove {ms1 ms2 : List (MGChain (MGBase N T) MGLic T)}
    {dom : MGLic → Prop} {val : MGLic → List T}
    {k0 : MGLic} {t : List T}
    (h : ExactMap (ms1 ++ ⟨t, [MGFeature.licensee k0]⟩ :: ms2) dom val) :
    dom k0 ∧ t = val k0 ∧
    ExactMap (ms1 ++ ms2) (fun k => dom k ∧ k ≠ k0) val := by
  obtain ⟨hsmc, hf, hb⟩ := h
  have hmem0 : ⟨t, [MGFeature.licensee k0]⟩ ∈ ms1 ++ ⟨t, [MGFeature.licensee k0]⟩ :: ms2 :=
    List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨k', hk', heq⟩ := hf _ hmem0
  have ht_eq : t = val k' := by injection heq
  have hk_eq : k0 = k' := by
    have hfeats := congrArg MGChain.feats heq
    simp at hfeats
    exact hfeats
  subst hk_eq
  refine ⟨hk', ht_eq, MG.smc_remove hsmc, ?_, ?_⟩
  · intro c hc
    have hc_in : c ∈ ms1 ++ ⟨t, [MGFeature.licensee k0]⟩ :: ms2 := by
      rcases List.mem_append.mp hc with h1 | h2
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
    obtain ⟨k, hk, rfl⟩ := hf c hc_in
    have hne : k ≠ k0 := by
      intro heqk; subst heqk
      have hnd := hsmc.2
      simp only [List.filterMap_append, List.filterMap_cons, MGChain.headLic,
        List.nodup_append, List.nodup_cons] at hnd
      rcases List.mem_append.mp hc with h1 | h2
      · exact hnd.2.2 k (List.mem_filterMap.mpr ⟨_, h1, rfl⟩) k (List.mem_cons_self ..) rfl
      · exact hnd.2.1.1 (List.mem_filterMap.mpr ⟨_, h2, rfl⟩)
    exact ⟨k, ⟨hk, hne⟩, rfl⟩
  · intro k ⟨hk, hne⟩
    have hm := hb k hk
    rcases List.mem_append.mp hm with h1 | h2
    · exact List.mem_append_left _ h1
    · rcases List.mem_cons.mp h2 with heq' | h2'
      · have hfe := congrArg MGChain.feats heq'
        simp at hfe
        exact absurd hfe hne
      · exact List.mem_append_right _ h2'

/-- Predicate expressing that every mover in `ms` has a single licensee feature. -/
def SingleMover (ms : List (MGChain (MGBase N T) MGLic T)) : Prop :=
  ∀ c, c ∈ ms → ∃ k, c.feats = [MGFeature.licensee k]

theorem exactMap_singleMover {ms : List (MGChain (MGBase N T) MGLic T)}
    {dom : MGLic → Prop} {val : MGLic → List T} (h : ExactMap ms dom val) :
    SingleMover ms := by
  intro c hc
  obtain ⟨k, _, rfl⟩ := h.2.1 c hc
  exact ⟨k, rfl⟩

theorem singleMover_nil : SingleMover (N := N) (T := T) [] := by
  intro c hc; simp at hc

theorem singleMover_no_move2 {ms1 ms2 : List (MGChain (MGBase N T) MGLic T)}
    {t : List T} {f f' : MGLic} {δ' : List (MGFeature (MGBase N T) MGLic)}
    (hs : SingleMover (ms1 ++ ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2)) :
    False := by
  obtain ⟨k, hk⟩ := hs _ (List.mem_append_right _ (List.mem_cons_self ..))
  simp at hk

/-! ### Part 3: Variable Domains, Rule Values, and Linearity Lemmas -/

/-- Variable pairs occurring in a single component template. -/
def compVars (comp : List (MCFGAtom T)) : List (Nat × Nat) :=
  comp.filterMap fun
    | MCFGAtom.tm _ => none
    | MCFGAtom.var i j => some (i, j)

/-- Variable pairs occurring across a list of component templates. -/
def compsVars (cs : List (List (MCFGAtom T))) : List (Nat × Nat) :=
  cs.flatMap compVars

theorem compVars_append (c1 c2 : List (MCFGAtom T)) :
    compVars (c1 ++ c2) = compVars c1 ++ compVars c2 :=
  List.filterMap_append

theorem compVars_reverse (c : List (MCFGAtom T)) :
    compVars c.reverse = (compVars c).reverse := by
  induction c with
  | nil => rfl
  | cons a t ih =>
    cases a with
    | tm x => simp [compVars]
    | var i j => simp [compVars]

theorem mem_compVars_reverse {c : List (MCFGAtom T)} {p : Nat × Nat} :
    p ∈ compVars c.reverse ↔ p ∈ compVars c := by
  rw [compVars_reverse, List.mem_reverse]

theorem compsVars_append (cs1 cs2 : List (List (MCFGAtom T))) :
    compsVars (cs1 ++ cs2) = compsVars cs1 ++ compsVars cs2 :=
  List.flatMap_append

theorem compsVars_cons (c : List (MCFGAtom T)) (cs : List (List (MCFGAtom T))) :
    compsVars (c :: cs) = compVars c ++ compsVars cs := rfl

theorem varOccurrences_eq_compsVars (r : MCFGRule N T) :
    r.varOccurrences = compsVars r.yield := rfl

theorem drop_eq_cons_drop_succ {α : Type} {L : List α} {k : Nat} {x : α}
    (h : L[k]? = some x) : L.drop k = x :: L.drop (k + 1) := by
  induction L generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero =>
      simp at h; subst h; rfl
    | succ k' =>
      simp only [List.getElem?_cons_succ] at h
      simpa [List.drop_succ_cons] using ih h

/-- Extract the `(i, j)`-th argument string from `args` (matching `MCFG.evalComp`). -/
def argPiece (args : List (List (List T))) (i j : Nat) : List T :=
  match args[i]? with
  | some tup =>
      match tup[j]? with
      | some s => s
      | none => []
  | none => []

theorem argPiece_eq_getD {args : List (List (List T))} {i j : Nat} {tup : List (List T)}
    (h : args[i]? = some tup) : argPiece args i j = (tup[j]?).getD [] := by
  simp only [argPiece, h]
  cases tup[j]? <;> rfl

/-- Canonical value map for a rule `r` evaluated on RHS argument tuples `args`. -/
def ruleVal (r : MCFGRule N T) (args : List (List (List T))) : MGLic → List T
  | (Bank.L, j) => argPiece args 0 j
  | (Bank.R, j) => argPiece args 1 j
  | (Bank.O, k) =>
      match r.yield[k]? with
      | some comp => MCFG.evalComp args comp
      | none => []

theorem ruleVal_O_eq_evalYield {r : MCFGRule N T} {args : List (List (List T))} {m : Nat} :
    ruleVal r args (Bank.O, m) = ((MCFG.evalYield args r.yield)[m]?).getD [] := by
  simp only [ruleVal, MCFG.evalYield, List.getElem?_map]
  cases r.yield[m]? <;> rfl

/-- Mover domain at `stage rid k` (`0 ≤ k ≤ r.yield.length`):
    output components `0 .. k-1` in bank `O`, plus all variables occurring in `r.yield.drop k`
    in banks `L` (`i = 0`) and `R` (`i = 1`). -/
def stageDom (r : MCFGRule N T) (k : Nat) : MGLic → Prop
  | (Bank.O, m) => m < k
  | (Bank.L, j) => (0, j) ∈ compsVars (r.yield.drop k)
  | (Bank.R, j) => (1, j) ∈ compsVars (r.yield.drop k)

/-- Mover domain while building component `k` with remaining reverse prefix `revPref`:
    output components `0 .. k-1` in bank `O`, plus variables in `revPref` or `r.yield.drop (k+1)`. -/
def buildDom (r : MCFGRule N T) (k : Nat) (revPref : List (MCFGAtom T)) : MGLic → Prop
  | (Bank.O, m) => m < k
  | (Bank.L, j) => (0, j) ∈ compVars revPref ∨ (0, j) ∈ compsVars (r.yield.drop (k + 1))
  | (Bank.R, j) => (1, j) ∈ compVars revPref ∨ (1, j) ∈ compsVars (r.yield.drop (k + 1))

/-- Mover domain during the copy phase (`0 ≤ k ≤ d`):
    `side` holds `0 .. k-1`, `O` holds `k .. d-1`. -/
def copyDom (d : Nat) (side : Side) (k : Nat) : MGLic → Prop :=
  fun m =>
    (∃ j, j < k ∧ m = (side.toBank, j)) ∨
    (∃ j, k ≤ j ∧ j < d ∧ m = (Bank.O, j))

/-- Every variable in `r.yield` of a well-formed rank-≤-2 rule has argument index `0` or `1`. -/
theorem var_index_lt_two {G : MCFG N T} {r : MCFGRule N T}
    (hwf : r.WellFormed G.dim) (hrank : r.rhs.length ≤ 2)
    {i j : Nat} (hv : (i, j) ∈ r.varOccurrences) : i = 0 ∨ i = 1 := by
  obtain ⟨B, hB, _⟩ := (hwf.2.2 i j).mp hv
  have hi : i < r.rhs.length := by
    by_cases hlt : i < r.rhs.length
    · exact hlt
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hB
      simp at hB
  omega

theorem nodup_of_reverse {α : Type} {L : List α} (h : L.reverse.Nodup) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    simp only [List.reverse_cons, List.nodup_append, List.nodup_cons, List.mem_singleton] at h
    rw [List.nodup_cons]
    refine ⟨?_, ih h.1⟩
    intro ha
    exact h.2.2 a (List.mem_reverse.mpr ha) a rfl rfl

/-- If `comp = r.yield[k]` and `comp = revPref.reverse ++ suf`, then
    `compVars revPref ++ compsVars (r.yield.drop (k + 1))` is `Nodup` by linearity of `r`. -/
theorem nodup_buildVars {r : MCFGRule N T} (hlin : r.isLinear)
    {k : Nat} {comp revPref suf : List (MCFGAtom T)}
    (hget : r.yield[k]? = some comp) (hsplit : comp = revPref.reverse ++ suf) :
    (compVars revPref ++ compsVars (r.yield.drop (k + 1))).Nodup := by
  have hfull : r.yield = r.yield.take k ++ comp :: r.yield.drop (k + 1) := by
    have h1 := (List.take_append_drop k r.yield).symm
    rw [drop_eq_cons_drop_succ hget] at h1
    exact h1
  have hnd : r.varOccurrences.Nodup := hlin
  rw [varOccurrences_eq_compsVars, hfull, compsVars_append, compsVars_cons, hsplit,
    compVars_append] at hnd
  have hnd1 := (List.nodup_append.mp hnd).2.1
  have hnd2 := List.nodup_append.mp hnd1
  have hnd_rev : (compVars revPref.reverse).Nodup := (List.nodup_append.mp hnd2.1).1
  have hnd_p : (compVars revPref).Nodup := by
    rw [compVars_reverse] at hnd_rev
    exact nodup_of_reverse hnd_rev
  rw [List.nodup_append]
  refine ⟨hnd_p, hnd2.2.1, ?_⟩
  intro x hx y hy
  exact hnd2.2.2 x (List.mem_append_left _ (mem_compVars_reverse.mpr hx)) y hy

theorem stageDom_zero_iff {G : MCFG N T} {r : MCFGRule N T} (hwf : r.WellFormed G.dim) :
    ∀ m, stageDom r 0 m ↔
      (∃ B j, r.rhs[0]? = some B ∧ j < G.dim B ∧ m = (Bank.L, j)) ∨
      (∃ C j, r.rhs[1]? = some C ∧ j < G.dim C ∧ m = (Bank.R, j)) := by
  intro ⟨bank, j⟩
  cases bank with
  | O => simp [stageDom]
  | L =>
    change (0, j) ∈ r.varOccurrences ↔ _
    rw [hwf.2.2 0 j]
    constructor
    · rintro ⟨B, hB, hj⟩; left; exact ⟨B, j, hB, hj, rfl⟩
    · rintro (⟨B, j', hB, hj, heq⟩ | ⟨C, j', _, _, heq⟩)
      · have : j = j' := by injection heq
        subst this; exact ⟨B, hB, hj⟩
      · simp at heq
  | R =>
    change (1, j) ∈ r.varOccurrences ↔ _
    rw [hwf.2.2 1 j]
    constructor
    · rintro ⟨C, hC, hj⟩; right; exact ⟨C, j, hC, hj, rfl⟩
    · rintro (⟨B, j', _, _, heq⟩ | ⟨C, j', hC, hj, heq⟩)
      · simp at heq
      · have : j = j' := by injection heq
        subst this; exact ⟨C, hC, hj⟩

theorem stageDom_eq_buildDom_start {r : MCFGRule N T} {k : Nat} {comp : List (MCFGAtom T)}
    (hget : r.yield[k]? = some comp) :
    ∀ m, stageDom r k m ↔ buildDom r k comp.reverse m := by
  intro ⟨bank, j⟩
  cases bank with
  | O => rfl
  | L =>
    simp only [stageDom, buildDom, drop_eq_cons_drop_succ hget, compsVars_cons,
      List.mem_append, mem_compVars_reverse]
  | R =>
    simp only [stageDom, buildDom, drop_eq_cons_drop_succ hget, compsVars_cons,
      List.mem_append, mem_compVars_reverse]

theorem buildDom_step_tm {r : MCFGRule N T} {k : Nat} (a : T) (rest : List (MCFGAtom T)) :
    ∀ m, buildDom r k (MCFGAtom.tm a :: rest) m ↔ buildDom r k rest m := by
  intro ⟨bank, j⟩
  cases bank <;> simp [buildDom, compVars]

theorem buildDom_step_var0 {r : MCFGRule N T} (hlin : r.isLinear)
    {k j0 : Nat} {comp rest suf : List (MCFGAtom T)}
    (hget : r.yield[k]? = some comp)
    (hsplit : comp = (MCFGAtom.var 0 j0 :: rest).reverse ++ suf) :
    ∀ m, (buildDom r k (MCFGAtom.var 0 j0 :: rest) m ∧ m ≠ (Bank.L, j0)) ↔
      buildDom r k rest m := by
  have hnd := nodup_buildVars hlin hget hsplit
  simp only [compVars, List.filterMap_cons, List.cons_append, List.nodup_cons,
    List.mem_append] at hnd
  obtain ⟨hnot_in, _⟩ := hnd
  intro ⟨bank, j⟩
  cases bank with
  | O => simp [buildDom]
  | R =>
    simp only [buildDom, compVars, List.filterMap_cons, List.mem_cons, Prod.mk.injEq,
      Nat.one_ne_zero, false_and, false_or, ne_eq, reduceCtorEq, not_false_eq_true, and_true]
  | L =>
    simp only [buildDom, compVars, List.filterMap_cons, List.mem_cons, Prod.mk.injEq,
      true_and, ne_eq]
    constructor
    · rintro ⟨(rfl | hrest) | hdrop, hne⟩
      · exact absurd rfl hne
      · exact Or.inl hrest
      · exact Or.inr hdrop
    · rintro (hrest | hdrop)
      · refine ⟨Or.inl (Or.inr hrest), ?_⟩
        rintro rfl; exact hnot_in (Or.inl hrest)
      · refine ⟨Or.inr hdrop, ?_⟩
        rintro rfl; exact hnot_in (Or.inr hdrop)

theorem buildDom_step_var1 {r : MCFGRule N T} (hlin : r.isLinear)
    {k j0 : Nat} {comp rest suf : List (MCFGAtom T)}
    (hget : r.yield[k]? = some comp)
    (hsplit : comp = (MCFGAtom.var 1 j0 :: rest).reverse ++ suf) :
    ∀ m, (buildDom r k (MCFGAtom.var 1 j0 :: rest) m ∧ m ≠ (Bank.R, j0)) ↔
      buildDom r k rest m := by
  have hnd := nodup_buildVars hlin hget hsplit
  simp only [compVars, List.filterMap_cons, List.cons_append, List.nodup_cons,
    List.mem_append] at hnd
  obtain ⟨hnot_in, _⟩ := hnd
  intro ⟨bank, j⟩
  cases bank with
  | O => simp [buildDom]
  | L =>
    simp only [buildDom, compVars, List.filterMap_cons, List.mem_cons, Prod.mk.injEq,
      Nat.zero_ne_one, false_and, false_or, ne_eq, reduceCtorEq, not_false_eq_true, and_true]
  | R =>
    simp only [buildDom, compVars, List.filterMap_cons, List.mem_cons, Prod.mk.injEq,
      true_and, ne_eq]
    constructor
    · rintro ⟨(rfl | hrest) | hdrop, hne⟩
      · exact absurd rfl hne
      · exact Or.inl hrest
      · exact Or.inr hdrop
    · rintro (hrest | hdrop)
      · refine ⟨Or.inl (Or.inr hrest), ?_⟩
        rintro rfl; exact hnot_in (Or.inl hrest)
      · refine ⟨Or.inr hdrop, ?_⟩
        rintro rfl; exact hnot_in (Or.inr hdrop)

theorem buildDom_end_insert {r : MCFGRule N T} {k : Nat} :
    ∀ m, (m = (Bank.O, k) ∨ buildDom r k [] m) ↔ stageDom r (k + 1) m := by
  intro ⟨bank, j⟩
  cases bank with
  | O =>
    simp only [buildDom, stageDom, Prod.mk.injEq, true_and]
    omega
  | L => simp [buildDom, stageDom, compVars]
  | R => simp [buildDom, stageDom, compVars]

theorem stageDom_end_eq_copyDom_zero {r : MCFGRule N T} (d : Nat) (hd : r.yield.length = d)
    (side : Side) :
    ∀ m, stageDom r r.yield.length m ↔ copyDom d side 0 m := by
  intro ⟨bank, j⟩
  cases bank with
  | O =>
    simp only [stageDom, copyDom, hd]
    constructor
    · intro hj; right; exact ⟨j, Nat.zero_le j, hj, rfl⟩
    · rintro (⟨j', hj', _⟩ | ⟨j', _, hj', heq⟩)
      · omega
      · have : j = j' := by injection heq
        subst this; exact hj'
  | L =>
    simp only [stageDom, List.drop_length, compsVars, List.flatMap_nil, List.not_mem_nil,
      copyDom, Prod.mk.injEq, false_iff]
    rintro (⟨j', hj', _, _⟩ | ⟨j', _, _, hbk, _⟩)
    · omega
    · simp at hbk
  | R =>
    simp only [stageDom, List.drop_length, compsVars, List.flatMap_nil, List.not_mem_nil,
      copyDom, Prod.mk.injEq, false_iff]
    rintro (⟨j', hj', _, _⟩ | ⟨j', _, _, hbk, _⟩)
    · omega
    · simp at hbk

theorem copyDom_step {d : Nat} {side : Side} {k : Nat} (hk : k < d) :
    ∀ m, (m = (side.toBank, k) ∨ (copyDom d side k m ∧ m ≠ (Bank.O, k))) ↔
      copyDom d side (k + 1) m := by
  intro m
  constructor
  · rintro (rfl | ⟨(⟨j, hj, rfl⟩ | ⟨j, hlo, hhi, rfl⟩), hne⟩)
    · left; exact ⟨k, by omega, rfl⟩
    · left; exact ⟨j, by omega, rfl⟩
    · right
      have hjk : j ≠ k := fun heq => hne (by rw [heq])
      exact ⟨j, by omega, hhi, rfl⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hlo, hhi, rfl⟩)
    · by_cases hjk : j = k
      · subst hjk; left; rfl
      · right
        refine ⟨Or.inl ⟨j, by omega, rfl⟩, ?_⟩
        intro heq
        have hbk : side.toBank = Bank.O := by injection heq
        exact Side.toBank_ne_O side hbk
    · right
      refine ⟨Or.inr ⟨j, by omega, hhi, rfl⟩, ?_⟩
      intro heq
      have hjk : j = k := by injection heq
      omega

theorem copyDom_end {d : Nat} {side : Side} :
    ∀ m, copyDom d side d m ↔ ∃ j, j < d ∧ m = (side.toBank, j) := by
  intro m
  simp only [copyDom]
  constructor
  · rintro (h | ⟨j, hlo, hhi, _⟩)
    · exact h
    · omega
  · exact Or.inl

/-! ### Part 4: Completeness (`MCFG.Yield G → MG.Derives (binMCFGToMG G)`) -/

/-- Helper: membership of a literal terminal in `buildLexicon G`. -/
theorem mem_lit_buildLexicon {G : MCFG N T} {r : MCFGRule N T}
    (hr : r ∈ G.rules) {comp : List (MCFGAtom T)} (hcomp : comp ∈ r.yield)
    {a : T} (ha : MCFGAtom.tm a ∈ comp) :
    ([a], [MGFeature.cat (MGBase.lit a)]) ∈ (binMCFGToMG G).lexicon := by
  change _ ∈ buildLexicon G
  unfold buildLexicon
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨a, ?_, rfl⟩
  unfold allTerminals
  simp only [List.mem_flatMap, List.mem_filterMap]
  exact ⟨r, hr, comp, hcomp, MCFGAtom.tm a, ha, rfl⟩

/-- Helper: membership of a rule lexicon entry in `buildLexicon G`. -/
theorem mem_ruleLexicon_buildLexicon {G : MCFG N T} {rid : Nat} {r : MCFGRule N T}
    (hr : G.rules[rid]? = some r)
    {entry : List T × List (MGFeature (MGBase N T) MGLic)}
    (he : entry ∈ ruleLexicon G rid r) :
    entry ∈ (binMCFGToMG G).lexicon := by
  change entry ∈ buildLexicon G
  unfold buildLexicon
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨(rid, r), (mem_indexFrom_zero_iff G.rules rid r).mpr hr, he⟩

/-- Completing component `k` by scanning `revPref` down to `[]`. -/
theorem buildComp_derives {G : MCFG N T}
    (hrank : ∀ r, r ∈ G.rules → r.rhs.length ≤ 2)
    {rid k : Nat} {r : MCFGRule N T} {comp : List (MCFGAtom T)}
    (hr : G.rules[rid]? = some r) (hcomp : r.yield[k]? = some comp)
    {args : List (List (List T))} :
    ∀ (revPref suf : List (MCFGAtom T)) (ms : List (MGChain (MGBase N T) MGLic T)),
      comp = revPref.reverse ++ suf →
      ExactMap ms (buildDom r k revPref) (ruleVal r args) →
      MG.Derives (binMCFGToMG G)
        ⟨false,
          ⟨MCFG.evalComp args suf,
            revPref.map (atomToFeat (N := N)) ++
              [MGFeature.cat (MGBase.built rid k), MGFeature.licensee (Bank.O, k)]⟩,
          ms⟩ →
      ∃ ms',
        ExactMap ms' (buildDom r k []) (ruleVal r args) ∧
        MG.Derives (binMCFGToMG G)
          ⟨false,
            ⟨MCFG.evalComp args comp,
              [MGFeature.cat (MGBase.built rid k), MGFeature.licensee (Bank.O, k)]⟩,
            ms'⟩ := by
  have hr_mem : r ∈ G.rules := List.mem_of_getElem? hr
  have hwf : r.WellFormed G.dim := G.rules_wf r hr_mem
  have hcomp_mem : comp ∈ r.yield := List.mem_of_getElem? hcomp
  intro revPref
  induction revPref with
  | nil =>
    intro suf ms hsplit hex hder
    simp only [List.reverse_nil, List.nil_append] at hsplit
    subst hsplit
    exact ⟨ms, hex, hder⟩
  | cons atom rest ih =>
    intro suf ms hsplit hex hder
    have hsplit' : comp = rest.reverse ++ (atom :: suf) := by
      simpa [List.reverse_cons, List.append_assoc] using hsplit
    cases atom with
    | tm a =>
      have ha_in : MCFGAtom.tm a ∈ comp := by
        rw [hsplit']; exact List.mem_append_right _ (List.mem_cons_self ..)
      have hlit : MG.Derives (binMCFGToMG G) ⟨true, ⟨[a], [MGFeature.cat (MGBase.lit a)]⟩, []⟩ :=
        MG.Derives.lex (mem_lit_buildLexicon hr_mem hcomp_mem ha_in)
      have hsmc' : SMC (ms ++ []) := by simpa using hex.1
      have hstep : MG.Derives (binMCFGToMG G)
          ⟨false,
            ⟨MCFG.evalComp args (MCFGAtom.tm a :: suf),
              rest.map (atomToFeat (N := N)) ++
                [MGFeature.cat (MGBase.built rid k), MGFeature.licensee (Bank.O, k)]⟩,
            ms⟩ := by
        have hm := MG.Derives.merge2 hder hlit hsmc'
        simpa [MCFG.evalComp] using hm
      have hex' : ExactMap ms (buildDom r k rest) (ruleVal r args) :=
        exactMap_ext hex (buildDom_step_tm a rest) (fun _ _ => rfl)
      exact ih (MCFGAtom.tm a :: suf) ms hsplit' hex' hstep
    | var i j =>
      have hv_in : (i, j) ∈ r.varOccurrences := by
        simp only [MCFGRule.varOccurrences, List.mem_flatMap, List.mem_filterMap]
        refine ⟨comp, hcomp_mem, MCFGAtom.var i j, ?_, rfl⟩
        rw [hsplit']; exact List.mem_append_right _ (List.mem_cons_self ..)
      rcases var_index_lt_two hwf (hrank r hr_mem) hv_in with rfl | rfl
      · -- i = 0 (Bank.L)
        have hdom0 : buildDom r k (MCFGAtom.var 0 j :: rest) (Bank.L, j) := by
          simp [buildDom, compVars]
        have hmem_ch : ⟨ruleVal r args (Bank.L, j), [MGFeature.licensee (Bank.L, j)]⟩ ∈ ms :=
          hex.2.2 (Bank.L, j) hdom0
        obtain ⟨ms1, ms2, hms_eq⟩ := List.append_of_mem hmem_ch
        subst hms_eq
        have hstep : MG.Derives (binMCFGToMG G)
            ⟨false,
              ⟨MCFG.evalComp args (MCFGAtom.var 0 j :: suf),
                rest.map (atomToFeat (N := N)) ++
                  [MGFeature.cat (MGBase.built rid k), MGFeature.licensee (Bank.O, k)]⟩,
              ms1 ++ ms2⟩ := by
          exact MG.Derives.move1 hder
        have ⟨_, _, hrem⟩ := exactMap_remove hex
        have hex' : ExactMap (ms1 ++ ms2) (buildDom r k rest) (ruleVal r args) :=
          exactMap_ext hrem (buildDom_step_var0 hwf.2.1 hcomp hsplit) (fun _ _ => rfl)
        exact ih (MCFGAtom.var 0 j :: suf) (ms1 ++ ms2) hsplit' hex' hstep
      · -- i = 1 (Bank.R)
        have hdom1 : buildDom r k (MCFGAtom.var 1 j :: rest) (Bank.R, j) := by
          simp [buildDom, compVars]
        have hmem_ch : ⟨ruleVal r args (Bank.R, j), [MGFeature.licensee (Bank.R, j)]⟩ ∈ ms :=
          hex.2.2 (Bank.R, j) hdom1
        obtain ⟨ms1, ms2, hms_eq⟩ := List.append_of_mem hmem_ch
        subst hms_eq
        have hstep : MG.Derives (binMCFGToMG G)
            ⟨false,
              ⟨MCFG.evalComp args (MCFGAtom.var 1 j :: suf),
                rest.map (atomToFeat (N := N)) ++
                  [MGFeature.cat (MGBase.built rid k), MGFeature.licensee (Bank.O, k)]⟩,
              ms1 ++ ms2⟩ := by
          exact MG.Derives.move1 hder
        have ⟨_, _, hrem⟩ := exactMap_remove hex
        have hex' : ExactMap (ms1 ++ ms2) (buildDom r k rest) (ruleVal r args) :=
          exactMap_ext hrem (buildDom_step_var1 hwf.2.1 hcomp hsplit) (fun _ _ => rfl)
        exact ih (MCFGAtom.var 1 j :: suf) (ms1 ++ ms2) hsplit' hex' hstep

/-- Advance from `stage rid 0` to `stage rid k` for all `k ≤ r.yield.length`. -/
theorem buildAllComps_derives {G : MCFG N T}
    (hrank : ∀ r, r ∈ G.rules → r.rhs.length ≤ 2)
    {rid : Nat} {r : MCFGRule N T} (hr : G.rules[rid]? = some r)
    {args : List (List (List T))} {b0 : Bool} {ms0 : List (MGChain (MGBase N T) MGLic T)}
    (hex0 : ExactMap ms0 (stageDom r 0) (ruleVal r args))
    (hder0 : MG.Derives (binMCFGToMG G) ⟨b0, ⟨[], [MGFeature.cat (MGBase.stage rid 0)]⟩, ms0⟩) :
    ∀ k, k ≤ r.yield.length →
      ∃ b ms,
        ExactMap ms (stageDom r k) (ruleVal r args) ∧
        MG.Derives (binMCFGToMG G) ⟨b, ⟨[], [MGFeature.cat (MGBase.stage rid k)]⟩, ms⟩ := by
  intro k
  induction k with
  | zero => intro _; exact ⟨b0, ms0, hex0, hder0⟩
  | succ k ih =>
    intro hkle
    obtain ⟨bk, msk, hexk, hderk⟩ := ih (by omega)
    have hlt : k < r.yield.length := by omega
    cases hcomp : r.yield[k]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at hcomp; omega
    | some comp =>
      -- 1. Merge1 builder lexical item with `stage rid k`
      have hbuild_lex :
          ([], MGFeature.sel (MGBase.stage rid k) ::
                comp.reverse.map (atomToFeat (N := N)) ++
                [MGFeature.cat (MGBase.built rid k), MGFeature.licensee (Bank.O, k)]) ∈
            (binMCFGToMG G).lexicon := by
        apply mem_ruleLexicon_buildLexicon hr
        unfold ruleLexicon
        simp only [List.mem_append, List.mem_flatMap, List.mem_cons]
        left; right
        exact ⟨(k, comp), (mem_indexFrom_zero_iff r.yield k comp).mpr hcomp, Or.inl rfl⟩
      have hstart_build : MG.Derives (binMCFGToMG G)
          ⟨false,
            ⟨MCFG.evalComp args [],
              comp.reverse.map (atomToFeat (N := N)) ++
                [MGFeature.cat (MGBase.built rid k), MGFeature.licensee (Bank.O, k)]⟩,
            msk⟩ := by
        simpa [MCFG.evalComp] using MG.Derives.merge1 (MG.Derives.lex hbuild_lex) hderk
      have hex_start : ExactMap msk (buildDom r k comp.reverse) (ruleVal r args) :=
        exactMap_ext hexk (stageDom_eq_buildDom_start hcomp) (fun _ _ => rfl)
      -- 2. Run `buildComp_derives` down to `built rid k`
      have hsplit0 : comp = comp.reverse.reverse ++ [] := by simp
      obtain ⟨ms_built, hex_built, hder_built⟩ :=
        buildComp_derives hrank hr hcomp comp.reverse [] msk hsplit0 hex_start hstart_build
      -- 3. Park finished component into `(Bank.O, k)` via Merge3
      have hpark_lex :
          ([], [MGFeature.sel (MGBase.built rid k), MGFeature.cat (MGBase.stage rid (k + 1))]) ∈
            (binMCFGToMG G).lexicon := by
        apply mem_ruleLexicon_buildLexicon hr
        unfold ruleLexicon
        simp only [List.mem_append, List.mem_flatMap, List.mem_cons]
        left; right
        exact ⟨(k, comp), (mem_indexFrom_zero_iff r.yield k comp).mpr hcomp, Or.inr (Or.inl rfl)⟩
      have hfresh : ¬buildDom r k [] (Bank.O, k) := by simp [buildDom]
      have hvalk : ruleVal r args (Bank.O, k) = MCFG.evalComp args comp := by
        simp [ruleVal, hcomp]
      have hex_parked :
          ExactMap (⟨MCFG.evalComp args comp, [MGFeature.licensee (Bank.O, k)]⟩ :: ms_built)
            (stageDom r (k + 1)) (ruleVal r args) :=
        exactMap_ext (exactMap_cons_fresh hex_built hfresh hvalk)
          buildDom_end_insert (fun _ _ => rfl)
      have hder_next : MG.Derives (binMCFGToMG G)
          ⟨false, ⟨[], [MGFeature.cat (MGBase.stage rid (k + 1))]⟩,
            ⟨MCFG.evalComp args comp, [MGFeature.licensee (Bank.O, k)]⟩ :: ms_built⟩ := by
        exact MG.Derives.merge3 (MG.Derives.lex hpark_lex) hder_built hex_parked.1
      exact ⟨false, _, hex_parked, hder_next⟩

/-- Copy all `d = G.dim r.lhs` components from bank `O` to target bank `side`,
    ending in `nt r.lhs side`. -/
theorem copyAll_derives {G : MCFG N T}
    {rid : Nat} {r : MCFGRule N T} (hr : G.rules[rid]? = some r)
    (side : Side) (tup : List (List T)) :
    ∀ rem k, k + rem = G.dim r.lhs →
      k < G.dim r.lhs →
      ∀ ms,
        ExactMap ms (copyDom (G.dim r.lhs) side k) (fun m => (tup[m.2]?).getD []) →
        MG.Derives (binMCFGToMG G)
          ⟨false, ⟨[], [MGFeature.cat (MGBase.copyStage rid side k)]⟩, ms⟩ →
        ∃ ms',
          ExactMap ms' (fun m => ∃ j, j < G.dim r.lhs ∧ m = (side.toBank, j))
            (fun m => (tup[m.2]?).getD []) ∧
          MG.Derives (binMCFGToMG G)
            ⟨false, ⟨[], [MGFeature.cat (MGBase.nt r.lhs side)]⟩, ms'⟩ := by
  intro rem
  induction rem with
  | zero => intro k hsum hk; omega
  | succ rem' ih =>
    intro k hsum hk ms hex hder
    -- 1. Merge1 lift lexical item with `copyStage rid side k`
    have hlift_lex :
        ([], [MGFeature.sel (MGBase.copyStage rid side k),
              MGFeature.licensor (Bank.O, k),
              MGFeature.cat (MGBase.copied rid side k),
              MGFeature.licensee (side.toBank, k)]) ∈ (binMCFGToMG G).lexicon := by
      apply mem_ruleLexicon_buildLexicon hr
      unfold ruleLexicon
      simp only [List.mem_append, List.mem_flatMap, List.mem_cons]
      right
      refine ⟨side, by cases side <;> simp, Or.inr ?_⟩
      exact ⟨k, List.mem_range.mpr hk, Or.inl rfl⟩
    have hstep1 : MG.Derives (binMCFGToMG G)
        ⟨false,
          ⟨[], [MGFeature.licensor (Bank.O, k),
                MGFeature.cat (MGBase.copied rid side k),
                MGFeature.licensee (side.toBank, k)]⟩,
          ms⟩ := by
      simpa using MG.Derives.merge1 (MG.Derives.lex hlift_lex) hder
    -- 2. Move1 on `(Bank.O, k)`
    have hdomO : copyDom (G.dim r.lhs) side k (Bank.O, k) :=
      Or.inr ⟨k, Nat.le_refl _, hk, rfl⟩
    have hmemO : ⟨(tup[k]?).getD [], [MGFeature.licensee (Bank.O, k)]⟩ ∈ ms :=
      hex.2.2 (Bank.O, k) hdomO
    obtain ⟨ms1, ms2, hms_eq⟩ := List.append_of_mem hmemO
    subst hms_eq
    have hstep2 : MG.Derives (binMCFGToMG G)
        ⟨false,
          ⟨(tup[k]?).getD [],
            [MGFeature.cat (MGBase.copied rid side k), MGFeature.licensee (side.toBank, k)]⟩,
          ms1 ++ ms2⟩ := by
      simpa using MG.Derives.move1 hstep1
    have ⟨_, _, hrem⟩ := exactMap_remove hex
    -- 3. Merge3 park lexical item
    let nextCat : MGBase N T :=
      if k + 1 < G.dim r.lhs then MGBase.copyStage rid side (k + 1)
      else MGBase.nt r.lhs side
    have hpark_lex :
        ([], [MGFeature.sel (MGBase.copied rid side k), MGFeature.cat nextCat]) ∈
          (binMCFGToMG G).lexicon := by
      apply mem_ruleLexicon_buildLexicon hr
      unfold ruleLexicon
      simp only [List.mem_append, List.mem_flatMap, List.mem_cons]
      right
      refine ⟨side, by cases side <;> simp, Or.inr ?_⟩
      exact ⟨k, List.mem_range.mpr hk, Or.inr (Or.inl rfl)⟩
    have hfresh : ¬(copyDom (G.dim r.lhs) side k (side.toBank, k) ∧ (side.toBank, k) ≠ (Bank.O, k)) := by
      rintro ⟨(⟨j, hj, heq⟩ | ⟨j, _, _, heq⟩), _⟩
      · have : k = j := by injection heq
        omega
      · have : side.toBank = Bank.O := by injection heq
        exact Side.toBank_ne_O side this
    have hex_next :
        ExactMap (⟨(tup[k]?).getD [], [MGFeature.licensee (side.toBank, k)]⟩ :: (ms1 ++ ms2))
          (copyDom (G.dim r.lhs) side (k + 1)) (fun m => (tup[m.2]?).getD []) :=
      exactMap_ext (exactMap_cons_fresh hrem hfresh rfl) (copyDom_step hk) (fun _ _ => rfl)
    have hstep3 : MG.Derives (binMCFGToMG G)
        ⟨false, ⟨[], [MGFeature.cat nextCat]⟩,
          ⟨(tup[k]?).getD [], [MGFeature.licensee (side.toBank, k)]⟩ :: (ms1 ++ ms2)⟩ :=
      MG.Derives.merge3 (MG.Derives.lex hpark_lex) hstep2 hex_next.1
    by_cases hlt' : k + 1 < G.dim r.lhs
    · have hnext_eq : nextCat = MGBase.copyStage rid side (k + 1) := by simp [nextCat, hlt']
      rw [hnext_eq] at hstep3
      exact ih (k + 1) (by omega) hlt' _ hex_next hstep3
    · have hnext_eq : nextCat = MGBase.nt r.lhs side := by simp [nextCat, hlt']
      have heq_d : k + 1 = G.dim r.lhs := by omega
      rw [hnext_eq] at hstep3
      rw [heq_d] at hex_next
      exact ⟨_, exactMap_ext hex_next copyDom_end (fun _ _ => rfl), hstep3⟩

/-- Inductive list helper for mutual structural recursion on `MCFG.Yield` / `MCFG.YieldList`. -/
inductive CompleteList (G : MCFG N T) : List N → List (List (List T)) → Prop where
  | nil : CompleteList G [] []
  | cons {A : N} {As : List N} {tup : List (List T)} {tups : List (List (List T))} :
      (∀ side : Side, ∃ ms,
        ExactMap ms (fun m => ∃ j, j < G.dim A ∧ m = (side.toBank, j))
          (fun m => (tup[m.2]?).getD []) ∧
        MG.Derives (binMCFGToMG G) ⟨false, ⟨[], [MGFeature.cat (MGBase.nt A side)]⟩, ms⟩) →
      CompleteList G As tups →
      CompleteList G (A :: As) (tup :: tups)

theorem getElem?_of_mem {α : Type} {x : α} {L : List α} (h : x ∈ L) :
    ∃ idx : Nat, L[idx]? = some x := by
  induction L with
  | nil => simp at h
  | cons a t ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · exact ⟨0, rfl⟩
    · obtain ⟨idx, hidx⟩ := ih ht
      exact ⟨idx + 1, by simpa using hidx⟩

mutual
  theorem binMCFGToMG_complete {G : MCFG N T}
      (hrank : ∀ r, r ∈ G.rules → r.rhs.length ≤ 2)
      {A : N} {tup : List (List T)} :
      MCFG.Yield G A tup →
      ∀ side : Side, ∃ ms,
        ExactMap ms (fun m => ∃ j, j < G.dim A ∧ m = (side.toBank, j))
          (fun m => (tup[m.2]?).getD []) ∧
        MG.Derives (binMCFGToMG G) ⟨false, ⟨[], [MGFeature.cat (MGBase.nt A side)]⟩, ms⟩
    | @MCFG.Yield.rule _ _ _ r args hr hargs_raw => by
      have hargs := binMCFGToMG_complete_list hrank hargs_raw
      obtain ⟨rid, hrid⟩ := getElem?_of_mem hr
      have hwf := G.rules_wf r hr
      have hlen_le := hrank r hr
      -- Step 1: Reach `stage rid 0`
      have hstage0 : ∃ b0 ms0,
          ExactMap ms0 (stageDom r 0) (ruleVal r args) ∧
          MG.Derives (binMCFGToMG G) ⟨b0, ⟨[], [MGFeature.cat (MGBase.stage rid 0)]⟩, ms0⟩ := by
        cases hrhs : r.rhs with
        | nil =>
          rw [hrhs] at hargs
          cases hargs
          have hinit_lex : ([], [MGFeature.cat (MGBase.stage rid 0)]) ∈ (binMCFGToMG G).lexicon := by
            apply mem_ruleLexicon_buildLexicon hrid
            unfold ruleLexicon
            simp [hrhs]
          have hdom0 : ∀ m, False ↔ stageDom r 0 m := by
            intro m; rw [stageDom_zero_iff hwf m, hrhs]; simp
          exact ⟨true, [], exactMap_ext (exactMap_nil (ruleVal r [])) hdom0 (fun _ h => False.elim h),
            MG.Derives.lex hinit_lex⟩
        | cons B rest =>
          cases rest with
          | nil =>
            rw [hrhs] at hargs
            cases hargs with
            | @cons _ _ tupB _ hB hnil =>
              cases hnil
              obtain ⟨msB, hexB, hderB⟩ := hB Side.L
              have hinit_lex :
                  ([], [MGFeature.sel (MGBase.nt B Side.L), MGFeature.cat (MGBase.stage rid 0)]) ∈
                    (binMCFGToMG G).lexicon := by
                apply mem_ruleLexicon_buildLexicon hrid
                unfold ruleLexicon
                simp [hrhs]
              have hder0 : MG.Derives (binMCFGToMG G)
                  ⟨false, ⟨[], [MGFeature.cat (MGBase.stage rid 0)]⟩, msB⟩ := by
                simpa using MG.Derives.merge1 (MG.Derives.lex hinit_lex) hderB
              have hex0 : ExactMap msB (stageDom r 0) (ruleVal r [tupB]) := by
                refine exactMap_ext hexB ?_ ?_
                · intro m
                  rw [stageDom_zero_iff hwf m, hrhs]
                  simp [Side.toBank]
                · intro m hm
                  obtain ⟨j, _, hm'⟩ := hm; subst hm'
                  simp only [Side.toBank, ruleVal]
                  exact (argPiece_eq_getD rfl).symm
              exact ⟨false, msB, hex0, hder0⟩
          | cons C rest' =>
            cases rest' with
            | nil =>
              rw [hrhs] at hargs
              cases hargs with
              | @cons _ _ tupB _ hB hrest =>
                cases hrest with
                | @cons _ _ tupC _ hC hnil =>
                  cases hnil
                  obtain ⟨msB, hexB, hderB⟩ := hB Side.L
                  obtain ⟨msC, hexC, hderC⟩ := hC Side.R
                  have hinit_lex :
                      ([], [MGFeature.sel (MGBase.nt B Side.L),
                            MGFeature.sel (MGBase.nt C Side.R),
                            MGFeature.cat (MGBase.stage rid 0)]) ∈ (binMCFGToMG G).lexicon := by
                    apply mem_ruleLexicon_buildLexicon hrid
                    unfold ruleLexicon
                    simp [hrhs]
                  have hmid : MG.Derives (binMCFGToMG G)
                      ⟨false, ⟨[], [MGFeature.sel (MGBase.nt C Side.R),
                                    MGFeature.cat (MGBase.stage rid 0)]⟩, msB⟩ := by
                    simpa using MG.Derives.merge1 (MG.Derives.lex hinit_lex) hderB
                  have hexB' : ExactMap msB (fun m => ∃ j, j < G.dim B ∧ m = (Bank.L, j))
                      (ruleVal r [tupB, tupC]) := by
                    refine exactMap_ext hexB (fun _ => Iff.rfl) ?_
                    intro m ⟨j, _, hm'⟩; subst hm'
                    simp only [Side.toBank, ruleVal]
                    exact (argPiece_eq_getD rfl).symm
                  have hexC' : ExactMap msC (fun m => ∃ j, j < G.dim C ∧ m = (Bank.R, j))
                      (ruleVal r [tupB, tupC]) := by
                    refine exactMap_ext hexC (fun _ => Iff.rfl) ?_
                    intro m ⟨j, _, hm'⟩; subst hm'
                    simp only [Side.toBank, ruleVal]
                    exact (argPiece_eq_getD rfl).symm
                  have hdisj : ∀ m, (∃ j, j < G.dim B ∧ m = (Bank.L, j)) →
                      ¬(∃ j, j < G.dim C ∧ m = (Bank.R, j)) := by
                    rintro m ⟨j1, _, rfl⟩ ⟨j2, _, heq⟩; simp at heq
                  have hexBC := exactMap_disjoint_append hexB' hexC' hdisj
                  have hder0 : MG.Derives (binMCFGToMG G)
                      ⟨false, ⟨[], [MGFeature.cat (MGBase.stage rid 0)]⟩, msB ++ msC⟩ := by
                    simpa using MG.Derives.merge2 hmid hderC hexBC.1
                  have hex0 : ExactMap (msB ++ msC) (stageDom r 0) (ruleVal r [tupB, tupC]) := by
                    refine exactMap_ext hexBC ?_ (fun _ _ => rfl)
                    intro m
                    rw [stageDom_zero_iff hwf m, hrhs]
                    simp
                  exact ⟨false, msB ++ msC, hex0, hder0⟩
            | cons _ _ =>
              rw [hrhs] at hlen_le; simp at hlen_le
      -- Step 2: Build all `r.yield.length` components into bank `O`
      obtain ⟨b0, ms0, hex0, hder0⟩ := hstage0
      obtain ⟨bEnd, msEnd, hexEnd, hderEnd⟩ :=
        buildAllComps_derives hrank hrid hex0 hder0 r.yield.length (Nat.le_refl _)
      -- Step 3: Bridge to `copyStage rid side 0` and copy `O → side`
      intro side
      have hbridge_lex :
          ([], [MGFeature.sel (MGBase.stage rid r.yield.length),
                MGFeature.cat (MGBase.copyStage rid side 0)]) ∈ (binMCFGToMG G).lexicon := by
        apply mem_ruleLexicon_buildLexicon hrid
        unfold ruleLexicon
        simp only [List.mem_append, List.mem_flatMap, List.mem_cons]
        right
        exact ⟨side, by cases side <;> simp, Or.inl rfl⟩
      have hder_c0 : MG.Derives (binMCFGToMG G)
          ⟨false, ⟨[], [MGFeature.cat (MGBase.copyStage rid side 0)]⟩, msEnd⟩ := by
        simpa using MG.Derives.merge1 (MG.Derives.lex hbridge_lex) hderEnd
      have hex_c0 : ExactMap msEnd (copyDom (G.dim r.lhs) side 0)
          (fun m => ((MCFG.evalYield args r.yield)[m.2]?).getD []) := by
        refine exactMap_ext hexEnd (stageDom_end_eq_copyDom_zero (G.dim r.lhs) hwf.1 side) ?_
        intro ⟨bank, m⟩ hm
        cases bank with
        | O => exact ruleVal_O_eq_evalYield
        | L => simp [stageDom, compsVars] at hm
        | R => simp [stageDom, compsVars] at hm
      exact copyAll_derives hrid side (MCFG.evalYield args r.yield)
        (G.dim r.lhs) 0 (by omega) (G.dim_pos r.lhs) msEnd hex_c0 hder_c0

  theorem binMCFGToMG_complete_list {G : MCFG N T}
      (hrank : ∀ r, r ∈ G.rules → r.rhs.length ≤ 2)
      {As : List N} {args : List (List (List T))} :
      MCFG.YieldList G As args → CompleteList G As args
    | MCFG.YieldList.nil => CompleteList.nil
    | MCFG.YieldList.cons hy hrest =>
      CompleteList.cons (binMCFGToMG_complete hrank hy)
        (binMCFGToMG_complete_list hrank hrest)
end

theorem binMCFGToMG_lang_of_mcfg {G : MCFG N T}
    (hrank : ∀ r, r ∈ G.rules → r.rhs.length ≤ 2) {w : List T}
    (h : G.Lang w) : (binMCFGToMG G).Lang w := by
  obtain ⟨ms, hex, hder_start⟩ := binMCFGToMG_complete hrank h Side.L
  have hstart_lex :
      ([], [MGFeature.sel (MGBase.nt G.start Side.L),
            MGFeature.licensor (Bank.L, 0),
            MGFeature.cat MGBase.start]) ∈ (binMCFGToMG G).lexicon := by
    change _ ∈ buildLexicon G
    unfold buildLexicon
    exact List.mem_cons_self ..
  have hmid : MG.Derives (binMCFGToMG G)
      ⟨false, ⟨[], [MGFeature.licensor (Bank.L, 0), MGFeature.cat MGBase.start]⟩, ms⟩ := by
    simpa using MG.Derives.merge1 (MG.Derives.lex hstart_lex) hder_start
  have hdom0 : ∃ j, j < G.dim G.start ∧ (Bank.L, 0) = (Side.L.toBank, j) :=
    ⟨0, by rw [G.dim_start]; omega, rfl⟩
  have hmem0 : ⟨w, [MGFeature.licensee (Bank.L, 0)]⟩ ∈ ms := by
    simpa using hex.2.2 (Bank.L, 0) hdom0
  obtain ⟨ms1, ms2, hms_eq⟩ := List.append_of_mem hmem0
  subst hms_eq
  have hfin : MG.Derives (binMCFGToMG G)
      ⟨false, ⟨w, [MGFeature.cat MGBase.start]⟩, ms1 ++ ms2⟩ := by
    simpa using MG.Derives.move1 hmid
  have ⟨_, _, hrem⟩ := exactMap_remove hex
  have hnil : ms1 ++ ms2 = [] := by
    apply exactMap_empty_eq_nil hrem
    rintro m ⟨⟨j, hj, rfl⟩, hne⟩
    rw [G.dim_start] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact hne rfl
  rw [hnil] at hfin
  exact ⟨false, hfin⟩

/-! ### Part 5: Soundness (`MG.Derives (binMCFGToMG G) → MGInv G`) -/

/-- Exact inductive invariant characterizing all 18 expression shapes
    of `binMCFGToMG G`. Every constructor has a disjoint syntactic signature. -/
inductive MGInv (G : MCFG N T) : MGExpr (MGBase N T) MGLic T → Prop where
  | startLex :
      MGInv G ⟨true, ⟨[], [MGFeature.sel (MGBase.nt G.start Side.L),
                           MGFeature.licensor (Bank.L, 0),
                           MGFeature.cat MGBase.start]⟩, []⟩
  | startMid {w : List T} {ms : List (MGChain (MGBase N T) MGLic T)} :
      G.Lang w →
      ExactMap ms (fun m => m = (Bank.L, 0)) (fun _ => w) →
      MGInv G ⟨false, ⟨[], [MGFeature.licensor (Bank.L, 0), MGFeature.cat MGBase.start]⟩, ms⟩
  | startDone {w : List T} :
      G.Lang w →
      MGInv G ⟨false, ⟨w, [MGFeature.cat MGBase.start]⟩, []⟩
  | litLex (a : T) :
      MGInv G ⟨true, ⟨[a], [MGFeature.cat (MGBase.lit a)]⟩, []⟩
  | ntReady {A : N} {side : Side} {tup : List (List T)}
      {ms : List (MGChain (MGBase N T) MGLic T)} :
      MCFG.Yield G A tup →
      ExactMap ms (fun m => ∃ j, j < G.dim A ∧ m = (side.toBank, j))
        (fun m => (tup[m.2]?).getD []) →
      MGInv G ⟨false, ⟨[], [MGFeature.cat (MGBase.nt A side)]⟩, ms⟩
  | initUnaryLex {rid : Nat} {r : MCFGRule N T} {B : N} :
      G.rules[rid]? = some r →
      r.rhs = [B] →
      MGInv G ⟨true, ⟨[], [MGFeature.sel (MGBase.nt B Side.L),
                           MGFeature.cat (MGBase.stage rid 0)]⟩, []⟩
  | initBinLex {rid : Nat} {r : MCFGRule N T} {B C : N} :
      G.rules[rid]? = some r →
      r.rhs = [B, C] →
      MGInv G ⟨true, ⟨[], [MGFeature.sel (MGBase.nt B Side.L),
                           MGFeature.sel (MGBase.nt C Side.R),
                           MGFeature.cat (MGBase.stage rid 0)]⟩, []⟩
  | initBinMid {rid : Nat} {r : MCFGRule N T} {B C : N} {tup0 : List (List T)}
      {ms : List (MGChain (MGBase N T) MGLic T)} :
      G.rules[rid]? = some r →
      r.rhs = [B, C] →
      MCFG.Yield G B tup0 →
      ExactMap ms (fun m => ∃ j, j < G.dim B ∧ m = (Bank.L, j))
        (fun m => (tup0[m.2]?).getD []) →
      MGInv G ⟨false, ⟨[], [MGFeature.sel (MGBase.nt C Side.R),
                            MGFeature.cat (MGBase.stage rid 0)]⟩, ms⟩
  | stageReady {b : Bool} {rid k : Nat} {r : MCFGRule N T}
      {args : List (List (List T))} {ms : List (MGChain (MGBase N T) MGLic T)} :
      G.rules[rid]? = some r →
      k ≤ r.yield.length →
      MCFG.YieldList G r.rhs args →
      ExactMap ms (stageDom r k) (ruleVal r args) →
      MGInv G ⟨b, ⟨[], [MGFeature.cat (MGBase.stage rid k)]⟩, ms⟩
  | buildLex {rid k : Nat} {r : MCFGRule N T} {comp : List (MCFGAtom T)} :
      G.rules[rid]? = some r →
      r.yield[k]? = some comp →
      MGInv G ⟨true, ⟨[], MGFeature.sel (MGBase.stage rid k) ::
                           comp.reverse.map (atomToFeat (N := N)) ++
                           [MGFeature.cat (MGBase.built rid k), MGFeature.licensee (Bank.O, k)]⟩, []⟩
  | buildActive {rid k : Nat} {r : MCFGRule N T} {comp revPref suf : List (MCFGAtom T)}
      {args : List (List (List T))} {ms : List (MGChain (MGBase N T) MGLic T)}
      {α : List (MGFeature (MGBase N T) MGLic)} :
      G.rules[rid]? = some r →
      r.yield[k]? = some comp →
      comp = revPref.reverse ++ suf →
      α = revPref.map (atomToFeat (N := N)) ++
          [MGFeature.cat (MGBase.built rid k), MGFeature.licensee (Bank.O, k)] →
      MCFG.YieldList G r.rhs args →
      ExactMap ms (buildDom r k revPref) (ruleVal r args) →
      MGInv G ⟨false, ⟨MCFG.evalComp args suf, α⟩, ms⟩
  | parkBuiltLex {rid k : Nat} {r : MCFGRule N T} {comp : List (MCFGAtom T)} :
      G.rules[rid]? = some r →
      r.yield[k]? = some comp →
      MGInv G ⟨true, ⟨[], [MGFeature.sel (MGBase.built rid k),
                           MGFeature.cat (MGBase.stage rid (k + 1))]⟩, []⟩
  | bridgeLex {rid : Nat} {r : MCFGRule N T} {side : Side} :
      G.rules[rid]? = some r →
      MGInv G ⟨true, ⟨[], [MGFeature.sel (MGBase.stage rid r.yield.length),
                           MGFeature.cat (MGBase.copyStage rid side 0)]⟩, []⟩
  | copyStageReady {rid k : Nat} {r : MCFGRule N T} {side : Side} {tup : List (List T)}
      {ms : List (MGChain (MGBase N T) MGLic T)} :
      G.rules[rid]? = some r →
      k < G.dim r.lhs →
      MCFG.Yield G r.lhs tup →
      ExactMap ms (copyDom (G.dim r.lhs) side k) (fun m => (tup[m.2]?).getD []) →
      MGInv G ⟨false, ⟨[], [MGFeature.cat (MGBase.copyStage rid side k)]⟩, ms⟩
  | copyLiftLex {rid k : Nat} {r : MCFGRule N T} {side : Side} :
      G.rules[rid]? = some r →
      k < G.dim r.lhs →
      MGInv G ⟨true, ⟨[], [MGFeature.sel (MGBase.copyStage rid side k),
                           MGFeature.licensor (Bank.O, k),
                           MGFeature.cat (MGBase.copied rid side k),
                           MGFeature.licensee (side.toBank, k)]⟩, []⟩
  | copyLiftMid {rid k : Nat} {r : MCFGRule N T} {side : Side} {tup : List (List T)}
      {ms : List (MGChain (MGBase N T) MGLic T)} :
      G.rules[rid]? = some r →
      k < G.dim r.lhs →
      MCFG.Yield G r.lhs tup →
      ExactMap ms (copyDom (G.dim r.lhs) side k) (fun m => (tup[m.2]?).getD []) →
      MGInv G ⟨false, ⟨[], [MGFeature.licensor (Bank.O, k),
                            MGFeature.cat (MGBase.copied rid side k),
                            MGFeature.licensee (side.toBank, k)]⟩, ms⟩
  | copiedReady {rid k : Nat} {r : MCFGRule N T} {side : Side} {tup : List (List T)}
      {ms : List (MGChain (MGBase N T) MGLic T)} :
      G.rules[rid]? = some r →
      k < G.dim r.lhs →
      MCFG.Yield G r.lhs tup →
      ExactMap ms (fun m => copyDom (G.dim r.lhs) side k m ∧ m ≠ (Bank.O, k))
        (fun m => (tup[m.2]?).getD []) →
      MGInv G ⟨false, ⟨(tup[k]?).getD [],
                        [MGFeature.cat (MGBase.copied rid side k),
                         MGFeature.licensee (side.toBank, k)]⟩, ms⟩
  | parkCopiedLex {rid k : Nat} {r : MCFGRule N T} {side : Side} :
      G.rules[rid]? = some r →
      k < G.dim r.lhs →
      MGInv G ⟨true, ⟨[], [MGFeature.sel (MGBase.copied rid side k),
                           MGFeature.cat (if k + 1 < G.dim r.lhs
                                          then MGBase.copyStage rid side (k + 1)
                                          else MGBase.nt r.lhs side)]⟩, []⟩

theorem MGInv.singleMover {G : MCFG N T} {e : MGExpr (MGBase N T) MGLic T}
    (h : MGInv G e) : SingleMover e.movers := by
  cases h with
  | startLex | startDone | litLex | initUnaryLex | initBinLex | buildLex
  | parkBuiltLex | bridgeLex | copyLiftLex | parkCopiedLex =>
    exact singleMover_nil
  | startMid _ hex | ntReady _ hex | initBinMid _ _ _ hex | stageReady _ _ _ hex
  | buildActive _ _ _ _ _ hex | copyStageReady _ _ _ hex | copyLiftMid _ _ _ hex
  | copiedReady _ _ _ hex =>
    exact exactMap_singleMover hex

/-- Helper: a `buildActive` feature list never has length 1 (`[cat x]`). -/
theorem buildActive_feats_ne_singleton {revPref : List (MCFGAtom T)} {rid k : Nat}
    {x : MGBase N T} :
    revPref.map (atomToFeat (N := N)) ++
      [MGFeature.cat (MGBase.built rid k), MGFeature.licensee (Bank.O, k)] ≠
    [MGFeature.cat x] := by
  intro heq
  have hlen := congrArg List.length heq
  simp at hlen

private theorem binMCFGToMG_merge1 {N T : Type} {G : MCFG N T}
  {s t : List T} {x : MGBase N T} {γ : List (MGFeature (MGBase N T) MGLic)} {b : Bool}
  {ms : List (MGChain (MGBase N T) MGLic T)}
  (ih1 : MGInv G { isLex := true, head := { str := s, feats := MGFeature.sel x :: γ }, movers := [] })
  (ih2 : MGInv G { isLex := b, head := { str := t, feats := [MGFeature.cat x] }, movers := ms }) :
  MGInv G { isLex := false, head := { str := s ++ t, feats := γ }, movers := ms } := by
  cases ih1 with
  | startLex =>
    cases ih2 with
    | @ntReady _ _ tup _ hy hex =>
      have hlen : tup.length = 1 := by rw [hy.length_eq, G.dim_start]
      cases tup with
      | nil => simp at hlen
      | cons w rest =>
        cases rest with
        | cons _ _ => simp at hlen
        | nil =>
          have hex' : ExactMap ms (fun m => m = (Bank.L, 0)) (fun _ => w) := by
            refine exactMap_ext hex ?_ ?_
            · intro m
              rw [G.dim_start]
              constructor
              · rintro ⟨j, hj, rfl⟩
                have : j = 0 := by omega
                subst this; rfl
              · rintro rfl; exact ⟨0, by omega, rfl⟩
            · rintro m ⟨j, hj, rfl⟩
              rw [G.dim_start] at hj
              have : j = 0 := by omega
              subst this; rfl
          simpa using MGInv.startMid hy hex'
    | buildActive _ _ _ hα _ _ => exact absurd hα.symm buildActive_feats_ne_singleton
  | @initUnaryLex rid r B hrid hrhs =>
    cases ih2 with
    | @ntReady _ _ tup _ hy hex =>
      have hwf := G.rules_wf r (List.mem_of_getElem? hrid)
      have hyl : MCFG.YieldList G r.rhs [tup] := by
        rw [hrhs]; exact MCFG.YieldList.cons hy MCFG.YieldList.nil
      have hex0 : ExactMap ms (stageDom r 0) (ruleVal r [tup]) := by
        refine exactMap_ext hex ?_ ?_
        · intro m; rw [stageDom_zero_iff hwf m, hrhs]; simp [Side.toBank]
        · intro m ⟨j, _, hm⟩; subst hm; simp only [Side.toBank, ruleVal]; exact (argPiece_eq_getD rfl).symm
      simpa using MGInv.stageReady hrid (Nat.zero_le _) hyl hex0
    | buildActive _ _ _ hα _ _ => exact absurd hα.symm buildActive_feats_ne_singleton
  | @initBinLex rid r B C hrid hrhs =>
    cases ih2 with
    | ntReady hy hex =>
      simpa using MGInv.initBinMid hrid hrhs hy hex
    | buildActive _ _ _ hα _ _ => exact absurd hα.symm buildActive_feats_ne_singleton
  | @buildLex rid k r comp hrid hcomp =>
    cases ih2 with
    | @stageReady _ _ _ r' args _ hrid' _ hyl hex =>
      rw [hrid] at hrid'; injection hrid' with hr_eq; subst hr_eq
      have hex' : ExactMap ms (buildDom r k comp.reverse) (ruleVal r args) :=
        exactMap_ext hex (stageDom_eq_buildDom_start hcomp) (fun _ _ => rfl)
      have hsplit : comp = comp.reverse.reverse ++ [] := by simp
      simpa [MCFG.evalComp] using MGInv.buildActive hrid hcomp hsplit rfl hyl hex'
    | buildActive _ _ _ hα _ _ => exact absurd hα.symm buildActive_feats_ne_singleton
  | parkBuiltLex _ _ =>
    cases ih2 with
    | buildActive _ _ _ hα _ _ => exact absurd hα.symm buildActive_feats_ne_singleton
  | @bridgeLex rid r side hrid =>
    cases ih2 with
    | @stageReady _ _ _ r' args _ hrid' _ hyl hex =>
      rw [hrid] at hrid'; injection hrid' with hr_eq; subst hr_eq
      have hwf := G.rules_wf r (List.mem_of_getElem? hrid)
      have hy : MCFG.Yield G r.lhs (MCFG.evalYield args r.yield) :=
        MCFG.Yield.rule (List.mem_of_getElem? hrid) hyl
      have hex' : ExactMap ms (copyDom (G.dim r.lhs) side 0)
          (fun m => ((MCFG.evalYield args r.yield)[m.2]?).getD []) := by
        refine exactMap_ext hex (stageDom_end_eq_copyDom_zero (G.dim r.lhs) hwf.1 side) ?_
        intro ⟨bank, m⟩ hm
        cases bank with
        | O => exact ruleVal_O_eq_evalYield
        | L => simp [stageDom, compsVars] at hm
        | R => simp [stageDom, compsVars] at hm
      simpa using MGInv.copyStageReady hrid (G.dim_pos r.lhs) hy hex'
    | buildActive _ _ _ hα _ _ => exact absurd hα.symm buildActive_feats_ne_singleton
  | @copyLiftLex rid k r side hrid hk =>
    cases ih2 with
    | @copyStageReady _ _ r' _ tup _ hrid' _ hy hex =>
      rw [hrid] at hrid'; injection hrid' with hr_eq; subst hr_eq
      simpa using MGInv.copyLiftMid hrid hk hy hex
    | buildActive _ _ _ hα _ _ => exact absurd hα.symm buildActive_feats_ne_singleton
  | parkCopiedLex _ _ =>
    cases ih2 with
    | buildActive _ _ _ hα _ _ => exact absurd hα.symm buildActive_feats_ne_singleton

private theorem binMCFGToMG_merge3 {N T : Type} {G : MCFG N T}
  {s t : List T} {x : MGBase N T} {f : MGLic} {γ δ' : List (MGFeature (MGBase N T) MGLic)} {b1 b2 : Bool}
  {ms1 ms2 : List (MGChain (MGBase N T) MGLic T)}
  (ih1 : MGInv G { isLex := b1, head := { str := s, feats := MGFeature.sel x :: γ }, movers := ms1 })
  (ih2 :
    MGInv G
      { isLex := b2, head := { str := t, feats := MGFeature.cat x :: MGFeature.licensee f :: δ' }, movers := ms2 }) :
  MGInv G
    { isLex := false, head := { str := s, feats := γ },
      movers := ms1 ++ { str := t, feats := MGFeature.licensee f :: δ' } :: ms2 } := by
  cases ih2 with
  | @buildActive rid k r comp revPref suf args _ _ hrid hcomp hsplit hα hyl hex =>
    cases revPref with
    | cons atom rest =>
      cases atom with
      | tm _ => simp [atomToFeat] at hα
      | var i _ => cases i <;> simp [atomToFeat] at hα
    | nil =>
      simp only [List.map_nil, List.nil_append, List.cons.injEq, MGFeature.cat.injEq,
        MGFeature.licensee.injEq] at hα
      obtain ⟨rfl, rfl, rfl⟩ := hα
      simp only [List.reverse_nil, List.nil_append] at hsplit
      cases ih1 with
      | @parkBuiltLex _ _ r' comp' hrid' hcomp' =>
        rw [hrid] at hrid'; injection hrid' with hr_eq; subst hr_eq
        have hklt : k < r.yield.length := by
          by_cases hlt : k < r.yield.length
          · exact hlt
          · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hcomp; simp at hcomp
        have hfresh : ¬buildDom r k [] (Bank.O, k) := by simp [buildDom]
        have hvalk : ruleVal r args (Bank.O, k) = MCFG.evalComp args suf := by
          subst hsplit; simp [ruleVal, hcomp]
        have hex' : ExactMap (⟨MCFG.evalComp args suf, [MGFeature.licensee (Bank.O, k)]⟩ :: ms2)
            (stageDom r (k + 1)) (ruleVal r args) :=
          exactMap_ext (exactMap_cons_fresh hex hfresh hvalk)
            buildDom_end_insert (fun _ _ => rfl)
        simpa using MGInv.stageReady hrid (by omega) hyl hex'
      | @buildActive _ _ _ _ revPref1 _ _ _ _ _ _ _ hα1 _ _ =>
        cases revPref1 with
        | nil => simp at hα1
        | cons a1 _ =>
          cases a1 with
          | tm _ => simp [atomToFeat] at hα1
          | var i _ => cases i <;> simp [atomToFeat] at hα1
  | @copiedReady rid k r side tup _ hrid hk hy hex =>
    cases ih1 with
    | @parkCopiedLex _ _ r' _ hrid' hk' =>
      rw [hrid] at hrid'; injection hrid' with hr_eq; subst hr_eq
      have hfresh : ¬(copyDom (G.dim r.lhs) side k (side.toBank, k) ∧
          (side.toBank, k) ≠ (Bank.O, k)) := by
        rintro ⟨(⟨j, hj, heq⟩ | ⟨j, _, _, heq⟩), _⟩
        · have : k = j := by injection heq
          omega
        · have : side.toBank = Bank.O := by injection heq
          exact Side.toBank_ne_O side this
      have hex_next :
          ExactMap (⟨(tup[k]?).getD [], [MGFeature.licensee (side.toBank, k)]⟩ :: ms2)
            (copyDom (G.dim r.lhs) side (k + 1)) (fun m => (tup[m.2]?).getD []) :=
        exactMap_ext (exactMap_cons_fresh hex hfresh rfl) (copyDom_step hk) (fun _ _ => rfl)
      by_cases hlt' : k + 1 < G.dim r.lhs
      · simpa [hlt'] using MGInv.copyStageReady hrid hlt' hy hex_next
      · have heq_d : k + 1 = G.dim r.lhs := by omega
        rw [heq_d] at hex_next
        simpa [hlt'] using MGInv.ntReady hy (exactMap_ext hex_next copyDom_end (fun _ _ => rfl))
    | @buildActive _ _ _ _ revPref1 _ _ _ _ _ _ _ hα1 _ _ =>
      cases revPref1 with
      | nil => simp at hα1
      | cons a1 _ =>
        cases a1 with
        | tm _ => simp [atomToFeat] at hα1
        | var i _ => cases i <;> simp [atomToFeat] at hα1

/-- Soundness of `binMCFGToMG`: every derivable MG expression satisfies `MGInv G`. -/
theorem binMCFGToMG_sound {G : MCFG N T}
    (hrank : ∀ r, r ∈ G.rules → r.rhs.length ≤ 2)
    {e : MGExpr (MGBase N T) MGLic T} (h : MG.Derives (binMCFGToMG G) e) :
    MGInv G e := by
  induction h with
  | @lex w α hlex =>
    change (w, α) ∈ buildLexicon G at hlex
    unfold buildLexicon at hlex
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap] at hlex
    rcases hlex with heq | ⟨a, _, heq⟩ | ⟨⟨rid, r⟩, hrid_mem, hrl⟩
    · injection heq with hw hα; subst hw; subst hα
      exact MGInv.startLex
    · injection heq with hw hα; subst hw; subst hα
      exact MGInv.litLex a
    · have hrid : G.rules[rid]? = some r := (mem_indexFrom_zero_iff G.rules rid r).mp hrid_mem
      have hwf := G.rules_wf r (List.mem_of_getElem? hrid)
      unfold ruleLexicon at hrl
      simp only [List.mem_append] at hrl
      rcases hrl with (hinit | hbuild) | hcopy
      · cases hrhs : r.rhs with
        | nil =>
          simp [hrhs] at hinit
          obtain ⟨rfl, rfl⟩ := hinit
          have hyl : MCFG.YieldList G r.rhs [] := by rw [hrhs]; exact MCFG.YieldList.nil
          have hdom0 : ∀ m, False ↔ stageDom r 0 m := by
            intro m; rw [stageDom_zero_iff hwf m, hrhs]; simp
          exact MGInv.stageReady hrid (Nat.zero_le _) hyl
            (exactMap_ext (exactMap_nil (ruleVal r [])) hdom0 (fun _ hf => False.elim hf))
        | cons B rest =>
          cases rest with
          | nil =>
            simp [hrhs] at hinit
            obtain ⟨rfl, rfl⟩ := hinit
            exact MGInv.initUnaryLex hrid hrhs
          | cons C rest' =>
            cases rest' with
            | nil =>
              simp [hrhs] at hinit
              obtain ⟨rfl, rfl⟩ := hinit
              exact MGInv.initBinLex hrid hrhs
            | cons _ _ => simp [hrhs] at hinit
      · simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hbuild
        obtain ⟨⟨k, comp⟩, hk_mem, h1 | h2⟩ := hbuild
        · have hcomp : r.yield[k]? = some comp := (mem_indexFrom_zero_iff r.yield k comp).mp hk_mem
          injection h1 with hw hα; subst hw; subst hα
          exact MGInv.buildLex hrid hcomp
        · have hcomp : r.yield[k]? = some comp := (mem_indexFrom_zero_iff r.yield k comp).mp hk_mem
          injection h2 with hw hα; subst hw; subst hα
          exact MGInv.parkBuiltLex hrid hcomp
      · simp only [List.mem_flatMap, List.mem_cons] at hcopy
        obtain ⟨side, _, hbr | hcp⟩ := hcopy
        · injection hbr with hw hα; subst hw; subst hα
          exact MGInv.bridgeLex hrid
        · simp only [List.not_mem_nil, or_false] at hcp
          obtain ⟨k, hk_mem, h1 | h2⟩ := hcp
          · have hk : k < G.dim r.lhs := List.mem_range.mp hk_mem
            injection h1 with hw hα; subst hw; subst hα
            exact MGInv.copyLiftLex hrid hk
          · have hk : k < G.dim r.lhs := List.mem_range.mp hk_mem
            injection h2 with hw hα; subst hw; subst hα
            exact MGInv.parkCopiedLex hrid hk
  | @merge1 s t x γ b ms h1 h2 ih1 ih2 =>
    exact binMCFGToMG_merge1 ih1 ih2
  | @merge2 s t x γ b ms1 ms2 h1 h2 hsmc12 ih1 ih2 =>
    cases ih1 with
    | @initBinMid rid r B C tup0 _ hrid hrhs hyB hexB =>
      cases ih2 with
      | @ntReady _ _ tup1 _ hyC hexC =>
        have hwf := G.rules_wf r (List.mem_of_getElem? hrid)
        have hyl : MCFG.YieldList G r.rhs [tup0, tup1] := by
          rw [hrhs]
          exact MCFG.YieldList.cons hyB (MCFG.YieldList.cons hyC MCFG.YieldList.nil)
        have hexB' : ExactMap ms1 (fun m => ∃ j, j < G.dim B ∧ m = (Bank.L, j))
            (ruleVal r [tup0, tup1]) := by
          refine exactMap_ext hexB (fun _ => Iff.rfl) ?_
          intro m ⟨j, _, hm⟩; subst hm; simp only [ruleVal]; exact (argPiece_eq_getD rfl).symm
        have hexC' : ExactMap ms2 (fun m => ∃ j, j < G.dim C ∧ m = (Bank.R, j))
            (ruleVal r [tup0, tup1]) := by
          refine exactMap_ext hexC (fun _ => Iff.rfl) ?_
          intro m ⟨j, _, hm⟩; subst hm; simp only [Side.toBank, ruleVal]; exact (argPiece_eq_getD rfl).symm
        have hdisj : ∀ m, (∃ j, j < G.dim B ∧ m = (Bank.L, j)) →
            ¬(∃ j, j < G.dim C ∧ m = (Bank.R, j)) := by
          rintro m ⟨_, _, rfl⟩ ⟨_, _, heq⟩; simp at heq
        have hexBC := exactMap_disjoint_append hexB' hexC' hdisj
        have hex0 : ExactMap (ms1 ++ ms2) (stageDom r 0) (ruleVal r [tup0, tup1]) := by
          refine exactMap_ext hexBC ?_ (fun _ _ => rfl)
          intro m; rw [stageDom_zero_iff hwf m, hrhs]; simp
        simpa using MGInv.stageReady hrid (Nat.zero_le _) hyl hex0
      | buildActive _ _ _ hα _ _ => exact absurd hα.symm buildActive_feats_ne_singleton
    | @buildActive rid k r comp revPref suf args _ _ hrid hcomp hsplit hα hyl hex =>
      cases revPref with
      | nil => simp at hα
      | cons atom rest =>
        cases atom with
        | tm a =>
          simp only [List.map_cons, atomToFeat, List.cons_append, List.cons.injEq,
            MGFeature.sel.injEq] at hα
          obtain ⟨rfl, rfl⟩ := hα
          cases ih2 with
          | litLex _ =>
            have hsplit' : comp = rest.reverse ++ (MCFGAtom.tm a :: suf) := by
              simpa [List.reverse_cons, List.append_assoc] using hsplit
            have hex' : ExactMap (ms1 ++ []) (buildDom r k rest) (ruleVal r args) := by
              simpa using exactMap_ext hex (buildDom_step_tm a rest) (fun _ _ => rfl)
            simpa [MCFG.evalComp] using MGInv.buildActive hrid hcomp hsplit' rfl hyl hex'
          | buildActive _ _ _ hα2 _ _ => exact absurd hα2.symm buildActive_feats_ne_singleton
        | var i j =>
          cases i <;> simp [atomToFeat] at hα
  | @merge3 s t x f γ δ' b1 b2 ms1 ms2 h1 h2 hsmc3 ih1 ih2 =>
    exact binMCFGToMG_merge3 ih1 ih2
  | @move1 s t f γ ms1 ms2 h1 ih1 =>
    cases ih1 with
    | @startMid w _ hlang hex =>
      have ⟨_, ht_eq, hrem⟩ := exactMap_remove hex
      have hnil : ms1 ++ ms2 = [] := by
        apply exactMap_empty_eq_nil hrem
        intro m ⟨hm, hne⟩; exact hne hm
      rw [ht_eq, hnil]
      simpa using MGInv.startDone hlang
    | @buildActive rid k r comp revPref suf args _ _ hrid hcomp hsplit hα hyl hex =>
      have hr_mem : r ∈ G.rules := List.mem_of_getElem? hrid
      have hwf := G.rules_wf r hr_mem
      have hcomp_mem : comp ∈ r.yield := List.mem_of_getElem? hcomp
      cases revPref with
      | nil => simp at hα
      | cons atom rest =>
        cases atom with
        | tm _ => simp [atomToFeat] at hα
        | var i j =>
          have hsplit' : comp = rest.reverse ++ (MCFGAtom.var i j :: suf) := by
            simpa [List.reverse_cons, List.append_assoc] using hsplit
          have hv_in : (i, j) ∈ r.varOccurrences := by
            simp only [MCFGRule.varOccurrences, List.mem_flatMap, List.mem_filterMap]
            refine ⟨comp, hcomp_mem, MCFGAtom.var i j, ?_, rfl⟩
            rw [hsplit']; exact List.mem_append_right _ (List.mem_cons_self ..)
          rcases var_index_lt_two hwf (hrank r hr_mem) hv_in with rfl | rfl
          · -- i = 0
            simp only [List.map_cons, atomToFeat, List.cons_append, List.cons.injEq,
              MGFeature.licensor.injEq] at hα
            obtain ⟨rfl, rfl⟩ := hα
            have ⟨_, ht_eq, hrem⟩ := exactMap_remove hex
            have hex' : ExactMap (ms1 ++ ms2) (buildDom r k rest) (ruleVal r args) :=
              exactMap_ext hrem (buildDom_step_var0 hwf.2.1 hcomp hsplit) (fun _ _ => rfl)
            rw [ht_eq]
            exact MGInv.buildActive hrid hcomp hsplit' rfl hyl hex'
          · -- i = 1
            simp only [List.map_cons, atomToFeat, List.cons_append, List.cons.injEq,
              MGFeature.licensor.injEq] at hα
            obtain ⟨rfl, rfl⟩ := hα
            have ⟨_, ht_eq, hrem⟩ := exactMap_remove hex
            have hex' : ExactMap (ms1 ++ ms2) (buildDom r k rest) (ruleVal r args) :=
              exactMap_ext hrem (buildDom_step_var1 hwf.2.1 hcomp hsplit) (fun _ _ => rfl)
            rw [ht_eq]
            exact MGInv.buildActive hrid hcomp hsplit' rfl hyl hex'
    | @copyLiftMid rid k r side tup _ hrid hk hy hex =>
      have ⟨_, ht_eq, hrem⟩ := exactMap_remove hex
      rw [ht_eq]
      simpa using MGInv.copiedReady hrid hk hy hrem
  | @move2 s t f f' γ δ' ms1 ms2 h1 hsmcNew ih1 =>
    exact False.elim (singleMover_no_move2 ih1.singleMover)

theorem mcfg_of_binMCFGToMG_lang {G : MCFG N T}
    (hrank : ∀ r, r ∈ G.rules → r.rhs.length ≤ 2) {w : List T}
    (h : (binMCFGToMG G).Lang w) : G.Lang w := by
  obtain ⟨b, hder⟩ := h
  have hinv := binMCFGToMG_sound hrank hder
  cases hinv with
  | startDone hlang => exact hlang
  | buildActive _ _ _ hα _ _ => exact absurd hα.symm buildActive_feats_ne_singleton

/-- Weak equivalence for any rank-≤-2 Linear Non-Erasing MCFG. -/
theorem binMCFGToMG_lang {G : MCFG N T}
    (hrank : ∀ r, r ∈ G.rules → r.rhs.length ≤ 2) (w : List T) :
    (binMCFGToMG G).Lang w ↔ G.Lang w :=
  ⟨mcfg_of_binMCFGToMG_lang hrank, binMCFGToMG_lang_of_mcfg hrank⟩

/-! ### Part 6: General `MCFG → MG` Theorem (Arbitrary Rank; Michaelis 2001 / Harkema 2001) -/

/-- The Minimalist Grammar weakly equivalent to ANY finite Linear Non-Erasing MCFG `G`
    (of arbitrary rank `k`), obtained by binarizing `G` and compiling via the 3-bank compiler. -/
def mcfgToMG (G : MCFG N T) : MG (MGBase (BinMCFGNT N) T) MGLic T :=
  binMCFGToMG (BinMCFG.binarizeMCFG G)

/-- **Harkema (2001) / Michaelis (2001) — Direction 2 (`MCFG → MG`)**:
    Every finite Linear Non-Erasing MCFG (LCFRS) has a weakly equivalent Minimalist Grammar. -/
theorem mcfgToMG_lang (G : MCFG N T) (w : List T) :
    (mcfgToMG G).Lang w ↔ G.Lang w := by
  unfold mcfgToMG
  rw [binMCFGToMG_lang (BinMCFG.binarizeMCFG_rank_le_two G) w, BinMCFG.binarizeMCFG_lang G w]

end MCFGtoMG
end FormalLinguistics
