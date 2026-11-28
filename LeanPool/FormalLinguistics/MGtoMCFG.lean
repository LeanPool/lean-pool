/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.MCFG
public import LeanPool.FormalLinguistics.MG
public import LeanPool.FormalLinguistics.CNF

/-!
  Direction 1 of Michaelis (1998, 2001) & Harkema (2001):
  Every Minimalist Grammar (Stabler & Keenan 2003) has a weakly equivalent
  Linear Non-Erasing Multiple Context-Free Grammar (MCFG / LCFRS).

  Key idea (after Michaelis 1998, Sect. 4, who fixes an enumeration of the licensees
  and indexes the components of each nonterminal by it):
    1. By the sub-suffix property (`MG.Derives.feats_suffix`), every feature stack
       in any derivation lies in the finite list `allFeats G`.
    2. Let `L = allLics G` be the duplicate-free finite list of licensee features
       occurring in `G.lexicon`. By the Shortest Move Constraint (`SMC`), every
       active mover list `ms` maps canonically to an `L`-indexed slot vector
       `slotsOf L ms : List (Option (List (MGFeature Base Lic)))` and corresponding
       string tuple `strsOf L ms : List (List T)`.
    3. Every MG rule (`lex`, `merge1`, `merge2`, `merge3`, `move1`, `move2`)
       translates directly into linear, non-erasing MCFG rules over the finite
       universe of canonical feature profiles `allProfiles G`.
-/

@[expose] public section

namespace FormalLinguistics

/-- Nonterminals of the MCFG constructed from a Minimalist Grammar. -/
inductive MGMCFGNT (Base Lic : Type) where
  | start : MGMCFGNT Base Lic
  | prof : Bool → List (MGFeature Base Lic) →
      List (Option (List (MGFeature Base Lic))) → MGMCFGNT Base Lic
  deriving DecidableEq, Repr

namespace MGtoMCFG

variable {Base Lic T : Type}

/-! ### Part 1: Finite Feature-Suffix & Licensee-Feature Universes -/

/-- All suffixes of a list `l` (from `l` down to `[]`). -/
def listSuffixes {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: t => (a :: t) :: listSuffixes t

theorem mem_listSuffixes_iff {α : Type} {s l : List α} :
    s ∈ listSuffixes l ↔ MG.isSuffix s l := by
  induction l with
  | nil =>
    simp [listSuffixes, MG.isSuffix]
  | cons a t ih =>
    simp only [listSuffixes, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨p, hp⟩)
      · exact ⟨[], rfl⟩
      · exact ⟨a :: p, by simp [hp]⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => left; simpa using hp
      | cons b p' =>
        simp at hp
        right
        exact ⟨p', hp.2⟩

/-- Finite deduplicated list of all feature suffixes occurring in `G.lexicon`. -/
def allFeats [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T) :
    List (List (MGFeature Base Lic)) :=
  dedupList (G.lexicon.flatMap fun entry => listSuffixes entry.2)

theorem mem_allFeats_of_suffix [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {fs : List (MGFeature Base Lic)} {entry : List T × List (MGFeature Base Lic)}
    (he : entry ∈ G.lexicon) (hs : MG.isSuffix fs entry.2) :
    fs ∈ allFeats G := by
  rw [allFeats, mem_dedupList]
  exact List.mem_flatMap.mpr ⟨entry, he, mem_listSuffixes_iff.mpr hs⟩

/-- Finite deduplicated list of all licensee features `f` appearing in `G.lexicon`. -/
def allLics [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T) : List Lic :=
  dedupList ((allFeats G).filterMap fun
    | MGFeature.licensee f :: _ => some f
    | _ => none)

theorem nodup_allLics [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T) :
    (allLics G).Nodup :=
  nodup_dedupList _

theorem mem_allLics_of_suffix [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {f : Lic} {δ : List (MGFeature Base Lic)}
    {entry : List T × List (MGFeature Base Lic)}
    (he : entry ∈ G.lexicon) (hs : MG.isSuffix (MGFeature.licensee f :: δ) entry.2) :
    f ∈ allLics G := by
  rw [allLics, mem_dedupList, List.mem_filterMap]
  exact ⟨MGFeature.licensee f :: δ, mem_allFeats_of_suffix he hs, rfl⟩

/-- All feature suffixes in `G` starting with `MGFeature.licensee f`. -/
def licFeats [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T) (f : Lic) :
    List (List (MGFeature Base Lic)) :=
  (allFeats G).filter fun fs =>
    match fs with
    | MGFeature.licensee f' :: _ => decide (f' = f)
    | _ => false

theorem mem_licFeats_iff [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {f : Lic} {fs : List (MGFeature Base Lic)} :
    fs ∈ licFeats G f ↔ fs ∈ allFeats G ∧ ∃ δ, fs = MGFeature.licensee f :: δ := by
  simp only [licFeats, List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    cases fs with
    | nil => simp at h2
    | cons hd tl =>
      cases hd with
      | licensee f' =>
        simp at h2; subst h2; exact ⟨tl, rfl⟩
      | _ => simp at h2
  · rintro ⟨h1, δ, rfl⟩
    exact ⟨h1, by simp⟩

/-! ### Part 2: Canonical `L`-Indexed Mover Slot Representation -/

/-- Find the unique mover in `ms` whose leading feature is `licensee f`. -/
def findChain [DecidableEq Lic] (f : Lic) (ms : List (MGChain Base Lic T)) :
    Option (MGChain Base Lic T) :=
  ms.find? fun c => decide (c.headLic = some f)

/-- Canonical `L`-indexed feature-slot list for a mover list `ms`. -/
def slotsOf [DecidableEq Lic] (L : List Lic) (ms : List (MGChain Base Lic T)) :
    List (Option (List (MGFeature Base Lic))) :=
  L.map fun f => (findChain f ms).map MGChain.feats

/-- Canonical `L`-indexed string tuple for a mover list `ms`. -/
def strsOf [DecidableEq Lic] (L : List Lic) (ms : List (MGChain Base Lic T)) :
    List (List T) :=
  L.filterMap fun f => (findChain f ms).map MGChain.str

/-- Dimension of an `MGMCFGNT`: `1` for `start`, `1 + activeSlots` for a profile. -/
def ntDim : MGMCFGNT Base Lic → Nat
  | MGMCFGNT.start => 1
  | MGMCFGNT.prof _ _ slots => 1 + slots.countP Option.isSome

theorem ntDim_pos (A : MGMCFGNT Base Lic) : 1 ≤ ntDim A := by
  cases A <;> simp [ntDim]

theorem slotsOf_length [DecidableEq Lic] (L : List Lic) (ms : List (MGChain Base Lic T)) :
    (slotsOf L ms).length = L.length := by
  simp [slotsOf]

theorem slotsOf_cons [DecidableEq Lic] (f : Lic) (t : List Lic) (ms : List (MGChain Base Lic T)) :
    slotsOf (f :: t) ms = (findChain f ms).map MGChain.feats :: slotsOf t ms := rfl

theorem strsOf_cons_none [DecidableEq Lic] {f : Lic} {t : List Lic} {ms : List (MGChain Base Lic T)}
    (h : findChain f ms = none) :
    strsOf (f :: t) ms = strsOf t ms := by
  simp [strsOf, h]

theorem strsOf_cons_some [DecidableEq Lic] {f : Lic} {t : List Lic} {ms : List (MGChain Base Lic T)}
    {c : MGChain Base Lic T} (h : findChain f ms = some c) :
    strsOf (f :: t) ms = c.str :: strsOf t ms := by
  simp [strsOf, h]

theorem strsOf_length [DecidableEq Lic] (L : List Lic) (ms : List (MGChain Base Lic T)) :
    (strsOf L ms).length = (slotsOf L ms).countP Option.isSome := by
  induction L with
  | nil => simp [strsOf, slotsOf]
  | cons f t ih =>
    cases h : findChain f ms with
    | none => rw [strsOf_cons_none h, slotsOf_cons, h]; simpa using ih
    | some c => rw [strsOf_cons_some h, slotsOf_cons, h]; simp [ih]

/-- Under `SMC ms`, there is at most one chain in `ms` with leading licensee `f`. -/
theorem smc_unique_chain {ms : List (MGChain Base Lic T)} (hsmc : SMC ms)
    {c1 c2 : MGChain Base Lic T} {f : Lic}
    (h1 : c1 ∈ ms) (hf1 : c1.headLic = some f)
    (h2 : c2 ∈ ms) (hf2 : c2.headLic = some f) : c1 = c2 := by
  induction ms with
  | nil => simp at h1
  | cons a t ih =>
    obtain ⟨hall, hnd⟩ := hsmc
    have hsmct : SMC t := by
      refine ⟨fun x hx => hall x (List.mem_cons_of_mem a hx), ?_⟩
      simp only [List.filterMap_cons] at hnd
      cases ha : a.headLic with
      | none => simpa [ha] using hnd
      | some fa => rw [ha] at hnd; exact (List.nodup_cons.mp hnd).2
    rcases List.mem_cons.mp h1 with rfl | ht1
    · rcases List.mem_cons.mp h2 with rfl | ht2
      · rfl
      · simp only [List.filterMap_cons, hf1, List.nodup_cons] at hnd
        have hf_in : f ∈ t.filterMap MGChain.headLic :=
          List.mem_filterMap.mpr ⟨c2, ht2, hf2⟩
        exact absurd hf_in hnd.1
    · rcases List.mem_cons.mp h2 with rfl | ht2
      · simp only [List.filterMap_cons, hf2, List.nodup_cons] at hnd
        have hf_in : f ∈ t.filterMap MGChain.headLic :=
          List.mem_filterMap.mpr ⟨c1, ht1, hf1⟩
        exact absurd hf_in hnd.1
      · exact ih hsmct ht1 ht2

/-- Under `SMC ms`, `findChain f ms = some c` iff `c ∈ ms` and `c.headLic = some f`. -/
theorem findChain_eq_some_iff [DecidableEq Lic] {ms : List (MGChain Base Lic T)} (hsmc : SMC ms)
    {f : Lic} {c : MGChain Base Lic T} :
    findChain f ms = some c ↔ c ∈ ms ∧ c.headLic = some f := by
  constructor
  · intro h
    have h1 := List.mem_of_find?_eq_some h
    have h2 := List.find?_some h
    simp only [decide_eq_true_eq] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨hc, hf⟩
    cases hfind : findChain f ms with
    | none =>
      have hnot := List.find?_eq_none.mp hfind c hc
      simp [hf] at hnot
    | some c' =>
      have hc' := List.mem_of_find?_eq_some hfind
      have hf' := List.find?_some hfind
      simp only [decide_eq_true_eq] at hf'
      have heq := smc_unique_chain hsmc hc' hf' hc hf
      subst heq; rfl

theorem findChain_eq_none_iff [DecidableEq Lic] {ms : List (MGChain Base Lic T)} {f : Lic} :
    findChain f ms = none ↔ ∀ c, c ∈ ms → c.headLic ≠ some f := by
  simp [findChain, List.find?_eq_none]

theorem findChain_nil [DecidableEq Lic] (f : Lic) :
    findChain f ([] : List (MGChain Base Lic T)) = none := rfl

theorem slotsOf_nil [DecidableEq Lic] (L : List Lic) :
    slotsOf (Base := Base) (T := T) L [] = L.map (fun _ => none) := by
  simp [slotsOf, findChain_nil]

theorem strsOf_nil [DecidableEq Lic] (L : List Lic) :
    strsOf (Base := Base) (T := T) L [] = [] := by
  induction L with
  | nil => rfl
  | cons f t _ => simp [strsOf, findChain_nil]

/-- If every chain in `ms` has its leading licensee in `L`, and `slotsOf L ms` is all `none`,
    then `ms = []`. -/
theorem movers_nil_of_slotsOf_all_none [DecidableEq Lic] {L : List Lic}
    {ms : List (MGChain Base Lic T)}
    (hsmc : SMC ms)
    (hL : ∀ c, c ∈ ms → ∀ f, c.headLic = some f → f ∈ L)
    (hall : slotsOf L ms = L.map (fun _ => none)) : ms = [] := by
  cases ms with
  | nil => rfl
  | cons c t =>
    obtain ⟨f, δ, hfeats⟩ := hsmc.1 c (List.mem_cons_self ..)
    have hlic : c.headLic = some f := by simp [MGChain.headLic, hfeats]
    have hfL : f ∈ L := hL c (List.mem_cons_self ..) f hlic
    have hfind : findChain f (c :: t) = some c :=
      (findChain_eq_some_iff hsmc).mpr ⟨List.mem_cons_self .., hlic⟩
    have hmem_some : some c.feats ∈ slotsOf L (c :: t) := by
      simp only [slotsOf, List.mem_map]
      exact ⟨f, hfL, by simp [hfind]⟩
    rw [hall] at hmem_some
    simp at hmem_some

/-! ### Part 3: Slot Combinators & Linear Non-Erasing Variable Generators -/

/-- Pointwise disjoint merge of two slot lists (returns `none` on SMC collision or length mismatch). -/
def mergeSlots {α : Type} : List (Option α) → List (Option α) → Option (List (Option α))
  | [], [] => some []
  | none :: t1, o2 :: t2 => (mergeSlots t1 t2).map (o2 :: ·)
  | some a :: t1, none :: t2 => (mergeSlots t1 t2).map (some a :: ·)
  | some _ :: _, some _ :: _ => none
  | _, _ => none

/-- Linear variable components produced by merging two slot lists, starting at component
    indices `c1` (for RHS 0) and `c2` (for RHS 1). -/
def mergeVars {α : Type} (c1 c2 : Nat) :
    List (Option α) → List (Option α) → List (List (MCFGAtom T))
  | none :: t1, none :: t2 => mergeVars c1 c2 t1 t2
  | some _ :: t1, none :: t2 => [MCFGAtom.var 0 c1] :: mergeVars (c1 + 1) c2 t1 t2
  | none :: t1, some _ :: t2 => [MCFGAtom.var 1 c2] :: mergeVars c1 (c2 + 1) t1 t2
  | _, _ => []

/-- Collect variable coordinates occurring in a list of component templates. -/
def compsVars (cs : List (List (MCFGAtom T))) : List (Nat × Nat) :=
  cs.flatMap fun comp =>
    comp.filterMap fun
      | MCFGAtom.tm _ => none
      | MCFGAtom.var i j => some (i, j)

theorem compsVars_nil : compsVars (T := T) [] = [] := rfl

theorem compsVars_cons_var (i j : Nat) (cs : List (List (MCFGAtom T))) :
    compsVars ([MCFGAtom.var i j] :: cs) = (i, j) :: compsVars cs := rfl

theorem mergeSlots_countP {α : Type} {s1 s2 s : List (Option α)}
    (h : mergeSlots s1 s2 = some s) :
    s.countP Option.isSome = s1.countP Option.isSome + s2.countP Option.isSome := by
  induction s1 generalizing s2 s with
  | nil =>
    cases s2 with
    | nil => simp [mergeSlots] at h; subst h; rfl
    | cons _ _ => simp [mergeSlots] at h
  | cons o1 t1 ih =>
    cases s2 with
    | nil => cases o1 <;> simp [mergeSlots] at h
    | cons o2 t2 =>
      cases o1 with
      | none =>
        simp only [mergeSlots, Option.map_eq_some_iff] at h
        obtain ⟨s', hs', rfl⟩ := h
        have ih' := ih hs'
        cases o2 <;> simp [ih'] <;> omega
      | some a =>
        cases o2 with
        | none =>
          simp only [mergeSlots, Option.map_eq_some_iff] at h
          obtain ⟨s', hs', rfl⟩ := h
          have ih' := ih hs'
          simp [ih']; omega
        | some b => simp [mergeSlots] at h

theorem mergeVars_props {α : Type} {s1 s2 s : List (Option α)}
    (h : mergeSlots s1 s2 = some s) :
    ∀ c1 c2,
      (mergeVars (T := T) c1 c2 s1 s2).length = s.countP Option.isSome ∧
      (compsVars (mergeVars (T := T) c1 c2 s1 s2)).Nodup ∧
      (∀ i j, (i, j) ∈ compsVars (mergeVars (T := T) c1 c2 s1 s2) ↔
        (i = 0 ∧ c1 ≤ j ∧ j < c1 + s1.countP Option.isSome) ∨
        (i = 1 ∧ c2 ≤ j ∧ j < c2 + s2.countP Option.isSome)) := by
  induction s1 generalizing s2 s with
  | nil =>
    cases s2 with
    | nil =>
      simp [mergeSlots] at h; subst h
      intro c1 c2
      refine ⟨rfl, List.nodup_nil, ?_⟩
      intro i j; simp [mergeVars, compsVars_nil]
    | cons _ _ => simp [mergeSlots] at h
  | cons o1 t1 ih =>
    cases s2 with
    | nil => cases o1 <;> simp [mergeSlots] at h
    | cons o2 t2 =>
      cases o1 with
      | none =>
        simp only [mergeSlots, Option.map_eq_some_iff] at h
        obtain ⟨s', hs', rfl⟩ := h
        intro c1 c2
        cases o2 with
        | none =>
          obtain ⟨hlen, hnd, hmem⟩ := ih hs' c1 c2
          refine ⟨by simpa [mergeVars] using hlen, by simpa [mergeVars] using hnd, ?_⟩
          intro i j; simpa [mergeVars] using hmem i j
        | some b =>
          obtain ⟨hlen, hnd, hmem⟩ := ih hs' c1 (c2 + 1)
          refine ⟨?_, ?_, ?_⟩
          · simp [mergeVars, hlen]
          · simp only [mergeVars]
            rw [compsVars_cons_var, List.nodup_cons]
            refine ⟨?_, hnd⟩
            intro hbad
            have := (hmem 1 c2).mp hbad
            omega
          · intro i j
            simp only [mergeVars]
            rw [compsVars_cons_var, List.mem_cons, Prod.mk.injEq, hmem i j]
            simp only [List.countP_cons, Option.isSome_none, Option.isSome_some,
              Bool.false_eq_true, ↓reduceIte]
            constructor
            · rintro (⟨rfl, rfl⟩ | h0 | h1)
              · right; refine ⟨rfl, Nat.le_refl _, ?_⟩; omega
              · left; omega
              · right; omega
            · rintro (⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩)
              · right; left; omega
              · by_cases hj : j = c2
                · left; exact ⟨rfl, hj⟩
                · right; right; omega
      | some a =>
        cases o2 with
        | some b => simp [mergeSlots] at h
        | none =>
          simp only [mergeSlots, Option.map_eq_some_iff] at h
          obtain ⟨s', hs', rfl⟩ := h
          intro c1 c2
          obtain ⟨hlen, hnd, hmem⟩ := ih hs' (c1 + 1) c2
          refine ⟨?_, ?_, ?_⟩
          · simp [mergeVars, hlen]
          · simp only [mergeVars]
            rw [compsVars_cons_var, List.nodup_cons]
            refine ⟨?_, hnd⟩
            intro hbad
            have := (hmem 0 c1).mp hbad
            omega
          · intro i j
            simp only [mergeVars]
            rw [compsVars_cons_var, List.mem_cons, Prod.mk.injEq, hmem i j]
            simp only [List.countP_cons, Option.isSome_none, Option.isSome_some,
              Bool.false_eq_true, ↓reduceIte]
            constructor
            · rintro (⟨rfl, rfl⟩ | h0 | h1)
              · left; refine ⟨rfl, Nat.le_refl _, ?_⟩; omega
              · left; omega
              · right; omega
            · rintro (⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩)
              · by_cases hj : j = c1
                · left; exact ⟨rfl, hj⟩
                · right; left; omega
              · right; right; omega

/-- Evaluate `mergeVars` on string lists `args = [p1 ++ strs1, p2 ++ strs2]` with prefix lengths `c1, c2`. -/
theorem evalYield_mergeVars [DecidableEq Lic]
    (L : List Lic) {ms1 ms2 : List (MGChain Base Lic T)}
    (hsmc1 : SMC ms1) (hsmc2 : SMC ms2) (hsmc12 : SMC (ms1 ++ ms2)) :
    mergeSlots (slotsOf L ms1) (slotsOf L ms2) = some (slotsOf L (ms1 ++ ms2)) ∧
    ∀ (p1 p2 : List (List T)),
      MCFG.evalYield [p1 ++ strsOf L ms1, p2 ++ strsOf L ms2]
        (mergeVars p1.length p2.length (slotsOf L ms1) (slotsOf L ms2)) =
      strsOf L (ms1 ++ ms2) := by
  induction L with
  | nil =>
    exact ⟨rfl, fun _ _ => rfl⟩
  | cons f t ih =>
    obtain ⟨hms, heval⟩ := ih
    have hcase :
        (findChain f ms1 = none ∧ findChain f ms2 = none ∧ findChain f (ms1 ++ ms2) = none) ∨
        (∃ c, findChain f ms1 = some c ∧ findChain f ms2 = none ∧ findChain f (ms1 ++ ms2) = some c) ∨
        (∃ c, findChain f ms1 = none ∧ findChain f ms2 = some c ∧ findChain f (ms1 ++ ms2) = some c) := by
      cases h1 : findChain f ms1 with
      | none =>
        cases h2 : findChain f ms2 with
        | none =>
          left
          refine ⟨rfl, rfl, ?_⟩
          rw [findChain_eq_none_iff] at h1 h2 ⊢
          intro c hc
          rcases List.mem_append.mp hc with hm1 | hm2
          · exact h1 c hm1
          · exact h2 c hm2
        | some c =>
          right; right
          obtain ⟨hc2, hf2⟩ := (findChain_eq_some_iff hsmc2).mp h2
          exact ⟨c, rfl, rfl, (findChain_eq_some_iff hsmc12).mpr ⟨List.mem_append_right _ hc2, hf2⟩⟩
      | some c =>
        cases h2 : findChain f ms2 with
        | none =>
          right; left
          obtain ⟨hc1, hf1⟩ := (findChain_eq_some_iff hsmc1).mp h1
          exact ⟨c, rfl, rfl, (findChain_eq_some_iff hsmc12).mpr ⟨List.mem_append_left _ hc1, hf1⟩⟩
        | some c2 =>
          -- Impossible by SMC (ms1 ++ ms2)!
          obtain ⟨hc1, hf1⟩ := (findChain_eq_some_iff hsmc1).mp h1
          obtain ⟨hc2, hf2⟩ := (findChain_eq_some_iff hsmc2).mp h2
          have hnd := hsmc12.2
          rw [List.filterMap_append, List.nodup_append] at hnd
          have hm1 : f ∈ ms1.filterMap MGChain.headLic := List.mem_filterMap.mpr ⟨c, hc1, hf1⟩
          have hm2 : f ∈ ms2.filterMap MGChain.headLic := List.mem_filterMap.mpr ⟨c2, hc2, hf2⟩
          exact absurd rfl (hnd.2.2 f hm1 f hm2)
    rcases hcase with ⟨h1, h2, h12⟩ | ⟨c, h1, h2, h12⟩ | ⟨c, h1, h2, h12⟩
    · refine ⟨?_, fun p1 p2 => ?_⟩
      · rw [slotsOf_cons, slotsOf_cons, slotsOf_cons, h1, h2, h12]; simp [mergeSlots, hms]
      · rw [slotsOf_cons, slotsOf_cons, h1, h2, strsOf_cons_none h1, strsOf_cons_none h2,
          strsOf_cons_none h12]
        simpa [mergeVars] using heval p1 p2
    · refine ⟨?_, fun p1 p2 => ?_⟩
      · rw [slotsOf_cons, slotsOf_cons, slotsOf_cons, h1, h2, h12]; simp [mergeSlots, hms]
      · rw [slotsOf_cons, slotsOf_cons, h1, h2, strsOf_cons_some h1, strsOf_cons_none h2,
          strsOf_cons_some h12]
        simp only [Option.map_some, Option.map_none, mergeVars, MCFG.evalYield, List.map_cons]
        have hhead : MCFG.evalComp [p1 ++ c.str :: strsOf t ms1, p2 ++ strsOf t ms2]
            [MCFGAtom.var 0 p1.length] = c.str := by
          simp [MCFG.evalComp]
        have htail := heval (p1 ++ [c.str]) p2
        simp only [List.length_append, List.length_singleton, List.append_assoc,
          List.singleton_append] at htail
        rw [hhead]
        exact congrArg (c.str :: ·) htail
    · refine ⟨?_, fun p1 p2 => ?_⟩
      · rw [slotsOf_cons, slotsOf_cons, slotsOf_cons, h1, h2, h12]; simp [mergeSlots, hms]
      · rw [slotsOf_cons, slotsOf_cons, h1, h2, strsOf_cons_none h1, strsOf_cons_some h2,
          strsOf_cons_some h12]
        simp only [Option.map_some, Option.map_none, mergeVars, MCFG.evalYield, List.map_cons]
        have hhead : MCFG.evalComp [p1 ++ strsOf t ms1, p2 ++ c.str :: strsOf t ms2]
            [MCFGAtom.var 1 p2.length] = c.str := by
          simp [MCFG.evalComp]
        have htail := heval p1 (p2 ++ [c.str])
        simp only [List.length_append, List.length_singleton, List.append_assoc,
          List.singleton_append] at htail
        rw [hhead]
        exact congrArg (c.str :: ·) htail

/-- Converse of `mergeSlots`: if `mergeSlots (slotsOf L ms1) (slotsOf L ms2) = some s`,
    and all mover heads of `ms1, ms2` lie in `L`, then `SMC (ms1 ++ ms2)`. -/
theorem smc_append_of_mergeSlots [DecidableEq Lic] {L : List Lic}
    {ms1 ms2 : List (MGChain Base Lic T)} {s : List (Option (List (MGFeature Base Lic)))}
    (hsmc1 : SMC ms1) (hsmc2 : SMC ms2)
    (hL1 : ∀ c, c ∈ ms1 → ∀ f, c.headLic = some f → f ∈ L)
    (hm : mergeSlots (slotsOf L ms1) (slotsOf L ms2) = some s) :
    SMC (ms1 ++ ms2) := by
  refine ⟨?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with h1 | h2
    · exact hsmc1.1 c h1
    · exact hsmc2.1 c h2
  · rw [List.filterMap_append, List.nodup_append]
    refine ⟨hsmc1.2, hsmc2.2, ?_⟩
    intro f1 hf1 f2 hf2 heq
    subst heq
    obtain ⟨c1, hc1, hlic1⟩ := List.mem_filterMap.mp hf1
    obtain ⟨c2, hc2, hlic2⟩ := List.mem_filterMap.mp hf2
    have hfL : f1 ∈ L := hL1 c1 hc1 f1 hlic1
    have hfind1 := (findChain_eq_some_iff hsmc1).mpr ⟨hc1, hlic1⟩
    have hfind2 := (findChain_eq_some_iff hsmc2).mpr ⟨hc2, hlic2⟩
    clear hL1
    induction L generalizing s with
    | nil => simp at hfL
    | cons g t ih =>
      rcases List.mem_cons.mp hfL with rfl | ht
      · rw [slotsOf_cons, slotsOf_cons, hfind1, hfind2] at hm
        simp [mergeSlots] at hm
      · rw [slotsOf_cons, slotsOf_cons] at hm
        cases hfg1 : findChain g ms1 <;> cases hfg2 : findChain g ms2
        · simp [hfg1, hfg2, mergeSlots] at hm
          obtain ⟨s', hs', _⟩ := hm
          exact ih hs' ht
        · simp [hfg1, hfg2, mergeSlots] at hm
          obtain ⟨s', hs', _⟩ := hm
          exact ih hs' ht
        · simp [hfg1, hfg2, mergeSlots] at hm
          obtain ⟨s', hs', _⟩ := hm
          exact ih hs' ht
        · simp [hfg1, hfg2, mergeSlots] at hm

/-- Insert a new mover `(f, δ)` into an `L`-indexed slot list (fails if `f ∉ L` or slot already occupied). -/
def insertSlot [DecidableEq Lic] (f : Lic) (δ : List (MGFeature Base Lic)) :
    List Lic → List (Option (List (MGFeature Base Lic))) →
    Option (List (Option (List (MGFeature Base Lic))))
  | [], [] => none
  | g :: t, o :: os =>
    if g = f then
      match o with
      | none => some (some δ :: os)
      | some _ => none
    else
      (insertSlot f δ t os).map (o :: ·)
  | _, _ => none

/-- Linear variable components for `Merge3`: inserts `[var 1 0]` at slot `f` and shifts
    the merged components `mergeVars` around it. -/
def merge3Vars [DecidableEq Lic] (f : Lic) (c1 c2 : Nat) :
    List Lic → List (Option (List (MGFeature Base Lic))) →
    List (Option (List (MGFeature Base Lic))) → List (List (MCFGAtom T))
  | g :: t, none :: t1, none :: t2 =>
    if g = f then
      [MCFGAtom.var 1 0] :: mergeVars c1 c2 t1 t2
    else
      merge3Vars f c1 c2 t t1 t2
  | g :: t, some _ :: t1, none :: t2 =>
    if g = f then []
    else [MCFGAtom.var 0 c1] :: merge3Vars f (c1 + 1) c2 t t1 t2
  | g :: t, none :: t1, some _ :: t2 =>
    if g = f then []
    else [MCFGAtom.var 1 c2] :: merge3Vars f c1 (c2 + 1) t t1 t2
  | _, _, _ => []

theorem merge3Vars_props [DecidableEq Lic] {f : Lic} {δ : List (MGFeature Base Lic)}
    {L : List Lic} {s1 s2 s12 s : List (Option (List (MGFeature Base Lic)))}
    (hm : mergeSlots s1 s2 = some s12)
    (hi : insertSlot f δ L s12 = some s) :
    ∀ c1 c2, 1 ≤ c2 →
      (merge3Vars (T := T) f c1 c2 L s1 s2).length = s.countP Option.isSome ∧
      (compsVars (merge3Vars (T := T) f c1 c2 L s1 s2)).Nodup ∧
      (∀ i j, (i, j) ∈ compsVars (merge3Vars (T := T) f c1 c2 L s1 s2) ↔
        (i = 1 ∧ j = 0) ∨
        (i = 0 ∧ c1 ≤ j ∧ j < c1 + s1.countP Option.isSome) ∨
        (i = 1 ∧ c2 ≤ j ∧ j < c2 + s2.countP Option.isSome)) := by
  induction L generalizing s1 s2 s12 s with
  | nil =>
    cases s12 <;> simp [insertSlot] at hi
  | cons g t ih =>
    cases s1 with
    | nil =>
      cases s2 with
      | nil => simp [mergeSlots] at hm; subst hm; simp [insertSlot] at hi
      | cons _ _ => simp [mergeSlots] at hm
    | cons o1 t1 =>
      cases s2 with
      | nil => cases o1 <;> simp [mergeSlots] at hm
      | cons o2 t2 =>
        cases o1 with
        | none =>
          simp only [mergeSlots, Option.map_eq_some_iff] at hm
          obtain ⟨s12', hm', rfl⟩ := hm
          cases o2 with
          | none =>
            simp only [insertSlot] at hi
            by_cases hgf : g = f
            · subst hgf
              simp at hi; subst hi
              intro c1 c2 hc2
              obtain ⟨hlen, hnd, hmem⟩ := mergeVars_props (T := T) hm' c1 c2
              refine ⟨?_, ?_, ?_⟩
              · simp [merge3Vars, hlen]
              · simp only [merge3Vars, ↓reduceIte]
                rw [compsVars_cons_var, List.nodup_cons]
                refine ⟨?_, hnd⟩
                intro hbad
                have := (hmem 1 0).mp hbad
                omega
              · intro i j
                simp only [merge3Vars, ↓reduceIte]
                rw [compsVars_cons_var, List.mem_cons, Prod.mk.injEq, hmem i j]
                simp only [List.countP_cons, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
                rfl
            · simp only [hgf, ↓reduceIte, Option.map_eq_some_iff] at hi
              obtain ⟨s', hi', rfl⟩ := hi
              intro c1 c2 hc2
              obtain ⟨hlen, hnd, hmem⟩ := ih hm' hi' c1 c2 hc2
              refine ⟨by simpa [merge3Vars, hgf] using hlen, by simpa [merge3Vars, hgf] using hnd, ?_⟩
              intro i j; simpa [merge3Vars, hgf] using hmem i j
          | some b =>
            simp only [insertSlot] at hi
            by_cases hgf : g = f
            · simp [hgf] at hi
            · simp only [hgf, ↓reduceIte, Option.map_eq_some_iff] at hi
              obtain ⟨s', hi', rfl⟩ := hi
              intro c1 c2 hc2
              obtain ⟨hlen, hnd, hmem⟩ := ih hm' hi' c1 (c2 + 1) (by omega)
              refine ⟨?_, ?_, ?_⟩
              · simp [merge3Vars, hgf, hlen]
              · simp only [merge3Vars, hgf, ↓reduceIte]
                rw [compsVars_cons_var, List.nodup_cons]
                refine ⟨?_, hnd⟩
                intro hbad
                have := (hmem 1 c2).mp hbad
                omega
              · intro i j
                simp only [merge3Vars, hgf, ↓reduceIte]
                rw [compsVars_cons_var, List.mem_cons, Prod.mk.injEq, hmem i j]
                simp only [List.countP_cons, Option.isSome_none, Option.isSome_some,
                  Bool.false_eq_true, ↓reduceIte]
                constructor
                · rintro (⟨rfl, rfl⟩ | h0 | h1 | h2)
                  · right; right; refine ⟨rfl, Nat.le_refl _, ?_⟩; omega
                  · left; exact h0
                  · right; left; exact h1
                  · right; right; omega
                · rintro (h0 | h1 | ⟨rfl, hlo, hhi⟩)
                  · right; left; exact h0
                  · right; right; left; exact h1
                  · by_cases hj : j = c2
                    · left; exact ⟨rfl, hj⟩
                    · right; right; right; omega
        | some a =>
          cases o2 with
          | some b => simp [mergeSlots] at hm
          | none =>
            simp only [mergeSlots, Option.map_eq_some_iff] at hm
            obtain ⟨s12', hm', rfl⟩ := hm
            simp only [insertSlot] at hi
            by_cases hgf : g = f
            · simp [hgf] at hi
            · simp only [hgf, ↓reduceIte, Option.map_eq_some_iff] at hi
              obtain ⟨s', hi', rfl⟩ := hi
              intro c1 c2 hc2
              obtain ⟨hlen, hnd, hmem⟩ := ih hm' hi' (c1 + 1) c2 hc2
              refine ⟨?_, ?_, ?_⟩
              · simp [merge3Vars, hgf, hlen]
              · simp only [merge3Vars, hgf, ↓reduceIte]
                rw [compsVars_cons_var, List.nodup_cons]
                refine ⟨?_, hnd⟩
                intro hbad
                have := (hmem 0 c1).mp hbad
                omega
              · intro i j
                simp only [merge3Vars, hgf, ↓reduceIte]
                rw [compsVars_cons_var, List.mem_cons, Prod.mk.injEq, hmem i j]
                simp only [List.countP_cons, Option.isSome_none, Option.isSome_some,
                  Bool.false_eq_true, ↓reduceIte]
                constructor
                · rintro (⟨rfl, rfl⟩ | h0 | h1 | h2)
                  · right; left; refine ⟨rfl, Nat.le_refl _, ?_⟩; omega
                  · left; exact h0
                  · right; left; omega
                  · right; right; exact h2
                · rintro (h0 | ⟨rfl, hlo, hhi⟩ | h2)
                  · right; left; exact h0
                  · by_cases hj : j = c1
                    · left; exact ⟨rfl, hj⟩
                    · right; right; left; omega
                  · right; right; right; exact h2

/-- Evaluation lemma for `Merge3`. -/
theorem evalYield_merge3Vars [DecidableEq Lic]
    (L : List Lic) (hLnd : L.Nodup) {f : Lic} (hfL : f ∈ L)
    {tStr : List T} {δ' : List (MGFeature Base Lic)}
    {ms1 ms2 : List (MGChain Base Lic T)}
    (hsmc1 : SMC ms1) (hsmc2 : SMC ms2)
    (hsmc3 : SMC (ms1 ++ ⟨tStr, MGFeature.licensee f :: δ'⟩ :: ms2)) :
    let δ := MGFeature.licensee f :: δ'
    let ms3 := ms1 ++ ⟨tStr, δ⟩ :: ms2
    insertSlot f δ L (slotsOf L (ms1 ++ ms2)) = some (slotsOf L ms3) ∧
    ∀ (p1 p2 : List (List T)), p2[0]? = some tStr →
      MCFG.evalYield [p1 ++ strsOf L ms1, p2 ++ strsOf L ms2]
        (merge3Vars f p1.length p2.length L (slotsOf L ms1) (slotsOf L ms2)) =
      strsOf L ms3 := by
  have hsmc12 : SMC (ms1 ++ ms2) := MG.smc_remove hsmc3
  induction L with
  | nil => simp at hfL
  | cons g t ih =>
    rw [List.nodup_cons] at hLnd
    obtain ⟨hg_not, ht_nd⟩ := hLnd
    let δ := MGFeature.licensee f :: δ'
    let newC : MGChain Base Lic T := ⟨tStr, δ⟩
    let ms3 := ms1 ++ newC :: ms2
    have hnew_lic : newC.headLic = some f := rfl
    have hnew_in : newC ∈ ms3 := List.mem_append_right _ (List.mem_cons_self ..)
    by_cases hgf : g = f
    · subst hgf
      have h1 : findChain g ms1 = none := by
        rw [findChain_eq_none_iff]
        intro c hc hlic
        have hnd := hsmc3.2
        simp only [List.filterMap_append, List.filterMap_cons, List.nodup_append] at hnd
        have hm1 : g ∈ ms1.filterMap MGChain.headLic := List.mem_filterMap.mpr ⟨c, hc, hlic⟩
        exact hnd.2.2 g hm1 g (List.mem_cons_self ..) rfl
      have h2 : findChain g ms2 = none := by
        rw [findChain_eq_none_iff]
        intro c hc hlic
        have hnd := hsmc3.2
        simp only [List.filterMap_append, List.filterMap_cons, List.nodup_append] at hnd
        have hm2 : g ∈ ms2.filterMap MGChain.headLic := List.mem_filterMap.mpr ⟨c, hc, hlic⟩
        exact (List.nodup_cons.mp hnd.2.1).1 hm2
      have h12 : findChain g (ms1 ++ ms2) = none := by
        rw [findChain_eq_none_iff]
        intro c hc
        rcases List.mem_append.mp hc with hm1 | hm2
        · exact (findChain_eq_none_iff.mp h1) c hm1
        · exact (findChain_eq_none_iff.mp h2) c hm2
      have h3 : findChain g ms3 = some newC :=
        (findChain_eq_some_iff hsmc3).mpr ⟨hnew_in, hnew_lic⟩
      -- For every g' ∈ t, g' ≠ g, so findChain g' ms3 = findChain g' (ms1 ++ ms2)
      have htail_find : ∀ g', g' ∈ t → findChain g' ms3 = findChain g' (ms1 ++ ms2) := by
        intro g' hg'
        have hne : g' ≠ g := fun heq => hg_not (heq ▸ hg')
        cases hf12 : findChain g' (ms1 ++ ms2) with
        | none =>
          rw [findChain_eq_none_iff] at hf12 ⊢
          intro c hc
          rcases List.mem_append.mp hc with hm1 | hm2
          · exact hf12 c (List.mem_append_left _ hm1)
          · rcases List.mem_cons.mp hm2 with rfl | hm2'
            · simp [hnew_lic, hne.symm]
            · exact hf12 c (List.mem_append_right _ hm2')
        | some c =>
          obtain ⟨hc12, hlic⟩ := (findChain_eq_some_iff hsmc12).mp hf12
          have hc3 : c ∈ ms3 := by
            rcases List.mem_append.mp hc12 with hm1 | hm2
            · exact List.mem_append_left _ hm1
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ hm2)
          exact (findChain_eq_some_iff hsmc3).mpr ⟨hc3, hlic⟩
      have hslots_tail : slotsOf t ms3 = slotsOf t (ms1 ++ ms2) := by
        apply List.map_congr_left
        intro g' hg'; rw [htail_find g' hg']
      have hstrs_tail : strsOf t ms3 = strsOf t (ms1 ++ ms2) := by
        simp only [strsOf]
        have : ∀ l : List Lic, (∀ g', g' ∈ l → findChain g' ms3 = findChain g' (ms1 ++ ms2)) →
            l.filterMap (fun x => (findChain x ms3).map MGChain.str) =
            l.filterMap (fun x => (findChain x (ms1 ++ ms2)).map MGChain.str) := by
          intro l hl
          induction l with
          | nil => rfl
          | cons a b ihb =>
            simp only [List.filterMap_cons, hl a (List.mem_cons_self ..)]
            cases (findChain a (ms1 ++ ms2)).map MGChain.str with
            | none => exact ihb (fun x hx => hl x (List.mem_cons_of_mem _ hx))
            | some s => exact congrArg (s :: ·) (ihb (fun x hx => hl x (List.mem_cons_of_mem _ hx)))
        exact this t htail_find
      have ⟨_, heval_mv⟩ := evalYield_mergeVars t hsmc1 hsmc2 hsmc12
      refine ⟨?_, fun p1 p2 hp2 => ?_⟩
      · rw [slotsOf_cons, slotsOf_cons, h12, h3, hslots_tail]
        simp [insertSlot, newC, δ]
      · rw [slotsOf_cons, slotsOf_cons, h1, h2, strsOf_cons_none h1, strsOf_cons_none h2,
          strsOf_cons_some h3]
        simp only [Option.map_none, merge3Vars, ↓reduceIte, MCFG.evalYield, List.map_cons]
        have hhead : MCFG.evalComp [p1 ++ strsOf t ms1, p2 ++ strsOf t ms2]
            [MCFGAtom.var 1 0] = tStr := by
          have hp2_len : 0 < p2.length := by
            cases p2 with
            | nil => simp at hp2
            | cons _ _ => simp
          simp only [MCFG.evalComp, List.getElem?_cons_succ, List.getElem?_cons_zero,
            List.getElem?_append_left hp2_len, hp2, List.append_nil]
        rw [hhead, hstrs_tail]
        exact congrArg (tStr :: ·) (heval_mv p1 p2)
    · have hf_in_t : f ∈ t := by
        rcases List.mem_cons.mp hfL with rfl | ht
        · exact absurd rfl hgf
        · exact ht
      obtain ⟨hins_t, heval_t⟩ := ih ht_nd hf_in_t
      have hg_same : findChain g ms3 = findChain g (ms1 ++ ms2) := by
        cases hf12 : findChain g (ms1 ++ ms2) with
        | none =>
          rw [findChain_eq_none_iff] at hf12 ⊢
          intro c hc
          rcases List.mem_append.mp hc with hm1 | hm2
          · exact hf12 c (List.mem_append_left _ hm1)
          · rcases List.mem_cons.mp hm2 with rfl | hm2'
            · simp [hnew_lic, Ne.symm hgf]
            · exact hf12 c (List.mem_append_right _ hm2')
        | some c =>
          obtain ⟨hc12, hlic⟩ := (findChain_eq_some_iff hsmc12).mp hf12
          have hc3 : c ∈ ms3 := by
            rcases List.mem_append.mp hc12 with hm1 | hm2
            · exact List.mem_append_left _ hm1
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ hm2)
          exact (findChain_eq_some_iff hsmc3).mpr ⟨hc3, hlic⟩
      have hcase :
          (findChain g ms1 = none ∧ findChain g ms2 = none ∧ findChain g (ms1 ++ ms2) = none) ∨
          (∃ c, findChain g ms1 = some c ∧ findChain g ms2 = none ∧ findChain g (ms1 ++ ms2) = some c) ∨
          (∃ c, findChain g ms1 = none ∧ findChain g ms2 = some c ∧ findChain g (ms1 ++ ms2) = some c) := by
        cases h1 : findChain g ms1 with
        | none =>
          cases h2 : findChain g ms2 with
          | none =>
            left; refine ⟨rfl, rfl, ?_⟩
            rw [findChain_eq_none_iff] at h1 h2 ⊢
            intro c hc; rcases List.mem_append.mp hc with hm1 | hm2
            · exact h1 c hm1
            · exact h2 c hm2
          | some c =>
            right; right
            obtain ⟨hc2, hf2⟩ := (findChain_eq_some_iff hsmc2).mp h2
            exact ⟨c, rfl, rfl, (findChain_eq_some_iff hsmc12).mpr ⟨List.mem_append_right _ hc2, hf2⟩⟩
        | some c =>
          cases h2 : findChain g ms2 with
          | none =>
            right; left
            obtain ⟨hc1, hf1⟩ := (findChain_eq_some_iff hsmc1).mp h1
            exact ⟨c, rfl, rfl, (findChain_eq_some_iff hsmc12).mpr ⟨List.mem_append_left _ hc1, hf1⟩⟩
          | some c2 =>
            obtain ⟨hc1, hf1⟩ := (findChain_eq_some_iff hsmc1).mp h1
            obtain ⟨hc2, hf2⟩ := (findChain_eq_some_iff hsmc2).mp h2
            have hnd := hsmc12.2
            rw [List.filterMap_append, List.nodup_append] at hnd
            exact absurd rfl (hnd.2.2 g (List.mem_filterMap.mpr ⟨c, hc1, hf1⟩) g
              (List.mem_filterMap.mpr ⟨c2, hc2, hf2⟩))
      rcases hcase with ⟨h1, h2, h12⟩ | ⟨c, h1, h2, h12⟩ | ⟨c, h1, h2, h12⟩
      · refine ⟨?_, fun p1 p2 hp2 => ?_⟩
        · rw [slotsOf_cons, slotsOf_cons, h12, hg_same, h12]; simp [insertSlot, hgf, hins_t]
        · rw [slotsOf_cons, slotsOf_cons, h1, h2, strsOf_cons_none h1, strsOf_cons_none h2,
            strsOf_cons_none (hg_same.trans h12)]
          simpa [merge3Vars, hgf] using heval_t p1 p2 hp2
      · refine ⟨?_, fun p1 p2 hp2 => ?_⟩
        · rw [slotsOf_cons, slotsOf_cons, h12, hg_same, h12]; simp [insertSlot, hgf, hins_t]
        · rw [slotsOf_cons, slotsOf_cons, h1, h2, strsOf_cons_some h1, strsOf_cons_none h2,
            strsOf_cons_some (hg_same.trans h12)]
          simp only [Option.map_some, Option.map_none, merge3Vars, hgf, ↓reduceIte, MCFG.evalYield,
            List.map_cons]
          have hhead : MCFG.evalComp [p1 ++ c.str :: strsOf t ms1, p2 ++ strsOf t ms2]
              [MCFGAtom.var 0 p1.length] = c.str := by simp [MCFG.evalComp]
          have htail := heval_t (p1 ++ [c.str]) p2 hp2
          simp only [List.length_append, List.length_singleton, List.append_assoc,
            List.singleton_append] at htail
          rw [hhead]
          exact congrArg (c.str :: ·) htail
      · refine ⟨?_, fun p1 p2 hp2 => ?_⟩
        · rw [slotsOf_cons, slotsOf_cons, h12, hg_same, h12]; simp [insertSlot, hgf, hins_t]
        · rw [slotsOf_cons, slotsOf_cons, h1, h2, strsOf_cons_none h1, strsOf_cons_some h2,
            strsOf_cons_some (hg_same.trans h12)]
          simp only [Option.map_some, Option.map_none, merge3Vars, hgf, ↓reduceIte, MCFG.evalYield,
            List.map_cons]
          have hhead : MCFG.evalComp [p1 ++ strsOf t ms1, p2 ++ c.str :: strsOf t ms2]
              [MCFGAtom.var 1 p2.length] = c.str := by simp [MCFG.evalComp]
          have hp2' : (p2 ++ [c.str])[0]? = some tStr := by
            cases p2 with
            | nil => simp at hp2
            | cons x xs => simpa using hp2
          have htail := heval_t p1 (p2 ++ [c.str]) hp2'
          simp only [List.length_append, List.length_singleton, List.append_assoc,
            List.singleton_append] at htail
          rw [hhead]
          exact congrArg (c.str :: ·) htail

/-- Converse of `insertSlot`: if `insertSlot f δ L (slotsOf L ms12) = some s`, then no chain in
    `ms12` has leading licensee `f`. -/
theorem not_mem_headLic_of_insertSlot [DecidableEq Lic] {f : Lic} {δ : List (MGFeature Base Lic)}
    {L : List Lic} {ms : List (MGChain Base Lic T)}
    {s : List (Option (List (MGFeature Base Lic)))}
    (_hsmc : SMC ms)
    (hi : insertSlot f δ L (slotsOf L ms) = some s) :
    ∀ c, c ∈ ms → c.headLic ≠ some f := by
  induction L generalizing s with
  | nil => simp [slotsOf, insertSlot] at hi
  | cons g t ih =>
    simp only [slotsOf, List.map_cons, insertSlot] at hi
    by_cases hgf : g = f
    · subst hgf
      simp only [↓reduceIte] at hi
      cases hfg : findChain g ms with
      | none => exact findChain_eq_none_iff.mp hfg
      | some _ => simp [hfg] at hi
    · simp only [hgf, ↓reduceIte, Option.map_eq_some_iff] at hi
      obtain ⟨s', hs', _⟩ := hi
      exact ih hs'

/-! ### Part 4: Move1 & Move2 Slot Operations -/

/-- Find the active component index (starting from `c`) and remaining slot list when clearing
    a final mover `[licensee f]` at slot `f`. -/
def clearSlot [DecidableEq Lic] (f : Lic) (c : Nat) :
    List Lic → List (Option (List (MGFeature Base Lic))) →
    Option (Nat × List (Option (List (MGFeature Base Lic))) × List (List (MCFGAtom T)))
  | [], [] => none
  | g :: t, o :: os =>
    if g = f then
      match o with
      | some [MGFeature.licensee f'] =>
        if f' = f then
          let restVars := (List.range (os.countP Option.isSome)).map fun k =>
            [MCFGAtom.var 0 (c + 1 + k)]
          some (c, none :: os, restVars)
        else none
      | _ => none
    else
      match o with
      | none =>
        (clearSlot f c t os).map fun (p, os', vs) => (p, none :: os', vs)
      | some fs =>
        (clearSlot f (c + 1) t os).map fun (p, os', vs) =>
          (p, some fs :: os', [MCFGAtom.var 0 c] :: vs)
  | _, _ => none

theorem range_vars_props (base len : Nat) :
    let vs : List (List (MCFGAtom T)) := (List.range len).map fun k => [MCFGAtom.var 0 (base + k)]
    vs.length = len ∧
    (compsVars vs).Nodup ∧
    (∀ i j, (i, j) ∈ compsVars vs ↔ i = 0 ∧ base ≤ j ∧ j < base + len) := by
  induction len generalizing base with
  | zero =>
    refine ⟨rfl, List.nodup_nil, ?_⟩
    intro i j; simp [compsVars]
  | succ len ih =>
    have hr : List.range (len + 1) = 0 :: (List.range len).map Nat.succ :=
      List.range_succ_eq_map (n := len)
    obtain ⟨hlen, hnd, hmem⟩ := ih (base + 1)
    have hmap : ((List.range (len + 1)).map fun k => [MCFGAtom.var (T := T) 0 (base + k)]) =
        [MCFGAtom.var 0 base] :: ((List.range len).map fun k => [MCFGAtom.var 0 (base + 1 + k)]) := by
      rw [hr, List.map_cons, List.map_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro k _
      have hidx : base + k.succ = base + 1 + k := by omega
      simp [Function.comp, hidx]
    simp only [hmap]
    refine ⟨?_, ?_, ?_⟩
    · simp [hlen]
    · rw [compsVars_cons_var, List.nodup_cons]
      refine ⟨?_, hnd⟩
      intro hbad
      have := (hmem 0 base).mp hbad
      omega
    · intro i j
      rw [compsVars_cons_var, List.mem_cons, Prod.mk.injEq, hmem i j]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, hlo, hhi⟩)
        · refine ⟨rfl, Nat.le_refl _, ?_⟩; omega
        · refine ⟨rfl, ?_, ?_⟩ <;> omega
      · rintro ⟨rfl, hlo, hhi⟩
        by_cases hj : j = base
        · left; exact ⟨rfl, hj⟩
        · right; refine ⟨rfl, ?_, ?_⟩ <;> omega

theorem clearSlot_props [DecidableEq Lic] {f : Lic}
    {L : List Lic} {s s' : List (Option (List (MGFeature Base Lic)))}
    {p : Nat} {vs : List (List (MCFGAtom T))} {c : Nat}
    (h : clearSlot f c L s = some (p, s', vs)) :
    c ≤ p ∧ p < c + s.countP Option.isSome ∧
    vs.length = s'.countP Option.isSome ∧
    (compsVars vs).Nodup ∧
    (∀ i j, (i, j) ∈ compsVars vs ↔
      i = 0 ∧ c ≤ j ∧ j < c + s.countP Option.isSome ∧ j ≠ p) := by
  induction L generalizing s s' p vs c with
  | nil => cases s <;> simp [clearSlot] at h
  | cons g t ih =>
    cases s with
    | nil => simp [clearSlot] at h
    | cons o os =>
      simp only [clearSlot] at h
      by_cases hgf : g = f
      · subst hgf
        simp only [↓reduceIte] at h
        cases o with
        | none => simp at h
        | some fs =>
          cases fs with
          | nil => simp at h
          | cons hd tl =>
            cases hd with
            | licensee f' =>
              cases tl with
              | cons _ _ => simp at h
              | nil =>
                by_cases hff' : f' = g
                · subst hff'
                  simp at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  obtain ⟨hlen, hnd, hmem⟩ := range_vars_props (T := T) (c + 1) (os.countP Option.isSome)
                  refine ⟨Nat.le_refl _, ?_, ?_, hnd, ?_⟩
                  · simp
                  · simp [hlen]
                  · intro i j
                    rw [hmem i j]
                    simp only [List.countP_cons, Option.isSome_some, ↓reduceIte]
                    omega
                · simp [hff'] at h
            | _ => simp at h
      · simp only [hgf, ↓reduceIte] at h
        cases o with
        | none =>
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨⟨p', os', vs'⟩, hrec, heq⟩ := h
          simp at heq; obtain ⟨rfl, rfl, rfl⟩ := heq
          obtain ⟨h1, h2, h3, h4, h5⟩ := ih hrec
          simpa using ⟨h1, h2, h3, h4, h5⟩
        | some fs =>
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨⟨p', os', vs'⟩, hrec, heq⟩ := h
          simp at heq; obtain ⟨rfl, rfl, rfl⟩ := heq
          obtain ⟨h1, h2, h3, h4, h5⟩ := ih hrec
          refine ⟨by omega, ?_, ?_, ?_, ?_⟩
          · simp; omega
          · simp [h3]
          · rw [compsVars_cons_var, List.nodup_cons]
            refine ⟨?_, h4⟩
            intro hbad
            have := (h5 0 c).mp hbad
            omega
          · intro i j
            rw [compsVars_cons_var, List.mem_cons, Prod.mk.injEq, h5 i j]
            simp only [List.countP_cons, Option.isSome_some, ↓reduceIte]
            constructor
            · rintro (⟨rfl, rfl⟩ | ⟨rfl, hlo, hhi, hne⟩)
              · refine ⟨rfl, Nat.le_refl _, ?_, ?_⟩ <;> omega
              · refine ⟨rfl, ?_, ?_, hne⟩ <;> omega
            · rintro ⟨rfl, hlo, hhi, hne⟩
              by_cases hj : j = c
              · left; exact ⟨rfl, hj⟩
              · right; refine ⟨rfl, ?_, ?_, hne⟩ <;> omega

theorem evalYield_range_vars (pre mid : List (List T)) :
    MCFG.evalYield [pre ++ mid]
      ((List.range mid.length).map fun k => [MCFGAtom.var 0 (pre.length + k)]) = mid := by
  induction mid generalizing pre with
  | nil => rfl
  | cons a t ih =>
    have hr : List.range (t.length + 1) = 0 :: (List.range t.length).map Nat.succ :=
      List.range_succ_eq_map (n := t.length)
    simp only [List.length_cons, hr, List.map_cons, List.map_map, MCFG.evalYield]
    have hhead : MCFG.evalComp [pre ++ a :: t] [MCFGAtom.var 0 (pre.length + 0)] = a := by
      simp [MCFG.evalComp]
    rw [hhead]
    congr 1
    have htail := ih (pre ++ [a])
    simp only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append, MCFG.evalYield, List.map_map] at htail
    refine Eq.trans ?_ htail
    apply List.map_congr_left
    intro k _
    have hidx : pre.length + k.succ = pre.length + 1 + k := by omega
    simp [Function.comp, hidx]

theorem evalYield_range_vars1 (u0 pre mid : List (List T)) :
    MCFG.evalYield [u0, pre ++ mid]
      ((List.range mid.length).map fun k => [MCFGAtom.var 1 (pre.length + k)]) = mid := by
  induction mid generalizing pre with
  | nil => rfl
  | cons a t ih =>
    have hr : List.range (t.length + 1) = 0 :: (List.range t.length).map Nat.succ :=
      List.range_succ_eq_map (n := t.length)
    simp only [List.length_cons, hr, List.map_cons, List.map_map, MCFG.evalYield]
    have hhead : MCFG.evalComp [u0, pre ++ a :: t] [MCFGAtom.var 1 (pre.length + 0)] = a := by
      simp [MCFG.evalComp]
    rw [hhead]
    congr 1
    have htail := ih (pre ++ [a])
    simp only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append, MCFG.evalYield, List.map_map] at htail
    refine Eq.trans ?_ htail
    apply List.map_congr_left
    intro k _
    have hidx : pre.length + k.succ = pre.length + 1 + k := by omega
    simp [Function.comp, hidx]

/-- Evaluation & soundness helper for `Move1` (`clearSlot`). -/
theorem clearSlot_eval_and_mem [DecidableEq Lic]
    (L : List Lic) (hLnd : L.Nodup) {f : Lic}
    {ms : List (MGChain Base Lic T)} (hsmc : SMC ms)
    {p : Nat} {s' : List (Option (List (MGFeature Base Lic)))} {vs : List (List (MCFGAtom T))} :
    ∀ (pre : List (List T)),
      clearSlot f pre.length L (slotsOf L ms) = some (p, s', vs) →
      ∃ tStr ms1 ms2,
        ms = ms1 ++ ⟨tStr, [MGFeature.licensee f]⟩ :: ms2 ∧
        slotsOf L (ms1 ++ ms2) = s' ∧
        (pre ++ strsOf L ms)[p]? = some tStr ∧
        MCFG.evalYield [pre ++ strsOf L ms] vs = strsOf L (ms1 ++ ms2) := by
  induction L generalizing p s' vs with
  | nil => intro pre h; simp [slotsOf, clearSlot] at h
  | cons g t ih =>
    rw [List.nodup_cons] at hLnd
    obtain ⟨hg_not, ht_nd⟩ := hLnd
    intro pre h
    rw [slotsOf_cons] at h
    simp only [clearSlot] at h
    by_cases hgf : g = f
    · subst hgf
      simp only [↓reduceIte] at h
      cases hfg : findChain g ms with
      | none => simp [hfg] at h
      | some c =>
        rw [hfg] at h
        simp only [Option.map_some] at h
        cases hcf : c.feats with
        | nil => simp [hcf] at h
        | cons hd tl =>
          cases hd with
          | licensee f' =>
            cases tl with
            | cons _ _ => simp [hcf] at h
            | nil =>
              by_cases hff' : f' = g
              · subst f'
                simp [hcf] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                obtain ⟨hc_in, hlic⟩ := (findChain_eq_some_iff hsmc).mp hfg
                obtain ⟨ms1, ms2, hms_eq⟩ := List.append_of_mem hc_in
                have hce : c = ⟨c.str, [MGFeature.licensee g]⟩ := by
                  cases c; simp at hcf; subst hcf; rfl
                have hms_eq' : ms = ms1 ++ ⟨c.str, [MGFeature.licensee g]⟩ :: ms2 := by
                  rw [← hce]; exact hms_eq
                have hsmc' : SMC (ms1 ++ ms2) := MG.smc_remove (hms_eq ▸ hsmc)
                have htail_find : ∀ x, x ∈ t → findChain x (ms1 ++ ms2) = findChain x ms := by
                  intro x hx
                  have hne : x ≠ g := fun heq => hg_not (heq ▸ hx)
                  cases hfx : findChain x ms with
                  | none =>
                    rw [findChain_eq_none_iff] at hfx ⊢
                    intro y hy
                    apply hfx y
                    rw [hms_eq]
                    rcases List.mem_append.mp hy with h1 | h2
                    · exact List.mem_append_left _ h1
                    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
                  | some y =>
                    obtain ⟨hy_in, hy_lic⟩ := (findChain_eq_some_iff hsmc).mp hfx
                    have hy_ne : y ≠ c := fun heq => by subst heq; rw [hlic] at hy_lic; simp at hy_lic; exact hne hy_lic.symm
                    have hy_in' : y ∈ ms1 ++ ms2 := by
                      rw [hms_eq] at hy_in
                      rcases List.mem_append.mp hy_in with h1 | h2
                      · exact List.mem_append_left _ h1
                      · rcases List.mem_cons.mp h2 with rfl | h2'
                        · exact absurd rfl hy_ne
                        · exact List.mem_append_right _ h2'
                    exact (findChain_eq_some_iff hsmc').mpr ⟨hy_in', hy_lic⟩
                have hfg' : findChain g (ms1 ++ ms2) = none := by
                  rw [findChain_eq_none_iff]
                  intro y hy hy_lic
                  have hy_in : y ∈ ms := by
                    rw [hms_eq]
                    rcases List.mem_append.mp hy with h1 | h2
                    · exact List.mem_append_left _ h1
                    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
                  have hy_eq := smc_unique_chain hsmc hy_in hy_lic hc_in hlic
                  subst hy_eq
                  have hnd := hsmc.2
                  rw [hms_eq] at hnd
                  simp only [List.filterMap_append, List.filterMap_cons, hlic, List.nodup_append] at hnd
                  rcases List.mem_append.mp hy with h1 | h2
                  · exact hnd.2.2 g (List.mem_filterMap.mpr ⟨y, h1, hlic⟩) g (List.mem_cons_self ..) rfl
                  · exact (List.nodup_cons.mp hnd.2.1).1 (List.mem_filterMap.mpr ⟨y, h2, hlic⟩)
                have hslots_tail : slotsOf t (ms1 ++ ms2) = slotsOf t ms := by
                  apply List.map_congr_left; intro x hx; rw [htail_find x hx]
                have hstrs_tail : strsOf t (ms1 ++ ms2) = strsOf t ms := by
                  simp only [strsOf]
                  have : ∀ l : List Lic, (∀ x, x ∈ l → findChain x (ms1 ++ ms2) = findChain x ms) →
                      l.filterMap (fun x => (findChain x (ms1 ++ ms2)).map MGChain.str) =
                      l.filterMap (fun x => (findChain x ms).map MGChain.str) := by
                    intro l hl
                    induction l with
                    | nil => rfl
                    | cons a b ihb =>
                      simp only [List.filterMap_cons, hl a (List.mem_cons_self ..)]
                      cases (findChain a ms).map MGChain.str with
                      | none => exact ihb (fun x hx => hl x (List.mem_cons_of_mem _ hx))
                      | some s => exact congrArg (s :: ·) (ihb (fun x hx => hl x (List.mem_cons_of_mem _ hx)))
                  exact this t htail_find
                refine ⟨c.str, ms1, ms2, hms_eq', ?_, ?_, ?_⟩
                · rw [slotsOf_cons, hfg']; simp [hslots_tail]
                · rw [strsOf_cons_some hfg]; simp
                · rw [strsOf_cons_some hfg, strsOf_cons_none hfg', hstrs_tail, ← strsOf_length t ms]
                  have hev := evalYield_range_vars (pre ++ [c.str]) (strsOf t ms)
                  simp only [List.length_append, List.length_singleton, List.append_assoc,
                    List.singleton_append] at hev
                  exact hev
              · simp [hcf, hff'] at h
          | _ => simp [hcf] at h
    · simp only [hgf, ↓reduceIte] at h
      cases hfg : findChain g ms with
      | none =>
        simp only [hfg, Option.map_none, Option.map_eq_some_iff] at h
        obtain ⟨⟨p', os', vs'⟩, hrec, heq⟩ := h
        simp at heq; obtain ⟨rfl, rfl, rfl⟩ := heq
        obtain ⟨tStr, ms1, ms2, hms_eq, hslots_t, hget, heval⟩ := ih ht_nd pre hrec
        have hfg' : findChain g (ms1 ++ ms2) = none := by
          rw [findChain_eq_none_iff] at hfg ⊢
          intro y hy
          apply hfg y
          rw [hms_eq]
          rcases List.mem_append.mp hy with h1 | h2
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
        refine ⟨tStr, ms1, ms2, hms_eq, ?_, ?_, ?_⟩
        · rw [slotsOf_cons, hfg']; simp [hslots_t]
        · rw [strsOf_cons_none hfg]; exact hget
        · rw [strsOf_cons_none hfg, strsOf_cons_none hfg']; exact heval
      | some c =>
        simp only [hfg, Option.map_some, Option.map_eq_some_iff] at h
        obtain ⟨⟨p', os', vs'⟩, hrec, heq⟩ := h
        simp at heq; obtain ⟨rfl, rfl, rfl⟩ := heq
        have hrec' : clearSlot f (pre ++ [c.str]).length t (slotsOf t ms) = some (p', os', vs') := by
          simpa [List.length_append] using hrec
        obtain ⟨tStr, ms1, ms2, hms_eq, hslots_t, hget, heval⟩ := ih ht_nd (pre ++ [c.str]) hrec'
        obtain ⟨hc_in, hlic⟩ := (findChain_eq_some_iff hsmc).mp hfg
        have hsmc' : SMC (ms1 ++ ms2) := MG.smc_remove (hms_eq ▸ hsmc)
        have hc_in' : c ∈ ms1 ++ ms2 := by
          rw [hms_eq] at hc_in
          rcases List.mem_append.mp hc_in with h1 | h2
          · exact List.mem_append_left _ h1
          · rcases List.mem_cons.mp h2 with heq | h2'
            · subst heq; simp [MGChain.headLic] at hlic; exact absurd hlic.symm hgf
            · exact List.mem_append_right _ h2'
        have hfg' : findChain g (ms1 ++ ms2) = some c :=
          (findChain_eq_some_iff hsmc').mpr ⟨hc_in', hlic⟩
        refine ⟨tStr, ms1, ms2, hms_eq, ?_, ?_, ?_⟩
        · rw [slotsOf_cons, hfg']; simp [hslots_t]
        · rw [strsOf_cons_some hfg]; simpa [List.append_assoc] using hget
        · rw [strsOf_cons_some hfg, strsOf_cons_some hfg']
          simp only [MCFG.evalYield, List.map_cons]
          have hhead : MCFG.evalComp [pre ++ c.str :: strsOf t ms]
              [MCFGAtom.var 0 pre.length] = c.str := by simp [MCFG.evalComp]
          rw [hhead]
          congr 1
          simpa [MCFG.evalYield, List.append_assoc] using heval

/-- Completeness helper for `Move1`: if `ms = ms1 ++ ⟨tStr, [licensee f]⟩ :: ms2` and `f ∈ L`,
    then `clearSlot f c L (slotsOf L ms)` succeeds. -/
theorem clearSlot_complete [DecidableEq Lic]
    (L : List Lic) {f : Lic} (hfL : f ∈ L)
    {tStr : List T} {ms1 ms2 : List (MGChain Base Lic T)}
    (hsmc : SMC (ms1 ++ ⟨tStr, [MGFeature.licensee f]⟩ :: ms2)) :
    ∀ c, ∃ p s' vs,
      clearSlot (T := T) f c L (slotsOf L (ms1 ++ ⟨tStr, [MGFeature.licensee f]⟩ :: ms2)) =
        some (p, s', vs) := by
  let ms := ms1 ++ ⟨tStr, [MGFeature.licensee f]⟩ :: ms2
  induction L with
  | nil => simp at hfL
  | cons g t ih =>
    intro c
    rw [slotsOf_cons]
    simp only [clearSlot]
    by_cases hgf : g = f
    · subst g
      have hfind : findChain f ms = some ⟨tStr, [MGFeature.licensee f]⟩ :=
        (findChain_eq_some_iff hsmc).mpr
          ⟨List.mem_append_right _ (List.mem_cons_self ..), rfl⟩
      simp [ms, hfind]
    · simp only [hgf, ↓reduceIte]
      have hft : f ∈ t := by
        rcases List.mem_cons.mp hfL with rfl | ht
        · exact absurd rfl hgf
        · exact ht
      cases hfg : findChain g ms with
      | none =>
        obtain ⟨p, s', vs, hrec⟩ := ih hft c
        exact ⟨p, none :: s', vs, by simp [hrec]⟩
      | some ch =>
        obtain ⟨p, s', vs, hrec⟩ := ih hft (c + 1)
        exact ⟨p, some ch.feats :: s', [MCFGAtom.var 0 c] :: vs, by simp [hrec]⟩

/-! ### Move2: Relocating a Mover from Slot `f` to Slot `f'` -/

/-- Find the active component index (starting from `c`) of slot `f` in `L`, plus its feature stack. -/
def locateSlot [DecidableEq Lic] (f : Lic) (c : Nat) :
    List Lic → List (Option (List (MGFeature Base Lic))) →
    Option (Nat × List (MGFeature Base Lic))
  | [], [] => none
  | g :: t, o :: os =>
    if g = f then
      match o with
      | some fs => some (c, fs)
      | none => none
    else
      match o with
      | none => locateSlot f c t os
      | some _ => locateSlot f (c + 1) t os
  | _, _ => none

/-- Traverse the slots while indexing the nonempty components of the original tuple. -/
def relocateSlot.go [DecidableEq Lic] (f f' : Lic)
    (δ : List (MGFeature Base Lic)) (pSrc : Nat) (c : Nat) :
    List Lic → List (Option (List (MGFeature Base Lic))) →
      Option (List (Option (List (MGFeature Base Lic))) × List (List (MCFGAtom T)))
  | [], [] => some ([], [])
  | g :: t, o :: os =>
    if g = f ∧ g = f' then
      -- Same slot: feature stack updates in place, variable stays `[var 0 pSrc]` (= `[var 0 c]`).
      (go f f' δ pSrc (c + 1) t os).map fun (os', vs) => (some δ :: os', [MCFGAtom.var 0 pSrc] :: vs)
    else if g = f then
      -- Source slot becomes `none` (skip `c`).
      (go f f' δ pSrc (c + 1) t os).map fun (os', vs) => (none :: os', vs)
    else if g = f' then
      -- Destination slot must currently be `none` (by SMC!).
      match o with
      | none => (go f f' δ pSrc c t os).map fun (os', vs) => (some δ :: os', [MCFGAtom.var 0 pSrc] :: vs)
      | some _ => none
    else
      match o with
      | none => (go f f' δ pSrc c t os).map fun (os', vs) => (none :: os', vs)
      | some fs' => (go f f' δ pSrc (c + 1) t os).map fun (os', vs) => (some fs' :: os', [MCFGAtom.var 0 c] :: vs)
  | _, _ => none

/-- Compute the updated slot list and variable permutation for `Move2`:
    slot `f` had `licensee f :: licensee f' :: δ'`; move it to slot `f'` with `licensee f' :: δ'`. -/
def relocateSlot [DecidableEq Base] [DecidableEq Lic] (f f' : Lic) (δ : List (MGFeature Base Lic))
    (L : List Lic) (s : List (Option (List (MGFeature Base Lic)))) :
    Option (List (Option (List (MGFeature Base Lic))) × List (List (MCFGAtom T))) :=
  match locateSlot f 1 L s with
  | none => none
  | some (pSrc, fs) =>
    if fs = MGFeature.licensee f :: δ then
      if f' ∈ L then relocateSlot.go f f' δ pSrc 1 L s else none
    else none

/-- Auxiliary properties of `locateSlot`. -/
theorem locateSlot_props [DecidableEq Lic] {f : Lic} {c p : Nat}
    {L : List Lic} {s : List (Option (List (MGFeature Base Lic)))}
    {fs : List (MGFeature Base Lic)}
    (h : locateSlot f c L s = some (p, fs)) :
    f ∈ L ∧ c ≤ p ∧ p < c + s.countP Option.isSome := by
  induction L generalizing s c with
  | nil => cases s <;> simp [locateSlot] at h
  | cons g t ih =>
    cases s with
    | nil => simp [locateSlot] at h
    | cons o os =>
      simp only [locateSlot] at h
      by_cases hgf : g = f
      · subst hgf
        cases o with
        | none => simp at h
        | some fs' =>
          simp at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨List.mem_cons_self .., Nat.le_refl _, by simp⟩
      · simp only [hgf, ↓reduceIte] at h
        cases o with
        | none =>
          obtain ⟨h1, h2, h3⟩ := ih h
          exact ⟨List.mem_cons_of_mem _ h1, h2, by simp; omega⟩
        | some _ =>
          obtain ⟨h1, h2, h3⟩ := ih h
          exact ⟨List.mem_cons_of_mem _ h1, by omega, by simp; omega⟩

/-- Auxiliary properties of `relocateSlot.go` guaranteeing exact linearity & non-erasing bijection. -/
theorem relocateSlot_go_props [DecidableEq Lic] {f f' : Lic} {δ : List (MGFeature Base Lic)}
    {pSrc : Nat} :
    ∀ (c : Nat) (L : List Lic) (s s' : List (Option (List (MGFeature Base Lic))))
      (vs : List (List (MCFGAtom T))),
      L.Nodup →
      (f ∈ L → ∃ fs, locateSlot f c L s = some (pSrc, fs)) →
      (f ∉ L → pSrc < c) →
      relocateSlot.go f f' δ pSrc c L s = some (s', vs) →
      vs.length = s'.countP Option.isSome ∧
      (compsVars vs).Nodup ∧
      (∀ i j, (i, j) ∈ compsVars vs ↔
        (i = 0 ∧ f' ∈ L ∧ j = pSrc) ∨
        (i = 0 ∧ c ≤ j ∧ j < c + s.countP Option.isSome ∧ (f ∈ L → j ≠ pSrc))) := by
  intro c L
  induction L generalizing c with
  | nil =>
    intro s s' vs _ _ _ hgo
    cases s with
    | nil =>
      simp [relocateSlot.go] at hgo
      obtain ⟨rfl, rfl⟩ := hgo
      refine ⟨rfl, List.nodup_nil, ?_⟩
      intro i j; simp [compsVars]
    | cons _ _ => simp [relocateSlot.go] at hgo
  | cons g t ih =>
    intro s s' vs hnd hloc hnot hgo
    rw [List.nodup_cons] at hnd
    obtain ⟨hg_not, ht_nd⟩ := hnd
    cases s with
    | nil => simp [relocateSlot.go] at hgo
    | cons o os =>
      simp only [relocateSlot.go] at hgo
      by_cases hgf : g = f
      · subst hgf
        obtain ⟨fs, hloc_g⟩ := hloc (List.mem_cons_self ..)
        simp only [locateSlot, ↓reduceIte] at hloc_g
        cases o with
        | none => simp at hloc_g
        | some fs0 =>
          simp at hloc_g; obtain ⟨rfl, rfl⟩ := hloc_g
          by_cases hgf' : g = f'
          · subst hgf'
            simp only [and_self, ↓reduceIte, Option.map_eq_some_iff] at hgo
            obtain ⟨⟨os', vs'⟩, hrec, heq⟩ := hgo
            simp at heq; obtain ⟨rfl, rfl⟩ := heq
            obtain ⟨hlen, hnd', hmem⟩ := ih (c + 1) os os' vs' ht_nd
              (fun hbad => absurd hbad hg_not) (fun _ => by omega) hrec
            refine ⟨by simp [hlen], ?_, ?_⟩
            · rw [compsVars_cons_var, List.nodup_cons]
              refine ⟨?_, hnd'⟩
              intro hbad
              have := (hmem 0 c).mp hbad
              rcases this with ⟨_, hbad', _⟩ | ⟨_, hlo, _, _⟩
              · exact hg_not hbad'
              · omega
            · intro i j
              rw [compsVars_cons_var, List.mem_cons, Prod.mk.injEq, hmem i j]
              simp only [List.mem_cons, true_or, List.countP_cons, Option.isSome_some, ↓reduceIte,
                hg_not, false_and, and_false, false_or, false_implies, and_true, true_and, true_implies]
              constructor
              · rintro (⟨rfl, rfl⟩ | ⟨rfl, hlo, hhi⟩)
                · left; exact ⟨rfl, rfl⟩
                · right; refine ⟨rfl, ?_, ?_, ?_⟩ <;> omega
              · rintro (⟨rfl, rfl⟩ | ⟨rfl, hlo, hhi, hne⟩)
                · left; exact ⟨rfl, rfl⟩
                · right; refine ⟨rfl, ?_, ?_⟩ <;> omega
          · simp only [hgf', and_false, ↓reduceIte, Option.map_eq_some_iff] at hgo
            obtain ⟨⟨os', vs'⟩, hrec, heq⟩ := hgo
            simp at heq; obtain ⟨rfl, rfl⟩ := heq
            obtain ⟨hlen, hnd', hmem⟩ := ih (c + 1) os os' vs' ht_nd
              (fun hbad => absurd hbad hg_not) (fun _ => by omega) hrec
            refine ⟨by simp [hlen], hnd', ?_⟩
            intro i j
            rw [hmem i j]
            simp only [List.mem_cons, Ne.symm hgf', false_or, true_or, List.countP_cons,
              Option.isSome_some, ↓reduceIte, hg_not, false_implies, and_true, true_implies]
            constructor
            · rintro (h1 | ⟨rfl, hlo, hhi⟩)
              · left; exact h1
              · right; refine ⟨rfl, ?_, ?_, ?_⟩ <;> omega
            · rintro (h1 | ⟨rfl, hlo, hhi, hne⟩)
              · left; exact h1
              · right; refine ⟨rfl, ?_, ?_⟩ <;> omega
      · simp only [hgf, false_and, ↓reduceIte] at hgo
        by_cases hgf' : g = f'
        · subst hgf'
          simp only [↓reduceIte] at hgo
          cases o with
          | some _ => simp at hgo
          | none =>
            simp only [Option.map_eq_some_iff] at hgo
            obtain ⟨⟨os', vs'⟩, hrec, heq⟩ := hgo
            simp at heq; obtain ⟨rfl, rfl⟩ := heq
            have hloc_t : f ∈ t → ∃ fs, locateSlot f c t os = some (pSrc, fs) := by
              intro hft
              obtain ⟨fs, h1⟩ := hloc (List.mem_cons_of_mem _ hft)
              exact ⟨fs, by simpa [locateSlot, hgf] using h1⟩
            have hnot_t : f ∉ t → pSrc < c := fun hnt =>
              hnot (fun hm => by
                rcases List.mem_cons.mp hm with rfl | ht'
                · exact hgf rfl
                · exact hnt ht')
            obtain ⟨hlen, hnd', hmem⟩ := ih c os os' vs' ht_nd hloc_t hnot_t hrec
            refine ⟨by simp [hlen], ?_, ?_⟩
            · rw [compsVars_cons_var, List.nodup_cons]
              refine ⟨?_, hnd'⟩
              intro hbad
              have := (hmem 0 pSrc).mp hbad
              rcases this with ⟨_, hbad', _⟩ | ⟨_, hlo, _, hne⟩
              · exact hg_not hbad'
              · by_cases hft : f ∈ t
                · exact hne hft rfl
                · have := hnot_t hft; omega
            · intro i j
              rw [compsVars_cons_var, List.mem_cons, Prod.mk.injEq, hmem i j]
              simp [List.mem_cons, hg_not, Ne.symm hgf]
        · simp only [hgf', ↓reduceIte] at hgo
          cases o with
          | none =>
            simp only [Option.map_eq_some_iff] at hgo
            obtain ⟨⟨os', vs'⟩, hrec, heq⟩ := hgo
            simp at heq; obtain ⟨rfl, rfl⟩ := heq
            have hloc_t : f ∈ t → ∃ fs, locateSlot f c t os = some (pSrc, fs) := by
              intro hft
              obtain ⟨fs, h1⟩ := hloc (List.mem_cons_of_mem _ hft)
              exact ⟨fs, by simpa [locateSlot, hgf] using h1⟩
            have hnot_t : f ∉ t → pSrc < c := fun hnt =>
              hnot (fun hm => by
                rcases List.mem_cons.mp hm with rfl | ht'
                · exact hgf rfl
                · exact hnt ht')
            obtain ⟨hlen, hnd', hmem⟩ := ih c os os' vs' ht_nd hloc_t hnot_t hrec
            refine ⟨by simp [hlen], hnd', ?_⟩
            intro i j
            rw [hmem i j]
            simp [List.mem_cons, Ne.symm hgf', Ne.symm hgf]
          | some fs0 =>
            simp only [Option.map_eq_some_iff] at hgo
            obtain ⟨⟨os', vs'⟩, hrec, heq⟩ := hgo
            simp at heq; obtain ⟨rfl, rfl⟩ := heq
            have hloc_t : f ∈ t → ∃ fs, locateSlot f (c + 1) t os = some (pSrc, fs) := by
              intro hft
              obtain ⟨fs, h1⟩ := hloc (List.mem_cons_of_mem _ hft)
              exact ⟨fs, by simpa [locateSlot, hgf] using h1⟩
            have hnot_t : f ∉ t → pSrc < c + 1 := fun hnt => by
              have := hnot (fun hm => by
                rcases List.mem_cons.mp hm with rfl | ht'
                · exact hgf rfl
                · exact hnt ht')
              omega
            have hp_ne_c : pSrc ≠ c := by
              by_cases hft : f ∈ t
              · obtain ⟨fs, hl⟩ := hloc_t hft
                have ⟨_, hge, _⟩ := locateSlot_props hl
                omega
              · have := hnot (fun hm => by
                  rcases List.mem_cons.mp hm with rfl | ht'
                  · exact hgf rfl
                  · exact hft ht')
                omega
            obtain ⟨hlen, hnd', hmem⟩ := ih (c + 1) os os' vs' ht_nd hloc_t hnot_t hrec
            refine ⟨by simp [hlen], ?_, ?_⟩
            · rw [compsVars_cons_var, List.nodup_cons]
              refine ⟨?_, hnd'⟩
              intro hbad
              have := (hmem 0 c).mp hbad
              rcases this with ⟨_, _, heq⟩ | ⟨_, hlo, _, _⟩
              · exact hp_ne_c heq.symm
              · omega
            · intro i j
              rw [compsVars_cons_var, List.mem_cons, Prod.mk.injEq, hmem i j]
              simp only [List.mem_cons, Ne.symm hgf', Ne.symm hgf, false_or,
                List.countP_cons, Option.isSome_some, ↓reduceIte]
              constructor
              · rintro (⟨rfl, rfl⟩ | h1 | ⟨rfl, hlo, hhi, hne⟩)
                · right; refine ⟨rfl, Nat.le_refl _, ?_, fun _ => Ne.symm hp_ne_c⟩; omega
                · left; exact h1
                · right; refine ⟨rfl, ?_, ?_, hne⟩ <;> omega
              · rintro (h1 | ⟨rfl, hlo, hhi, hne⟩)
                · right; left; exact h1
                · by_cases hj : j = c
                  · left; exact ⟨rfl, hj⟩
                  · right; right; refine ⟨rfl, ?_, ?_, hne⟩ <;> omega

theorem relocateSlot_props [DecidableEq Base] [DecidableEq Lic] {f f' : Lic} {δ : List (MGFeature Base Lic)}
    {L : List Lic} (hnd : L.Nodup)
    {s s' : List (Option (List (MGFeature Base Lic)))} {vs : List (List (MCFGAtom T))}
    (h : relocateSlot f f' δ L s = some (s', vs)) :
    vs.length = s'.countP Option.isSome ∧
    (compsVars vs).Nodup ∧
    (∀ i j, (i, j) ∈ compsVars vs ↔ i = 0 ∧ 1 ≤ j ∧ j < 1 + s.countP Option.isSome) := by
  unfold relocateSlot at h
  cases hloc : locateSlot f 1 L s with
  | none => simp [hloc] at h
  | some pr =>
    obtain ⟨pSrc, fs⟩ := pr
    simp only [hloc] at h
    by_cases hfs : fs = MGFeature.licensee f :: δ
    · simp only [hfs, ↓reduceIte] at h
      by_cases hf' : f' ∈ L
      · simp only [hf', ↓reduceIte] at h
        have ⟨hfL, hge, hlt⟩ := locateSlot_props hloc
        obtain ⟨hlen, hnd', hmem⟩ := relocateSlot_go_props (T := T) 1 L s s' vs hnd
          (fun _ => ⟨fs, hloc⟩) (fun hnot => absurd hfL hnot) h
        refine ⟨hlen, hnd', ?_⟩
        intro i j
        rw [hmem i j]
        simp only [hf', hfL, true_and, true_implies]
        constructor
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, h1, h2, _⟩)
          · exact ⟨rfl, hge, hlt⟩
          · exact ⟨rfl, h1, h2⟩
        · rintro ⟨rfl, h1, h2⟩
          by_cases hj : j = pSrc
          · left; exact ⟨rfl, hj⟩
          · right; exact ⟨rfl, h1, h2, hj⟩
      · simp [hf'] at h
    · simp [hfs] at h

/-- Helper: `locateSlot` recovers the exact chain and string at position `pSrc`. -/
theorem locateSlot_eval [DecidableEq Lic] {f : Lic}
    (L : List Lic) {ms : List (MGChain Base Lic T)} (_hsmc : SMC ms)
    {p : Nat} {fs : List (MGFeature Base Lic)} :
    ∀ (pre : List (List T)),
      locateSlot f pre.length L (slotsOf L ms) = some (p, fs) →
      ∃ c, findChain f ms = some c ∧ c.feats = fs ∧ (pre ++ strsOf L ms)[p]? = some c.str := by
  induction L generalizing p with
  | nil => intro pre h; simp [slotsOf, locateSlot] at h
  | cons g t ih =>
    intro pre h
    rw [slotsOf_cons] at h
    simp only [locateSlot] at h
    by_cases hgf : g = f
    · subst hgf
      simp only [↓reduceIte] at h
      cases hfg : findChain g ms with
      | none => simp [hfg] at h
      | some c =>
        simp [hfg] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨c, rfl, rfl, by rw [strsOf_cons_some hfg]; simp⟩
    · simp only [hgf, ↓reduceIte] at h
      cases hfg : findChain g ms with
      | none =>
        simp only [hfg, Option.map_none] at h
        obtain ⟨c, hc, hcf, hget⟩ := ih pre h
        exact ⟨c, hc, hcf, by rw [strsOf_cons_none hfg]; exact hget⟩
      | some cg =>
        simp only [hfg, Option.map_some] at h
        have h' : locateSlot f (pre ++ [cg.str]).length t (slotsOf t ms) = some (p, fs) := by
          simpa [List.length_append] using h
        obtain ⟨c, hc, hcf, hget⟩ := ih (pre ++ [cg.str]) h'
        exact ⟨c, hc, hcf, by rw [strsOf_cons_some hfg]; simpa [List.append_assoc] using hget⟩

private theorem relocateSlot_go_eval [DecidableEq Lic]
    {f f' : Lic} {δ' : List (MGFeature Base Lic)}
    (L : List Lic) {ms : List (MGChain Base Lic T)} (hsmc : SMC ms)
    (sHead : List T) (pSrc : Nat) (c : MGChain Base Lic T)
    (hfc : findChain f ms = some c) (hgetSrc : (sHead :: strsOf L ms)[pSrc]? = some c.str)
    (hc_in : c ∈ ms) (hlic : c.headLic = some f)
    (ms1 ms2 : List (MGChain Base Lic T)) (hms_eq : ms = ms1 ++ c :: ms2) :
    let δ := MGFeature.licensee f' :: δ'
    let newC : MGChain Base Lic T := ⟨c.str, MGFeature.licensee f' :: δ'⟩
    let msNew := ms1 ++ newC :: ms2
    SMC msNew →
    ∀ (L0 : List Lic) (pre : List (List T))
      (os' : List (Option (List (MGFeature Base Lic)))) (vs0 : List (List (MCFGAtom T))),
      pre ++ strsOf L0 ms = sHead :: strsOf L ms →
      relocateSlot.go f f' δ pSrc pre.length L0 (slotsOf L0 ms) = some (os', vs0) →
      slotsOf L0 msNew = os' ∧
        MCFG.evalYield [sHead :: strsOf L ms] vs0 = strsOf L0 msNew := by
  intro δ newC msNew hsmcNew
  intro L0
  induction L0 with
  | nil =>
    intro pre os' vs0 _ hgo
    simp [slotsOf, relocateSlot.go] at hgo
    obtain ⟨rfl, rfl⟩ := hgo
    exact ⟨rfl, rfl⟩
  | cons g t ih =>
    intro pre os' vs0 hpre hgo
    rw [slotsOf_cons] at hgo
    simp only [relocateSlot.go] at hgo
    have hfind_other : g ≠ f → g ≠ f' → findChain g msNew = findChain g ms := by
      intro hgf hgf'
      cases hfg : findChain g ms with
      | none =>
        rw [findChain_eq_none_iff] at hfg ⊢
        intro y hy
        rcases List.mem_append.mp hy with h1 | h2
        · exact hfg y (hms_eq ▸ List.mem_append_left _ h1)
        · rcases List.mem_cons.mp h2 with rfl | h2'
          · simp [newC, MGChain.headLic, Ne.symm hgf']
          · exact hfg y (hms_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ h2'))
      | some y =>
        obtain ⟨hy_in, hy_lic⟩ := (findChain_eq_some_iff hsmc).mp hfg
        have hy_in' : y ∈ msNew := by
          rw [hms_eq] at hy_in
          rcases List.mem_append.mp hy_in with h1 | h2
          · exact List.mem_append_left _ h1
          · rcases List.mem_cons.mp h2 with rfl | h2'
            · rw [hlic] at hy_lic; simp at hy_lic; exact absurd hy_lic.symm hgf
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2')
        exact (findChain_eq_some_iff hsmcNew).mpr ⟨hy_in', hy_lic⟩
    have hfind_f' : findChain f' msNew = some newC :=
      (findChain_eq_some_iff hsmcNew).mpr ⟨List.mem_append_right _ (List.mem_cons_self ..), rfl⟩
    have hfind_f_ne : f ≠ f' → findChain f msNew = none := by
      intro hne
      rw [findChain_eq_none_iff]
      intro y hy hylic
      rcases List.mem_append.mp hy with h1 | h2
      · have hy_eq := smc_unique_chain hsmc (hms_eq ▸ List.mem_append_left _ h1) hylic hc_in hlic
        subst hy_eq
        have hnd0 := hsmc.2; rw [hms_eq] at hnd0
        simp only [List.filterMap_append, List.filterMap_cons, hlic, List.nodup_append,
          List.nodup_cons] at hnd0
        exact hnd0.2.2 f (List.mem_filterMap.mpr ⟨y, h1, hlic⟩) f (List.mem_cons_self ..) rfl
      · rcases List.mem_cons.mp h2 with rfl | h2'
        · simp [newC, MGChain.headLic] at hylic; exact hne hylic.symm
        · have hy_eq := smc_unique_chain hsmc (hms_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ h2')) hylic hc_in hlic
          subst hy_eq
          have hnd0 := hsmc.2; rw [hms_eq] at hnd0
          simp only [List.filterMap_append, List.filterMap_cons, hlic, List.nodup_append,
            List.nodup_cons] at hnd0
          exact hnd0.2.1.1 (List.mem_filterMap.mpr ⟨y, h2', hlic⟩)
    by_cases hgf : g = f
    · subst hgf
      have hpre' : (pre ++ [c.str]) ++ strsOf t ms = sHead :: strsOf L ms := by
        rw [strsOf_cons_some hfc] at hpre
        simpa [List.append_assoc] using hpre
      by_cases hgf' : g = f'
      · subst hgf'
        simp only [and_self, ↓reduceIte, Option.map_eq_some_iff] at hgo
        obtain ⟨⟨os1, vs1⟩, hrec, heq⟩ := hgo
        simp at heq; obtain ⟨rfl, rfl⟩ := heq
        have hrec' : relocateSlot.go g g δ pSrc (pre ++ [c.str]).length t (slotsOf t ms) = some (os1, vs1) := by
          simpa [List.length_append] using hrec
        obtain ⟨hsl, hev⟩ := ih (pre ++ [c.str]) os1 vs1 hpre' hrec'
        refine ⟨?_, ?_⟩
        · rw [slotsOf_cons, hfind_f']; simp [newC, δ, hsl]
        · rw [strsOf_cons_some hfind_f']
          simp only [MCFG.evalYield, List.map_cons]
          have hhead : MCFG.evalComp [sHead :: strsOf L ms] [MCFGAtom.var 0 pSrc] = c.str := by
            simp [MCFG.evalComp, hgetSrc]
          rw [hhead]
          exact congrArg (c.str :: ·) hev
      · simp only [hgf', and_false, ↓reduceIte, Option.map_eq_some_iff] at hgo
        obtain ⟨⟨os1, vs1⟩, hrec, heq⟩ := hgo
        simp at heq; obtain ⟨rfl, rfl⟩ := heq
        have hrec' : relocateSlot.go g f' δ pSrc (pre ++ [c.str]).length t (slotsOf t ms) = some (os1, vs1) := by
          simpa [List.length_append] using hrec
        obtain ⟨hsl, hev⟩ := ih (pre ++ [c.str]) os1 vs1 hpre' hrec'
        have hfn := hfind_f_ne hgf'
        refine ⟨?_, ?_⟩
        · rw [slotsOf_cons, hfn]; simp [hsl]
        · rw [strsOf_cons_none hfn]; exact hev
    · simp only [hgf, false_and, ↓reduceIte] at hgo
      by_cases hgf' : g = f'
      · subst hgf'
        simp only [↓reduceIte] at hgo
        cases hfg : findChain g ms with
        | some _ => simp [hfg] at hgo
        | none =>
          simp only [hfg, Option.map_none, Option.map_eq_some_iff] at hgo
          obtain ⟨⟨os1, vs1⟩, hrec, heq⟩ := hgo
          simp at heq; obtain ⟨rfl, rfl⟩ := heq
          have hpre' : pre ++ strsOf t ms = sHead :: strsOf L ms := by
            rw [strsOf_cons_none hfg] at hpre; exact hpre
          obtain ⟨hsl, hev⟩ := ih pre os1 vs1 hpre' hrec
          refine ⟨?_, ?_⟩
          · rw [slotsOf_cons, hfind_f']; simp [newC, δ, hsl]
          · rw [strsOf_cons_some hfind_f']
            simp only [MCFG.evalYield, List.map_cons]
            have hhead : MCFG.evalComp [sHead :: strsOf L ms] [MCFGAtom.var 0 pSrc] = c.str := by
              simp [MCFG.evalComp, hgetSrc]
            rw [hhead]
            exact congrArg (c.str :: ·) hev
      · simp only [hgf', ↓reduceIte] at hgo
        have hsame := hfind_other hgf hgf'
        cases hfg : findChain g ms with
        | none =>
          simp only [hfg, Option.map_none, Option.map_eq_some_iff] at hgo
          obtain ⟨⟨os1, vs1⟩, hrec, heq⟩ := hgo
          simp at heq; obtain ⟨rfl, rfl⟩ := heq
          have hpre' : pre ++ strsOf t ms = sHead :: strsOf L ms := by
            rw [strsOf_cons_none hfg] at hpre; exact hpre
          obtain ⟨hsl, hev⟩ := ih pre os1 vs1 hpre' hrec
          refine ⟨?_, ?_⟩
          · rw [slotsOf_cons, hsame, hfg]; simp [hsl]
          · rw [strsOf_cons_none (hsame.trans hfg)]; exact hev
        | some cg =>
          simp only [hfg, Option.map_some, Option.map_eq_some_iff] at hgo
          obtain ⟨⟨os1, vs1⟩, hrec, heq⟩ := hgo
          simp at heq; obtain ⟨rfl, rfl⟩ := heq
          have hpre' : (pre ++ [cg.str]) ++ strsOf t ms = sHead :: strsOf L ms := by
            rw [strsOf_cons_some hfg] at hpre
            simpa [List.append_assoc] using hpre
          have hrec' : relocateSlot.go f f' δ pSrc (pre ++ [cg.str]).length t (slotsOf t ms) = some (os1, vs1) := by
            simpa [List.length_append] using hrec
          obtain ⟨hsl, hev⟩ := ih (pre ++ [cg.str]) os1 vs1 hpre' hrec'
          refine ⟨?_, ?_⟩
          · rw [slotsOf_cons, hsame, hfg]; simp [hsl]
          · rw [strsOf_cons_some (hsame.trans hfg)]
            simp only [MCFG.evalYield, List.map_cons]
            have hhead : MCFG.evalComp [sHead :: strsOf L ms] [MCFGAtom.var 0 pre.length] = cg.str := by
              have hgetcg : (sHead :: strsOf L ms)[pre.length]? = some cg.str := by
                rw [← hpre, strsOf_cons_some hfg]; simp
              simp [MCFG.evalComp, hgetcg]
            rw [hhead]
            exact congrArg (cg.str :: ·) hev

/-- Soundness & evaluation helper for `Move2` (`relocateSlot`). -/
theorem relocateSlot_eval_and_mem [DecidableEq Base] [DecidableEq Lic]
    {f f' : Lic} {δ' : List (MGFeature Base Lic)}
    (L : List Lic) (_hLnd : L.Nodup)
    {ms : List (MGChain Base Lic T)} (hsmc : SMC ms)
    (_hLms : ∀ c, c ∈ ms → ∀ g, c.headLic = some g → g ∈ L)
    {s' : List (Option (List (MGFeature Base Lic)))} {vs : List (List (MCFGAtom T))}
    (sHead : List T)
    (h : relocateSlot f f' (MGFeature.licensee f' :: δ') L (slotsOf L ms) = some (s', vs)) :
    ∃ tStr ms1 ms2,
      ms = ms1 ++ ⟨tStr, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2 ∧
      SMC (ms1 ++ ⟨tStr, MGFeature.licensee f' :: δ'⟩ :: ms2) ∧
      slotsOf L (ms1 ++ ⟨tStr, MGFeature.licensee f' :: δ'⟩ :: ms2) = s' ∧
      MCFG.evalYield [sHead :: strsOf L ms] vs =
        strsOf L (ms1 ++ ⟨tStr, MGFeature.licensee f' :: δ'⟩ :: ms2) := by
  let δ := MGFeature.licensee f' :: δ'
  unfold relocateSlot at h
  cases hloc : locateSlot f 1 L (slotsOf L ms) with
  | none => simp [hloc] at h
  | some pr =>
    obtain ⟨pSrc, fs⟩ := pr
    simp only [hloc] at h
    by_cases hfs : fs = MGFeature.licensee f :: MGFeature.licensee f' :: δ'
    · simp only [hfs, ↓reduceIte] at h
      by_cases hf'L : f' ∈ L
      · simp only [hf'L, ↓reduceIte] at h
        obtain ⟨c, hfc, hcf, hgetSrc⟩ := locateSlot_eval L hsmc [sHead] hloc
        simp only [List.singleton_append] at hgetSrc
        have hcf' : c.feats = MGFeature.licensee f :: MGFeature.licensee f' :: δ' := hcf.trans hfs
        obtain ⟨hc_in, hlic⟩ := (findChain_eq_some_iff hsmc).mp hfc
        obtain ⟨ms1, ms2, hms_eq⟩ := List.append_of_mem hc_in
        have hce : c = ⟨c.str, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ := by
          cases c; simp at hcf'; subst hcf'; rfl
        have hms_eq' : ms = ms1 ++ ⟨c.str, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2 := by
          rw [← hce]; exact hms_eq
        let newC : MGChain Base Lic T := ⟨c.str, MGFeature.licensee f' :: δ'⟩
        let msNew := ms1 ++ newC :: ms2
        -- First check SMC msNew: if f' ≠ f, then slot f' in slotsOf L ms must be none!
        have hsmc_rem : SMC (ms1 ++ ms2) := MG.smc_remove (hms_eq ▸ hsmc)
        have hf'_free : f' ≠ f → findChain f' ms = none := by
          intro hne
          -- From relocateSlot.go succeeding with f' ∈ L and f' ≠ f, the slot at f' in slotsOf L ms is none
          have hgo_none : ∀ (c0 : Nat) (L0 : List Lic) (os' : List (Option (List (MGFeature Base Lic))))
              (vs0 : List (List (MCFGAtom T))),
              f' ∈ L0 → relocateSlot.go f f' δ pSrc c0 L0 (slotsOf L0 ms) = some (os', vs0) →
              findChain f' ms = none := by
            intro c0 L0
            induction L0 generalizing c0 with
            | nil => intro _ _ hm; simp at hm
            | cons g t ih =>
              intro os' vs0 hm hgo
              rw [slotsOf_cons] at hgo
              simp only [relocateSlot.go] at hgo
              rcases List.mem_cons.mp hm with rfl | ht
              · simp only [hne, false_and, ↓reduceIte] at hgo
                cases hff : findChain f' ms with
                | none => rfl
                | some _ => simp [hff] at hgo
              · by_cases hgf : g = f
                · subst hgf
                  by_cases hgf' : g = f'
                  · exact absurd hgf'.symm hne
                  · simp only [hgf', and_false, ↓reduceIte, Option.map_eq_some_iff] at hgo
                    obtain ⟨⟨_, _⟩, hrec, _⟩ := hgo
                    exact ih (c0 + 1) _ _ ht hrec
                · by_cases hgf' : g = f'
                  · subst hgf'
                    simp only [hgf, false_and, ↓reduceIte] at hgo
                    cases hff : findChain g ms with
                    | none => rfl
                    | some _ => simp [hff] at hgo
                  · simp only [hgf, false_and, hgf', ↓reduceIte] at hgo
                    cases hfg : findChain g ms with
                    | none =>
                      simp only [hfg, Option.map_none, Option.map_eq_some_iff] at hgo
                      obtain ⟨⟨_, _⟩, hrec, _⟩ := hgo
                      exact ih c0 _ _ ht hrec
                    | some _ =>
                      simp only [hfg, Option.map_some, Option.map_eq_some_iff] at hgo
                      obtain ⟨⟨_, _⟩, hrec, _⟩ := hgo
                      exact ih (c0 + 1) _ _ ht hrec
          exact hgo_none 1 L s' vs hf'L h
        have hsmcNew : SMC msNew := by
          refine ⟨?_, ?_⟩
          · intro x hx
            rcases List.mem_append.mp hx with h1 | h2
            · exact hsmc_rem.1 x (List.mem_append_left _ h1)
            · rcases List.mem_cons.mp h2 with rfl | h2'
              · exact ⟨f', δ', rfl⟩
              · exact hsmc_rem.1 x (List.mem_append_right _ h2')
          · have hnd := hsmc_rem.2
            simp only [msNew, List.filterMap_append, List.filterMap_cons]
            change ((ms1.filterMap MGChain.headLic) ++ f' :: (ms2.filterMap MGChain.headLic)).Nodup
            rw [List.filterMap_append, List.nodup_append] at hnd
            rw [List.nodup_append, List.nodup_cons]
            have hf'_not_rem : ∀ x, x ∈ ms1 ++ ms2 → x.headLic ≠ some f' := by
              intro x hx hxlic
              by_cases hff' : f' = f
              · subst hff'
                have hx_in : x ∈ ms := by
                  rw [hms_eq]
                  rcases List.mem_append.mp hx with h1 | h2
                  · exact List.mem_append_left _ h1
                  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
                have hxeq := smc_unique_chain hsmc hx_in hxlic hc_in hlic
                subst hxeq
                have hnd0 := hsmc.2
                rw [hms_eq] at hnd0
                simp only [List.filterMap_append, List.filterMap_cons, hlic, List.nodup_append,
                  List.nodup_cons] at hnd0
                rcases List.mem_append.mp hx with h1 | h2
                · exact hnd0.2.2 f' (List.mem_filterMap.mpr ⟨x, h1, hlic⟩) f' (List.mem_cons_self ..) rfl
                · exact hnd0.2.1.1 (List.mem_filterMap.mpr ⟨x, h2, hlic⟩)
              · have hnone := hf'_free hff'
                have hx_in : x ∈ ms := by
                  rw [hms_eq]
                  rcases List.mem_append.mp hx with h1 | h2
                  · exact List.mem_append_left _ h1
                  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
                exact (findChain_eq_none_iff.mp hnone) x hx_in hxlic
            refine ⟨hnd.1, ⟨?_, hnd.2.1⟩, ?_⟩
            · intro hmem2
              obtain ⟨x, hx2, hxlic⟩ := List.mem_filterMap.mp hmem2
              exact hf'_not_rem x (List.mem_append_right _ hx2) hxlic
            · intro a ha b hb
              rcases List.mem_cons.mp hb with rfl | hb2
              · intro heq; subst heq
                obtain ⟨x, hx1, hxlic⟩ := List.mem_filterMap.mp ha
                exact hf'_not_rem x (List.mem_append_left _ hx1) hxlic
              · exact hnd.2.2 a ha b hb2
        -- Now prove slotsOf and evalYield match by induction on L0 with running prefix `pre`!
        obtain ⟨hsl, hev⟩ := relocateSlot_go_eval (f' := f') (δ' := δ') L hsmc
          sHead pSrc c hfc hgetSrc hc_in hlic ms1 ms2 hms_eq hsmcNew L [sHead] s' vs rfl h
        exact ⟨c.str, ms1, ms2, hms_eq', hsmcNew, hsl, hev⟩
      · simp [hf'L] at h
    · simp [hfs] at h

/-- Completeness helper for `Move2`: if `ms = ms1 ++ ⟨tStr, licensee f :: licensee f' :: δ'⟩ :: ms2`
    and `SMC (ms1 ++ ⟨tStr, licensee f' :: δ'⟩ :: ms2)` and `f, f' ∈ L`, then `relocateSlot` succeeds. -/
theorem relocateSlot_complete [DecidableEq Base] [DecidableEq Lic]
    {f f' : Lic} {δ' : List (MGFeature Base Lic)} {tStr : List T}
    (L : List Lic) (hfL : f ∈ L) (hf'L : f' ∈ L)
    {ms1 ms2 : List (MGChain Base Lic T)}
    (hsmc : SMC (ms1 ++ ⟨tStr, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2))
    (hsmcNew : SMC (ms1 ++ ⟨tStr, MGFeature.licensee f' :: δ'⟩ :: ms2)) :
    ∃ s' vs,
      relocateSlot (T := T) f f' (MGFeature.licensee f' :: δ') L
        (slotsOf L (ms1 ++ ⟨tStr, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2)) =
      some (s', vs) := by
  let oldC : MGChain Base Lic T := ⟨tStr, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩
  let newC : MGChain Base Lic T := ⟨tStr, MGFeature.licensee f' :: δ'⟩
  let ms := ms1 ++ oldC :: ms2
  let msNew := ms1 ++ newC :: ms2
  have hfc : findChain f ms = some oldC :=
    (findChain_eq_some_iff hsmc).mpr ⟨List.mem_append_right _ (List.mem_cons_self ..), rfl⟩
  -- locateSlot succeeds because f ∈ L and findChain f ms = some oldC
  have hloc_ex : ∀ (L0 : List Lic) (c0 : Nat), f ∈ L0 →
      ∃ p, locateSlot f c0 L0 (slotsOf L0 ms) = some (p, oldC.feats) := by
    intro L0
    induction L0 with
    | nil => intro _ hm; simp at hm
    | cons g t ih =>
      intro c0 hm
      simp only [slotsOf, List.map_cons, locateSlot]
      by_cases hgf : g = f
      · subst hgf; simp [hfc]
      · simp only [hgf, ↓reduceIte]
        have hft : f ∈ t := by
          rcases List.mem_cons.mp hm with rfl | ht
          · exact absurd rfl hgf
          · exact ht
        cases findChain g ms with
        | none => exact ih c0 hft
        | some _ => exact ih (c0 + 1) hft
  obtain ⟨pSrc, hloc⟩ := hloc_ex L 1 hfL
  -- If f' ≠ f, then findChain f' ms = none (otherwise SMC msNew would fail!)
  have hf'_none : f' ≠ f → findChain f' ms = none := by
    intro hne
    rw [findChain_eq_none_iff]
    intro x hx hxlic
    rcases List.mem_append.mp hx with h1 | h2
    · have hnd := hsmcNew.2
      simp only [List.filterMap_append, List.filterMap_cons, List.nodup_append] at hnd
      have hm1 : f' ∈ ms1.filterMap MGChain.headLic := List.mem_filterMap.mpr ⟨x, h1, hxlic⟩
      exact hnd.2.2 f' hm1 f' (List.mem_cons_self ..) rfl
    · rcases List.mem_cons.mp h2 with rfl | h2'
      · simp [oldC, MGChain.headLic] at hxlic; exact hne hxlic.symm
      · have hnd := hsmcNew.2
        simp only [List.filterMap_append, List.filterMap_cons, MGChain.headLic,
          List.nodup_append, List.nodup_cons] at hnd
        have hm2 : f' ∈ ms2.filterMap MGChain.headLic := List.mem_filterMap.mpr ⟨x, h2', hxlic⟩
        exact hnd.2.1.1 hm2
  have hgo_ex : ∀ (L0 : List Lic) (c0 : Nat),
      ∃ os' vs0, relocateSlot.go (T := T) f f' (MGFeature.licensee f' :: δ') pSrc c0 L0 (slotsOf L0 ms) = some (os', vs0) := by
    intro L0
    induction L0 with
    | nil => intro c0; exact ⟨[], [], rfl⟩
    | cons g t ih =>
      intro c0
      rw [slotsOf_cons]
      simp only [relocateSlot.go]
      by_cases hgf : g = f
      · subst hgf
        by_cases hgf' : g = f'
        · subst hgf'
          obtain ⟨os', vs0, hrec⟩ := ih (c0 + 1)
          exact ⟨some (MGFeature.licensee g :: δ') :: os', [MCFGAtom.var 0 pSrc] :: vs0, by simp [hrec]⟩
        · obtain ⟨os', vs0, hrec⟩ := ih (c0 + 1)
          exact ⟨none :: os', vs0, by simp [hgf', hrec]⟩
      · by_cases hgf' : g = f'
        · subst hgf'
          have hfn : findChain g ms = none := hf'_none hgf
          obtain ⟨os', vs0, hrec⟩ := ih c0
          exact ⟨some (MGFeature.licensee g :: δ') :: os', [MCFGAtom.var 0 pSrc] :: vs0, by simp [hgf, hfn, hrec]⟩
        · cases hfg : findChain g ms with
          | none =>
            obtain ⟨os', vs0, hrec⟩ := ih c0
            exact ⟨none :: os', vs0, by simp [hgf, hgf', hrec]⟩
          | some ch =>
            obtain ⟨os', vs0, hrec⟩ := ih (c0 + 1)
            exact ⟨some ch.feats :: os', [MCFGAtom.var 0 c0] :: vs0, by simp [hgf, hgf', hrec]⟩
  obtain ⟨s', vs, hgo⟩ := hgo_ex L 1
  refine ⟨s', vs, ?_⟩
  change relocateSlot (T := T) f f' (MGFeature.licensee f' :: δ') L (slotsOf L ms) = some (s', vs)
  unfold relocateSlot
  simp only [hloc, oldC, ↓reduceIte, hf'L]
  exact hgo

/-! ### Part 5: Finite Enumeration of All Valid MG Profiles & MCFG Rules -/

/-- Cartesian product of finite lists of slot choices along `L`. -/
def allSlotVectors [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T) :
    List Lic → List (List (Option (List (MGFeature Base Lic))))
  | [] => [[]]
  | f :: t =>
    let tailVecs := allSlotVectors G t
    let headChoices : List (Option (List (MGFeature Base Lic))) :=
      none :: (licFeats G f).map some
    headChoices.flatMap fun o => tailVecs.map fun rest => o :: rest

theorem mem_allSlotVectors_of_movers [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {ms : List (MGChain Base Lic T)} (hsmc : SMC ms)
    (hsuf : ∀ c, c ∈ ms → ∃ entry, entry ∈ G.lexicon ∧ MG.isSuffix c.feats entry.2) :
    ∀ L, slotsOf L ms ∈ allSlotVectors G L := by
  intro L
  induction L with
  | nil => simp [slotsOf, allSlotVectors]
  | cons f t ih =>
    simp only [slotsOf, List.map_cons, allSlotVectors, List.mem_flatMap, List.mem_map]
    cases hfg : findChain f ms with
    | none =>
      exact ⟨none, List.mem_cons_self .., slotsOf t ms, ih, rfl⟩
    | some c =>
      obtain ⟨hc_in, hlic⟩ := (findChain_eq_some_iff hsmc).mp hfg
      obtain ⟨entry, hentry, hs⟩ := hsuf c hc_in
      obtain ⟨f', δ, hcf⟩ := hsmc.1 c hc_in
      have hfeq : f' = f := by simp [MGChain.headLic, hcf] at hlic; exact hlic
      subst f'
      have hmem_lf : c.feats ∈ licFeats G f :=
        mem_licFeats_iff.mpr ⟨mem_allFeats_of_suffix hentry hs, δ, hcf⟩
      refine ⟨some c.feats, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c.feats, hmem_lf, rfl⟩),
        slotsOf t ms, ih, rfl⟩

/-- Finite list of all reachable MG profiles `(isLex, headFeats, slots)`. -/
def allProfiles [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T) :
    List (Bool × List (MGFeature Base Lic) × List (Option (List (MGFeature Base Lic)))) :=
  [true, false].flatMap fun b =>
    (allFeats G).flatMap fun α =>
      (allSlotVectors G (allLics G)).map fun slots => (b, α, slots)

theorem mem_allProfiles_of_derives [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {e : MGExpr Base Lic T} (h : MG.Derives G e) :
    (e.isLex, e.head.feats, slotsOf (allLics G) e.movers) ∈ allProfiles G := by
  obtain ⟨⟨e1, he1, hs1⟩, hm⟩ := h.feats_suffix
  have hsmc := h.smc
  simp only [allProfiles, List.mem_flatMap, List.mem_map]
  refine ⟨e.isLex, by cases e.isLex <;> simp, e.head.feats,
    mem_allFeats_of_suffix he1 hs1,
    slotsOf (allLics G) e.movers, mem_allSlotVectors_of_movers hsmc hm (allLics G), rfl⟩

/-- Simulating rules for merging a lexical selector with an already completed argument. -/
abbrev merge1Rules [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T)
    (profiles : List (Bool × List (MGFeature Base Lic) ×
      List (Option (List (MGFeature Base Lic))))) :
    List (MCFGRule (MGMCFGNT Base Lic) T) :=
  profiles.flatMap fun (b1, α1, s1) =>
    if b1 = true ∧ s1 = ((allLics G).map fun _ => none) then
      match α1 with
      | MGFeature.sel x :: γ =>
        profiles.filterMap fun (b2, α2, s2) =>
          if α2 = [MGFeature.cat x] then
            let tailVars := (List.range (s2.countP Option.isSome)).map fun k =>
              [MCFGAtom.var 1 (1 + k)]
            some {
              lhs := MGMCFGNT.prof false γ s2
              rhs := [MGMCFGNT.prof true (MGFeature.sel x :: γ) ((allLics G).map fun _ => none),
                      MGMCFGNT.prof b2 [MGFeature.cat x] s2]
              yield := [MCFGAtom.var 0 0, MCFGAtom.var 1 0] :: tailVars
            }
          else none
      | _ => []
    else []

/-- Simulating rules for merging a derived selector with an already completed argument. -/
abbrev merge2Rules [DecidableEq Base] [DecidableEq Lic]
    (profiles : List (Bool × List (MGFeature Base Lic) ×
      List (Option (List (MGFeature Base Lic))))) :
    List (MCFGRule (MGMCFGNT Base Lic) T) :=
  profiles.flatMap fun (b1, α1, s1) =>
    if b1 = false then
      match α1 with
      | MGFeature.sel x :: γ =>
        profiles.filterMap fun (b2, α2, s2) =>
          if α2 = [MGFeature.cat x] then
            match mergeSlots s1 s2 with
            | some s12 =>
              some {
                lhs := MGMCFGNT.prof false γ s12
                rhs := [MGMCFGNT.prof false (MGFeature.sel x :: γ) s1,
                        MGMCFGNT.prof b2 [MGFeature.cat x] s2]
                yield := [MCFGAtom.var 1 0, MCFGAtom.var 0 0] :: mergeVars 1 1 s1 s2
              }
            | none => none
          else none
      | _ => []
    else []

/-- Simulating rules for merging a selector whose argument must move later. -/
abbrev merge3Rules [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T)
    (profiles : List (Bool × List (MGFeature Base Lic) ×
      List (Option (List (MGFeature Base Lic))))) :
    List (MCFGRule (MGMCFGNT Base Lic) T) :=
  let L := allLics G
  profiles.flatMap fun (b1, α1, s1) =>
    match α1 with
    | MGFeature.sel x :: γ =>
      profiles.filterMap fun (b2, α2, s2) =>
        match α2 with
        | MGFeature.cat x' :: MGFeature.licensee f :: δ' =>
          if x' = x then
            match mergeSlots s1 s2 with
            | some s12 =>
              match insertSlot f (MGFeature.licensee f :: δ') L s12 with
              | some s3 =>
                some {
                  lhs := MGMCFGNT.prof false γ s3
                  rhs := [MGMCFGNT.prof b1 (MGFeature.sel x :: γ) s1,
                          MGMCFGNT.prof b2 (MGFeature.cat x :: MGFeature.licensee f :: δ') s2]
                  yield := [MCFGAtom.var 0 0] :: merge3Vars f 1 1 L s1 s2
                }
              | none => none
            | none => none
          else none
        | _ => none
    | _ => []

/-- Build the finite list of MCFG rules simulating `G`. -/
def buildRules [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T) :
    List (MCFGRule (MGMCFGNT Base Lic) T) :=
  let L := allLics G
  let emptySlots : List (Option (List (MGFeature Base Lic))) := L.map fun _ => none
  let profs := allProfiles G
  -- 0. Start rules (accepting lexical or derived `[cat G.start]` with empty movers)
  let startRules : List (MCFGRule (MGMCFGNT Base Lic) T) :=
    [true, false].map fun b =>
      { lhs := MGMCFGNT.start
        rhs := [MGMCFGNT.prof b [MGFeature.cat G.start] emptySlots]
        yield := [[MCFGAtom.var 0 0]] }
  -- 1. Lexicon rules
  let lexRules : List (MCFGRule (MGMCFGNT Base Lic) T) :=
    G.lexicon.map fun (w, α) =>
      { lhs := MGMCFGNT.prof true α emptySlots
        rhs := []
        yield := [w.map MCFGAtom.tm] }
  -- 5. Move 1 rules
  let move1Rules : List (MCFGRule (MGMCFGNT Base Lic) T) :=
    profs.filterMap fun (b, α, s) =>
      if b = false then
        match α with
        | MGFeature.licensor f :: γ =>
          match clearSlot (T := T) f 1 L s with
          | some (p, s', vs) =>
            some {
              lhs := MGMCFGNT.prof false γ s'
              rhs := [MGMCFGNT.prof false (MGFeature.licensor f :: γ) s]
              yield := [MCFGAtom.var 0 p, MCFGAtom.var 0 0] :: vs
            }
          | none => none
        | _ => none
      else none
  -- 6. Move 2 rules
  let move2Rules : List (MCFGRule (MGMCFGNT Base Lic) T) :=
    profs.flatMap fun (b, α, s) =>
      if b = false then
        match α with
        | MGFeature.licensor f :: γ =>
          L.flatMap fun f' =>
            (licFeats G f').filterMap fun δ =>
              match relocateSlot (T := T) f f' δ L s with
              | some (s', vs) =>
                some {
                  lhs := MGMCFGNT.prof false γ s'
                  rhs := [MGMCFGNT.prof false (MGFeature.licensor f :: γ) s]
                  yield := [MCFGAtom.var 0 0] :: vs
                }
              | none => none
        | _ => []
      else []
  startRules ++ lexRules ++ merge1Rules G profs ++ merge2Rules profs ++ merge3Rules G profs ++
    move1Rules ++ move2Rules

/-! ### Part 6: Proof That Every Built Rule Is Linear & Non-Erasing (`WellFormed`) -/

theorem countP_map_none {α β : Type} (L : List α) :
    (L.map fun _ => (none : Option β)).countP Option.isSome = 0 := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem ntDim_none {Base Lic : Type} (b : Bool) (α : List (MGFeature Base Lic)) (L : List Lic) :
    ntDim (MGMCFGNT.prof b α (L.map fun _ => none)) = 1 := by
  simp only [ntDim, countP_map_none]

theorem evalComp_map_tm (args : List (List (List T))) (w : List T) :
    MCFG.evalComp args (w.map MCFGAtom.tm) = w := by
  induction w with
  | nil => rfl
  | cons a t ih => simp [MCFG.evalComp, ih]

theorem varOccurrences_cons_comp {N : Type} (lhs : N) (rhs : List N)
    (c0 : List (MCFGAtom T)) (cs : List (List (MCFGAtom T))) :
    MCFGRule.varOccurrences { lhs := lhs, rhs := rhs, yield := c0 :: cs } =
      (c0.filterMap fun | MCFGAtom.tm _ => none | MCFGAtom.var i j => some (i, j)) ++
      compsVars cs := rfl

theorem range_vars1_props (base len : Nat) :
    let vs : List (List (MCFGAtom T)) := (List.range len).map fun k => [MCFGAtom.var 1 (base + k)]
    vs.length = len ∧
    (compsVars vs).Nodup ∧
    (∀ i j, (i, j) ∈ compsVars vs ↔ i = 1 ∧ base ≤ j ∧ j < base + len) := by
  induction len generalizing base with
  | zero =>
    refine ⟨rfl, List.nodup_nil, ?_⟩
    intro i j; simp [compsVars]
  | succ len ih =>
    have hr : List.range (len + 1) = 0 :: (List.range len).map Nat.succ :=
      List.range_succ_eq_map (n := len)
    obtain ⟨hlen, hnd, hmem⟩ := ih (base + 1)
    have hmap : ((List.range (len + 1)).map fun k => [MCFGAtom.var (T := T) 1 (base + k)]) =
        [MCFGAtom.var 1 base] :: ((List.range len).map fun k => [MCFGAtom.var 1 (base + 1 + k)]) := by
      rw [hr, List.map_cons, List.map_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro k _
      have hidx : base + k.succ = base + 1 + k := by omega
      simp [Function.comp, hidx]
    simp only [hmap]
    refine ⟨by simp [hlen], ?_, ?_⟩
    · rw [compsVars_cons_var, List.nodup_cons]
      refine ⟨?_, hnd⟩
      intro hbad; have := (hmem 1 base).mp hbad; omega
    · intro i j
      rw [compsVars_cons_var, List.mem_cons, Prod.mk.injEq, hmem i j]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, hlo, hhi⟩) <;> refine ⟨rfl, ?_, ?_⟩ <;> omega
      · rintro ⟨rfl, hlo, hhi⟩
        by_cases hj : j = base
        · left; exact ⟨rfl, hj⟩
        · right; refine ⟨rfl, ?_, ?_⟩ <;> omega

private theorem merge1Rules_wellFormed [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {r : MCFGRule (MGMCFGNT Base Lic) T}
    (hM1 : r ∈ merge1Rules G (allProfiles G)) : r.WellFormed ntDim := by
  simp only [merge1Rules, List.mem_flatMap] at hM1
  obtain ⟨⟨b1, α1, s1⟩, _, h1⟩ := hM1
  dsimp only at h1
  split at h1
  · next hcond =>
    cases α1 with
    | nil => simp at h1
    | cons hd γ =>
      cases hd with
      | sel x =>
        simp only [List.mem_filterMap] at h1
        obtain ⟨⟨b2, α2, s2⟩, _, h2⟩ := h1
        dsimp only at h2
        split at h2
        · simp at h2; subst h2
          obtain ⟨hlen, hnd, hmem⟩ := range_vars1_props (T := T) 1 (s2.countP Option.isSome)
          refine ⟨by simp [ntDim, hlen]; omega, ?_, ?_⟩
          · unfold MCFGRule.isLinear
            rw [varOccurrences_cons_comp]
            simp only [List.filterMap_cons, List.filterMap_nil, List.cons_append, List.nil_append,
              List.nodup_cons]
            refine ⟨?_, ?_, hnd⟩
            · intro hm; rcases List.mem_cons.mp hm with heq | hm'
              · simp at heq
              · have := (hmem 0 0).mp hm'; omega
            · intro hm'; have := (hmem 1 0).mp hm'; omega
          · intro i j
            rw [varOccurrences_cons_comp]
            simp only [List.filterMap_cons, List.filterMap_nil, List.cons_append, List.nil_append,
              List.mem_cons, Prod.mk.injEq]
            rw [hmem i j]
            constructor
            · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hlo, hhi⟩)
              · exact ⟨_, rfl, by simp [ntDim_none]⟩
              · exact ⟨_, rfl, by simp [ntDim]; omega⟩
              · exact ⟨_, rfl, by simp [ntDim]; omega⟩
            · rintro ⟨B, hget, hj⟩
              cases i with
              | zero =>
                simp at hget; subst hget
                rw [ntDim_none] at hj
                left; exact ⟨rfl, by omega⟩
              | succ i' =>
                cases i' with
                | zero =>
                  simp at hget; subst hget
                  simp [ntDim] at hj
                  by_cases hj0 : j = 0
                  · right; left; exact ⟨rfl, hj0⟩
                  · right; right; refine ⟨rfl, ?_, ?_⟩ <;> omega
                | succ _ => simp at hget
        · simp at h2
      | _ => simp at h1
  · simp at h1

private theorem merge2Rules_wellFormed [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {r : MCFGRule (MGMCFGNT Base Lic) T}
    (hM2 : r ∈ merge2Rules (allProfiles G)) : r.WellFormed ntDim := by
  simp only [merge2Rules, List.mem_flatMap] at hM2
  obtain ⟨⟨b1, α1, s1⟩, _, h1⟩ := hM2
  dsimp only at h1
  split at h1
  · cases α1 with
    | nil => simp at h1
    | cons hd γ =>
      cases hd with
      | sel x =>
        simp only [List.mem_filterMap] at h1
        obtain ⟨⟨b2, α2, s2⟩, _, h2⟩ := h1
        dsimp only at h2
        split at h2
        · cases hm : mergeSlots s1 s2 with
          | none => simp [hm] at h2
          | some s12 =>
            simp [hm] at h2; subst h2
            obtain ⟨hlen, hnd, hmem⟩ := mergeVars_props (T := T) hm 1 1
            refine ⟨by simp [ntDim, hlen]; omega, ?_, ?_⟩
            · unfold MCFGRule.isLinear
              rw [varOccurrences_cons_comp]
              simp only [List.filterMap_cons, List.filterMap_nil, List.cons_append, List.nil_append,
                List.nodup_cons]
              refine ⟨?_, ?_, hnd⟩
              · intro hm'; rcases List.mem_cons.mp hm' with heq | hmv
                · simp at heq
                · have := (hmem 1 0).mp hmv; omega
              · intro hmv; have := (hmem 0 0).mp hmv; omega
            · intro i j
              rw [varOccurrences_cons_comp]
              simp only [List.filterMap_cons, List.filterMap_nil, List.cons_append, List.nil_append,
                List.mem_cons, Prod.mk.injEq]
              rw [hmem i j]
              constructor
              · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩)
                · exact ⟨_, rfl, by simp [ntDim]; omega⟩
                · exact ⟨_, rfl, by simp [ntDim]; omega⟩
                · exact ⟨_, rfl, by simp [ntDim]; omega⟩
                · exact ⟨_, rfl, by simp [ntDim]; omega⟩
              · rintro ⟨B, hget, hj⟩
                cases i with
                | zero =>
                  simp at hget; subst hget; simp [ntDim] at hj
                  by_cases hj0 : j = 0
                  · right; left; exact ⟨rfl, hj0⟩
                  · right; right; left; refine ⟨rfl, ?_, ?_⟩ <;> omega
                | succ i' =>
                  cases i' with
                  | zero =>
                    simp at hget; subst hget; simp [ntDim] at hj
                    by_cases hj0 : j = 0
                    · left; exact ⟨rfl, hj0⟩
                    · right; right; right; refine ⟨rfl, ?_, ?_⟩ <;> omega
                  | succ _ => simp at hget
        · simp at h2
      | _ => simp at h1
  · simp at h1

private theorem merge3Rules_wellFormed [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {r : MCFGRule (MGMCFGNT Base Lic) T}
    (hM3 : r ∈ merge3Rules G (allProfiles G)) : r.WellFormed ntDim := by
  simp only [merge3Rules, List.mem_flatMap] at hM3
  obtain ⟨⟨b1, α1, s1⟩, _, h1⟩ := hM3
  dsimp only at h1
  cases α1 with
  | nil => simp at h1
  | cons hd γ =>
    cases hd with
    | sel x =>
      simp only [List.mem_filterMap] at h1
      obtain ⟨⟨b2, α2, s2⟩, _, h2⟩ := h1
      dsimp only at h2
      cases α2 with
      | nil => simp at h2
      | cons hd2 tl2 =>
        cases hd2 with
        | cat x' =>
          cases tl2 with
          | nil => simp at h2
          | cons hd3 δ' =>
            cases hd3 with
            | licensee f =>
              dsimp only at h2
              split at h2
              · next hx =>
                subst hx
                cases hm : mergeSlots s1 s2 with
                | none => simp [hm] at h2
                | some s12 =>
                  rw [hm] at h2
                  cases hi : insertSlot f (MGFeature.licensee f :: δ') (allLics G) s12 with
                  | none => simp [hi] at h2
                  | some s3 =>
                    simp [hi] at h2; subst h2
                    obtain ⟨hlen, hnd, hmem⟩ := merge3Vars_props (T := T) hm hi 1 1 (Nat.le_refl 1)
                    refine ⟨by simp [ntDim, hlen]; omega, ?_, ?_⟩
                    · unfold MCFGRule.isLinear
                      rw [varOccurrences_cons_comp]
                      simp only [List.filterMap_cons, List.filterMap_nil, List.cons_append,
                        List.nil_append, List.nodup_cons]
                      refine ⟨?_, hnd⟩
                      intro hmv; have := (hmem 0 0).mp hmv; omega
                    · intro i j
                      rw [varOccurrences_cons_comp]
                      simp only [List.filterMap_cons, List.filterMap_nil, List.cons_append,
                        List.nil_append, List.mem_cons, Prod.mk.injEq]
                      rw [hmem i j]
                      constructor
                      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩)
                        · exact ⟨_, rfl, by simp [ntDim]; omega⟩
                        · exact ⟨_, rfl, by simp [ntDim]; omega⟩
                        · exact ⟨_, rfl, by simp [ntDim]; omega⟩
                        · exact ⟨_, rfl, by simp [ntDim]; omega⟩
                      · rintro ⟨B, hget, hj⟩
                        cases i with
                        | zero =>
                          simp at hget; subst hget; simp [ntDim] at hj
                          by_cases hj0 : j = 0
                          · left; exact ⟨rfl, hj0⟩
                          · right; right; left; refine ⟨rfl, ?_, ?_⟩ <;> omega
                        | succ i' =>
                          cases i' with
                          | zero =>
                            simp at hget; subst hget; simp [ntDim] at hj
                            by_cases hj0 : j = 0
                            · right; left; exact ⟨rfl, hj0⟩
                            · right; right; right; refine ⟨rfl, ?_, ?_⟩ <;> omega
                          | succ _ => simp at hget
              · simp at h2
            | _ => simp at h2
        | _ => simp at h2
    | _ => simp at h1

theorem buildRules_wf [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T) :
    ∀ r, r ∈ buildRules G → r.WellFormed ntDim := by
  intro r hr
  unfold buildRules at hr
  simp only [List.mem_append] at hr
  rcases hr with (((((hStart | hLex) | hM1) | hM2) | hM3) | hV1) | hV2
  · -- Start rules
    simp only [List.mem_map] at hStart
    obtain ⟨b, _, rfl⟩ := hStart
    refine ⟨rfl, ?_, ?_⟩
    · simp [MCFGRule.isLinear, MCFGRule.varOccurrences]
    · intro i j
      simp only [MCFGRule.varOccurrences, List.flatMap_cons, List.flatMap_nil,
        List.filterMap_cons, List.filterMap_nil, List.append_nil, List.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨_, rfl, by simp [ntDim_none]⟩
      · rintro ⟨B, hget, hj⟩
        cases i with
        | zero =>
          simp at hget; subst hget
          rw [ntDim_none] at hj
          exact ⟨rfl, by omega⟩
        | succ _ => simp at hget
  · -- Lex rules
    simp only [List.mem_map] at hLex
    obtain ⟨⟨w, α⟩, _, rfl⟩ := hLex
    have hvars : MCFGRule.varOccurrences
        ({ lhs := MGMCFGNT.prof true α ((allLics G).map fun _ => none),
           rhs := [], yield := [w.map MCFGAtom.tm] } : MCFGRule (MGMCFGNT Base Lic) T) = [] := by
      simp only [MCFGRule.varOccurrences, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      induction w with
      | nil => rfl
      | cons a t _ => simp
    refine ⟨by simp [ntDim_none], ?_, ?_⟩
    · simp [MCFGRule.isLinear, hvars]
    · intro i j
      simp [hvars]
  · -- Merge 1 rules
    exact merge1Rules_wellFormed hM1
  · -- Merge 2 rules
    exact merge2Rules_wellFormed hM2
  · -- Merge 3 rules
    exact merge3Rules_wellFormed hM3
  · -- Move 1 rules
    simp only [List.mem_filterMap] at hV1
    obtain ⟨⟨b, α, s⟩, _, h1⟩ := hV1
    dsimp only at h1
    split at h1
    · cases α with
      | nil => simp at h1
      | cons hd γ =>
        cases hd with
        | licensor f =>
          cases hcl : clearSlot (T := T) f 1 (allLics G) s with
          | none => simp [hcl] at h1
          | some triple =>
            obtain ⟨p, s', vs⟩ := triple
            simp [hcl] at h1; subst h1
            obtain ⟨hge, hlt, hlen, hnd, hmem⟩ := clearSlot_props (T := T) hcl
            refine ⟨by simp [ntDim, hlen]; omega, ?_, ?_⟩
            · unfold MCFGRule.isLinear
              rw [varOccurrences_cons_comp]
              simp only [List.filterMap_cons, List.filterMap_nil, List.cons_append, List.nil_append,
                List.nodup_cons]
              refine ⟨?_, ?_, hnd⟩
              · intro hm; rcases List.mem_cons.mp hm with heq | hmv
                · simp at heq; omega
                · have := (hmem 0 p).mp hmv; omega
              · intro hmv; have := (hmem 0 0).mp hmv; omega
            · intro i j
              rw [varOccurrences_cons_comp]
              simp only [List.filterMap_cons, List.filterMap_nil, List.cons_append, List.nil_append,
                List.mem_cons, Prod.mk.injEq]
              rw [hmem i j]
              constructor
              · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hlo, hhi, _⟩)
                · exact ⟨_, rfl, by simp [ntDim]; omega⟩
                · exact ⟨_, rfl, by simp [ntDim]; omega⟩
                · exact ⟨_, rfl, by simp [ntDim]; omega⟩
              · rintro ⟨B, hget, hj⟩
                cases i with
                | zero =>
                  simp at hget; subst hget; simp [ntDim] at hj
                  by_cases hj0 : j = 0
                  · right; left; exact ⟨rfl, hj0⟩
                  · by_cases hjp : j = p
                    · left; exact ⟨rfl, hjp⟩
                    · right; right; refine ⟨rfl, ?_, ?_, hjp⟩ <;> omega
                | succ _ => simp at hget
        | _ => simp at h1
    · simp at h1
  · -- Move 2 rules
    simp only [List.mem_flatMap] at hV2
    obtain ⟨⟨b, α, s⟩, _, h1⟩ := hV2
    dsimp only at h1
    split at h1
    · cases α with
      | nil => simp at h1
      | cons hd γ =>
        cases hd with
        | licensor f =>
          simp only [List.mem_flatMap, List.mem_filterMap] at h1
          obtain ⟨f', _, δ, _, h2⟩ := h1
          cases hrel : relocateSlot (T := T) f f' δ (allLics G) s with
          | none => simp [hrel] at h2
          | some pr =>
            obtain ⟨s', vs⟩ := pr
            simp [hrel] at h2; subst h2
            obtain ⟨hlen, hnd, hmem⟩ := relocateSlot_props (T := T) (nodup_allLics G) hrel
            refine ⟨by simp [ntDim, hlen]; omega, ?_, ?_⟩
            · unfold MCFGRule.isLinear
              rw [varOccurrences_cons_comp]
              simp only [List.filterMap_cons, List.filterMap_nil, List.cons_append, List.nil_append,
                List.nodup_cons]
              refine ⟨?_, hnd⟩
              intro hmv; have := (hmem 0 0).mp hmv; omega
            · intro i j
              rw [varOccurrences_cons_comp]
              simp only [List.filterMap_cons, List.filterMap_nil, List.cons_append, List.nil_append,
                List.mem_cons, Prod.mk.injEq]
              rw [hmem i j]
              constructor
              · rintro (⟨rfl, rfl⟩ | ⟨rfl, hlo, hhi⟩)
                · exact ⟨_, rfl, by simp [ntDim]; omega⟩
                · exact ⟨_, rfl, by simp [ntDim]; omega⟩
              · rintro ⟨B, hget, hj⟩
                cases i with
                | zero =>
                  simp at hget; subst hget; simp [ntDim] at hj
                  by_cases hj0 : j = 0
                  · left; exact ⟨rfl, hj0⟩
                  · right; refine ⟨rfl, ?_, ?_⟩ <;> omega
                | succ _ => simp at hget
        | _ => simp at h1
    · simp at h1

/-- The Linear Non-Erasing MCFG (LCFRS) equivalent to Minimalist Grammar `G`. -/
def mgToMCFG [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T) :
    MCFG (MGMCFGNT Base Lic) T where
  start := MGMCFGNT.start
  dim := ntDim
  dim_pos := ntDim_pos
  dim_start := rfl
  rules := buildRules G
  rules_wf := buildRules_wf G

/-! ### Part 7: Soundness & Completeness (`MG.Lang ↔ MCFG.Lang`) -/

/-- Semantic interpretation of an `MGMCFGNT` tuple back in `MG.Derives G`. -/
def ntInterp [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T) :
    MGMCFGNT Base Lic → List (List T) → Prop
  | MGMCFGNT.start, tup => ∃ w, tup = [w] ∧ G.Lang w
  | MGMCFGNT.prof b α slots, tup =>
      ∃ s ms, tup = s :: strsOf (allLics G) ms ∧
        slotsOf (allLics G) ms = slots ∧
        MG.Derives G ⟨b, ⟨s, α⟩, ms⟩

/-- Helper list-level predicate for mutual structural recursion on `MCFG.Yield` / `MCFG.YieldList`. -/
inductive InterpList [DecidableEq Base] [DecidableEq Lic] (G : MG Base Lic T) :
    List (MGMCFGNT Base Lic) → List (List (List T)) → Prop where
  | nil : InterpList G [] []
  | cons {A : MGMCFGNT Base Lic} {As : List (MGMCFGNT Base Lic)}
      {tup : List (List T)} {tups : List (List (List T))} :
      ntInterp G A tup → InterpList G As tups → InterpList G (A :: As) (tup :: tups)

theorem movers_in_allLics [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {e : MGExpr Base Lic T} (h : MG.Derives G e) :
    ∀ c, c ∈ e.movers → ∀ f, c.headLic = some f → f ∈ allLics G := by
  intro c hc f hlic
  obtain ⟨entry, hentry, hsuf⟩ := h.feats_suffix.2 c hc
  cases hcf : c.feats with
  | nil => simp [MGChain.headLic, hcf] at hlic
  | cons hd tl =>
    cases hd with
    | licensee f' =>
      simp [MGChain.headLic, hcf] at hlic; subst hlic
      rw [hcf] at hsuf
      exact mem_allLics_of_suffix hentry hsuf
    | _ => simp [MGChain.headLic, hcf] at hlic

private theorem merge1Rules_sound [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {r : MCFGRule (MGMCFGNT Base Lic) T}
    {args : List (List (List T))} (hM1 : r ∈ merge1Rules G (allProfiles G))
    (hargs : InterpList G r.rhs args) : ntInterp G r.lhs (MCFG.evalYield args r.yield) := by
  simp only [merge1Rules, List.mem_flatMap] at hM1
  obtain ⟨⟨b1, α1, s1⟩, _, h1⟩ := hM1
  dsimp only at h1
  split at h1
  · cases α1 with
    | nil => simp at h1
    | cons hd γ =>
      cases hd with
      | sel x =>
        simp only [List.mem_filterMap] at h1
        obtain ⟨⟨b2, α2, s2⟩, _, h2⟩ := h1
        dsimp only at h2
        split at h2
        · simp at h2; subst h2
          cases hargs with
          | cons hi1 hrest =>
            cases hrest with
            | cons hi2 hnil =>
              cases hnil
              obtain ⟨s, ms1, rfl, hslots1, hder1⟩ := hi1
              obtain ⟨t, ms2, rfl, hslots2, hder2⟩ := hi2
              have hms1 : ms1 = [] :=
                movers_nil_of_slotsOf_all_none hder1.smc (movers_in_allLics hder1) hslots1
              subst hms1
              refine ⟨s ++ t, ms2, ?_, hslots2, MG.Derives.merge1 hder1 hder2⟩
              simp only [MCFG.evalYield, List.map_cons]
              have hhead : MCFG.evalComp [s :: strsOf (allLics G) ([] : List (MGChain Base Lic T)), t :: strsOf (allLics G) ms2]
                  [MCFGAtom.var 0 0, MCFGAtom.var 1 0] = s ++ t := by
                simp [MCFG.evalComp]
              rw [hhead]
              congr 1
              rw [← hslots2, ← strsOf_length (allLics G) ms2]
              exact evalYield_range_vars1 (s :: strsOf (allLics G) ([] : List (MGChain Base Lic T)))
                [t] (strsOf (allLics G) ms2)
        · simp at h2
      | _ => simp at h1
  · simp at h1

private theorem merge2Rules_sound [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {r : MCFGRule (MGMCFGNT Base Lic) T}
    {args : List (List (List T))} (hM2 : r ∈ merge2Rules (allProfiles G))
    (hargs : InterpList G r.rhs args) : ntInterp G r.lhs (MCFG.evalYield args r.yield) := by
  simp only [merge2Rules, List.mem_flatMap] at hM2
  obtain ⟨⟨b1, α1, s1⟩, _, h1⟩ := hM2
  dsimp only at h1
  split at h1
  · cases α1 with
    | nil => simp at h1
    | cons hd γ =>
      cases hd with
      | sel x =>
        simp only [List.mem_filterMap] at h1
        obtain ⟨⟨b2, α2, s2⟩, _, h2⟩ := h1
        dsimp only at h2
        split at h2
        · cases hm : mergeSlots s1 s2 with
          | none => simp [hm] at h2
          | some s12 =>
            simp [hm] at h2; subst h2
            cases hargs with
            | cons hi1 hrest =>
              cases hrest with
              | cons hi2 hnil =>
                cases hnil
                obtain ⟨s, ms1, rfl, hslots1, hder1⟩ := hi1
                obtain ⟨t, ms2, rfl, hslots2, hder2⟩ := hi2
                rw [← hslots1, ← hslots2] at hm
                have hsmc12 : SMC (ms1 ++ ms2) :=
                  smc_append_of_mergeSlots hder1.smc hder2.smc (movers_in_allLics hder1) hm
                obtain ⟨hm', heval⟩ :=
                  evalYield_mergeVars (allLics G) hder1.smc hder2.smc hsmc12
                have hs12_eq : slotsOf (allLics G) (ms1 ++ ms2) = s12 := by
                  rw [hm] at hm'; simp at hm'; exact hm'.symm
                refine ⟨t ++ s, ms1 ++ ms2, ?_, hs12_eq, MG.Derives.merge2 hder1 hder2 hsmc12⟩
                simp only [MCFG.evalYield, List.map_cons]
                have hhead : MCFG.evalComp [s :: strsOf (allLics G) ms1, t :: strsOf (allLics G) ms2]
                    [MCFGAtom.var 1 0, MCFGAtom.var 0 0] = t ++ s := by simp [MCFG.evalComp]
                rw [hhead, ← hslots1, ← hslots2]
                exact congrArg ((t ++ s) :: ·) (heval [s] [t])
        · simp at h2
      | _ => simp at h1
  · simp at h1

private theorem merge3Rules_sound [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {r : MCFGRule (MGMCFGNT Base Lic) T}
    {args : List (List (List T))} (hM3 : r ∈ merge3Rules G (allProfiles G))
    (hargs : InterpList G r.rhs args) : ntInterp G r.lhs (MCFG.evalYield args r.yield) := by
  simp only [merge3Rules, List.mem_flatMap] at hM3
  obtain ⟨⟨b1, α1, s1⟩, _, h1⟩ := hM3
  dsimp only at h1
  cases α1 with
  | nil => simp at h1
  | cons hd γ =>
    cases hd with
    | sel x =>
      simp only [List.mem_filterMap] at h1
      obtain ⟨⟨b2, α2, s2⟩, _, h2⟩ := h1
      dsimp only at h2
      cases α2 with
      | nil => simp at h2
      | cons hd2 tl2 =>
        cases hd2 with
        | cat x' =>
          cases tl2 with
          | nil => simp at h2
          | cons hd3 δ' =>
            cases hd3 with
            | licensee f =>
              dsimp only at h2
              split at h2
              · next hx =>
                subst hx
                cases hm : mergeSlots s1 s2 with
                | none => simp [hm] at h2
                | some s12 =>
                  rw [hm] at h2
                  cases hi : insertSlot f (MGFeature.licensee f :: δ') (allLics G) s12 with
                  | none => simp [hi] at h2
                  | some s3 =>
                    simp [hi] at h2; subst h2
                    cases hargs with
                    | cons hi1 hrest =>
                      cases hrest with
                      | cons hi2 hnil =>
                        cases hnil
                        obtain ⟨s, ms1, rfl, hslots1, hder1⟩ := hi1
                        obtain ⟨t, ms2, rfl, hslots2, hder2⟩ := hi2
                        rw [← hslots1, ← hslots2] at hm
                        have hsmc12 : SMC (ms1 ++ ms2) :=
                          smc_append_of_mergeSlots hder1.smc hder2.smc (movers_in_allLics hder1) hm
                        obtain ⟨hm', _⟩ :=
                          evalYield_mergeVars (allLics G) hder1.smc hder2.smc hsmc12
                        have hs12_eq : slotsOf (allLics G) (ms1 ++ ms2) = s12 := by
                          rw [hm] at hm'; simp at hm'; exact hm'.symm
                        rw [← hs12_eq] at hi
                        have hnotf := not_mem_headLic_of_insertSlot hsmc12 hi
                        have hsmc3 : SMC (ms1 ++ ⟨t, MGFeature.licensee f :: δ'⟩ :: ms2) := by
                          refine ⟨?_, ?_⟩
                          · intro c hc
                            rcases List.mem_append.mp hc with h1' | h2'
                            · exact hder1.smc.1 c h1'
                            · rcases List.mem_cons.mp h2' with rfl | h2''
                              · exact ⟨f, δ', rfl⟩
                              · exact hder2.smc.1 c h2''
                          · have hnd := hsmc12.2
                            rw [List.filterMap_append, List.nodup_append] at hnd
                            simp only [List.filterMap_append, List.filterMap_cons]
                            change ((ms1.filterMap MGChain.headLic) ++ f :: (ms2.filterMap MGChain.headLic)).Nodup
                            rw [List.nodup_append, List.nodup_cons]
                            refine ⟨hnd.1, ⟨?_, hnd.2.1⟩, ?_⟩
                            · intro hmem2
                              obtain ⟨c, hc2, hlic⟩ := List.mem_filterMap.mp hmem2
                              exact hnotf c (List.mem_append_right _ hc2) hlic
                            · intro a ha b hb
                              rcases List.mem_cons.mp hb with rfl | hb2
                              · intro heq; subst heq
                                obtain ⟨c, hc1, hlic⟩ := List.mem_filterMap.mp ha
                                exact hnotf c (List.mem_append_left _ hc1) hlic
                              · exact hnd.2.2 a ha b hb2
                        have hfL : f ∈ allLics G := by
                          obtain ⟨entry, hentry, hsuf⟩ := hder2.feats_suffix.1
                          exact mem_allLics_of_suffix hentry (MG.isSuffix_tail hsuf)
                        obtain ⟨hi', heval⟩ :=
                          evalYield_merge3Vars (allLics G) (nodup_allLics G) hfL hder1.smc hder2.smc hsmc3
                        have hs3_eq : slotsOf (allLics G) (ms1 ++ ⟨t, MGFeature.licensee f :: δ'⟩ :: ms2) = s3 := by
                          rw [hi] at hi'; simp at hi'; exact hi'.symm
                        refine ⟨s, ms1 ++ ⟨t, MGFeature.licensee f :: δ'⟩ :: ms2, ?_, hs3_eq,
                          MG.Derives.merge3 hder1 hder2 hsmc3⟩
                        simp only [MCFG.evalYield, List.map_cons]
                        have hhead : MCFG.evalComp [s :: strsOf (allLics G) ms1, t :: strsOf (allLics G) ms2]
                            [MCFGAtom.var 0 0] = s := by simp [MCFG.evalComp]
                        rw [hhead, ← hslots1, ← hslots2]
                        exact congrArg (s :: ·) (heval [s] [t] rfl)
              · simp at h2
            | _ => simp at h2
        | _ => simp at h2
    | _ => simp at h1

mutual
  theorem mgToMCFG_sound [DecidableEq Base] [DecidableEq Lic]
      {G : MG Base Lic T} {A : MGMCFGNT Base Lic} {tup : List (List T)} :
      MCFG.Yield (mgToMCFG G) A tup → ntInterp G A tup
    | MCFG.Yield.rule hr hargs_raw => by
      have hargs := mgToMCFG_sound_list hargs_raw
      change _ ∈ buildRules G at hr
      unfold buildRules at hr
      simp only [List.mem_append] at hr
      rcases hr with (((((hStart | hLex) | hM1) | hM2) | hM3) | hV1) | hV2
      · -- Start rules
        simp only [List.mem_map] at hStart
        obtain ⟨b, _, rfl⟩ := hStart
        cases hargs with
        | cons hi1 hnil =>
          cases hnil
          obtain ⟨s, ms, rfl, hslots, hder⟩ := hi1
          have hms : ms = [] :=
            movers_nil_of_slotsOf_all_none hder.smc (movers_in_allLics hder) hslots
          subst hms
          exact ⟨s, by simp [MCFG.evalYield, MCFG.evalComp], b, hder⟩
      · -- Lex rules
        simp only [List.mem_map] at hLex
        obtain ⟨⟨w, α⟩, hlex, rfl⟩ := hLex
        cases hargs
        refine ⟨w, [], ?_, slotsOf_nil (allLics G), MG.Derives.lex hlex⟩
        simp [MCFG.evalYield, evalComp_map_tm, strsOf_nil]
      · -- Merge 1 rules
        exact merge1Rules_sound hM1 hargs
      · -- Merge 2 rules
        exact merge2Rules_sound hM2 hargs
      · -- Merge 3 rules
        exact merge3Rules_sound hM3 hargs
      · -- Move 1 rules
        simp only [List.mem_filterMap] at hV1
        obtain ⟨⟨b, α, s⟩, _, h1⟩ := hV1
        dsimp only at h1
        split at h1
        · cases α with
          | nil => simp at h1
          | cons hd γ =>
            cases hd with
            | licensor f =>
              cases hcl : clearSlot (T := T) f 1 (allLics G) s with
              | none => simp [hcl] at h1
              | some triple =>
                obtain ⟨p, s', vs⟩ := triple
                simp [hcl] at h1; subst h1
                cases hargs with
                | cons hi1 hnil =>
                  cases hnil
                  obtain ⟨sHead, ms, rfl, hslots, hder⟩ := hi1
                  rw [← hslots] at hcl
                  obtain ⟨tStr, ms1, ms2, hms_eq, hslots', hget, heval⟩ :=
                    clearSlot_eval_and_mem (allLics G) (nodup_allLics G) hder.smc [sHead] hcl
                  dsimp only at hms_eq hget heval
                  simp only [List.singleton_append] at hget heval
                  rw [hms_eq] at hder
                  refine ⟨tStr ++ sHead, ms1 ++ ms2, ?_, hslots', MG.Derives.move1 hder⟩
                  simp only [MCFG.evalYield, List.map_cons]
                  have hhead : MCFG.evalComp [sHead :: strsOf (allLics G) ms]
                      [MCFGAtom.var 0 p, MCFGAtom.var 0 0] = tStr ++ sHead := by
                    simp [MCFG.evalComp, hget]
                  rw [hhead]
                  exact congrArg ((tStr ++ sHead) :: ·) heval
            | _ => simp at h1
        · simp at h1
      · -- Move 2 rules
        simp only [List.mem_flatMap] at hV2
        obtain ⟨⟨b, α, s⟩, _, h1⟩ := hV2
        dsimp only at h1
        split at h1
        · cases α with
          | nil => simp at h1
          | cons hd γ =>
            cases hd with
            | licensor f =>
              simp only [List.mem_flatMap, List.mem_filterMap] at h1
              obtain ⟨f', _, δ, hδ, h2⟩ := h1
              cases hrel : relocateSlot (T := T) f f' δ (allLics G) s with
              | none => simp [hrel] at h2
              | some pr =>
                obtain ⟨s', vs⟩ := pr
                simp [hrel] at h2; subst h2
                obtain ⟨_, δ', rfl⟩ := mem_licFeats_iff.mp hδ
                cases hargs with
                | cons hi1 hnil =>
                  cases hnil
                  obtain ⟨sHead, ms, rfl, hslots, hder⟩ := hi1
                  rw [← hslots] at hrel
                  obtain ⟨tStr, ms1, ms2, hms_eq, hsmcNew, hslots', heval⟩ :=
                    relocateSlot_eval_and_mem (allLics G) (nodup_allLics G) hder.smc
                      (movers_in_allLics hder) sHead hrel
                  dsimp only at hms_eq heval
                  rw [hms_eq] at hder
                  refine ⟨sHead, ms1 ++ ⟨tStr, MGFeature.licensee f' :: δ'⟩ :: ms2,
                    ?_, hslots', MG.Derives.move2 hder hsmcNew⟩
                  simp only [MCFG.evalYield, List.map_cons]
                  have hhead : MCFG.evalComp [sHead :: strsOf (allLics G) ms]
                      [MCFGAtom.var 0 0] = sHead := by simp [MCFG.evalComp]
                  rw [hhead]
                  exact congrArg (sHead :: ·) heval
            | _ => simp at h1
        · simp at h1

  theorem mgToMCFG_sound_list [DecidableEq Base] [DecidableEq Lic]
      {G : MG Base Lic T} {As : List (MGMCFGNT Base Lic)} {args : List (List (List T))} :
      MCFG.YieldList (mgToMCFG G) As args → InterpList G As args
    | MCFG.YieldList.nil => InterpList.nil
    | MCFG.YieldList.cons hy hrest =>
      InterpList.cons (mgToMCFG_sound hy) (mgToMCFG_sound_list hrest)
end

private theorem split_at_unique_chain {c : MGChain Base Lic T} {f : Lic}
    {left right left' right' : List (MGChain Base Lic T)} (head : c.headLic = some f)
    (shortestMove : SMC (left ++ c :: right))
    (split : left ++ c :: right = left' ++ c :: right') :
    left = left' ∧ right = right' := by
  have not_in_left {a b : List (MGChain Base Lic T)} (smc : SMC (a ++ c :: b)) : c ∉ a := by
    intro mem
    have unique := smc.2
    simp only [List.filterMap_append, List.filterMap_cons, head, List.nodup_append,
      List.nodup_cons] at unique
    exact unique.2.2 f (List.mem_filterMap.mpr ⟨c, mem, head⟩)
      f (List.mem_cons_self ..) rfl
  have leftExcludes := not_in_left shortestMove
  have rightExcludes := not_in_left (split ▸ shortestMove)
  rcases List.append_eq_append_iff.mp split with ⟨middle, hprefix, hsuffix⟩ |
    ⟨middle, hprefix, hsuffix⟩
  · cases middle with
    | nil => simp at hprefix hsuffix; exact ⟨hprefix.symm, hsuffix⟩
    | cons first rest =>
      have first_eq : c = first := (List.cons.inj hsuffix).1
      subst first
      apply (rightExcludes ?_).elim
      rw [hprefix]
      exact List.mem_append_right _ (List.mem_cons_self ..)
  · cases middle with
    | nil => simp at hprefix hsuffix; exact ⟨hprefix, hsuffix.symm⟩
    | cons first rest =>
      have first_eq : c = first := (List.cons.inj hsuffix).1
      subst first
      apply (leftExcludes ?_).elim
      rw [hprefix]
      exact List.mem_append_right _ (List.mem_cons_self ..)

private theorem mgToMCFG_move1_complete [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {s t : List T}
    {f : Lic} {γ : List (MGFeature Base Lic)} {ms1 ms2 : List (MGChain Base Lic T)}
    (h1 : G.Derives ⟨false, ⟨s, MGFeature.licensor f :: γ⟩, ms1 ++ ⟨t, [MGFeature.licensee f]⟩ :: ms2⟩)
    (ih1 : (mgToMCFG G).Yield
      (MGMCFGNT.prof false (MGFeature.licensor f :: γ)
        (slotsOf (allLics G) (ms1 ++ ⟨t, [MGFeature.licensee f]⟩ :: ms2)))
      (s :: strsOf (allLics G) (ms1 ++ ⟨t, [MGFeature.licensee f]⟩ :: ms2))) :
    (mgToMCFG G).Yield (MGMCFGNT.prof false γ (slotsOf (allLics G) (ms1 ++ ms2)))
      ((t ++ s) :: strsOf (allLics G) (ms1 ++ ms2)) := by
  have hp1 := mem_allProfiles_of_derives h1
  have hfL : f ∈ allLics G :=
    movers_in_allLics h1 ⟨t, [MGFeature.licensee f]⟩
      (List.mem_append_right _ (List.mem_cons_self ..)) f rfl
  obtain ⟨p, s', vs, hcl⟩ := clearSlot_complete (T := T) (allLics G) hfL h1.smc 1
  obtain ⟨t', ms1', ms2', hms_eq, hslots', hget, heval⟩ :=
    clearSlot_eval_and_mem (allLics G) (nodup_allLics G) h1.smc [s] hcl
  dsimp only at hms_eq hget heval
  simp only [List.singleton_append] at hget heval
  -- Uniqueness of the mover with headLic = some f forces t' = t and same slots/strs!
  have ht_eq : t' = t := by
    have hc1 : ⟨t, [MGFeature.licensee f]⟩ ∈ ms1 ++ ⟨t, [MGFeature.licensee f]⟩ :: ms2 :=
      List.mem_append_right _ (List.mem_cons_self ..)
    have hc2 : ⟨t', [MGFeature.licensee f]⟩ ∈ ms1 ++ ⟨t, [MGFeature.licensee f]⟩ :: ms2 := by
      rw [hms_eq]; exact List.mem_append_right _ (List.mem_cons_self ..)
    have hceq := smc_unique_chain h1.smc hc2 rfl hc1 rfl
    simpa using congrArg MGChain.str hceq
  subst t'
  obtain ⟨rfl, rfl⟩ := split_at_unique_chain rfl h1.smc hms_eq
  have hr : ({ lhs := MGMCFGNT.prof false γ s',
               rhs := [MGMCFGNT.prof false (MGFeature.licensor f :: γ)
                 (slotsOf (allLics G) (ms1 ++ ⟨t, [MGFeature.licensee f]⟩ :: ms2))],
               yield := [MCFGAtom.var 0 p, MCFGAtom.var 0 0] :: vs } :
      MCFGRule (MGMCFGNT Base Lic) T) ∈ (mgToMCFG G).rules := by
    change _ ∈ buildRules G
    unfold buildRules
    simp only [List.mem_append, List.mem_filterMap]
    left; right
    exact ⟨(false, MGFeature.licensor f :: γ,
      slotsOf (allLics G) (ms1 ++ ⟨t, [MGFeature.licensee f]⟩ :: ms2)), hp1, by simp [hcl]⟩
  have hy := MCFG.Yield.rule hr (MCFG.YieldList.cons ih1 MCFG.YieldList.nil)
  have hev : MCFG.evalYield [s :: strsOf (allLics G) (ms1 ++ ⟨t, [MGFeature.licensee f]⟩ :: ms2)]
      ([MCFGAtom.var 0 p, MCFGAtom.var 0 0] :: vs) =
      (t ++ s) :: strsOf (allLics G) (ms1 ++ ms2) := by
    simp only [MCFG.evalYield, List.map_cons]
    have hhead : MCFG.evalComp [s :: strsOf (allLics G) (ms1 ++ ⟨t, [MGFeature.licensee f]⟩ :: ms2)]
        [MCFGAtom.var 0 p, MCFGAtom.var 0 0] = t ++ s := by simp [MCFG.evalComp, hget]
    rw [hhead]
    exact congrArg ((t ++ s) :: ·) heval
  simpa [hslots', hev] using hy

private theorem mgToMCFG_move2_complete [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {s t : List T}
    {f f' : Lic} {γ δ' : List (MGFeature Base Lic)} {ms1 ms2 : List (MGChain Base Lic T)}
    (h1 : G.Derives ⟨false, ⟨s, MGFeature.licensor f :: γ⟩, ms1 ++ ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2⟩)
    (hsmcNew : SMC (ms1 ++ ⟨t, MGFeature.licensee f' :: δ'⟩ :: ms2))
    (ih1 : (mgToMCFG G).Yield
      (MGMCFGNT.prof false (MGFeature.licensor f :: γ)
        (slotsOf (allLics G) (ms1 ++ ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2)))
      (s :: strsOf (allLics G) (ms1 ++ ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2))) :
    (mgToMCFG G).Yield (MGMCFGNT.prof false γ (slotsOf (allLics G) (ms1 ++ ⟨t, MGFeature.licensee f' :: δ'⟩ :: ms2)))
      ((s) :: strsOf (allLics G) (ms1 ++ ⟨t, MGFeature.licensee f' :: δ'⟩ :: ms2)) := by
  have hp1 := mem_allProfiles_of_derives h1
  have hfL : f ∈ allLics G :=
    movers_in_allLics h1 ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩
      (List.mem_append_right _ (List.mem_cons_self ..)) f rfl
  obtain ⟨entry, hentry, hsuf⟩ :=
    h1.feats_suffix.2 ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩
      (List.mem_append_right _ (List.mem_cons_self ..))
  have hf'L : f' ∈ allLics G := mem_allLics_of_suffix hentry (MG.isSuffix_tail hsuf)
  have hlf : MGFeature.licensee f' :: δ' ∈ licFeats G f' :=
    mem_licFeats_iff.mpr ⟨mem_allFeats_of_suffix hentry (MG.isSuffix_tail hsuf), δ', rfl⟩
  obtain ⟨s', vs, hrel⟩ := relocateSlot_complete (T := T) (allLics G) hfL hf'L h1.smc hsmcNew
  obtain ⟨t', ms1', ms2', hms_eq, _, hslots', heval⟩ :=
    relocateSlot_eval_and_mem (allLics G) (nodup_allLics G) h1.smc (movers_in_allLics h1) s hrel
  dsimp only at hms_eq heval
  have ht_eq : t' = t := by
    have hc1 : ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ ∈
        ms1 ++ ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2 :=
      List.mem_append_right _ (List.mem_cons_self ..)
    have hc2 : ⟨t', MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ ∈
        ms1 ++ ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2 := by
      rw [hms_eq]; exact List.mem_append_right _ (List.mem_cons_self ..)
    have hceq := smc_unique_chain h1.smc hc2 rfl hc1 rfl
    simpa using congrArg MGChain.str hceq
  subst t'
  obtain ⟨rfl, rfl⟩ := split_at_unique_chain rfl h1.smc hms_eq
  have hr : ({ lhs := MGMCFGNT.prof false γ s',
               rhs := [MGMCFGNT.prof false (MGFeature.licensor f :: γ)
                 (slotsOf (allLics G) (ms1 ++ ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2))],
               yield := [MCFGAtom.var 0 0] :: vs } :
      MCFGRule (MGMCFGNT Base Lic) T) ∈ (mgToMCFG G).rules := by
    change _ ∈ buildRules G
    unfold buildRules
    simp only [List.mem_append, List.mem_flatMap, List.mem_filterMap]
    right
    refine ⟨(false, MGFeature.licensor f :: γ,
      slotsOf (allLics G) (ms1 ++ ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2)), hp1, ?_⟩
    simp only [↓reduceIte, List.mem_flatMap, List.mem_filterMap]
    exact ⟨f', hf'L, MGFeature.licensee f' :: δ', hlf, by simp [hrel]⟩
  have hy := MCFG.Yield.rule hr (MCFG.YieldList.cons ih1 MCFG.YieldList.nil)
  have hev : MCFG.evalYield [s :: strsOf (allLics G) (ms1 ++ ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2)]
      ([MCFGAtom.var 0 0] :: vs) =
      s :: strsOf (allLics G) (ms1 ++ ⟨t, MGFeature.licensee f' :: δ'⟩ :: ms2) := by
    simp only [MCFG.evalYield, List.map_cons]
    have hhead : MCFG.evalComp [s :: strsOf (allLics G) (ms1 ++ ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2)]
        [MCFGAtom.var 0 0] = s := by simp [MCFG.evalComp]
    rw [hhead]
    exact congrArg (s :: ·) heval
  simpa [hslots', hev] using hy

/-- Completeness of `mgToMCFG`: every derivable MG expression yields its canonical tuple in `mgToMCFG G`. -/
theorem mgToMCFG_complete [DecidableEq Base] [DecidableEq Lic]
    {G : MG Base Lic T} {e : MGExpr Base Lic T} (h : MG.Derives G e) :
    MCFG.Yield (mgToMCFG G)
      (MGMCFGNT.prof e.isLex e.head.feats (slotsOf (allLics G) e.movers))
      (e.head.str :: strsOf (allLics G) e.movers) := by
  induction h with
  | @lex w α hlex =>
    have hr : ({ lhs := MGMCFGNT.prof true α ((allLics G).map fun _ => none),
                 rhs := [], yield := [w.map MCFGAtom.tm] } : MCFGRule (MGMCFGNT Base Lic) T) ∈
        (mgToMCFG G).rules := by
      change _ ∈ buildRules G
      unfold buildRules
      simp only [List.mem_append, List.mem_map]
      left; left; left; left; left; right
      exact ⟨(w, α), hlex, rfl⟩
    have hy := MCFG.Yield.rule hr MCFG.YieldList.nil
    simpa [slotsOf_nil, strsOf_nil, MCFG.evalYield, evalComp_map_tm] using hy
  | @merge1 s t x γ b ms h1 h2 ih1 ih2 =>
    have hp1 := mem_allProfiles_of_derives h1
    have hp2 := mem_allProfiles_of_derives h2
    simp only [slotsOf_nil] at hp1 ih1
    let tailVars := (List.range ((slotsOf (allLics G) ms).countP Option.isSome)).map fun k =>
      [MCFGAtom.var (T := T) 1 (1 + k)]
    have hr : ({ lhs := MGMCFGNT.prof false γ (slotsOf (allLics G) ms),
                 rhs := [MGMCFGNT.prof true (MGFeature.sel x :: γ) ((allLics G).map fun _ => none),
                         MGMCFGNT.prof b [MGFeature.cat x] (slotsOf (allLics G) ms)],
                 yield := [MCFGAtom.var 0 0, MCFGAtom.var 1 0] :: tailVars } :
        MCFGRule (MGMCFGNT Base Lic) T) ∈ (mgToMCFG G).rules := by
      change _ ∈ buildRules G
      unfold buildRules
      simp only [List.mem_append, List.mem_flatMap, List.mem_filterMap]
      left; left; left; left; right
      refine ⟨(true, MGFeature.sel x :: γ, (allLics G).map fun _ => none), hp1, ?_⟩
      simp only [and_self, ↓reduceIte, List.mem_filterMap]
      exact ⟨(b, [MGFeature.cat x], slotsOf (allLics G) ms), hp2, by simp [tailVars]⟩
    have hy := MCFG.Yield.rule hr (MCFG.YieldList.cons ih1 (MCFG.YieldList.cons ih2 MCFG.YieldList.nil))
    have hev : MCFG.evalYield [s :: strsOf (allLics G) ([] : List (MGChain Base Lic T)), t :: strsOf (allLics G) ms]
        ([MCFGAtom.var 0 0, MCFGAtom.var 1 0] :: tailVars) =
        (s ++ t) :: strsOf (allLics G) ms := by
      simp only [MCFG.evalYield, List.map_cons]
      have hhead : MCFG.evalComp [s :: strsOf (allLics G) ([] : List (MGChain Base Lic T)), t :: strsOf (allLics G) ms]
          [MCFGAtom.var 0 0, MCFGAtom.var 1 0] = s ++ t := by simp [MCFG.evalComp]
      rw [hhead]; congr 1
      dsimp only [tailVars]
      rw [← strsOf_length (allLics G) ms]
      exact evalYield_range_vars1 (s :: strsOf (allLics G) ([] : List (MGChain Base Lic T)))
        [t] (strsOf (allLics G) ms)
    simpa [hev] using hy
  | @merge2 s t x γ b ms1 ms2 h1 h2 hsmc12 ih1 ih2 =>
    have hp1 := mem_allProfiles_of_derives h1
    have hp2 := mem_allProfiles_of_derives h2
    obtain ⟨hm, heval⟩ := evalYield_mergeVars (allLics G) h1.smc h2.smc hsmc12
    have hr : ({ lhs := MGMCFGNT.prof false γ (slotsOf (allLics G) (ms1 ++ ms2)),
                 rhs := [MGMCFGNT.prof false (MGFeature.sel x :: γ) (slotsOf (allLics G) ms1),
                         MGMCFGNT.prof b [MGFeature.cat x] (slotsOf (allLics G) ms2)],
                 yield := [MCFGAtom.var 1 0, MCFGAtom.var 0 0] ::
                   mergeVars 1 1 (slotsOf (allLics G) ms1) (slotsOf (allLics G) ms2) } :
        MCFGRule (MGMCFGNT Base Lic) T) ∈ (mgToMCFG G).rules := by
      change _ ∈ buildRules G
      unfold buildRules
      simp only [List.mem_append, List.mem_flatMap, List.mem_filterMap]
      left; left; left; right
      refine ⟨(false, MGFeature.sel x :: γ, slotsOf (allLics G) ms1), hp1, ?_⟩
      simp only [↓reduceIte, List.mem_filterMap]
      exact ⟨(b, [MGFeature.cat x], slotsOf (allLics G) ms2), hp2, by simp [hm]⟩
    have hy := MCFG.Yield.rule hr (MCFG.YieldList.cons ih1 (MCFG.YieldList.cons ih2 MCFG.YieldList.nil))
    have hev : MCFG.evalYield [s :: strsOf (allLics G) ms1, t :: strsOf (allLics G) ms2]
        ([MCFGAtom.var 1 0, MCFGAtom.var 0 0] ::
          mergeVars 1 1 (slotsOf (allLics G) ms1) (slotsOf (allLics G) ms2)) =
        (t ++ s) :: strsOf (allLics G) (ms1 ++ ms2) := by
      simp only [MCFG.evalYield, List.map_cons]
      have hhead : MCFG.evalComp [s :: strsOf (allLics G) ms1, t :: strsOf (allLics G) ms2]
          [MCFGAtom.var 1 0, MCFGAtom.var 0 0] = t ++ s := by simp [MCFG.evalComp]
      rw [hhead]
      exact congrArg ((t ++ s) :: ·) (heval [s] [t])
    simpa [hev] using hy
  | @merge3 s t x f γ δ' b1 b2 ms1 ms2 h1 h2 hsmc3 ih1 ih2 =>
    have hp1 := mem_allProfiles_of_derives h1
    have hp2 := mem_allProfiles_of_derives h2
    have hsmc12 : SMC (ms1 ++ ms2) := MG.smc_remove hsmc3
    have hfL : f ∈ allLics G := by
      obtain ⟨entry, hentry, hsuf⟩ := h2.feats_suffix.1
      exact mem_allLics_of_suffix hentry (MG.isSuffix_tail hsuf)
    obtain ⟨hm, _⟩ := evalYield_mergeVars (allLics G) h1.smc h2.smc hsmc12
    obtain ⟨hi, heval⟩ :=
      evalYield_merge3Vars (allLics G) (nodup_allLics G) hfL h1.smc h2.smc hsmc3
    let ms3 := ms1 ++ ⟨t, MGFeature.licensee f :: δ'⟩ :: ms2
    have hr : ({ lhs := MGMCFGNT.prof false γ (slotsOf (allLics G) ms3),
                 rhs := [MGMCFGNT.prof b1 (MGFeature.sel x :: γ) (slotsOf (allLics G) ms1),
                         MGMCFGNT.prof b2 (MGFeature.cat x :: MGFeature.licensee f :: δ') (slotsOf (allLics G) ms2)],
                 yield := [MCFGAtom.var 0 0] ::
                   merge3Vars f 1 1 (allLics G) (slotsOf (allLics G) ms1) (slotsOf (allLics G) ms2) } :
        MCFGRule (MGMCFGNT Base Lic) T) ∈ (mgToMCFG G).rules := by
      change _ ∈ buildRules G
      unfold buildRules
      simp only [List.mem_append, List.mem_flatMap, List.mem_filterMap]
      left; left; right
      refine ⟨(b1, MGFeature.sel x :: γ, slotsOf (allLics G) ms1), hp1, ?_⟩
      simp only [List.mem_filterMap]
      exact ⟨(b2, MGFeature.cat x :: MGFeature.licensee f :: δ', slotsOf (allLics G) ms2), hp2,
        by simp [hm, hi, ms3]⟩
    have hy := MCFG.Yield.rule hr (MCFG.YieldList.cons ih1 (MCFG.YieldList.cons ih2 MCFG.YieldList.nil))
    have hev : MCFG.evalYield [s :: strsOf (allLics G) ms1, t :: strsOf (allLics G) ms2]
        ([MCFGAtom.var 0 0] ::
          merge3Vars f 1 1 (allLics G) (slotsOf (allLics G) ms1) (slotsOf (allLics G) ms2)) =
        s :: strsOf (allLics G) ms3 := by
      simp only [MCFG.evalYield, List.map_cons]
      have hhead : MCFG.evalComp [s :: strsOf (allLics G) ms1, t :: strsOf (allLics G) ms2]
          [MCFGAtom.var 0 0] = s := by simp [MCFG.evalComp]
      rw [hhead]
      exact congrArg (s :: ·) (heval [s] [t] rfl)
    simpa [hev] using hy
  | @move1 s t f γ ms1 ms2 h1 ih1 =>
    exact mgToMCFG_move1_complete h1 ih1
  | @move2 s t f f' γ δ' ms1 ms2 h1 hsmcNew ih1 =>
    exact mgToMCFG_move2_complete h1 hsmcNew ih1

/-- **Michaelis Theorem (1998, 2001) — Direction 1 (`MG → MCFG`)**:
    Every Minimalist Grammar has a weakly equivalent Linear Non-Erasing MCFG (LCFRS). -/
theorem mgToMCFG_lang [DecidableEq Base] [DecidableEq Lic]
    (G : MG Base Lic T) (w : List T) :
    (mgToMCFG G).Lang w ↔ G.Lang w := by
  constructor
  · intro h
    obtain ⟨w', hw, hlang⟩ := mgToMCFG_sound h
    simp at hw; subst hw; exact hlang
  · rintro ⟨b, hder⟩
    have hy := mgToMCFG_complete hder
    simp only [slotsOf_nil, strsOf_nil] at hy
    have hr : ({ lhs := MGMCFGNT.start,
                 rhs := [MGMCFGNT.prof b [MGFeature.cat G.start] ((allLics G).map fun _ => none)],
                 yield := [[MCFGAtom.var 0 0]] } : MCFGRule (MGMCFGNT Base Lic) T) ∈
        (mgToMCFG G).rules := by
      change _ ∈ buildRules G
      unfold buildRules
      simp only [List.mem_append, List.mem_map]
      left; left; left; left; left; left
      exact ⟨b, by cases b <;> simp, rfl⟩
    have hres := MCFG.Yield.rule hr (MCFG.YieldList.cons hy MCFG.YieldList.nil)
    change MCFG.Yield (mgToMCFG G) MGMCFGNT.start [w]
    simpa [MCFG.evalYield, MCFG.evalComp] using hres

end MGtoMCFG
end FormalLinguistics
