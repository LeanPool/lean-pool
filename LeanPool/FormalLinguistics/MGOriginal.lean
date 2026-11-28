/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.MGMCFGEquiv

/-!
# Stabler–Keenan rules and the invariant-carrying presentation

`DerivesSK` is a chain-based presentation of the merge and move rules in Stabler
and Keenan, *Structural similarity within and among languages* (2003), §2.
It keeps category names and licensing features in separate types and uses
the nonempty feature lists specified by `MG.lex_nonempty` for lexical items.

`merge` may introduce movers with any nonempty remaining feature sequence.
`move` applies when no other chain starts with the requested licensee. The
head's feature sequence may be empty after removing the selected feature.
The invariant-carrying `MG.Derives` additionally requires movers to start
with a licensee and imposes the shortest-move constraint on all derived
expressions. The two presentations yield the same complete strings.

Harkema’s *A Recognizer for Minimalist Grammars* (2000), §3.2.2, splits
`merge3` into lexical- and derived-selector cases. His other merge and move
cases correspond to `merge1`, `merge2`, `move1`, and `move2` here.

The language-equivalence result following the rule comparison concerns the
chain-based grammar in this file. See Stabler and Keenan (2003), §2.3,
for weak generative capacity.
-/

@[expose] public section

namespace FormalLinguistics

namespace MG

variable {Base Lic T : Type}

/-- Derivable expressions of a Minimalist Grammar, based on Stabler and Keenan (2003): `merge` has no SMC condition and admits any non-empty remaining
    feature string `δ` on the selected phrase; `move` applies only when no *other*
    mover has `-f` as its first feature (the Shortest Move Constraint). -/
inductive DerivesSK (G : MG Base Lic T) : MGExpr Base Lic T → Prop where
  /-- Lexical insertion. -/
  | lex {w : List T} {α : List (MGFeature Base Lic)} :
      (w, α) ∈ G.lexicon →
      DerivesSK G ⟨true, ⟨w, α⟩, []⟩

  /-- merge1: `s :: =x γ` and `t · x, ms` give `st : γ, ms`. -/
  | merge1 {s t : List T} {x : Base} {γ : List (MGFeature Base Lic)}
      {b : Bool} {ms : List (MGChain Base Lic T)} :
      DerivesSK G ⟨true, ⟨s, MGFeature.sel x :: γ⟩, []⟩ →
      DerivesSK G ⟨b, ⟨t, [MGFeature.cat x]⟩, ms⟩ →
      DerivesSK G ⟨false, ⟨s ++ t, γ⟩, ms⟩

  /-- merge2: `s : =x γ, ms1` and `t · x, ms2` give `ts : γ, ms1, ms2`. -/
  | merge2 {s t : List T} {x : Base} {γ : List (MGFeature Base Lic)}
      {b : Bool} {ms1 ms2 : List (MGChain Base Lic T)} :
      DerivesSK G ⟨false, ⟨s, MGFeature.sel x :: γ⟩, ms1⟩ →
      DerivesSK G ⟨b, ⟨t, [MGFeature.cat x]⟩, ms2⟩ →
      DerivesSK G ⟨false, ⟨t ++ s, γ⟩, ms1 ++ ms2⟩

  /-- merge3: `s · =x γ, ms1` and `t · x δ, ms2` with `δ ≠ ε` give
      `s : γ, ms1, t : δ, ms2`. -/
  | merge3 {s t : List T} {x : Base} {γ δ : List (MGFeature Base Lic)}
      {b1 b2 : Bool} {ms1 ms2 : List (MGChain Base Lic T)} :
      DerivesSK G ⟨b1, ⟨s, MGFeature.sel x :: γ⟩, ms1⟩ →
      DerivesSK G ⟨b2, ⟨t, MGFeature.cat x :: δ⟩, ms2⟩ →
      δ ≠ [] →
      DerivesSK G ⟨false, ⟨s, γ⟩, ms1 ++ ⟨t, δ⟩ :: ms2⟩

  /-- move1: `s : +f γ, ms1, t : -f, ms2` gives `ts : γ, ms1, ms2`,
      provided no other mover has `-f` as its first feature (SMC). -/
  | move1 {s t : List T} {f : Lic} {γ : List (MGFeature Base Lic)}
      {ms1 ms2 : List (MGChain Base Lic T)} :
      DerivesSK G ⟨false, ⟨s, MGFeature.licensor f :: γ⟩,
        ms1 ++ ⟨t, [MGFeature.licensee f]⟩ :: ms2⟩ →
      (∀ c, c ∈ ms1 ++ ms2 → c.headLic ≠ some f) →
      DerivesSK G ⟨false, ⟨t ++ s, γ⟩, ms1 ++ ms2⟩

  /-- move2: `s : +f γ, ms1, t : -f δ, ms2` with `δ ≠ ε` gives
      `s : γ, ms1, t : δ, ms2`, provided no other mover has `-f` as its first
      feature (SMC). -/
  | move2 {s t : List T} {f : Lic} {γ δ : List (MGFeature Base Lic)}
      {ms1 ms2 : List (MGChain Base Lic T)} :
      DerivesSK G ⟨false, ⟨s, MGFeature.licensor f :: γ⟩,
        ms1 ++ ⟨t, MGFeature.licensee f :: δ⟩ :: ms2⟩ →
      δ ≠ [] →
      (∀ c, c ∈ ms1 ++ ms2 → c.headLic ≠ some f) →
      DerivesSK G ⟨false, ⟨s, γ⟩, ms1 ++ ⟨t, δ⟩ :: ms2⟩

/-- The string language of a Minimalist Grammar under the literal
    Stabler–Keenan definition. -/
def LangSK (G : MG Base Lic T) (w : List T) : Prop :=
  ∃ b, DerivesSK G ⟨b, ⟨w, [MGFeature.cat G.start]⟩, []⟩

/-! ### Elementary facts about the `SMC` invariant -/

theorem smc_nil : SMC ([] : List (MGChain Base Lic T)) :=
  ⟨fun _ h => by simp at h, List.nodup_nil⟩

theorem mem_filterMap_headLic {ms : List (MGChain Base Lic T)} {f : Lic} :
    f ∈ ms.filterMap MGChain.headLic ↔ ∃ c, c ∈ ms ∧ c.headLic = some f := by
  simp [List.mem_filterMap]

theorem smc_append_left {ms1 ms2 : List (MGChain Base Lic T)}
    (h : SMC (ms1 ++ ms2)) : SMC ms1 := by
  obtain ⟨hall, hnd⟩ := h
  refine ⟨fun c hc => hall c (List.mem_append_left _ hc), ?_⟩
  rw [List.filterMap_append] at hnd
  exact (List.nodup_append.mp hnd).1

theorem smc_append_right {ms1 ms2 : List (MGChain Base Lic T)}
    (h : SMC (ms1 ++ ms2)) : SMC ms2 := by
  obtain ⟨hall, hnd⟩ := h
  refine ⟨fun c hc => hall c (List.mem_append_right _ hc), ?_⟩
  rw [List.filterMap_append] at hnd
  exact (List.nodup_append.mp hnd).2.1

/-- The distinguished chain of an SMC-valid mover list begins with a licensee. -/
theorem smc_mid {ms1 ms2 : List (MGChain Base Lic T)} {c : MGChain Base Lic T}
    (h : SMC (ms1 ++ c :: ms2)) : ∃ f δ, c.feats = MGFeature.licensee f :: δ :=
  h.1 c (List.mem_append_right _ (List.mem_cons_self ..))

/-- In an SMC-valid mover list, no *other* chain shares the head licensee of `c`. -/
theorem smc_others {ms1 ms2 : List (MGChain Base Lic T)} {c : MGChain Base Lic T} {f : Lic}
    (h : SMC (ms1 ++ c :: ms2)) (hc : c.headLic = some f) :
    ∀ c', c' ∈ ms1 ++ ms2 → c'.headLic ≠ some f := by
  obtain ⟨_, hnd⟩ := h
  rw [List.filterMap_append, List.filterMap_cons, hc] at hnd
  obtain ⟨_, hnd2, hdisj⟩ := List.nodup_append.mp hnd
  obtain ⟨hnot, _⟩ := List.nodup_cons.mp hnd2
  intro c' hc' hf
  rcases List.mem_append.mp hc' with h1 | h2
  · exact hdisj f (mem_filterMap_headLic.mpr ⟨c', h1, hf⟩) f (List.mem_cons_self ..) rfl
  · exact hnot (mem_filterMap_headLic.mpr ⟨c', h2, hf⟩)

/-- Inserting a licensee-initial chain whose head licensee is fresh preserves `SMC`. -/
theorem smc_insert {ms1 ms2 : List (MGChain Base Lic T)} {c : MGChain Base Lic T}
    {f : Lic} {δ : List (MGFeature Base Lic)}
    (h : SMC (ms1 ++ ms2)) (hc : c.feats = MGFeature.licensee f :: δ)
    (hfresh : ∀ c', c' ∈ ms1 ++ ms2 → c'.headLic ≠ some f) :
    SMC (ms1 ++ c :: ms2) := by
  obtain ⟨hall, hnd⟩ := h
  have hhead : c.headLic = some f := by simp [MGChain.headLic, hc]
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h1 | h2
    · exact hall x (List.mem_append_left _ h1)
    · rcases List.mem_cons.mp h2 with rfl | h2'
      · exact ⟨f, δ, hc⟩
      · exact hall x (List.mem_append_right _ h2')
  · rw [List.filterMap_append] at hnd
    obtain ⟨hnd1, hnd2, hdisj⟩ := List.nodup_append.mp hnd
    rw [List.filterMap_append, List.filterMap_cons, hhead]
    refine List.nodup_append.mpr ⟨hnd1, List.nodup_cons.mpr ⟨?_, hnd2⟩, ?_⟩
    · intro hmem
      obtain ⟨c', hc', hf⟩ := mem_filterMap_headLic.mp hmem
      exact hfresh c' (List.mem_append_right _ hc') hf
    · intro a ha b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · intro hab
        subst hab
        obtain ⟨c', hc', hf⟩ := mem_filterMap_headLic.mp ha
        exact hfresh c' (List.mem_append_left _ hc') hf
      · exact hdisj a ha b hb'

/-! ### The two presentations coincide -/

/-- Every expression derivable in the invariant-carrying presentation is derivable
    under the `DerivesSK` rules. -/
theorem Derives.toSK {G : MG Base Lic T} {e : MGExpr Base Lic T} (h : Derives G e) :
    DerivesSK G e := by
  induction h with
  | lex hl => exact DerivesSK.lex hl
  | merge1 _ _ ih1 ih2 => exact DerivesSK.merge1 ih1 ih2
  | merge2 _ _ _ ih1 ih2 => exact DerivesSK.merge2 ih1 ih2
  | merge3 _ _ _ ih1 ih2 => exact DerivesSK.merge3 ih1 ih2 (by simp)
  | move1 h ih =>
    exact DerivesSK.move1 ih (smc_others h.smc (by simp [MGChain.headLic]))
  | move2 h _ ih =>
    exact DerivesSK.move2 ih (by simp) (smc_others h.smc (by simp [MGChain.headLic]))

/-- Conversely, a Stabler–Keenan derivation whose *conclusion* satisfies the SMC
    invariant is a derivation in the invariant-carrying presentation: the
    invariant propagates backwards through every rule. -/
theorem DerivesSK.toDerives {G : MG Base Lic T} {e : MGExpr Base Lic T}
    (h : DerivesSK G e) : SMC e.movers → Derives G e := by
  induction h with
  | lex hl => intro _; exact Derives.lex hl
  | merge1 _ _ ih1 ih2 =>
    intro hs
    exact Derives.merge1 (ih1 smc_nil) (ih2 hs)
  | merge2 _ _ ih1 ih2 =>
    intro hs
    exact Derives.merge2 (ih1 (smc_append_left hs)) (ih2 (smc_append_right hs)) hs
  | merge3 _ _ _ ih1 ih2 =>
    intro hs
    obtain ⟨f, δ', hfe⟩ := smc_mid hs
    simp only at hfe
    subst hfe
    have hrest := smc_remove hs
    exact Derives.merge3 (ih1 (smc_append_left hrest)) (ih2 (smc_append_right hrest)) hs
  | move1 _ hfresh ih =>
    intro hs
    exact Derives.move1 (ih (smc_insert hs rfl hfresh))
  | move2 _ _ hfresh ih =>
    intro hs
    obtain ⟨f', δ', hfe⟩ := smc_mid hs
    simp only at hfe
    subst hfe
    exact Derives.move2 (ih (smc_insert (smc_remove hs) rfl hfresh)) hs

/-- `Derives` derives exactly the Stabler–Keenan expressions whose movers satisfy
    the SMC invariant. -/
theorem derives_iff_SK_and_smc {G : MG Base Lic T} {e : MGExpr Base Lic T} :
    Derives G e ↔ DerivesSK G e ∧ SMC e.movers :=
  ⟨fun h => ⟨h.toSK, h.smc⟩, fun ⟨h, hs⟩ => h.toDerives hs⟩

/-- Both presentations of Minimalist Grammars generate the same string language. -/
theorem langSK_iff_lang (G : MG Base Lic T) (w : List T) :
    G.LangSK w ↔ G.Lang w :=
  ⟨fun ⟨b, h⟩ => ⟨b, h.toDerives smc_nil⟩, fun ⟨b, h⟩ => ⟨b, h.toSK⟩⟩

end MG

/-! ### Main theorem for the Stabler–Keenan presentation -/

/-- Language class of finite Minimalist Grammars under the literal
    Stabler–Keenan (2003) definition. -/
def IsMGLangSK {T : Type} (L : List T → Prop) : Prop :=
  ∃ (Base Lic : Type) (G : MG Base Lic T), ∀ w, G.LangSK w ↔ L w

theorem isMGLangSK_iff_isMGLang {T : Type} (L : List T → Prop) :
    IsMGLangSK L ↔ IsMGLang L := by
  constructor
  · rintro ⟨Base, Lic, G, hG⟩
    exact ⟨Base, Lic, G, fun w => by rw [← MG.langSK_iff_lang, hG]⟩
  · rintro ⟨Base, Lic, G, hG⟩
    exact ⟨Base, Lic, G, fun w => by rw [MG.langSK_iff_lang, hG]⟩

/-- **Michaelis–Harkema Equivalence Theorem for Stabler–Keenan Minimalist Grammars**:
    a language is generated by a finite Minimalist Grammar, in the literal sense of
    Stabler & Keenan (2003), iff it is generated by a finite linear non-erasing
    MCFG (LCFRS). -/
theorem michaelis_harkema_equivalence_SK {T : Type} (L : List T → Prop) :
    IsMGLangSK L ↔ IsMCFGLang L := by
  rw [isMGLangSK_iff_isMGLang, michaelis_harkema_equivalence]


end FormalLinguistics
