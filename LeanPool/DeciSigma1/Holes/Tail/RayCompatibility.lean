/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Tail.TerminalRays
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Compatible rays

The bound on rejected tails replaces the rejected tails of several coordinates by rays at once.
For a ray `Ω` and a cut `J`, `Ω.prefixBeforeOnset` is its text before the onset and
`Ω.suffixBeforeOnset J` the part of that text after `J` (`Words.Basic`). A ray `v` whose first
rejected cut `J v` lies before its onset can close a cycle of constraints in the ray system
through this stretch. Three overlaps of `v` with another ray `u` are therefore forbidden
(`NoForbiddenRayOverlap`): the stretch of `v` is a suffix of the text of `u` before its onset,
while `u` is not periodic at its first rejected cut (`PrefixOverlap`) or with the same periodic
part (`PeriodicTailOverlap`); or the stretch of `u` is a suffix of the text of `v` before its
onset and not longer than the stretch of `v` (`ReversePrefixOverlap`). A ray with no forbidden
overlap lies on no closed walk of the ray system
(`not_mem_closed_walk_of_noForbiddenRayOverlap`).

Among the candidate rays of one coordinate with distinct onsets, few have a given forbidden
overlap with a fixed ray (`card_prefixOverlap_le`, `card_periodicTailOverlap_le`,
`card_reversePrefixOverlap_le`), because the corresponding cuts carry distinct live states. The
module ends with a bound on uncovered positions (`uncoveredPositions_card_le`).

## Main declarations

- `PrefixOverlap`, `PeriodicTailOverlap`, `ReversePrefixOverlap`, `NoForbiddenRayOverlap`: the
  forbidden overlaps.
- `not_mem_closed_walk_of_noForbiddenRayOverlap`: rays without forbidden overlaps lie on no
  closed walk.
- `card_prefixOverlap_le`, `card_periodicTailOverlap_le`, `card_reversePrefixOverlap_le`: few
  candidates have a forbidden overlap.
- `uncoveredPositions_card_le`: a bound on uncovered positions from bounded gaps.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table

variable {α S : Type} {k : ℕ}

/-- A ray agreeing with a word is periodic there from its onset. -/
theorem periodicOn_of_rayAgrees [DecidableEq α] {Ω : Ray α} {x : List α} {E : ℕ}
    (h : RayAgrees Ω x E) : PeriodicOn x Ω.period Ω.onset E := by
  intro p hp hpe
  have hper := Ray.periodicFrom_period Ω (p - Ω.onset)
  simp only at hper
  rw [h.getElem? (by omega), h.getElem? (by omega), show p = Ω.onset + (p - Ω.onset) by omega,
    show Ω.onset + (p - Ω.onset) + Ω.period = Ω.onset + (p - Ω.onset + Ω.period) by ring, hper]

/-- If `h` is a period of `f` from position `A` on, so is every multiple of `h`. -/
theorem shift_mul {f : ℕ → α} {A h : ℕ} (hper : ∀ p, A ≤ p → f (p + h) = f p) :
    ∀ j p, A ≤ p → f (p + j * h) = f p := by
  intro j
  induction j with
  | zero => intro p _; simp
  | succ j ih =>
    intro p hp
    rw [show p + (j + 1) * h = (p + j * h) + h by ring, hper _ (by nlinarith), ih p hp]

/-! ## The ray of a factor closed at a window -/

section RepeatFactorRay

variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}

/-- The ray of a factor closed at window `B` is periodic with the factor length from `c - B`
on. -/
theorem repeatFactorRay_period (hcl : ClosedAt T q0 x B c c') :
    ∀ p, c - B ≤ p → (repeatFactorRay x c c' hcl.2.1 hcl.2.2.1).stream (p + (c' - c)) =
      (repeatFactorRay x c c' hcl.2.1 hcl.2.2.1).stream p := by
  intro p hp
  have hcc := hcl.2.1; have hc' := hcl.2.2.1
  have hpre := streamPrefix_repeatFactorRay hcc hc' (p + (c' - c) + 1)
  have h1 := pumpFactor_letter_period hcl (L := p + (c' - c) + 1) (by omega) hp (by omega)
  rw [← hpre, List.getElem?_eq_getElem (by simp; omega),
    List.getElem?_eq_getElem (by simp; omega), getElem_streamPrefix _ _ _ (by omega),
    getElem_streamPrefix _ _ _ (by omega)] at h1
  exact (Option.some.inj h1).symm

/-- A period `p ∣ c' - c` of the closure region `[c - B, c')` is a period of the ray from
`c - B` on. -/
theorem repeatFactorRay_periodicFrom (hcl : ClosedAt T q0 x B c c') {p : ℕ}
    (hp : 0 < p)
    (hdvd : p ∣ c' - c) (hper : PeriodicOn x p (c - B) c') :
    PeriodicFrom (repeatFactorRay x c c' hcl.2.1 hcl.2.2.1).stream (c - B) p := by
  classical
  have hcc := hcl.2.1; have hc' := hcl.2.2.1; have hB := hcl.1
  set Ω := repeatFactorRay x c c' hcc hc'
  set h := c' - c
  have hh : 0 < h := by omega
  have hag := repeatFactorRay_agrees hcc hc'
  have hmul := shift_mul (f := Ω.stream) (A := c - B) (h := h) (repeatFactorRay_period hcl)
  -- every position from `c - B` on reduces into `[c - B, c' - B)`
  have hred : ∀ y, c - B ≤ y → Ω.stream y = Ω.stream (c - B + (y - (c - B)) % h) := by
    intro y hy
    have := hmul ((y - (c - B)) / h) (c - B + (y - (c - B)) % h) (by omega)
    rw [← this]; congr 1
    have := Nat.mod_add_div (y - (c - B)) h
    rw [Nat.mul_comm] at this; omega
  intro t
  change Ω.stream (c - B + (t + p)) = Ω.stream (c - B + t)
  rw [hred _ (by omega), hred (c - B + t) (by omega)]
  have h1 : (c - B + (c - B + (t + p) - (c - B)) % h) < c' := by
    have := Nat.mod_lt (c - B + (t + p) - (c - B)) hh; omega
  have h2 : (c - B + (c - B + t - (c - B)) % h) < c' := by
    have := Nat.mod_lt (c - B + t - (c - B)) hh; omega
  have e := hper.eq_of_mod (p := c - B + (c - B + (t + p) - (c - B)) % h)
    (q := c - B + (c - B + t - (c - B)) % h) (by omega) (by omega) h1 h2 (by
      rw [show c - B + (t + p) - (c - B) = t + p by omega, show c - B + t - (c - B) = t by omega]
      obtain ⟨j, hj⟩ := hdvd
      rw [Nat.add_mod (c - B), Nat.add_mod (c - B) (t % h), hj, Nat.mod_mul_right_mod,
        Nat.mod_mul_right_mod, Nat.add_mod t p, Nat.mod_self, Nat.add_zero, Nat.mod_mod])
  rw [hag.getElem? h1, hag.getElem? h2] at e
  exact (Option.some.inj e)

end RepeatFactorRay

/-! ## Forbidden overlaps -/

section Compatibility

variable [DecidableEq α]

/-- The stretch of `v` after `Jv` is a suffix of the text of `u` before its onset, at least as
long as the stretch of `u` after `Ju`, and `u` is not periodic at `Ju`. -/
def PrefixOverlap (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Prop :=
  Ju < Ωu.onset ∧ Ωv.suffixBeforeOnset Jv <:+ Ωu.prefixBeforeOnset ∧
      (Ωu.suffixBeforeOnset Ju).length ≤ (Ωv.suffixBeforeOnset Jv).length

/-- The stretch of `v` after `Jv` is a suffix of the text of `u` before its onset, `u` is periodic
at `Ju`, and the periodic parts of `v` and `u` are equal. -/
def PeriodicTailOverlap (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Prop :=
  Ωu.onset ≤ Ju ∧ Ωv.suffixBeforeOnset Jv <:+ Ωu.prefixBeforeOnset ∧ ∀ t, Ωv.stream (Ωv.onset + t) =
      Ωu.stream (Ωu.onset + t)

/-- The stretch of `u` after `Ju` is nonempty, a suffix of the text of `v` before its onset, and
at least as long as the stretch of `v` after `Jv`. -/
def ReversePrefixOverlap (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Prop :=
  Ωu.suffixBeforeOnset Ju ≠ [] ∧ Ωu.suffixBeforeOnset Ju <:+ Ωv.prefixBeforeOnset ∧
      (Ωv.suffixBeforeOnset Jv).length ≤ (Ωu.suffixBeforeOnset Ju).length

/-- The ray `v` has none of the three forbidden overlaps with the ray `u`. -/
def NoForbiddenRayOverlap (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Prop :=
  ¬ PrefixOverlap Ωv Ωu Jv Ju ∧ ¬ PeriodicTailOverlap Ωv Ωu Jv Ju ∧
      ¬ ReversePrefixOverlap Ωv Ωu Jv Ju

instance (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Decidable (PrefixOverlap Ωv Ωu Jv Ju) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Decidable (PeriodicTailOverlap Ωv Ωu Jv Ju) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ t, Ωv.stream (Ωv.onset + t) = Ωu.stream (Ωu.onset + t)))

instance (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Decidable (ReversePrefixOverlap Ωv Ωu Jv Ju) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Decidable (NoForbiddenRayOverlap Ωv Ωu Jv Ju) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- For two rays that are not periodic at their first rejected cuts, the absence of forbidden
overlaps is symmetric. -/
theorem compatible_symm {Ωv Ωu : Ray α} {Jv Ju : ℕ} (hv : Jv < Ωv.onset) (hu : Ju < Ωu.onset)
    (h : NoForbiddenRayOverlap Ωv Ωu Jv Ju) : NoForbiddenRayOverlap Ωu Ωv Ju Jv := by
  obtain ⟨h1, _, h2⟩ := h
  refine ⟨fun hc => h2 ⟨?_, hc.2.1, hc.2.2⟩, fun hc => by have := hc.1; omega,
    fun hc => h1 ⟨hu, hc.2.1, hc.2.2⟩⟩
  intro he
  have := congrArg List.length he
  simp at this
  omega

/-- A constraint `h → x` of the ray system into a ray `x` with `J x` before its onset aligns the
onsets and makes the stretch of `x` a suffix of the text of `h` before its onset. -/
theorem edge_step {Ωh Ωx : Ray α} {a b Jx : ℕ} (heq : ∀ t, Ωh.stream (a + t) = Ωx.stream (b + t))
    (hb : b ≤ Jx) (hx : Jx < Ωx.onset) :
    Ωx.suffixBeforeOnset Jx <:+ Ωh.prefixBeforeOnset ∧ ∀ t, Ωh.stream (Ωh.onset + t) =
        Ωx.stream (Ωx.onset + t) := by
  rcases Ray.suffix_eq_cases heq with ⟨_, h2⟩ | ⟨_, h2⟩
  · omega
  · constructor
    · rw [Ray.prefixBeforeOnset, Ray.suffixBeforeOnset, streamPrefix_suffix_iff]
      refine ⟨by omega, fun t ht => ?_⟩
      have := heq (Jx - b + t)
      rw [show a + (Jx - b + t) = Ωh.onset - (Ωx.onset - Jx) + t by omega,
        show b + (Jx - b + t) = Jx + t by omega] at this
      exact this.symm
    · intro t
      have := heq (Ωh.onset - a + t)
      rwa [show a + (Ωh.onset - a + t) = Ωh.onset + t by omega,
        show b + (Ωh.onset - a + t) = Ωx.onset + t by omega] at this

variable {ι : Type} [Fintype S]

/-- An edge of the ray system joins distinct rays with equal infinite suffixes at a target cut
`b ≤ J`. -/
theorem raySys_edge [Fintype ι] [DecidableEq ι] {M : StructuralReader α S k} {st : ι → S}
    {Ω : ι → Ray α} {J : ι → ℕ} {i j : ι} (h : ((raySystem M st Ω J).edgeWeight i j).isSome) :
    i ≠ j ∧ ∃ a b, b ≤ J j ∧ ∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  have hmem := Finset.mem_of_max hc
  obtain ⟨e, he, -⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_filter] at he
  obtain ⟨he, hi, hj⟩ := he
  simp only [rayEdges, Finset.mem_biUnion, Finset.mem_univ, true_and] at he
  obtain ⟨i', j', he⟩ := he
  split_ifs at he with hij
  · simp at he
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hab, -, heq⟩ := Finset.mem_filter.mp hab
    obtain ⟨-, hb⟩ := Finset.mem_product.mp hab
    simp only at hi hj
    subst hi hj
    exact ⟨hij, a, b, by have := Finset.mem_range.mp hb; omega, heq⟩

section NoCycle

variable [Fintype ι] [DecidableEq ι] (M : StructuralReader α S k) (st : ι → S) (Ω : ι → Ray α)
  (J : ι → ℕ) (v : ι)

/-- The invariant of a backward walk from `v` in the ray system: the stretch of `v` is a suffix of
the stretch of `x`, with the same periodic part, and strictly shorter unless `x = v`. -/
def CandidateInvariant (x : ι) : Prop :=
  J x < (Ω x).onset ∧ (Ω v).suffixBeforeOnset (J v) <:+ (Ω x).suffixBeforeOnset (J x) ∧
    (∀ t, (Ω x).stream ((Ω x).onset + t) = (Ω v).stream ((Ω v).onset + t)) ∧
    (x = v ∨ ((Ω v).suffixBeforeOnset (J v)).length < ((Ω x).suffixBeforeOnset (J x)).length)

variable {M st Ω J v}

omit [Fintype ι] in
omit [DecidableEq ι] in
theorem ncInv_step (hclean : ∀ u, u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u)) {h x : ι}
    (hhx : h ≠ x) {a b : ℕ} (hb : b ≤ J x) (heq : ∀ t, (Ω h).stream (a + t) = (Ω x).stream (b + t))
    (hx : CandidateInvariant Ω J v x) : CandidateInvariant Ω J v h ∧ h ≠ v := by
  classical
  obtain ⟨hxJ, hXv, hal, hxv⟩ := hx
  obtain ⟨hXx, hal'⟩ := edge_step heq hb hxJ
  have hXvh : (Ω v).suffixBeforeOnset (J v) <:+ (Ω h).prefixBeforeOnset := hXv.trans hXx
  have halv : ∀ t, (Ω v).stream ((Ω v).onset + t) = (Ω h).stream ((Ω h).onset + t) :=
    fun t => ((hal' t).trans (hal t)).symm
  by_cases hhv : h = v
  · subst hhv
    have hlt : ((Ω h).suffixBeforeOnset (J h)).length < ((Ω x).suffixBeforeOnset (J x)).length := by
      rcases hxv with rfl | h' <;> [exact absurd rfl hhx; exact h']
    exfalso
    apply (hclean x (Ne.symm hhx)).2.2
    refine ⟨fun he => by rw [he] at hlt; simp at hlt, hXx, hlt.le⟩
  · have hc := hclean h hhv
    by_cases hA : (Ω h).onset ≤ J h
    · exact absurd ⟨hA, hXvh, halv⟩ hc.2.1
    push Not at hA
    by_cases hlen : ((Ω h).suffixBeforeOnset (J h)).length ≤ ((Ω v).suffixBeforeOnset (J v)).length
    · exact absurd ⟨hA, hXvh, hlen⟩ hc.1
    push Not at hlen
    refine ⟨⟨hA, ?_, fun t => ((halv t).symm), Or.inr hlen⟩, hhv⟩
    exact List.suffix_of_suffix_length_le hXvh
        ((Ω h).suffixBeforeOnset_suffix_prefixBeforeOnset (J h)) hlen.le

theorem ncInv_walk (hclean : ∀ u, u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u)) :
    ∀ (ys : List ι) (y : ι), (raySystem M st Ω J).IsWalk (ys ++ [y]) → CandidateInvariant Ω J v y →
      ∀ z ∈ ys, CandidateInvariant Ω J v z ∧ z ≠ v
  | [], _, _, _ => by simp
  | z :: zs, y, hw, hy => by
    have hw' : (raySystem M st Ω J).IsWalk (z :: (zs ++ [y])) := by simpa using hw
    have ih := ncInv_walk hclean zs y (by
      cases zs with
      | nil => simp [DifferenceSystem.IsWalk]
      | cons w ws =>
        rw [List.cons_append, DifferenceSystem.isWalk_cons_cons] at hw'
        simpa using hw'.2) hy
    -- the successor of `z`
    obtain ⟨hd, hhd, hzhd, hInv⟩ : ∃ hd, (zs ++ [y]).head? = some hd ∧
        ((raySystem M st Ω J).edgeWeight z hd).isSome ∧ CandidateInvariant Ω J v hd := by
      cases zs with
      | nil =>
        simp only [List.nil_append] at hw' ⊢
        rw [DifferenceSystem.isWalk_cons_cons] at hw'
        exact ⟨y, rfl, hw'.1, hy⟩
      | cons w ws =>
        rw [List.cons_append, DifferenceSystem.isWalk_cons_cons] at hw'
        exact ⟨w, rfl, hw'.1, (ih w List.mem_cons_self).1⟩
    obtain ⟨hne, a, b, hb, heq⟩ := raySys_edge hzhd
    have hz := ncInv_step hclean hne hb heq hInv
    intro z' hz'
    rcases List.mem_cons.mp hz' with rfl | hz'
    · exact hz
    · exact ih z' hz'

/-- A ray `v` that is not periodic at its first rejected cut and has no forbidden overlap with
any other ray lies on no closed walk of the ray system. -/
theorem not_mem_closed_walk_of_noForbiddenRayOverlap (hv : J v < (Ω v).onset)
    (hclean : ∀ u, u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u))
    {i : ι} {p : List ι} (hw : (raySystem M st Ω J).IsWalk (i :: p ++ [i])) : v ∉ i :: p := by
  intro hmem
  have hInvv : CandidateInvariant Ω J v v := ⟨hv, List.suffix_refl _, fun _ => rfl, Or.inl rfl⟩
  rcases List.mem_cons.mp hmem with hvi | hp
  · have hInvi : CandidateInvariant Ω J v i := by rw [← hvi]; exact hInvv
    have := ncInv_walk hclean (i :: p) i hw hInvi i List.mem_cons_self
    exact this.2 hvi.symm
  · obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hp
    have hsplit : i :: (p1 ++ v :: p2) ++ [i] = (i :: p1) ++ v :: (p2 ++ [i]) := by simp
    rw [hsplit] at hw
    have h12 := List.isChain_split.mp hw
    have hi := ncInv_walk hclean (i :: p1) v h12.1 hInvv i List.mem_cons_self
    have h2 : (raySystem M st Ω J).IsWalk ((v :: p2) ++ [i]) := by
      rw [List.cons_append]; exact h12.2
    have := ncInv_walk hclean (v :: p2) i h2 hi.1 v List.mem_cons_self
    exact this.2 rfl

end NoCycle

end Compatibility

/-! ## Counting candidates with forbidden overlaps -/

section Count

variable [DecidableEq α] [Fintype S]
    [DecidableEq S] {M : StructuralReader α S k} {W : Fin k → List α}
  {u v : Fin k} {Ωu : Ray α} {κ : Type} (R : Finset κ) (Ωc : κ → Ray α) (Ec : κ → ℕ)

omit [DecidableEq S] in
/-- Among candidate rays of the word `v` with distinct onsets, at most `N - 1` have a
`PrefixOverlap` with the ray `u`: the corresponding cuts of `W u`, at or before its first
rejected cut, carry distinct live states. -/
theorem card_prefixOverlap_le (hu : M.Eligible W u) {Eu : ℕ} (hΩu : RayAgrees Ωu (W u) Eu)
    (hAu : Ωu.onset ≤ Eu) (hc : ∀ r ∈ R, RayAgrees (Ωc r) (W v) (Ec r))
    (hAc : ∀ r ∈ R, (Ωc r).onset ≤ Ec r) (hinj : Set.InjOn (fun r => (Ωc r).onset) R) :
    (R.filter (fun r => PrefixOverlap (Ωc r) Ωu (M.firstRejection W v)
        (M.firstRejection W u))).card ≤
      Fintype.card S - 1 := by
  classical
  classical
  apply card_le_card_sub_one_of_injOn _ (fun r => (Ωc r).onset)
      (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
    (fun r => M.runPrefix W u (Ωu.onset - ((Ωc r).onset - M.firstRejection W v))) M.dead
  · intro r hr r' hr' hlt
    rw [Finset.mem_filter] at hr hr'
    obtain ⟨hrR, hJu, hsuf, hlen⟩ := hr
    obtain ⟨hrR', -, hsuf', hlen'⟩ := hr'
    rw [Ray.suffixBeforeOnset, Ray.prefixBeforeOnset, streamPrefix_suffix_iff] at hsuf hsuf'
    simp only [Ray.length_suffixBeforeOnset] at hlen hlen'
    have key : ∀ q ∈ R, (Ωc q).onset - M.firstRejection W v ≤ Ωu.onset →
        (∀ t < (Ωc q).onset - M.firstRejection W v, (Ωc q).stream (M.firstRejection W v + t) =
          Ωu.stream (Ωu.onset - ((Ωc q).onset - M.firstRejection W v) + t)) →
        ∀ t < (Ωc q).onset - M.firstRejection W v,
          (W u)[Ωu.onset - ((Ωc q).onset - M.firstRejection W v) + t]? =
              (W v)[M.firstRejection W v + t]? := by
      intro q hq h1 h2 t ht
      rw [hΩu.getElem? (by omega), (hc q hq).getElem? (by have := hAc q hq; omega), h2 t ht]
    intro he
    apply no_early_repeat hu (a' := Ωu.onset - ((Ωc r').onset - M.firstRejection W v))
      (a := Ωu.onset - ((Ωc r).onset - M.firstRejection W v)) (by omega) (by omega) _ he.symm
    intro t ht
    rw [key r' hrR' hsuf'.1 hsuf'.2 t (by omega), key r hrR hsuf.1 hsuf.2 t (by omega)]
  · intro r _; exact hu.runPrefix_ne _

omit [DecidableEq S] in
/-- Among candidate rays of the word `v` with distinct onsets, at most `N - 1` have a
`ReversePrefixOverlap` with the ray `u`: the stretch of `u` occurs in `W v` ending at the onset
of the candidate, and the starts of these occurrences carry distinct live states. -/
theorem card_reversePrefixOverlap_le (hv : M.Eligible W v)
    (hc : ∀ r ∈ R, RayAgrees (Ωc r) (W v) (Ec r))
    (hAc : ∀ r ∈ R, (Ωc r).onset ≤ Ec r) (hJc : ∀ r ∈ R, M.firstRejection W v < (Ωc r).onset)
    (hinj : Set.InjOn (fun r => (Ωc r).onset) R) :
    (R.filter (fun r => ReversePrefixOverlap (Ωc r) Ωu (M.firstRejection W v)
        (M.firstRejection W u))).card ≤
      Fintype.card S - 1 := by
  classical
  classical
  apply card_le_card_sub_one_of_injOn _ (fun r => (Ωc r).onset)
      (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
    (fun r => M.runPrefix W v ((Ωc r).onset - (Ωu.onset - M.firstRejection W u))) M.dead
  · intro r hr r' hr' hlt
    rw [Finset.mem_filter] at hr hr'
    obtain ⟨hrR, -, hsuf, hlen⟩ := hr
    obtain ⟨hrR', -, hsuf', hlen'⟩ := hr'
    rw [Ray.suffixBeforeOnset, Ray.prefixBeforeOnset, streamPrefix_suffix_iff] at hsuf hsuf'
    simp only [Ray.length_suffixBeforeOnset] at hlen hlen'
    have h1 := hJc r hrR
    have h2 := hJc r' hrR'
    have key : ∀ q ∈ R, Ωu.onset - M.firstRejection W u ≤ (Ωc q).onset →
        (∀ t < Ωu.onset - M.firstRejection W u, Ωu.stream (M.firstRejection W u + t) =
          (Ωc q).stream ((Ωc q).onset - (Ωu.onset - M.firstRejection W u) + t)) →
        ∀ t < Ωu.onset - M.firstRejection W u,
          (W v)[(Ωc q).onset - (Ωu.onset - M.firstRejection W u) + t]? =
            some (Ωu.stream (M.firstRejection W u + t)) := by
      intro q hq h1 h2 t ht
      rw [(hc q hq).getElem? (by have := hAc q hq; omega), h2 t ht]
    intro he
    apply no_early_repeat hv (a' := (Ωc r).onset - (Ωu.onset - M.firstRejection W u))
      (a := (Ωc r').onset - (Ωu.onset - M.firstRejection W u)) (by omega) (by omega) _ he
    intro t ht
    rw [key r hrR hsuf.1 hsuf.2 t (by omega), key r' hrR' hsuf'.1 hsuf'.2 t (by omega)]
  · intro r _; exact hv.runPrefix_ne _

omit [DecidableEq S] in
/-- If every candidate of `v` agrees with `W v` on at least `(N + 1) ν` letters from its onset,
where `ν` is the period of `u`, at most `N - 1` candidates have a `PeriodicTailOverlap` with
`u`. -/
theorem card_periodicTailOverlap_le (hu : M.Eligible W u) {Eu : ℕ} (hΩu : RayAgrees Ωu (W u) Eu)
    (hJu : M.firstRejection W u ≤ Eu) (hc : ∀ r ∈ R, RayAgrees (Ωc r) (W v) (Ec r))
    (hrun : ∀ r ∈ R, (Ωc r).onset + (Fintype.card S + 1) * Ωu.period ≤ Ec r)
    (hJc : ∀ r ∈ R, M.firstRejection W v < (Ωc r).onset)
    (hinj : Set.InjOn (fun r => (Ωc r).onset) R) :
    (R.filter (fun r => PeriodicTailOverlap (Ωc r) Ωu (M.firstRejection W v)
        (M.firstRejection W u))).card ≤
      Fintype.card S - 1 := by
  classical
  classical
  have hν : 0 < Ωu.period := Ray.period_pos
  have hNν : Fintype.card S * Ωu.period + Ωu.period = (Fintype.card S + 1) * Ωu.period := by ring
  apply card_le_card_sub_one_of_injOn _ (fun r => (Ωc r).onset)
      (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
    (fun r => M.runPrefix W u (Ωu.onset - ((Ωc r).onset - M.firstRejection W v))) M.dead
  · intro s hs t ht hlt
    rw [Finset.mem_filter] at hs ht
    obtain ⟨hsR, hAu, hsuf, hal⟩ := hs
    obtain ⟨htR, -, hsuf', hal'⟩ := ht
    rw [Ray.suffixBeforeOnset, Ray.prefixBeforeOnset, streamPrefix_suffix_iff] at hsuf hsuf'
    have hrs := hrun s hsR
    have hrt := hrun t htR
    have hJs := hJc s hsR
    have hJt := hJc t htR
    -- `J_u - A_u < N ν_u`
    have hf := firstRejection_sub_lt_word hu hν (periodicOn_of_rayAgrees hΩu) hAu hJu
    -- the candidates are `ν_u`-periodic from their onsets
    have hpu := Ray.periodicFrom_period Ωu
    have hps : PeriodicFrom (Ωc s).stream (Ωc s).onset Ωu.period := by
      intro y; change (Ωc s).stream ((Ωc s).onset + (y + Ωu.period)) =
          (Ωc s).stream ((Ωc s).onset + y)
      rw [hal, hal]; exact hpu y
    -- the two onsets are more than `N ν_u` apart
    have hsep : (Ωc s).onset + Fintype.card S * Ωu.period < (Ωc t).onset := by
      by_contra hle
      push Not at hle
      have hpt : PeriodicFrom (Ωc t).stream (Ωc t).onset Ωu.period := by
        intro y; change (Ωc t).stream ((Ωc t).onset + (y + Ωu.period)) =
            (Ωc t).stream ((Ωc t).onset + y)
        rw [hal', hal']; exact hpu y
      have hagree : ∀ y < Ωu.period, (Ωc s).stream ((Ωc t).onset + y) =
          (Ωc t).stream ((Ωc t).onset + y) := fun y hy =>
        (hc s hsR).stream_eq (hc t htR) (by omega) (by omega)
      have hps' : StreamPeriod (fun y => (Ωc s).stream ((Ωc t).onset + y)) Ωu.period := by
        have := hps.mono (A' := (Ωc t).onset) (by omega)
        exact this
      have hext : ∀ y, (Ωc s).stream ((Ωc t).onset + y) = (Ωc t).stream ((Ωc t).onset + y) := by
        intro y
        have e1 := streamPeriod_mod hps' y
        have e2 := streamPeriod_mod hpt y
        rw [e1, e2]; exact hagree _ (Nat.mod_lt _ hν)
      have heqs : ∀ x, (Ωc s).onset ≤ x → (Ωc t).stream x = (Ωc s).stream x := by
        intro x hx
        by_cases hxt : x < (Ωc t).onset
        · exact (hc t htR).stream_eq (hc s hsR) (by omega) (by omega)
        · have := hext (x - (Ωc t).onset)
          rw [show (Ωc t).onset + (x - (Ωc t).onset) = x by omega] at this
          exact this.symm
      have hpts : PeriodicFrom (Ωc t).stream (Ωc s).onset Ωu.period := by
        intro y
        change (Ωc t).stream ((Ωc s).onset + (y + Ωu.period)) = (Ωc t).stream ((Ωc s).onset + y)
        rw [heqs _ (by omega), heqs _ (by omega)]
        exact hps y
      have := Ray.onset_le_of_periodicFrom hν hpts
      omega
    -- letters of `W u` from `a_s` and from `a_t` agree with `W v` from `J_v`
    have keys : ∀ y < M.firstRejection W u - (Ωu.onset - ((Ωc s).onset - M.firstRejection W v)),
        (W u)[Ωu.onset - ((Ωc s).onset - M.firstRejection W v) + y]? =
            (W v)[M.firstRejection W v + y]? := by
      intro y hy
      by_cases hyX : y < (Ωc s).onset - M.firstRejection W v
      · rw [hΩu.getElem? (by omega), (hc s hsR).getElem? (by omega), hsuf.2 y hyX]
      · have e1 : Ωu.onset - ((Ωc s).onset - M.firstRejection W v) + y =
            Ωu.onset + (y - ((Ωc s).onset - M.firstRejection W v)) := by omega
        have e2 : M.firstRejection W v + y = (Ωc s).onset +
            (y - ((Ωc s).onset - M.firstRejection W v)) := by
          omega
        rw [e1, e2, hΩu.getElem? (by omega), (hc s hsR).getElem? (by omega), hal]
    have keyt : ∀ y < (Ωc t).onset - M.firstRejection W v,
        (W u)[Ωu.onset - ((Ωc t).onset - M.firstRejection W v) + y]? =
            (W v)[M.firstRejection W v + y]? := by
      intro y hy
      rw [hΩu.getElem? (by omega), (hc t htR).getElem? (by omega), hsuf'.2 y hy]
    intro he
    apply no_early_repeat hu (a' := Ωu.onset - ((Ωc t).onset - M.firstRejection W v))
      (a := Ωu.onset - ((Ωc s).onset - M.firstRejection W v)) (by omega) (by omega) _ he.symm
    intro y hy
    rw [keyt y (by omega), keys y hy]
  · intro r _; exact hu.runPrefix_ne _

end Count

/-! ## Gap charging -/

/-- If each of `n` consecutive segments of `T` positions from `J` contains a covered position
below `len`, and `len ≤ J + n T + T`, at most `(|fs| + 1) · 2T` positions of `[J, len)` are
uncovered: an uncovered position before the last full segment is charged to the start of the
next factor, at distance at most `2T`. -/
theorem uncoveredPositions_card_le (fs : List PeriodicFactor) {J T n len : ℕ} (hT : 0 < T)
    (hlen : len ≤ J + n * T + T)
    (hcov : ∀ m < n, ∃ y, J + m * T ≤ y ∧ y < J + m * T + T ∧ y < len ∧ Covers fs y) :
    (uncoveredPositions fs J len).card ≤ (fs.length + 1) * (2 * T) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := uncoveredPositions fs J len)
    (p := fun x => (x - J) / T + 1 < n)
  have hearly : (uncoveredPositions fs J len).filter (fun x => (x - J) / T + 1 < n) ⊆
      (fs.toFinset ×ˢ Finset.Icc 1 (2 * T)).image (fun q => q.1.start - q.2) := by
    intro x hx
    simp only [uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hx
    obtain ⟨⟨⟨hJx, hxl⟩, hunc⟩, hm⟩ := hx
    have hm1 : (x - J) / T * T ≤ x - J := Nat.div_mul_le_self _ _
    have hm2 : x - J < (x - J) / T * T + T := Nat.lt_div_mul_add hT
    obtain ⟨y, hy1, hy2, -, hyc⟩ := hcov ((x - J) / T + 1) hm
    rw [add_one_mul] at hy1 hy2
    have hex : ∃ z, x < z ∧ Covers fs z := ⟨y, by omega, hyc⟩
    have hz := Nat.find_spec hex
    have hzle : Nat.find hex ≤ y := Nat.find_min' hex ⟨by omega, hyc⟩
    obtain ⟨f, hf, hfs, hfe⟩ := hz.2
    have hfs0 : f.start = Nat.find hex := by
      by_contra hne
      by_cases hxz : x < Nat.find hex - 1
      · exact Nat.find_min hex (m := Nat.find hex - 1) (by omega) ⟨hxz, f, hf, by omega, by omega⟩
      · exact hunc ⟨f, hf, by omega, by omega⟩
    rw [Finset.mem_image]
    refine ⟨(f, Nat.find hex - x), Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hf,
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, by simp only; omega⟩
  have hlate : (uncoveredPositions fs J len).filter (fun x => ¬ ((x - J) / T + 1 < n)) ⊆
      Finset.Ico (J + (n - 1) * T) len := by
    intro x hx
    simp only [uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    obtain ⟨⟨⟨hJx, hxl⟩, -⟩, hm⟩ := hx
    have h2 : (x - J) / T * T ≤ x - J := Nat.div_mul_le_self _ _
    generalize (x - J) / T = q at hm h2
    have h1 : (n - 1) * T ≤ q * T := Nat.mul_le_mul_right _ (by omega)
    exact ⟨by omega, hxl⟩
  have hn := Nat.sub_one_mul n T
  have c1 := Finset.card_le_card hearly
  have c2 := Finset.card_le_card hlate
  have c3 : ((fs.toFinset ×ˢ Finset.Icc 1 (2 * T)).image (fun q => q.1.start - q.2)).card ≤
      fs.length * (2 * T) := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Nat.card_Icc]
    exact Nat.mul_le_mul (List.toFinset_card_le fs) (by omega)
  rw [Nat.card_Ico] at c2
  have : (fs.length + 1) * (2 * T) = fs.length * (2 * T) + 2 * T := by ring
  omega

theorem periodicOn_take {w : List α} {p s e n : ℕ} (h : PeriodicOn w p s e) (hen : e ≤ n) :
    PeriodicOn (w.take n) p s e := by
  intro x hx hxe
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)]
  exact h x hx hxe

end DeciSigma1.Holes.Tail
