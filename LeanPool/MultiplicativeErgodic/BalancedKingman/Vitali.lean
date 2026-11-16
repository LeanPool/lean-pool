/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Kingman
public import LeanPool.MultiplicativeErgodic.NonAtomic
public import LeanPool.MultiplicativeErgodic.BackwardVitali.CoverGeometric

/-!
# Infrastructure for the backward Vitali lemma

Rudolph's backward-Vitali development (`rudolph1990fundamentals`) as it is used by the covering
argument: hitting times, iterate images, and the measure bookkeeping for a family of windows.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
## Infrastructure for the Backward Vitali lemma (Rudolph's backward-Vitali development
[rudolph1990fundamentals])

The Backward Vitali lemma is stated in the paper as "a simplified version of the backward Vitali
theorem of
[rudolph1990fundamentals]" with no proof; Rudolph's proof (his backward-Vitali development, from
the disjoint-translates lemma
through backward Vitali itself) is self-contained *given non-periodicity of `σ`*, with no Rokhlin
towers.

**Added hypotheses (with justification).** Mathlib's `Ergodic σ μ` is only
`MeasurePreserving + PreErgodic`; it bundles neither `IsProbabilityMeasure μ` nor any
non-atomicity assumption. The lemma is *false* without both. For example, take `μ` supported on
a period-2 orbit: it is (trivially) ergodic, but windows of half-width `≥ 1` around distinct
orbit points cannot stay pairwise disjoint, so no positive-measure `A` can cover `> 1 - ε`.
The paper's own standing hypothesis is "an invertible ergodic system on a **Lebesgue
probability space**" (`human/proof_met.tex` line 479), i.e. `[IsProbabilityMeasure μ]` and,
implicitly, non-atomicity. We encode "Lebesgue probability space" exactly as `ProofMet.Rokhlin`
does: `[StandardBorelSpace Ω] [IsProbabilityMeasure μ] [NullSingletonClass μ]`. The
`StandardBorelSpace` hypothesis is load-bearing (not decoration): Mathlib's `NullSingletonClass`
(singletons are null) is strictly weaker than the classical "no atoms" property on a general
measurable space, and `StandardBorelSpace` is what closes the gap, via the embedding into `ℝ`
used by `ProofMet.NonAtomic`.

Below, the foundational "non-periodicity" step of Rudolph's argument is proved in full
(`periodic_null`): periodic points are null. The greedy-covering steps
(disjoint translates → covering across scales → backward Vitali) are likewise proved in
full, so `backwardVitali` is `sorry`-free
and available to callers as a genuine lemma, not merely as a statement.
-/

/-- **Boundedness via truncation** (the "delete a small sliver of measure to enforce
boundedness" step used repeatedly in Rudolph's proof of the backward Vitali theorem: delete at most
`ε/2^{u+1}` in measure of `A_{u-1}` to obtain `A_u` on which the relevant index is bounded). Any
measurable `h : Ω → ℕ` is, trivially, everywhere
finite, so the "overflow" sets `{x ∈ A | N < h x}` shrink (as `N → ∞`) to `∅`; continuity of `μ`
from above (available since `μ A ≤ 1 < ∞`) then makes their measure `→ 0`, giving a single
threshold `N` whose overflow has measure `< δ`. The mechanism is
`tendsto_measure_iInter_atTop`-style continuity from above. -/
theorem exists_meas_bound_sliver {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Set Ω} (hA : MeasurableSet A) (h : Ω → ℕ) (hh : Measurable h)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N : ℕ, μ (A ∩ {x | N < h x}) < δ := by
  set s : ℕ → Set Ω := fun N => A ∩ {x | N < h x} with hsdef
  have hmeas : ∀ N, MeasurableSet (s N) := fun N => hA.inter (hh measurableSet_Ioi)
  have hanti : Antitone s := by
    intro N M hNM x hx
    exact ⟨hx.1, lt_of_le_of_lt hNM hx.2⟩
  have hinter : (⋂ N, s N) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := Set.mem_iInter.mp hx (h x)
    simp only [hsdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at hx'
    exact lt_irrefl _ hx'.2
  have hfin : ∃ i, μ (s i) ≠ ∞ := ⟨0, measure_ne_top μ (s 0)⟩
  have htendsto : Tendsto (μ ∘ s) atTop (nhds (μ (⋂ n, s n))) :=
    tendsto_measure_iInter_atTop (fun n => (hmeas n).nullMeasurableSet) hanti hfin
  rw [hinter, measure_empty] at htendsto
  obtain ⟨N, hN⟩ := ((tendsto_order.mp htendsto).2 δ hδ).exists
  exact ⟨N, hN⟩

/-- **Measurable selection of an index whose value dominates a given bound** (the "select
`k(x)` measurably" step in Rudolph's proof: select `k(x)` measurably so that for all
`x ∈ A_1`, the selected window satisfies `≤ (ε/8)(j_{k(x)}(x) - i_{k(x)}(x) + 1)`).
Given `j k ω → ∞` pointwise (`hjtop`) and a measurable target `b : Ω → ℕ`, there is a
measurable `k : Ω → ℕ` with `b ω ≤ j (k ω) ω` at *every* `ω`. Proof: `k ω := Nat.find` of the
(pointwise) witness extracted from `hjtop`; measurability is exactly Mathlib's
`measurable_find` applied to the predicate `p ω n := b ω ≤ j n ω` (`{ω | p ω n}` is measurable
for each fixed `n` since `b`, `j n` are). -/
theorem exists_meas_dominating_index (j : ℕ → Ω → ℕ) (hj : ∀ k, Measurable (j k))
    (hjtop : ∀ ω, Tendsto (fun k => j k ω) atTop atTop) (b : Ω → ℕ) (hb : Measurable b) :
    ∃ k : Ω → ℕ, Measurable k ∧ ∀ ω, b ω ≤ j (k ω) ω := by
  classical
  have hex : ∀ ω, ∃ n, b ω ≤ j n ω := fun ω => ((tendsto_atTop.mp (hjtop ω)) (b ω)).exists
  refine ⟨fun ω => Nat.find (hex ω), ?_, fun ω => Nat.find_spec (hex ω)⟩
  exact measurable_find hex (fun n => measurableSet_le hb (hj n))

/-- Repeated measurable truncation gives nested domains with a bounded loss at each step. -/
private theorem exists_truncation_ladder {μ : Measure Ω} [IsProbabilityMeasure μ]
    (radius : ℕ → Ω → ℕ) (hrad : ∀ b, Measurable (radius b))
    {δ : ℝ≥0∞} (hδpos : 0 < δ) :
    ∃ (A : ℕ → Set Ω) (Bnd : ℕ → ℕ), A 0 = Set.univ ∧
      (∀ u, MeasurableSet (A u)) ∧ Antitone A ∧
      (∀ u, ∀ x ∈ A (u + 1), radius (Bnd u) x ≤ Bnd (u + 1)) ∧
      ∀ u, μ (A u \ A (u + 1)) < δ := by
  classical
  set Aux : ℕ → Set Ω × ℕ := fun u => Nat.rec (Set.univ, (1:ℕ))
      (fun _ prev =>
        if h : MeasurableSet prev.1 then
          (prev.1 ∩ {x | radius prev.2 x ≤
              (exists_meas_bound_sliver (μ := μ) h (radius prev.2) (hrad prev.2) hδpos).choose},
           (exists_meas_bound_sliver (μ := μ) h (radius prev.2) (hrad prev.2) hδpos).choose)
        else (∅, 1)) u with hAuxdef
  set A : ℕ → Set Ω := fun u => (Aux u).1 with hAdef
  set Bnd : ℕ → ℕ := fun u => (Aux u).2 with hBnddef
  have hA0 : A 0 = Set.univ := by simp [hAdef, hAuxdef]
  have hAmeas : ∀ u, MeasurableSet (A u) := by
    intro u
    induction u with
    | zero => simp [hAdef, hAuxdef]
    | succ u ih =>
      simp only [hAdef, hAuxdef] at ih ⊢
      rw [dite_eq_left ih]
      exact ih.inter (measurableSet_le (hrad _) measurable_const)
  have hAuxsucc : ∀ u, Aux (u + 1) =
      (A u ∩ {x | radius (Bnd u) x ≤
          (exists_meas_bound_sliver (μ := μ) (hAmeas u) (radius (Bnd u)) (hrad (Bnd u))
            hδpos).choose},
       (exists_meas_bound_sliver (μ := μ) (hAmeas u) (radius (Bnd u)) (hrad (Bnd u))
          hδpos).choose) := by
    intro u
    change (if h : MeasurableSet (A u) then _ else _) = _
    rw [dite_eq_left (hAmeas u)]
  have hBndeq : ∀ u, Bnd (u + 1) =
      (exists_meas_bound_sliver (μ := μ) (hAmeas u) (radius (Bnd u)) (hrad (Bnd u))
        hδpos).choose := fun u => congrArg Prod.snd (hAuxsucc u)
  have hAeq : ∀ u, A (u + 1) = A u ∩ {x | radius (Bnd u) x ≤ Bnd (u + 1)} := by
    intro u
    rw [hBndeq u]
    exact congrArg Prod.fst (hAuxsucc u)
  have hsliver : ∀ u, μ (A u ∩ {x | Bnd (u + 1) < radius (Bnd u) x}) < δ := by
    intro u
    rw [hBndeq u]
    exact (exists_meas_bound_sliver (μ := μ) (hAmeas u) (radius (Bnd u)) (hrad (Bnd u))
      hδpos).choose_spec
  have hAstep : ∀ u, A (u + 1) ⊆ A u := by
    intro u x hx; rw [hAeq u] at hx; exact hx.1
  have hAanti : Antitone A := antitone_nat_of_succ_le hAstep
  have hboundedOn : ∀ u, ∀ x ∈ A (u + 1), radius (Bnd u) x ≤ Bnd (u + 1) := by
    intro u x hx; rw [hAeq u] at hx; exact hx.2
  have hAdiff : ∀ u, A u \ A (u + 1) = A u ∩ {x | Bnd (u + 1) < radius (Bnd u) x} := by
    intro u
    rw [hAeq u]
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and, not_le]
    constructor
    · rintro ⟨hxA, hcond⟩; exact ⟨hxA, hcond hxA⟩
    · rintro ⟨hxA, hcond⟩; exact ⟨hxA, fun _ => hcond⟩
  exact ⟨A, Bnd, hA0, hAmeas, hAanti, hboundedOn, fun u => by
    rw [hAdiff u]
    exact hsliver u⟩

/-- **Lemma \ref{bvit} (Backward Vitali).** Given integer-valued `j_k(ω) → ∞`, there is a
measurable set `A` of measure `> 1 - ε` and a measurable choice `j : A → ℕ` (agreeing with
some `j_k(ω)` at each `ω ∈ A`) for which the windows `I_ω = {σ^i ω : |i| ≤ j(ω)}` are pairwise
disjoint across `ω ∈ A`.

Hypotheses `[StandardBorelSpace Ω] [IsProbabilityMeasure μ] [NullSingletonClass μ]` were added to
the paper's bare `Ergodic σ μ`; see the module note above (the statement is false without them).

**Status: fully proved, no `sorry`.** The non-periodicity foundation (`periodic_null`) and its
non-atomic scaffolding, plus Rudolph's greedy covering chain (`exists_subset_disjoint_iterates`,
`vitali_cover_third`, `vitali_cover_geometric`), are all proved; this lemma (Rudolph's backward
Vitali theorem) is the
final assembly, closed once `vitali_cover_geometric` was fixed to restrict `hgrow`/`hwB` to
`s < m` (see `CoverGeometric.lean`'s own docstring for that history — an earlier whole-`Ω`,
unbounded-`s` version was confirmed logically inconsistent for any useful `G`, via a standalone
Lean derivation, before being fixed).

**Proof strategy.** Clamp to `ε' := min ε 1` for clean `ENNReal` bookkeeping (the goal is monotone
in `ε`, so proving it for the smaller `ε'` suffices). Choose `G, m : ℕ` (via `exists_nat_gt`) large
enough that `vitali_cover_geometric`'s error bound `3(G+1)/(Gm) + 1/G < ε'/2`. Build a nested
sequence of domains `A 0 = univ ⊇ A 1 ⊇ A 2 ⊇ … ` (as a `Nat.rec`-defined state, mirroring the
`if h : MeasurableSet _ then … else …` pattern used for `Piece`/`R` in `CoverGeometric.lean`,
to avoid needing proof obligations *inside* the recursion): at step `u`, `Bnd u` is the truncation
threshold from the *previous* step, `jhatOf (Bnd u) := j (kOf (Bnd u) ·) ·` is the next candidate
(selected via `exists_meas_dominating_index` with **global** target `max 1 (G * Bnd u)` — the
`max 1` ensures `jhatOf b ω ≥ 1` unconditionally, needed for `vitali_cover_geometric`'s `hw1`), and
`A (u+1) := A u ∩ {x | jhatOf (Bnd u) x ≤ Bnd (u+1)}` where `Bnd (u+1)` is the threshold from
`exists_meas_bound_sliver` applied to `jhatOf (Bnd u)` on `A u` with budget
`δ := ε'/(4(m+1))` (so the sliver lost over all `m` steps is `< ε'/4` total, well inside budget).
Because `kOf`'s target is **global** (not just on the current domain), `jhatOf (Bnd(s+1))` is
`≥ G * Bnd(s+1)` *everywhere*, while `jhatOf (Bnd s)` is `≤ Bnd(s+1)` on the *retained* domain
`A(s+1)` — combining these on the *final* domain `A m` (which is `⊆ A(s+1)` for every `s < m`)
gives exactly the growth condition `vitali_cover_geometric` needs, now that it is correctly scoped
to `s < m` and `ω, ω' ∈ A₀ := A m`. Define the global `w s ω := if ω ∈ A m then jhatOf (Bnd s) ω
else 1` (junk `1` outside `A m`, harmless since `vitali_cover_geometric`'s output is guaranteed
`⊆ A m`) and `BndGlobal := (Finset.range (m+1)).sup Bnd + 1` for the uniform bound `hwB`. Apply
`vitali_cover_geometric` to get `Asel ⊆ A m` and `scale`; set `jω ω := w (scale ω) ω`, which for
`ω ∈ Asel ⊆ A m` unfolds to `j (kOf (Bnd (scale ω)) ω) ω`, giving the required `∃ k, jω ω = j k ω`.
Finally, bound the total uncovered measure `μ (univ \ ⋃ windows) ≤ μ (univ \ A m) + μ (A m \ ⋃
windows)`: the first term is `≤ m • δ < ε'/4` by telescoping the `m` sliver deletions (`A 0 \ A m
⊆ ⋃_{u<m} (A u \ A (u+1))`, proved by induction), the second is `< ε'/2` from
`vitali_cover_geometric`'s own bound; summing gives `< 3ε'/4 ≤ ε'`, and converting (via
`measure_add_sdiff` and `ENNReal.add_lt_add_left`/`add_lt_add_iff_right`, avoiding truncated
subtraction) yields `ENNReal.ofReal (1 - ε') < μ (⋃ windows)`, hence (since `ε' ≤ ε`, so
`1 - ε ≤ 1 - ε'`) the goal `ENNReal.ofReal (1 - ε) < μ (⋃ windows)`. -/
theorem backwardVitali [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ) (ε : ℝ) (hε : 0 < ε)
    (j : ℕ → Ω → ℕ) (hj : ∀ k, Measurable (j k))
    (hjtop : ∀ ω, Tendsto (fun k => j k ω) atTop atTop) :
    ∃ (A : Set Ω) (jω : Ω → ℕ), MeasurableSet A ∧ Measurable jω ∧
      (∀ ω ∈ A, ∃ k, jω ω = j k ω) ∧
      (A.PairwiseDisjoint fun ω => (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω)) ∧
      ENNReal.ofReal (1 - ε) <
        μ (⋃ ω ∈ A, (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω)) := by
  classical
  set ε' : ℝ := min ε 1 with hε'def
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le1 : ε' ≤ 1 := min_le_right _ _
  have hε'leε : ε' ≤ ε := min_le_left _ _
  obtain ⟨G, hG⟩ := exists_nat_gt (4 / ε')
  have hGpos : (0:ℝ) < G := lt_trans (by positivity) hG
  have hG1 : 1 ≤ G := by
    have : 0 < G := by exact_mod_cast hGpos
    omega
  have hGm1 : (1:ℝ) ≤ G := by exact_mod_cast hG1
  have hGbound : (4:ℝ) < (G:ℝ) * ε' := by
    rw [div_lt_iff₀ hε'pos] at hG; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (12 * ((G:ℝ) + 1) / ε')
  have hm1 : 1 ≤ m := by
    have hpos : (0:ℝ) < 12 * ((G:ℝ)+1) / ε' := by positivity
    have hmpos : (0:ℝ) < m := lt_trans hpos hm
    have : 0 < m := by exact_mod_cast hmpos
    omega
  have hmm1 : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hmbound : 12 * ((G:ℝ)+1) < (m:ℝ) * ε' := by
    rw [div_lt_iff₀ hε'pos] at hm; linarith
  have hfinal : 3 * ((G:ℝ)+1) / (G*m) + 1/G < ε' / 2 := by
    have h1 : 3 * ((G:ℝ)+1) / (G*m) ≤ 3 * ((G:ℝ)+1)/m :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    have h2 : 3 * ((G:ℝ)+1)/m < ε'/4 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h3 : 1/(G:ℝ) < ε'/4 := by
      rw [div_lt_div_iff₀ hGpos (by norm_num)]; nlinarith
    linarith
  set δr : ℝ := ε' / (4 * (m + 1)) with hδrdef
  have hδrpos : 0 < δr := by positivity
  set δ : ℝ≥0∞ := ENNReal.ofReal δr with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact ENNReal.ofReal_pos.mpr hδrpos
  set kOf : ℕ → Ω → ℕ := fun b =>
    (exists_meas_dominating_index j hj hjtop (fun _ => max 1 (G*b)) measurable_const).choose
    with hkOfdef
  have hkOf_spec : ∀ b ω, max 1 (G*b) ≤ j (kOf b ω) ω := fun b ω =>
    (exists_meas_dominating_index j hj hjtop
      (fun _ => max 1 (G*b)) measurable_const).choose_spec.2 ω
  have hkOf_meas : ∀ b, Measurable (kOf b) := fun b =>
    (exists_meas_dominating_index j hj hjtop (fun _ => max 1 (G*b)) measurable_const).choose_spec.1
  set jhatOf : ℕ → Ω → ℕ := fun b ω => j (kOf b ω) ω with hjhatOfdef
  have hjhatOf_meas : ∀ b, Measurable (jhatOf b) := by
    intro b
    have hf : Measurable (fun p : Ω × ℕ => j p.2 p.1) :=
      measurable_from_prod_countable_left (fun n => hj n)
    exact hf.comp (Measurable.prodMk measurable_id (hkOf_meas b))
  have hjhatOf_ge : ∀ b ω, G * b ≤ jhatOf b ω := by
    intro b ω
    calc G * b ≤ max 1 (G*b) := le_max_right _ _
      _ ≤ j (kOf b ω) ω := hkOf_spec b ω
  have hjhatOf_ge1 : ∀ b ω, 1 ≤ jhatOf b ω := by
    intro b ω
    calc (1:ℕ) ≤ max 1 (G*b) := le_max_left _ _
      _ ≤ j (kOf b ω) ω := hkOf_spec b ω
  obtain ⟨A, Bnd, hA0, hAmeas, hAanti, hboundedOn, hsliver⟩ :=
    exists_truncation_ladder (μ := μ) jhatOf hjhatOf_meas hδpos
  have hgrow_final : ∀ s, s < m → ∀ ω ω', ω ∈ A m → ω' ∈ A m →
      G * jhatOf (Bnd s) ω ≤ jhatOf (Bnd (s+1)) ω' := by
    intro s hs ω ω' hω hω'
    have hωs1 : ω ∈ A (s+1) := hAanti (by omega : s+1 ≤ m) hω
    have h1 : jhatOf (Bnd s) ω ≤ Bnd (s+1) := hboundedOn s ω hωs1
    have h2 : G * Bnd (s+1) ≤ jhatOf (Bnd (s+1)) ω' := hjhatOf_ge (Bnd (s+1)) ω'
    calc G * jhatOf (Bnd s) ω ≤ G * Bnd (s+1) := by gcongr
      _ ≤ jhatOf (Bnd (s+1)) ω' := h2
  set BndGlobal : ℕ := (Finset.range (m+1)).sup Bnd + 1 with hBndGdef
  have hBndGle : ∀ u, u ≤ m → Bnd u ≤ BndGlobal := by
    intro u hu
    have : Bnd u ≤ (Finset.range (m+1)).sup Bnd :=
      Finset.le_sup (Finset.mem_range.mpr (by omega))
    omega
  set w : ℕ → Ω → ℕ := fun s ω => if ω ∈ A m then jhatOf (Bnd s) ω else 1 with hwdef
  have hwmeas : ∀ s, Measurable (w s) := fun s =>
    Measurable.ite (hAmeas m) (hjhatOf_meas (Bnd s)) measurable_const
  have hw1 : ∀ s ω, 1 ≤ w s ω := by
    intro s ω
    simp only [hwdef]
    split
    · exact hjhatOf_ge1 (Bnd s) ω
    · exact le_refl 1
  have hwB : ∀ s, s < m → ∀ ω, w s ω ≤ BndGlobal := by
    intro s hs ω
    simp only [hwdef]
    split
    · rename_i hωm
      have h1 : jhatOf (Bnd s) ω ≤ Bnd (s+1) := hboundedOn s ω (hAanti (by omega : s+1 ≤ m) hωm)
      calc jhatOf (Bnd s) ω ≤ Bnd (s+1) := h1
        _ ≤ BndGlobal := hBndGle (s+1) (by omega)
    · omega
  have hgrow : ∀ s, s < m → ∀ ω ω', ω ∈ A m → ω' ∈ A m → G * w s ω ≤ w (s+1) ω' := by
    intro s hs ω ω' hω hω'
    simp only [hwdef, ite_eq_left hω, ite_eq_left hω']
    exact hgrow_final s hs ω ω' hω hω'
  obtain ⟨Asel, scale, hAselsub, hAselmeas, hscalemeas, hscalelt, hdisj, hcov⟩ :=
    vitali_cover_geometric μ σ hσ (A m) (hAmeas m) m hm1 w hwmeas BndGlobal hwB hw1 G hG1 hgrow
  set jω : Ω → ℕ := fun ω => w (scale ω) ω with hjωdef
  have hjωmeas : Measurable jω := by
    have hf : Measurable (fun p : Ω × ℕ => w p.2 p.1) :=
      measurable_from_prod_countable_left (fun n => hwmeas n)
    exact hf.comp (Measurable.prodMk measurable_id hscalemeas)
  have hjω_eq_j : ∀ ω ∈ Asel, ∃ k, jω ω = j k ω := by
    intro ω hω
    have hωm : ω ∈ A m := hAselsub hω
    refine ⟨kOf (Bnd (scale ω)) ω, ?_⟩
    change w (scale ω) ω = j (kOf (Bnd (scale ω)) ω) ω
    simp only [hwdef, ite_eq_left hωm, hjhatOfdef]
  refine ⟨Asel, jω, hAselmeas, hjωmeas, hjω_eq_j, hdisj, ?_⟩
  -- final measure bookkeeping
  have htelescope : ∀ k, μ (A 0 \ A k) ≤ ∑ u ∈ Finset.range k, μ (A u \ A (u+1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsub : A 0 \ A (k+1) ⊆ (A 0 \ A k) ∪ (A k \ A (k+1)) := by
        intro x hx
        by_cases hxk : x ∈ A k
        · exact Or.inr ⟨hxk, hx.2⟩
        · exact Or.inl ⟨hx.1, hxk⟩
      calc μ (A 0 \ A (k+1)) ≤ μ ((A 0 \ A k) ∪ (A k \ A (k+1))) := measure_mono hsub
        _ ≤ μ (A 0 \ A k) + μ (A k \ A (k+1)) := measure_union_le _ _
        _ ≤ (∑ u ∈ Finset.range k, μ (A u \ A (u+1))) + μ (A k \ A (k+1)) := by gcongr
        _ = ∑ u ∈ Finset.range (k+1), μ (A u \ A (u+1)) := by rw [Finset.sum_range_succ]
  have hunivAm : μ (Set.univ \ A m) ≤ (m : ℝ≥0∞) * δ := by
    have h1 := htelescope m
    rw [hA0] at h1
    have h2 : ∑ u ∈ Finset.range m, μ (A u \ A (u+1)) ≤
        ∑ _u ∈ Finset.range m, δ :=
      Finset.sum_le_sum (fun u _ => (hsliver u).le)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    exact h1.trans h2
  have hmdelta_lt : (m:ℝ≥0∞) * δ < ENNReal.ofReal (ε'/4) := by
    rw [hδdef, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
    rw [hδrdef, ← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hunivAm_lt : μ (Set.univ \ A m) < ENNReal.ofReal (ε'/4) :=
    lt_of_le_of_lt hunivAm hmdelta_lt
  have hcov_lt : μ (A m \ ⋃ ω ∈ Asel, (fun t => zIter σ t ω) ''
      Set.Icc (-(w (scale ω) ω:ℤ)) (w (scale ω) ω))
      < ENNReal.ofReal (ε'/2) := by
    refine lt_of_le_of_lt hcov ?_
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
    linarith
  set U : Set Ω := ⋃ ω ∈ Asel, (fun t => zIter σ t ω) '' Set.Icc (-(jω ω:ℤ)) (jω ω) with hUdef
  have hUeq : U = ⋃ ω ∈ Asel, (fun t => zIter σ t ω) ''
      Set.Icc (-(w (scale ω) ω:ℤ)) (w (scale ω) ω) := rfl
  have hUmeas : MeasurableSet U := measurableSet_iUnion_win σ hAselmeas jω hjωmeas
  have hUsub : Set.univ \ U ⊆ (Set.univ \ A m) ∪ (A m \ U) := by
    intro x hx
    by_cases hxm : x ∈ A m
    · exact Or.inr ⟨hxm, hx.2⟩
    · exact Or.inl ⟨hx.1, hxm⟩
  have hstep : μ (Set.univ \ U) ≤ μ (Set.univ \ A m) + μ (A m \ U) :=
    le_trans (measure_mono hUsub) (measure_union_le _ _)
  have hUcov : μ (A m \ U) < ENNReal.ofReal (ε'/2) := by rw [hUeq]; exact hcov_lt
  have hsum : μ (Set.univ \ A m) + μ (A m \ U) < ENNReal.ofReal (ε'/4) + ENNReal.ofReal (ε'/2) :=
    ENNReal.add_lt_add hunivAm_lt hUcov
  have heq4 : ENNReal.ofReal (ε'/4) + ENNReal.ofReal (ε'/2) = ENNReal.ofReal (3*ε'/4) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  have hle34 : ENNReal.ofReal (3*ε'/4) ≤ ENNReal.ofReal ε' := ENNReal.ofReal_le_ofReal (by linarith)
  have htotal : μ (Set.univ \ U) < ENNReal.ofReal ε' := by
    calc μ (Set.univ \ U) ≤ μ (Set.univ \ A m) + μ (A m \ U) := hstep
      _ < ENNReal.ofReal (ε'/4) + ENNReal.ofReal (ε'/2) := hsum
      _ = ENNReal.ofReal (3*ε'/4) := heq4
      _ ≤ ENNReal.ofReal ε' := hle34
  have hadd : μ U + μ (Set.univ \ U) = 1 := by
    have := measure_add_sdiff (μ := μ) hUmeas.nullMeasurableSet (Set.univ : Set Ω)
    rwa [Set.union_univ, measure_univ] at this
  have hsplit : ENNReal.ofReal (1 - ε') + ENNReal.ofReal ε' = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    norm_num
  have hlt : ENNReal.ofReal (1 - ε') + μ (Set.univ \ U) <
      ENNReal.ofReal (1 - ε') + ENNReal.ofReal ε' :=
    ENNReal.add_lt_add_left (by finiteness) htotal
  rw [hsplit, ← hadd] at hlt
  have hfin : ENNReal.ofReal (1 - ε') < μ U :=
    (ENNReal.add_lt_add_iff_right (by finiteness)).mp hlt
  calc ENNReal.ofReal (1 - ε) ≤ ENNReal.ofReal (1 - ε') :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ < μ U := hfin

end MultiplicativeErgodic
