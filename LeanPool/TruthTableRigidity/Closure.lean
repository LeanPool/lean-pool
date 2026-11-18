/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import LeanPool.TruthTableRigidity.Approx

/-!
# Closure properties of tt-functionals

* functionals given by a primitive recursive truth table on a primitive recursive
  number of queries are tt-functionals (`isTTFunctional_of_use`);
* joins `X ↦ Φ₁ X ⊕ Φ₂ X` (`IsTTFunctional.join`);
* constant functionals with a tt-computable value (`isTTFunctional_const`);
* iteration: `X ↦ (m ↦ (Θ^[m] X) j)` (`IsTTFunctional.iterate`);
* every tt-functional is continuous, and there are only countably many.
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity Encodable
open scoped BigOperators

/-- The recursive join `A ⊕ B`. -/
def ojoin (A B : Oracle) : Oracle := fun n => if n % 2 = 0 then A (n / 2) else B (n / 2)

theorem ojoin_even (A B : Oracle) (n : ℕ) : ojoin A B (2 * n) = A n := by
  simp [ojoin]

theorem ojoin_odd (A B : Oracle) (n : ℕ) : ojoin A B (2 * n + 1) = B n := by
  simp [ojoin, Nat.add_mod]
  congr 1
  omega

/-! ### Lists -/

theorem filterMap_id_map_some {α : Type*} (l : List (Option α))
    (h : (l.filterMap id).length = l.length) : (l.filterMap id).map some = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases a with
    | none =>
      have := List.length_filterMap_le id t
      rw [List.filterMap_cons_none rfl, List.length_cons] at h
      omega
    | some a =>
      rw [List.filterMap_cons_some (f := id) rfl, List.length_cons, List.length_cons] at h
      rw [List.filterMap_cons_some (f := id) rfl, List.map_cons, ih (by omega)]

theorem pre_prefix (X : Oracle) {m M : ℕ} (h : m ≤ M) : pre X m <+: pre X M := by
  rw [List.prefix_iff_eq_take, length_pre]
  simp only [pre]
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem map_pre_prefix (X : Oracle) {m M : ℕ} (h : m ≤ M) {σ : List (Option Bool)}
    (hσ : (pre X M).map some <+: σ) : (pre X m).map some <+: σ :=
  ((pre_prefix X h).map some).trans hσ

theorem take_eq_of_pre_prefix {X : Oracle} {M : ℕ} {σ : List (Option Bool)}
    (hσ : (pre X M).map some <+: σ) : σ.take M = (pre X M).map some := by
  have := List.prefix_iff_eq_take.mp hσ
  simpa [length_pre] using this.symm

theorem getElem?_of_pre_prefix {X : Oracle} {M : ℕ} {σ : List (Option Bool)}
    (hσ : (pre X M).map some <+: σ) {i : ℕ} (hi : i < M) : σ[i]? = some (some (X i)) := by
  have h1 := take_eq_of_pre_prefix hσ
  have : (σ.take M)[i]? = σ[i]? := by rw [List.getElem?_take]; simp [hi]
  rw [← this, h1]
  simp [getElem?_pre, hi]

theorem pre_prefix_of_getElem {Y : Oracle} {N : ℕ} {L : List (Option Bool)}
    (h : ∀ i < N, L[i]? = some (some (Y i))) : (pre Y N).map some <+: L := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro i
  simp only [List.length_map, length_pre, List.getElem?_take, List.getElem?_map, getElem?_pre]
  split_ifs with hi
  · rw [h i hi]; rfl
  · rfl

/-! ### Truth tables -/

/-- A functional whose `n`-th bit is a primitive recursive function `t` of `n` and of the
prefix of the argument of primitive recursive length `u n` is a tt-functional. -/
theorem isTTFunctional_of_use {Φ : Oracle → Oracle} {u : ℕ → ℕ} {t : ℕ → List Bool → Bool}
    (hu : Primrec u) (ht : Primrec₂ t) (hΦ : ∀ X n, Φ X n = t n (pre X (u n))) :
    IsTTFunctional Φ := by
  let τ : List (Option Bool) → ℕ → List Bool := fun σ n => (σ.take (u n)).filterMap id
  let H : List (Option Bool) → ℕ → Option Bool := fun σ n =>
    cond ((τ σ n).length == u n) (some (t n (τ σ n))) none
  have hτ : Primrec₂ τ :=
    Primrec.listFilterMap (Primrec.list_take.comp (hu.comp Primrec.snd) Primrec.fst)
      (Primrec.snd : Primrec (Prod.snd : (List (Option Bool) × ℕ) × Option Bool → Option Bool)).to₂
  have key : ∀ X σ n, Compat σ X → (τ σ n).length = u n → τ σ n = pre X (u n) := by
    intro X σ n hσ hlen
    have hle : (σ.take (u n)).length ≤ u n := by simp
    have hle2 := List.length_filterMap_le id (σ.take (u n))
    have heq : (τ σ n).length = (σ.take (u n)).length := by
      simp only [τ] at hlen ⊢; omega
    have hms := filterMap_id_map_some _ heq
    apply List.ext_getElem?
    intro i
    rw [getElem?_pre]
    split_ifs with hi
    · have h1 : (σ.take (u n))[i]? = σ[i]? := by simp [hi]
      have h2 : ((τ σ n).map some)[i]? = σ[i]? := by
        rw [← h1]; exact congrArg (·[i]?) hms
      rw [List.getElem?_map] at h2
      obtain ⟨b, hb⟩ : ∃ b, (τ σ n)[i]? = some b := by
        exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [hb] at h2 ⊢
      simp only [Option.map_some] at h2
      rw [hσ i b h2.symm]
    · exact List.getElem?_eq_none (by omega)
  have happ : IsApprox Φ H := by
    refine ⟨?_, ?_, ?_⟩
    · exact Primrec.cond (Primrec.beq.comp (Primrec.list_length.comp hτ) (hu.comp Primrec.snd))
        (Primrec.option_some.comp (ht.comp Primrec.snd hτ)) (Primrec.const none)
    · intro X σ n b hσ hb
      simp only [H] at hb
      cases hl : ((τ σ n).length == u n) with
      | false => rw [hl] at hb; simp at hb
      | true =>
        rw [hl] at hb
        simp only [Bool.cond_true, Option.some.injEq] at hb
        rw [hΦ, ← key X σ n hσ (by simpa using hl), hb]
    · intro X n
      refine ⟨u n, fun σ _ hσ => ?_⟩
      have hτX : τ σ n = pre X (u n) := by
        simp only [τ, take_eq_of_pre_prefix hσ]
        simp
      simp [H, hτX, length_pre]
  exact happ.isTTFunctional

/-! ### Joins and constants -/

theorem IsTTFunctional.join {Φ₁ Φ₂ : Oracle → Oracle} (h₁ : IsTTFunctional Φ₁)
    (h₂ : IsTTFunctional Φ₂) : IsTTFunctional fun X => ojoin (Φ₁ X) (Φ₂ X) := by
  have g₁ : UTot fun X n => bv (Φ₁ X (n / 2)) :=
    UTot.precomp h₁ (Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp
  have g₂ : UTot fun X n => bv (Φ₂ X (n / 2)) :=
    UTot.precomp h₂ (Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp
  let sel : ℕ → ℕ → ℕ := fun n p => cond (n % 2 == 0) p.unpair.1 p.unpair.2
  have hsel : Computable₂ sel :=
    (Primrec.cond (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2))
      (Primrec.const 0)) (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))).to_comp
  have := UTot.map₂ hsel UTot.id (UTot.pair g₁ g₂)
  refine isTTFunctional_of_utot ((show (fun X n => sel n (Nat.pair (bv (Φ₁ X (n / 2)))
      (bv (Φ₂ X (n / 2))))) = fun X n => bv (ojoin (Φ₁ X) (Φ₂ X) n) from ?_) ▸ this)
  funext X n
  simp only [sel, ojoin, Nat.unpair_pair]
  by_cases h : n % 2 = 0
  · simp [h]
  · have hb : (n % 2 == 0) = false := beq_false_of_ne h
    simp [h, hb]

/-- `A` is *tt-computable*: `A ≤tt ∅`. -/
def TTComputable (A : Oracle) : Prop := TTReducible A (fun _ => false)

theorem isTTFunctional_const {P : Oracle} (hP : TTComputable P) :
    IsTTFunctional fun _ => P := by
  obtain ⟨Ψ, ⟨e, he⟩, rfl⟩ := hP
  refine ⟨substCode e .zero, fun X => ?_⟩
  rw [eval_substCode]
  change OracleCode.eval (oracleFunction (fun _ => false)) e = _
  exact he _

theorem TTComputable.ttReducible {P : Oracle} (hP : TTComputable P) (B : Oracle) :
    TTReducible P B :=
  ⟨fun _ => P, isTTFunctional_const hP, rfl⟩

theorem TTComputable.apply {P : Oracle} (hP : TTComputable P) {Φ : Oracle → Oracle}
    (hΦ : IsTTFunctional Φ) : TTComputable (Φ P) :=
  TTReducible.trans ⟨Φ, hΦ, rfl⟩ hP

theorem TTComputable.of_ttReducible {A P : Oracle} (h : TTReducible A P) (hP : TTComputable P) :
    TTComputable A :=
  TTReducible.trans h hP

theorem ttComputable_const_false : TTComputable fun _ => false := TTReducible.refl _

/-! ### Iteration -/

/-- One step of the finite approximation of a functional. -/
def stepL (H : List (Option Bool) → ℕ → Option Bool) (σ : List (Option Bool)) :
    List (Option Bool) :=
  (List.range σ.length).map (H σ)

theorem stepL_compat {Θ : Oracle → Oracle} {H} (hH : IsApprox Θ H) {σ : List (Option Bool)}
    {X : Oracle} (hσ : Compat σ X) : Compat (stepL H σ) (Θ X) := by
  intro i b hi
  simp only [stepL, List.getElem?_map] at hi
  rw [Option.map_eq_some_iff] at hi
  obtain ⟨k, hk, hk'⟩ := hi
  have : k = i := by
    by_cases hi : i < σ.length
    · rw [List.getElem?_range hi] at hk
      exact (Option.some.inj hk).symm
    · rw [List.getElem?_eq_none (by simp; omega)] at hk
      simp at hk
  subst this
  exact hH.sound X σ k b hσ hk'

theorem iterate_stepL_compat {Θ : Oracle → Oracle} {H} (hH : IsApprox Θ H) (m : ℕ) :
    ∀ {σ : List (Option Bool)} {X : Oracle}, Compat σ X →
      Compat ((stepL H)^[m] σ) (Θ^[m] X) := by
  induction m with
  | zero => intro σ X h; exact h
  | succ m ih =>
    intro σ X h
    simp only [Function.iterate_succ_apply]
    exact ih (stepL_compat hH h)

theorem stepL_prefix {Θ : Oracle → Oracle} {H} (hH : IsApprox Θ H) (X : Oracle) (N : ℕ) :
    ∃ M, ∀ σ, Compat σ X → (pre X M).map some <+: σ → (pre (Θ X) N).map some <+: stepL H σ := by
  choose Mb hMb using hH.complete X
  refine ⟨N + ∑ i ∈ Finset.range N, Mb i, fun σ hc hσ => ?_⟩
  have hlen : N + ∑ i ∈ Finset.range N, Mb i ≤ σ.length := by
    simpa [length_pre] using hσ.length_le
  apply pre_prefix_of_getElem
  intro i hi
  have hMi : Mb i ≤ N + ∑ i ∈ Finset.range N, Mb i :=
    le_add_left (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi))
  have hsome := hMb i σ hc (map_pre_prefix X hMi hσ)
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
  have hval := hH.sound X σ i b hc hb
  simp only [stepL, List.getElem?_map, List.getElem?_range (show i < σ.length by omega),
    Option.map_some, hb, hval]

theorem iterate_stepL_prefix {Θ : Oracle → Oracle} {H} (hH : IsApprox Θ H) (m : ℕ) :
    ∀ (X : Oracle) (N : ℕ), ∃ M, ∀ σ, Compat σ X → (pre X M).map some <+: σ →
      (pre (Θ^[m] X) N).map some <+: (stepL H)^[m] σ := by
  induction m with
  | zero => intro X N; exact ⟨N, fun σ _ h => h⟩
  | succ m ih =>
    intro X N
    obtain ⟨M', hM'⟩ := ih (Θ X) N
    obtain ⟨M, hM⟩ := stepL_prefix hH X M'
    refine ⟨M, fun σ hc hσ => ?_⟩
    simp only [Function.iterate_succ_apply]
    exact hM' _ (stepL_compat hH hc) (hM σ hc hσ)

theorem stepL_primrec {H : List (Option Bool) → ℕ → Option Bool} (hH : Primrec₂ H) :
    Primrec (stepL H) :=
  Primrec.list_map (Primrec.list_range.comp Primrec.list_length) hH

/-- Iterating a tt-functional and reading off a fixed bit is a tt-functional. -/
theorem IsTTFunctional.iterate {Θ : Oracle → Oracle} (hΘ : IsTTFunctional Θ) (j : ℕ) :
    IsTTFunctional fun X m => (Θ^[m] X) j := by
  obtain ⟨H, hH⟩ := hΘ.exists_approx
  let H' : List (Option Bool) → ℕ → Option Bool := fun σ m => ((stepL H)^[m] σ)[j]?.bind id
  refine IsApprox.isTTFunctional (H := H') ⟨?_, ?_, ?_⟩
  · have hit : Primrec₂ fun (σ : List (Option Bool)) (m : ℕ) => (stepL H)^[m] σ :=
      Primrec.nat_iterate Primrec.snd Primrec.fst ((stepL_primrec hH.primrec).comp Primrec.snd).to₂
    exact Primrec.option_bind (Primrec.list_getElem?.comp hit (Primrec.const j))
      (Primrec.snd : Primrec (Prod.snd : (List (Option Bool) × ℕ) × Option Bool → Option Bool)).to₂
  · intro X σ m b hσ hb
    simp only [H'] at hb
    rw [Option.bind_eq_some_iff] at hb
    obtain ⟨o, ho, ho'⟩ := hb
    simp only [id] at ho'
    rw [ho'] at ho
    exact iterate_stepL_compat hH m hσ j b ho
  · intro X m
    obtain ⟨M, hM⟩ := iterate_stepL_prefix hH m X (j + 1)
    refine ⟨M, fun σ hc hσ => ?_⟩
    have := getElem?_of_pre_prefix (hM σ hc hσ) (Nat.lt_succ_self j)
    simp [H', this]

/-! ### Continuity and countability -/

/-- The cylinder of oracles agreeing with `X` below `M`. -/
def cyl (X : Oracle) (M : ℕ) : Set Oracle := {Y | ∀ i < M, Y i = X i}

theorem isOpen_cyl (X : Oracle) (M : ℕ) : IsOpen (cyl X M) := by
  have : cyl X M = ⋂ i ∈ Finset.range M, (fun Y : Oracle => Y i) ⁻¹' {X i} := by
    ext Y; simp [cyl]
  rw [this]
  exact isOpen_biInter_finset fun i _ =>
    (isOpen_discrete _).preimage (continuous_apply i)

theorem mem_cyl (X : Oracle) (M : ℕ) : X ∈ cyl X M := fun _ _ => rfl

theorem pre_eq_of_mem_cyl {X Y : Oracle} {M : ℕ} (h : Y ∈ cyl X M) : pre Y M = pre X M := by
  simp only [pre]
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- A functional each of whose output bits depends only on finitely many input bits is
continuous. -/
theorem continuous_of_locally_determined {Φ : Oracle → Oracle}
    (h : ∀ X n, ∃ M, ∀ Y ∈ cyl X M, Φ Y n = Φ X n) : Continuous Φ := by
  apply continuous_pi
  intro n
  rw [continuous_iff_continuousAt]
  intro X
  obtain ⟨M, hM⟩ := h X n
  have hev : (fun Y => Φ Y n) =ᶠ[nhds X] fun _ => Φ X n :=
    Filter.eventually_of_mem ((isOpen_cyl X M).mem_nhds (mem_cyl X M)) hM
  exact (continuousAt_congr hev).mpr continuousAt_const

theorem IsTTFunctional.continuous {Φ : Oracle → Oracle} (hΦ : IsTTFunctional Φ) :
    Continuous Φ := by
  obtain ⟨H, hH⟩ := hΦ.exists_approx
  apply continuous_of_locally_determined
  intro X n
  obtain ⟨M, hM⟩ := hH.complete X n
  refine ⟨M, fun Y hY => ?_⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hM _ (compat_pre X M) (List.prefix_refl _))
  rw [hH.sound X _ n b (compat_pre X M) hb]
  rw [← pre_eq_of_mem_cyl hY] at hb
  exact hH.sound Y _ n b (compat_pre Y M) hb

theorem countable_ttFunctionals : {Φ : Oracle → Oracle | IsTTFunctional Φ}.Countable := by
  have : {Φ : Oracle → Oracle | IsTTFunctional Φ} ⊆
      ⋃ c : OracleCode, {Φ | ∀ X, OracleCode.eval (oracleFunction X) c = oracleFunction (Φ X)} := by
    intro Φ ⟨c, hc⟩
    exact Set.mem_iUnion.mpr ⟨c, hc⟩
  refine (Set.countable_iUnion fun c => ?_).mono this
  apply Set.Subsingleton.countable
  intro Φ hΦ Ψ hΨ
  funext X
  apply oracleFunction_injective
  rw [← hΦ X, ← hΨ X]

instance : Countable {Φ : Oracle → Oracle // IsTTFunctional Φ} :=
  countable_ttFunctionals.to_subtype

theorem countable_ttReducible (B : Oracle) : {A | TTReducible A B}.Countable := by
  have : {A | TTReducible A B} ⊆ (fun Φ : Oracle → Oracle => Φ B) '' {Φ | IsTTFunctional Φ} := by
    rintro A ⟨Φ, hΦ, rfl⟩
    exact ⟨Φ, hΦ, rfl⟩
  exact (countable_ttFunctionals.image _).mono this

end TT
