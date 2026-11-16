/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Constraints.GroundBounds
public import LeanPool.DeciSigma1.Full.Models.Observations
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Finite solutions satisfying finitely many ground bounds

Finitely many ground bounds that hold together in some covariant solution of a constraint hold
together in a finite solution, provided the constraint has a finite solution
(`finiteBoundPinning`). Each bound is compiled into one-sided constructor literals on fresh
variables (`Constraints.GroundCompiler.compile`). The compiled literals form a ranked extension,
so the extended constraint has a finite solution; the bounds are added one at a time, and the
finite solution is then restricted to the original variables. A constraint over an arbitrary type
of variables is reduced to the finitely many variables that occur in it and in the bounds.

## Main declarations

- `Pinning.realize_bounds`: realization of ground bounds over the variables `Fin k`.
- `finiteBoundPinning`: every flat constraint has the property `FiniteBoundPinning`.
-/

@[expose] public section


namespace DeciSigma1.Full.Models.Pinning
open DeciSigma1.Semantics DeciSigma1.Constraints

variable {n : ℕ}

/-- Finitely many ground bounds that hold together in some solution of `Γ` hold together in a
finite solution, provided `Γ` has a finite solution. -/
theorem realize_bounds {k : ℕ} (B : List (GroundBound n (Fin k))) (Γ : List (LitT n (Fin k)))
    (hf : ∃ σ : Fin k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ)
    (hs : ∃ ρ, Covariant.Sat ρ Γ ∧ ∀ b ∈ B, b.Holds ρ) :
    ∃ σ : Fin k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ ∧
      ∀ b ∈ B, b.Holds (FTree.toTree ∘ σ) := by
  cases B with
  | nil => obtain ⟨σ, hσ⟩ := hf; exact ⟨σ, hσ, by simp⟩
  | cons b B =>
    obtain ⟨ρ, hΓ, hb⟩ := hs
    let ρ' := GroundCompiler.extend b.tree ρ
    let ψ := lift Γ _ ++ GroundCompiler.compile b.lower (Fin.castAdd _ b.var)
      b.tree (GroundCompiler.occurrenceVar b.tree)
    have hr : ρ' ∘ Fin.castAdd _ = ρ := funext (GroundCompiler.extend_original b.tree ρ)
    have hs' : Covariant.Sat ρ' ψ :=
      (sat_append ..).mpr ⟨(sat_lift ..).mpr (hr.symm ▸ hΓ),
        GroundCompiler.complete b.lower b.tree b.var ρ (hb b (by simp))⟩
    have hf' := (Ranked.Extension.satFin_iff
      (GroundCompiler.extension b.lower b.tree b.var Γ)).mpr ⟨⟨ρ', hs'⟩, hf⟩
    obtain ⟨σ, hσ, hB⟩ := realize_bounds (B.map (GroundBound.map (Fin.castAdd _))) ψ hf'
      ⟨ρ', hs', by
        simp only [List.forall_mem_map, GroundBound.holds_map, hr]
        intro q hq; exact hb q (by simp [hq])⟩
    obtain ⟨hbase, hbound⟩ := (sat_append ..).mp hσ
    refine ⟨σ ∘ Fin.castAdd _, (sat_lift ..).mp hbase, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact GroundCompiler.sound q.lower q.tree (Fin.castAdd _ q.var)
        (GroundCompiler.occurrenceVar q.tree) hbound
    · exact hB (q.map (Fin.castAdd _)) (List.mem_map.mpr ⟨q, hq, rfl⟩)
termination_by B.length

/-- Every flat constraint over a finite type of variables has the property
`FiniteBoundPinning`. -/
theorem finiteBoundPinning_fintype {V : Type*} [Finite V] (Γ : List (LitT n V)) :
    FiniteBoundPinning Γ := by
  classical
  let := Fintype.ofFinite V
  classical
  intro hf B hs
  let e := Fintype.equivFin V
  obtain ⟨δ, hδfin, hδ⟩ := hf
  choose D hD using hδfin
  obtain ⟨ρ, hΓ, hb⟩ := hs
  have he (τ : V → Tree n) : (τ ∘ e.symm) ∘ e = τ := by funext v; simp
  obtain ⟨σ, hσ, hB⟩ := realize_bounds (B.map (GroundBound.map e))
    (Γ.map (LitT.map e))
    ⟨D ∘ e.symm, (sat_rename ..).mpr (by
      simpa only [Function.comp_def, Equiv.symm_apply_apply, hD, ← sat_false] using hδ)⟩
    ⟨ρ ∘ e.symm, (sat_rename ..).mpr (by simpa only [he, ← sat_false] using hΓ), by
      simpa only [List.forall_mem_map, GroundBound.holds_map, he] using hb⟩
  refine ⟨FTree.toTree ∘ σ ∘ e, fun v => ⟨_, rfl⟩, ?_, ?_⟩
  · exact (sat_false ..).mpr ((sat_rename e (FTree.toTree ∘ σ) Γ).mp hσ)
  · intro b hm
    exact hB (b.map e) (List.mem_map.mpr ⟨b, hm, rfl⟩)

end DeciSigma1.Full.Models.Pinning

namespace DeciSigma1.Full.Models
open DeciSigma1.Constraints DeciSigma1.Semantics

variable {n : ℕ}

namespace Pinning

/-- The variables of a literal. -/
def vars {V : Type*} : LitT n V → List V
  | .le u v => [u, v]
  | .fLe a u | .leF u a => (List.finRange n).map a ++ [u]
  | .eqBot u | .eqTop u => [u]

theorem holds_congr {V : Type*} (c : Fin n → Bool) (l : LitT n V)
    {ρ τ : V → Semantics.Tree n} (h : ∀ v ∈ vars l, ρ v = τ v) :
    HoldsT c ρ l ↔ HoldsT c τ l := by
  cases l with
  | le u v =>
    simp only [vars, List.forall_mem_cons] at h
    simp_all [HoldsT]
  | fLe a u =>
    have hu := h u (by simp [vars])
    have ha : ρ ∘ a = τ ∘ a := by
      funext i
      exact h (a i) (by simp [vars])
    simp only [HoldsT, hu, ha]
  | leF u a =>
    have hu := h u (by simp [vars])
    have ha : ρ ∘ a = τ ∘ a := by
      funext i
      exact h (a i) (by simp [vars])
    simp only [HoldsT, hu, ha]
  | eqBot u => simp only [vars, List.forall_mem_cons] at h; simp_all [HoldsT]
  | eqTop u => simp only [vars, List.forall_mem_cons] at h; simp_all [HoldsT]

end Pinning

/-- Every flat constraint has the property `FiniteBoundPinning`, over any type of variables. -/
theorem finiteBoundPinning {V : Type*} (Γ : List (LitT n V)) : FiniteBoundPinning Γ := by
  classical
  intro hf B hs
  let S : Finset V := (Γ.flatMap Pinning.vars ++ B.map GroundBound.var).toFinset
  let W := Option {v // v ∈ S}
  let tag : V → W := fun v => if h : v ∈ S then some ⟨v, h⟩ else none
  let pull (ρ : V → Semantics.Tree n) : W → Semantics.Tree n := fun w =>
    match w with
    | none => Tree.bot
    | some v => ρ v.val
  have htag (ρ : V → Semantics.Tree n) (v : V) (hv : v ∈ S) : pull ρ (tag v) = ρ v := by
    simp [pull, tag, hv]
  have hvar {l : LitT n V} (hl : l ∈ Γ) {v : V} (hv : v ∈ Pinning.vars l) :
      v ∈ S := by
    simp only [S, List.mem_toFinset, List.mem_append]
    exact Or.inl (List.mem_flatMap.mpr ⟨l, hl, hv⟩)
  have hbvar {b : GroundBound n V} (hb : b ∈ B) : b.var ∈ S := by
    simp only [S, List.mem_toFinset, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨b, hb, rfl⟩)
  let Γ' := Γ.map (LitT.map tag)
  let B' : List (GroundBound n W) := B.map fun b => ⟨tag b.var, b.lower, b.tree⟩
  have hsat (ρ : V → Semantics.Tree n) (hρ : SatT (fun _ => false) ρ Γ) :
      SatT (fun _ => false) (pull ρ) Γ' := by
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
    rw [holdsT_map]
    exact (Pinning.holds_congr _ l0 (fun v hv => htag ρ v (hvar hl0 hv))).mpr (hρ l0 hl0)
  have hf' : SatisfiableIn FiniteTop (fun _ => false) Γ' := by
    obtain ⟨ρ, hc, ht⟩ := hf
    refine ⟨pull ρ, ?_, hsat ρ ht⟩
    intro w
    cases w with
    | none => exact ⟨.bot, rfl⟩
    | some v => exact hc v.val
  obtain ⟨ρ, ht, hb⟩ := hs
  have hb' : ∀ b ∈ B', b.Holds (pull ρ) := by
    intro b hm
    obtain ⟨b0, hm0, rfl⟩ := List.mem_map.mp hm
    simpa only [GroundBound.Holds, htag ρ b0.var (hbvar hm0)] using hb b0 hm0
  obtain ⟨τ, hc, ht, hbτ⟩ := Pinning.finiteBoundPinning_fintype Γ' hf' B'
    ⟨pull ρ, hsat ρ ht, hb'⟩
  refine ⟨τ ∘ tag, fun v => hc (tag v), ?_, ?_⟩
  · intro l hl
    exact (holdsT_map _ tag τ l).mp (ht _ (List.mem_map.mpr ⟨l, hl, rfl⟩))
  · intro b hm
    exact hbτ ⟨tag b.var, b.lower, b.tree⟩ (List.mem_map.mpr ⟨b, hm, rfl⟩)

end DeciSigma1.Full.Models
