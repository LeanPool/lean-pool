/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Defs
public import LeanPool.HubbardMoments.Fermions

/-! # Fermionic hopping matrices on finite graphs -/

@[expose] public section

namespace HubbardMoments

open Finset Complex
open scoped Matrix

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]

/-! ### Fock states of configurations -/

omit [Fintype V] [Fintype σ] [DecidableEq V] [DecidableEq σ] in
theorem mem_configState [Fintype V] [Fintype σ] [DecidableEq σ] {c : Config V σ}
    {o : V × σ} : o ∈ configState c ↔ c o.1 = some o.2 := by
  simp [configState]

omit [DecidableEq V] in
theorem configState_injective : Function.Injective (configState : Config V σ → FockState V σ) := by
  intro c b h
  funext v
  cases hc : c v with
  | none =>
    cases hb : b v with
    | none => rfl
    | some s =>
      have : (v, s) ∈ configState b := mem_configState.2 hb
      rw [← h, mem_configState] at this
      simp [hc] at this
  | some s =>
    have : (v, s) ∈ configState c := mem_configState.2 hc
    rw [h, mem_configState] at this
    exact this.symm

/-- The Fock state after one hop of the configuration. -/
theorem configState_move {c : Config V σ} {i j : V} {s : σ} (hi : c i = some s)
    (hj : c j = none) :
    configState (move c i j) = insert (j, s) ((configState c).erase (i, s)) := by
  ext ⟨v, s'⟩
  simp only [mem_configState, move, Function.update_apply, mem_insert, mem_erase, ne_eq,
    Prod.mk.injEq]
  by_cases hvj : v = j
  · subst hvj
    simp [hi, hj, eq_comm]
  · by_cases hvi : v = i
    · subst hvi
      simp [hvj, hi, eq_comm]
    · simp [hvj, hvi]

/-- A replacement of one orbital by another of the same spin between two configurations
must move the particle to an empty site. -/
theorem config_eq_move_of_replace {c b : Config V σ} {i j : V} {s : σ} (hij : i ≠ j)
    (hi : (i, s) ∈ configState c) (hj : (j, s) ∉ (configState c).erase (i, s))
    (hb : configState b = insert (j, s) ((configState c).erase (i, s))) :
    c i ≠ none ∧ c j = none ∧ b = move c i j := by
  have hci : c i = some s := mem_configState.1 hi
  have hbj : b j = some s := mem_configState.1 (by rw [hb]; exact mem_insert_self _ _)
  have hcj : c j = none := by
    by_contra h
    obtain ⟨s', hs'⟩ := Option.ne_none_iff_exists'.1 h
    have hmem : (j, s') ∈ (configState c).erase (i, s) :=
      mem_erase.2 ⟨fun h => hij (congrArg Prod.fst h).symm, mem_configState.2 hs'⟩
    have hb' : b j = some s' :=
      mem_configState.1 (by rw [hb]; exact mem_insert_of_mem hmem)
    have hspin : s' = s := Option.some.inj (hb'.symm.trans hbj)
    subst s'
    exact hj hmem
  exact ⟨by simp [hci], hcj, configState_injective (hb.trans (configState_move hci hcj).symm)⟩

/-- Two hops from the same Fock state that give the same state are the same hop. -/
theorem hop_unique {O : Type*} [DecidableEq O] {S : Finset O} {o₁ o₁' o₂ o₂' : O}
    (h₁ : o₁ ∈ S) (h₁' : o₁' ∉ S.erase o₁) (hne : o₁ ≠ o₁')
    (heq : insert o₁' (S.erase o₁) = insert o₂' (S.erase o₂)) : o₁ = o₂ ∧ o₁' = o₂' := by
  have hn : o₁ ∉ insert o₁' (S.erase o₁) := by simp [hne]
  rw [heq] at hn
  have e₁ : o₁ = o₂ := by
    by_contra h
    exact hn (mem_insert_of_mem (mem_erase.2 ⟨h, h₁⟩))
  subst e₁
  refine ⟨rfl, ?_⟩
  have : o₁' ∈ insert o₂' (S.erase o₁) := heq ▸ mem_insert_self o₁' _
  rcases mem_insert.1 this with h | h
  · exact h
  · exact absurd h h₁'

/-! ### The hopping term -/

section FermionHopping

variable (G : SimpleGraph V) [DecidableRel G.Adj] (amplitude : V → V → ℂ) (ord : V × σ ↪ ℕ)

/-- The matrix elements of `H_t`. -/
theorem fermionHopping_apply (S' S : FockState V σ) :
    fermionHopping G amplitude ord S' S = ∑ p ∈ arcs G, ∑ s,
      amplitude p.1 p.2 *
        if (p.1, s) ∈ S ∧ (p.2, s) ∉ S.erase (p.1, s) ∧ S' = insert (p.2, s) (S.erase (p.1, s))
        then (-1) ^ (countBelow ord S (p.1, s) + countBelow ord (S.erase (p.1, s)) (p.2, s))
        else 0 := by
  simp only [fermionHopping, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    create_mul_annihilate_apply]

/-- The hopping matrix is Hermitian when reversals conjugate the coefficients. -/
theorem fermionHopping_isHermitian
    (h : ∀ i j, G.Adj i j → star (amplitude i j) = amplitude j i) :
    (fermionHopping G amplitude ord).IsHermitian := by
  have hcr : ∀ o, (create ord o)ᴴ = annihilate ord o := fun o => by
    rw [← annihilate_conjTranspose, Matrix.conjTranspose_conjTranspose]
  unfold Matrix.IsHermitian fermionHopping
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    hcr, annihilate_conjTranspose]
  conv_rhs => rw [← sum_arcs_swap G]
  refine sum_congr rfl fun p hp ↦ sum_congr rfl fun _ _ ↦ ?_
  simp only [h _ _ ((mem_arcs G).mp hp), Prod.fst_swap, Prod.snd_swap]

/-- **`H_t` is a hopping operator**: it connects only Fock states one hop apart. -/
theorem fermionHopping_isHoppingOperator :
    IsHoppingOperator G (fermionHopping G amplitude ord) := by
  refine ⟨fun a b hab => ?_⟩
  rw [fermionHopping_apply]
  refine sum_eq_zero fun p hp => sum_eq_zero fun s _ => ?_
  have hadj : G.Adj p.1 p.2 := (mem_arcs G).mp hp
  rw [ite_eq_right_iff.2 ?_, mul_zero]
  rintro ⟨h₁, h₂, rfl⟩
  refine absurd ⟨p.1, p.2, s, hadj, h₁, fun h => h₂ (mem_erase.2 ⟨?_, h⟩), rfl⟩ hab
  intro he
  exact G.ne_of_adj hadj (congrArg Prod.fst he).symm

/-- Restricting a Hermitian hopping matrix to the configuration basis preserves Hermiticity. -/
theorem projectedFermionHopping_isHermitian
    (h : ∀ i j, G.Adj i j → star (amplitude i j) = amplitude j i) :
    (projectedFermionHopping G amplitude ord).IsHermitian := by
  ext c b
  exact (fermionHopping_isHermitian G amplitude ord h).apply (configState c) (configState b)

/-- Only the specified hop and its spin contribute to the corresponding matrix entry. -/
theorem norm_projectedFermionHopping_move {c : Config V σ} {i j : V}
    (hadj : G.Adj i j) (hci : c i ≠ none) (hcj : c j = none) :
    ‖projectedFermionHopping G amplitude ord (move c i j) c‖ = ‖amplitude i j‖ := by
  obtain ⟨s₀, hs₀⟩ := Option.ne_none_iff_exists'.1 hci
  have hij : i ≠ j := G.ne_of_adj hadj
  have hmem : (i, s₀) ∈ configState c := mem_configState.2 hs₀
  have hnot : (j, s₀) ∉ configState c := by simp [mem_configState, hcj]
  simp only [projectedFermionHopping, configState_move hs₀ hcj, fermionHopping_apply]
  -- only the hop `i → j` of spin `s₀` contributes
  rw [sum_eq_single (i, j), sum_eq_single s₀]
  · have hnot' : (j, s₀) ∉ (configState c).erase (i, s₀) := fun h => hnot (mem_of_mem_erase h)
    have hone : ‖(1 : ℂ)‖ = 1 := by
      simpa only [Complex.ofReal_one, Real.norm_eq_abs, abs_one] using Complex.norm_real 1
    simp [hmem, hnot', Complex.norm_pow, hone]
  · intro s _ hs
    rw [ite_eq_right_iff.2, mul_zero]
    rintro ⟨h₁, h₂, h₃⟩
    exfalso
    exact hs (Prod.mk.inj (hop_unique h₁ h₂ (by simp [hij]) h₃.symm).1).2
  · intro h
    exact absurd (mem_univ s₀) h
  · intro p hp hpij
    refine sum_eq_zero fun s _ => ?_
    have hadj' : G.Adj p.1 p.2 := (mem_arcs G).mp hp
    rw [ite_eq_right_iff.2, mul_zero]
    rintro ⟨h₁, h₂, h₃⟩
    have hne : (p.1, s) ≠ (p.2, s) := fun h => G.ne_of_adj hadj' (congrArg Prod.fst h)
    obtain ⟨e₁, e₂⟩ := hop_unique h₁ h₂ hne h₃.symm
    have e₁' : p.1 = i := congrArg Prod.fst e₁
    have e₂' : p.2 = j := congrArg Prod.fst e₂
    exact absurd (Prod.ext e₁' e₂') hpij
  · intro h
    exact absurd (by simp [hadj] : (i, j) ∈ arcs G) h

/-- In the configuration basis, an entry vanishes whenever no graph hop gives its target. -/
theorem projectedFermionHopping_apply_eq_zero (c b : Config V σ)
    (hb : ¬ IsProjectedHop G c b) :
    projectedFermionHopping G amplitude ord b c = 0 := by
  simp only [projectedFermionHopping, fermionHopping_apply]
  refine sum_eq_zero fun p hp => sum_eq_zero fun s _ => ?_
  have hadj : G.Adj p.1 p.2 := (mem_arcs G).mp hp
  have hne : p.1 ≠ p.2 := G.ne_of_adj hadj
  rw [ite_eq_right_iff.2, mul_zero]
  rintro ⟨h₁, h₂, h₃⟩
  obtain ⟨hci, hcj, hmove⟩ := config_eq_move_of_replace hne h₁ h₂ h₃
  exact (hb ⟨p.1, p.2, hadj, hci, hcj, hmove⟩).elim

end FermionHopping

end HubbardMoments
