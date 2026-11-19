/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.PeierlsModel
public import LeanPool.HubbardMoments.Fermions
public import LeanPool.HubbardMoments.ProjectedHopping
public import LeanPool.HubbardMoments.SchriefferWolff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring

/-!
# The Hubbard hopping term and `H∞` from fermion operators

`HubbardMoments.hubbardHopping` is the hopping term `H_t = -t ∑ e^{iA} c†_{y s} c_{x s}` built
from the fermion operators of `HubbardMoments.Fermions`, for an arbitrary ordering `ord` of
the orbitals (any fermionic sign convention). `HubbardMoments.projectedHubbard` is
`H∞ = P₀ H_t P₀` in the configuration basis.

* `hubbardHopping_isHermitian`: `H_t` is Hermitian when `A` is antisymmetric;
* `hubbardHopping_isHoppingOperator`: `H_t` only connects Fock states one hop apart;
* `projectedHubbard_isProjectedHopping`: `H∞` has the three properties of
  `IsProjectedHopping`, for `t ≥ 0`;
* consequently the exact second-moment theorem holds for `H∞` itself
  (`secondMoment_projectedHubbard`, `secondMoment_projectedHubbard_torus`), and the
  Schrieffer–Wolff cross term vanishes for `H_t` itself
  (`secondMoment_hubbardHopping_sub_virtualOp`, `…_torus` for `L ≥ 4`).

This closes the gap stated in the documentation of `IsProjectedHopping` and
`IsHoppingOperator`.
-/

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
  refine sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa [arcs, G.adj_comm] using hp
  · intro p hp
    simpa [arcs, G.adj_comm] using hp
  · intro p _
    rfl
  · intro p _
    rfl
  · intro p hp
    refine sum_congr rfl fun _ _ => ?_
    simp only [h _ _ (mem_filter.mp hp).2, Prod.fst_swap, Prod.snd_swap]

/-- **`H_t` is a hopping operator**: it connects only Fock states one hop apart. -/
theorem fermionHopping_isHoppingOperator :
    IsHoppingOperator G (fermionHopping G amplitude ord) := by
  refine ⟨fun a b hab => ?_⟩
  rw [fermionHopping_apply]
  refine sum_eq_zero fun p hp => sum_eq_zero fun s _ => ?_
  have hadj : G.Adj p.1 p.2 := (mem_filter.1 hp).2
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
    simp [hmem, hnot']
  · intro s _ hs
    rw [ite_eq_right_iff.2, mul_zero]
    rintro ⟨h₁, h₂, h₃⟩
    exfalso
    exact hs (Prod.mk.inj (hop_unique h₁ h₂ (by simp [hij]) h₃.symm).1).2
  · intro h
    exact absurd (mem_univ s₀) h
  · intro p hp hpij
    refine sum_eq_zero fun s _ => ?_
    have hadj' : G.Adj p.1 p.2 := (mem_filter.1 hp).2
    rw [ite_eq_right_iff.2, mul_zero]
    rintro ⟨h₁, h₂, h₃⟩
    have hne : (p.1, s) ≠ (p.2, s) := fun h => G.ne_of_adj hadj' (congrArg Prod.fst h)
    obtain ⟨e₁, e₂⟩ := hop_unique h₁ h₂ hne h₃.symm
    have e₁' : p.1 = i := congrArg Prod.fst e₁
    have e₂' : p.2 = j := congrArg Prod.fst e₂
    exact absurd (Prod.ext e₁' e₂') hpij
  · intro h
    exact absurd (by simp [arcs, hadj] : (i, j) ∈ arcs G) h

/-- In the configuration basis, an entry vanishes whenever no graph hop gives its target. -/
theorem projectedFermionHopping_apply_eq_zero (c b : Config V σ)
    (hb : ∀ i j, G.Adj i j → c i ≠ none → c j = none → b ≠ move c i j) :
    projectedFermionHopping G amplitude ord b c = 0 := by
  simp only [projectedFermionHopping, fermionHopping_apply]
  refine sum_eq_zero fun p hp => sum_eq_zero fun s _ => ?_
  have hadj : G.Adj p.1 p.2 := (mem_filter.1 hp).2
  have hne : p.1 ≠ p.2 := G.ne_of_adj hadj
  rw [ite_eq_right_iff.2, mul_zero]
  rintro ⟨h₁, h₂, h₃⟩
  obtain ⟨hci, hcj, hmove⟩ := config_eq_move_of_replace hne h₁ h₂ h₃
  exact (hb p.1 p.2 hadj hci hcj hmove).elim

end FermionHopping

/-! ### Hubbard hopping with Peierls phases -/

variable (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (A : V → V → ℝ) (ord : V × σ ↪ ℕ)

/-- The matrix elements of `H_t`. -/
theorem hubbardHopping_apply (S' S : FockState V σ) :
    hubbardHopping G t A ord S' S = ∑ p ∈ arcs G, ∑ s,
      (-(t : ℂ) * exp (A p.2 p.1 * I)) *
        if (p.1, s) ∈ S ∧ (p.2, s) ∉ S.erase (p.1, s) ∧ S' = insert (p.2, s) (S.erase (p.1, s))
        then (-1) ^ (countBelow ord S (p.1, s) + countBelow ord (S.erase (p.1, s)) (p.2, s))
        else 0 :=
  fermionHopping_apply G _ ord S' S

/-- **`H_t` is Hermitian** when the Peierls phases are antisymmetric. -/
theorem hubbardHopping_isHermitian {A : V → V → ℝ} (hA : ∀ x y, G.Adj x y → A y x = -A x y) :
    (hubbardHopping G t A ord).IsHermitian :=
  fermionHopping_isHermitian G _ ord (fun i j hij => by rw [star_peierlsAmplitude, hA j i hij.symm])

/-- **`H_t` is a hopping operator**: it connects only Fock states one hop apart. -/
theorem hubbardHopping_isHoppingOperator : IsHoppingOperator G (hubbardHopping G t A ord) :=
  fermionHopping_isHoppingOperator G _ ord

/-! ### `H∞ = P₀ H_t P₀` -/

/-- **`H∞` built from fermion operators is a projected hopping operator.** For `t ≥ 0` and
antisymmetric Peierls phases, with any ordering of the orbitals. -/
theorem projectedHubbard_isProjectedHopping (ht : 0 ≤ t) {A : V → V → ℝ}
    (hA : ∀ x y, G.Adj x y → A y x = -A x y) :
    IsProjectedHopping G t (projectedHubbard G t A ord) := by
  refine ⟨projectedFermionHopping_isHermitian G _ ord ?_, ?_,
    projectedFermionHopping_apply_eq_zero G _ ord⟩
  · intro i j hij
    rw [star_peierlsAmplitude, hA j i hij.symm]
  · intro c i j hadj hci hcj
    simpa [projectedHubbard, peierlsAmplitude, Complex.norm_mul, Real.norm_of_nonneg ht] using
      norm_projectedFermionHopping_move G
        (fun i j => peierlsAmplitude t (A j i)) ord hadj hci hcj

/-! ### Consequences -/

/-- **The exact second-moment theorem for `H∞` itself.** -/
theorem secondMoment_projectedHubbard (ht : 0 ≤ t) {A : V → V → ℝ}
    (hA : ∀ x y, G.Adj x y → A y x = -A x y) (n : σ → ℕ) (hB : (basis V n).Nonempty)
    (hN : 2 ≤ Fintype.card V) :
    secondMoment (basis V n) (projectedHubbard G t A ord) =
      (t : ℂ) ^ 2 * (2 * G.edgeFinset.card) * (∑ s, n s : ℕ) *
          ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
        ((Fintype.card V : ℂ) * ((Fintype.card V : ℂ) - 1)) :=
  second_moment (projectedHubbard_isProjectedHopping G t ord ht hA) n hB hN

/-- **No `1/U` correction for the Hubbard hopping term on a triangle-free graph.** -/
theorem secondMoment_hubbardHopping_sub_virtualOp (hG : G.CliqueFree 3)
    {B Q : Finset (FockState V σ)} (hB : ∀ a ∈ B, ∀ v, siteOcc a v ≤ 1)
    (hQ : ∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) (U : ℝ) :
    secondMoment B (hubbardHopping G t A ord - (U : ℂ)⁻¹ • virtualOp Q (hubbardHopping G t A ord)) =
      secondMoment B (hubbardHopping G t A ord) +
        secondMoment B (virtualOp Q (hubbardHopping G t A ord)) / (U : ℂ) ^ 2 :=
  secondMoment_sub_virtualOp (hubbardHopping_isHoppingOperator G t A ord) hG hB hQ U

/-- **The second moment of `H∞` on the `L × L` torus** (`L ≥ 3`):
`μ₂ = t² · 4n(L² - n)/(L² - 1)`. -/
theorem secondMoment_projectedHubbard_torus {L : ℕ} (hL : 3 ≤ L) (ht : 0 ≤ t)
    {A : Fin L × Fin L → Fin L × Fin L → ℝ} (hA : ∀ x y, (torus L).Adj x y → A y x = -A x y)
    (ord : (Fin L × Fin L) × σ ↪ ℕ) (n : σ → ℕ) (hB : (basis (Fin L × Fin L) n).Nonempty) :
    secondMoment (basis (Fin L × Fin L) n) (projectedHubbard (torus L) t A ord) =
      (t : ℂ) ^ 2 * 4 * (∑ s, n s : ℕ) * ((L : ℂ) * L - (∑ s, n s : ℕ)) / ((L : ℂ) * L - 1) :=
  second_moment_torus hL (projectedHubbard_isProjectedHopping (torus L) t ord ht hA) n hB

/-- **No `1/U` correction for the Hubbard hopping term on the `L × L` torus**, `L ≥ 4`. -/
theorem secondMoment_hubbardHopping_sub_virtualOp_torus {L : ℕ} (hL : 4 ≤ L)
    (A : Fin L × Fin L → Fin L × Fin L → ℝ) (ord : (Fin L × Fin L) × σ ↪ ℕ)
    {B Q : Finset (FockState (Fin L × Fin L) σ)} (hB : ∀ a ∈ B, ∀ v, siteOcc a v ≤ 1)
    (hQ : ∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) (U : ℝ) :
    secondMoment B (hubbardHopping (torus L) t A ord -
        (U : ℂ)⁻¹ • virtualOp Q (hubbardHopping (torus L) t A ord)) =
      secondMoment B (hubbardHopping (torus L) t A ord) +
        secondMoment B (virtualOp Q (hubbardHopping (torus L) t A ord)) / (U : ℂ) ^ 2 :=
  secondMoment_sub_virtualOp_torus hL (hubbardHopping_isHoppingOperator (torus L) t A ord) hB hQ U

end HubbardMoments
