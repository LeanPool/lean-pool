/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalMultilinearExpansion
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DiagonalMassComparison
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalSlotPerm
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PolarizationAlgebra
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerDomination

/-!
# Mixed total mass is unchanged under bounded differences

Let `θ₁, …, θₙ` be arbitrary closed real `(1,1)`-forms on a compact Kähler manifold
and let `aᵢ ≤ bᵢ ≤ aᵢ + t` be nondegenerate `θᵢ`-PSH potentials. Then the global
mixed measures of `a` and `b` have the same total mass.

Index the slots together with a Kähler slot by `Option (Fin n)`: the form `ω` with
potential `0` sits at `none`. For `S ⊆ Fin n` and `N ∈ ℕ` consider the diagonal
measure of the combination `∑_{i ∈ S} (θᵢ, aᵢ) + N (ω, 0)`. For `N` large its
form is semipositive, and the combinations for `a` and `b` differ by a bounded
amount, so their diagonal masses agree (`DiagonalMassComparison`). Expanding
multilinearly (`GlobalMultilinearExpansion`), these masses are polynomials in `N`;
their constant coefficients are the sums `E_S` of the mixed masses of all maps
`Fin n → S`. Inclusion–exclusion over `S` isolates the maps `Fin n → Fin n` that
are bijective, and slot symmetry (`GlobalSlotPerm`) identifies all of them with the
mixed mass itself (`PolarizationAlgebra`).
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.MixedMassBoundedDifference

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open GlobalNonPluripolar BoundedGlobalProduct GlobalMultilinearExpansion
open DiagonalMassComparison GlobalSlotPerm PolarizationAlgebra KahlerDomination

noncomputable section

theorem ereal_sum_add_coe {ι : Type*} (T : Finset ι) (x : ι → EReal) (c : ι → ℝ) :
    ∑ i ∈ T, (x i + (c i : EReal)) = ∑ i ∈ T, x i + ((∑ i ∈ T, c i : ℝ) : EReal) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, ih, EReal.coe_add]
    ac_rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The forms, indexed by the slots and a Kähler slot `none`. -/
def optForm (omega : KahlerBackground n M) (θ : Fin n → ClosedRealOneOneForm n M) :
    Option (Fin n) → ClosedRealOneOneForm n M :=
  fun o => o.elim omega.form θ

/-- The potentials, with `0` at the Kähler slot. -/
def optPot (a : Fin n → M → EReal) : Option (Fin n) → M → EReal :=
  fun o => o.elim (fun _ => ((0 : ℝ) : EReal)) a

/-- The weights: `1` on the slots, `N` at the Kähler slot. -/
def optWeight (N : ℝ) : Option (Fin n) → ℝ :=
  fun o => o.elim N (fun _ => 1)

/-- The index set of `S` together with the Kähler slot. -/
def optSet (S : Finset (Fin n)) : Finset (Option (Fin n)) :=
  insert none (S.map Function.Embedding.some)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem optPot_psh (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {a : Fin n → M → EReal} (ha : ∀ i, IsThetaPshPotential (θ i).val (a i)) :
    ∀ o, ThetaPlurisubharmonic (optForm omega θ o).val (optPot a o)
  | none => thetaPlurisubharmonic_const omega.form omega.isSemipositive 0
  | some i => (ha i).1

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem optPot_quasiPsh {θ : Fin n → ClosedRealOneOneForm n M} {a : Fin n → M → EReal}
    (ha : ∀ i, IsThetaPshPotential (θ i).val (a i)) :
    ∀ o, IsGlobalQuasiPshPotential (n := n) (optPot a o)
  | none => isGlobalQuasiPshPotential_const 0
  | some i => ⟨(ha i).1.quasiPlurisubharmonic, (ha i).2⟩

theorem optWeight_pos {N : ℝ} (hN : 0 < N) : ∀ o : Option (Fin n), 0 < optWeight N o
  | none => hN
  | some _ => one_pos

theorem optSet_nonempty (S : Finset (Fin n)) : (optSet S).Nonempty := ⟨none, by simp [optSet]⟩

theorem prod_optWeight (N : ℝ) (g : Fin n → Option (Fin n)) :
    ∏ j, optWeight N (g j) = N ^ (Finset.univ.filter (fun j => g j = none)).card := by
  classical
  have h : ∀ j, optWeight N (g j) = if g j = none then N else 1 := fun j => by
    cases g j <;> simp [optWeight]
  simp only [h]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem sumForm_optSet (omega : KahlerBackground n M) (θ : Fin n → ClosedRealOneOneForm n M)
    (S : Finset (Fin n)) (N : ℝ) :
    sumForm (optSet S) (optWeight N) (optForm omega θ) =
      (∑ i ∈ S, θ i) + N • omega.form := by
  classical
  rw [sumForm, optSet, Finset.sum_insert (by simp), Finset.sum_map, add_comm]
  simp [optWeight, optForm]

/-- **Mixed mass is unchanged under a bounded difference**, for arbitrary backgrounds. -/
theorem globalMixedMeasure_univ_eq_of_le_add (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M} {a b : Fin n → M → EReal}
    (ha : ∀ i, IsThetaPshPotential (θ i).val (a i))
    (hb : ∀ i, IsThetaPshPotential (θ i).val (b i))
    {t : ℝ} (ht : 0 ≤ t) (hab : ∀ i p, a i p ≤ b i p)
    (hba : ∀ i p, b i p ≤ a i p + (t : EReal)) :
    globalMixedMeasure θ a (fun i => (ha i).1) univ =
      globalMixedMeasure θ b (fun i => (hb i).1) univ := by
  classical
  -- mixed masses along maps into the slots and the Kähler slot
  let mm (c : Fin n → M → EReal) (hc : ∀ i, IsThetaPshPotential (θ i).val (c i))
      (g : Fin n → Option (Fin n)) : ℝ :=
    (globalMixedMeasure (fun j => optForm omega θ (g j)) (fun j => optPot c (g j))
      (fun j => optPot_psh omega hc (g j)) univ).toReal
  -- a large Kähler multiple makes every partial sum semipositive
  obtain ⟨A, -, hA⟩ := exists_pos_forall_isSemipositive_add_smul omega
    (fun S : Finset (Fin n) => ∑ i ∈ S, θ i)
  set N₀ : ℕ := ⌈A⌉₊ + 1 with hN₀
  have hsemi (S : Finset (Fin n)) (N : ℕ) (hN : N₀ ≤ N) :
      (sumForm (optSet S) (optWeight (N : ℝ)) (optForm omega θ)).val.IsSemipositive := by
    rw [sumForm_optSet]
    refine isSemipositive_add_smul_mono omega.isSemipositive ?_ (hA S)
    have : (⌈A⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith [Nat.le_ceil A]
  have hopt1 : ∀ o p, optPot a o p ≤ optPot b o p
    | none, _ => le_rfl
    | some i, p => hab i p
  have hopt2 : ∀ o p, optPot b o p ≤ optPot a o p + (t : EReal)
    | none, _ => by
      change (0 : EReal) ≤ 0 + (t : EReal)
      rw [zero_add, ← EReal.coe_zero]
      exact EReal.coe_le_coe_iff.mpr ht
    | some i, p => hba i p
  -- step 1: for every `S` and large `N`, the polynomial identity
  have hpoly (S : Finset (Fin n)) (N : ℕ) (hN : N₀ ≤ N) :
      ∑ g ∈ Fintype.piFinset (fun _ : Fin n => optSet S),
        (N : ℝ) ^ (Finset.univ.filter (fun j => g j = none)).card * (mm a ha g - mm b hb g) =
        0 := by
    have hNpos : (0 : ℝ) < N := by
      have : 1 ≤ N := le_trans (by omega) hN
      exact_mod_cast this
    have hw := optWeight_pos (n := n) hNpos
    have hfa := optPot_psh omega ha
    have hfb := optPot_psh omega hb
    have hdiag := diagonal_univ_eq_of_le_add omega (hsemi S N hN)
      (thetaPlurisubharmonic_sumPot (optSet_nonempty S) hw hfa)
      (thetaPlurisubharmonic_sumPot (optSet_nonempty S) hw hfb)
      (t := (∑ o ∈ optSet S, optWeight (N : ℝ) o) * t)
      (mul_nonneg (Finset.sum_nonneg fun o _ => (hw o).le) ht)
      (fun p => Finset.sum_le_sum fun o _ =>
        mul_le_mul_of_nonneg_left (hopt1 o p) (EReal.coe_nonneg.mpr (hw o).le))
      (fun p => by
        calc sumPot (optSet S) (optWeight (N : ℝ)) (optPot b) p
            ≤ ∑ o ∈ optSet S, ((optWeight (N : ℝ) o : ℝ) : EReal) *
                (optPot a o p + (t : EReal)) :=
              Finset.sum_le_sum fun o _ =>
                mul_le_mul_of_nonneg_left (hopt2 o p) (EReal.coe_nonneg.mpr (hw o).le)
          _ = ∑ o ∈ optSet S, (((optWeight (N : ℝ) o : ℝ) : EReal) * optPot a o p +
                ((optWeight (N : ℝ) o * t : ℝ) : EReal)) := by
              refine Finset.sum_congr rfl fun o _ => ?_
              rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (hw o).le)
                (EReal.coe_ne_top _), ← EReal.coe_mul]
          _ = _ := by rw [ereal_sum_add_coe, Finset.sum_mul]; rfl)
    rw [globalMixedMeasure_diagonal_sumPot (optSet_nonempty S) hw hfa (optPot_quasiPsh ha),
      globalMixedMeasure_diagonal_sumPot (optSet_nonempty S) hw hfb (optPot_quasiPsh hb)]
      at hdiag
    simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul]
      at hdiag
    have hfin (c : Fin n → M → EReal) (hc : ∀ i, IsThetaPshPotential (θ i).val (c i))
        (g : Fin n → Option (Fin n)) :
        ENNReal.ofReal (∏ j, optWeight (N : ℝ) (g j)) *
          globalMixedMeasure (fun j => optForm omega θ (g j)) (fun j => optPot c (g j))
            (fun j => optPot_psh omega hc (g j)) univ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (globalMixedMeasure_apply_lt_top omega _ univ).ne
    have hreal := congrArg ENNReal.toReal hdiag
    rw [ENNReal.toReal_sum fun g _ => hfin a ha g, ENNReal.toReal_sum fun g _ => hfin b hb g]
      at hreal
    have hkey : ∀ k : ℕ, (ENNReal.ofReal ((N : ℝ) ^ k)).toReal = (N : ℝ) ^ k := fun k =>
      ENNReal.toReal_ofReal (pow_nonneg hNpos.le k)
    simp only [ENNReal.toReal_mul, prod_optWeight, hkey] at hreal
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hreal
  -- step 2: the constant coefficient `E_S` agrees for `a` and `b`
  have hE (S : Finset (Fin n)) :
      ∑ h : Fin n → Fin n with ∀ j, h j ∈ S,
        (mm a ha (fun j => some (h j)) - mm b hb (fun j => some (h j))) = 0 := by
    let d : (Fin n → Option (Fin n)) → ℝ := fun g =>
      if ∀ j, g j ∈ optSet S then mm a ha g - mm b hb g else 0
    have hk : ∀ N : ℕ, N₀ ≤ N →
        ∑ g, (N : ℝ) ^ (Finset.univ.filter (fun j => g j = none)).card * d g = 0 := by
      intro N hN
      rw [← hpoly S N hN]
      have hpi : Fintype.piFinset (fun _ : Fin n => optSet S) =
          Finset.univ.filter (fun g : Fin n → Option (Fin n) => ∀ j, g j ∈ optSet S) := by
        ext g; simp [Fintype.mem_piFinset]
      rw [hpi, Finset.sum_filter]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [d]
      split_ifs <;> simp
    have h0 := sum_eq_zero_of_forall_nat_ge _ d N₀ hk
    rw [← h0, Finset.sum_filter, Finset.sum_filter]
    let e : (Fin n → Fin n) ↪ (Fin n → Option (Fin n)) :=
      ⟨fun h j => some (h j), fun h h' hh => funext fun j => Option.some_injective _
        (congrFun hh j)⟩
    symm
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) ?_, Finset.sum_map]
    · refine Finset.sum_congr rfl fun h _ => ?_
      have hc : (Finset.univ.filter fun j => e h j = none).card = 0 := by
        simp [e]
      simp only [hc, ite_true, d]
      congr 1
      change (∀ j, some (h j) ∈ optSet S) = _
      simp [optSet]
    · intro g _ hg
      have hnone : ∃ j, g j = none := by
        by_contra hcon
        push Not at hcon
        refine hg (Finset.mem_map.mpr ⟨fun j => (g j).get (Option.isSome_iff_ne_none.mpr
          (hcon j)), Finset.mem_univ _, funext fun j => ?_⟩)
        exact Option.some_get _
      obtain ⟨j, hj⟩ := hnone
      have hc : (Finset.univ.filter fun j => g j = none).card ≠ 0 :=
        Finset.card_ne_zero.mpr ⟨j, by simp [hj]⟩
      simp [hc]
  -- step 3: inclusion–exclusion and slot symmetry
  let dd : (Fin n → Fin n) → ℝ := fun h =>
    mm a ha (fun j => some (h j)) - mm b hb (fun j => some (h j))
  have hperm : ∀ σ : Equiv.Perm (Fin n), dd σ = dd id := by
    intro σ
    simp only [dd, mm, optForm, optPot, Option.elim, id]
    rw [globalMixedMeasure_perm (fun i => (ha i).1) σ,
      globalMixedMeasure_perm (fun i => (hb i).1) σ]
  have hsum := sum_powerset_signed_eq_factorial_mul dd hperm
  simp only [dd, hE, mul_zero, Finset.sum_const_zero] at hsum
  have hid : dd id = 0 := by
    have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    exact (mul_eq_zero.mp hsum.symm).resolve_left hfac
  have hreal : (globalMixedMeasure θ a (fun i => (ha i).1) univ).toReal =
      (globalMixedMeasure θ b (fun i => (hb i).1) univ).toReal := sub_eq_zero.mp hid
  exact (ENNReal.toReal_eq_toReal_iff' (globalMixedMeasure_apply_lt_top omega _ univ).ne
    (globalMixedMeasure_apply_lt_top omega _ univ).ne).mp hreal

end

end SGPT.Foundations.Analysis.Pending.MixedMassBoundedDifference
