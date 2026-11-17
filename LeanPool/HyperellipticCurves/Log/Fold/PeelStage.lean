/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.MomentDet

/-!
# The peel-stage identities of the certificate route

The nonvanishing certificates of the moment route evaluate a pattern determinant
(`ChabautyColeman.momentDet`) of a product alphabet by peeling one node variable `u` at a
time: `momentDet_mul` expands the determinant of `q·F` (with `F` the `u`-part, e.g. `u+X`
or `(u+X)²`) into a weighted sum over shift choices, and the **stage identities** of this
file split off the surviving choices — the term of top `u`-degree — from a remainder of
smaller `u`-degree. Every intermediate pattern belongs to the single family
`ChabautyColeman.peelPattern`: `c_r = (0, 1, …, r-1, r+1, r+3, …)`, from the identity
pattern `c_g` down to the terminal `c_0 = (1, 3, 5, …)`, whose matrix is diagonal
(`momentDet_C_peelPattern_zero`).

The five stage shapes, each stated for a general peeled factor `F` (only its degree bound
enters the survivor analysis; its coefficients form the top weight):

* `ChabautyColeman.peelStage_lead`: the unshifted choice survives at the unchanged pattern
  with weight `(F.coeff 0)^g` — the whole stage identity for the doubled and signed leads
  at `r - G' ≤ 0`, whose top coefficients `u^(2g)`, `(-1)^g·u^(2g)`, `±u^(3g)` are the
  sign sources of the certificates.
* `ChabautyColeman.peelStage_single`: the single peel at `r - G' = 1` moves `c_(r+1)` to
  `c_r` with unit coefficient at `u`-degree `r`.
* `ChabautyColeman.peelStage_id`: any peel at the identity pattern with `r - G' = 1` moves
  to `peelPattern (g+1) g` with weight `F.coeff 0 ^ g * F.coeff 1` — instantiating to the
  doubled peel (`κ = 2`) and the signed trio (`κ = (-1)^(g+1)`).
* `ChabautyColeman.peelStage_double`: the doubled peel at `r - G' = 2` moves `c_(r+2)` to
  `c_r` with weight `F.coeff 0 ^ r * F.coeff 1 * F.coeff 2 ^ (g-r-1)` (`κ = 2`).
* `ChabautyColeman.peelStage_triple_id`: the tripled peel at the identity pattern has TWO
  surviving choices, combined by a column swap (`momentDet_comp_swap`) into the weight
  `F.coeff 0 ^ g * (F.coeff 1 * F.coeff 2 - F.coeff 0 * F.coeff 3)` — for `(u+X)³` this
  is `8·u^(3g+3)`, so the tripled certificate coefficient stays a power of two.

The survivor analyses (`singlePeel_det_eq_zero`, `idPeel_det_eq_zero`,
`doublePeel_det_eq_zero`, `triplePeel_det_eq_zero`) kill every other choice of top
`u`-degree by a too-large zero block (`det_eq_zero_of_zero_block`, via the window wrapper
`momentDet_eq_zero_of_block`) or a repeated column. All identities hold over any
commutative ring; the `u`-degree bookkeeping (`shiftSum`) becomes an exact top-coefficient
statement in `LeanPool.HyperellipticCurves.Log.Fold.PeelCoeff`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section ZeroBlock

variable {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]

/-- A determinant vanishes when the matrix has a too-large zero block: if `M` vanishes on
`S × T` with `|S| + |T| > n`, every permutation sends some column of `T` into `S`. -/
theorem det_eq_zero_of_zero_block {M : Matrix n n R} {S T : Finset n}
    (hST : Fintype.card n < S.card + T.card) (h : ∀ i ∈ S, ∀ j ∈ T, M i j = 0) :
    M.det = 0 := by
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ ↦ ?_
  obtain ⟨j, hjT, hjS⟩ : ∃ j ∈ T, σ j ∈ S := by
    by_contra! hc
    have h1 : T.image σ ⊆ Sᶜ := fun x hx ↦ by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_compl.mpr (hc j hj)
    have h2 := Finset.card_le_card h1
    rw [Finset.card_image_of_injective _ (Equiv.injective σ), Finset.card_compl] at h2
    lia [(Finset.card_le_univ S).trans_eq Finset.card_univ]
  have hz : ∏ i, M (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (h _ hjS _ hjT)
  rw [hz, smul_zero]

end ZeroBlock

section PeelStage

variable {R : Type*} [CommRing R] {g : ℕ} {q : R[X]}

/-- The number of `Fin g`-indices with value at least `r`. -/
private theorem card_filter_le_val {g r : ℕ} (hr : r ≤ g) :
    (Finset.univ.filter fun m : Fin g ↦ r ≤ (m : ℕ)).card = g - r := by
  rcases eq_or_lt_of_le hr with rfl | hlt
  · rw [Finset.filter_false_of_mem fun m _ ↦ by have := m.isLt; lia, Finset.card_empty]
    lia
  · rw [show Finset.univ.filter (fun m : Fin g ↦ r ≤ (m : ℕ)) = Finset.Ici ⟨r, hlt⟩ from
      Finset.ext fun m ↦ by simp [Fin.le_def], Fin.card_Ici]

/-- The stage pattern of the peeling induction: the first `r` columns keep the consecutive
shifts `0, …, r-1`, the remaining ones jump with gaps of two. `peelPattern g g` is the
identity pattern of the moment determinant, and each peel stage moves `c_r` towards the
terminal `peelPattern g 0 = (1, 3, 5, …)`, whose pattern determinant is diagonal
(`momentDet_C_peelPattern_zero`). -/
def peelPattern (g r : ℕ) : Fin g → ℕ :=
  fun m ↦ if (m : ℕ) < r then (m : ℕ) else 2 * (m : ℕ) - r + 1

theorem peelPattern_of_lt {r : ℕ} {m : Fin g} (h : (m : ℕ) < r) :
    peelPattern g r m = (m : ℕ) := ite_eq_left h

theorem peelPattern_of_le {r : ℕ} {m : Fin g} (h : r ≤ (m : ℕ)) :
    peelPattern g r m = 2 * (m : ℕ) - r + 1 := ite_eq_right (by lia)

theorem peelPattern_eq_id {r : ℕ} (h : g ≤ r) : peelPattern g r = fun m : Fin g ↦ (m : ℕ) :=
  funext fun m ↦ peelPattern_of_lt (m.isLt.trans_le h)

/-- The terminal value of the peeling induction: at the pattern `(1, 3, 5, …)` a constant
node polynomial gives a diagonal matrix. -/
theorem momentDet_C_peelPattern_zero (a : R) :
    momentDet g (C a) (peelPattern g 0) = a ^ g := by
  have h : (Matrix.of fun i m : Fin g ↦
      (C a * X ^ peelPattern g 0 m).coeff (2 * (i : ℕ) + 1)) = Matrix.diagonal fun _ ↦ a := by
    ext i m
    rw [Matrix.of_apply, Matrix.diagonal_apply, peelPattern_of_le (Nat.zero_le _),
      coeff_C_mul, coeff_X_pow]
    rcases eq_or_ne i m with rfl | hne
    · rw [ite_eq_left rfl, ite_eq_left (by lia), mul_one]
    · rw [ite_eq_right hne, ite_eq_right fun hc ↦ hne (Fin.ext (by lia)), mul_zero]
  rw [momentDet, h, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- A pattern determinant vanishes when all columns up to `m₀` are out of range from row
`m₀` on: the zero block `[m₀, g) × [0, m₀]` is too large. -/
theorem momentDet_eq_zero_of_block {c : Fin g → ℕ} {m₀ : Fin g}
    (h : ∀ m ≤ m₀, q.natDegree + c m < 2 * (m₀ : ℕ) + 1) : momentDet g q c = 0 := by
  rw [momentDet]
  refine det_eq_zero_of_zero_block (S := Finset.Ici m₀) (T := Finset.Iic m₀) ?_ ?_
  · rw [Fin.card_Ici, Fin.card_Iic, Fintype.card_fin]
    lia
  · intro i hi m hm
    rw [Matrix.of_apply]
    refine coeff_mul_X_pow_eq_zero_of_natDegree_lt ?_
    lia [h m (Finset.mem_Iic.mp hm), Fin.le_def.mp (Finset.mem_Ici.mp hi)]

/-- The total shift of a choice function in the peel expansion `momentDet_mul`; for the
peel of a factor of degree `e`, the `u`-degree of the weight of `σ` is `e * g - shiftSum σ`.
-/
def shiftSum {g ρ : ℕ} (σ : Fin g → Fin ρ) : ℕ := ∑ m, (σ m : ℕ)

/-- For a binary choice function, the total shift counts the shifted columns. -/
theorem shiftSum_eq_card {σ : Fin g → Fin 2} :
    shiftSum σ = (Finset.univ.filter fun m ↦ σ m = 1).card := by
  rw [shiftSum, Finset.card_filter]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rcases eq_or_ne (σ m) 0 with h | h
  · simp [h]
  · simp [Fin.eq_one_of_ne_zero _ h]

/-- The total shift of a choice function is at most `(ρ - 1) * g`. -/
theorem shiftSum_le {g ρ : ℕ} (σ : Fin g → Fin ρ) : shiftSum σ ≤ (ρ - 1) * g :=
  (Finset.sum_le_card_nsmul Finset.univ _ (ρ - 1) fun m _ ↦ by
    have := (σ m).isLt; lia).trans_eq (by simp [mul_comm])

/-- The total shift of a nonzero choice function is positive. -/
theorem one_le_shiftSum_of_ne_zero {g ρ : ℕ} [NeZero ρ] {σ : Fin g → Fin ρ} (hσ : σ ≠ 0) :
    1 ≤ shiftSum σ := by
  by_contra h
  refine hσ (funext fun m ↦ Fin.ext ?_)
  have h0 := Finset.sum_eq_zero_iff.mp (show shiftSum σ = 0 by lia) m (Finset.mem_univ m)
  rw [h0, Pi.zero_apply, Fin.val_zero]

/-- The weights of the peel expansion of a monic linear factor are powers of `u`. -/
theorem prod_coeff_C_add_X (u : R) (σ : Fin g → Fin 2) :
    ∏ m, (C u + X).coeff (σ m : ℕ) = u ^ (g - shiftSum σ) := by
  have h1 (m : Fin g) : (C u + X).coeff (σ m : ℕ) = u ^ (1 - (σ m : ℕ)) := by
    rcases eq_or_ne (σ m) 0 with h | h
    · simp [h, coeff_add]
    · simp [Fin.eq_one_of_ne_zero _ h, coeff_add]
  rw [Finset.prod_congr rfl fun m _ ↦ h1 m, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.sum_tsub_distrib _ fun m _ ↦ by have := (σ m).isLt; lia, shiftSum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- The surviving choice of a single peel at stage `r + 1`: take the shift from column `r`
on. It moves the stage pattern `c_(r+1)` to `c_r`
(`peelPattern_add_singlePeelChoice`). -/
def singlePeelChoice (g r : ℕ) : Fin g → Fin 2 := fun m ↦ if (m : ℕ) < r then 0 else 1

theorem peelPattern_add_singlePeelChoice (g r : ℕ) :
    (fun m ↦ peelPattern g (r + 1) m + (singlePeelChoice g r m : ℕ)) = peelPattern g r := by
  funext m
  simp only [peelPattern, singlePeelChoice]
  split_ifs <;> simp only [Fin.val_zero, Fin.val_one] <;> lia

theorem shiftSum_singlePeelChoice {r : ℕ} (hr : r ≤ g) :
    shiftSum (singlePeelChoice g r) = g - r := by
  rw [shiftSum_eq_card, ← card_filter_le_val hr]
  congr 1
  refine Finset.filter_congr fun m _ ↦ ?_
  simp only [singlePeelChoice]
  split_ifs
  · exact iff_of_false (by decide) (by lia)
  · exact iff_of_true rfl (by lia)

/-- **Vanishing at a single peel** (node polynomial of degree at most `r`, stage pattern
`c_(r+1)`): every choice of total shift at most `g - r` other than the surviving one has
vanishing pattern determinant — by a zero block (an unshifted jump column, or all
consecutive columns unshifted) or a repeated column. -/
theorem singlePeel_det_eq_zero {r : ℕ} (hq : q.natDegree ≤ r) (hr : r < g) {σ : Fin g → Fin 2}
    (hσ : shiftSum σ + r ≤ g) (hne : σ ≠ singlePeelChoice g r) :
    momentDet g q (fun m ↦ peelPattern g (r + 1) m + (σ m : ℕ)) = 0 := by
  by_cases hB : ∃ m₀ : Fin g, r + 1 ≤ (m₀ : ℕ) ∧ σ m₀ = 0
  · -- an unshifted jump column cuts a zero block below and left of itself
    obtain ⟨m₀, hm₀, hσ0⟩ := hB
    refine momentDet_eq_zero_of_block (m₀ := m₀) fun m hm ↦ ?_
    have h2 := Fin.le_def.mp hm
    have h3 := (σ m).isLt
    rcases Nat.lt_or_ge (m : ℕ) (r + 1) with h4 | h4
    · rw [peelPattern_of_lt h4]
      lia
    · rw [peelPattern_of_le h4]
      rcases eq_or_lt_of_le h2 with h5 | h5
      · rw [show m = m₀ from Fin.ext h5, hσ0]
        lia
      · lia
  · -- all jump columns shift; at most one consecutive column may
    have hB1 : ∀ m : Fin g, r + 1 ≤ (m : ℕ) → σ m = 1 :=
      fun m hm ↦ Fin.eq_one_of_ne_zero _ fun hc ↦ hB ⟨m, hm, hc⟩
    set Q : Finset (Fin g) := Finset.univ.filter fun m ↦ (m : ℕ) ≤ r ∧ σ m = 1 with hQdef
    have hQcard : Q.card ≤ 1 := by
      have h1 : (Finset.univ.filter fun m : Fin g ↦ r + 1 ≤ (m : ℕ))
          ⊆ Finset.univ.filter fun m : Fin g ↦ σ m = 1 :=
        fun m hm ↦ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hB1 m (Finset.mem_filter.mp hm).2⟩
      have h2 : Q = (Finset.univ.filter fun m : Fin g ↦ σ m = 1)
          \ Finset.univ.filter fun m : Fin g ↦ r + 1 ≤ (m : ℕ) := by
        refine Finset.ext fun m ↦ ?_
        simp only [hQdef, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact ⟨fun h ↦ ⟨h.2, by lia⟩, fun h ↦ ⟨by have := h.2; lia, h.1⟩⟩
      have h3 := shiftSum_eq_card (σ := σ)
      have h4 := card_filter_le_val (g := g) (r := r + 1) (by lia)
      rw [h2, Finset.card_sdiff_of_subset h1, h4, ← h3]
      lia
    by_cases hA : Q.Nonempty
    · -- a single shifted consecutive column: the survivor, or a collision one right
      obtain ⟨p, hp⟩ := hA
      obtain ⟨-, hpr, hp1⟩ := Finset.mem_filter.mp hp
      have hother : ∀ m : Fin g, (m : ℕ) ≤ r → m ≠ p → σ m = 0 := by
        intro m hm hmp
        by_contra hc
        have h1 : m ∈ Q := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hm, Fin.eq_one_of_ne_zero _ hc⟩
        lia [Finset.one_lt_card.mpr ⟨m, h1, p, hp, hmp⟩]
      rcases eq_or_lt_of_le hpr with hpe | hpe
      · -- the shifted column is the last consecutive one: `σ` is the survivor
        refine absurd (_root_.funext fun m ↦ ?_) hne
        rw [singlePeelChoice]
        rcases lt_trichotomy (m : ℕ) r with h1 | h1 | h1
        · rw [ite_eq_left h1, hother m (by lia) fun hc ↦ by rw [hc] at h1; lia]
        · rw [ite_eq_right (by lia), show m = p from Fin.ext (by lia), hp1]
        · rw [ite_eq_right (by lia), hB1 m (by lia)]
      · -- collision: column `p` shifts onto the unshifted column `p + 1`
        have hlt : (p : ℕ) + 1 < g := by lia
        refine momentDet_eq_zero_of_eq (m := p) (m' := ⟨(p : ℕ) + 1, hlt⟩) ?_
          (Fin.ne_of_val_ne (show (p : ℕ) ≠ (p : ℕ) + 1 by lia))
        rw [hp1, hother ⟨(p : ℕ) + 1, hlt⟩ (show (p : ℕ) + 1 ≤ r by lia)
            (Fin.ne_of_val_ne (show (p : ℕ) + 1 ≠ (p : ℕ) by lia)),
          peelPattern_of_lt (show (p : ℕ) < r + 1 by lia),
          peelPattern_of_lt (show (p : ℕ) + 1 < r + 1 by lia)]
        simp
    · -- no consecutive column shifts: the top rows see only the jump columns
      rw [Finset.not_nonempty_iff_eq_empty] at hA
      refine momentDet_eq_zero_of_block (m₀ := ⟨r, hr⟩) fun m hm ↦ ?_
      have h1 : (m : ℕ) ≤ r := Fin.le_def.mp hm
      have h2 : σ m = 0 := by
        by_contra hc
        have h3 : m ∈ Q := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, h1, Fin.eq_one_of_ne_zero _ hc⟩
        rw [hA] at h3
        exact Finset.notMem_empty m h3
      rw [h2, peelPattern_of_lt (show (m : ℕ) < r + 1 by lia)]
      have h4 : ((⟨r, hr⟩ : Fin g) : ℕ) = r := rfl
      simp only [Fin.val_zero]
      lia

/-- Swapping two columns of a pattern negates the pattern determinant. -/
theorem momentDet_comp_swap (c : Fin g → ℕ) {m m' : Fin g} (hmm : m ≠ m') :
    momentDet g q (c ∘ Equiv.swap m m') = -momentDet g q c := by
  have h1 : (Matrix.of fun i m'' : Fin g ↦
      (q * X ^ (c ∘ Equiv.swap m m') m'').coeff (2 * (i : ℕ) + 1))
      = (Matrix.of fun i m'' : Fin g ↦
        (q * X ^ c m'').coeff (2 * (i : ℕ) + 1)).submatrix id (Equiv.swap m m') := by
    ext i m''
    rfl
  rw [momentDet, h1, Matrix.det_permute', Equiv.Perm.sign_swap hmm, momentDet]
  simp

/-- A choice function of total shift at most one is zero, or takes the value `1` at a
single index. -/
private theorem sum_le_one_cases {ρ : ℕ} {s : Finset (Fin g)} {σ : Fin g → Fin ρ}
    (h : ∑ m ∈ s, (σ m : ℕ) ≤ 1) :
    (∀ m ∈ s, (σ m : ℕ) = 0) ∨
      ∃ p ∈ s, (σ p : ℕ) = 1 ∧ ∀ m ∈ s, m ≠ p → (σ m : ℕ) = 0 := by
  by_cases hz : ∀ m ∈ s, (σ m : ℕ) = 0
  · exact .inl hz
  · obtain ⟨p, hps, hp⟩ := not_forall₂.mp hz
    have h1 : (σ p : ℕ) ≤ 1 := (Finset.single_le_sum (fun m _ ↦ Nat.zero_le _) hps).trans h
    have h2 := Finset.add_sum_erase s (fun m ↦ (σ m : ℕ)) hps
    refine .inr ⟨p, hps, by lia, fun m hms hmp ↦ ?_⟩
    lia [Finset.single_le_sum (f := fun m' ↦ (σ m' : ℕ)) (fun m' _ ↦ Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hmp, hms⟩)]

/-- The surviving choice of a peel at the identity pattern (size `g + 1`, node polynomial
of degree at most `g`): shift the last column once, moving the identity pattern to
`peelPattern (g+1) g`. -/
def idPeelChoice (g ρ : ℕ) [NeZero ρ] : Fin (g + 1) → Fin ρ :=
  fun m ↦ if m = Fin.last g then 1 else 0

/-- **Vanishing at an identity-pattern peel**: every choice of total shift at most one
other than the surviving one has vanishing pattern determinant. -/
theorem idPeel_det_eq_zero {ρ : ℕ} [NeZero ρ] (hq : q.natDegree ≤ g)
    {σ : Fin (g + 1) → Fin ρ} (hσ : shiftSum σ ≤ 1) (hne : σ ≠ idPeelChoice g ρ) :
    momentDet (g + 1) q (fun m ↦ (m : ℕ) + (σ m : ℕ)) = 0 := by
  rcases sum_le_one_cases (s := Finset.univ) (by rwa [← shiftSum]) with
    h | ⟨p, -, hp1, hp0⟩
  · -- no shift at all: the matrix misses the top row
    refine momentDet_eq_zero_of_block (m₀ := Fin.last g) fun m hm ↦ ?_
    rw [h m (Finset.mem_univ m)]
    have := m.isLt
    rw [Fin.val_last]
    lia
  · rcases eq_or_ne p (Fin.last g) with rfl | hpl
    · -- the shifted column is the last one: `σ` is the survivor
      refine absurd (_root_.funext fun m ↦ ?_) hne
      rw [idPeelChoice]
      rcases eq_or_ne m (Fin.last g) with rfl | hml
      · rw [ite_eq_left rfl]
        refine Fin.ext ?_
        rw [hp1, Fin.val_one']
        exact (Nat.mod_eq_of_lt (hp1 ▸ (σ (Fin.last g)).isLt)).symm
      · rw [ite_eq_right hml]
        exact Fin.ext (hp0 m (Finset.mem_univ m) hml)
    · -- the shifted column collides with its right neighbour
      have hlt : (p : ℕ) + 1 < g + 1 := by
        have h1 := Fin.lt_last_iff_ne_last.mpr hpl
        rw [Fin.lt_def, Fin.val_last] at h1
        lia
      refine momentDet_eq_zero_of_eq (m := p) (m' := ⟨(p : ℕ) + 1, hlt⟩)
        ?_ (Fin.ne_of_val_ne (show (p : ℕ) ≠ (p : ℕ) + 1 by lia))
      rw [hp1, hp0 ⟨(p : ℕ) + 1, hlt⟩ (Finset.mem_univ _)
        (Fin.ne_of_val_ne (show (p : ℕ) + 1 ≠ (p : ℕ) by lia))]

/-- The survivor of an identity-pattern peel moves the pattern to `peelPattern (g+1) g`. -/
theorem id_add_idPeelChoice {ρ : ℕ} [NeZero ρ] (hρ : 2 ≤ ρ) :
    (fun m : Fin (g + 1) ↦ (m : ℕ) + (idPeelChoice g ρ m : ℕ)) = peelPattern (g + 1) g := by
  funext m
  rw [idPeelChoice]
  rcases eq_or_ne m (Fin.last g) with rfl | hml
  · rw [ite_eq_left rfl, peelPattern_of_le (by rw [Fin.val_last]), Fin.val_one',
      Nat.mod_eq_of_lt hρ, Fin.val_last]
    lia
  · have h1 := Fin.lt_last_iff_ne_last.mpr hml
    rw [Fin.lt_def, Fin.val_last] at h1
    rw [ite_eq_right hml, peelPattern_of_lt h1]
    rfl

/-- The total shift of the identity-pattern survivor. -/
theorem shiftSum_idPeelChoice {ρ : ℕ} [NeZero ρ] (hρ : 2 ≤ ρ) :
    shiftSum (idPeelChoice g ρ) = 1 := by
  rw [shiftSum, Fin.sum_univ_castSucc]
  simp [idPeelChoice, Fin.castSucc_ne_last, Nat.mod_eq_of_lt hρ]

/-- **The identity-pattern stage identity**: peeling any factor `F` off a node polynomial
of degree at most `g` at the identity pattern of size `g + 1` moves the pattern to
`peelPattern (g+1) g`, with coefficient `F.coeff 0 ^ g * F.coeff 1`. Instantiations:
the doubled peel `F = (u+X)²` at `r - G' = 1` (coefficient `2·u^(2g+1)`) and the signed
trio `F = (u+X)²(X-u)` (coefficient `(-1)^(g+1)·u^(3g+2)`). -/
theorem peelStage_id {F : R[X]} {ρ : ℕ} [NeZero ρ] (hρ : 2 ≤ ρ) (hF : F.natDegree < ρ)
    (hq : q.natDegree ≤ g) :
    momentDet (g + 1) (q * F) (fun m ↦ (m : ℕ))
      = F.coeff 0 ^ g * F.coeff 1 * momentDet (g + 1) q (peelPattern (g + 1) g)
        + ∑ σ ∈ Finset.univ.filter fun σ : Fin (g + 1) → Fin ρ ↦ 2 ≤ shiftSum σ,
            (∏ m, F.coeff (σ m : ℕ))
              * momentDet (g + 1) q (fun m ↦ (m : ℕ) + (σ m : ℕ)) := by
  rw [momentDet_mul hF, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun σ : Fin (g + 1) → Fin ρ ↦ 2 ≤ shiftSum σ), add_comm]
  congr 1
  rw [Finset.sum_eq_single_of_mem (idPeelChoice g ρ)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [shiftSum_idPeelChoice hρ]; lia⟩)
    fun σ hσ hne ↦ mul_eq_zero_of_right _ (idPeel_det_eq_zero hq
      (by have := (Finset.mem_filter.mp hσ).2; lia) hne),
    id_add_idPeelChoice hρ]
  congr 1
  have h1 (m : Fin (g + 1)) : F.coeff (idPeelChoice g ρ m : ℕ)
      = if m = Fin.last g then F.coeff ((1 : Fin ρ) : ℕ) else F.coeff 0 := by
    rw [idPeelChoice]
    split_ifs <;> rfl
  rw [Finset.prod_congr rfl fun m _ ↦ h1 m, Fin.prod_univ_castSucc]
  rw [Finset.prod_congr rfl fun m _ ↦ ite_eq_right (Fin.castSucc_lt_last m).ne, ite_eq_left rfl,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fin.val_one',
    Nat.mod_eq_of_lt hρ]

private theorem card_filter_lt_val {g r : ℕ} (hr : r ≤ g) :
    (Finset.univ.filter fun m : Fin g ↦ (m : ℕ) < r).card = r := by
  have h1 : (Finset.univ.filter fun m : Fin g ↦ (m : ℕ) < r)
      = Finset.univ \ Finset.univ.filter fun m : Fin g ↦ r ≤ (m : ℕ) := by
    rw [← Finset.filter_not]
    exact Finset.filter_congr fun m _ ↦ not_le.symm
  rw [h1, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), card_filter_le_val hr,
    Finset.card_univ, Fintype.card_fin]
  lia

/-- The surviving choice of a doubled peel at stage `r + 2` (node polynomial of degree at
most `r`): keep the low columns, shift the column at `r` once and all later columns twice.
Valuewise it is the sum of the two single-peel survivors at `r + 1` and `r`, so it moves
the stage pattern `c_(r+2)` to `c_r`. -/
def doublePeelChoice (g r : ℕ) : Fin g → Fin 3 :=
  fun m ↦ if (m : ℕ) < r then 0 else if (m : ℕ) = r then 1 else 2

theorem doublePeelChoice_val {r : ℕ} (m : Fin g) :
    (doublePeelChoice g r m : ℕ)
      = (singlePeelChoice g (r + 1) m : ℕ) + (singlePeelChoice g r m : ℕ) := by
  simp only [doublePeelChoice, singlePeelChoice]
  split_ifs <;> simp <;> lia

theorem peelPattern_add_doublePeelChoice (g r : ℕ) :
    (fun m ↦ peelPattern g (r + 2) m + (doublePeelChoice g r m : ℕ)) = peelPattern g r := by
  funext m
  rw [doublePeelChoice_val, ← add_assoc,
    show peelPattern g (r + 2) m + (singlePeelChoice g (r + 1) m : ℕ)
      = peelPattern g (r + 1) m from congrFun (peelPattern_add_singlePeelChoice g (r + 1)) m,
    show peelPattern g (r + 1) m + (singlePeelChoice g r m : ℕ) = peelPattern g r m from
      congrFun (peelPattern_add_singlePeelChoice g r) m]

theorem shiftSum_doublePeelChoice {r : ℕ} (hr : r + 2 ≤ g) :
    shiftSum (doublePeelChoice g r) = 2 * g - 2 * r - 1 := by
  rw [shiftSum, Finset.sum_congr rfl fun m _ ↦ doublePeelChoice_val m,
    Finset.sum_add_distrib, ← shiftSum, ← shiftSum, shiftSum_singlePeelChoice (by lia),
    shiftSum_singlePeelChoice (by lia)]
  lia

/-- The weight of the doubled survivor collects the three column regions. -/
private theorem prod_doublePeelChoice {f : ℕ → R} {r : ℕ} (hr : r + 2 ≤ g) :
    ∏ m : Fin g, f (doublePeelChoice g r m : ℕ) = f 0 ^ r * f 1 * f 2 ^ (g - r - 1) := by
  have h1 (m : Fin g) : f (doublePeelChoice g r m : ℕ)
      = if (m : ℕ) < r then f 0 else if (m : ℕ) = r then f 1 else f 2 := by
    simp only [doublePeelChoice]
    split_ifs <;> rfl
  have h2 : (Finset.univ.filter fun m : Fin g ↦ ¬(m : ℕ) < r).filter (fun m : Fin g ↦ (m : ℕ) = r)
      = {⟨r, by lia⟩} := by
    refine Finset.ext fun m ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_univ, true_and,
      Fin.ext_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨by lia, h⟩⟩
  have h3 : (Finset.univ.filter fun m : Fin g ↦ ¬(m : ℕ) < r).filter (fun m : Fin g ↦ ¬(m : ℕ) = r)
      = Finset.univ.filter fun m : Fin g ↦ r + 1 ≤ (m : ℕ) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun m _ ↦ ⟨fun h ↦ by lia, fun h ↦ ⟨by lia, by lia⟩⟩
  rw [Finset.prod_congr rfl fun m _ ↦ h1 m, Finset.prod_ite, Finset.prod_const,
    card_filter_lt_val (by lia), Finset.prod_ite, h2, h3, Finset.prod_singleton,
    Finset.prod_const, card_filter_le_val (by lia),
    show g - (r + 1) = g - r - 1 from (Nat.sub_sub g r 1).symm, mul_assoc]

/-- **Vanishing at a doubled peel** (node polynomial of degree at most `r`, stage pattern
`c_(r+2)`): every choice of total shift at most `2g - 2r - 1` other than the surviving one
has vanishing pattern determinant — an under-shifted jump column, the column at `r + 1`
under-shifting, all low columns unshifted, or a repeated column. -/
theorem doublePeel_det_eq_zero {r : ℕ} (hq : q.natDegree ≤ r) (hr : r + 2 ≤ g)
    {σ : Fin g → Fin 3} (hσ : shiftSum σ + 2 * r + 1 ≤ 2 * g)
    (hne : σ ≠ doublePeelChoice g r) :
    momentDet g q (fun m ↦ peelPattern g (r + 2) m + (σ m : ℕ)) = 0 := by
  by_cases hB : ∃ m₀ : Fin g, r + 2 ≤ (m₀ : ℕ) ∧ (σ m₀ : ℕ) ≤ 1
  · -- an under-shifted jump column cuts a zero block below and left of itself
    obtain ⟨m₀, hm₀, hσ0⟩ := hB
    refine momentDet_eq_zero_of_block (m₀ := m₀) fun m hm ↦ ?_
    have h2 := Fin.le_def.mp hm
    have h3 := (σ m).isLt
    rcases Nat.lt_or_ge (m : ℕ) (r + 2) with h4 | h4
    · rw [peelPattern_of_lt h4]
      lia
    · rw [peelPattern_of_le h4]
      rcases eq_or_lt_of_le h2 with h5 | h5
      · rw [show m = m₀ from Fin.ext h5]
        lia
      · lia
  · -- all jump columns doubly shift
    have hB1 : ∀ m : Fin g, r + 2 ≤ (m : ℕ) → (σ m : ℕ) = 2 := by
      intro m hm
      have h1 := (σ m).isLt
      by_contra hc
      exact hB ⟨m, hm, by lia⟩
    by_cases hA1 : (σ ⟨r + 1, by lia⟩ : ℕ) ≤ 1
    · -- the column at `r + 1` under-shifts: the rows from `r + 1` on are cut off
      refine momentDet_eq_zero_of_block (m₀ := ⟨r + 1, by lia⟩) fun m hm ↦ ?_
      have h2 := Fin.le_def.mp hm
      have h3 := (σ m).isLt
      have h4 : ((⟨r + 1, by lia⟩ : Fin g) : ℕ) = r + 1 := rfl
      rw [h4] at h2
      rw [peelPattern_of_lt (by lia)]
      rcases eq_or_lt_of_le h2 with h5 | h5
      · rw [show m = ⟨r + 1, by lia⟩ from Fin.ext (by lia)]
        lia
      · lia
    · have hA1' : (σ ⟨r + 1, by lia⟩ : ℕ) = 2 := by lia
      have hB2 : ∀ m : Fin g, r + 1 ≤ (m : ℕ) → (σ m : ℕ) = 2 := by
        intro m hm
        rcases eq_or_lt_of_le hm with h | h
        · rw [show m = ⟨r + 1, by lia⟩ from Fin.ext h.symm]
          exact hA1'
        · exact hB1 m (by lia)
      -- the low columns carry total shift at most one
      have hlow : ∑ m ∈ Finset.univ.filter (fun m : Fin g ↦ (m : ℕ) ≤ r), (σ m : ℕ) ≤ 1 := by
        have h1 := Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun m : Fin g ↦ (m : ℕ) ≤ r) (fun m ↦ (σ m : ℕ))
        have h2 : ∑ m ∈ Finset.univ.filter (fun m : Fin g ↦ ¬(m : ℕ) ≤ r), (σ m : ℕ)
            = 2 * (g - (r + 1)) := by
          rw [Finset.sum_congr rfl fun m hm ↦
              hB2 m (by have := (Finset.mem_filter.mp hm).2; lia),
            Finset.sum_const, smul_eq_mul, mul_comm]
          congr 1
          rw [show (Finset.univ.filter fun m : Fin g ↦ ¬(m : ℕ) ≤ r)
              = Finset.univ.filter fun m : Fin g ↦ r + 1 ≤ (m : ℕ) from
            Finset.filter_congr fun m _ ↦ ⟨fun h ↦ by lia, fun h ↦ by lia⟩]
          exact card_filter_le_val (by lia)
        rw [shiftSum, ← h1, h2] at hσ
        lia
      rcases sum_le_one_cases hlow with h | ⟨p, hp, hp1, hp0⟩
      · -- no low column shifts: the top rows see only shifted columns
        refine momentDet_eq_zero_of_block (m₀ := ⟨r, by lia⟩) fun m hm ↦ ?_
        have h2 := Fin.le_def.mp hm
        have h4 : ((⟨r, by lia⟩ : Fin g) : ℕ) = r := rfl
        rw [h4] at h2
        rw [h m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩),
          peelPattern_of_lt (by lia), h4]
        lia
      · have hpr : (p : ℕ) ≤ r := (Finset.mem_filter.mp hp).2
        rcases eq_or_lt_of_le hpr with hpe | hpe
        · -- the shifted low column is at `r`: `σ` is the survivor
          refine absurd (_root_.funext fun m ↦ ?_) hne
          rw [doublePeelChoice]
          rcases lt_trichotomy (m : ℕ) r with h1 | h1 | h1
          · rw [ite_eq_left h1]
            exact Fin.ext (hp0 m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by lia⟩)
              fun hc ↦ by rw [hc] at h1; lia)
          · rw [ite_eq_right (by lia), ite_eq_left h1]
            exact Fin.ext (by rw [show m = p from Fin.ext (by lia), hp1]; rfl)
          · rw [ite_eq_right (by lia), ite_eq_right (by lia)]
            exact Fin.ext (hB2 m (by lia))
        · -- collision: the shifted low column collides with its right neighbour
          have hlt : (p : ℕ) + 1 < g := by lia
          refine momentDet_eq_zero_of_eq (m := p) (m' := ⟨(p : ℕ) + 1, hlt⟩) ?_
            (Fin.ne_of_val_ne (show (p : ℕ) ≠ (p : ℕ) + 1 by lia))
          rw [hp1, hp0 ⟨(p : ℕ) + 1, hlt⟩
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, show (p : ℕ) + 1 ≤ r by lia⟩)
              (Fin.ne_of_val_ne (show (p : ℕ) + 1 ≠ (p : ℕ) by lia)),
            peelPattern_of_lt (show (p : ℕ) < r + 2 by lia),
            peelPattern_of_lt (show (p : ℕ) + 1 < r + 2 by lia)]

/-- **The doubled-peel stage identity**: peeling a factor `F` of degree at most two off a
node polynomial of degree at most `r` moves the stage pattern `c_(r+2)` to `c_r`, with
coefficient `F.coeff 0 ^ r * F.coeff 1 * F.coeff 2 ^ (g-r-1)` — for `F = (u+X)²` this is
`2·u^(2r+1)`, the `κ = 2` of the doubled peel at `r - G' = 2`. -/
theorem peelStage_double {F : R[X]} {r : ℕ} (hF : F.natDegree < 3) (hq : q.natDegree ≤ r)
    (hr : r + 2 ≤ g) :
    momentDet g (q * F) (peelPattern g (r + 2))
      = F.coeff 0 ^ r * F.coeff 1 * F.coeff 2 ^ (g - r - 1) * momentDet g q (peelPattern g r)
        + ∑ σ ∈ Finset.univ.filter fun σ : Fin g → Fin 3 ↦ 2 * g < shiftSum σ + 2 * r + 1,
            (∏ m, F.coeff (σ m : ℕ))
              * momentDet g q (fun m ↦ peelPattern g (r + 2) m + (σ m : ℕ)) := by
  rw [momentDet_mul hF, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun σ : Fin g → Fin 3 ↦ 2 * g < shiftSum σ + 2 * r + 1), add_comm]
  congr 1
  rw [Finset.sum_eq_single_of_mem (doublePeelChoice g r)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [shiftSum_doublePeelChoice hr]; lia⟩)
    fun σ hσ hne ↦ mul_eq_zero_of_right _ (doublePeel_det_eq_zero hq hr
      (by have := (Finset.mem_filter.mp hσ).2; lia) hne),
    peelPattern_add_doublePeelChoice, prod_doublePeelChoice hr]

/-- The values of the shift choice of a nearly maximal single column vanish elsewhere. -/
private theorem eq_zero_of_shiftSum_le {ρ : ℕ} {σ : Fin g → Fin ρ} {m₁ : Fin g} {k : ℕ}
    (h : shiftSum σ ≤ k) (hm : k ≤ (σ m₁ : ℕ)) {m : Fin g} (hmm : m ≠ m₁) :
    (σ m : ℕ) = 0 := by
  have h1 := Finset.add_sum_erase Finset.univ (fun m ↦ (σ m : ℕ)) (Finset.mem_univ m₁)
  have h2 : (σ m : ℕ) ≤ ∑ m' ∈ Finset.univ.erase m₁, (σ m' : ℕ) :=
    Finset.single_le_sum (f := fun m' ↦ (σ m' : ℕ)) (fun m' _ ↦ Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hmm, Finset.mem_univ m⟩)
  rw [shiftSum] at h
  lia

/-- The main surviving choice of a tripled peel at the identity pattern (size `g + 2`,
node polynomial of degree at most `g`): shift the column at `g` once and the last column
twice. Valuewise it is `doublePeelChoice (g+2) g`. -/
def triplePeelChoice (g : ℕ) : Fin (g + 2) → Fin 4 :=
  fun m ↦ if (m : ℕ) < g then 0 else if (m : ℕ) = g then 1 else 2

/-- The interfering choice of a tripled peel: the whole triple shift on the column at `g`,
reaching the swapped survivor pattern. -/
def tripleSwapChoice (g : ℕ) : Fin (g + 2) → Fin 4 :=
  fun m ↦ if (m : ℕ) = g then 3 else 0

theorem triplePeelChoice_val (m : Fin (g + 2)) :
    (triplePeelChoice g m : ℕ) = (doublePeelChoice (g + 2) g m : ℕ) := by
  simp only [triplePeelChoice, doublePeelChoice]
  split_ifs <;> rfl

theorem shiftSum_triplePeelChoice : shiftSum (triplePeelChoice g) = 3 := by
  rw [shiftSum, Finset.sum_congr rfl fun m _ ↦ triplePeelChoice_val m, ← shiftSum,
    shiftSum_doublePeelChoice (by lia)]
  lia

theorem shiftSum_tripleSwapChoice : shiftSum (tripleSwapChoice g) = 3 := by
  have h1 (m : Fin (g + 2)) : (tripleSwapChoice g m : ℕ)
      = if m = (⟨g, by lia⟩ : Fin (g + 2)) then 3 else 0 := by
    simp only [tripleSwapChoice]
    rcases eq_or_ne (m : ℕ) g with h | h
    · rw [ite_eq_left h, ite_eq_left (Fin.ext h)]
      rfl
    · rw [ite_eq_right h, ite_eq_right fun hc ↦ h (by rw [hc])]
      rfl
  rw [shiftSum, Finset.sum_congr rfl fun m _ ↦ h1 m,
    Finset.sum_ite_eq' Finset.univ (⟨g, by lia⟩ : Fin (g + 2)) fun _ ↦ 3,
    ite_eq_left (Finset.mem_univ _)]

/-- The main tripled survivor moves the identity pattern to `peelPattern (g+2) g`. -/
theorem id_add_triplePeelChoice :
    (fun m : Fin (g + 2) ↦ (m : ℕ) + (triplePeelChoice g m : ℕ))
      = peelPattern (g + 2) g := by
  rw [show (fun m : Fin (g + 2) ↦ (m : ℕ) + (triplePeelChoice g m : ℕ))
      = fun m : Fin (g + 2) ↦ peelPattern (g + 2) (g + 2) m + (doublePeelChoice (g + 2) g m : ℕ)
    from funext fun m ↦ by
      rw [triplePeelChoice_val, peelPattern_of_lt m.isLt]]
  exact peelPattern_add_doublePeelChoice (g + 2) g

/-- The interfering tripled survivor reaches the swapped pattern. -/
theorem id_add_tripleSwapChoice :
    (fun m : Fin (g + 2) ↦ (m : ℕ) + (tripleSwapChoice g m : ℕ))
      = peelPattern (g + 2) g ∘ Equiv.swap ⟨g, by lia⟩ ⟨g + 1, by lia⟩ := by
  have e1 : ((⟨g, by lia⟩ : Fin (g + 2)) : ℕ) = g := rfl
  have e2 : ((⟨g + 1, by lia⟩ : Fin (g + 2)) : ℕ) = g + 1 := rfl
  funext m
  rw [Function.comp_apply, tripleSwapChoice]
  rcases lt_trichotomy (m : ℕ) g with h | h | h
  · rw [ite_eq_right (by lia), Equiv.swap_apply_of_ne_of_ne
      (Fin.ne_of_val_ne (show (m : ℕ) ≠ g by lia))
      (Fin.ne_of_val_ne (show (m : ℕ) ≠ g + 1 by lia)), peelPattern_of_lt h,
      show ((0 : Fin 4) : ℕ) = 0 from rfl, add_zero]
  · rw [ite_eq_left h, show m = (⟨g, by lia⟩ : Fin (g + 2)) from Fin.ext h, Equiv.swap_apply_left,
      peelPattern_of_le (show g ≤ g + 1 by lia), e1, e2,
      show ((3 : Fin 4) : ℕ) = 3 from rfl]
    lia
  · have h1 : (m : ℕ) = g + 1 := by have := m.isLt; lia
    rw [ite_eq_right (by lia), show m = (⟨g + 1, by lia⟩ : Fin (g + 2)) from Fin.ext h1,
      Equiv.swap_apply_right, peelPattern_of_le (show g ≤ g by lia), e1, e2,
      show ((0 : Fin 4) : ℕ) = 0 from rfl]
    lia

/-- The weight of the interfering tripled survivor. -/
private theorem prod_tripleSwapChoice {f : ℕ → R} :
    ∏ m : Fin (g + 2), f (tripleSwapChoice g m : ℕ) = f 0 ^ (g + 1) * f 3 := by
  have h1 (m : Fin (g + 2)) : f (tripleSwapChoice g m : ℕ)
      = if m = (⟨g, by lia⟩ : Fin (g + 2)) then f 3 else f 0 := by
    simp only [tripleSwapChoice]
    rcases eq_or_ne (m : ℕ) g with h | h
    · rw [ite_eq_left h, ite_eq_left (Fin.ext h), show ((3 : Fin 4) : ℕ) = 3 from rfl]
    · rw [ite_eq_right h, ite_eq_right fun hc ↦ h (by rw [hc]), show ((0 : Fin 4) : ℕ) = 0 from rfl]
  rw [Finset.prod_congr rfl fun m _ ↦ h1 m,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨g, by lia⟩ : Fin (g + 2))),
    ite_eq_left rfl, Finset.prod_congr rfl fun m hm ↦ ite_eq_right (Finset.mem_erase.mp hm).1,
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, show g + 2 - 1 = g + 1 from rfl, mul_comm]

/-- **Vanishing at a tripled peel** (identity pattern, node polynomial of degree at most
`g`): every choice of total shift at most three other than the two surviving ones has
vanishing pattern determinant. -/
theorem triplePeel_det_eq_zero (hq : q.natDegree ≤ g) {σ : Fin (g + 2) → Fin 4}
    (hσ : shiftSum σ ≤ 3) (hne1 : σ ≠ triplePeelChoice g) (hne2 : σ ≠ tripleSwapChoice g) :
    momentDet (g + 2) q (fun m ↦ (m : ℕ) + (σ m : ℕ)) = 0 := by
  by_cases hall : ∀ m : Fin (g + 2), (m : ℕ) + (σ m : ℕ) ≤ g + 2
  · -- all shifted columns stay in range: the top row is out of reach
    refine momentDet_eq_zero_of_block (m₀ := Fin.last (g + 1)) fun m hm ↦ ?_
    have h1 := hall m
    rw [Fin.val_last]
    lia
  · obtain ⟨m₁, hm₁⟩ : ∃ m : Fin (g + 2), g + 3 ≤ (m : ℕ) + (σ m : ℕ) := by
      by_contra! hc
      exact hall fun m ↦ by have := hc m; lia
    have hval := m₁.isLt
    have hσ4 := (σ m₁).isLt
    rcases eq_or_lt_of_le (show (m₁ : ℕ) ≤ g + 1 by lia) with hlast | hlast
    · -- the overflowing column is the last one
      rcases eq_or_lt_of_le (show 2 ≤ (σ m₁ : ℕ) by lia) with hσ2 | hσ2
      · -- doubly shifted last column: at most one more shift, on a low column
        have herase : ∑ m ∈ Finset.univ.erase m₁, (σ m : ℕ) ≤ 1 := by
          have h1 := Finset.add_sum_erase Finset.univ (fun m ↦ (σ m : ℕ))
            (Finset.mem_univ m₁)
          rw [shiftSum] at hσ
          lia
        rcases sum_le_one_cases herase with h | ⟨p, hp, hp1, hp0⟩
        · -- no other shift: the row at `g` is out of reach
          refine momentDet_eq_zero_of_block (m₀ := ⟨g, by lia⟩) fun m hm ↦ ?_
          have h2 := Fin.le_def.mp hm
          rw [h m (Finset.mem_erase.mpr
            ⟨fun hc ↦ by rw [hc, hlast] at h2; lia, Finset.mem_univ m⟩)]
          lia
        · have hpg : (p : ℕ) ≤ g := by
            have h1 := (Finset.mem_erase.mp hp).1
            have h2 := p.isLt
            rcases eq_or_lt_of_le (show (p : ℕ) ≤ g + 1 by lia) with h3 | h3
            · exact absurd (Fin.ext (h3.trans hlast.symm)) h1
            · lia
          rcases eq_or_lt_of_le hpg with hpe | hpe
          · -- survivor: shift one at `g`, two at the last column
            refine absurd (_root_.funext fun m ↦ ?_) hne1
            rw [triplePeelChoice]
            rcases lt_trichotomy (m : ℕ) g with h1 | h1 | h1
            · rw [ite_eq_left h1]
              exact Fin.ext (hp0 m (Finset.mem_erase.mpr
                ⟨fun hc ↦ by rw [hc, hlast] at h1; lia, Finset.mem_univ m⟩)
                fun hc ↦ by rw [hc] at h1; lia)
            · rw [ite_eq_right (by lia), ite_eq_left h1]
              exact Fin.ext (by rw [show m = p from Fin.ext (by lia), hp1]; rfl)
            · rw [ite_eq_right (by lia), ite_eq_right (by lia)]
              have h2 : m = m₁ := Fin.ext (by have := m.isLt; lia)
              exact Fin.ext (by rw [h2, ← hσ2]; rfl)
          · -- collision: the shifted low column collides with its right neighbour
            have hlt : (p : ℕ) + 1 < g + 2 := by lia
            refine momentDet_eq_zero_of_eq (m := p) (m' := ⟨(p : ℕ) + 1, hlt⟩) ?_
              (Fin.ne_of_val_ne (show (p : ℕ) ≠ (p : ℕ) + 1 by lia))
            rw [hp1, hp0 ⟨(p : ℕ) + 1, hlt⟩ (Finset.mem_erase.mpr
                ⟨Fin.ne_of_val_ne (show (p : ℕ) + 1 ≠ (m₁ : ℕ) by lia), Finset.mem_univ _⟩)
              (Fin.ne_of_val_ne (show (p : ℕ) + 1 ≠ (p : ℕ) by lia))]
      · -- triply shifted last column: everything else is unshifted
        refine momentDet_eq_zero_of_block (m₀ := ⟨g, by lia⟩) fun m hm ↦ ?_
        have h2 := Fin.le_def.mp hm
        rw [eq_zero_of_shiftSum_le hσ (show 3 ≤ (σ m₁ : ℕ) by lia)
          (fun hc ↦ by rw [hc, hlast] at h2; lia)]
        lia
    · -- the overflowing column is at `g`, triply shifted: the interfering survivor
      have hg : (m₁ : ℕ) = g := by lia
      have hσ3 : (σ m₁ : ℕ) = 3 := by lia
      refine absurd (_root_.funext fun m ↦ ?_) hne2
      rw [tripleSwapChoice]
      rcases eq_or_ne (m : ℕ) g with h | h
      · rw [ite_eq_left h, show m = m₁ from Fin.ext (by lia)]
        exact Fin.ext (by rw [hσ3]; rfl)
      · rw [ite_eq_right h]
        exact Fin.ext (eq_zero_of_shiftSum_le hσ (show 3 ≤ (σ m₁ : ℕ) by lia)
          fun hc ↦ h (by rw [hc, hg]))

/-- **The tripled-peel stage identity** (identity pattern of size `g + 2`, node polynomial
of degree at most `g`): the two surviving choices combine — the swapped one with a negative
sign — into the coefficient `F.coeff 0 ^ g * (F.coeff 1 * F.coeff 2 - F.coeff 0 * F.coeff 3)`
at `peelPattern (g+2) g`. For `F = (u+X)³` this is `(9-1)·u^(3g+3) = 8·u^(3g+3)`: the
tripled certificate coefficient stays a power of two. -/
theorem peelStage_triple_id {F : R[X]} (hF : F.natDegree < 4) (hq : q.natDegree ≤ g) :
    momentDet (g + 2) (q * F) (fun m ↦ (m : ℕ))
      = F.coeff 0 ^ g * (F.coeff 1 * F.coeff 2 - F.coeff 0 * F.coeff 3)
          * momentDet (g + 2) q (peelPattern (g + 2) g)
        + ∑ σ ∈ Finset.univ.filter fun σ : Fin (g + 2) → Fin 4 ↦ 4 ≤ shiftSum σ,
            (∏ m, F.coeff (σ m : ℕ))
              * momentDet (g + 2) q (fun m ↦ (m : ℕ) + (σ m : ℕ)) := by
  have hswapne : (⟨g, by lia⟩ : Fin (g + 2)) ≠ ⟨g + 1, by lia⟩ :=
    Fin.ne_of_val_ne (show g ≠ g + 1 by lia)
  have hchoicene : triplePeelChoice g ≠ tripleSwapChoice g := fun hc ↦
    absurd (congrFun hc (⟨g, by lia⟩ : Fin (g + 2)))
      (by simp [triplePeelChoice, tripleSwapChoice])
  have hpa : ∏ m, F.coeff (triplePeelChoice g m : ℕ)
      = F.coeff 0 ^ g * F.coeff 1 * F.coeff 2 := by
    rw [Finset.prod_congr rfl fun m _ ↦ by rw [triplePeelChoice_val m],
      prod_doublePeelChoice (f := fun k ↦ F.coeff k) (by lia),
      show g + 2 - g - 1 = 1 by lia, pow_one]
  rw [momentDet_mul hF, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun σ : Fin (g + 2) → Fin 4 ↦ 4 ≤ shiftSum σ), add_comm]
  congr 1
  rw [Finset.sum_eq_add_of_mem (triplePeelChoice g) (tripleSwapChoice g)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [shiftSum_triplePeelChoice]; lia⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [shiftSum_tripleSwapChoice]; lia⟩)
    hchoicene
    fun σ hσ hne ↦ mul_eq_zero_of_right _ (triplePeel_det_eq_zero hq
      (by have := (Finset.mem_filter.mp hσ).2; lia) hne.1 hne.2),
    hpa, prod_tripleSwapChoice (f := fun k ↦ F.coeff k), id_add_triplePeelChoice,
    id_add_tripleSwapChoice, momentDet_comp_swap _ hswapne]
  ring

/-- **The lead peel identity**: for any peeled factor `F`, the choice `σ = 0` contributes
`(F.coeff 0) ^ g` at the unchanged pattern, and every other choice carries a weight of
smaller `u`-degree. This is the entire stage lemma for the peels whose pattern determinant
survives unchanged — the doubled and signed leads at `r - G' ≤ 0`, where `(F.coeff 0) ^ g`
is `u ^ (2g)`, `(-1)^g u^(2g)` (signed pair), or `± u^(3g)` (trios). -/
theorem peelStage_lead {F : R[X]} {ρ : ℕ} [NeZero ρ] (hF : F.natDegree < ρ)
    (c : Fin g → ℕ) :
    momentDet g (q * F) c
      = F.coeff 0 ^ g * momentDet g q c
        + ∑ σ ∈ Finset.univ.filter fun σ : Fin g → Fin ρ ↦ σ ≠ 0,
            (∏ m, F.coeff (σ m : ℕ)) * momentDet g q (fun m ↦ c m + (σ m : ℕ)) := by
  rw [momentDet_mul hF c, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun σ : Fin g → Fin ρ ↦ σ ≠ 0), add_comm]
  congr 1
  rw [Finset.sum_eq_single_of_mem (0 : Fin g → Fin ρ)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩)
    fun σ hσ hne ↦ absurd (not_ne_iff.mp (Finset.mem_filter.mp hσ).2) hne]
  have h0 (m : Fin g) : (((0 : Fin g → Fin ρ) m) : ℕ) = 0 := by rw [Pi.zero_apply, Fin.val_zero]
  simp only [h0, add_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The single-peel stage identity**: multiplying the node polynomial (of degree at most
`r`) by a monic linear factor moves the stage pattern `c_(r+1)` to `c_r`, with unit
coefficient at the top `u`-power `r`; all other choices of total shift at most `g - r`
vanish, so the remainder sum is over shifts with `u`-power less than `r` only. -/
theorem peelStage_single {r : ℕ} (hq : q.natDegree ≤ r) (hr : r < g) (u : R) :
    momentDet g (q * (C u + X)) (peelPattern g (r + 1))
      = u ^ r * momentDet g q (peelPattern g r)
        + ∑ σ ∈ Finset.univ.filter fun σ : Fin g → Fin 2 ↦ g < shiftSum σ + r,
            u ^ (g - shiftSum σ)
              * momentDet g q (fun m ↦ peelPattern g (r + 1) m + (σ m : ℕ)) := by
  have hF : (C u + X).natDegree < 2 :=
    (natDegree_add_le (C u) X).trans_lt
      (max_lt (by rw [natDegree_C]; lia) (natDegree_X_le.trans_lt (by lia)))
  rw [momentDet_mul hF, Finset.sum_congr rfl fun σ _ ↦ by rw [prod_coeff_C_add_X],
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun σ : Fin g → Fin 2 ↦ g < shiftSum σ + r), add_comm]
  congr 1
  rw [Finset.sum_eq_single_of_mem (singlePeelChoice g r)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [shiftSum_singlePeelChoice hr.le]; lia⟩)
    fun σ hσ hne ↦ mul_eq_zero_of_right _ (singlePeel_det_eq_zero hq hr
      (by have := (Finset.mem_filter.mp hσ).2; lia) hne),
    shiftSum_singlePeelChoice hr.le, peelPattern_add_singlePeelChoice,
    Nat.sub_sub_self hr.le]

end PeelStage

end ChabautyColeman

end
