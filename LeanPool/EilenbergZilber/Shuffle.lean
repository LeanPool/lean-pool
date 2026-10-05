/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li
-/
module

public import Mathlib.Tactic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Order.Fin.Basic

/-!
# Shuffles

A `(p, q)`-shuffle is an injective monotone map `Fin (p + q + 1) → Fin (p + 1) × Fin (q + 1)`,
i.e. a lattice path from `(0, 0)` to `(p, q)` taking unit left and right steps. This file develops
the combinatorics of shuffles needed for the Eilenberg–Zilber shuffle map: inversion counts and
signs, the boundary decomposition of a shuffle into insertions of left/right steps, and the
sign-reversing involution `swapDiagonalSteps` that cancels the diagonal boundary terms.
-/

@[expose] public section

noncomputable section

namespace LeanPool.EilenbergZilber

/-! ### Shuffles -/


/-- The finite chain object `0 ≤ 1 ≤ ··· ≤ k` in `PoSet`, represented by `Fin (k+1)`. -/
abbrev Index (k : ℕ) := Fin (k + 1)

/-- A `(p,q)`-shuffle as an injective monotone map
`Index (p + q) ⟶ Index p × Index q` in `PoSet`. -/
abbrev Shuffle (p q : ℕ) :=
  { φ : Index (p + q) →o (Index p × Index q) // Function.Injective φ }

namespace Shuffle

/-- There are finitely many (p,q)-shuffles: exactly `Nat.choose (p + q) p`. -/
noncomputable instance instFintype (p q : ℕ) : Fintype (Shuffle p q) := by
  classical
  have : Finite (Index (p + q) →o (Index p × Index q)) := by
    classical
    refine Finite.of_injective (fun f : Index (p + q) →o (Index p × Index q) => f.toFun) ?_
    intro f g h
    ext x
    repeat simp at h; simp [h]
  exact Fintype.ofFinite (Shuffle p q)

/-- The **number of inversions** of a shuffle. -/
def invCount {p q : ℕ} (μ : Shuffle p q) : ℕ :=
  ∑ r : Fin (p + q),
    if ((μ.1 (Fin.castSucc r)).1 < (μ.1 (Fin.succ r)).1) then
      ((μ.1 (Fin.castSucc r)).2).1
    else 0

/-- The sign of a shuffle: `(-1)^k` where `k` is the number of inversions. -/
def sign {p q : ℕ} (μ : Shuffle p q) : ℤ :=
  (-1 : ℤ) ^ μ.invCount

/-- Swap the two coordinates of a shuffle, yielding a `(q,p)`-shuffle. -/
def swap {p q : ℕ} (μ : Shuffle p q) : Shuffle q p := by
  classical
  let e : Index (q + p) ≃o Index (p + q) :=
    Fin.castOrderIso (by simp [Nat.add_comm, Nat.add_assoc])
  refine ⟨?_, ?_⟩
  · refine
      { toFun := fun x => (μ.1 (e x)).swap
        monotone' := ?_ }
    intro a b hab
    have h := μ.1.monotone (e.monotone hab)
    rcases h with ⟨h₁, h₂⟩
    exact ⟨h₂, h₁⟩
  · intro a b hab
    have hab' : μ.1 (e a) = μ.1 (e b) := Prod.swap_injective hab
    have : e a = e b := μ.2 hab'
    exact e.injective this

@[grind =, simp]
theorem swap_swap {p q : ℕ} (μ : Shuffle p q) : swap (swap μ) = μ := by
  classical
  apply Subtype.ext
  ext x
  repeat simp [swap]

/-- Swapping coordinates gives an equivalence `Shuffle p q ≃ Shuffle q p`. -/
def swapEquiv (p q : ℕ) : Shuffle p q ≃ Shuffle q p where
  toFun := swap
  invFun := swap
  left_inv μ := by simp
  right_inv μ := by simp

/-! #### Lattice path structure -/

/-- The coordinate sum `fst + snd` is strictly monotone along a shuffle path. -/
private lemma coordSum_lt {p q : ℕ} (u : Shuffle p q)
    {i j : Fin (p + q + 1)} (hij : i < j) :
    (u.1 i).1.val + (u.1 i).2.val < (u.1 j).1.val + (u.1 j).2.val := by
  have hmono := u.1.monotone (le_of_lt hij)
  have hinj : u.1 i ≠ u.1 j := fun h => (ne_of_lt hij) (u.2 h)
  obtain ⟨h1, h2⟩ := hmono
  -- Extract val-level inequalities for omega
  rcases Nat.lt_or_eq_of_le h1 with h1' | h1'
  · grind
  · rcases Nat.lt_or_eq_of_le h2 with h2' | h2'
    · grind
    · exact absurd (Prod.ext (Fin.ext h1') (Fin.ext h2')) hinj

/-- At every position `r`, the coordinate sum equals `r.val`. -/
@[grind =]
lemma coordSum_eq {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q + 1)) :
    (u.1 r).1.val + (u.1 r).2.val = r.val := by
  have castSucc_lt_succ : ∀ i : Fin (p + q), i.castSucc < i.succ := by
    intro i; simp [Fin.lt_def]
  apply le_antisymm
  · -- Upper bound by reverse induction: g(last) ≤ p + q, g(r) < g(r+1) ≤ r+1
    induction r using Fin.reverseInduction with
    | last =>
      have := (u.1 (Fin.last (p + q))).1.isLt
      have := (u.1 (Fin.last (p + q))).2.isLt
      simp [Fin.val_last]; omega
    | cast i ih =>
      have hlt := coordSum_lt u (castSucc_lt_succ i)
      simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢; omega
  · -- Lower bound by forward induction: g(0) ≥ 0, g(r+1) > g(r) ≥ r
    induction r using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hlt := coordSum_lt u (castSucc_lt_succ i)
      simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢; omega

/-- At each step of a shuffle, exactly one coordinate increases by 1. -/
private lemma shuffle_step {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) :
    ((u.1 r.castSucc).1.val + 1 = (u.1 r.succ).1.val ∧
     (u.1 r.castSucc).2.val = (u.1 r.succ).2.val) ∨
    ((u.1 r.castSucc).1.val = (u.1 r.succ).1.val ∧
     (u.1 r.castSucc).2.val + 1 = (u.1 r.succ).2.val) := by
  have hmono := u.1.monotone (show r.castSucc ≤ r.succ from by simp [Fin.le_def])
  obtain ⟨h1, h2⟩ := hmono
  have h1v : (u.1 r.castSucc).1.val ≤ (u.1 r.succ).1.val := h1
  have h2v : (u.1 r.castSucc).2.val ≤ (u.1 r.succ).2.val := h2
  have hsum1 := coordSum_eq u r.castSucc
  have hsum2 := coordSum_eq u r.succ
  simp only [Fin.val_succ, Fin.val_castSucc] at hsum1 hsum2
  omega

/-- First coordinate increases iff second doesn't at each step. -/
private lemma shuffle_fst_lt_iff_not_snd_lt {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) :
    (u.1 r.castSucc).1.val < (u.1 r.succ).1.val ↔
    ¬ ((u.1 r.castSucc).2.val < (u.1 r.succ).2.val) := by
  rcases shuffle_step u r with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega


/-- A shuffle path crosses every intermediate `snd`-level: for `i + 1 ≤ q` there is a step `a`
that is a **`q`-step at level `i`** — the second coordinate goes `i → i + 1` while the first
coordinate is fixed. This is the degeneracy analog of the face-insertion step lemmas, and is what
lets the Eilenberg–Zilber map carry a one-direction degeneracy to a diagonal one. -/
lemma exists_snd_step {p q : ℕ} (μ : Shuffle p q) (i : ℕ) (hi : i + 1 ≤ q) :
    ∃ a : Fin (p + q), (μ.1 a.castSucc).2.val = i ∧ (μ.1 a.succ).2.val = i + 1 ∧
      (μ.1 a.castSucc).1 = (μ.1 a.succ).1 := by
  classical
  let S : Finset (Fin (p + q + 1)) := Finset.univ.filter (fun r => i + 1 ≤ (μ.1 r).2.val)
  have hlast : Fin.last (p + q) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    have hsum := coordSum_eq μ (Fin.last (p + q))
    have h1 := (μ.1 (Fin.last (p + q))).1.isLt
    have h2 := (μ.1 (Fin.last (p + q))).2.isLt
    simp only [Fin.val_last] at hsum
    omega
  have hSne : S.Nonempty := ⟨_, hlast⟩
  set a0 := S.min' hSne with ha0_def
  have ha0 : i + 1 ≤ (μ.1 a0).2.val := by
    grind [Finset.min'_mem]
  have ha0pos : 0 < a0.val := by
    refine Or.resolve_left (Nat.eq_zero_or_pos a0.val) ?_
    grind [(coordSum_eq μ a0)]
  set a : Fin (p + q) := ⟨a0.val - 1, by have := a0.isLt; omega⟩ with ha_def
  have ha_val : a.val = a0.val - 1 := rfl
  have hsucc : a.succ = a0 := Fin.ext (by rw [Fin.val_succ, ha_val]; omega)
  have hcast_lt : a.castSucc < a0 := by
    rw [Fin.lt_def, Fin.val_castSucc, ha_val]; omega
  have hcast_notin : a.castSucc ∉ S := fun h => absurd (S.min'_le _ h) (not_le.mpr hcast_lt)
  have hcast_le : (μ.1 a.castSucc).2.val ≤ i := by
    by_contra h
    exact hcast_notin
      (by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
  have hsucc_ge : i + 1 ≤ (μ.1 a.succ).2.val := by rw [hsucc]; grind [Finset.min'_mem]
  rcases shuffle_step μ a with ⟨hf, hs⟩ | ⟨hf, hs⟩
  · exact absurd hs (by omega)
  · exact ⟨a, by omega, by omega, Fin.ext hf⟩

/-- The first-coordinate analog of `exists_snd_step`: for `i + 1 ≤ p` there is a **`p`-step at
level `i`** — the first coordinate goes `i → i + 1` while the second coordinate is fixed. Used for
the outer (horizontal) Eilenberg–Zilber degeneracy kill. -/
lemma exists_fst_step {p q : ℕ} (μ : Shuffle p q) (i : ℕ) (hi : i + 1 ≤ p) :
    ∃ a : Fin (p + q), (μ.1 a.castSucc).1.val = i ∧ (μ.1 a.succ).1.val = i + 1 ∧
      (μ.1 a.castSucc).2 = (μ.1 a.succ).2 := by
  classical
  let S : Finset (Fin (p + q + 1)) := Finset.univ.filter (fun r => i + 1 ≤ (μ.1 r).1.val)
  have hlast : Fin.last (p + q) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    have hsum := coordSum_eq μ (Fin.last (p + q))
    have h1 := (μ.1 (Fin.last (p + q))).1.isLt
    have h2 := (μ.1 (Fin.last (p + q))).2.isLt
    simp only [Fin.val_last] at hsum
    omega
  have hSne : S.Nonempty := ⟨_, hlast⟩
  set a0 := S.min' hSne with ha0_def
  have ha0S : a0 ∈ S := S.min'_mem hSne
  have ha0 : i + 1 ≤ (μ.1 a0).1.val := by
    have h := ha0S; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h
  have ha0pos : 0 < a0.val := by
    rcases Nat.eq_zero_or_pos a0.val with h | h
    · exfalso
      have hsum := coordSum_eq μ a0
      rw [h] at hsum
      omega
    · exact h
  set a : Fin (p + q) := ⟨a0.val - 1, by have := a0.isLt; omega⟩ with ha_def
  have ha_val : a.val = a0.val - 1 := rfl
  have hsucc : a.succ = a0 := Fin.ext (by rw [Fin.val_succ, ha_val]; omega)
  have hcast_lt : a.castSucc < a0 := by
    rw [Fin.lt_def, Fin.val_castSucc, ha_val]; omega
  have hcast_notin : a.castSucc ∉ S := fun h => absurd (S.min'_le _ h) (not_le.mpr hcast_lt)
  have hcast_le : (μ.1 a.castSucc).1.val ≤ i := by
    by_contra h
    exact hcast_notin
      (by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
  have hsucc_ge : i + 1 ≤ (μ.1 a.succ).1.val := by rw [hsucc]; exact ha0
  rcases shuffle_step μ a with ⟨hf, hs⟩ | ⟨hf, hs⟩
  · exact ⟨a, by omega, by omega, Fin.ext hs⟩
  · exact absurd hf (by omega)

/-- The swap of a shuffle at position x gives the swapped coordinates of u at the same position. -/
private lemma swap_apply_fst {p q : ℕ} (u : Shuffle p q) (x : Fin (q + p + 1)) :
    ((u.swap).1 x).1.val = (u.1 (x.cast (by omega))).2.val := by
  simp [swap, Fin.castOrderIso, Prod.swap]

private lemma swap_apply_snd {p q : ℕ} (u : Shuffle p q) (x : Fin (q + p + 1)) :
    ((u.swap).1 x).2.val = (u.1 (x.cast (by omega))).1.val := by
  simp [swap, Fin.castOrderIso, Prod.swap]

/-- Reindex swap's invCount to a sum over `Fin (p + q)` in terms of u's coordinates. -/
private lemma invCount_swap_eq {p q : ℕ} (u : Shuffle p q) :
    (u.swap).invCount = ∑ s : Fin (p + q),
      if (u.1 (Fin.castSucc s)).2 < (u.1 (Fin.succ s)).2
      then (u.1 (Fin.castSucc s)).1.val
      else 0 := by
  simp only [invCount]
  -- Establish Fin-level equalities for swap's coordinates
  have hswap1 : ∀ x : Fin (q + p + 1),
      ((u.swap).1 x).1 = (u.1 (x.cast (by omega))).2 :=
    fun x => Fin.ext (swap_apply_fst u x)
  have hswap2 : ∀ x : Fin (q + p + 1),
      ((u.swap).1 x).2 = (u.1 (x.cast (by omega))).1 :=
    fun x => Fin.ext (swap_apply_snd u x)
  simp_rw [hswap1, hswap2]
  -- Reindex from Fin(q+p) to Fin(p+q) via finCongr
  refine Fintype.sum_equiv (finCongr (by omega)) _ _ fun s => ?_
  have hcs : Fin.cast (show q + p + 1 = p + q + 1 from by omega) s.castSucc =
             (finCongr (show q + p = p + q from by omega) s).castSucc :=
    Fin.ext (by simp [finCongr])
  have hss : Fin.cast (show q + p + 1 = p + q + 1 from by omega) s.succ =
             (finCongr (show q + p = p + q from by omega) s).succ :=
    Fin.ext (by simp [finCongr])
  simp_rw [hcs, hss]

/- Total inversions of a shuffle and its swap equal `p * q`. -/
section

/-
A shuffle path starts at (0,0).
-/
lemma apply_zero {p q : ℕ} (u : Shuffle p q) : u.1 0 = (0, 0) := by
  -- Since u is injective and monotone, it must map the least element 0 to itself.
  have h_least : ∀ x : Fin (p + q + 1), (u.1 x).1.val + (u.1 x).2.val = x.val := by
    -- Apply the lemma that states the coordinate sum equals the position for any shuffle.
    apply coordSum_eq;
  specialize h_least 0; aesop;

/-
A shuffle path ends at (p,q).
-/
lemma apply_last {p q : ℕ} (u : Shuffle p q) : u.1 (Fin.last (p + q)) = (Fin.last p,
    Fin.last q) := by
  have := @coordSum_eq p q u ( Fin.last ( p + q ) );
  exact Prod.ext ( Fin.ext ( by linarith! [ Fin.is_lt ( u.1 ( Fin.last ( p + q ) ) |>.1 ),
                                 Fin.is_lt ( u.1 ( Fin.last ( p + q ) ) |>.2 ) ] ) ) ( Fin.ext (
                                 by linarith! [ Fin.is_lt ( u.1 ( Fin.last ( p + q ) ) |>.1 ),
                                     Fin.is_lt ( u.1 ( Fin.last ( p + q ) ) |>.2 ) ] ) )

/-
Express invCount as a sum of y * dx.
-/
lemma invCount_eq_sum_mul_diff {p q : ℕ} (u : Shuffle p q) :
    u.invCount = ∑ r : Fin (p + q), (u.1 r.castSucc).2.val * ((u.1 r.succ).1.val - (u.1
        r.castSucc).1.val) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have := shuffle_step u i;
      grind

/-
Express swap.invCount as a sum of x * dy.
-/
lemma swap_invCount_eq_sum_mul_diff {p q : ℕ} (u : Shuffle p q) :
    (u.swap).invCount = ∑ r : Fin (p + q), (u.1 r.castSucc).1.val * ((u.1 r.succ).2.val - (u.1
        r.castSucc).2.val) := by
      rw [ invCount_swap_eq, Finset.sum_congr rfl ];
      intro x hx; split_ifs <;> simp_all +decide [] ;
      have := shuffle_step u x;
      grind

/-
The change in the product of coordinates equals y*dx + x*dy.
-/
lemma xy_diff_eq_sum_mixed {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) :
    (u.1 r.succ).1.val * (u.1 r.succ).2.val - (u.1 r.castSucc).1.val * (u.1 r.castSucc).2.val =
    (u.1 r.castSucc).2.val * ((u.1 r.succ).1.val - (u.1 r.castSucc).1.val) +
    (u.1 r.castSucc).1.val * ((u.1 r.succ).2.val - (u.1 r.castSucc).2.val) := by
      rw [ Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib ];
      cases shuffle_step u r <;> simp_all +decide [ mul_comm ]

end

lemma invCount_add_invCount_swap {p q : ℕ} (u : Shuffle p q) :
    u.invCount + (u.swap).invCount = p * q := by
  -- The sum of the differences in the product of coordinates is a telescoping sum, so most terms
  -- cancel out.
  have h_telescope : ∑ r : Fin (p + q), ((u.1 (Fin.succ r)).1.val * (u.1 (Fin.succ r)).2.val - (u.1
      (Fin.castSucc r)).1.val * (u.1 (Fin.castSucc r)).2.val) = (u.1 (Fin.last (p +
      q))).1.val * (u.1 (Fin.last (p + q))).2.val - (u.1 0).1.val * (u.1 0).2.val := by
    have h_telescope_int : ∀ (n : ℕ) (f : Fin (n + 1) → ℤ),
        ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
      intro n f
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.succ_castSucc]
        rw [ih (fun i => f i.castSucc)]
        simp
    have h_telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℕ),
        (∀ i : Fin n, f i.castSucc ≤ f i.succ) →
        ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
      intro n f hf
      have hmono : Monotone f := Fin.monotone_iff_le_succ.mpr hf
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub (hmono (Fin.zero_le _)), Nat.cast_sum]
      simp_rw [Nat.cast_sub (hf _)]
      exact h_telescope_int n (fun i => (f i : ℤ))
    convert h_telescope ( p + q ) ( fun i => ( u.1 i ).1.val * ( u.1 i ).2.val ) _ using 1;
    exact fun i => mul_le_mul' ( u.1.monotone ( Nat.le_succ _ ) |>.1 ) ( u.1.monotone ( Nat.le_succ
        _ ) |>.2 );
  convert h_telescope using 1;
  · rw [ Shuffle.invCount_eq_sum_mul_diff, Shuffle.swap_invCount_eq_sum_mul_diff,
        ← Finset.sum_add_distrib ];
    exact Finset.sum_congr rfl fun _ _ => by rw [ Shuffle.xy_diff_eq_sum_mixed ] ;
  · rw [ eq_tsub_iff_add_eq_of_le ] <;> norm_num [ Shuffle.apply_zero, Shuffle.apply_last ]

/-- Swapping a `(p,q)`-shuffle changes the sign by the Koszul factor `(-1)^(p*q)`. -/
theorem sign_eq_negOnePow_mul_swap_sign {p q : ℕ} (u : Shuffle p q) :
    u.sign = (-1 : ℤ) ^ (p * q) * (u.swap).sign := by
  have h := invCount_add_invCount_swap u
  simp only [sign]
  conv_rhs => rw [show (p * q : ℕ) = u.invCount + (u.swap).invCount from h.symm]
  rw [pow_add, mul_assoc]
  suffices (-1 : ℤ) ^ (u.swap).invCount * (-1 : ℤ) ^ (u.swap).invCount = 1 by
    rw [this, mul_one]
  rw [← mul_pow]
  norm_num

/-! #### Shuffle (0,0) -/

/-- For `Shuffle 0 0`, the domain and codomain are both `Fin 1`, so every shuffle
has the same underlying map: the unique monotone injection to `(0, 0)`. -/
lemma unique_0_0 (μ : Shuffle 0 0) :
    μ.1 = ⟨fun _ => (0, 0), fun _ _ _ => le_refl _⟩ := by
  ext x
  · simp [Fin.eq_zero (μ.1 x).1]
  · simp [Fin.eq_zero (μ.1 x).2]

/-- There is exactly one `(0,0)`-shuffle. -/
instance subsingleton_0_0 : Subsingleton (Shuffle 0 0) :=
  ⟨fun μ ν => Subtype.ext (by rw [unique_0_0 μ, unique_0_0 ν])⟩

/-- The **staircase** `(r,m)`-shuffle `k ↦ (min(k,r), k - r)`: it goes right `r` steps then up
`m` steps (the lexicographically smallest shuffle path). Its front-`r` face and back-`m` face
recover the identity, so it is the unique shuffle contributing the identity summand to the
diagonal Eilenberg–Zilber/Alexander–Whitney pairing. -/
def trivialShuffle (r m : ℕ) : Shuffle r m :=
  ⟨OrderHom.prod
      ⟨fun k => ⟨min k.val r, by omega⟩, fun a b h => by
        simp only [Fin.mk_le_mk]; have : a.val ≤ b.val := h; omega⟩
      ⟨fun k => ⟨k.val - r, by have := k.isLt; omega⟩, fun a b h => by
        simp only [Fin.mk_le_mk]; have : a.val ≤ b.val := h; omega⟩,
    fun a b hab => by
      have h1 : min a.val r = min b.val r := congrArg (fun p => (p.1 : ℕ)) hab
      have h2 : a.val - r = b.val - r := congrArg (fun p => (p.2 : ℕ)) hab
      apply Fin.ext
      have ha := a.isLt; have hb := b.isLt
      omega⟩

/-- The coordinates of the staircase shuffle: `fst = min(·, r)`, `snd = · - r`. -/
@[simp] lemma trivialShuffle_apply (r m : ℕ) (k : Index (r + m)) :
    (trivialShuffle r m).1 k = (⟨min k.val r, by omega⟩, ⟨k.val - r, by have := k.isLt; omega⟩) :=
  rfl

/-- The staircase shuffle has no inversions, hence sign `1`. -/
lemma sign_trivialShuffle (r m : ℕ) : (trivialShuffle r m).sign = 1 := by
  have hinv : (trivialShuffle r m).invCount = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [trivialShuffle_apply, Fin.val_succ, Fin.val_castSucc, Fin.mk_lt_mk]
    split_ifs with h
    · -- `fst` strictly increases at step `i` ⟹ `i < r` ⟹ `snd = i - r = 0`.
      omega
    · rfl
  rw [sign, hinv, pow_zero]

/-! #### Face-shuffle decomposition (Leibniz rule infrastructure)

**Why "remove step" doesn't work.**  An earlier attempt defined `removeLeftStep μ r`
by removing vertex `r` from the shuffle path whenever step `r` is a left step.
This is wrong: the face map `δ_r` removes **vertex** `r`, which merges the steps
on either side of `r`. If those steps have different types (one left, one right),
the merged step is a **diagonal** (both coordinates increase), which cannot be a
valid shuffle step.

Example: the `(1,1)`-shuffle `(0,0) → (1,0) → (1,1)` has step 0 = Left,
step 1 = Right.  Removing vertex 1 = `(1,0)` gives `(0,0) → (1,1)`, a diagonal.
This doesn't factor as `ν ≫ (δⱼ × id)` for any shuffle `ν`.  The factorization
only works for "LL" vertices (both adjacent steps are left) or "RR" vertices.

**The insert approach.**  Instead of decomposing the LHS face terms, we work from
the RHS and **inject** into the LHS.  Given a `(p, q+1)`-shuffle `ν` and a face
index `j : Fin (p+2)`, we construct a `(p+1, q+1)`-shuffle `insertLeftStep ν j`
by lifting ν's first coordinate via `Fin.succAbove j` (skipping value `j`) and
inserting a new left step where the first coordinate crosses `j`.

The proof of `universalSimplexCrossProduct_boundary` then proceeds:
1. Show the RHS terms inject into the LHS via `insertLeftStep` / `insertRightStep`.
2. Show the remaining LHS terms (diagonal terms) cancel via a sign-reversing
   involution `swapDiagonalSteps`.
-/

/-- Whether step `r` of shuffle `μ` is a "left step" (first coordinate increments). -/
def isLeftStep {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q)) : Prop :=
  (μ.1 r.castSucc).1.val < (μ.1 r.succ).1.val

instance decidableIsLeftStep {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q)) :
    Decidable (isLeftStep μ r) :=
  inferInstanceAs (Decidable (_ < _))

/-! ##### Insertion indices -/

/-- The vertex index in the `(p+1, q)`-shuffle's domain where the new left step
was inserted. Removing this vertex via `δ` recovers the original shuffle.
Equals the number of vertices of `ν` whose first coordinate is `< j`. -/
def insertLeftIndex {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    Fin (p + q + 2) :=
  ⟨(Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).1.val < j.val).card, by
    exact Nat.lt_of_le_of_lt (Finset.card_filter_le _ _) (by simp)⟩

/-- The vertex index where the new right step was inserted.
Equals the number of vertices of `ν` whose second coordinate is `< k`. -/
def insertRightIndex {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    Fin (p + q + 2) :=
  ⟨(Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).2.val < k.val).card, by
    exact Nat.lt_of_le_of_lt (Finset.card_filter_le _ _) (by simp)⟩

/-! ##### Insertion helpers -/

/-- The insertion index satisfies `t ≤ j + q`: vertices with fst < j have
index ≤ (j-1) + q by `coordSum_eq`, so there are at most j + q of them. -/
lemma insertLeftIndex_le {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    (insertLeftIndex ν j).val ≤ j.val + q := by
  simp only [insertLeftIndex]
  -- Inject the filter into Finset.range (j+q) via Fin.val
  calc (Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).1.val < j.val).card
      = ((Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).1.val < j.val).image
          Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range (j.val + q)).card := by
          apply Finset.card_le_card; intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_range] at hx ⊢
          obtain ⟨r, hr, rfl⟩ := hx
          have := coordSum_eq ν r; have := (ν.1 r).2.isLt; omega
    _ = j.val + q := Finset.card_range _

/-- Symmetric bound: the right insertion index satisfies `t ≤ p + k`. -/
private lemma insertRightIndex_le {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightIndex ν k).val ≤ p + k.val := by
  simp only [insertRightIndex]
  calc (Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).2.val < k.val).card
      = ((Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).2.val < k.val).image
          Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range (p + k.val)).card := by
          apply Finset.card_le_card; intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_range] at hx ⊢
          obtain ⟨r, hr, rfl⟩ := hx
          have := coordSum_eq ν r; have := (ν.1 r).1.isLt; omega
    _ = p + k.val := Finset.card_range _

/-- Lower bound: the left insertion index satisfies `j ≤ t`.
Proof: any r with r.val < j has fst(r) ≤ r < j, so the filter includes all r < j. -/
private lemma insertLeftIndex_ge {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    j.val ≤ (insertLeftIndex ν j).val := by
  -- The set of indices where the first coordinate is less than $j$ contains at least the indices
  -- $0, 1, ..., j-1$.
  have h_filter : Finset.filter (fun r : Fin (p + q + 1) => (ν.1 r).1.val <
      j.val) Finset.univ ⊇ Finset.univ.filter (fun r : Fin (p + q + 1) => r.val < j.val) := by
    intro r hr;
    have := coordSum_eq ν r;
    grind;
  refine le_trans ?_ (Finset.card_mono h_filter)
  rw [Finset.card_eq_of_bijective]
  · exact fun i hi => ⟨i, by linarith [Fin.is_lt j]⟩
  · aesop;
  · aesop;
  · aesop

/-- Symmetric lower bound: the right insertion index satisfies `k ≤ t`. -/
private lemma insertRightIndex_ge {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    k.val ≤ (insertRightIndex ν k).val := by
  -- Since `ν` is a monotone function, for any `r` with `r.val < k`, we have `ν.1 r ≤ r`. Therefore,
  -- the filter includes all `r < k`, so the cardinality is at least `k`.
  have h_filter : ∀ r : Fin (p + q + 1), r.val < k.val → (ν.1 r).2.val < k.val := by
    -- By the properties of ν, we know that the second coordinate of ν(r) is less than or equal to
    -- r.val.
    have h_second_coord_le_r : ∀ r : Fin (p + q + 1), (ν.1 r).2.val ≤ r.val := by
      exact fun r => by linarith [ coordSum_eq ν r ] ;
    exact fun r hr => lt_of_le_of_lt ( h_second_coord_le_r r ) hr;
  have h_filter_card : (Finset.univ.filter fun r : Fin (p + q + 1) => r.val <
      k.val).card ≤ (Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).2.val < k.val).card := by
    exact Finset.card_le_card fun x hx => by aesop;
  refine le_trans ?_ h_filter_card;
  rw [Finset.card_eq_of_bijective]
  · exact fun i hi => ⟨i, by linarith [Fin.is_lt k]⟩
  · aesop;
  · aesop;
  · aesop

/-- The filter `{r | fst(r) < j}` is a downward-closed initial segment:
`fst(ν r) < j ↔ r.val < t` where `t = insertLeftIndex`. -/
private lemma insertLeftIndex_iff {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (r : Fin (p + q + 1)) :
    (ν.1 r).1.val < j.val ↔ r.val < (insertLeftIndex ν j).val := by
  constructor <;> intro h;
  · -- Since ν is monotone, the set {x | x.val < t} is exactly the set of elements in the filter.
    -- Therefore, if r is in the filter, then r < t.
    have h_filter : {x : Fin (p + q + 1) | (ν.1 x).1.val < j.val} ⊇ Finset.Iio r := by
      intro x hx;
      exact lt_of_le_of_lt ( Nat.cast_le.mpr <| ν.1.monotone ( le_of_lt <| by aesop ) |> fun h =>
          h.1 ) h;
    have h_filter_card : Finset.card (Finset.filter (fun x => (ν.1 x).1.val < j.val)
        Finset.univ) ≥ Finset.card (Finset.Iio r) + 1 := by
      refine Finset.card_lt_card ?_
      simp_all +decide only [Finset.coe_Iio, ge_iff_le, Finset.ssubset_def, Finset.subset_iff,
          Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_lt];
      exact ⟨ fun x hx => h_filter hx, r, h, le_rfl ⟩;
    aesop;
  · contrapose! h;
    exact le_trans ( Finset.card_le_card <| show Finset.filter ( fun x : Fin ( p + q + 1 ) => ( ν.1
        x |>.1 : ℕ ) < j ) Finset.univ ⊆ Finset.Iio r from fun x hx => Finset.mem_Iio.mpr <|
        lt_of_not_ge fun hx' => by linarith [ Finset.mem_filter.mp hx,
                                    show ( ν.1 x |>.1 : ℕ ) ≥ ( ν.1 r |>.1 : ℕ )
                                    by exact ν.1.monotone hx' |>.1 ] ) <| by simp +decide [] ;

/-- Symmetric: `snd(ν r) < k ↔ r.val < insertRightIndex`. -/
private lemma insertRightIndex_iff {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2))
    (r : Fin (p + q + 1)) :
    (ν.1 r).2.val < k.val ↔ r.val < (insertRightIndex ν k).val := by
  constructor <;> intro h
  · have h_filter :
        {x : Fin (p + q + 1) | (ν.1 x).2.val < k.val} ⊇ Finset.Iio r := by
      intro x hx
      exact lt_of_le_of_lt
        (Nat.cast_le.mpr ((ν.1.monotone (le_of_lt (by aesop))).2)) h
    have h_filter_card :
        Finset.card (Finset.filter (fun x => (ν.1 x).2.val < k.val) Finset.univ) ≥
          Finset.card (Finset.Iio r) + 1 := by
      refine Finset.card_lt_card ?_
      simp_all +decide only [Finset.coe_Iio, ge_iff_le, Finset.ssubset_def, Finset.subset_iff,
          Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_lt]
      exact ⟨fun x hx => h_filter hx, r, h, le_rfl⟩
    aesop
  · contrapose! h
    exact le_trans
      (Finset.card_le_card (show
        Finset.filter (fun x : Fin (p + q + 1) => (ν.1 x).2.val < k.val) Finset.univ ⊆
          Finset.Iio r from fun x hx => Finset.mem_Iio.mpr (lt_of_not_ge fun hx' => by
            have hmono : (ν.1 r).2.val ≤ (ν.1 x).2.val := (ν.1.monotone hx').2
            linarith [Finset.mem_filter.mp hx])))
      (by simp +decide [])

/-! ##### Insertion maps (RHS → LHS direction) -/

/-- The underlying piecewise map for `insertLeftStep`: before the insertion point,
embed the original vertex via `succAbove j`; at the insertion point, place `(j, t-j)`;
after the insertion point, embed the shifted-back vertex via `succAbove j`. -/
noncomputable def insertLeftStepFun {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    Fin ((p + 1) + q + 1) → Index (p + 1) × Index q :=
  let t := (insertLeftIndex ν j).val
  have ht_lt : t < p + q + 2 := (insertLeftIndex ν j).isLt
  have ht_le : t ≤ j.val + q := insertLeftIndex_le ν j
  fun r =>
    -- Before insertion: embed original vertex via succAbove j (preserves value since fst < j)
    if h : r.val < t then
      (j.succAbove (ν.1 ⟨r, by omega⟩).1, (ν.1 ⟨r, by omega⟩).2)
    -- At insertion point: new left step with fst = j, snd = t - j
    else if h2 : r.val = t then
      (j, ⟨r.val - j.val, by omega⟩)
    -- After insertion: embed shifted-back vertex via succAbove j (adds 1 since fst ≥ j)
    else
      (j.succAbove (ν.1 ⟨r - 1, by omega⟩).1, (ν.1 ⟨r - 1, by omega⟩).2)

/-- Coordinate sum of the piecewise map equals the position index. -/
private lemma insertLeftStepFun_coordSum {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (r : Fin ((p + 1) + q + 1)) :
    (insertLeftStepFun ν j r).1.val + (insertLeftStepFun ν j r).2.val = r.val := by
  simp only [insertLeftStepFun]
  split_ifs with h1 h2
  · -- r < t: succAbove preserves value since fst < j, then use coordSum_eq
    have hfst := (insertLeftIndex_iff ν j ⟨r.val, by omega⟩).mpr h1
    simp only [Fin.succAbove]
    split
    · simp only [Fin.val_castSucc]
      have := coordSum_eq ν ⟨r.val, by omega⟩
      simp at this; omega
    · rename_i hn
      exfalso
      simp only [not_lt, Fin.le_def, Fin.val_castSucc] at hn
      omega
  · -- r = t: j + (t - j) = t = r
    have hge := insertLeftIndex_ge ν j
    simp; omega
  · -- r > t: succAbove adds 1 since fst ≥ j, then use coordSum_eq
    have hfst : ¬ (ν.1 ⟨r.val - 1, by omega⟩).1.val < j.val := by
      rw [insertLeftIndex_iff]; simp; omega
    simp only [Fin.succAbove]
    split
    · rename_i hlt; exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at hlt; omega
    · simp only [Fin.val_succ]
      have := coordSum_eq ν ⟨r.val - 1, by omega⟩
      simp at this; omega

/-- Insert a left step at face index `j`, turning a `(p, q)`-shuffle into a
`(p+1, q)`-shuffle.  The original path from `(0,0)` to `(p, q)` is embedded
into a path from `(0,0)` to `(p+1, q)` by applying `Fin.succAbove j` to the
first coordinate and inserting a new left step where the first coordinate
crosses `j`. -/
noncomputable def insertLeftStep {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    Shuffle (p + 1) q :=
  ⟨⟨insertLeftStepFun ν j, by
    -- Monotonicity: use coordSum to derive both coordinates weakly increasing
    intro a b hab
    simp only [Prod.le_def]
    constructor
    · -- First coordinate monotone
      suffices hsuc : ∀ r : Fin (p + 1 + q),
          (insertLeftStepFun ν j r.castSucc).1 ≤ (insertLeftStepFun ν j r.succ).1 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertLeftStepFun ν j r).1) ).2 hsuc hab
      intro r
      simp only [insertLeftStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (Fin.succAbove_le_succAbove_iff.mpr (ν.1.monotone (Fin.castSucc_le_succ
            r)).1) -- cs < t, succ < t
      · -- cs < t, succ = t: succAbove(fst) ≤ j since fst < j
        have hfst := (insertLeftIndex_iff ν j ⟨r.val, by omega⟩).mpr h1
        simp only [Fin.succAbove]
        split
        · simp [Fin.le_def]; omega
        · rename_i hn; exfalso; simp only [not_lt, Fin.le_def, Fin.val_castSucc] at hn; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs < t, succ > t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs = t, succ < t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs = t, succ = t (impossible)
      · -- cs = t, succ > t: j ≤ succAbove(fst) since fst ≥ j
        have hfst : ¬ (ν.1 ⟨r.val, by omega⟩).1.val < j.val := by
          rw [insertLeftIndex_iff]; simp at h4; simp; omega
        push Not at hfst
        have heq : (⟨r.succ.val - 1, by omega⟩ : Fin (p + q + 1)) = ⟨r.val, by omega⟩ := by
          ext; simp [Fin.val_succ]
        rw [heq]
        simp only [Fin.succAbove]
        split
        · rename_i hlt; exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at hlt; omega
        · simp [Fin.le_def, Fin.val_succ]; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs > t, succ < t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs > t, succ = t (impossible)
      · exact (Fin.succAbove_le_succAbove_iff.mpr -- cs > t, succ > t
          (ν.1.monotone (by simp [Fin.le_def, Fin.val_succ])).1)
    · -- Second coordinate monotone
      suffices hsuc : ∀ r : Fin (p + 1 + q),
          (insertLeftStepFun ν j r.castSucc).2 ≤ (insertLeftStepFun ν j r.succ).2 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertLeftStepFun ν j r).2)).2 hsuc hab
      intro r
      simp only [insertLeftStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (ν.1.monotone (Fin.castSucc_le_succ r)).2 -- castSucc < t, succ < t
      · -- castSucc < t, succ = t: snd(ν r) ≤ r+1-j
        -- Reduce to j ≤ ν(r).1 + 1 using coordSum_eq
        simp only [Fin.val_castSucc, Fin.val_succ]
        have hge := insertLeftIndex_ge ν j
        have hsv := Fin.val_succ r
        have hsum := coordSum_eq ν ⟨r.val, by omega⟩
        suffices h : j.val ≤ (ν.1 ⟨r.val, by omega⟩).1.val + 1 by
          simp only [Fin.le_def] at hsum ⊢; omega
        by_cases hr : r.val + 1 = p + 1 + q
        · -- r is the last vertex: ν(r) = (p, q), so fst = p and j ≤ p + 1
          have hlast : ν.1 ⟨r.val, by omega⟩ = (Fin.last p, Fin.last q) := by
            have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
              Fin.ext (by simp [Fin.last]; omega)
            rw [this]; exact Shuffle.apply_last ν
          have hfst : (ν.1 ⟨r.val, by omega⟩).1.val = p := by
            rw [hlast]; simp [Fin.last]
          rw [hfst]; omega
        · -- r is not the last vertex: ν(r+1).1 ≥ j (by insertLeftIndex_iff)
          -- and ν(r+1).1 ≤ ν(r).1 + 1 (by shuffle step), so j ≤ ν(r).1 + 1
          let r' : Fin (p + q + 1) := ⟨r.val + 1, by omega⟩
          have hge_j : j.val ≤ (ν.1 r').1.val := by
            by_contra hlt
            push Not at hlt
            have h_iff := (insertLeftIndex_iff ν j r').mp hlt
            have ht : (insertLeftIndex ν j).val = r.val + 1 := by
              simp [Fin.val_succ] at hsv; omega
            change r.val + 1 < _ at h_iff
            omega
          have hstep := shuffle_step ν ⟨r.val, by omega⟩
          have hcs : (⟨r.val, by omega⟩ : Fin (p + q)).castSucc = (⟨r.val,
              by omega⟩ : Fin (p + q + 1)) :=
            Fin.ext (by simp [Fin.castSucc])
          have hsu : (⟨r.val, by omega⟩ : Fin (p + q)).succ = r' :=
            Fin.ext (by simp [Fin.succ, r'])
          rw [hcs, hsu] at hstep
          rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs < t, succ > t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs = t, succ < t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs = t, succ = t (impossible)
      ·  -- castSucc = t, succ > t
        simp only [Fin.val_castSucc, Fin.val_succ, add_tsub_cancel_right]
        simp only [Fin.le_def]
        have hcs := coordSum_eq ν ⟨r.val, by omega⟩
        suffices h : (ν.1 ⟨r.val, by omega⟩).1.val ≤ j.val by
          have : (⟨r.val, by omega⟩ : Fin (p + q + 1)).val = r.val := rfl
          omega
        by_cases hr : r.val = 0
        · have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = 0 := Fin.ext (by simp [hr])
          rw [this, Shuffle.apply_zero]; simp
        · let r' : Fin (p + q + 1) := ⟨r.val - 1, by omega⟩
          have hr'lt : r'.val < (insertLeftIndex ν j).val := by
            simp [r'] at h4 ⊢; omega
          have hfst_lt : (ν.1 r').1.val < j.val :=
            (insertLeftIndex_iff ν j r').mpr hr'lt
          have hstep := shuffle_step ν ⟨r.val - 1, by omega⟩
          have hcs2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).castSucc = r' :=
            Fin.ext (by simp [Fin.castSucc, r'])
          have hsu2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).succ = ⟨r.val, by omega⟩ :=
            Fin.ext (by simp [Fin.succ]; omega)
          rw [hcs2, hsu2] at hstep
          rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs > t, succ < t (impossible)
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega -- cs > t, succ = t (impossible)
      · exact (ν.1.monotone (by simp [Fin.le_def, Fin.val_succ])).2 -- cs > t, succ > t
      ⟩, by
    -- Injectivity: f(a) = f(b) → coordSum(f(a)) = coordSum(f(b)) → a = b
    intro a b hab
    have ha := insertLeftStepFun_coordSum ν j a
    have hb := insertLeftStepFun_coordSum ν j b
    have heq : insertLeftStepFun ν j a = insertLeftStepFun ν j b := hab
    have : (insertLeftStepFun ν j a).1.val + (insertLeftStepFun ν j a).2.val =
        (insertLeftStepFun ν j b).1.val + (insertLeftStepFun ν j b).2.val := by rw [heq]
    exact Fin.ext (by omega)⟩

/-- The underlying piecewise map for `insertRightStep`: before the insertion point,
embed the original vertex via `succAbove k` on the second coordinate; at the
insertion point, place `(t-k, k)`; after the insertion point, embed the
shifted-back vertex via `succAbove k`. -/
noncomputable def insertRightStepFun {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    Fin (p + (q + 1) + 1) → Index p × Index (q + 1) :=
  let t := (insertRightIndex ν k).val
  fun r =>
    if h : r.val < t then
      ((ν.1 ⟨r, by omega⟩).1, k.succAbove (ν.1 ⟨r, by omega⟩).2)
    else if h2 : r.val = t then
      (⟨r.val - k.val, by
        have := insertRightIndex_le ν k; omega⟩, k)
    else
      ((ν.1 ⟨r - 1, by omega⟩).1, k.succAbove (ν.1 ⟨r - 1, by omega⟩).2)

/-- Coordinate sum of the right-insertion piecewise map equals the position index. -/
private lemma insertRightStepFun_coordSum {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2))
    (r : Fin (p + (q + 1) + 1)) :
    (insertRightStepFun ν k r).1.val + (insertRightStepFun ν k r).2.val = r.val := by
  simp only [insertRightStepFun]
  split_ifs with h1 h2
  · have hsnd := (insertRightIndex_iff ν k ⟨r.val, by omega⟩).mpr h1
    simp only [Fin.succAbove]
    split
    · simp only [Fin.val_castSucc]
      have := coordSum_eq ν ⟨r.val, by omega⟩
      simp at this; omega
    · rename_i hn
      exfalso
      simp only [not_lt, Fin.le_def, Fin.val_castSucc] at hn
      omega
  · have hge := insertRightIndex_ge ν k
    simp; omega
  · have hsnd : ¬ (ν.1 ⟨r.val - 1, by omega⟩).2.val < k.val := by
      rw [insertRightIndex_iff]; simp; omega
    simp only [Fin.succAbove]
    split
    · rename_i hlt; exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at hlt; omega
    · simp only [Fin.val_succ]
      have := coordSum_eq ν ⟨r.val - 1, by omega⟩
      simp at this; omega

/-- Insert a right step at face index `k`, turning a `(p, q)`-shuffle into a
`(p, q+1)`-shuffle.  Applies `Fin.succAbove k` to the second coordinate and
inserts a new right step where the second coordinate crosses `k`. -/
noncomputable def insertRightStep {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    Shuffle p (q + 1) :=
  ⟨⟨insertRightStepFun ν k, by
    intro a b hab
    simp only [Prod.le_def]
    constructor
    · -- First coordinate monotone
      suffices hsuc : ∀ r : Fin (p + (q + 1)),
          (insertRightStepFun ν k r.castSucc).1 ≤ (insertRightStepFun ν k r.succ).1 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertRightStepFun ν k r).1)).2 hsuc hab
      intro r
      simp only [insertRightStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (ν.1.monotone (Fin.castSucc_le_succ r)).1 -- cs < t, succ < t
      · -- cs < t, succ = t: fst(ν r) ≤ r+1-k
        simp only [Fin.val_castSucc, Fin.val_succ]
        have hge := insertRightIndex_ge ν k
        have hsv := Fin.val_succ r
        have hsum := coordSum_eq ν ⟨r.val, by omega⟩
        suffices h : k.val ≤ (ν.1 ⟨r.val, by omega⟩).2.val + 1 by
          simp only [Fin.le_def] at hsum ⊢; omega
        by_cases hr : r.val + 1 = p + q + 1
        · have hlast : ν.1 ⟨r.val, by omega⟩ = (Fin.last p, Fin.last q) := by
            have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
              Fin.ext (by simp [Fin.last]; omega)
            rw [this]; exact Shuffle.apply_last ν
          have hsnd : (ν.1 ⟨r.val, by omega⟩).2.val = q := by
            rw [hlast]; simp [Fin.last]
          rw [hsnd]; omega
        · let r' : Fin (p + q + 1) := ⟨r.val + 1, by omega⟩
          have hge_k : k.val ≤ (ν.1 r').2.val := by
            by_contra hlt
            push Not at hlt
            have h_iff := (insertRightIndex_iff ν k r').mp hlt
            have ht : (insertRightIndex ν k).val = r.val + 1 := by
              simp [Fin.val_succ] at hsv; omega
            change r.val + 1 < _ at h_iff
            omega
          have hstep := shuffle_step ν ⟨r.val, by omega⟩
          have hcs : (⟨r.val, by omega⟩ : Fin (p + q)).castSucc = (⟨r.val,
              by omega⟩ : Fin (p + q + 1)) :=
            Fin.ext (by simp [Fin.castSucc])
          have hsu : (⟨r.val, by omega⟩ : Fin (p + q)).succ = r' :=
            Fin.ext (by simp [Fin.succ, r'])
          rw [hcs, hsu] at hstep
          rcases hstep with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · -- castSucc = t, succ > t
        simp only [Fin.val_castSucc, Fin.val_succ, add_tsub_cancel_right, Fin.eta]
        have hcs := coordSum_eq ν ⟨r.val, by omega⟩
        have hcsv : (⟨r.val, by omega⟩ : Fin (p + q + 1)).val = r.val := rfl
        suffices h : (ν.1 ⟨r.val, by omega⟩).2.val ≤ k.val by
          have hre : (ν.1 r).1.val = (ν.1 ⟨r.val, by omega⟩).1.val := by congr 3
          simp only [Fin.le_def] at hcs ⊢; omega
        by_cases hr : r.val = 0
        · have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = 0 := Fin.ext (by simp [hr])
          rw [this, Shuffle.apply_zero]; simp
        · let r' : Fin (p + q + 1) := ⟨r.val - 1, by omega⟩
          have hr'lt : r'.val < (insertRightIndex ν k).val := by
            simp [r'] at h4 ⊢; omega
          have hsnd_lt : (ν.1 r').2.val < k.val :=
            (insertRightIndex_iff ν k r').mpr hr'lt
          have hstep := shuffle_step ν ⟨r.val - 1, by omega⟩
          have hcs2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).castSucc = r' :=
            Fin.ext (by simp [Fin.castSucc, r'])
          have hsu2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).succ = ⟨r.val, by omega⟩ :=
            Fin.ext (by simp [Fin.succ]; omega)
          rw [hcs2, hsu2] at hstep
          rcases hstep with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · exact (ν.1.monotone (by simp [Fin.le_def, Fin.val_succ])).1
    · -- Second coordinate monotone
      suffices hsuc : ∀ r : Fin (p + (q + 1)),
          (insertRightStepFun ν k r.castSucc).2 ≤ (insertRightStepFun ν k r.succ).2 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertRightStepFun ν k r).2)).2 hsuc hab
      intro r
      simp only [insertRightStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (Fin.succAbove_le_succAbove_iff.mpr (ν.1.monotone (Fin.castSucc_le_succ
            r)).2) -- cs < t, succ < t
      · -- cs < t, succ = t: succAbove(snd) ≤ k since snd < k
        have hrcs : (⟨r.castSucc.val, by simp; omega⟩ : Fin (p + q + 1)) =
            ⟨r.val, by omega⟩ := Fin.ext (by simp)
        have hsnd := (insertRightIndex_iff ν k ⟨r.val, by omega⟩).mpr h1
        simp only [Fin.succAbove]; split
        · simp only [Fin.le_def, Fin.val_castSucc]
          have : (ν.1 ⟨r.castSucc.val, by simp; omega⟩).2.val =
              (ν.1 ⟨r.val, by omega⟩).2.val := by rw [hrcs]
          omega
        · rename_i hn; exfalso
          simp only [not_lt, Fin.le_def, Fin.val_castSucc] at hn
          have : (ν.1 ⟨r.castSucc.val, by simp; omega⟩).2.val =
              (ν.1 ⟨r.val, by omega⟩).2.val := by rw [hrcs]
          omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · -- cs = t, succ > t: k ≤ succAbove(snd) since snd ≥ k
        have hsnd : ¬ (ν.1 ⟨r.val, by omega⟩).2.val < k.val := by
          rw [insertRightIndex_iff]; simp at h4; simp; omega
        push Not at hsnd
        have heq : (⟨r.succ.val - 1, by omega⟩ : Fin (p + q + 1)) = ⟨r.val, by omega⟩ := by
          ext; simp [Fin.val_succ]
        rw [heq]
        simp only [Fin.succAbove]
        split
        · rename_i hlt; exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at hlt; omega
        · simp only [Fin.le_def, Fin.val_succ]
          simp only [Fin.val_castSucc] at h4
          omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · have := Fin.val_succ r; have := Fin.val_castSucc r; omega
      · exact (Fin.succAbove_le_succAbove_iff.mpr
          (ν.1.monotone (by simp [Fin.le_def, Fin.val_succ])).2)
    ⟩, by
    -- Injectivity: f(a) = f(b) → coordSum(f(a)) = coordSum(f(b)) → a = b
    intro a b hab
    have ha := insertRightStepFun_coordSum ν k a
    have hb := insertRightStepFun_coordSum ν k b
    have heq : insertRightStepFun ν k a = insertRightStepFun ν k b := hab
    have : (insertRightStepFun ν k a).1.val + (insertRightStepFun ν k a).2.val =
        (insertRightStepFun ν k b).1.val + (insertRightStepFun ν k b).2.val := by rw [heq]
    exact Fin.ext (by omega)⟩

/-- Inserting a left step and removing the inserted vertex recovers the original
shuffle with `Fin.succAbove j` applied to the first coordinate.
(Purely combinatorial: no `SimplexCategory` or topology needed.) -/
lemma insertLeftStep_face {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    ∀ (k : Index (p + q)),
      (insertLeftStep ν j).1 (Fin.succAbove
        (⟨(insertLeftIndex ν j).val, by omega⟩ : Fin ((p + 1) + q + 1))
        (k.cast (by omega))) =
      (j.succAbove (ν.1 k).1, (ν.1 k).2) := by
  unfold LeanPool.EilenbergZilber.Shuffle.insertLeftStep;
  intro k
  unfold LeanPool.EilenbergZilber.Shuffle.insertLeftStepFun
  simp only [Fin.succAbove, OrderHom.coe_mk] at *;
  split_ifs <;> simp_all +decide only [Fin.castSucc, Fin.val_castAdd, Fin.val_cast, Fin.eta,
      Fin.succ, not_lt, Prod.mk.injEq, add_tsub_cancel_right];
  · exact absurd ‹_› ( ne_of_lt ‹_› );
  · exact absurd ‹_› ( not_le_of_gt ‹_› );
  · exact False.elim <| ‹¬_› <| Nat.lt_of_succ_lt ‹_›;
  · split_ifs <;> simp_all +decide [ Fin.ext_iff];
    · have := insertLeftIndex_ge ν j; have := insertLeftIndex_le ν j;
          simp_all +decide [ Fin.le_iff_val_le_val ] ; omega;
    · have := insertLeftIndex_iff ν j k; simp_all +decide [ Fin.le_def ] ;
      grind

/-- Inserting a right step and removing the inserted vertex recovers the original
shuffle with `Fin.succAbove k` applied to the second coordinate. -/
lemma insertRightStep_face {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    ∀ (i : Index (p + q)),
      (insertRightStep ν k).1 (Fin.succAbove
        (⟨(insertRightIndex ν k).val, by omega⟩ : Fin (p + (q + 1) + 1))
        (i.cast (by omega))) =
      ((ν.1 i).1, k.succAbove (ν.1 i).2) := by
  intro i
  generalize_proofs at *;
  unfold LeanPool.EilenbergZilber.Shuffle.insertRightStep; simp +decide only [Fin.succAbove,
      Fin.cast_eq_self, Fin.eta, OrderHom.coe_mk] ;
  unfold LeanPool.EilenbergZilber.Shuffle.insertRightStepFun; split_ifs <;>
      simp_all +decide only [Order.lt_add_one_iff, Fin.val_castSucc, Fin.eta, Prod.mk.injEq,
      Fin.ext_iff, true_and, not_lt, Fin.val_succ, add_tsub_cancel_right] ;
  all_goals split_ifs <;> simp_all +decide only [Fin.val_castSucc, Fin.succAbove, ↓reduceIte,
      not_lt, Fin.val_succ, Std.le_refl] ;
  any_goals split_ifs <;> simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;
  any_goals linarith [ show ( i : ℕ ) < ν.insertRightIndex k from by assumption ] ;
  · exact False.elim <| ‹¬Fin.castSucc i < ν.insertRightIndex k› <| Nat.lt_of_succ_lt ‹_›;
  · have := Fin.le_iff_val_le_val.mp ‹_›; simp_all +decide [] ; omega;
  · exact absurd ‹_› ( by linarith [ show ( i : ℕ ) + 1 > ( ν.insertRightIndex k : ℕ ) from
                           by linarith [ show ( i : ℕ ) ≥ ( ν.insertRightIndex k : ℕ ) from
                               by assumption ] ] ) ;

/-- The insert-left map `(j, ν) ↦ (insertLeftStep ν j, insertLeftIndex ν j)` is
injective: distinct `(j, ν)` pairs produce distinct `(μ, vertex)` pairs. -/
lemma insertLeftStep_injective {p q : ℕ}
    (j₁ j₂ : Fin (p + 2)) (ν₁ ν₂ : Shuffle p q)
    (hμ : insertLeftStep ν₁ j₁ = insertLeftStep ν₂ j₂)
    (hr : insertLeftIndex ν₁ j₁ = insertLeftIndex ν₂ j₂) :
    j₁ = j₂ ∧ ν₁ = ν₂ := by
  have h_eq : ν₁.insertLeftStep j₁ = ν₂.insertLeftStep j₂ → j₁ = j₂ := by
    intro h_eq
    have h_eq_fun : ∀ r : Fin (p + 1 + q + 1), (insertLeftStepFun ν₁ j₁ r).1 = (insertLeftStepFun ν₂
        j₂ r).1 := by
      intro r
      have := congr_arg (fun f => f.1 r) h_eq
      generalize_proofs at *; (
      exact congr_arg Prod.fst this)
    generalize_proofs at *; (
    have := h_eq_fun ⟨(insertLeftIndex ν₁ j₁).val, by
      exact Nat.lt_succ_of_le ( by linarith [ Fin.is_lt ( ν₁.insertLeftIndex j₁ ) ] ) ;⟩
    generalize_proofs at *; (
    unfold insertLeftStepFun at this; aesop;))
  generalize_proofs at *; exact ⟨h_eq hμ, by
    have := insertLeftStep_face ν₁ j₁; have := insertLeftStep_face ν₂ j₂; aesop;⟩;

/-- The insert-right map is injective. -/
lemma insertRightStep_injective {p q : ℕ}
    (k₁ k₂ : Fin (q + 2)) (ν₁ ν₂ : Shuffle p q)
    (hμ : insertRightStep ν₁ k₁ = insertRightStep ν₂ k₂)
    (hr : insertRightIndex ν₁ k₁ = insertRightIndex ν₂ k₂) :
    k₁ = k₂ ∧ ν₁ = ν₂ := by
  -- By comparing the coordinates of the last elements, we can conclude that k₁ = k₂.
  have hk : k₁ = k₂ := by
    unfold Shuffle.insertRightStep at hμ;
    simp_all +decide only [insertRightStepFun, Fin.val_fin_lt, Subtype.mk.injEq, OrderHom.mk.injEq,
        Fin.ext_iff];
    replace hμ := congr_fun hμ ( ν₂.insertRightIndex k₂ ) ; aesop;
  have := insertRightStep_face ν₁ k₁; have := insertRightStep_face ν₂ k₁; aesop;

/-! ##### Helper lemmas for `sign_insertLeftStep`

The proof reduces to an inversion-count identity: inserting a left step at
position `j` adds exactly `t - j` to the inversion count, where
`t = insertLeftIndex ν j`. We split the `invCount` sum at `t` using
`Fin.sum_univ_succAbove`, match the non-inserted terms against `invCount ν`,
and compute the contribution of the inserted step directly. -/

/-- The inserted step is a left step: the first coordinate increases from `j`
to `succAbove j (ν.1 t).1 > j` at the insertion vertex. -/
private lemma insertLeftStep_isLeftStep_at {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2))
    (ht : (insertLeftIndex ν j).val < p + 1 + q) :
    isLeftStep (insertLeftStep ν j) ⟨(insertLeftIndex ν j).val, ht⟩ := by
  -- Unfold to: j < j.succAbove (ν.1 ⟨t, ...⟩).fst
  unfold isLeftStep; simp +decide only [insertLeftStep, insertLeftStepFun, Fin.castSucc_mk,
      OrderHom.coe_mk, lt_self_iff_false, ↓reduceDIte, Fin.succ_mk, add_lt_iff_neg_left,
      Nat.add_eq_left, add_tsub_cancel_right, Fin.val_fin_lt]
  have hfst : ¬ (ν.1 ⟨(insertLeftIndex ν j).val, by omega⟩).1.val < j.val := by
    intro h
    have := (insertLeftIndex_iff ν j ⟨(insertLeftIndex ν j).val, by omega⟩).mp h
    simp at this
  -- succAbove j fst = fst.succ when fst ≥ j, so j < fst + 1
  simp only [Fin.succAbove]
  split
  · exfalso; simp [Fin.lt_def] at *; omega
  · simp [Fin.lt_def, Fin.val_succ] at *; omega

/-- The second coordinate at the insertion point equals `t - j`. -/
private lemma insertLeftStep_snd_at {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) :
    ((insertLeftStep ν j).1 ⟨(insertLeftIndex ν j).val, by omega⟩).2.val =
    (insertLeftIndex ν j).val - j.val := by
  simp +decide [insertLeftStep, insertLeftStepFun]

/-- The `invCount` term at the insertion point contributes `t - j`:
`if isLeftStep μ t then μ(t).snd else 0 = t - j`. -/
private lemma insertLeftStep_invCount_term_at {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2))
    (ht : (insertLeftIndex ν j).val < p + 1 + q) :
    (if ((insertLeftStep ν j).1 (Fin.castSucc ⟨(insertLeftIndex ν j).val, ht⟩)).1 <
        ((insertLeftStep ν j).1 (Fin.succ ⟨(insertLeftIndex ν j).val, ht⟩)).1
     then ((insertLeftStep ν j).1 (Fin.castSucc ⟨(insertLeftIndex ν j).val, ht⟩)).2.val
     else 0) =
    (insertLeftIndex ν j).val - j.val := by
  split_ifs with h
  · exact insertLeftStep_snd_at ν j
  · exact absurd (insertLeftStep_isLeftStep_at ν j ht) h

/-- Each non-inserted step of `insertLeftStep ν j` has the same `invCount`
contribution as the corresponding step of `ν`. For step `i` of `ν`, the
matching step in the new shuffle is `i` if `i < t`, or `i + 1` if `i ≥ t`
(where `t = insertLeftIndex ν j`).

**Proof sketch** (three cases by position of `i` relative to `t`):
- **i+1 < t** (both endpoints in 'before' region): `insertLeftStepFun` applies
  `succAbove j` to both fst coords. `Fin.succAbove_lt_succAbove_iff` shows
  the fst comparison is preserved. The snd coord is unchanged.
- **i < t ≤ i+1** (castSucc in 'before', succ at insertion point): The new
  fst comparison is `succAbove(j, ν(i).fst) < j`. Since `ν(i).fst < j`
  (by `insertLeftIndex_iff`), `succAbove = castSucc`, so the condition
  reduces to `ν(i).fst < j`. The original condition `ν(i).fst < ν(i+1).fst`
  is equivalent since `ν(i).fst < j ≤ ν(i+1).fst`. Snd is unchanged.
- **i ≥ t** (both endpoints in 'after' region): `insertLeftStepFun` shifts
  by -1, mapping back to indices `i` and `i+1` of ν. Same argument via
  `succAbove` preserving ordering. Snd unchanged.

The main difficulty is Fin proof-irrelevance: `split_ifs` creates many
branches where `⟨i.val, proof₁⟩` and `i.castSucc` need to be identified.
Use `congr 3; ext; simp [Fin.val_castSucc]` to close the `.2.val` goals,
and `Fin.succAbove_lt_succAbove_iff` + `convert` for the condition goals.
`Fin.lt_def` loops with `simp` — avoid it or use `- Fin.lt_def`. -/
private lemma insertLeftStep_invCount_term_skip {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2))
    (i : Fin (p + q)) :
    let t := (insertLeftIndex ν j).val
    let r : Fin (p + 1 + q) :=
      if i.val < t then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩
    (if ((insertLeftStep ν j).1 r.castSucc).1 <
        ((insertLeftStep ν j).1 r.succ).1
     then ((insertLeftStep ν j).1 r.castSucc).2.val
     else 0) =
    (if (ν.1 (Fin.castSucc i)).1 < (ν.1 (Fin.succ i)).1
     then (ν.1 (Fin.castSucc i)).2.val
     else 0) := by
  set t := (insertLeftIndex ν j).val
  by_cases h1 : i.val + 1 < t
  · -- Case 1: i+1 < t (both endpoints in 'before' region)
    simp only [show i.val < t from by omega]
    simp only [ite_true, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
    have hcs_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 + q)).castSucc.val = i.val := by
      simp [Fin.val_mk]
    have hsu_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 + q)).succ.val = i.val + 1 := by
      simp [Fin.val_mk]
    split_ifs <;> try omega
    all_goals simp only at *
    -- Goal 1: .2 values match (Fin proof-irrelevance)
    · congr 2;
    -- Goal 2: contradiction (succAbove preserves ordering)
    · exfalso; rename_i h_sa h_not
      exact h_not (Fin.succAbove_lt_succAbove_iff.mp (by
        convert h_sa using 2 <;>
          (congr 1)))
    -- Goal 3: contradiction (same)
    · exfalso; rename_i h_sa h_orig
      apply h_sa
      exact Fin.succAbove_lt_succAbove_iff.mpr (by
        convert h_orig using 2 <;>
          (congr 1))
  · by_cases h2 : i.val < t
    · -- Case 2: i < t ≤ i+1 (castSucc before, succ at insertion point)
      simp only [h2]
      simp only [ite_true, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
      have hcs_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 +
          q)).castSucc.val = i.val := by
        simp [Fin.val_mk]
      have hsu_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 +
          q)).succ.val = i.val + 1 := by
        simp [Fin.val_mk]
      split_ifs <;> try omega
      all_goals simp only at *
      · congr 2;
      · exfalso; rename_i h_sa h_not
        simp only [hcs_val, hsu_val] at *
        apply h_not
        -- (↑ν i.castSucc).1.val < j.val since i < t, and (↑ν i.succ).1.val ≥ j.val since ¬(i+1 < t)
        have heq1 : (⟨i.val, (by omega : i.val < p + q + 1)⟩ : Fin (p + q + 1)) = i.castSucc := by
          ext; simp
        have heq2 : (⟨i.val + 1, (by omega : i.val + 1 < p + q + 1)⟩ : Fin (p + q +
            1)) = i.succ := by
          ext; simp [Fin.val_succ]
        have h_cs_lt := (insertLeftIndex_iff ν j ⟨i.val, by omega⟩).mpr (by simp; omega)
        have h_su_ge := mt (insertLeftIndex_iff ν j ⟨i.val + 1, by omega⟩).mp (by simp; omega)
        rw [heq1] at h_cs_lt; rw [heq2] at h_su_ge
        push Not at h_su_ge
        exact Fin.lt_def.mpr (by omega)
      · exfalso; rename_i h_sa h_orig
        simp only [hcs_val, hsu_val] at *
        apply h_sa
        rw [Fin.succAbove_lt_iff_castSucc_lt]
        have heq1 : (⟨i.val, (by omega : i.val < p + q + 1)⟩ : Fin (p + q + 1)) = i.castSucc := by
          ext; simp
        have h_cs_lt := (insertLeftIndex_iff ν j ⟨i.val, by omega⟩).mpr (by simp; omega)
        rw [heq1] at h_cs_lt
        exact Fin.mk_lt_mk.mpr h_cs_lt
    · -- Case 3: i ≥ t (both endpoints in 'after' region)
      simp only [show ¬(i.val < t) from h2]
      simp only [ite_false, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
      have hcs_val : (⟨↑i + 1, (by omega : ↑i + 1 < p + 1 + q)⟩ : Fin (p + 1 +
          q)).castSucc.val = i.val + 1 := by
        simp [Fin.val_mk]
      have hsu_val : (⟨↑i + 1, (by omega : ↑i + 1 < p + 1 + q)⟩ : Fin (p + 1 +
          q)).succ.val = i.val + 2 := by
        simp [Fin.val_mk]
      split_ifs <;> try omega
      all_goals simp only at *
      · congr 2;
      · exfalso; rename_i h_sa h_not
        apply h_not
        exact Fin.succAbove_lt_succAbove_iff.mp (by
          convert h_sa using 2 <;>
            (congr 1))
      · exfalso; rename_i h_sa h_orig
        apply h_sa
        exact Fin.succAbove_lt_succAbove_iff.mpr (by
          convert h_orig using 2 <;>
            (congr 1))

/-- **Key inversion-count identity** (additive form, avoiding ℕ subtraction):
`invCount(insertLeftStep ν j) + j = invCount(ν) + insertLeftIndex(ν, j)`.

Proof sketch: split the invCount sum for the new shuffle at the insertion
index `t`. The term at `t` contributes `t - j`
(by `insertLeftStep_invCount_term_at`). Each remaining step `r ≠ t` bijects
with a step of `ν` having the same contribution
(by `insertLeftStep_invCount_term_skip`). -/
private lemma invCount_insertLeftStep_add {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) :
    (insertLeftStep ν j).invCount + j.val =
    ν.invCount + (insertLeftIndex ν j).val := by
  set μ := insertLeftStep ν j
  have hge : j.val ≤ (insertLeftIndex ν j).val := insertLeftIndex_ge ν j
  have hle : (insertLeftIndex ν j).val ≤ j.val + q := insertLeftIndex_le ν j
  -- Key: rewrite p+1+q as (p+q)+1 to use Fin.sum_univ_succAbove
  -- This is valid because p + 1 + q = (p + q) + 1 definitionally in Lean's kernel?
  -- No — but we can cast via finCongr.
  -- The insertion index as a Fin ((p+q)+1), if in range
  -- Since t ≤ j + q ≤ (p+1) + q = p + 1 + q, and p + 1 + q = (p + q) + 1,
  -- we have t ≤ (p+q) + 1. But we need t < (p+q) + 1, i.e., t ≤ p + q.
  -- When t = (p+q)+1, the insertion is at the very end.
  -- Actually, Fin.sum_univ_succAbove splits Fin (n+1) at ANY element of Fin (n+1),
  -- so we just need t < p + 1 + q. This might not hold when t = p+q+1 = p+1+q.
  -- Use Finset approach instead: extract element from univ, biject rest.
  simp only [invCount]
  -- Use Finset.sum_erase_add to extract one element
  by_cases ht_in : (insertLeftIndex ν j).val < p + 1 + q
  · -- Main case: t is a valid step index
    set t : Fin (p + 1 + q) := ⟨(insertLeftIndex ν j).val, ht_in⟩
    -- Extract term at t: ∑ = f(t) + (∑ over univ \ {t})
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    -- f(t) = t - j by insertLeftStep_invCount_term_at
    rw [insertLeftStep_invCount_term_at ν j ht_in]
    -- Biject remaining terms with invCount(ν) via skip map
    have hskip := insertLeftStep_invCount_term_skip ν j
    suffices h : ∑ x ∈ Finset.univ.erase t,
        (if (μ.1 x.castSucc).1 < (μ.1 x.succ).1 then (μ.1 x.castSucc).2.val else 0) =
      ∑ r : Fin (p + q),
        (if (ν.1 r.castSucc).1 < (ν.1 r.succ).1 then (ν.1 r.castSucc).2.val else 0) by omega
    -- φ(i) = if i.val < t then ⟨i, _⟩ else ⟨i+1, _⟩
    let φ : Fin (p + q) → Fin (p + 1 + q) :=
      fun i => if h : i.val < (insertLeftIndex ν j).val
        then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩
    apply (Finset.sum_nbij φ _ _ _ _).symm
    · -- maps into erase t
      intro i _; simp only [Finset.mem_erase, Finset.mem_univ, and_true, φ]
      intro heq
      have : (if h : i.val < (insertLeftIndex ν j).val then (⟨i.val, by omega⟩ : Fin (p+1+q))
        else ⟨i.val + 1, by omega⟩).val = t.val := congr_arg Fin.val heq
      have ht_val : t.val = (insertLeftIndex ν j).val := rfl
      split_ifs at this with h <;> simp at this <;> omega
    · -- injective
      intro a _ b _ hab
      have : (φ a).val = (φ b).val := congr_arg Fin.val hab
      simp only [φ] at this
      ext
      split_ifs at this with ha hb <;> simp at this <;> omega
    · -- surjective onto erase t
      intro r hr
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
          Set.mem_singleton_iff, true_and] at hr
      have hr_ne : r.val ≠ (insertLeftIndex ν j).val := fun h => hr (Fin.ext h)
      by_cases hrlt : r.val < (insertLeftIndex ν j).val
      · exact ⟨⟨r.val, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val, by omega⟩ = r
          simp only [φ, hrlt, dite_true];⟩
      · exact ⟨⟨r.val - 1, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val - 1, by omega⟩ = r
          simp only [φ]; split_ifs with h; · exfalso; omega
          · exact Fin.ext (by simp; omega)⟩
    · -- pointwise equality: fν(i) = fμ(φ(i))
      intro i _; exact (hskip i).symm
  · -- Boundary case: t = p + 1 + q (insertion at the very end, j = p+1)
    have hfmu : (if (μ.1 (Fin.castSucc ⟨p + q, by omega⟩)).1 < (μ.1 (Fin.succ ⟨p + q, by omega⟩)).1
      then (μ.1 (Fin.castSucc ⟨p + q, by omega⟩)).2.val else 0) = q := by
      have ht_eq : (insertLeftIndex ν j).val = p + 1 + q := by omega
      simp only [μ, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all <;> try omega
      -- Remaining: "before" branch for castSucc, "at" branch for succ
      · have hlast : ν.1 ⟨p + q, by omega⟩ = (Fin.last p, Fin.last q) := by
          have : (⟨p + q, (by omega : p + q < p + q + 1)⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
            Fin.ext (by simp [Fin.last])
          rw [this]; exact Shuffle.apply_last ν
        simp only [hlast, Fin.last]
      · exfalso; simp at h2; omega
      · have heq : (⟨p + q, (by omega : p + q < p + q + 1)⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
          Fin.ext (by simp [Fin.last])
        have h := Shuffle.apply_last ν; rw [← heq] at h
        change (ν.1 ⟨p + q, _⟩).2.val = q
        rw [show (ν.1 ⟨p + q, _⟩).2 = (Fin.last q) from congr_arg Prod.snd h]
        simp [Fin.last]
      · exfalso
        have heq : (⟨p + q, (by omega : p + q < p + q + 1)⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
          Fin.ext (by simp [Fin.last])
        have hlast' := Shuffle.apply_last ν; rw [← heq] at hlast'
        simp only [hlast', Fin.last] at h5
        rw [Fin.le_def, Fin.val_castSucc] at h5
        omega
    set s : Fin (p + 1 + q) := ⟨p + q, by omega⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), hfmu]
    have hskip := insertLeftStep_invCount_term_skip ν j
    suffices h : ∑ x ∈ Finset.univ.erase s,
        (if (μ.1 x.castSucc).1 < (μ.1 x.succ).1 then (μ.1 x.castSucc).2.val else 0) =
      ∑ r : Fin (p + q),
        (if (ν.1 r.castSucc).1 < (ν.1 r.succ).1 then (ν.1 r.castSucc).2.val else 0) by omega
    let φ : Fin (p + q) → Fin (p + 1 + q) :=
      fun i => if h : i.val < (insertLeftIndex ν j).val
        then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩
    apply (Finset.sum_nbij φ _ _ _ _).symm
    · -- maps into erase s
      intro i _; simp only [Finset.mem_erase, Finset.mem_univ, and_true, φ]
      intro heq
      have : (if h : i.val < (insertLeftIndex ν j).val then (⟨i.val, by omega⟩ : Fin (p+1+q))
        else ⟨i.val + 1, by omega⟩).val = s.val := congr_arg Fin.val heq
      have hs_val : s.val = p + q := rfl
      split_ifs at this with h <;> simp at this <;> omega
    · -- injective
      intro a _ b _ hab
      have : (φ a).val = (φ b).val := congr_arg Fin.val hab
      simp only [φ] at this
      ext
      split_ifs at this with ha hb <;> simp at this <;> omega
    · -- surjective onto erase s
      intro r hr
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
          Set.mem_singleton_iff, true_and] at hr
      have hr_ne : r.val ≠ p + q := fun h => hr (Fin.ext h)
      by_cases hrlt : r.val < (insertLeftIndex ν j).val
      · exact ⟨⟨r.val, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val, by omega⟩ = r
          simp only [φ, hrlt, dite_true]⟩
      · exact ⟨⟨r.val - 1, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val - 1, by omega⟩ = r
          simp only [φ]; split_ifs with h; · exfalso; omega
          · exact Fin.ext (by simp; omega)⟩
    · -- pointwise equality
      intro i _; exact (hskip i).symm

/-- Sign relation for left insertion:
`(insertLeftStep ν j).sign * (-1)^(insertLeftIndex ν j) = (-1)^j * ν.sign`.

Derived from `invCount_insertLeftStep_add` via exponent arithmetic:
the identity `invCount(μ) + j = invCount(ν) + t` gives
`(-1)^(invCount(μ) + j) = (-1)^(invCount(ν) + t)`, hence
`sign(μ) * (-1)^j = sign(ν) * (-1)^t`, and multiplying both sides
by `(-1)^(j+t)` (using `(-1)^(2k) = 1`) yields the result. -/
lemma sign_insertLeftStep {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) :
    (insertLeftStep ν j).sign * (-1 : ℤ) ^ (insertLeftIndex ν j).val =
    (-1 : ℤ) ^ j.val * ν.sign := by
  simp only [sign, ← pow_add]
  have h := invCount_insertLeftStep_add ν j
  have hge := insertLeftIndex_ge ν j
  rw [show (insertLeftStep ν j).invCount + (insertLeftIndex ν j).val =
    (j.val + ν.invCount) + 2 * ((insertLeftIndex ν j).val - j.val) from by omega]
  rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]



/-- Right insertion index equals left insertion index on the swapped shuffle. -/
private lemma insertRightIndex_eq_swap {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightIndex ν k).val = (insertLeftIndex (ν.swap) k).val := by
  simp only [insertRightIndex, insertLeftIndex]
  have : (Finset.univ.filter fun r : Fin (q + p + 1) =>
      ((ν.swap).1 r).1.val < k.val) =
    (Finset.univ.filter fun r : Fin (p + q + 1) =>
      (ν.1 r).2.val < k.val).map (Fin.castOrderIso (by omega)).toEquiv.toEmbedding := by
    ext x
    simp only [Finset.mem_filter_univ, Finset.mem_map]
    simp only [swap_apply_fst]
    exact ⟨fun h => ⟨_, h, Fin.ext rfl⟩, by rintro ⟨a, ha, rfl⟩; exact ha⟩
  rw [this, Finset.card_map]


/-- Right insertion is left insertion on the swapped shuffle. -/
private lemma insertRightStep_eq_swap {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightStep ν k).swap = insertLeftStep (ν.swap) k := by
  have hidx := insertRightIndex_eq_swap ν k
  apply Subtype.ext; ext r
  all_goals
    simp only [insertRightStep, insertLeftStep, insertRightStepFun, insertLeftStepFun]
    -- Replace the left index of `ν.swap` by the right index of `ν` before unfolding `swap`:
    -- once `swap` is unfolded inside the index's `Finset.filter`, simp cannot rewrite there
    -- because the filter's `DecidablePred` instance depends on the predicate.
    simp only [← hidx]
    simp only [swap, OrderHom.coe_mk, Fin.castOrderIso, Prod.swap, RelIso.coe_fn_mk,
      Equiv.coe_fn_mk, Fin.val_cast]
    split_ifs <;> simp_all [Fin.cast]


/-- Sign relation for right insertion:
`(insertRightStep ν k).sign * (-1)^(insertRightIndex ν k) =
 (-1)^p * (-1)^k * ν.sign`. -/
lemma sign_insertRightStep {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightStep ν k).sign * (-1 : ℤ) ^ (insertRightIndex ν k).val =
    (-1 : ℤ) ^ p * ((-1 : ℤ) ^ k.val * ν.sign) := by
  have h1 := sign_eq_negOnePow_mul_swap_sign (insertRightStep ν k)
  have h2 := insertRightStep_eq_swap ν k
  have h3 := insertRightIndex_eq_swap ν k
  have h4 := sign_insertLeftStep (ν.swap) k
  have h5 := sign_eq_negOnePow_mul_swap_sign ν
  rw [h1, h2, h3, h5]
  -- LHS: (-1)^(p*(q+1)) * sign * (-1)^idx
  -- RHS: (-1)^p * ((-1)^k * ((-1)^(p*q) * swap_sign))
  -- Use h4: sign * (-1)^idx = (-1)^k * swap_sign
  -- Then LHS = (-1)^(p*(q+1)) * (-1)^k * swap_sign
  -- RHS = (-1)^(p + p*q) * (-1)^k * swap_sign, and p*(q+1) = p + p*q
  calc (-1 : ℤ) ^ (p * (q + 1)) *
      (insertLeftStep (ν.swap) k).sign * (-1) ^ (insertLeftIndex (ν.swap) k).val
      = (-1) ^ (p * (q + 1)) *
        ((insertLeftStep (ν.swap) k).sign * (-1) ^ (insertLeftIndex (ν.swap) k).val) := by ring
    _ = (-1) ^ (p * (q + 1)) * ((-1) ^ k.val * (ν.swap).sign) := by rw [h4]
    _ = (-1) ^ p * ((-1) ^ k.val * ((-1) ^ (p * q) * (ν.swap).sign)) := by
        rw [show p * (q + 1) = p * q + p from by ring, pow_add]; ring

/-! ##### Diagonal cancellation

The LHS terms not in the image of `insertLeftStep` or `insertRightStep` are
"diagonal" terms: they arise from vertex removals where the steps on either
side have different types (one left, one right).  These cancel pairwise via
a sign-reversing involution that swaps the two steps around the removed vertex. -/

/-- A `(μ, r)` pair is a **diagonal term** if vertex `r` has one adjacent left
step and one adjacent right step (in either order LR or RL).
Boundary vertices (r = 0 or r = last) are never diagonal. -/
def isDiagonalVertex {p q : ℕ} (μ : Shuffle p q)
    (r : Index (p + q)) : Prop :=
  if h₁ : 0 < r.val then
    if h₂ : r.val < p + q then
      (isLeftStep μ ⟨r.val - 1, by omega⟩ ∧ ¬ isLeftStep μ ⟨r.val, h₂⟩) ∨
      (¬ isLeftStep μ ⟨r.val - 1, by omega⟩ ∧ isLeftStep μ ⟨r.val, h₂⟩)
    else False
  else False

instance decidablePredIsDiagonalVertex {p q : ℕ} (μ : Shuffle (p) (q)) :
    DecidablePred (isDiagonalVertex μ) := by
  intro r; unfold isDiagonalVertex; split_ifs <;> infer_instance

/-! ##### Insertion–diagonal interface

The insertion maps produce exactly the non-diagonal terms of the boundary sum.
Each insertion lands in the non-diagonal set, together they cover it, and
their images are disjoint. -/

/-- Left insertion always produces a non-diagonal vertex: the two steps
adjacent to the inserted vertex are both left steps (LL pattern). -/
lemma insertLeftStep_not_diagonal {p q : ℕ}
    (ν : Shuffle p (q)) (j : Fin (p + 2)) :
    ¬isDiagonalVertex (insertLeftStep ν j)
      ((insertLeftIndex ν j).cast (by omega)) := by
  by_contra h_contra
  generalize_proofs at *;
  unfold Shuffle.isDiagonalVertex at h_contra
  generalize_proofs at *;
  split_ifs at h_contra ; simp_all +decide only [isLeftStep, Fin.val_cast, Fin.castSucc_mk,
      Fin.succ_mk, Fin.val_fin_lt, not_lt];
  cases h : ( ν.insertLeftIndex j : ℕ ) <;> simp_all +decide only [zero_tsub, Fin.zero_eta,
      zero_add, Fin.val_eq_zero_iff, add_tsub_cancel_right];
  · grind;
  · unfold Shuffle.insertLeftStep at * ; simp_all +decide only [OrderHom.coe_mk] ;
    unfold Shuffle.insertLeftStepFun at * ; simp_all +decide only [lt_add_iff_pos_right,
        ↓reduceDIte, lt_self_iff_false, Fin.succAbove_lt_iff, Fin.castSucc,
        Order.lt_add_one_iff, Order.add_one_le_iff, add_lt_iff_neg_left, Nat.add_eq_left,
        add_tsub_cancel_right, Fin.succAbove_le_iff] ;
    cases h_contra <;> try simp_all +decide only [Fin.succAbove]
    · -- Both neighbours lie before `j`, but the right one sits at `insertLeftIndex ν j` itself.
      rename_i n hlt
      have hb : n + 1 < p + q + 1 := by
        have := ‹↑(Fin.cast _ (ν.insertLeftIndex j)) < p + 1 + q›
        simp only [Fin.val_cast] at this
        omega
      have := (insertLeftIndex_iff ν j ⟨n + 1, hb⟩).mp (by simpa [Fin.lt_def] using hlt.2)
      simp [h] at this
    · split_ifs at * <;> simp_all +decide only [Fin.lt_def, Fin.val_castSucc, Fin.le_iff_val_le_val,
          not_lt, Fin.val_succ, Order.lt_add_one_iff, and_true]
      · omega
      · linarith! [ Fin.is_lt j ] ;
      · linarith! [ ν.1.monotone ( show ⟨ ‹_›, by linarith ⟩ ≤ ⟨ ‹_› + 1,
            by linarith ⟩ from Nat.le_succ _ ) ] ;
      · have := insertLeftIndex_iff ν j ⟨ ‹_›,
            by omega ⟩ ; simp_all +decide only [lt_add_iff_pos_right, iff_true] ;
        linarith! [ Fin.is_lt j ] ;

/-- Right insertion always produces a non-diagonal vertex: the two steps
adjacent to the inserted vertex are both right steps (RR pattern). -/
lemma insertRightStep_not_diagonal {p q : ℕ}
    (ν : Shuffle (p + 1) q) (k : Fin (q + 2)) :
    ¬isDiagonalVertex (insertRightStep ν k)
      ((insertRightIndex ν k).cast (by omega)) := by
  unfold Shuffle.isDiagonalVertex; simp +decide only [Fin.cast_eq_self, Fin.val_pos_iff,
      insertRightStep, dite_false_right, not_exists, not_or, not_and, Decidable.not_not] ;
  unfold Shuffle.isLeftStep; intros; simp_all +decide only [insertRightStepFun, Fin.val_fin_lt,
      Fin.castSucc_mk, OrderHom.coe_mk, Fin.succ_mk, add_tsub_cancel_right, Fin.eta,
      lt_self_iff_false, ↓reduceDIte, Nat.add_eq_left, not_lt] ;
  split_ifs at * <;> simp_all +decide only [not_lt, Fin.eta, lt_self_iff_false, not_false_eq_true,
      IsEmpty.forall_iff, Std.le_refl, forall_const, true_and, not_true_eq_false, Nat.add_eq_left];
  all_goals erw [ Fin.lt_def ] at *; simp_all +decide only [Fin.coe_ofNat_eq_mod,
      lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, Nat.mod_eq_of_lt, Fin.val_pos_iff,
      tsub_lt_self_iff, and_self, add_lt_iff_neg_left, Fin.val_fin_lt, Nat.add_eq_left,
      implies_true, true_and] ;
  any_goals omega;
  · constructor <;> intro h <;> have := ν.1.monotone ( show ⟨ ( ν.insertRightIndex k : ℕ ) - 1,
        by omega ⟩ ≤ ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩ from Nat.sub_le _ _
        ) <;> simp_all +decide [ Fin.le_iff_val_le_val ] ;
    · have := insertRightIndex_iff ν k ⟨ ( ν.insertRightIndex k : ℕ ) - 1,
          by omega ⟩ ; simp_all +decide [] ;
      have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ) - 1,
          by omega ⟩ ; have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ),
          by omega ⟩ ; simp_all +decide [] ; omega;
    · have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩ ; simp_all +decide [] ;
      have := ( insertRightIndex_iff ν k ⟨ ( ν.insertRightIndex k : ℕ ),
          by omega ⟩ ) ; simp_all +decide [] ;
      omega;
  · exact absurd ‹_› ( not_le_of_gt ( Nat.pred_lt ( ne_bot_of_gt ‹_› ) ) )



/- Every non-diagonal vertex of a `(p+1,q+1)`-shuffle is in the image of
either `insertLeftStep` (from a `(p, q+1)`-shuffle and face index `j`) or
`insertRightStep` (from a `(p+1, q)`-shuffle and face index `k`).

This covers interior LL/RR vertices and boundary vertices (r = 0 or r = last). -/
section

/-- A vertex `r` is a "left vertex" if the adjacent steps are both left steps
(or it is a boundary vertex adjacent to a left step). -/
def isLeftVertex {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q + 1)) : Prop :=
  (∀ k : Fin (p + q), k.succ = r → isLeftStep μ k) ∧
  (∀ k : Fin (p + q), k.castSucc = r → isLeftStep μ k)

/-- A vertex `r` is a "right vertex" if the adjacent steps are both right steps. -/
def isRightVertex {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q + 1)) : Prop :=
  (∀ k : Fin (p + q), k.succ = r → ¬Shuffle.isLeftStep μ k) ∧
  (∀ k : Fin (p + q), k.castSucc = r → ¬Shuffle.isLeftStep μ k)

/-- Inverse of `Fin.succAbove p`: maps `i` to `j` such that `p.succAbove j = i`,
assuming `i ≠ p`. -/
def finRemove {n : ℕ} (p : Fin (n + 2)) (i : Fin (n + 2)) : Fin (n + 1) :=
  if h : i < p then
    ⟨i.val, by omega⟩
  else
    ⟨i.val - 1, by
      have : i.val < n + 2 := i.isLt
      omega⟩

/-- Removing a left step at `r` (assuming `isLeftVertex μ r`). -/
def removeLeftFun {p q : ℕ} (μ : Shuffle (p + 1) q) (r : Fin (p + q + 2)) : Index (p +
    q) → Index p × Index q :=
  fun k =>
    let r' : Index (p + 1 + q) := r.cast (by omega)
    let k_mapped := r'.succAbove (k.cast (by omega))
    let val := μ.1 k_mapped
    (finRemove (μ.1 r').1 val.1, val.2)

/-- Removing a right step at `r` (assuming `isRightVertex μ r`). -/
def removeRightFun {p q : ℕ} (μ : Shuffle p (q + 1)) (r : Fin (p + q + 2)) : Index (p +
    q) → Index p × Index q :=
  fun k =>
    let r' : Index (p + q + 1) := r.cast (by omega)
    let k_mapped := r'.succAbove (k.cast (by omega))
    let val := μ.1 k_mapped
    (val.1, finRemove (μ.1 r').2 val.2)

lemma succAbove_finRemove {n : ℕ} (p : Fin (n + 2)) (i : Fin (n + 2)) (h : i ≠ p) :
    p.succAbove (finRemove p i) = i := by
  unfold finRemove
  split_ifs with hi
  · rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    rfl
  · have hpi : p.val < i.val := Fin.lt_def.mp (lt_of_le_of_ne (not_lt.mp hi) (Ne.symm h))
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.mpr (by simp; omega))]
    ext
    simp
    omega

lemma finRemove_strictMono_on {n : ℕ} (p : Fin (n + 2)) :
    StrictMonoOn (finRemove p) {i | i ≠ p} := by
      -- To prove strict monotonicity, we need to show that if $i < j$ and both are not equal to
      -- $p$, then $\text{finRemove } p i < \text{finRemove } p j$.
      intros i hi j hj hij
      simp only [ne_eq, Set.mem_ofPred_eq, finRemove] at *;
      -- By definition of `finRemove`, we split into cases based on whether `i` and `j` are less
      -- than `p` or not.
      by_cases hip : i < p
      · by_cases hjp : j < p
        · aesop
        · -- Since $i < p$ and $j \geq p$, we have $i.val < j.val - 1$.
          have h_val : i.val < j.val - 1 := by
            grind
          generalize_proofs at *;
          split_ifs ; aesop
      · split_ifs <;> simp_all +decide only [Fin.ext_iff, not_lt, Fin.mk_lt_mk]
        · omega
        · generalize_proofs at *
          exact tsub_lt_tsub_iff_right (Nat.one_le_iff_ne_zero.mpr <| by aesop) |>.2 hij

lemma ne_fst_of_isLeftVertex {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Index ((p + 1) + q)}
    (h : isLeftVertex μ r) (k : Index ((p + 1) + q)) (hkr : k ≠ r) :
    (μ.1 k).1 ≠ (μ.1 r).1 := by
      -- Consider two cases: $k < r$ and $k > r$.
      by_cases h_cases : k.val < r.val;
      · -- Since $k < r$, we have $μ(k).1 ≤ μ(r-1).1$.
        have h_le : (μ.1 k).1 ≤ (μ.1 (Fin.mk (r.val - 1) (by omega))).1 := by
          exact μ.1.monotone ( Nat.le_sub_one_of_lt h_cases ) |>.1;
        rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +decide only [Fin.zero_eta, ne_eq, zero_tsub,
            add_tsub_cancel_right];
        · tauto;
        · exact ne_of_lt ( lt_of_le_of_lt h_le ( h.1 ⟨ r, by linarith ⟩ rfl ) );
      · -- Since $k$ is not less than $r$, we have $k > r$.
        have h_k_gt_r : (r.val + 1 : ℕ) ≤ k.val := by
          exact Nat.succ_le_of_lt ( lt_of_le_of_ne ( le_of_not_gt h_cases ) ( Ne.symm <|
              by simpa [ Fin.ext_iff ] using hkr ) );
        -- Since $r$ is a left vertex, we have $(μ.1 r).1 < (μ.1 (r + 1)).1$.
        have h_left_vertex : (μ.1 r).1.val < (μ.1 (Fin.mk (r.val + 1) (by
        linarith [ Fin.is_lt r, Fin.is_lt k ]))).1.val := by
          all_goals generalize_proofs at *;
          have := h.2 ⟨ r.val, by linarith ⟩ ; aesop;
        generalize_proofs at *;
        exact ne_of_gt ( lt_of_lt_of_le h_left_vertex ( μ.1.monotone ( Nat.succ_le_of_lt h_k_gt_r )
            |> And.left ) )

lemma ne_snd_of_isRightVertex {p q : ℕ} {μ : Shuffle p (q + 1)} {r : Index (p + (q + 1))}
    (h : isRightVertex μ r) (k : Index (p + (q + 1))) (hkr : k ≠ r) :
    (μ.1 k).2 ≠ (μ.1 r).2 := by
  by_cases h_cases : k.val < r.val
  · have h_le : (μ.1 k).2 ≤ (μ.1 (Fin.mk (r.val - 1) (by omega))).2 :=
      (μ.1.monotone (Nat.le_sub_one_of_lt h_cases)).2
    rcases r with ⟨_ | r, hr⟩ <;> simp_all +decide only [Fin.zero_eta, ne_eq, zero_tsub,
        add_tsub_cancel_right]
    · tauto
    · have hnot := h.1 ⟨r, by omega⟩ rfl
      unfold isLeftStep at hnot
      have hidx1 : (⟨r, by omega⟩ : Fin (p + (q + 1))).castSucc =
          ⟨r, by omega⟩ := Fin.ext (by simp)
      have hidx2 : (⟨r, by omega⟩ : Fin (p + (q + 1))).succ =
          ⟨r + 1, hr⟩ := Fin.ext (by simp)
      rcases shuffle_step μ ⟨r, by omega⟩ with hs | hs
      · rw [hidx1, hidx2] at hnot hs; omega
      · rw [hidx1, hidx2] at hs
        exact ne_of_lt (lt_of_le_of_lt h_le (Fin.lt_def.mpr (by omega)))
  · have h_k_gt_r : r.val + 1 ≤ k.val := by
      exact Nat.succ_le_of_lt
        (lt_of_le_of_ne (le_of_not_gt h_cases)
          (Ne.symm (by simpa [Fin.ext_iff] using hkr)))
    have h_right_vertex :
        (μ.1 r).2.val < (μ.1 (Fin.mk (r.val + 1) (by omega))).2.val := by
      have hnot := h.2 ⟨r.val, by omega⟩ rfl
      unfold isLeftStep at hnot
      have hidx1 : (⟨r.val, by omega⟩ : Fin (p + (q + 1))).castSucc = r :=
        Fin.ext (by simp)
      have hidx2 : (⟨r.val, by omega⟩ : Fin (p + (q + 1))).succ =
          ⟨r.val + 1, by omega⟩ := Fin.ext (by simp)
      rcases shuffle_step μ ⟨r.val, by omega⟩ with hs | hs
      · rw [hidx1, hidx2] at hnot hs; omega
      · rw [hidx1, hidx2] at hs; omega
    exact ne_of_gt
      (lt_of_lt_of_le h_right_vertex
        ((μ.1.monotone (Nat.succ_le_of_lt h_k_gt_r)).2))

lemma removeLeft_is_shuffle {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Fin (p + q + 2)}
    (h : isLeftVertex μ (r.cast (by omega))) :
    StrictMono (removeLeftFun μ r) := by
      intro i j hij;
      -- Let `v₁ = μ.1 (r.succAbove i)` and `v₂ = μ.1 (r.succAbove j)`.
      set v₁ := μ.1 (Fin.succAbove (Fin.cast (by omega) r) (i.cast (by omega)))
      set v₂ := μ.1 (Fin.succAbove (Fin.cast (by omega) r) (j.cast (by omega)));
      -- Since `μ` is a shuffle and `succAbove` is strictly monotone, `v₁ < v₂`.
      have hv₁v₂ : v₁ < v₂ := by
        refine lt_of_le_of_ne ?_ ?_
        · refine μ.1.monotone ?_
          simp +decide only [Fin.succAbove];
          split_ifs <;> simp_all +decide only [Fin.castSucc_le_castSucc_iff, Fin.cast_le_cast,
              not_lt, Fin.succ_le_castSucc_iff, Fin.cast_lt_cast, Fin.succ_le_succ_iff];
          · exact le_of_lt hij;
          · exact Nat.le_succ_of_le ( Nat.le_trans ( Nat.le_of_lt ‹_› ) ‹_› );
          · exact le_of_lt hij;
        · have := μ.2;
          intro H; have := @this ( Fin.succAbove ( Fin.cast ( by omega ) r ) ( Fin.cast (
              by omega ) i ) ) ( Fin.succAbove ( Fin.cast ( by omega ) r ) ( Fin.cast (
              by omega ) j ) ) ; simp_all +decide only [Fin.succAbove_inj, Fin.cast_inj] ;
          exact absurd ( this H ) hij.ne;
      -- Since `v₁.1 ≠ (μ.1 r).1` and `v₂.1 ≠ (μ.1 r).1` by `ne_fst_of_isLeftVertex`, we can apply
      -- `finRemove_strictMono_on`.
      have hv₁v₂_fst : v₁.1 ≠ (μ.1 (Fin.cast (by omega) r)).1 ∧ v₂.1 ≠ (μ.1 (Fin.cast (by omega)
          r)).1 := by
        apply And.intro;
        · have := ne_fst_of_isLeftVertex h (Fin.succAbove (Fin.cast (by omega) r) (i.cast
              (by omega))) ?_ <;> aesop;
        · apply ne_fst_of_isLeftVertex h;
          simp +decide [ Fin.succAbove_ne ];
      by_cases h : v₁.1 < v₂.1 <;> simp_all +decide only [Prod.lt_iff, true_and, ne_eq, false_and,
          false_or, not_lt];
      · have h_finRemove : finRemove (μ.1 (Fin.cast (by omega) r)).1 v₁.1 < finRemove (μ.1 (Fin.cast
            (by omega) r)).1 v₂.1 := by
          apply finRemove_strictMono_on
          · simp [hv₁v₂_fst]
          · exact hv₁v₂_fst.2;
          · exact h;
        exact Or.inl ⟨ h_finRemove, hv₁v₂.elim ( fun h => h ) fun h => h.2.le ⟩;
      · have h_eq : finRemove (μ.1 (Fin.cast (by omega) r)).1 v₁.1 = finRemove (μ.1 (Fin.cast
            (by omega) r)).1 v₂.1 := by
          rw [ le_antisymm hv₁v₂.1 h ];
        exact Or.inr ⟨ h_eq.le, hv₁v₂.2 ⟩

lemma removeRight_is_shuffle {p q : ℕ} {μ : Shuffle p (q + 1)} {r : Fin (p + q + 2)}
    (h : isRightVertex μ (r.cast (by omega))) :
    StrictMono (removeRightFun μ r) := by
      intro k l hkl
      simp only [Fin.cast_eq_self, removeRightFun, Prod.mk_lt_mk] at *;
      have h_comp : (μ.1 (r.succAbove k)).1 ≤ (μ.1 (r.succAbove l)).1 ∧ (μ.1 (r.succAbove
          k)).2 ≤ (μ.1 (r.succAbove l)).2 := by
        exact μ.1.monotone (by
        exact Fin.le_iff_val_le_val.mpr ( by simpa using hkl.le
                                              ) |> le_trans <| Fin.le_iff_val_le_val.mpr le_rfl;);
      have h_neq : (μ.1 (r.succAbove k)).2 ≠ (μ.1 r).2 ∧ (μ.1 (r.succAbove l)).2 ≠ (μ.1 r).2 := by
        have h_neq : ∀ k : Fin (p + q + 2), k ≠ r → (μ.1 k).2 ≠ (μ.1 r).2 := by
          exact fun k a => ne_snd_of_isRightVertex h k a
        generalize_proofs at *; aesop;
      cases lt_or_eq_of_le h_comp.1 <;> cases lt_or_eq_of_le h_comp.2 <;>
          simp_all +decide only [ne_eq, true_and, Std.le_refl, and_true, and_self,
          lt_self_iff_false, and_false, or_false, false_and, false_or, gt_iff_lt, or_self];
      · -- Since the second components are not equal and the first components are strictly
        -- increasing, the second component must be strictly increasing.
        have h_second_inc : (μ.1 (r.succAbove k)).2 < (μ.1 (r.succAbove l)).2 := by
          assumption;
        exact Or.inr ( finRemove_strictMono_on _ ( show ( μ.1 ( r.succAbove k ) ).2 ≠ ( μ.1 r ).2
            from h_neq.1 ) ( show ( μ.1 ( r.succAbove l ) ).2 ≠ ( μ.1 r ).2 from h_neq.2 )
            h_second_inc );
      · apply finRemove_strictMono_on;
        · exact h_neq.1;
        · aesop;
        · assumption;
      · have h_eq : (μ.1 (r.succAbove k)).1 = (μ.1 (r.succAbove l)).1 ∧ (μ.1 (r.succAbove
            k)).2 = (μ.1 (r.succAbove l)).2 := by
          aesop;
        have := μ.2; simp_all +decide [ Function.Injective ] ;
        specialize this ( show μ.1 ( r.succAbove k ) = μ.1 ( r.succAbove l ) from Prod.ext h_eq.1
            h_eq.2 ) ; simp_all +decide [] ;

/-- The shuffle obtained by removing a left step. -/
def removeLeft {p q : ℕ} (μ : Shuffle (p + 1) q) (r : Fin (p + q + 2))
    (h : isLeftVertex μ (r.cast (by omega))) : Shuffle p q :=
  ⟨⟨removeLeftFun μ r, (removeLeft_is_shuffle h).monotone⟩, (removeLeft_is_shuffle h).injective⟩

/-- The shuffle obtained by removing a right step. -/
def removeRight {p q : ℕ} (μ : Shuffle p (q + 1)) (r : Fin (p + q + 2))
    (h : isRightVertex μ (r.cast (by omega))) : Shuffle p q :=
  ⟨⟨removeRightFun μ r, (removeRight_is_shuffle h).monotone⟩, (removeRight_is_shuffle h).injective⟩

lemma finRemove_val_lt_iff {n : ℕ} {p : Fin (n + 2)} {i : Fin (n + 2)} (h : i ≠ p) :
    (finRemove p i).val < p.val ↔ i < p := by
      cases lt_or_gt_of_ne h <;> simp +decide [ *, LeanPool.EilenbergZilber.Shuffle.finRemove ];
      grind

lemma insertIndex_removeLeft {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Fin (p + q + 2)}
    (h : isLeftVertex μ (r.cast (by omega))) :
    insertLeftIndex (removeLeft μ r h) (μ.1 (r.cast (by omega))).1 = r.cast (by omega) := by
      refine Fin.ext ?_
      simp +decide only [isLeftVertex, Fin.cast_eq_self] at h ⊢;
      -- By definition of `isLeftVertex`, we know that for all `k`, if `k.castSucc = r.cast`, then
      -- `μ.isLeftStep k`.
      have h_fst_lt : ∀ k : Fin (p + q + 1), (μ.1 (Fin.succAbove (Fin.cast (by omega) r) (k.cast
          (by omega)))).1.val < (μ.1 (Fin.cast (by omega) r)).1.val ↔ k.val < r.val := by
        intro k; exact ⟨fun hk => by
          contrapose! hk;
          refine (μ.1.monotone ?_).1
          simp +decide [ Fin.le_iff_val_le_val, Fin.succAbove ];
          split_ifs <;> simp_all +decide [];
          linarith, fun hk => by
          have h_fst_lt : (μ.1 (Fin.succAbove (Fin.cast (by omega) r) (k.cast
              (by omega)))).1.val ≤ (μ.1 (Fin.cast (by omega) r)).1.val := by
            refine (μ.1.monotone ?_).1
            simp +decide [ Fin.le_iff_val_le_val, Fin.succAbove ];
            split_ifs <;> simp_all +decide [ Fin.lt_def ];
            linarith;
          refine lt_of_le_of_ne h_fst_lt ?_
          have := ne_fst_of_isLeftVertex h ( Fin.succAbove ( Fin.cast ( by omega ) r ) ( Fin.cast (
              by omega ) k ) ) ?_ <;> simp_all +decide only [Fin.ext_iff, Fin.val_succ,
              Fin.val_cast, Fin.val_castSucc, Fin.val_fin_le, ne_eq, not_false_eq_true];
          simp +decide only [Fin.succAbove];
          split_ifs <;> simp_all +decide only [Fin.lt_def, Fin.val_castSucc, Fin.val_cast,
              not_true_eq_false];
          exact Nat.ne_of_lt hk⟩;
      -- By definition of `insertLeftIndex`, we know that `insertLeftIndex ν j` is the number of `k`
      -- such that `(ν.1 k).1.val < j.val`.
      have h_insertLeftIndex : ∀ ν : Shuffle p q, ∀ j : Fin (p + 2), (ν.insertLeftIndex
          j).val = Finset.card (Finset.filter (fun k : Fin (p + q + 1) => (ν.1 k).1.val < j.val)
          Finset.univ) := by
        intro ν j; simp [insertLeftIndex]
      rw [h_insertLeftIndex, Finset.card_eq_of_bijective]
      · exact fun i hi => ⟨i, by linarith [Fin.is_lt r]⟩
      · intro a ha;
        use a.val;
        convert h_fst_lt a |>.1 _;
        · exact ⟨ fun h => h.1, fun h => ⟨ h, rfl ⟩ ⟩;
        · convert ha using 1
          rw [Finset.mem_filter_univ]
          simp +decide only [Fin.val_fin_lt, removeLeft, OrderHom.coe_mk, removeLeftFun];
          rw [ finRemove_val_lt_iff ];
          intro H; have := ne_fst_of_isLeftVertex h; simp_all +decide only [Fin.val_fin_lt,
              Subtype.forall, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, ne_eq,
              Fin.val_cast] ;
          specialize this ( Fin.succAbove ( Fin.cast ( by omega ) r ) ( Fin.cast (
              by omega ) a ) ) ; simp_all +decide only [Fin.succAbove, not_true_eq_false, imp_false,
              Decidable.not_not];
          split_ifs at this <;> simp_all +decide only [↓reduceIte, Fin.val_castSucc, Fin.val_cast,
              not_lt, Fin.val_succ];
          · exact absurd this ( ne_of_lt ‹_› );
          · grind;
      · intro i hi;
        convert h_fst_lt ⟨ i, by linarith [ Fin.is_lt r ] ⟩ |>.2 hi using 1
        rw [Finset.mem_filter_univ]
        simp +decide only [removeLeft, OrderHom.coe_mk, Fin.cast_mk, Fin.val_fin_lt];
        simp +decide only [removeLeftFun, Fin.cast_mk];
        rw [ finRemove_val_lt_iff ];
        have := ne_fst_of_isLeftVertex h ( Fin.succAbove ( Fin.cast ( by omega ) r ) ⟨ i,
            by linarith [ Fin.is_lt r ] ⟩ ) ?_ <;> simp_all +decide only [Fin.succAbove,
            Fin.val_fin_lt, Subtype.forall, Fin.castSucc_mk, Fin.succ_mk, ne_eq, not_false_eq_true];
        split_ifs <;> simp_all +decide only [Fin.ext_iff, Fin.val_succ, Fin.val_cast,
            Fin.val_castSucc, not_lt];
        · linarith;
        · exact absurd ‹_› ( not_le_of_gt ( Nat.lt_of_succ_le hi ) );
      · simp +contextual [ Fin.ext_iff ]

/-- `insertLeftStep` before the insertion index: the vertex of `ν`, with its first coordinate
pushed past `j`. -/
private lemma insertLeftStep_apply_of_lt {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (k : Fin ((p + 1) + q + 1)) (hk : k.val < (insertLeftIndex ν j).val) :
    (insertLeftStep ν j).1 k =
      (j.succAbove (ν.1 ⟨k, by have := (insertLeftIndex ν j).isLt; omega⟩).1,
        (ν.1 ⟨k, by have := (insertLeftIndex ν j).isLt; omega⟩).2) := by
  simp [insertLeftStep, insertLeftStepFun, hk]

/-- `insertLeftStep` at the insertion index: the new vertex `(j, t - j)`. -/
private lemma insertLeftStep_apply_of_eq {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (k : Fin ((p + 1) + q + 1)) (hk : k.val = (insertLeftIndex ν j).val) :
    (insertLeftStep ν j).1 k = (j, ⟨k.val - j.val, by have := insertLeftIndex_le ν j; omega⟩) := by
  simp [insertLeftStep, insertLeftStepFun, hk]

/-- `insertLeftStep` after the insertion index: the previous vertex of `ν`, with its first
coordinate pushed past `j`. -/
private lemma insertLeftStep_apply_of_gt {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (k : Fin ((p + 1) + q + 1)) (hk : (insertLeftIndex ν j).val < k.val) :
    (insertLeftStep ν j).1 k =
      (j.succAbove (ν.1 ⟨k - 1, by omega⟩).1, (ν.1 ⟨k - 1, by omega⟩).2) := by
  simp [insertLeftStep, insertLeftStepFun, hk.not_gt, hk.ne']

/-- Every vertex of `removeLeft μ r h`, with its first coordinate pushed back past `(μ r).1`, is
the corresponding vertex of `μ` away from `r`. -/
private lemma succAbove_removeLeft_apply {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Fin (p + q + 2)}
    (h : isLeftVertex μ (r.cast (by omega))) (i : Index (p + q)) :
    ((μ.1 (r.cast (by omega))).1.succAbove ((removeLeft μ r h).1 i).1,
        ((removeLeft μ r h).1 i).2) =
      μ.1 ((r.cast (by omega) : Index (p + 1 + q)).succAbove (i.cast (by omega))) :=
  Prod.ext (succAbove_finRemove _ _ (ne_fst_of_isLeftVertex h _ (Fin.succAbove_ne _ _))) rfl

lemma insertLeft_removeLeft {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Fin (p + q + 2)}
    (h : isLeftVertex μ (r.cast (by omega))) :
    insertLeftStep (removeLeft μ r h) (μ.1 (r.cast (by omega))).1 = μ := by
  have ht : (insertLeftIndex (removeLeft μ r h) (μ.1 (r.cast (by omega))).1).val = r.val := by
    simpa using congrArg Fin.val (insertIndex_removeLeft h)
  refine Subtype.ext (OrderHom.ext _ _ (funext fun k => ?_))
  rcases lt_trichotomy k.val r.val with hk | hk | hk
  · -- before `r`: the vertex is unchanged by `succAbove r`
    rw [insertLeftStep_apply_of_lt _ _ k (by omega), succAbove_removeLeft_apply h]
    congr 1
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]
    exact Fin.ext (by simp)
  · -- at `r`: the inserted vertex is `(μ r).1` paired with the complementary coordinate
    rw [insertLeftStep_apply_of_eq _ _ k (by omega)]
    have hkr : r.cast (by omega) = k := Fin.ext (by simp [hk])
    have h1 := congrArg (fun x => ((μ.1 x).1 : ℕ)) hkr
    have h2 := coordSum_eq μ k
    refine Prod.ext (congrArg (fun x => (μ.1 x).1) hkr) (Fin.ext ?_)
    dsimp only at h1 ⊢
    omega
  · -- after `r`: `succAbove r` shifts the preceding vertex back up to `k`
    rw [insertLeftStep_apply_of_gt _ _ k (by omega), succAbove_removeLeft_apply h]
    congr 1
    rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]
    exact Fin.ext (by simp; omega)

lemma insertIndex_removeRight {p q : ℕ} {μ : Shuffle p (q + 1)} {r : Fin (p + q + 2)}
    (h : isRightVertex μ (r.cast (by omega))) :
    insertRightIndex (removeRight μ r h) (μ.1 (r.cast (by omega))).2 = r.cast (by omega) := by
      have h_equiv : ∀ k : Fin (p + q + 1), (μ.1 (r.cast (by omega) |> Fin.succAbove <| k.cast
          (by omega))).2 < (μ.1 (Fin.cast (by omega) r)).2 ↔ k.val < r.val := by
        intro k
        constructor;
        · intro hk;
          contrapose! hk;
          exact μ.1.monotone (by
          simp +decide [ Fin.succAbove];
          split_ifs <;> simp_all +decide [ Fin.le_iff_val_le_val ];
          grind) |>.2;
        · intro hk
          have h_succ_above : (Fin.cast (by omega) r).succAbove (Fin.cast (by omega) k) < r := by
            simp +decide [ Fin.succAbove];
            split_ifs <;> simp_all +decide [ Fin.lt_def ];
          refine lt_of_le_of_ne ?_ ?_
          · exact μ.1.monotone h_succ_above.le |>.2;
          · apply ne_snd_of_isRightVertex h;
            exact ne_of_lt h_succ_above;
      norm_num [ Fin.ext_iff, Fin.val_mk, h_equiv ] at *;
      rw [ show ( μ.removeRight r h |> LeanPool.EilenbergZilber.Shuffle.insertRightIndex ) ( ( μ.1 r
          ).2 ) = Finset.card ( Finset.filter ( fun k : Fin ( p + q + 1 ) => ( μ.1 ( r.succAbove k )
          ).2 < ( μ.1 r ).2 ) Finset.univ ) from ?_ ];
      · rw [Finset.card_eq_of_bijective]
        · exact fun i hi => ⟨i, by linarith [Fin.is_lt r]⟩
        · grind;
        · aesop;
        · aesop;
      · unfold LeanPool.EilenbergZilber.Shuffle.insertRightIndex; simp +decide only
        congr! 2
        rename_i x hx
        simp only [removeRight, OrderHom.coe_mk, removeRightFun, Fin.cast_eq_self]
        have hne : (μ.1 (r.succAbove x)).2 ≠ (μ.1 r).2 :=
          ne_snd_of_isRightVertex h _ (Fin.succAbove_ne r x)
        rw [finRemove_val_lt_iff hne]

lemma isRightVertex_swap {p q : ℕ} {μ : Shuffle p q} {r : Fin (p + q + 1)} :
    isRightVertex μ r ↔ isLeftVertex μ.swap (r.cast (by omega)) := by
      simp +decide only [isRightVertex, isLeftVertex, swap, Fin.castOrderIso_apply];
      simp +decide only [isLeftStep];
      constructor;
      · intro h;
        constructor <;> intro k hk;
        · convert h.1 ⟨ k, by linarith [ Fin.is_lt k ] ⟩ _ using 1;
          · simp +decide only [Fin.succ, Fin.cast, Fin.mk.injEq, OrderHom.coe_mk, Fin.val_castSucc,
                Prod.fst_swap, Fin.val_fin_lt, Fin.castSucc_mk, not_lt] at hk ⊢;
            have := coordSum_eq μ ⟨ k, by linarith [ Fin.is_lt k ] ⟩ ; have := coordSum_eq μ ⟨ k +
                1, by linarith [ Fin.is_lt k ] ⟩ ; simp_all +decide only [Fin.val_fin_lt, not_lt,
                Fin.eta] ;
            constructor <;> intro <;> omega;
          · exact Fin.ext ( by simpa [ Fin.ext_iff ] using congr_arg Fin.val hk );
        · -- castSucc case: ¬isLeftStep at k ⇒ snd increases ⇒ isLeftStep for swap
          have hk' : (⟨k.val, by omega⟩ : Fin (p + q)).castSucc = r :=
            Fin.ext (by simpa [Fin.val_castSucc, Fin.val_cast] using congrArg Fin.val hk)
          have hnot : ¬isLeftStep μ ⟨k.val, by omega⟩ := h.2 _ hk'
          have hsnd : (μ.1 (⟨k.val, by omega⟩ : Fin (p + q)).castSucc).2.val <
              (μ.1 (⟨k.val, by omega⟩ : Fin (p + q)).succ).2.val := by
            have hiff := shuffle_fst_lt_iff_not_snd_lt μ ⟨k.val, by omega⟩
            exact Decidable.not_not.mp (mt hiff.mpr hnot)
          convert hsnd using 1 <;> rfl
      · intro h;
        constructor <;> intro k hk <;> simp_all +decide only [Fin.ext_iff, Fin.val_succ,
            Fin.val_cast, OrderHom.coe_mk, Fin.cast_castSucc, Prod.fst_swap, Fin.cast_succ_eq,
            Fin.val_fin_lt, Fin.val_castSucc, not_lt];
        · contrapose! h;
          intro h; specialize h ⟨ k, by linarith [ Fin.is_lt k ] ⟩ hk; simp_all +decide [ Fin.cast,
              Fin.castSucc ] ;
          have := coordSum_eq μ ( Fin.castAdd 1 k ) ; have := coordSum_eq μ k.succ ;
              simp_all +decide [ Fin.castAdd, Fin.succ ] ;
          grind;
        · contrapose! h;
          intro h';
          use ⟨ r.val, by
            linarith [ Fin.is_lt k, Fin.is_lt r ] ⟩
          generalize_proofs at *;
          simp_all +decide only [Fin.castSucc, Fin.cast, Fin.castAdd_mk, Fin.succ_mk, Fin.eta,
              true_and];
          simp_all +decide only [Fin.castAdd, Fin.succ];
          convert le_of_not_gt fun h'' => _;
          have := coordSum_eq μ r; have := coordSum_eq μ ⟨ r.val + 1,
              by linarith ⟩ ; simp_all +decide [ Fin.castLE ] ;
          linarith [ show ( μ.1 r |>.1 : ℕ ) < ( μ.1 ⟨ r.val + 1, by linarith ⟩ |>.1 : ℕ ) from h,
              show ( μ.1 r |>.2 : ℕ ) < ( μ.1 ⟨ r.val + 1, by linarith ⟩ |>.2 : ℕ ) from h'' ]

lemma removeRight_eq_swap_removeLeft {p q : ℕ} (μ : Shuffle p (q + 1)) (r : Fin (p + q + 2))
    (h : isRightVertex μ (r.cast (by omega))) :
    removeRight μ r h = (removeLeft μ.swap (r.cast (by omega)) (isRightVertex_swap.mp h)).swap := by
      unfold LeanPool.EilenbergZilber.Shuffle.removeRight
          LeanPool.EilenbergZilber.Shuffle.removeLeft
      generalize_proofs at *;
      unfold LeanPool.EilenbergZilber.Shuffle.removeRightFun
          LeanPool.EilenbergZilber.Shuffle.removeLeftFun
      generalize_proofs at *;
      ext ⟨ i, j ⟩
      · simp +decide only [Fin.cast_eq_self, OrderHom.coe_mk, Fin.cast_cast]
        unfold LeanPool.EilenbergZilber.Shuffle.swap; simp +decide only [Fin.castOrderIso_apply,
            OrderHom.coe_mk, Fin.cast_cast, Fin.cast_eq_self, Prod.fst_swap, Prod.snd_swap,
            Prod.swap_prod_mk, Fin.cast_mk] ;
        congr! 2
        generalize_proofs at *; simp +arith +decide only [Fin.succAbove, Fin.castSucc_mk,
            Fin.succ_mk] ; (
        congr! 2
        generalize_proofs at *; simp +arith +decide only [Fin.cast, Fin.mk_lt_mk] ; (
        split_ifs <;> simp +decide [ *, Fin.lt_def ] at * ;));
      · unfold LeanPool.EilenbergZilber.Shuffle.swap; simp +decide only [Fin.cast_eq_self,
            OrderHom.coe_mk, Fin.castOrderIso_apply, Fin.cast_cast, Prod.fst_swap, Prod.snd_swap,
            Prod.swap_prod_mk, Fin.cast_mk] ;
        congr! 2;
        congr! 2; simp +decide [ Fin.succAbove ] ; ring_nf;
        split_ifs <;> simp +decide only [Fin.cast, Fin.mk.injEq, Nat.right_eq_add,
            Nat.add_eq_right];
        · exact ‹¬_› ( by simpa [ Fin.cast ] using ‹_› );
        · exact ‹¬_› ( by simpa [ Fin.cast ] using ‹_› )

lemma not_diagonal_iff_left_or_right {p q : ℕ} {μ : Shuffle (p + 1) (q + 1)} {r : Fin (p + q + 3)} :
    ¬isDiagonalVertex μ (r.cast (by omega)) ↔ isLeftVertex μ (r.cast
        (by omega)) ∨ isRightVertex μ (r.cast (by omega)) := by
      unfold isDiagonalVertex isLeftVertex isRightVertex
      generalize_proofs at *;
      split_ifs <;> simp_all +decide only [Fin.val_cast, not_or, not_and, Decidable.not_not,
          Fin.val_pos_iff, not_lt, true_iff, isEmpty_Prop, IsEmpty.forall_iff, imp_self,
          nonpos_iff_eq_zero, Fin.cast_zero, Fin.succ_ne_zero, implies_true,
          Fin.castSucc_eq_zero_iff, forall_eq, true_and, lt_self_iff_false, Fin.coe_ofNat_eq_mod,
          Nat.zero_mod, add_pos_iff, Order.lt_add_one_iff, zero_le, or_self, zero_tsub];
      · constructor <;> intro h <;> rcases r with ⟨ _ | r, hr ⟩ <;> norm_num at *;
        · tauto;
        · rcases em (μ.isLeftStep ⟨r, by linarith⟩) with h' | h' <;>
            simp_all +decide only [forall_const, not_true_eq_false, IsEmpty.forall_iff, and_true,
              Fin.ext_iff, Fin.val_succ, Nat.add_right_cancel_iff, Fin.val_castSucc,
              not_false_eq_true, true_and];
          · exact Or.inl ⟨fun k hk => by convert h' using 1; aesop,
                fun k hk => by convert h using 1; aesop⟩;
          · exact Or.inr ⟨ fun k hk => by convert h' using 2; exact Fin.ext hk,
                fun k hk => by convert h using 2; exact Fin.ext hk ⟩;
        · cases h <;> simp_all +decide [ Fin.ext_iff ];
      · simp_all +decide [ Fin.ext_iff ];
        grind +ring;
      · exact em _

end

lemma nondiag_mem_insertLeft_or_insertRight {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index ((p + 1) + (q + 1)))
    (hr : ¬isDiagonalVertex μ r) :
    (∃ (j : Fin (p + 2)) (ν : Shuffle p (q + 1)),
      μ = insertLeftStep ν j ∧ (insertLeftIndex ν j).val = r.val) ∨
    (∃ (k : Fin (q + 2)) (ν : Shuffle (p + 1) q),
      μ = insertRightStep ν k ∧ (insertRightIndex ν k).val = r.val) := by
  -- By definition of diagonal vertex, if r is not diagonal, then it must be either left or right.
  have h_cases : isLeftVertex μ r ∨ isRightVertex μ r := by
    simpa [Fin.cast] using
      (not_diagonal_iff_left_or_right
        (μ := μ) (r := (⟨r.val, by omega⟩ : Fin (p + q + 3)))).mp
        (by simpa [Fin.cast] using hr)
  obtain h | h := h_cases <;> [left; right]
  · -- Left vertex case
    let rFin : Fin (p + (q + 1) + 2) := ⟨r.val, by omega⟩
    have hr_eq : (rFin.cast (by omega) : Index ((p + 1) + (q + 1))) = r := Fin.ext rfl
    have h' : isLeftVertex μ (rFin.cast (by omega)) := hr_eq ▸ h
    refine ⟨(μ.1 (rFin.cast (by omega))).1, removeLeft μ rFin h',
      (insertLeft_removeLeft h').symm, ?_⟩
    simpa [hr_eq] using congrArg Fin.val (insertIndex_removeLeft h')
  · -- Right vertex case
    let rFin : Fin ((p + 1) + q + 2) := ⟨r.val, by omega⟩
    have hr_eq : (rFin.cast (by omega) : Index ((p + 1) + (q + 1))) = r := Fin.ext rfl
    have h' : isRightVertex μ (rFin.cast (by omega)) := hr_eq ▸ h
    refine ⟨(μ.1 (rFin.cast (by omega))).2, removeRight μ rFin h', ?_, ?_⟩
    · have h_swap := removeRight_eq_swap_removeLeft μ rFin h'
      have h_ins := insertRightStep_eq_swap (removeRight μ rFin h')
        (μ.1 (rFin.cast (by omega))).2
      apply (swapEquiv (p + 1) (q + 1)).injective
      change μ.swap = ((μ.removeRight rFin h').insertRightStep
        (μ.1 (rFin.cast (by omega))).2).swap
      rw [h_ins, h_swap, swap_swap]
      let rFin' : Fin (q + (p + 1) + 2) := rFin.cast (by omega)
      have hL : isLeftVertex μ.swap (rFin'.cast (by omega)) := by
        have := isRightVertex_swap (μ := μ) (r := rFin.cast (by omega)) |>.mp h'
        convert this using 1
        exact Fin.ext rfl
      have hIL := insertLeft_removeLeft (μ := μ.swap) (r := rFin') hL
      convert hIL.symm using 2
      rfl
    · simpa [hr_eq] using congrArg Fin.val (insertIndex_removeRight h')

/-- Left insertion produces a left-type vertex: the step at (or just before)
the inserted vertex is a left step.  Here `isLeftType` checks `isLeftStep`
at index `min r.val ((p+1)+(q)-1)`. -/
lemma insertLeftStep_isLeftType {p q : ℕ}
    (ν : Shuffle p (q)) (j : Fin (p + 2)) :
    isLeftStep (insertLeftStep ν j)
      ⟨min (insertLeftIndex ν j).val ((p + 1) + (q) - 1), by omega⟩ := by
  cases min_cases ( ν.insertLeftIndex j : ℕ ) ( p + 1 + ( q ) - 1
      ) <;> simp_all +decide only [Nat.succ_add_sub_one, inf_eq_left, and_self, isLeftStep,
      inf_of_le_left, Fin.castSucc_mk, Fin.succ_mk, Fin.val_fin_lt, inf_eq_right, inf_of_le_right];
  · have := insertLeftStep_isLeftStep_at ν j ( by omega ) ; aesop;
  · -- Since the first component of the last element is (insertLeftIndex ν j).val, which is j.val +
    -- (q ), and the second component is 0, the pair (j, 0) is indeed the last element.
    have h_last : (insertLeftIndex ν j).val = j.val + (q) := by
      have h_last : (insertLeftIndex ν j).val ≤ j.val + (q) := by
        apply_rules [ insertLeftIndex_le ]
      generalize_proofs at *; (
      linarith [ Fin.is_lt j ])
    generalize_proofs at *;
    norm_num [ show ( ( ν.insertLeftStep j ) : Fin ( p + 1 + ( q ) + 1 ) → Index ( p + 1 ) × Index
        ( q  ) ) = insertLeftStepFun ν j from rfl, insertLeftStepFun ] at *;
    split_ifs <;> simp_all +decide [ Fin.succAbove ];
    · grind;
    · split_ifs <;> norm_num [ Fin.lt_def ] at * <;> omega;
    · omega

/-- Right insertion produces a non-left-type vertex: the step at (or just before)
the inserted vertex is a right step, not a left step. -/
lemma insertRightStep_not_isLeftType {p q : ℕ}
    (ν : Shuffle (p) q) (k : Fin (q + 2)) :
    ¬isLeftStep (insertRightStep ν k)
      ⟨min (insertRightIndex ν k).val ((p) + (q + 1) - 1), by omega⟩ := by
  intro h_left_step
  generalize_proofs at *;
  unfold isLeftStep at h_left_step;
  simp +decide only [insertRightStep, Nat.add_succ_sub_one, Fin.castSucc_mk, OrderHom.coe_mk,
      Fin.succ_mk, Fin.val_fin_lt] at h_left_step ⊢;
  unfold insertRightStepFun at h_left_step; simp +decide only [min_lt_iff, lt_self_iff_false,
      false_or, inf_eq_left, add_tsub_cancel_right] at h_left_step ⊢;
  split_ifs at h_left_step <;> try linarith [ Fin.is_lt ( ν.insertRightIndex k ) ] ;
  any_goals omega;
  · have := ν.1.monotone ( show ⟨ Min.min ( ν.insertRightIndex k : ℕ ) ( p + q ),
        by omega ⟩ ≤ ⟨ p + q, by omega ⟩ from Nat.min_le_right _ _
        ) ; simp_all +decide only [lt_self_iff_false, not_false_eq_true] ;
    have h_last : ν.1 ⟨p + q, by omega⟩ = (Fin.last (p), Fin.last q) := by
      exact Shuffle.apply_last ν
    generalize_proofs at *; simp_all +decide only [Nat.add_succ_sub_one, min_lt_iff,
        add_lt_add_iff_left, lt_add_iff_pos_right, or_true] ;
    simp_all +decide only [min_eq_right (by linarith : p + q ≤ (ν.insertRightIndex k : ℕ)),
        Std.le_refl];
    exact h_left_step.not_ge ( Nat.le_of_lt_succ <| by simp +arith +decide [ *] );
  · cases min_cases ( ν.insertRightIndex k : ℕ ) ( p + q ) <;> simp_all +decide [ Fin.lt_def ];
    have := insertRightIndex_iff ν k ⟨ ( ν.insertRightIndex k : ℕ ),
        by omega ⟩ ; simp_all +decide [] ;
    have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩ ; simp_all +decide [] ; omega;


/-- Extract the two facts from `isDiagonalVertex`: `0 < r` and `r < (p+1)+(q+1)`. -/
lemma isDiagonalVertex_bounds {p q : ℕ} {μ : Shuffle p q}
    {r : Index (p + (q))} (hr : isDiagonalVertex μ r) :
    0 < r.val ∧ r.val < (p) + (q) := by
  unfold isDiagonalVertex at hr
  split_ifs at hr with h₁ h₂
  exact ⟨‹_›, ‹_›⟩

/-- At a diagonal vertex with a left step at `r-1`, the shuffle step from
`r-1` to `r` increments fst, giving `μ(r).1 ≥ 1`. -/
lemma diagonal_left_fst_pos {p q : ℕ} {μ : Shuffle (p) (q)}
    {r : Index (p + (q))} (hr : isDiagonalVertex μ r)
    (hL : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    0 < (μ.1 r).1.val := by
  have ⟨h₁, h₂⟩ := isDiagonalVertex_bounds hr
  have hstep := shuffle_step μ ⟨r.val - 1, by omega⟩
  have hcs : (⟨r.val - 1, by omega⟩ : Fin ((p) + (q))).castSucc =
      (⟨r.val - 1, by omega⟩ : Index ((p) + (q))) :=
    Fin.ext (by simp [Fin.castSucc])
  have hsu : (⟨r.val - 1, by omega⟩ : Fin ((p) + (q))).succ = r :=
    Fin.ext (by simp [Fin.succ]; omega)
  rw [hcs, hsu] at hstep
  unfold isLeftStep at hL; rw [hcs, hsu] at hL
  rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩
  · omega
  · omega

/-- At a diagonal vertex with a right step at `r-1`, the shuffle step from
`r-1` to `r` increments snd, giving `μ(r).2 ≥ 1`. -/
lemma diagonal_right_snd_pos {p q : ℕ} {μ : Shuffle (p) (q)}
    {r : Index (p + (q))} (hr : isDiagonalVertex μ r)
    (hR : ¬isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    0 < (μ.1 r).2.val := by
  have ⟨h₁, h₂⟩ := isDiagonalVertex_bounds hr
  have hstep := shuffle_step μ ⟨r.val - 1, by omega⟩
  have hcs : (⟨r.val - 1, by omega⟩ : Fin ((p) + (q))).castSucc =
      (⟨r.val - 1, by omega⟩ : Index ((p) + (q))) :=
    Fin.ext (by simp [Fin.castSucc])
  have hsu : (⟨r.val - 1, by omega⟩ : Fin ((p) + (q))).succ = r :=
    Fin.ext (by simp [Fin.succ]; omega)
  rw [hcs, hsu] at hstep
  unfold isLeftStep at hR; rw [hcs, hsu] at hR
  rcases hstep with ⟨h1, _⟩ | ⟨_, h2⟩
  · omega
  · omega

/-- The underlying function for `swapDiagonalSteps`: agrees with `μ` everywhere
except at vertex `r`, where the step type is swapped.
- LR diagonal (left then right): `μ(r)` becomes `(μ(r).1 - 1, μ(r).2 + 1)`
- RL diagonal (right then left): `μ(r)` becomes `(μ(r).1 + 1, μ(r).2 - 1)` -/
def swapDiagonalStepsFun {p q : ℕ} (μ : Shuffle p q)
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r) :
    Index ((p ) + (q )) → Index (p) × Index (q) :=
  fun i =>
    if i = r then
      have ⟨h₁, h₂⟩ := isDiagonalVertex_bounds hr
      have hsum := coordSum_eq μ r
      if hL : isLeftStep μ ⟨r.val - 1, by omega⟩ then
        -- LR case: fst decrements, snd increments
        -- fst ≥ 1 (step r-1 incremented fst) so fst - 1 is valid
        have hfst_pos := diagonal_left_fst_pos hr hL
        -- snd < q+1 because step r is right (snd increments at r),
        -- so μ(r+1).2 > μ(r).2 and μ(r+1).2 ≤ q+1
        have hsnd_lt : (μ.1 r).2.val < q := by
          -- Step r is right (not left) in LR diagonal, so snd increments at r
          unfold isDiagonalVertex at hr; simp [h₁, h₂] at hr
          have hnotL : ¬isLeftStep μ ⟨r.val, h₂⟩ := by tauto
          have hstep := shuffle_step μ ⟨r.val, h₂⟩
          have hcs : (⟨r.val, h₂⟩ : Fin ((p) + (q))).castSucc = r :=
            Fin.ext (by simp [Fin.castSucc])
          rw [hcs] at hstep
          unfold isLeftStep at hnotL; rw [hcs] at hnotL
          have hsucc_snd := (μ.1 (⟨r.val, h₂⟩ : Fin ((p) + (q))).succ).2.isLt
          rcases hstep with ⟨h1, _⟩ | ⟨_, h2⟩
          · exfalso; exact hnotL (by omega)
          · omega
        (⟨(μ.1 r).1.val - 1, by omega⟩,
         ⟨(μ.1 r).2.val + 1, by omega⟩)
      else
        -- RL case: fst increments, snd decrements
        -- snd ≥ 1 (step r-1 incremented snd) so snd - 1 is valid
        have hsnd_pos := diagonal_right_snd_pos hr (by exact hL)
        -- fst < p+1 because step r is left (fst increments at r),
        -- so μ(r+1).1 > μ(r).1 and μ(r+1).1 ≤ p+1
        have hfst_lt : (μ.1 r).1.val < p := by
          -- Step r is left in RL diagonal, so fst increments at r
          unfold isDiagonalVertex at hr; simp [h₁, h₂] at hr
          have hisL : isLeftStep μ ⟨r.val, h₂⟩ := by tauto
          have hstep := shuffle_step μ ⟨r.val, h₂⟩
          have hcs : (⟨r.val, h₂⟩ : Fin ((p) + (q))).castSucc = r :=
            Fin.ext (by simp [Fin.castSucc])
          rw [hcs] at hstep
          unfold isLeftStep at hisL; rw [hcs] at hisL
          have hsucc_fst := (μ.1 (⟨r.val, h₂⟩ : Fin ((p) + (q))).succ).1.isLt
          rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩
          · omega
          · exfalso; exact absurd (by omega : (μ.1 r).1.val < _) (by omega)
        (⟨(μ.1 r).1.val + 1, by omega⟩,
         ⟨(μ.1 r).2.val - 1, by omega⟩)
    else
      μ.1 i

/-- `swapDiagonalStepsFun` preserves the coordinate sum: fst + snd = i for all i.
At `i ≠ r` this is `coordSum_eq μ`. At `i = r` the ±1 adjustments cancel. -/
private lemma swapDiagonalStepsFun_coordSum {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) (i : Index ((p) + (q))) :
    (swapDiagonalStepsFun μ r hr i).1.val +
      (swapDiagonalStepsFun μ r hr i).2.val = i.val := by
  have hsum := coordSum_eq μ i
  unfold swapDiagonalStepsFun
  split_ifs with hi
  · subst hi
    split
    dsimp only
    split_ifs with hL
    · have := diagonal_left_fst_pos hr hL
      dsimp only
      omega
    · have := diagonal_right_snd_pos hr hL
      dsimp only
      omega
  · exact hsum

/- `swapDiagonalStepsFun` is monotone in the product order. Only the pairs
`(r-1, r)` and `(r, r+1)` need checking — the two adjacent steps swap type
(LR↔RL) but both remain valid (one coordinate +1, the other unchanged). -/
section

private lemma swapDiagonalStepsFun_local_bounds {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    μ.1 ⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩ ≤ swapDiagonalStepsFun μ r hr r ∧
    swapDiagonalStepsFun μ r hr r ≤ μ.1 ⟨r.val + 1, by have := isDiagonalVertex_bounds hr;
                                                         omega⟩ := by
      -- By definition of swapDiagonalStepsFun, we need to consider the two cases for the diagonal
      -- vertex.
      by_cases hL : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩
      all_goals generalize_proofs at *;
      · -- By definition of swapDiagonalStepsFun, when isLeftStep is true, the function returns
        -- (μ(r-1).fst, μ(r-1).snd + 1).
        have h_swap : μ.swapDiagonalStepsFun r hr r = (⟨(μ.1 r).1.val - 1, by
          exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.1 ) ]
                                                                )⟩, ⟨(μ.1 r).2.val + 1, by
          simp +zetaDelta only [Order.lt_add_one_iff, tsub_le_iff_right, Fin.is_le',
              Order.add_one_le_iff] at *;
          unfold isDiagonalVertex at hr
          generalize_proofs at *;
          have hnotL : ¬isLeftStep μ ⟨r.val, by
            assumption⟩ := by
            grind +ring
          generalize_proofs at *;
          have hstep := shuffle_step μ ⟨r.val, by
            assumption⟩
          generalize_proofs at *;
          unfold isLeftStep at hnotL; simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;⟩) := by
          unfold LeanPool.EilenbergZilber.Shuffle.swapDiagonalStepsFun; aesop;
        generalize_proofs at *;
        -- By definition of swapDiagonalStepsFun, we know that μ(r) is equal to (μ(r-1).fst + 1,
        -- μ(r-1).snd).
        have h_mu_r : μ.1 r = (⟨(μ.1 ⟨r.val - 1, by
          omega⟩).1.val + 1, by
          exact Nat.lt_succ_of_le ( Nat.le_trans ( Nat.succ_le_of_lt hL ) ( Nat.le_of_lt_succ (
              by simp only [Fin.succ_mk,
            Nat.succ_eq_add_one, Fin.is_lt] ) ) ) ⟩,
            ⟨(μ.1 ⟨r.val - 1, by
          omega⟩).2.val, by
          grind⟩) := by
          all_goals generalize_proofs at *;
          have h_step : μ.1 (Fin.succ ⟨r.val - 1, by
            omega⟩) = (⟨(μ.1 ⟨r.val - 1, by
            omega⟩).1.val + 1, by
            omega⟩, ⟨(μ.1 ⟨r.val - 1, by
            omega⟩).2.val, by
            linarith⟩) := by
            have := shuffle_step μ ⟨r.val - 1, by
              omega⟩
            generalize_proofs at *;
            rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all +decide [ isLeftStep ] ; omega
          generalize_proofs at *;
          convert h_step using 1
          generalize_proofs at *; (
          congr! 1
          generalize_proofs at *; (
          exact Eq.symm ( Fin.ext <| Nat.succ_pred_eq_of_pos <| Nat.pos_of_ne_zero <|
              by rintro h; have := isDiagonalVertex_bounds hr; aesop )))
        generalize_proofs at *;
        have h_mu_r_next : μ.1 ⟨r.val + 1, by
          omega⟩ = (⟨(μ.1 r).1.val, by
          exact (μ.1 r).1.isLt⟩, ⟨(μ.1 r).2.val + 1, by
          omega⟩) := by
          have h_mu_r_next : ¬isLeftStep μ ⟨r.val, by
            exact Nat.lt_of_succ_lt_succ ‹_›⟩ := by
            unfold isDiagonalVertex at hr; simp +decide [ hL ] at hr; tauto;
          generalize_proofs at *;
          have := shuffle_step μ ⟨r.val, by
            linarith [ Fin.is_lt r ]⟩
          generalize_proofs at *;
          simp_all +decide only [isLeftStep, Fin.castSucc_mk, Fin.succ_mk, Fin.val_fin_lt, Fin.eta,
              add_tsub_cancel_right, not_lt];
          ext <;> simp_all +decide [ Fin.ext_iff, Prod.ext_iff ] <;> omega
        generalize_proofs at *;
        simp_all +decide [ Prod.le_def, Fin.le_def ];
      · -- Since μ(r-1) is a right step, we have (μ.1 r).2 = (μ.1 r-1).2 + 1.
        have h_right_step : (μ.1 r).2.val = (μ.1 ⟨r.val - 1, by
          omega⟩).2.val + 1 := by
          have h_right_step : (μ.1 ⟨r.val - 1, by
            omega⟩).1.val = (μ.1 r).1.val := by
            rcases r with ⟨ _ | r, hr ⟩ <;> norm_num at *;
            exact Classical.not_not.1 fun h => hL <| by exact lt_of_le_of_ne ( by exact μ.1.monotone
                                                                                   ( Nat.le_succ _ )
                                                                                   |> And.left
                                                                                   ) <| Ne.symm <|
                                                                                   by aesop;
          generalize_proofs at *;
          have := coordSum_eq μ ⟨r.val - 1, by
            omega⟩
          generalize_proofs at *;
          have := coordSum_eq μ r
          generalize_proofs at *;
          have := coordSum_eq μ ⟨r.val + 1, by
            linarith [ Fin.is_lt r ]⟩
          generalize_proofs at *;
          rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +arith +decide only [Fin.zero_eta, zero_tsub,
              Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
              add_zero, zero_add, zero_ne_one, add_tsub_cancel_right]
          · generalize_proofs at *
            unfold isDiagonalVertex at hr; simp_all +decide ;
          · linarith! [ shuffle_step μ ⟨ r, by linarith ⟩ ]
        generalize_proofs at *;
        have h_left_step : (μ.1 ⟨r.val + 1, by
          grind⟩).1.val = (μ.1 r).1.val + 1 := by
          have := shuffle_step μ ⟨ r.val, by
            linarith [ Fin.is_lt r ] ⟩
          generalize_proofs at *;
          unfold isDiagonalVertex at hr; simp_all +decide [ isLeftStep ] ; omega;
        generalize_proofs at *;
        -- By definition of `swapDiagonalStepsFun`, we need to consider the two cases for the
        -- diagonal vertex. Since `hL` is false, we have `¬isLeftStep μ ⟨r.val - 1, _⟩`.
        have h_swap : swapDiagonalStepsFun μ r hr r = (⟨(μ.1 r).1.val + 1, by
          grind⟩, ⟨(μ.1 r).2.val - 1, by
          grind⟩) := by
          -- By definition of swapDiagonalStepsFun, when i = r and hL is false, we have:
          simp [swapDiagonalStepsFun, hL]
        generalize_proofs at *;
        constructor <;> simp_all +decide only [add_tsub_cancel_right, Fin.eta, Prod.le_def,
            Std.le_refl, and_true];
        · exact Nat.le_succ_of_le ( μ.1.monotone ( Nat.pred_le _ ) |> And.left );
        · constructor
          · simp only [Fin.le_iff_val_le_val]; omega
          -- `by omega` alone fails: omega doesn't reduce `Fin.le` to `val ≤ val`,
          -- so we `simp [Fin.le_def]` first to expose the ℕ comparison.
          · exact μ.1.monotone (show _ ≤ _ by simp [Fin.le_def]; omega) |>.2

end

lemma swapDiagonalStepsFun_monotone {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    Monotone (swapDiagonalStepsFun μ r hr) := by
  -- Let's unfold the definition of `swapDiagonalStepsFun`.
  unfold swapDiagonalStepsFun;
  intro i j hij; by_cases hi : i = r <;> by_cases hj : j = r <;> simp +decide only [hi, hj,
      Std.le_refl, ↓reduceIte] at hij ⊢;
  · have h_swap_diag : swapDiagonalStepsFun μ r hr r ≤ μ.1 j := by
      have h_swap_diag : swapDiagonalStepsFun μ r hr r ≤ μ.1 ⟨r.val + 1, by
        grind⟩ := by
        exact swapDiagonalStepsFun_local_bounds μ r hr |>.2
      generalize_proofs at *;
      refine le_trans h_swap_diag ?_
      exact μ.1.monotone ( Nat.succ_le_of_lt ( hij.lt_of_ne' hj ) );
    unfold swapDiagonalStepsFun at h_swap_diag; simp_all +decide [ Fin.ext_iff ] ;
  · have := swapDiagonalStepsFun_local_bounds μ r hr;
    convert this.1.trans' _ using 1;
    · unfold LeanPool.EilenbergZilber.Shuffle.swapDiagonalStepsFun; aesop;
    · exact μ.1.monotone ( Nat.le_pred_of_lt ( hij.lt_of_ne hi ) );
  · exact μ.1.monotone hij

/-- `swapDiagonalStepsFun` is injective.  Follows from monotonicity +
coordinate-sum preservation (same argument as for `insertLeftStep`). -/
lemma swapDiagonalStepsFun_injective {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    Function.Injective (swapDiagonalStepsFun μ r hr) := by
  intros i j hij; have := swapDiagonalStepsFun_coordSum μ r hr i;
      have := swapDiagonalStepsFun_coordSum μ r hr j; aesop;


/-- The sign-reversing involution on diagonal terms.  Given a `(p+1, q+1)`-shuffle
`μ` and a diagonal vertex `r`, swap the steps adjacent to `r` (replacing an LR
corner with RL or vice versa).  This produces a new shuffle `μ'` such that:
- `μ' ∘ δ_r = μ ∘ δ_r` (same underlying map after vertex removal)
- `μ'.sign = -μ.sign` (opposite sign, from the inversion count change) -/
def swapDiagonalSteps {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r) :
    Shuffle (p) (q) :=
  ⟨⟨swapDiagonalStepsFun μ r hr, swapDiagonalStepsFun_monotone μ r hr⟩,
   swapDiagonalStepsFun_injective μ r hr⟩

/- The swap involution preserves the diagonal vertex property. -/
section

/-
For any index `i` different from the diagonal vertex `r`, the shuffle map `swapDiagonalSteps` has
the same value as the original shuffle `μ`. This follows directly from the definition of
`swapDiagonalStepsFun`, which uses an `if i = r` condition.
-/
lemma swapDiagonalSteps_apply_ne {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r)
    (i : Index (p + (q))) (hi : i ≠ r) :
    (swapDiagonalSteps μ r hr).1 i = μ.1 i := by
      -- Since $i \neq r$, the else part of the definition of `swapDiagonalStepsFun` applies.
      simp only [swapDiagonalSteps, OrderHom.coe_mk];
      unfold LeanPool.EilenbergZilber.Shuffle.swapDiagonalStepsFun; aesop;

/-
If the step entering the diagonal vertex `r` is a Left step, then `swapDiagonalSteps` modifies the
value at `r` by decrementing the first coordinate and incrementing the second. This corresponds to
the `then` branch of `swapDiagonalStepsFun`.
-/
lemma swapDiagonalSteps_apply_r_of_left {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r)
    (hL : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    (swapDiagonalSteps μ r hr).1 r =
      (⟨(μ.1 r).1.val - 1, by
        exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.1 ) ]
                                                              )⟩, ⟨(μ.1 r).2.val + 1, by
        -- Since the second component of `μ r` is in `Fin (q)`, its value is between 0 and q.
        have h_snd_range : (μ.1 r).2.val < q := by
          have h_snd_lt : (μ.1 r).2.val < q := by
            have h_not_left : ¬isLeftStep μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩ := by
              unfold isDiagonalVertex at hr; simp [hL] at hr; tauto;
            have h_step := shuffle_step μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩
            generalize_proofs at *;
            unfold isLeftStep at h_not_left; simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;
          generalize_proofs at *;
          exact h_snd_lt.trans_le ( Nat.le_refl _ ) |> lt_of_lt_of_le <| Nat.le_refl _;
        linarith [h_snd_range]⟩) := by
        exact ite_eq_left rfl |> fun h => h.trans ( by aesop )

/-
If the step entering the diagonal vertex `r` is a Right step (not
    Left), then `swapDiagonalSteps` modifies the value at `r`
    by incrementing the first coordinate and decrementing the second. This corresponds to the `else`
    branch of `swapDiagonalStepsFun`.
-/
lemma swapDiagonalSteps_apply_r_of_right {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r)
    (hR : ¬ isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    (swapDiagonalSteps μ r hr).1 r =
      (⟨(μ.1 r).1.val + 1, by
        -- By definition of `isDiagonalVertex`, we know that `isLeftStep μ ⟨r.val, h₂⟩` is false.
        unfold isDiagonalVertex at hr; simp_all +decide [];
        split_ifs at hr ; simp_all +decide [ isLeftStep ];
        grind⟩, ⟨(μ.1 r).2.val - 1, by
        exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.2 ) ]
                                                              )⟩) := by
        unfold LeanPool.EilenbergZilber.Shuffle.swapDiagonalSteps
        generalize_proofs at *;
        unfold LeanPool.EilenbergZilber.Shuffle.swapDiagonalStepsFun; aesop;

/-
The step entering the diagonal vertex `r` (index `r-1`) flips its type (Left ↔
    Right) under `swapDiagonalSteps`.
Proof sketch:
1. Let `i = r-1`. We compare `(μ'.1 i).1` and `(μ'.1 (i+1)).1`.
2. `μ'.1 i = μ.1 i` since `i ≠ r` (as `r > 0`).
3. `μ'.1 (i+1) = μ'.1 r`.
4. If `isLeftStep μ i` is true (Left step):
   - `(μ.1 i).1 + 1 = (μ.1 r).1`.
   - `(μ'.1 r).1 = (μ.1 r).1 - 1` (by `swapDiagonalSteps_apply_r_of_left`).
   - So `(μ'.1 r).1 = (μ.1 i).1`.
   - Thus `isLeftStep μ' i` is false.
5. If `isLeftStep μ i` is false (Right step):
   - `(μ.1 i).1 = (μ.1 r).1`.
   - `(μ'.1 r).1 = (μ.1 r).1 + 1` (by `swapDiagonalSteps_apply_r_of_right`).
   - So `(μ'.1 i).1 < (μ'.1 r).1`.
   - Thus `isLeftStep μ' i` is true.
-/
lemma swapDiagonalSteps_flip_prev {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r) :
    isLeftStep (swapDiagonalSteps μ r hr) ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2;
                                                          omega⟩ ↔
    ¬ isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by
      unfold isLeftStep
      generalize_proofs at *;
      by_cases hL : isLeftStep μ ⟨ r.val - 1, by have := ( isDiagonalVertex_bounds hr ).2; omega
                                                  ⟩ <;> simp_all +decide only [Fin.castSucc_mk,
                                                  Fin.succ_mk, Fin.val_fin_lt, not_lt];
      · rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +decide only [isLeftStep, zero_tsub,
            Fin.castSucc_mk, Fin.zero_eta, Fin.succ_mk, zero_add, Fin.val_fin_lt,
            add_tsub_cancel_right];
        · unfold isDiagonalVertex at hr
          simp at hr
        · rw [ swapDiagonalSteps_apply_r_of_left ] <;> norm_num [ hL ];
          · constructor <;> intro h <;> contrapose! h;
            · convert Nat.le_refl _ using 1;
              rotate_left;
              · exact ( μ.1 ⟨ r + 1, by linarith ⟩ |>.1 : ℕ ) - 1
              (generalize_proofs at *; (simp_all +decide only [add_tsub_cancel_right, Fin.le_def,
                  tsub_le_iff_right, Std.le_refl, iff_true] ) ;);
              rw [ swapDiagonalSteps_apply_ne ] <;> norm_num [ h ];
              have := shuffle_step μ ⟨ r, by linarith ⟩ ; aesop;
            · exact hL
          · exact hL;
      · rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +decide only [zero_tsub, Fin.zero_eta, zero_add,
            add_tsub_cancel_right];
        · unfold isDiagonalVertex at hr;
          grind +ring;
        · -- Since `hL` states that `isLeftStep μ ⟨r, by omega⟩` is false, we have `(μ.1 ⟨r, by
          -- omega⟩).1 = (μ.1 ⟨r + 1, by omega⟩).1`.
          have h_eq : (μ.1 ⟨r, by omega⟩).1 = (μ.1 ⟨r + 1, by omega⟩).1 := by
            -- Since `hL` states that `isLeftStep μ ⟨r, by omega⟩` is false, we have `(μ.1 ⟨r, by
            -- omega⟩).1 = (μ.1 ⟨r + 1, by omega⟩).1` by definition of `isLeftStep`.
            simp only [isLeftStep, Fin.castSucc_mk, Fin.succ_mk, Fin.val_fin_lt, not_lt] at hL ⊢
            generalize_proofs at *; (
            exact le_antisymm ( by simpa using μ.1.monotone ( show ⟨ r, by omega ⟩ ≤ ⟨ r + 1,
                                    by omega ⟩ from Nat.le_succ _ ) |> And.left ) hL)
          generalize_proofs at *; (
          rw [ swapDiagonalSteps_apply_ne, swapDiagonalSteps_apply_r_of_right
              ] <;> simp_all +decide only [add_tsub_cancel_right, Std.le_refl, iff_true, gt_iff_lt,
              not_false_eq_true, ne_eq, Fin.mk.injEq, Nat.left_eq_add];
          exact Nat.lt_succ_self _)

/-
The step leaving the diagonal vertex `r` (index `r`) flips its type (Left ↔
    Right) under `swapDiagonalSteps`.
Proof sketch:
1. Let `i = r`. We compare `isLeftStep μ' i` with `isLeftStep μ i`.
2. `μ'.1 (i+1) = μ.1 (i+1)` since `i+1 ≠ r`.
3. `μ'.1 i` is given by `swapDiagonalSteps_apply_r_of_left` or `_right`.
4. If `isLeftStep μ (r-1)` is true (Left incoming):
   - `μ` has Left at `r-1`. Since `r` is diagonal, `μ` must have Right at `r`.
   - So `isLeftStep μ r` is false.
   - We want to show `isLeftStep μ' r` is true.
   - `μ'.1 r = (μ.1 r).1 - 1`.
   - `μ.1 (r+1) = (μ.1 r).1` (since step `r` is Right).
   - So `(μ'.1 r).1 < (μ'.1 (r+1)).1` becomes `(μ.1 r).1 - 1 < (μ.1 r).1`, which is true.
5. If `isLeftStep μ (r-1)` is false (Right incoming):
   - `μ` has Right at `r-1`. Since `r` is diagonal, `μ` must have Left at `r`.
   - So `isLeftStep μ r` is true.
   - We want to show `isLeftStep μ' r` is false.
   - `μ'.1 r = (μ.1 r).1 + 1`.
   - `μ.1 (r+1) = (μ.1 r).1 + 1` (since step `r` is Left).
   - So `(μ'.1 r).1 < (μ'.1 (r+1)).1` becomes `(μ.1 r).1 + 1 < (μ.1 r).1 + 1`, which is false.
-/
lemma swapDiagonalSteps_flip_curr {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r) :
    isLeftStep (swapDiagonalSteps μ r hr) ⟨r.val, by have := (isDiagonalVertex_bounds hr).2;
                                                      omega⟩ ↔
    ¬ isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by
      unfold LeanPool.EilenbergZilber.Shuffle.isLeftStep
      generalize_proofs at *;
      by_cases h : isLeftStep μ ⟨r.val - 1, by
        exact lt_of_le_of_lt ( Nat.pred_le _ ) ‹_›⟩
      all_goals generalize_proofs at *;
      · have h_step : (μ.1 (Fin.succ ⟨r.val, by
          assumption⟩)).1.val = (μ.1 ⟨r.val, by
          grind⟩).1.val := by
          have := shuffle_step μ ⟨r.val, by
            assumption⟩
          generalize_proofs at *;
          unfold isDiagonalVertex at hr; simp_all +decide [] ;
          unfold Shuffle.isLeftStep at hr; simp_all +decide [] ;
          grind
        generalize_proofs at *;
        have := swapDiagonalSteps_apply_r_of_left μ r hr h; simp_all +decide only [Fin.succ,
            Fin.eta, Fin.castSucc, Fin.castAdd_mk, lt_self_iff_false, not_false_eq_true, iff_true,
            gt_iff_lt] ;
        convert Nat.sub_lt ( diagonal_left_fst_pos hr h ) zero_lt_one using 1
        generalize_proofs at *;
        convert h_step using 1
        generalize_proofs at *; (
        exact congr_arg Fin.val ( swapDiagonalSteps_apply_ne μ r hr ⟨ r.val + 1,
            by omega ⟩ ( by simp +decide [ Fin.ext_iff ] ) |> congr_arg Prod.fst
            ) |> Eq.trans <| rfl);
      · simp_all +decide only [Fin.castSucc, Fin.castAdd_mk, Fin.eta, Fin.succ, Fin.val_fin_lt,
            not_lt];
        rw [ show ( μ.swapDiagonalSteps r hr : LeanPool.EilenbergZilber.Index ( p + ( q ) ) →o
            LeanPool.EilenbergZilber.Index ( p ) × LeanPool.EilenbergZilber.Index ( q ) ) r =
            ( ⟨ ( μ.1 r ).1.val + 1, by
              unfold LeanPool.EilenbergZilber.Shuffle.isDiagonalVertex at hr; simp_all +decide [] ;
              have := μ.1 r |>.1.isLt; have := μ.1 r |>.2.isLt;
                  simp_all +arith +decide [ LeanPool.EilenbergZilber.Shuffle.isLeftStep ] ;
              grind ⟩, ⟨ ( μ.1 r ).2.val - 1, by
              exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.2
                                                                    ) ] ) ⟩ ) from ?_ ]
        all_goals generalize_proofs at *;
        · rw [ show ( μ.swapDiagonalSteps r hr : LeanPool.EilenbergZilber.Index ( p + ( q ) ) →o
              LeanPool.EilenbergZilber.Index ( p ) × LeanPool.EilenbergZilber.Index ( q ) ) ⟨ r.val
              + 1, by linarith ⟩ = μ.1 ⟨ r.val + 1, by linarith ⟩ from ?_ ];
          · rw [ Fin.lt_def, Fin.le_iff_val_le_val ] ; simp +arith +decide only [Fin.val_fin_le];
            constructor <;> intro <;> simp_all +decide only [Order.lt_add_one_iff,
                Order.add_one_le_iff, tsub_le_iff_right, Fin.is_le', Nat.succ_le_iff];
            · unfold isDiagonalVertex at hr; simp_all +decide [] ;
              exact le_of_not_gt fun h => h.not_ge <| by have := shuffle_step μ ⟨ r,
                                                          by linarith ⟩ ; unfold isLeftStep at hr;
                                                          aesop;
            · unfold isDiagonalVertex at hr; simp_all +decide only [Fin.val_pos_iff, ↓reduceDIte,
                  false_and, not_false_eq_true, true_and, false_or, dite_eq_ite, ite_false_right] ;
              exact absurd ‹_› ( not_le_of_gt hr.2 );
          · exact swapDiagonalSteps_apply_ne _ _ _ _ ( ne_of_gt ( Nat.lt_succ_self _ ) );
        · exact swapDiagonalSteps_apply_r_of_right μ r hr h

end

lemma swapDiagonalSteps_vertex {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    isDiagonalVertex (swapDiagonalSteps μ r hr) r := by
  unfold isDiagonalVertex at *; simp_all +decide only [Fin.val_pos_iff, isLeftStep, Fin.castSucc_mk,
      Fin.succ_mk, Fin.val_fin_lt, Fin.eta, not_lt, dite_false_right] ;
  split_ifs at hr ; simp_all +decide only [isLeftStep, Fin.castSucc_mk, Fin.succ_mk, Fin.val_fin_lt,
      Fin.eta, not_lt, exists_true_left] ;
  -- Apply the lemmas swapDiagonalSteps_flip_prev and swapDiagonalSteps_flip_curr to show that the
  -- step types are different.
  have h_diff : ¬isLeftStep (swapDiagonalSteps μ r ‹_›) ⟨r.val - 1,
      by have := (isDiagonalVertex_bounds ‹_›).2; omega⟩ ∧ isLeftStep (swapDiagonalSteps μ r
      ‹_›) ⟨r.val, by have := (isDiagonalVertex_bounds ‹_›).2;
                       omega⟩ ∨ isLeftStep (swapDiagonalSteps μ r ‹_›) ⟨r.val - 1,
                       by have := (isDiagonalVertex_bounds ‹_›).2;
                           omega⟩ ∧ ¬isLeftStep (swapDiagonalSteps μ r ‹_›) ⟨r.val,
                           by have := (isDiagonalVertex_bounds ‹_›).2; omega⟩ := by
    have := swapDiagonalSteps_flip_prev μ r ‹_›; have := swapDiagonalSteps_flip_curr μ r ‹_›;
        simp_all +decide [ isLeftStep ] ;
  generalize_proofs at *; (
  cases h_diff <;> simp_all +decide [ isLeftStep ])


/- The swap is an involution. -/
section

/-
The `swapDiagonalSteps` map agrees with the original shuffle at all indices other than `r`.
-/
lemma swapDiagonalSteps_apply_ne_r {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) (i : Index (p + (q))) (h : i ≠ r) :
    (swapDiagonalSteps μ r hr).1 i = μ.1 i := by
      unfold LeanPool.EilenbergZilber.Shuffle.swapDiagonalSteps;
      unfold LeanPool.EilenbergZilber.Shuffle.swapDiagonalStepsFun; aesop;

/-
The value of the swapped shuffle at the diagonal vertex `r` is given
    by decrementing/incrementing coordinates based on the step type.
-/
lemma swapDiagonalSteps_val_r {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r)
    (rm1 : Fin ((p) + (q)))
    (h_rm1 : rm1.val = r.val - 1) :
    (swapDiagonalSteps μ r hr).1 r =
      if h : isLeftStep μ rm1 then
        (⟨(μ.1 r).1.val - 1, by
          grind⟩, ⟨(μ.1 r).2.val + 1, by
          have h_snd_lt : ¬isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2;
                                                    omega⟩ := by
            have h_snd_lt : ¬isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2;
                                                      omega⟩ := by
              have := hr
              unfold isDiagonalVertex at this
              have h_snd_lt : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2;
                                                           omega⟩ := by
                convert h using 1
                generalize_proofs at *; (
                exact Fin.ext ( by aesop ) ;)
              generalize_proofs at *; (
              split_ifs at this ; tauto;)
            (generalize_proofs at *; (
            exact h_snd_lt))
          generalize_proofs at *; (
          have hstep := shuffle_step μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩
          generalize_proofs at *; (
          unfold isLeftStep at h_snd_lt; simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;))⟩)
      else
        (⟨(μ.1 r).1.val + 1, by
          convert Nat.lt_succ_of_le ( Fin.is_le _ ) using 1;
          on_goal 1 => convert rfl
          convert Fin.val_cast_of_lt _;
          · infer_instance;
          · contrapose! h;
            unfold isDiagonalVertex at hr; simp_all +decide only [Fin.val_pos_iff, isLeftStep,
                Fin.castSucc_mk, Fin.succ_mk, Fin.val_fin_lt, Fin.eta, not_lt, dite_false_right,
                add_le_add_iff_right] ;
            rw [ show rm1.castSucc = ⟨ r.val - 1, by omega ⟩ from ?_, show rm1.succ = r from ?_ ];
            · grind;
            · exact Fin.ext ( by simp +decide [ h_rm1, Nat.sub_add_cancel ( show 1 ≤ ( r : ℕ ) from
                                  Nat.pos_of_ne_zero ( by aesop_cat ) ) ] );
            · exact Fin.ext h_rm1⟩, ⟨(μ.1 r).2.val - 1, by
          exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.2 ) ]
                                                                )⟩) := by
          -- By definition of swapDiagonalSteps, applying it twice returns the original shuffle.
          simp only [swapDiagonalSteps, OrderHom.coe_mk, swapDiagonalStepsFun, ↓reduceIte] at *; (
          have h_if_eq : (isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2;
                                                       omega⟩) = (isLeftStep μ rm1) := by
            exact congr_arg _ ( Fin.ext <| by simp +decide [ h_rm1 ] )
          generalize_proofs at *; (
          split_ifs <;> aesop ( simp_config := { singlePass := true } ) ;))

/-
The `swapDiagonalSteps` involution toggles the type (Left/Right) of the step immediately preceding
the diagonal vertex `r`.
-/
lemma swapDiagonalSteps_isLeftStep_toggle {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    let rm1 : Fin ((p) + (q)) := ⟨r.val - 1, by
      unfold isDiagonalVertex at hr
      split_ifs at hr
      omega⟩
    isLeftStep (swapDiagonalSteps μ r hr) rm1 ↔ ¬ isLeftStep μ rm1 := by
      have hrlt: r.val - 1 < p + q := by have := isDiagonalVertex_bounds hr; omega
      have hswap := swapDiagonalSteps_val_r μ r hr ⟨r.val - 1, by exact hrlt⟩ rfl
      generalize_proofs at *;
      split_ifs at hswap <;> simp_all +decide only [isLeftStep, Fin.castSucc_mk, Fin.succ_mk,
          Fin.val_fin_lt, not_lt, Order.lt_add_one_iff, Order.add_one_le_iff, tsub_le_iff_right,
          Fin.is_le'];
      · convert iff_of_false ?_ ?_ using 1
        all_goals generalize_proofs at *;
        · rw [ swapDiagonalSteps_apply_ne_r ] <;> norm_num [ * ];
          · rcases r with ⟨ _ | r, hr ⟩ <;> norm_num at *;
            · simp_all +decide [ Shuffle.apply_zero ];
            · simp_all +decide only [forall_const];
              exact Nat.sub_le_of_le_add <| by linarith! [ show ( μ.1 ⟨ r + 1,
                                                by linarith ⟩ |>.1 : ℕ ) ≤ ( μ.1 ⟨ r,
                                                by linarith ⟩ |>.1 : ℕ ) + 1 from by
                                                            have := shuffle_step μ ⟨ r,
                                                                by linarith ⟩ ; aesop; ] ;
          · exact ne_of_lt ( Nat.pred_lt ( ne_bot_of_gt ( isDiagonalVertex_bounds hr |>.1 ) ) );
        · cases r ; aesop
      · rw [ swapDiagonalSteps_apply_ne_r μ r hr ⟨ r.val - 1, by omega ⟩ ( by
          rcases r with ⟨ _ | r, hr ⟩ <;> norm_num at *;
          unfold Shuffle.isDiagonalVertex at hr ; aesop ( simp_config := { decide := true } ) ; ) ]
        generalize_proofs at *;
        rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +decide only [zero_tsub, Fin.zero_eta,
            Order.lt_add_one_iff, Order.add_one_le_iff, zero_add, not_false_eq_true, forall_const,
            add_tsub_cancel_right, implies_true];
        · exact absurd (isDiagonalVertex_bounds hr).1 (lt_irrefl _)
        · unfold Shuffle.isLeftStep at * ; simp_all +decide only [Fin.castSucc_mk, Fin.succ_mk,
              Fin.val_fin_lt, not_lt, isEmpty_Prop, IsEmpty.forall_iff, iff_true, gt_iff_lt];
          exact Nat.lt_succ_of_le ( by exact le_trans ( by aesop ) ( μ.1.monotone ( Nat.le_succ _ )
                                        |>.1 ) )

end

lemma swapDiagonalSteps_involutive {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    swapDiagonalSteps (swapDiagonalSteps μ r hr) r
      (swapDiagonalSteps_vertex μ r hr) = μ := by
  refine ExistsUnique.unique (p := fun x => x.1 = μ.1) ?_ ?_ ?_
  · use μ; aesop;
  · -- By definition of swapDiagonalSteps, we know that applying it twice returns the original
    -- shuffle.
    have h_swap : ∀ i : Index ((p) + (q)), (swapDiagonalSteps (swapDiagonalSteps μ r hr) r
        (swapDiagonalSteps_vertex μ r hr)).1 i = μ.1 i := by
      intro i; by_cases hi : i = r <;> simp +decide only [hi, ne_eq, not_false_eq_true,
          swapDiagonalSteps_apply_ne_r] ;
      let rm1 : Fin ((p) + (q)) := ⟨r.val - 1, by
        have := isDiagonalVertex_bounds hr
        omega⟩
      have h₁ := swapDiagonalSteps_val_r μ r hr rm1 rfl
      have h₂ := swapDiagonalSteps_val_r (swapDiagonalSteps μ r hr) r (swapDiagonalSteps_vertex μ r
          hr) rm1 rfl
      have htoggle : isLeftStep (swapDiagonalSteps μ r hr) rm1 ↔ ¬ isLeftStep μ rm1 := by
        simpa [rm1] using swapDiagonalSteps_isLeftStep_toggle μ r hr
      by_cases hL : isLeftStep μ rm1
      · have hS : ¬ isLeftStep (swapDiagonalSteps μ r hr) rm1 := by
          exact fun hs => (htoggle.mp hs) hL
        rw [h₂]
        simp only [hS, ↓reduceDIte, h₁, hL, add_tsub_cancel_right, Fin.eta, rm1]
        exact Prod.ext (Fin.ext <| Nat.sub_add_cancel <| Nat.pos_of_ne_zero <| by
          have := diagonal_left_fst_pos hr (by simpa [rm1] using hL)
          aesop) rfl
      · have hS : isLeftStep (swapDiagonalSteps μ r hr) rm1 := by
          exact htoggle.mpr hL
        rw [h₂]
        simp only [hS, ↓reduceDIte, h₁, hL, add_tsub_cancel_right, Fin.eta, rm1]
        exact Prod.ext rfl (Fin.ext <| Nat.sub_add_cancel <| Nat.pos_of_ne_zero <| by
          have := diagonal_right_snd_pos hr (by simpa [rm1] using hL)
          aesop)
    aesop;
  · rfl


/-- The sum `invCount(μ') + invCount(μ)` is odd, where `μ' = swapDiagonalSteps μ r hr`.

Proof sketch: rewrite both invCounts via `invCount_eq_sum_mul_diff` as sums over
`Fin ((p+1)+(q+1))`.  The swap only changes `μ.1` at position `r`, so the only
affected summands are at `s = ⟨r.val - 1, _⟩` (where `Fin.succ s = r`) and
`s = ⟨r.val, _⟩` (where `Fin.castSucc s = r`).  All other summands are equal
for `μ` and `μ'`, so they contribute an even amount to the combined sum.

For the two affected summands, set `y := (μ.1 ⟨r-1⟩).2.val`.  In the LR case
(step `r-1` is Left): the four terms are `y, 0, 0, y+1`, summing to `2y+1`.
In the RL case (step `r-1` is Right): the four terms are `0, y, y+1, 0`,
also summing to `2y+1`.  Hence the total is even + odd = odd. -/
private lemma swapDiagonalSteps_invCount_sum_odd {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    Odd ((swapDiagonalSteps μ r hr).invCount + μ.invCount) := by
  rw [Shuffle.invCount_eq_sum_mul_diff, Shuffle.invCount_eq_sum_mul_diff,
    ← Finset.sum_add_distrib]
  let rm1 : Fin ((p) + (q)) := ⟨r.val - 1, by
    have := isDiagonalVertex_bounds hr; omega⟩
  let r' : Fin ((p) + (q)) := ⟨r.val, by
    have := isDiagonalVertex_bounds hr; omega⟩
  have hne : rm1 ≠ r' := by
    simp only [rm1, r', ne_eq, Fin.mk.injEq]
    have := isDiagonalVertex_bounds hr; omega
  rw [← Finset.sum_sdiff (s₁ := {rm1, r'}) (Finset.subset_univ _),
      Finset.sum_pair hne]
  have h_eq : ∀ x ∈ Finset.univ \ ({rm1, r'} : Finset _),
      ((μ.swapDiagonalSteps r hr).1 x.castSucc).2.val *
          (((μ.swapDiagonalSteps r hr).1 x.succ).1.val -
            ((μ.swapDiagonalSteps r hr).1 x.castSucc).1.val) +
        (μ.1 x.castSucc).2.val * ((μ.1 x.succ).1.val - (μ.1 x.castSucc).1.val) =
      2 * ((μ.1 x.castSucc).2.val * ((μ.1 x.succ).1.val - (μ.1 x.castSucc).1.val)) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or] at hx
    rw [swapDiagonalSteps_apply_ne μ r hr x.castSucc (by
          intro h; exact absurd (Fin.ext (show x.val = r'.val by
            have := congr_arg Fin.val h
            simpa using this) : x = r') hx.2),
        swapDiagonalSteps_apply_ne μ r hr x.succ (by
          intro h; exact absurd (Fin.ext (show x.val = rm1.val by
            have := congr_arg Fin.val h
            simp only [Fin.val_succ] at this
            change x.val = r.val - 1; omega) : x = rm1) hx.1)]
    ring
  rw [Finset.sum_congr rfl h_eq, ← Finset.mul_sum]
  apply Even.add_odd (even_two_mul _)
  rw [swapDiagonalSteps_apply_ne μ r hr rm1.castSucc (by
        simp only [rm1, ne_eq, Fin.ext_iff, Fin.val_castSucc]
        have := isDiagonalVertex_bounds hr; omega),
      swapDiagonalSteps_apply_ne μ r hr r'.succ (by
        simp only [r', ne_eq, Fin.ext_iff, Fin.val_succ]
        omega)]
  by_cases hL : isLeftStep μ ⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩
  · have hrm1_succ : rm1.succ = r := Fin.ext (by simp [rm1]; have := isDiagonalVertex_bounds hr;
                                                  omega)
    have hr'_castSucc : r'.castSucc = r := Fin.ext (by simp [r'])
    rw [hrm1_succ, hr'_castSucc, swapDiagonalSteps_apply_r_of_left μ r hr hL]
    have hstep_rm1 := shuffle_step μ ⟨r.val - 1, by
      have := isDiagonalVertex_bounds hr; omega⟩
    have hcs_rm1 : (⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).castSucc = rm1.castSucc := by
      ext; simp [rm1]
    have hsucc_rm1 : (⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).succ = r := by
      ext; simp; have := isDiagonalVertex_bounds hr; omega
    rw [hcs_rm1, hsucc_rm1] at hstep_rm1
    have hfst : (μ.1 rm1.castSucc).1.val + 1 = (μ.1 r).1.val := by
      rcases hstep_rm1 with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h1
      · exfalso; unfold isLeftStep at hL; rw [hcs_rm1, hsucc_rm1] at hL; omega
    have hsnd : (μ.1 rm1.castSucc).2.val = (μ.1 r).2.val := by
      rcases hstep_rm1 with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exfalso; unfold isLeftStep at hL; rw [hcs_rm1, hsucc_rm1] at hL; omega
    -- Step r is Right (diagonal: r-1 is Left, r is Right), so fst doesn't change
    have hstep_r := shuffle_step μ ⟨r.val, by
      have := isDiagonalVertex_bounds hr; omega⟩
    have hcs_r : (⟨r.val, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).castSucc = r := Fin.ext (by simp)
    have hsucc_r : (⟨r.val, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).succ = r'.succ := Fin.ext (by simp [r'])
    rw [hcs_r, hsucc_r] at hstep_r
    have hnotL_r : ¬isLeftStep μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩ := by
      unfold isDiagonalVertex at hr
      simp [(isDiagonalVertex_bounds hr).1, (isDiagonalVertex_bounds hr).2] at hr
      tauto
    have hfst_r : (μ.1 r'.succ).1.val = (μ.1 r).1.val := by
      rcases hstep_r with ⟨h1, _⟩ | ⟨h1, _⟩
      · exfalso; unfold isLeftStep at hnotL_r; rw [hcs_r, hsucc_r] at hnotL_r
        exact hnotL_r (by omega)
      · omega
    simp only at *
    -- Substitute: fst diff at rm1 is 0 and 1; fst diff at r' is 1 and 0
    have h1 : (μ.1 r).1.val - 1 - (μ.1 rm1.castSucc).1.val = 0 := by omega
    have h2 : (μ.1 r).1.val - (μ.1 rm1.castSucc).1.val = 1 := by omega
    have h3 : (μ.1 r'.succ).1.val - ((μ.1 r).1.val - 1) = 1 := by
      have := diagonal_left_fst_pos hr hL; omega
    have h4 : (μ.1 r'.succ).1.val - (μ.1 r).1.val = 0 := by omega
    rw [h1, h2, h3, h4]
    simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
    rw [← hsnd]
    exact ⟨(μ.1 rm1.castSucc).2.val, by omega⟩
  · have hrm1_succ : rm1.succ = r := Fin.ext (by
      simp [rm1]; have := isDiagonalVertex_bounds hr; omega)
    have hr'_castSucc : r'.castSucc = r := Fin.ext (by simp [r'])
    rw [hrm1_succ, hr'_castSucc, swapDiagonalSteps_apply_r_of_right μ r hr hL]
    have hstep_rm1 := shuffle_step μ ⟨r.val - 1, by
      have := isDiagonalVertex_bounds hr; omega⟩
    have hcs_rm1 : (⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).castSucc = rm1.castSucc := by
      ext; simp [rm1]
    have hsucc_rm1 : (⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).succ = r := by
      ext; simp; have := isDiagonalVertex_bounds hr; omega
    rw [hcs_rm1, hsucc_rm1] at hstep_rm1
    have hfst : (μ.1 rm1.castSucc).1.val = (μ.1 r).1.val := by
      rcases hstep_rm1 with ⟨h1, _⟩ | ⟨h1, _⟩
      · exfalso; unfold isLeftStep at hL; rw [hcs_rm1, hsucc_rm1] at hL
        exact hL (by omega)
      · exact h1
    have hsnd : (μ.1 rm1.castSucc).2.val + 1 = (μ.1 r).2.val := by
      rcases hstep_rm1 with ⟨h1, _⟩ | ⟨_, h2⟩
      · exfalso; unfold isLeftStep at hL; rw [hcs_rm1, hsucc_rm1] at hL
        exact hL (by omega)
      · exact h2
    have hstep_r := shuffle_step μ ⟨r.val, by
      have := isDiagonalVertex_bounds hr; omega⟩
    have hcs_r : (⟨r.val, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).castSucc = r := Fin.ext (by simp)
    have hsucc_r : (⟨r.val, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).succ = r'.succ := Fin.ext (by simp [r'])
    rw [hcs_r, hsucc_r] at hstep_r
    have hisL_r : isLeftStep μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩ := by
      unfold isDiagonalVertex at hr
      grind
    have hfst_r : (μ.1 r'.succ).1.val = (μ.1 r).1.val + 1 := by
      rcases hstep_r with ⟨h1, _⟩ | ⟨h1, _⟩
      · omega
      · unfold isLeftStep at hisL_r; rw [hcs_r, hsucc_r] at hisL_r; omega
    grind


/-- The swap negates the signed coefficient.

Derives from `swapDiagonalSteps_invCount_sum_odd`: since the invCount sum is
odd, `(-1)^invCount' * (-1)^invCount = -1`, and multiplying both sides by
`(-1)^invCount` (which squares to 1) gives `(-1)^invCount' = -(-1)^invCount`. -/
@[grind =]
lemma swapDiagonalSteps_neg_sign {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    (swapDiagonalSteps μ r hr).sign  =
    -(μ.sign) := by
  unfold sign
  have key : (-1 : ℤ) ^ (swapDiagonalSteps μ r hr).invCount *
      (-1 : ℤ) ^ μ.invCount = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow (swapDiagonalSteps_invCount_sum_odd μ r hr)
  have sq : (-1 : ℤ) ^ μ.invCount * (-1 : ℤ) ^ μ.invCount = 1 := by
    rw [← mul_pow]; norm_num
  grind

/-- The swap involution is never the identity: swapping two steps of different
type always produces a distinct shuffle. -/
lemma swapDiagonalSteps_ne {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    swapDiagonalSteps μ r hr ≠ μ := by
  apply mt (congrArg Shuffle.sign)
  grind [Int.neg_one_pow_ne_zero, Shuffle.sign]


end Shuffle

instance uniqueShuffleNZero {n : ℕ} : Unique (Shuffle n 0) where
  default := ⟨⟨fun i => (i, 0), fun i j h => ⟨h, by simp⟩⟩, fun i j h => congrArg Prod.fst h⟩
  uniq := fun ⟨⟨f, hf⟩, hinj⟩ => by
    apply Subtype.ext
    apply OrderHom.ext
    funext i
    ext
    · have hmono : StrictMono (fun i => (f i).1) := by
        intro a b hab
        have h_le := hf hab.le
        have h_neq : f a ≠ f b := fun h => hab.ne (hinj h)
        have h_le_1 : (f a).1 ≤ (f b).1 := h_le.1
        cases eq_or_lt_of_le h_le_1 with
        | inl heq =>
          exfalso
          apply h_neq
          ext
          · exact congrArg Fin.val heq
          · simp
        | inr hlt => exact hlt
      have heq : ∀ i, (f i).1 = i := by
        intro i
        exact le_antisymm (StrictMono.le_id hmono i) (StrictMono.id_le hmono i)
      exact congrArg Fin.val (heq i)
    · simp

attribute [grind =] OrderHom.coe_mk


instance uniqueShuffleZeroN {n : ℕ} : Unique (Shuffle 0 n) where
  default := ⟨⟨fun i => (0, i.cast (by omega)),
    fun i j h => ⟨by simp, by simpa using h⟩⟩,
    fun i j h => Fin.cast_injective (by omega) (congrArg Prod.snd h)⟩
  uniq := fun ⟨⟨f, hf⟩, hinj⟩ => by
    apply Subtype.ext; apply OrderHom.ext; funext i
    have hmono : StrictMono (fun i => (f i).2) := by
      intro a b hab
      have h_neq : f a ≠ f b := fun h => hab.ne (hinj h)
      cases eq_or_lt_of_le (hf hab.le).2 with
      | inl heq =>
        exact absurd (Prod.ext (by simp [Fin.eq_zero])
          (Fin.ext (congrArg Fin.val heq))) h_neq
      | inr hlt => exact hlt
    let g : Fin (n + 1) → Fin (n + 1) := fun j => (f (j.cast (by omega))).2
    have hg : StrictMono g := fun a b h =>
      -- grind
      hmono (show a.cast _ < b.cast _ by exact_mod_cast h)
    have hg_eq : ∀ j, g j = j :=
      fun j => le_antisymm (StrictMono.le_id hg j) (StrictMono.id_le hg j)
    apply Prod.ext (Fin.eq_zero _)
    simp only [OrderHom.coe_mk, Fin.isValue]
    grind
    -- grind only [= Fin.val_cast, = Lean.Grind.toInt_fin, = OrderHom.coe_mk]
    -- exact Prod.ext (Fin.eq_zero _) h2

/-- The unique `(n,0)`-shuffle has sign `1`. -/
lemma Shuffle.sign_default_zero_right {n : ℕ} : (default : Shuffle n 0).sign = 1 := by
  simp [Shuffle.sign, Shuffle.invCount]

/-- The unique `(0,n)`-shuffle has sign `1`. -/
lemma Shuffle.sign_default_zero_left {n : ℕ} : (default : Shuffle 0 n).sign = 1 := by
  have h := sign_eq_negOnePow_mul_swap_sign (u := (default : Shuffle 0 n))
  have hswap : (default : Shuffle 0 n).swap = (default : Shuffle n 0) := by
    exact Subsingleton.elim _ _
  rw [Nat.zero_mul, pow_zero, one_mul, hswap, Shuffle.sign_default_zero_right] at h
  exact h

end LeanPool.EilenbergZilber
