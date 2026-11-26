/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Dense
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Folding.Transfer
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Interior.Fill
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Border.Price
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Bounds
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Sums.Model
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Dual
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Strict
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagWords
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagGrowth
public import Mathlib.Analysis.Convex.StdSimplex

/-! # Quadratic nonrigidity of decoder powers -/

universe u

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Interior
open Filter Prices.Motion

variable {F : Type} [Field F] {q : ℕ} {K l : ℝ}

theorem pack (h : Folding.Folds K) (hK : 1 ≤ K) (hl : 1 ≤ l) (hq : (q : ℝ) = l * l) :
    ∀ᶠ d : ℕ in atTop, ∀ M : Matrix (Fin d) (Fin d) F,
      Packed (matPower (fun _ : Fin q => matPower (fun _ : Fin (2 ^ q) => M)))
        (((d : ℝ) ^ (2 ^ q : ℕ)) ^ ((q : ℝ) - 1 / 2)) (((d : ℝ) ^ (2 ^ q : ℕ)) ^ (4 * (K + 4) * l))
          := by
  let C := K + 4
  have hC : 1 ≤ C := by unfold C; linarith
  have hq' : 0 < (q : ℝ) := by rw [hq]; positivity
  have ht : (q : ℝ) ≤ (2 : ℝ) ^ q := by
    exact_mod_cast (Nat.lt_pow_self (by decide : 1 < 2) (n := q)).le
  have hs (i : Fin q) := h.grid (F := F) hK q (r := (i.val + 1 : ℕ) / (q : ℝ)) (by positivity)
    ((div_le_one hq').mpr (by exact_mod_cast i.isLt)) (by
      rw [div_mul_eq_mul_div, le_div_iff₀ hq', one_mul]
      exact ht.trans (le_mul_of_one_le_left (by positivity) (by exact_mod_cast Nat.succ_pos i.val)))
  have hg := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, eventually_all.mpr hs,
    hg.eventually_ge_atTop ((2 * ((q : ℝ) + 1)) ^ q)] with d hd hn hn' M
  let n := 2 ^ q
  let D := (d : ℝ) ^ n
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hD : 1 ≤ D := one_le_pow₀ hd'
  have hfactor : (2 * ((q : ℝ) + 1)) ^ q ≤ D ^ (1 / 2 : ℝ) := by
    have hpos : n ≠ 0 := by
      unfold n
      positivity
    exact hn'.trans (Real.rpow_le_rpow (by positivity) (le_self_pow₀ hd' hpos) (by norm_num))
  have H := collect (M := matPower (fun _ : Fin n => M))
    hD (by simp [D]) hl hq hC (fun j hj hj' => by
      simpa only [Nat.sub_add_cancel hj] using hn ⟨j - 1, by omega⟩ M)
  have hh {a b : ℝ} (hab : 1 / 2 + a ≤ b) : (2 * ((q : ℝ) + 1)) ^ q * D ^ a ≤ D ^ b := by
    apply le_trans (mul_le_mul_of_nonneg_right hfactor (by positivity))
    change D ^ (1 / 2 : ℝ) * D ^ a ≤ D ^ b
    rw [← Real.rpow_add (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hD hab
  obtain ⟨A, B, he, ha, hb⟩ := H
  have hp : (2 * ((q : ℝ) + 1)) ^ q * D ^ (3 * C * l) ≤ D ^ (4 * C * l) := hh (by nlinarith)
  exact ⟨A, B, he, ha.mono hp, hb.mono (hh (by linarith)) hp⟩

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Interior
end

section
/-
# A thin product with one private multiplication per output

The seed is integral, with the auxiliary field used only to index
zero-one coefficients. The number of independent products is a
square, so the whole batch tiles one larger output with no padding.
-/

namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Interior

private theorem tile_seed {F : Type*} [Field F] {G A H E C : Type}
    [Fintype G] [Fintype A] [Fintype H] [Fintype E] [Fintype C]
    (S : Seed F G A H E C) {b a g n : ℕ}
    (hg : Fintype.card G = g * g) (ha : Fintype.card A = a)
    (hb : 0 < b) (hn : 0 < n)
    (hgap : 2 ^ b * Fintype.card G * Fintype.card H * 2 < Fintype.card H ^ b)
    (herr : 2 ^ (b + 1) * Fintype.card E ≤ Fintype.card (Out G A)) :
    let q := (g * a) ^ b
    ∃ r, 2 ^ n * r ≤ q ^ n * q ^ n ∧ PrivateProducts F (q ^ n) (q ^ n) (2 ^ n) r := by
  classical
  intro q
  obtain ⟨r, hsize, hpriv⟩ := S.amplify hb hgap herr hn
  let m := b * n
  have he : q ^ n = g ^ m * a ^ m := by unfold q m; rw [← pow_mul, mul_pow]
  have hG : Fintype.card (Pos (g ^ m) (g ^ m)) = Fintype.card (Fin (b * n) → G) := by
    simp [Pos, hg, m, mul_pow]
  have hA : Fintype.card (Fin (a ^ m)) = Fintype.card (Fin (b * n) → A) := by simp [ha, m]
  rw [he]
  refine ⟨r, hsize.trans_eq ?_, tile (Fintype.equivOfCardEq hG) (Fintype.equivOfCardEq hA)
    (Equiv.refl _) hpriv⟩
  simp only [Out, Fintype.card_prod, hg, ha, mul_pow, m]
  ring

/-- A fixed geometric sequence suffices for converting short signals
into private products. -/
theorem thin : ∃ S : ℕ, 2 ≤ S ∧ ∀ (F : Type u) [Field F] (n : ℕ), 0 < n →
    ∃ r : ℕ, 2 ^ n * r ≤ S ^ n * S ^ n ∧ PrivateProducts F (S ^ n) (S ^ n) (2 ^ n) r := by
  classical
  obtain ⟨l, hl⟩ : ∃ l : ℕ, l + 1 = 1024 * 1024 := ⟨1048575, by norm_num⟩
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  let K := ZMod 17
  have hK : Fintype.card K = 17 := ZMod.card _
  have hH : Fintype.card Kˣ = 16 := by rw [Fintype.card_units, hK]
  let a := 17 ^ l
  have ha : 0 < a := by unfold a; positivity
  let S := (1024 * a) ^ 10
  have hS : 2 ≤ S := by
    apply le_trans (b := 1024 * a) (by omega)
    exact Nat.le_self_pow (by decide) _
  refine ⟨S, hS, ?_⟩
  intro F _ n hn
  apply tile_seed (blockSeed F K l) (b := 10) (g := 1024) (a := a)
    (by simpa using hl) (by simp [hK, a]) (by decide) hn
  · rw [Fintype.card_fin, hH, hl]
    norm_num
  · simp only [Out, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hK]
    rw [pow_succ (17 * 17), mul_pow, hl]
    have h : 2 ^ 11 * (17 * 17) ≤ 1024 * 1024 := by norm_num
    rw [mul_comm (17 ^ l * 17 ^ l), ← mul_assoc]
    exact Nat.mul_le_mul_right _ h

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Interior
end

/- # From a packed decoder to short sums of products -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Interior
open Finset Prices.Motion Border

variable {F T : Type} [Field F] [Fintype T] {M : Matrix T T F} {i j k d : ℕ}

open scoped Classical in
/-- The defining condition `∃ (row : Pos i j → T) (P : T → Product F (Pos i k) (Pos k j)), ∀ z x
y, matrix F i j k z x y = ∑ t, M (row z) t * (P t).apply x y`. -/
def Decoded (M : Matrix T T F) (i j k : ℕ) : Prop :=
  ∃ (row : Pos i j → T) (P : T → Product F (Pos i k) (Pos k j)),
    ∀ z x y, matrix F i j k z x y = ∑ t, M (row z) t * (P t).apply x y

open scoped Classical in
theorem decoder (h : RankLE F i j k d) (ha : i * j ≤ d) :
    ∃ M : Matrix (Fin d) (Fin d) F, Decoded M i j k := by
  obtain ⟨a, b, c, he⟩ := h
  let row : Pos i j ↪ Fin d := finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb ha)
  let M := Function.extend row (fun z t => c t z) (fun _ _ => 0)
  refine ⟨M, row, fun t => ⟨a t, b t⟩, fun z x y => ?_⟩
  simpa only [matrix, Product.apply, M, row.injective.extend_apply, mul_comm] using (he x y z).symm

open scoped Classical in
theorem Decoded.pow (h : Decoded M i j k) (n : ℕ) :
    Decoded (matPower (fun _ : Fin n => M)) (i ^ n) (j ^ n) (k ^ n) := by
  obtain ⟨row, P, he⟩ := h
  refine ⟨fun z l => row (digit z l), fun t => ⟨fun x => ∏ l, (P (t l)).left (digit x l),
    fun y => ∏ l, (P (t l)).right (digit y l)⟩, fun z x y => ?_⟩
  have hm : matrix F (i ^ n) (j ^ n) (k ^ n) z x y =
      ∏ l, matrix F i j k (digit z l) (digit x l) (digit y l) := by
    simpa only [coefficients, WPower, prod_const_one, matrix] using
      (coefficients_pow (fun _ _ _ => (1 : F)) n x y z).symm
  rw [hm]
  simp only [he, matPower, Product.apply, Fintype.prod_sum, prod_mul_distrib]

open scoped Classical in
private theorem Rows.short {Z X Y : Type} {A : Matrix Z T F} {p : ℝ} (h : Rows A p)
    (P : T → Product F X Y) (z : Z) : ∃ a : Fin ⌊p⌋₊ → Product F X Y, ∀ x y,
      ∑ t, A z t * (P t).apply x y = ∑ l, (a l).apply x y := by
  let s : Finset T := {t | A z t ≠ 0}
  have hs : s.card ≤ ⌊p⌋₊ := Nat.le_floor (h z)
  let e : Fin ⌊p⌋₊ ≃ ↥s ⊕ Fin (⌊p⌋₊-s.card) := Fintype.equivOfCardEq (by simp; omega)
  let Q : ↥s ⊕ Fin (⌊p⌋₊-s.card) → Product F X Y :=
    Sum.elim (fun t => ⟨fun x => A z t * (P t).left x, (P t).right⟩) (fun _ => ⟨0, 0⟩)
  refine ⟨Q ∘ e, fun x y => ?_⟩
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun t => (Q t).apply x y), Fintype.sum_sum_type]
  simp only [Q, Sum.elim_inl, Sum.elim_inr, Product.apply, Pi.zero_apply, zero_mul, sum_const_zero,
    add_zero, mul_assoc]
  rw [sum_coe_sort s (fun t => A z t * ((P t).left x * (P t).right y))]
  symm
  apply sum_subset (subset_univ _)
  intro t _ ht
  have hz : A z t = 0 := by simpa [s] using ht
  simp [hz]

open scoped Classical in
theorem Decoded.slots {r p : ℝ} (h : Decoded M i j k) (hp : Packed M r p) :
    ∃ e : ℕ, (e : ℝ) ≤ r ∧ Slots (matrix F i j k) e ⌊p⌋₊ := by
  obtain ⟨row, P, he⟩ := h
  obtain ⟨A, B, hM, ha, e, he', L, R, hB, hR⟩ := hp
  choose a h₁ using ha.short P
  choose b h₂ using hR.short P
  refine ⟨e, he', Sum.elim (a ∘ row) b, fun z => L (row z), fun z x y => ?_⟩
  rw [he, hM, hB]
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, ← h₁, ← h₂, Matrix.add_apply,
    Matrix.mul_apply, add_mul, sum_add_distrib, sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Interior
end

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Sums
open Spectral Filter
open scoped Topology

variable {F : Type} [Field F] {A B : Three F}

theorem rank_spec (A : Three F) : A ≤ (rank A : Three F) :=
  Nat.sInf_mem (s := {n : ℕ | A ≤ (n : Three F)}) (Tensor.exists_bound A)

private theorem rank_le {r : ℕ} (h : A ≤ (r : Three F)) : rank A ≤ r := Nat.sInf_le h

private theorem rank_mul (A B : Three F) : rank (A * B) ≤ rank A * rank B := by
  apply rank_le
  rw [Nat.cast_mul]
  refine (Tensor.mul_le_mul_left _ _ A (rank_spec B)).trans ?_
  rw [mul_comm A, mul_comm (rank A : Three F)]
  exact Tensor.mul_le_mul_left _ _ _ (rank_spec A)

private theorem rank_pos (hA : A ≠ 0) (n : ℕ) : 0 < rank (A ^ n) := by
  obtain ⟨f, hf, _⟩ := maximum_score F 0 0 0
  have hf₁ : 1 ≤ f A := by simpa using hf (Tensor.one_le A hA)
  have hh := hf (rank_spec (A ^ n))
  rw [map_pow, map_natCast] at hh
  exact_mod_cast (pow_pos (zero_lt_one.trans_le hf₁) n).trans_le hh

theorem rate_spec (hA : A ≠ 0) :
    Tendsto (fun n : ℕ => (rank (A ^ n) : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 (asymptotic A)) ∧
      ∀ n : ℕ, 0 < n → asymptotic A ≤ Real.exp (Real.log (rank (A ^ n)) / n) := by
  have hm (n m : ℕ) : rank (A ^ (n + m)) ≤ rank (A ^ n) * rank (A ^ m)
    := by rw [pow_add]; apply rank_mul
  obtain ⟨L, hl, hb⟩ := rank_rate (rank_pos hA) hm
  rw [asymptotic, hl.limUnder_eq]
  exact ⟨hl, hb⟩

theorem price_le {f : Point F} (hf : Monotone f) (hA : A ≠ 0) : (f A : ℝ) ≤ asymptotic A := by
  apply ge_of_tendsto (rate_spec hA).1
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hh := hf (rank_spec (A ^ n))
  rw [map_pow, map_natCast] at hh
  rw [← Real.pow_rpow_inv_natCast (NNReal.coe_nonneg (f A)) hn.ne']
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hh) (by positivity)

theorem asymptotic_pos (hA : A ≠ 0) : 0 < asymptotic A := by
  obtain ⟨f, hf, _⟩ := maximum_score F 0 0 0
  have hf₁ : 1 ≤ f A := by simpa using hf (Tensor.one_le A hA)
  exact (by positivity : 0 < (f A : ℝ)).trans_le (price_le hf hA)

theorem detected (hA : A ≠ 0) :
    ∃ f : Point F, Monotone f ∧ (f A : ℝ) = asymptotic A := by
  have h := asymptotic_pos hA
  obtain ⟨f, hf, hf'⟩ := detector (A := A) h (by
    intro n r hr
    rcases n.eq_zero_or_pos with rfl | hn
    · rw [pow_zero, ← Nat.cast_one] at hr
      rw [pow_zero]
      exact_mod_cast (Tensor.natCast_le_iff _ _).mp hr
    have he := (rate_spec hA).2 _ hn
    have hp : 0 < (rank (A ^ n) : ℝ) := by exact_mod_cast rank_pos hA n
    rw [div_eq_mul_inv, ← Real.rpow_def_of_pos hp] at he
    have hh := pow_le_pow_left₀ h.le he n
    rw [Real.rpow_inv_natCast_pow hp.le hn.ne'] at hh
    exact hh.trans (by exact_mod_cast rank_le hr))
  exact ⟨f, hf, le_antisymm (price_le hf hA) hf'⟩

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Sums
end

/-
# Minimum price of a sum

For each mixed product use a point detecting a full-support weighting.
The point may depend on the multiplicities of the summands. Grouping
words by multiplicity loses only a polynomial factor.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Sums
open Spectral MatrixMultiplicationAllFields.TensorSpectrum.TagWords

variable {F : Type} [Field F] {n : ℕ} {A B : Three F}

private theorem products {A B : Fin n → Three F} (hn : 0 < n) (h : ∀ i, Dominates (A i) (B i))
    (t : Fin n → ℕ) : Dominates (∏ i, A i ^ t i) (∏ i, B i ^ t i) := by
  suffices ∀ s : Finset (Fin n), Dominates (∏ i ∈ s, A i ^ t i) (∏ i ∈ s, B i ^ t i) from this _
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (h ⟨0, hn⟩).pow 0
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((h i).pow _).mul ih

private theorem majorize {A B : Fin n → Three F} (hn : 0 < n) (h : ∀ i, Dominates (A i) (B i))
    (hA : (∑ i, A i) ≠ 0) (f : Point F) (hf : Monotone f) :
    ∑ i, (f (B i) : ℝ) ≤ asymptotic (∑ i, A i) := by
  let b i := (f (B i) : ℝ)
  apply TensorSpectrum.le_of_pow_le_polynomial_mul_pow _ _ 1 n (asymptotic_pos hA).le
    zero_lt_one
  intro N _
  obtain ⟨t, ht⟩ := exists_fiberMass_ge_average (N := N) b
  obtain ⟨g, hg, hv⟩ := (products hn h fun i => (t i).val).price hf
  let a i := (g (A i) : ℝ)
  have hh : countWeight b t ≤ countWeight a t := by
    simpa only [countWeight, map_prod, map_pow, NNReal.coe_prod, NNReal.coe_pow] using hv
  have hmass : fiberMass b t ≤ fiberMass a t := mul_le_mul_of_nonneg_left hh (by positivity)
  have hm : fiberMass a t ≤ (∑ i, a i) ^ N := by
    rw [← sum_fiberMass]
    apply Finset.single_le_sum _ (Finset.mem_univ t)
    intro i _
    unfold fiberMass countWeight a
    positivity
  have he : ∑ i, a i ≤ asymptotic (∑ i, A i) := by
    simpa only [a, map_sum, NNReal.coe_sum] using price_le hg hA
  rw [one_mul, Real.rpow_natCast, mul_comm]
  apply (div_le_iff₀ (by positivity)).mp
  exact ht.trans (hmass.trans (hm.trans (pow_le_pow_left₀ (by unfold a; positivity) he N)))

variable {v : Fin n → Shape} {w : ∀ t, Weights F (v t)}

theorem blocks_ne_zero (hn : 0 < n) (hw : ∀ t a b c, w t a b c ≠ 0) : blocks v w ≠ 0 := by
  let t : Fin n := ⟨0, hn⟩
  obtain ⟨f, _, h, _⟩ := weighted_maximizer (hw t) (v t).hi (v t).hj (v t).hk
  intro he
  have hh : f (weightedTensor (w t)) ≤ f (blocks v w) := by
    rw [blocks, map_sum]
    exact Finset.single_le_sum (fun i _ => (show 0
      ≤ f (weightedTensor (w i)) from zero_le)) (Finset.mem_univ t)
  rw [he, map_zero] at hh
  exact (Real.exp_pos _).not_ge (h.trans (NNReal.coe_le_coe.mpr hh))

/-- Computes the price by the application `Real.exp (score f (Real.log v.i) (Real.log v.j)
(Real.log v.k))`. -/
def price (f : Point F) (v : Shape) := Real.exp (score f (Real.log v.i) (Real.log v.j) (Real.log
    v.k))

theorem price_lower (hn : 0 < n) (hw : ∀ t a b c, w t a b c ≠ 0) (f : Point F) (hf : Monotone f) :
    ∑ i, price f (v i) ≤ asymptotic (blocks v w) := by
  have h (t) : Dominates (weightedTensor (w t)) (tensor F (v t).i (v t).j (v t).k) :=
    ⟨_, _, _, (v t).hi, (v t).hj, (v t).hk, ⟨w t, hw t, le_rfl⟩, rfl⟩
  have he := majorize hn h (blocks_ne_zero hn hw) f hf
  simp_rw [tensor_price hf (v _).hi (v _).hj (v _).hk] at he
  exact he

theorem price_upper (F : Type) [Field F] (v : Fin n → Shape) (hn : 0 < n) :
    ∃ f : Point F, Monotone f ∧ asymptotic (blocks v (unweighted F v)) ≤ ∑ t, price f (v t) := by
  have h : blocks v (unweighted F v) ≠ 0 := blocks_ne_zero hn fun _ _ _ _ => one_ne_zero
  obtain ⟨f, hf, he⟩ := detected h
  refine ⟨f, hf, ?_⟩
  rw [← he, blocks, map_sum, NNReal.coe_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [price, ← tensor_price hf (v t).hi (v t).hj (v t).hk]
  exact NNReal.coe_le_coe.mpr (hf (ordinary_le_tensor F (v t).hi (v t).hj (v t).hk))

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Sums
end

/- # Variational formula for independent products of different shapes -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Sums
open Set Filter
open scoped Topology

variable {F : Type} [Field F] {n : ℕ} (v : Fin n → Shape)

/-- Uses `{p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}` as the representation. -/
def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

private theorem log_sum (hn : 0 < n) (t : Fin n → ℝ) :
    IsGreatest ((fun p => entropy p + ∑ i, p i * t i) '' simplex n)
      (Real.log (∑ i, Real.exp (t i))) := by
  let S := ∑ i, Real.exp (t i)
  have hS : 0 < S := Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let p i := Real.exp (t i) / S
  have hp i : 0 < p i := div_pos (Real.exp_pos _) hS
  have hs : ∑ i, p i = 1 := by
    unfold p
    rw [← Finset.sum_div, div_self hS.ne']
  have he (i) : Real.log (p i) = t i - Real.log S := by
    rw [show p i = _ from rfl, Real.log_div (Real.exp_ne_zero _) hS.ne', Real.log_exp]
  have hid (q) (hq : q ∈ simplex n) :
      entropy q + ∑ i, q i * t i = Real.log S + ∑ i, q i * (Real.log (p i) - Real.log (q i)) := by
    simp only [he, entropy, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq.2, one_mul]
    ring
  have hp' : p ∈ simplex n := ⟨fun i => (hp i).le, hs⟩
  constructor
  · refine ⟨p, hp', ?_⟩
    change entropy p + _ = Real.log S
    rw [hid p hp']
    simp
  · rintro _ ⟨q, hq, rfl⟩
    have hh := gibbs hq.1 hq.2 (fun i => (hp i).le) hs.le (fun i _ => hp i)
    change entropy q + _ ≤ Real.log S
    rw [hid q hq]
    linarith

private theorem mean_nonneg {p : Fin n → ℝ} (hp : p ∈ simplex n)
    (q : Shape → ℕ) (hq : ∀ v, 0 < q v) : 0 ≤ mean v p q :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (Real.log_nonneg (by exact_mod_cast hq (v i)))

private theorem mean_score (p : Fin n → ℝ) (f : Point F) :
    score f (mean v p Shape.i) (mean v p Shape.j) (mean v p Shape.k) =
      ∑ i, p i * score f (Real.log (v i).i) (Real.log (v i).j) (Real.log (v i).k) := by
  unfold score mean
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem blocks_limit (hn : 0 < n) (w : ∀ i, Weights F (v i)) (hw : ∀ t a b c, w t a b c ≠ 0) :
    Tendsto (fun m : ℕ => (rank ((blocks v w) ^ m) : ℝ) ^ (m : ℝ)⁻¹) atTop
      (𝓝 (asymptotic (blocks v w))) :=
  (rate_spec (blocks_ne_zero hn hw)).1

private theorem maximum_le (hn : 0 < n) (w : ∀ i, Weights F (v i)) (hw : ∀ t a b c, w t a b c ≠ 0)
    {p : Fin n → ℝ} (hp : p ∈ simplex n) :
    objective (exponent F) v p ≤ Real.log (asymptotic (blocks v w)) := by
  obtain ⟨x, y, z, hP, he⟩ := (support F).attains (mean_nonneg v hp _ Shape.hi)
    (mean_nonneg v hp _ Shape.hj) (mean_nonneg v hp _ Shape.hk)
  obtain ⟨f, hf, hval⟩ := hP.score (a := mean v p Shape.i) (b := mean v p Shape.j) (c
    := mean v p Shape.k)
  have hl := (log_sum hn (fun i => score f (Real.log (v i).i) (Real.log (v i).j) (Real.log (v
    i).k))).2
    ⟨p, hp, rfl⟩
  unfold objective
  rw [← he, hval, mean_score]
  refine hl.trans (Real.log_le_log ?_ (price_lower hn hw f hf))
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem minimum (F : Type) [Field F] (v : Fin n → Shape) (hn : 0 < n) :
    IsLeast {s | ∃ w : ∀ t, Weights F (v t), (∀ t a b c, w t a b c ≠ 0) ∧
      asymptotic (blocks v w) = s} (asymptotic (blocks v (unweighted F v))) ∧
    IsGreatest (objective (exponent F) v '' simplex n)
      (Real.log (asymptotic (blocks v (unweighted F v)))) := by
  let w := unweighted F v
  have hw : ∀ t a b c, w t a b c ≠ 0 := fun _ _ _ _ => one_ne_zero
  obtain ⟨f, hf, hh⟩ := price_upper F v hn
  constructor
  · refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rintro _ ⟨v', hv', rfl⟩
    exact hh.trans (price_lower hn hv' f hf)
  have hpos := asymptotic_pos (blocks_ne_zero hn hw)
  have he := Real.log_le_log hpos hh
  obtain ⟨p, hp, heq⟩ :=
    (log_sum hn (fun i => score f (Real.log (v i).i) (Real.log (v i).j) (Real.log (v i).k))).1
  have hscore := score_le_exponent hf (mean_nonneg v hp _ Shape.hi)
    (mean_nonneg v hp _ Shape.hj) (mean_nonneg v hp _ Shape.hk)
  rw [mean_score] at hscore
  have hle : Real.log (asymptotic (blocks v w)) ≤ objective (exponent F) v p :=
    he.trans (heq.ge.trans (add_le_add_right hscore _))
  refine ⟨⟨p, hp, le_antisymm (maximum_le v hn w hw hp) hle⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact maximum_le v hn w hw hq

/-- The rectangular law evaluates the maximum for heterogeneous direct sums. -/
theorem benchmark_maximum (v : Fin n → Shape) (hn : 0 < n)
    (hr : Rigidity F) (hs : MatrixExponent.omega F = 9 / 4) :
    IsGreatest (objective U v '' simplex n)
      (Real.log (asymptotic (blocks v (unweighted F v)))) := by
  have he : objective U v '' simplex n = objective (exponent F) v '' simplex n := by
    apply Set.image_congr
    intro p hp
    unfold objective
    rw [all_shapes hr hs (mean_nonneg v hp _ Shape.hi)
      (mean_nonneg v hp _ Shape.hj) (mean_nonneg v hp _ Shape.hk)]
  rw [he]
  exact (minimum F v hn).2

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Sums
end
