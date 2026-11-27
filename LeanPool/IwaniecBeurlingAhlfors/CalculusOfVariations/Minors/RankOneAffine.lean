/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Basic

/-!
# Rank-one affine functions are affine combinations of minors

`RankOneAffine.exists_eq_sum_minor`: a rank-one affine `f : ℝ^{N×n} → ℝ` is an affine combination
of the minors of its argument, of orders `k ≤ min (N, n)`. This is the implication (ii) ⇒ (iii′) of
Theorem 5.20 (p. 179) of B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed.,
Springer, 2008 ([D08]). As in [D08], `f` is not assumed continuous. Only this implication of the
theorem is proved here, by the proof of [D08], pp. 181–191 (induction on the number of rows, and
Lemma 5.24), with the repairs listed at the end; the equivalence is in `Minors.Characterization`.

## The proof of [D08], step by step

`ξ¹, …, ξ^N` are the rows of `ξ` (`ξ¹` is row `0` in Lean), `ξ_1, …, ξ_n` its columns, and
`ξ′ = (ξ², …, ξ^N)`. `M_{I,S}` is the minor with the rows `I` and the columns `S`, `|I| = |S| = s`;
the `s`-subsets are order embeddings `Fin s ↪o Fin n`, and the entries of [D08]'s `adj_s` are these
minors up to signs.

* **What is used of (ii)** (p. 181). The function `f` is affine along the rank-one lines
  `t ↦ ξ + t a ⊗ b` (`RankOneAffine.add_smul_vecMulVec`; `MinorsRA`). If `L` maps rank-one lines to
  rank-one lines, then `f ∘ L` has the same property (`minors_RA_comp`); the maps `L` below are the
  transposition, setting rows to zero, removing or adding a first row, and placing a smaller matrix
  in given rows and columns.
* **Reduction to `n ≥ N`** (p. 182): `f` is replaced with `ξ ↦ f (ξᵀ)` (`minors_transpose_RA`, and
  the proof of the theorem).
* **Induction on `N`, for all `n ≥ N`** (`minors_mem_span`). The induction starts at `N = 0` (`f` is
  constant). Step 1 of [D08] (`N = 1`, `f` is affine) is the case of the induction step where `ξ′`
  has no row; Step 2 (`N = 2`) is an illustration in [D08].
* **Step `N`**, (5.42) to (5.44), pp. 184–185: `f` is affine in `ξ¹`,
  `f (ξ) = ⟨ψ (ξ′); ξ¹⟩ + χ (ξ′)` (5.42), with `χ (ξ′) = f (0; ξ′)` (`minorsChi`) and
  `ψ_l (ξ′) = f (e_l; ξ′) − f (0; ξ′)` (`minorsPsi`, `minors_rowAffine`). The functions `χ` and
  `ψ_l` are affine along the rank-one lines (`minors_rowCons_RA`), so by the induction hypothesis
  they are combinations of minors of `ξ′` (5.43), and
  `f (ξ) = χ (ξ′) + ∑_s ∑_I h^I (ξ)`, `h^I (ξ) = ∑_{S,l} γ^{I}_{l,S} ξ¹_l M_{I,S} (ξ′)` (5.44)
  (`minorsPart`), `I` over the `s`-sets of rows of `ξ′`. The term `⟨β¹; ξ¹⟩` of (5.44) is the part
  `s = 0`.
* **The parts are rank-one affine** (p. 185; `minors_part_RA`): `h = f − χ` is affine along the
  rank-one lines. Setting the rows of `ξ′` outside `I` to zero (`minorsKeep`) turns `h` into
  `∑_{J ⊆ I} h^J` (`minors_part_keep`), so the `h^I` are affine along the rank-one lines, by
  induction on `s = |I|`.
* **Lemma 5.24**, p. 186, in the "stronger version" of p. 187, for one row set `I`, `|I| = s < n`
  (`minors_part_eq_sum_minor`): if `g (ξ) = ∑_{S,l} γ_{l,S} ξ¹_l M_{I,S} (ξ′)` is affine along the
  rank-one lines, then `g (ξ) = ∑_B δ_B M_{{1} ∪ I, B} (ξ)`, `B` over the `(s+1)`-sets of columns
  (5.45). Here `s ≤ N − 1 < n`, by `n ≥ N`. Part 1 (`N = 2`) is an illustration in [D08]. Part 2:
  * Fix `B = {λ_1 < ⋯ < λ_{s+1}}`. The function `X_B` (5.47) is `g` with the columns outside `B`
    set to zero, seen as a function of the `(s+1) × (s+1)` matrix `Y` placed in the rows `{1} ∪ I`
    and the columns `B` (`minorsPlace`, `minors_place_RA`):
    `X_B (Y) = ∑_{q,l} κ_{l,q} Y¹_l det (Y without the row 1 and the column q)`,
    `κ_{l,q} = γ_{λ_l, B ∖ λ_q}` (`minorsX`, `minors_part_place`).
  * The function `t ↦ X_B (ξ + t a ⊗ b)` is affine. For the pair `(λ_k, λ_{s+1})`, `k ≤ s`, of
    columns of `B`, take `a = e_1 + e_2` and `ξ` with the rows `1` and `2` zero and the rows
    `3, …, s+1` the identity on the other columns of `B`, so that `ξ_{λ_k} = ξ_{λ_{s+1}} = 0` (a
    case of (5.49), (5.52); `minorsTest`, `minors_test_add`). Then
    `X_B (ξ + t a ⊗ b) = t² X_B (ξ + a ⊗ b)` (`minors_X_test_smul`), so "the coefficient of the term
    in `t²` must be `0`" (p. 189; `minors_X_test_eq_zero`). This coefficient is the sum of the terms
    of the columns `λ_k` and `λ_{s+1}`, as displayed on p. 190, for every vector `b`
    (`minors_coeff_eq`, `minors_coeff_last`, with the minors of `minors_test_det` and
    `minors_test_det_eq_zero`).
  * Varying `b` gives (5.51) and (5.53) (`minors_coeff`): `κ_{l,q} = 0` for `l ≠ q`, and
    `κ_{k,k} = (-1)^{k+s+1} κ_{s+1,s+1}`. By the Laplace expansion along the first row,
    `X_B = δ_B det` (5.48), `δ_B = (-1)^s κ_{s+1,s+1}` (`minors_X_eq_det`).
  * If `l ∈ S`, then `γ_{l,S} = 0`: take `B = S ∪ {x}`, `x ∉ S`. The pairs `(l, S)` with `l ∉ S` are
    the `(λ_q, B ∖ λ_q)`, each counted once (`minors_exists_insert`, `minors_del_injective`), so
    `g (ξ) = ∑_B X_B (ξ_{{1} ∪ I, B})`, and (5.48) gives (5.45).
* **Conclusion** (p. 185; `minors_mem_span`): `f` is a combination of minors of `ξ′`, which are
  minors of `ξ` (`minors_tail_mem`), and of `(s+1) × (s+1)` minors of `ξ` that contain the first
  row.

## Repairs of the source, and details filled in

* (a) [D08] passes from (ii) to (ii′): `f ∈ C¹` and `f (ξ + a ⊗ b) = f (ξ) + ⟨∇f (ξ); a ⊗ b⟩`
  (pp. 181–182). That a function affine along the rank-one lines is `C¹` is not justified there,
  and it is not needed: the proof uses only the affinity along the rank-one lines. Where [D08]
  takes `β = ∇f (0)` (Step 1), `minors_affine_of_lines` shows that a function on `ℝ^n` that is
  affine along every line is affine.
* (b) In (5.47) the inner sums run over all `l = 1, …, n`, and [D08] states that `g = ∑_β X_β` and
  that the `X_β` are rank-one affine (p. 189). Both fail for `n > s + 1`: every pair `(l, S)` is
  counted `n − s` times. For `N = 2`, `n = 3`, `s = 1` and `g = det (ξ_1, ξ_2) + det (ξ_1, ξ_3)`,
  the sum of the three `X_β` is `2 g`, and the `X_β` of the columns `{1, 2}` is
  `det (ξ_1, ξ_2) − ξ¹_3 ξ²_1`, which is not rank-one affine. Here `X_B` is the restriction of `g`
  to the columns in `B`, which is rank-one affine; the identity `g = ∑_B X_B` holds once
  `γ_{l,S} = 0` is known for `l ∈ S`, and it is proved then.
* (c) The `t²` coefficients displayed on p. 190 omit terms. The columns `λ_k`, `λ_{s+1}` are equal
  for `ξ`, but not for `ξ + t a ⊗ b`, so the summands of (5.47) without another column of `B`
  contribute `b_l (b_{λ_{s+1}} − b_{λ_k})` times minors that contain the common column. These terms
  vanish for the choice `ξ_{λ_k} = ξ_{λ_{s+1}} = 0` in the rows `3, …, s+1`, which is made here.
* (d) (5.50) and (5.52) set `b_l = 0` for the other columns `l` of `B`. Then the `γ_{λ_j, B ∖ λ_k}`
  with `j ≠ k`, `j, k ≤ s`, which (5.51) and (5.53) state to vanish, are in none of the displayed
  coefficients (the terms omitted in (c), for the pair `(λ_j, λ_{s+1})`, would give them). For the
  choice of `ξ` in (c) the restriction on `b` is not needed, and `b` is arbitrary here.
* (e) In Step `N`, [D08] ("proceeding as in Step 2") does not say that `χ` and `ψ_l` are rank-one
  affine, which the induction hypothesis requires: `minors_rowCons_RA` and `minors_RA_sub`.
* (f) The row sets: [D08] shows that the `h_1^i` are rank-one affine, then "with the same
  reasoning" the `h_s` (p. 185) and the `g^i` (p. 187), and proves Lemma 5.24 for the last row set
  only, "the general case being handled similarly" (p. 187). Here `minors_part_RA` and
  `minors_part_eq_sum_minor` treat every row set `I`.
-/

@[expose] public section

namespace CalculusOfVariations

variable {d m : ℕ}

private lemma minors_rank_eq_zero_imp {A : Matrix (Fin d) (Fin m) ℝ} (h : A.rank = 0) :
    A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun F => F (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply] using this

open Matrix

/-! ### Affinity along the rank-one lines -/

/-- A function on `ℝ` that is convex and concave is affine. -/
private lemma minors_affine_of_convex_concave {g : ℝ → ℝ} (h1 : ConvexOn ℝ Set.univ g)
    (h2 : ConvexOn ℝ Set.univ (-g)) (t : ℝ) : g t = g 0 + t * (g 1 - g 0) := by
  have key : ∀ x y a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → g (a * x + b * y) = a * g x + b * g y := by
    intro x y a b ha hb hab
    have e1 := h1.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have e2 := h2.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul, Pi.neg_apply] at e1 e2
    linarith
  rcases le_or_gt t 1 with ht1 | ht1
  · rcases le_or_gt 0 t with ht0 | ht0
    · have := key 0 1 (1 - t) t (by linarith) ht0 (by ring)
      simp only [mul_zero, zero_add, mul_one] at this
      rw [this]; ring
    · -- `0` is a convex combination of `t` and `1`
      have hpos : 0 < 1 - t := by linarith
      have := key t 1 (1 / (1 - t)) (-t / (1 - t)) (by positivity)
        (div_nonneg (by linarith) hpos.le) (by field_simp; ring)
      have e : 1 / (1 - t) * t + -t / (1 - t) * 1 = 0 := by field_simp; ring
      rw [e] at this
      field_simp at this
      linarith
  · have hpos : 0 < t := by linarith
    have := key 0 t (1 - 1 / t) (1 / t) (by rw [sub_nonneg, div_le_one hpos]; linarith)
      (by positivity) (by ring)
    have e : (1 - 1 / t) * 0 + 1 / t * t = 1 := by
      rw [mul_zero, zero_add, one_div, inv_mul_cancel₀ hpos.ne']
    rw [e] at this
    field_simp at this
    linarith

private lemma minors_rank_vecMulVec {u : Fin d → ℝ} {v : Fin m → ℝ} (h : vecMulVec u v ≠ 0) :
    (vecMulVec u v).rank = 1 :=
  le_antisymm (rank_vecMulVec_le _ _) (Nat.one_le_iff_ne_zero.2 fun h' =>
    h (minors_rank_eq_zero_imp h'))

/-- A rank-one affine function is affine along the rank-one lines `t ↦ A + t (u ⊗ v)`: by
definition it is convex and concave along them. -/
theorem RankOneAffine.add_smul_vecMulVec {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : RankOneAffine f) (A : Matrix (Fin d) (Fin m) ℝ) (u : Fin d → ℝ) (v : Fin m → ℝ)
    (t : ℝ) : f (A + t • vecMulVec u v) = f A + t * (f (A + vecMulVec u v) - f A) := by
  by_cases h : vecMulVec u v = 0
  · simp [h]
  have hr := minors_rank_vecMulVec h
  have := minors_affine_of_convex_concave (hf.1 A _ hr) (hf.2 A _ hr) t
  simpa using this

/-- Affinity along the rank-one lines `t ↦ A + t (u ⊗ v)`. -/
private def MinorsRA {d m : ℕ} (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A (u : Fin d → ℝ) (v : Fin m → ℝ) (t : ℝ),
    f (A + t • vecMulVec u v) = f A + t * (f (A + vecMulVec u v) - f A)

private lemma minors_RA_sub {f g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    (hg : MinorsRA g) : MinorsRA fun A => f A - g A := by
  intro A u v t
  simp only [hf A u v t, hg A u v t]
  ring

private lemma minors_RA_sum {ι : Type*} (s : Finset ι) {F : ι → Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hF : ∀ i ∈ s, MinorsRA (F i)) : MinorsRA fun A => ∑ i ∈ s, F i A := by
  intro A u v t
  simp only
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi => hF i hi A u v t

/-- If `L` maps rank-one lines to rank-one lines and `f` is affine along the rank-one lines, then
so is `f ∘ L`. -/
private lemma minors_RA_comp {d' m' : ℕ} {f : Matrix (Fin d') (Fin m') ℝ → ℝ}
    {L : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d') (Fin m') ℝ}
    (hL : ∀ u v, ∃ u' v', ∀ Y (t : ℝ), L (Y + t • vecMulVec u v) = L Y + t • vecMulVec u' v')
    (hf : MinorsRA f) : MinorsRA fun Y => f (L Y) := by
  intro A u v t
  obtain ⟨u', v', h⟩ := hL u v
  have h1 := h A 1
  rw [one_smul, one_smul] at h1
  simp only [h, h1]
  exact hf _ _ _ _

/-- "We reverse the roles of `n` and `N`" ([D08], p. 182): `ξ ↦ f (ξᵀ)` is affine along the rank-one
lines, `(a ⊗ b)ᵀ = b ⊗ a`. -/
private lemma minors_transpose_RA {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f) :
    MinorsRA fun ξ : Matrix (Fin m) (Fin d) ℝ => f ξᵀ :=
  minors_RA_comp (fun u v => ⟨v, u, fun Y t => by
    rw [transpose_add, transpose_smul, transpose_vecMulVec]⟩) hf

/-! ### `s`-subsets of `{1, …, n}`, as order embeddings `Fin s ↪o Fin n` -/

section Emb

variable {s n : ℕ}

/-- An `s`-subset of an `s`-set is the whole set. -/
private lemma minors_emb_eq (r r' : Fin s ↪o Fin n) (h : ∀ i, r' i ∈ Set.range r) : r' = r := by
  have h1 : Set.range r' ⊆ Set.range r := by rintro _ ⟨i, rfl⟩; exact h i
  have h2 : Set.range r' = Set.range r := by
    refine Set.eq_of_subset_of_ncard_le h1 ?_ (Set.toFinite _)
    rw [← Set.image_univ, ← Set.image_univ, Set.ncard_image_of_injective _ r.injective,
      Set.ncard_image_of_injective _ r'.injective]
  exact DFunLike.coe_injective
    ((r'.strictMono.range_inj_of_wellFoundedLT r.strictMono).1 h2)

/-- A `k'`-subset of a `k`-set has `k' ≤ k`. -/
private lemma minors_emb_le {k k' : ℕ} (r : Fin k ↪o Fin n) (r' : Fin k' ↪o Fin n)
    (h : ∀ i, r' i ∈ Set.range r) : k' ≤ k := by
  choose p hp using h
  have hinj : Function.Injective p := fun i j hij => r'.injective (by rw [← hp i, ← hp j, hij])
  simpa using Fintype.card_le_of_injective p hinj

/-- The `s`-subset `B ∖ λ_q` of `B = {λ_0 < ⋯ < λ_s}`. -/
private def minorsDel (C : Fin (s + 1) ↪o Fin n) (q : Fin (s + 1)) : Fin s ↪o Fin n :=
  q.succAboveOrderEmb.trans C

private lemma minors_del_apply (C : Fin (s + 1) ↪o Fin n) (q : Fin (s + 1)) (i : Fin s) :
    minorsDel C q i = C (q.succAbove i) := rfl

/-- An `s`-subset of `B` is `B ∖ λ_q` for some `q`. -/
private lemma minors_exists_del (C : Fin (s + 1) ↪o Fin n) (c : Fin s ↪o Fin n)
    (h : ∀ i, c i ∈ Set.range C) : ∃ q, minorsDel C q = c := by
  obtain ⟨q, hq⟩ : ∃ q, C q ∉ Set.range c := by
    by_contra! hcon
    have := minors_emb_le c C hcon
    omega
  refine ⟨q, (minors_emb_eq _ _ fun i => ?_).symm⟩
  obtain ⟨x, hx⟩ := h i
  obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq (x := x) (y := q) fun hxq =>
    hq ⟨i, by rw [← hx, hxq]⟩
  exact ⟨y, hx⟩

/-- A pair `(S, l)` with `|S| = s` and `l ∉ S` is `(B ∖ λ_q, λ_q)`, with `B = S ∪ {l}`. -/
private lemma minors_exists_insert (c : Fin s ↪o Fin n) {l : Fin n} (hl : l ∉ Set.range c) :
    ∃ (C : Fin (s + 1) ↪o Fin n) (q : Fin (s + 1)), minorsDel C q = c ∧ C q = l := by
  have hl' : l ∉ Finset.univ.map c.toEmbedding := by simpa using hl
  have hcard : (insert l (Finset.univ.map c.toEmbedding)).card = s + 1 := by
    rw [Finset.card_insert_of_notMem hl', Finset.card_map, Finset.card_fin]
  set C := (insert l (Finset.univ.map c.toEmbedding)).orderEmbOfFin hcard with hC
  have hmem : ∀ x, x ∈ insert l (Finset.univ.map c.toEmbedding) → x ∈ Set.range C := by
    intro x hx
    rw [hC, Finset.range_orderEmbOfFin]
    exact Finset.mem_coe.2 hx
  obtain ⟨q, hq⟩ := hmem l (Finset.mem_insert_self _ _)
  refine ⟨C, q, (minors_emb_eq _ _ fun i => ?_).symm, hq⟩
  obtain ⟨x, hx⟩ := hmem (c i) (Finset.mem_insert_of_mem
    (Finset.mem_map_of_mem c.toEmbedding (Finset.mem_univ i)))
  obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq (x := x) (y := q) fun hxq =>
    hl ⟨i, by rw [← hx, hxq, hq]⟩
  exact ⟨y, hx⟩

/-- The pair `(B ∖ λ_q, λ_q)` determines `B` and `q`. -/
private lemma minors_del_injective :
    Function.Injective fun p : (Fin (s + 1) ↪o Fin n) × Fin (s + 1) =>
      (minorsDel p.1 p.2, p.1 p.2) := by
  rintro ⟨C, q⟩ ⟨C', q'⟩ h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  have hC : C = C' := by
    refine minors_emb_eq _ _ fun i => ?_
    rcases eq_or_ne i q with rfl | hi
    · exact ⟨q', h2.symm⟩
    · obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq hi
      exact ⟨q'.succAbove y, by rw [← minors_del_apply C, h1, minors_del_apply]⟩
  subst hC
  exact Prod.ext rfl (C.injective h2)

end Emb

/-! ### Lemma 5.24: the functions `X_B` -/

section Coeff

/-- The right-hand side of (5.47), with the columns in `B`:
`X_B (Y) = ∑_{q,l} κ_{l,q} Y¹_l det (Y without the row 1 and the column q)`. -/
private def minorsX {s : ℕ} (κ : Fin (s + 1) → Fin (s + 1) → ℝ)
    (Y : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ) : ℝ :=
  ∑ q, ∑ l, κ l q * (Y 0 l * (Y.submatrix Fin.succ q.succAbove).det)

/-- The matrix with rows `b`, `b` and the identity on the columns other than `q` and
`p = q.succAbove j` below: it is `ξ + a ⊗ b` for `a = e_1 + e_2` and for `ξ` with rows `1`, `2` and
columns `p`, `q` zero. -/
private def minorsTest {s : ℕ} (q : Fin (s + 2)) (j : Fin (s + 1)) (b : Fin (s + 2) → ℝ) :
    Matrix (Fin (s + 2)) (Fin (s + 2)) ℝ :=
  Matrix.of (Fin.cons b (Fin.cons b fun i : Fin s => Pi.single (q.succAbove (j.succAbove i)) 1))

variable {s : ℕ}

private lemma minors_test_zero (q : Fin (s + 2)) (j : Fin (s + 1)) (b : Fin (s + 2) → ℝ)
    (k : Fin (s + 2)) : minorsTest q j b 0 k = b k := rfl

private lemma minors_test_one (q : Fin (s + 2)) (j : Fin (s + 1)) (b : Fin (s + 2) → ℝ)
    (k : Fin (s + 2)) : minorsTest q j b 1 k = b k := rfl

private lemma minors_test_succ (q : Fin (s + 2)) (j : Fin (s + 1)) (b : Fin (s + 2) → ℝ)
    (i : Fin s) (k : Fin (s + 2)) : minorsTest q j b i.succ.succ k =
      (Pi.single (q.succAbove (j.succAbove i)) 1 : Fin (s + 2) → ℝ) k := rfl

/-- The line `t ↦ ξ + t a ⊗ b` of (5.49), (5.52), with `a = e_1 + e_2`. -/
private lemma minors_test_add (q : Fin (s + 2)) (j : Fin (s + 1)) (b : Fin (s + 2) → ℝ) (t : ℝ) :
    minorsTest q j 0 + t • vecMulVec (Fin.cons 1 (Fin.cons 1 0)) b = minorsTest q j (t • b) := by
  ext i k
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simp [minors_test_zero, vecMulVec_apply]
  · simp [minors_test_one, vecMulVec_apply]
  · simp [minors_test_succ, vecMulVec_apply]

/-- `X_B (ξ + t a ⊗ b) = t² X_B (ξ + a ⊗ b)`. -/
private lemma minors_X_test_smul (κ : Fin (s + 2) → Fin (s + 2) → ℝ) (q : Fin (s + 2))
    (j : Fin (s + 1)) (b : Fin (s + 2) → ℝ) (t : ℝ) :
    minorsX κ (minorsTest q j (t • b)) = t ^ 2 * minorsX κ (minorsTest q j b) := by
  have h : ∀ x : Fin (s + 2), ((minorsTest q j (t • b)).submatrix Fin.succ x.succAbove).det =
      t * ((minorsTest q j b).submatrix Fin.succ x.succAbove).det := by
    intro x
    have e : (minorsTest q j (t • b)).submatrix Fin.succ x.succAbove =
        ((minorsTest q j b).submatrix Fin.succ x.succAbove).updateRow 0
          (t • ((minorsTest q j b).submatrix Fin.succ x.succAbove) 0) := by
      ext i k
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [updateRow_self, minors_test_one]
      · rw [updateRow_ne (Fin.succ_ne_zero i)]
        simp [minors_test_succ]
    rw [e, det_updateRow_smul, updateRow_eq_self]
  simp only [minorsX, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [minors_test_zero, Pi.smul_apply, smul_eq_mul]
  ring

/-- "The coefficient of the term in `t²` must be `0`" ([D08], p. 189). -/
private lemma minors_X_test_eq_zero {κ : Fin (s + 2) → Fin (s + 2) → ℝ}
    (hX : MinorsRA (minorsX κ)) (q : Fin (s + 2)) (j : Fin (s + 1)) (b : Fin (s + 2) → ℝ) :
    minorsX κ (minorsTest q j b) = 0 := by
  have h := hX (minorsTest q j 0) (Fin.cons 1 (Fin.cons 1 0)) b 2
  have h1 := minors_test_add q j b 1
  rw [one_smul, one_smul] at h1
  have h0 := minors_X_test_smul κ q j b 0
  rw [zero_smul] at h0
  rw [minors_test_add, h1, minors_X_test_smul, h0] at h
  linarith

/-- The minor without the column `q`: its first row is `b`, the others are the identity on the
columns other than `p = q.succAbove j`. -/
private lemma minors_test_det (q : Fin (s + 2)) (j : Fin (s + 1)) (b : Fin (s + 2) → ℝ) :
    ((minorsTest q j b).submatrix Fin.succ q.succAbove).det =
      (-1) ^ (j : ℕ) * b (q.succAbove j) := by
  rw [det_succ_row_zero, Finset.sum_eq_single j]
  · have e : ((minorsTest q j b).submatrix Fin.succ q.succAbove).submatrix Fin.succ j.succAbove =
        1 := by
      ext i k
      simp [minors_test_succ, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [e, det_one, mul_one]
    simp [minors_test_one]
  · intro x _ hx
    obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq hx
    rw [det_eq_zero_of_row_eq_zero y fun k => ?_, mul_zero]
    simp [minors_test_succ, Fin.succAbove_ne]
  · simp

/-- The minors without a column other than `p` and `q` have a zero row. -/
private lemma minors_test_det_eq_zero (q : Fin (s + 2)) (j : Fin (s + 1)) (b : Fin (s + 2) → ℝ)
    (i : Fin s) : ((minorsTest q j b).submatrix Fin.succ
      (q.succAbove (j.succAbove i)).succAbove).det = 0 := by
  refine det_eq_zero_of_row_eq_zero i.succ fun k => ?_
  simp [minors_test_succ, Fin.succAbove_ne]

/-- The `t²` coefficients of p. 190 of [D08], for the columns `q` and `p = q.succAbove j`. -/
private lemma minors_coeff_eq {κ : Fin (s + 2) → Fin (s + 2) → ℝ} (hX : MinorsRA (minorsX κ))
    (q : Fin (s + 2)) (j : Fin (s + 1)) (b : Fin (s + 2) → ℝ) :
    (∑ l, κ l q * b l) * ((-1) ^ (j : ℕ) * b (q.succAbove j)) +
      (∑ l, κ l (q.succAbove j) * b l) *
        ((minorsTest q j b).submatrix Fin.succ (q.succAbove j).succAbove).det = 0 := by
  have h := minors_X_test_eq_zero hX q j b
  have h' : ∀ x : Fin (s + 2), ∑ l, κ l x * (minorsTest q j b 0 l *
      ((minorsTest q j b).submatrix Fin.succ x.succAbove).det) = (∑ l, κ l x * b l) *
      ((minorsTest q j b).submatrix Fin.succ x.succAbove).det := by
    intro x
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by rw [minors_test_zero, mul_assoc]
  simp only [minorsX, h'] at h
  rw [Fin.sum_univ_succAbove _ q, Fin.sum_univ_succAbove _ j, minors_test_det] at h
  simp only [minors_test_det_eq_zero, mul_zero, Finset.sum_const_zero, add_zero] at h
  exact h

/-- The displayed coefficient of p. 190 of [D08] for the pair `(λ_k, λ_{s+1})`, for every `b`: the
sum of the terms of the columns `λ_k` and `λ_{s+1}`. -/
private lemma minors_coeff_last {κ : Fin (s + 2) → Fin (s + 2) → ℝ} (hX : MinorsRA (minorsX κ))
    (k : Fin (s + 1)) (b : Fin (s + 2) → ℝ) :
    (∑ l, κ l k.castSucc * b l) * ((-1) ^ s * b (Fin.last (s + 1))) +
      (∑ l, κ l (Fin.last (s + 1)) * b l) * ((-1) ^ (k : ℕ) * b k.castSucc) = 0 := by
  have h := minors_coeff_eq hX k.castSucc (Fin.last s) b
  have e : k.castSucc.succAbove (Fin.last s) = Fin.last (s + 1) := by simp
  have ht : minorsTest k.castSucc (Fin.last s) b = minorsTest (Fin.last (s + 1)) k b := by
    simp [minorsTest, Fin.succAbove_last, Fin.castSucc_succAbove_castSucc]
  rw [e, ht, minors_test_det, Fin.succAbove_last, Fin.val_last] at h
  exact h

/-- (5.51), (5.53): if `X_B` is affine along the rank-one lines, then `κ_{l,q} = 0` for `l ≠ q`, and
the `κ_{q,q}` alternate. As in [D08], only the pairs `(λ_k, λ_{s+1})` are used. The vector `b` is
arbitrary: `e_{s+1}` and `e_{s+1} + e_l` give `κ_{l,k} = 0` for `l ≠ k`, `e_k` and `e_k + e_l` give
`κ_{l,s+1} = 0` for `l ≠ s + 1`, and `e_k + e_{s+1}` gives the relation of `κ_{k,k}` and
`κ_{s+1,s+1}`. -/
private lemma minors_coeff {κ : Fin (s + 1) → Fin (s + 1) → ℝ} (hX : MinorsRA (minorsX κ)) :
    (∀ l q, l ≠ q → κ l q = 0) ∧
      ∀ q, κ q q = (-1) ^ (q : ℕ) * ((-1) ^ s * κ (Fin.last s) (Fin.last s)) := by
  cases s with
  | zero =>
    refine ⟨fun l q hlq => absurd ((Fin.fin_one_eq_zero l).trans (Fin.fin_one_eq_zero q).symm) hlq,
      fun q => ?_⟩
    rw [show q = Fin.last 0 from (Fin.fin_one_eq_zero q).trans rfl]
    simp
  | succ s =>
    have hpow : ∀ n : ℕ, ((-1 : ℝ)) ^ n ≠ 0 := fun n => pow_ne_zero _ (by norm_num)
    -- the pair `(λ_k, λ_{s+1})`
    have hk : ∀ k : Fin (s + 1), (∀ l, l ≠ k.castSucc → κ l k.castSucc = 0) ∧
        ∀ l, l ≠ Fin.last (s + 1) → κ l (Fin.last (s + 1)) = 0 := by
      intro k
      have hne : Fin.last (s + 1) ≠ k.castSucc := (Fin.castSucc_lt_last k).ne'
      have h1 : κ (Fin.last (s + 1)) k.castSucc = 0 := by
        have h := minors_coeff_last hX k (Pi.single (Fin.last (s + 1)) 1)
        simpa [Pi.single_apply, hne, hne.symm] using h
      have h2 : κ k.castSucc (Fin.last (s + 1)) = 0 := by
        have h := minors_coeff_last hX k (Pi.single k.castSucc 1)
        simpa [Pi.single_apply, hne, hne.symm] using h
      constructor
      · intro l hl
        by_cases hl' : l = Fin.last (s + 1)
        · rw [hl', h1]
        · have h := minors_coeff_last hX k (Pi.single (Fin.last (s + 1)) 1 + Pi.single l 1)
          simpa [mul_add, Finset.sum_add_distrib, Pi.single_apply, hne, hne.symm, hl, Ne.symm hl,
            hl', Ne.symm hl', h1] using h
      · intro l hl
        by_cases hl' : l = k.castSucc
        · rw [hl', h2]
        · have h := minors_coeff_last hX k (Pi.single k.castSucc 1 + Pi.single l 1)
          simpa [mul_add, Finset.sum_add_distrib, Pi.single_apply, hne, hne.symm, hl, Ne.symm hl,
            hl', Ne.symm hl', h2] using h
    constructor
    · intro l q hlq
      refine Fin.lastCases (fun hlq => (hk 0).2 l hlq) (fun k hlq => (hk k).1 l hlq) q hlq
    · refine Fin.lastCases ?_ (fun k => ?_)
      · rw [Fin.val_last, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
      · have hne : Fin.last (s + 1) ≠ k.castSucc := (Fin.castSucc_lt_last k).ne'
        have h := minors_coeff_last hX k (Pi.single k.castSucc 1 + Pi.single (Fin.last (s + 1)) 1)
        have h1 := (hk k).1 _ hne
        have h2 := (hk k).2 _ hne.symm
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hne, hne.symm, ite_false, h1, h2,
          add_zero, zero_add] at h
        rw [Fin.val_castSucc]
        have e1 : ((-1 : ℝ)) ^ s * (-1) ^ s = 1 := by rw [← mul_pow]; norm_num
        calc κ k.castSucc k.castSucc = κ k.castSucc k.castSucc * ((-1) ^ s * (-1) ^ s) := by
              rw [e1, mul_one]
          _ = (-1) ^ (k : ℕ) * ((-1) ^ (s + 1) * κ (Fin.last (s + 1)) (Fin.last (s + 1))) := by
              rw [pow_succ]
              linear_combination (-1 : ℝ) ^ s * h

/-- (5.48): `X_B = δ_B det`, by the Laplace expansion along the first row, with
`δ_B = (-1)^s κ_{s+1,s+1}`. -/
private lemma minors_X_eq_det {κ : Fin (s + 1) → Fin (s + 1) → ℝ} (hX : MinorsRA (minorsX κ))
    (Y : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ) :
    minorsX κ Y = ((-1) ^ s * κ (Fin.last s) (Fin.last s)) * Y.det := by
  rw [det_succ_row_zero, minorsX, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_eq_single q (fun l _ hl => by rw [(minors_coeff hX).1 l q hl, zero_mul])
    fun hq => absurd (Finset.mem_univ q) hq, (minors_coeff hX).2 q]
  ring

end Coeff

/-! ### Lemma 5.24 -/

section Lemma524

variable {N s : ℕ}

/-- The rows `{1} ∪ I` of `ξ`, for a set `I` of rows of `ξ′`. -/
private def minorsRows (r : Fin s ↪o Fin N) : Fin (s + 1) ↪o Fin (N + 1) :=
  OrderEmbedding.ofStrictMono (Fin.cons 0 (Fin.succ ∘ r))
    (Fin.strictMono_cons.2 ⟨fun _ => Fin.succ_pos _, Fin.strictMono_succ.comp r.strictMono⟩)

private lemma minors_rows_zero (r : Fin s ↪o Fin N) : minorsRows r 0 = 0 := rfl

/-- The function `g (ξ) = ∑_{S,l} γ_{l,S} ξ¹_l M_{I,S} (ξ′)` of Lemma 5.24 (p. 187), for a set `I`
of rows of `ξ′`; the parts `h^I` in (5.44). -/
private noncomputable def minorsPart (r : Fin s ↪o Fin N) (γ : (Fin s ↪o Fin m) → Fin m → ℝ)
    (ξ : Matrix (Fin (N + 1)) (Fin m) ℝ) : ℝ :=
  ∑ c, ∑ l, γ c l * (ξ 0 l * minor (ξ.submatrix Fin.succ id) r c)

/-- The matrix `Y` in the rows `R` and the columns `C`, with zeros elsewhere. -/
private def minorsPlace {k : ℕ} (R : Fin k ↪o Fin d) (C : Fin k ↪o Fin m)
    (Y : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin d) (Fin m) ℝ :=
  (1 : Matrix (Fin d) (Fin d) ℝ).submatrix id R * Y *
    (1 : Matrix (Fin m) (Fin m) ℝ).submatrix C id

private lemma minors_place_apply {k : ℕ} (R : Fin k ↪o Fin d) (C : Fin k ↪o Fin m)
    (Y : Matrix (Fin k) (Fin k) ℝ) (i j : Fin k) : minorsPlace R C Y (R i) (C j) = Y i j := by
  simp [minorsPlace, Matrix.mul_apply, Matrix.one_apply]

private lemma minors_place_of_notMem {k : ℕ} (R : Fin k ↪o Fin d) (C : Fin k ↪o Fin m)
    (Y : Matrix (Fin k) (Fin k) ℝ) (i : Fin d) {j : Fin m} (hj : j ∉ Set.range C) :
    minorsPlace R C Y i j = 0 := by
  have hj' : ∀ x, C x ≠ j := fun x hx => hj ⟨x, hx⟩
  simp [minorsPlace, Matrix.mul_apply, Matrix.one_apply, hj']

private lemma minors_place_RA {k : ℕ} {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    (R : Fin k ↪o Fin d) (C : Fin k ↪o Fin m) : MinorsRA fun Y => f (minorsPlace R C Y) := by
  refine minors_RA_comp (fun u v => ⟨(1 : Matrix (Fin d) (Fin d) ℝ).submatrix id R *ᵥ u,
    v ᵥ* (1 : Matrix (Fin m) (Fin m) ℝ).submatrix C id, fun Y t => ?_⟩) hf
  rw [minorsPlace, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_vecMulVec, vecMulVec_mul]
  rfl

/-- (5.47), restricted to the columns in `B`: `X_B (Y)` is the value of `g` at `Y` placed in the
rows `{1} ∪ I` and the columns `B`. -/
private lemma minors_part_place (r : Fin s ↪o Fin N) (γ : (Fin s ↪o Fin m) → Fin m → ℝ)
    (C : Fin (s + 1) ↪o Fin m) (Y : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ) :
    minorsPart r γ (minorsPlace (minorsRows r) C Y) =
      minorsX (fun l q => γ (minorsDel C q) (C l)) Y := by
  have hinj : Function.Injective fun q => minorsDel C q := by
    intro q q' h
    by_contra hqq
    obtain ⟨y, hy⟩ := Fin.exists_succAbove_eq (Ne.symm hqq)
    have h1 : C (q.succAbove y) = C (q'.succAbove y) := congrArg (fun c => c y) h
    rw [hy] at h1
    exact Fin.succAbove_ne q' y (C.injective h1).symm
  symm
  refine Fintype.sum_of_injective _ hinj _ _ (fun c hc => ?_) fun q => ?_
  · -- a column of the minor is outside `B`
    obtain ⟨k, hk⟩ : ∃ k, c k ∉ Set.range C := by
      by_contra! hcon
      exact hc (minors_exists_del C c hcon)
    have h0 : minor ((minorsPlace (minorsRows r) C Y).submatrix Fin.succ id) r c = 0 :=
      det_eq_zero_of_column_eq_zero k fun i => minors_place_of_notMem _ _ _ _ hk
    simp [h0]
  · have h0 : minor ((minorsPlace (minorsRows r) C Y).submatrix Fin.succ id) r (minorsDel C q) =
        (Y.submatrix Fin.succ q.succAbove).det := by
      unfold minor
      congr 1
      ext i k
      exact minors_place_apply (minorsRows r) C Y i.succ (q.succAbove k)
    refine Fintype.sum_of_injective C C.injective _ _ (fun l hl => ?_) fun l => ?_
    · rw [minors_place_of_notMem _ _ _ _ hl, zero_mul, mul_zero]
    · rw [h0, ← minors_place_apply (minorsRows r) C Y 0 l, minors_rows_zero]

/-- **Lemma 5.24** of [D08], p. 186, for one row set `I`, `|I| = s < n` (the "stronger version" of
p. 187): if `g (ξ) = ∑_{S,l} γ_{l,S} ξ¹_l M_{I,S} (ξ′)` is affine along the rank-one lines, then
`g (ξ) = ∑_B δ_B M_{{1} ∪ I, B} (ξ)`, `B` over the `(s+1)`-sets of columns (5.45). -/
private lemma minors_part_eq_sum_minor (hs : s < m) (r : Fin s ↪o Fin N)
    (γ : (Fin s ↪o Fin m) → Fin m → ℝ) (hg : MinorsRA (minorsPart r γ)) :
    ∃ δ : (Fin (s + 1) ↪o Fin m) → ℝ,
      ∀ ξ, minorsPart r γ ξ = ∑ C, δ C * minor ξ (minorsRows r) C := by
  have hX : ∀ C : Fin (s + 1) ↪o Fin m, MinorsRA (minorsX fun l q => γ (minorsDel C q) (C l)) := by
    intro C
    simpa only [minors_part_place] using minors_place_RA hg (minorsRows r) C
  -- `γ_{l,S} = 0` for `l ∈ S`
  have hzero : ∀ (c : Fin s ↪o Fin m) l, l ∈ Set.range c → γ c l = 0 := by
    rintro c _ ⟨k, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x, x ∉ Set.range c := by
      by_contra! hcon
      have := Fintype.card_le_of_surjective c hcon
      simp only [Fintype.card_fin] at this
      omega
    obtain ⟨C, q, rfl, -⟩ := minors_exists_insert c hx
    exact (minors_coeff (hX C)).1 (q.succAbove k) q (Fin.succAbove_ne q k)
  refine ⟨fun C => (-1) ^ s * γ (minorsDel C (Fin.last s)) (C (Fin.last s)), fun ξ => ?_⟩
  -- the sum over the pairs `(l, S)`, `l ∉ S`, regrouped by `B = S ∪ {l}`
  rw [minorsPart, ← Fintype.sum_prod_type', ← Fintype.sum_of_injective _ minors_del_injective
    (fun p => γ (minorsDel p.1 p.2) (p.1 p.2) *
      (ξ 0 (p.1 p.2) * minor (ξ.submatrix Fin.succ id) r (minorsDel p.1 p.2))) _
    (fun p hp => ?_) fun _ => rfl, Fintype.sum_prod_type]
  · refine Finset.sum_congr rfl fun C _ => ?_
    -- the term of `B` is `X_B = δ_B det`
    rw [minor, ← minors_X_eq_det (hX C), minorsX]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single q (fun l _ hl => by rw [(minors_coeff (hX C)).1 l q hl, zero_mul])
      fun hq => absurd (Finset.mem_univ q) hq]
    rfl
  · obtain ⟨c, l⟩ := p
    rw [hzero c l, zero_mul]
    by_contra hl
    obtain ⟨C, q, h1, h2⟩ := minors_exists_insert c hl
    exact hp ⟨(C, q), Prod.ext h1 h2⟩

end Lemma524

/-! ### The parts of (5.44) are affine along the rank-one lines -/

section Parts

variable {N : ℕ}

/-- The matrix `ξ` with the rows of `ξ′` outside `I` set to zero. -/
private def minorsKeep {s : ℕ} (r : Fin s ↪o Fin N) (ξ : Matrix (Fin (N + 1)) (Fin m) ℝ) :
    Matrix (Fin (N + 1)) (Fin m) ℝ :=
  Matrix.of (Fin.cons (ξ 0) fun i j => if ∃ a, r a = i then ξ i.succ j else 0)

private lemma minors_keep_zero {s : ℕ} (r : Fin s ↪o Fin N) (ξ : Matrix (Fin (N + 1)) (Fin m) ℝ)
    (j : Fin m) : minorsKeep r ξ 0 j = ξ 0 j := rfl

private lemma minors_keep_succ {s : ℕ} (r : Fin s ↪o Fin N) (ξ : Matrix (Fin (N + 1)) (Fin m) ℝ)
    (i : Fin N) (j : Fin m) :
    minorsKeep r ξ i.succ j = if ∃ a, r a = i then ξ i.succ j else 0 := rfl

private lemma minors_keep_RA {s : ℕ} {f : Matrix (Fin (N + 1)) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    (r : Fin s ↪o Fin N) : MinorsRA fun ξ => f (minorsKeep r ξ) := by
  refine minors_RA_comp (fun u v => ⟨Fin.cons (u 0) fun i => if ∃ a, r a = i then u i.succ else 0,
    v, fun Y t => ?_⟩) hf
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [minors_keep_zero, vecMulVec_apply]
  · by_cases h : ∃ a, r a = i <;> simp [minors_keep_succ, vecMulVec_apply, h]

/-- With the rows of `ξ′` outside `I` set to zero, `h^J` is unchanged if `J ⊆ I` and zero
otherwise. -/
private lemma minors_part_keep {s s' : ℕ} (r : Fin s ↪o Fin N) (r' : Fin s' ↪o Fin N)
    (γ : (Fin s' ↪o Fin m) → Fin m → ℝ) (ξ : Matrix (Fin (N + 1)) (Fin m) ℝ) :
    minorsPart r' γ (minorsKeep r ξ) =
      if ∀ i, ∃ a, r a = r' i then minorsPart r' γ ξ else 0 := by
  split_ifs with h
  · rw [minorsPart, minorsPart]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => ?_
    congr 2
    unfold minor
    congr 1
    ext i j
    simp [minors_keep_succ, h i]
  · rw [minorsPart]
    push Not at h
    obtain ⟨i, hi⟩ := h
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun l _ => ?_
    have h0 : minor ((minorsKeep r ξ).submatrix Fin.succ id) r' c = 0 := by
      refine det_eq_zero_of_row_eq_zero i fun j => ?_
      simp [minors_keep_succ, hi]
    rw [h0, mul_zero, mul_zero]

/-- [D08], p. 185: if `h = ∑_s ∑_I h^I` is affine along the rank-one lines, then so is each `h^I`.
Induction on `s = |I|`: with the rows of `ξ′` outside `I` set to zero, `h` is the sum of `h^I` and
of the `h^J`, `J ⊂ I`, `|J| < s`. -/
private lemma minors_part_RA {K : ℕ}
    {γ : (k : ℕ) → (Fin k ↪o Fin N) → (Fin k ↪o Fin m) → Fin m → ℝ}
    (h : MinorsRA fun ξ => ∑ k ∈ Finset.range K, ∑ r, minorsPart r (γ k r) ξ) :
    ∀ s < K, ∀ r : Fin s ↪o Fin N, MinorsRA (minorsPart r (γ s r)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs r
    have key : ∀ ξ, minorsPart r (γ s r) ξ =
        (∑ k ∈ Finset.range K, ∑ r', minorsPart r' (γ k r') (minorsKeep r ξ)) -
          ∑ k ∈ Finset.range s, ∑ r', minorsPart r' (γ k r') (minorsKeep r ξ) := by
      intro ξ
      rw [← Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_of_lt hs)),
        Finset.sum_range_succ, add_sub_cancel_left, Finset.sum_eq_single r]
      · simp [minors_part_keep]
      · intro r' _ hr'
        rw [minors_part_keep, ite_eq_right]
        exact fun hsub => hr' (minors_emb_eq r r' hsub)
      · exact fun hr => absurd (Finset.mem_univ r) hr
      · intro k _ hk
        refine Finset.sum_eq_zero fun r' _ => ?_
        rw [minors_part_keep, ite_eq_right]
        intro hsub
        have := minors_emb_le r r' hsub
        rw [Finset.mem_range, not_lt] at hk
        omega
    rw [funext key]
    refine minors_RA_sub (minors_keep_RA h r) (minors_RA_sum _ fun k hk => minors_RA_sum _
      fun r' _ => minors_keep_RA (ih k (Finset.mem_range.1 hk) ?_ r') r)
    exact (Finset.mem_range.1 hk).trans hs

end Parts

/-! ### The induction on the number of rows -/

section Induction

/-- The span of the minors. -/
private def minorsSpan (d m : ℕ) : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ → ℝ) :=
  Submodule.span ℝ {g | ∃ (k : ℕ) (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m),
    g = fun A => minor A r c}

private lemma minors_minor_mem {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m) :
    (fun A : Matrix (Fin d) (Fin m) ℝ => minor A r c) ∈ minorsSpan d m :=
  Submodule.subset_span ⟨k, r, c, rfl⟩

/-- The coefficients of an element of the span of the minors. -/
private lemma minors_exists_coeff {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : f ∈ minorsSpan d m) :
    ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
      ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c := by
  let ι := Σ k : Fin (min d m + 1), (Fin k ↪o Fin d) × (Fin k ↪o Fin m)
  let v : ι → Matrix (Fin d) (Fin m) ℝ → ℝ := fun i A => minor A i.2.1 i.2.2
  have hle : minorsSpan d m ≤ Submodule.span ℝ (Set.range v) := by
    refine Submodule.span_le.2 ?_
    rintro g ⟨k, r, c, rfl⟩
    have hk : k < min d m + 1 := by
      have h1 := Fintype.card_le_of_embedding r.toEmbedding
      have h2 := Fintype.card_le_of_embedding c.toEmbedding
      simp only [Fintype.card_fin] at h1 h2
      omega
    exact Submodule.subset_span ⟨⟨⟨k, hk⟩, (r, c)⟩, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hle hf)
  refine ⟨fun k r c => if hk : k < min d m + 1 then a ⟨⟨k, hk⟩, (r, c)⟩ else 0, fun A => ?_⟩
  rw [← ha, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [k.isLt, ↓reduceDIte, Pi.smul_apply, smul_eq_mul, v]

/-- The minors of `ξ′` are minors of `ξ`. -/
private lemma minors_tail_mem {g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hg : g ∈ minorsSpan d m) :
    (fun ξ : Matrix (Fin (d + 1)) (Fin m) ℝ => g (ξ.submatrix Fin.succ id)) ∈
      minorsSpan (d + 1) m := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, r, c, rfl⟩ := hx
    exact minors_minor_mem (r.trans (Fin.succOrderEmb d)) c
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

/-- The matrix `(a; ξ′)` with first row `a` and the rows of `ξ′` below it. -/
private def minorsRowCons (a : Fin m → ℝ) (ξ' : Matrix (Fin d) (Fin m) ℝ) :
    Matrix (Fin (d + 1)) (Fin m) ℝ :=
  Matrix.of (Fin.cons a fun i => ξ' i)

@[simp] private lemma minorsRowCons_zero (a : Fin m → ℝ) (ξ' : Matrix (Fin d) (Fin m) ℝ)
    (j : Fin m) : minorsRowCons a ξ' 0 j = a j := rfl

@[simp] private lemma minorsRowCons_succ (a : Fin m → ℝ) (ξ' : Matrix (Fin d) (Fin m) ℝ)
    (i : Fin d) (j : Fin m) : minorsRowCons a ξ' i.succ j = ξ' i j := rfl

private lemma minorsRowCons_eta (ξ : Matrix (Fin (d + 1)) (Fin m) ℝ) :
    minorsRowCons (ξ 0) (ξ.submatrix Fin.succ id) = ξ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

/-- A function on `ℝ^m` that is affine along every line is affine (Step 1 of [D08], p. 182, without
the gradient). -/
private lemma minors_affine_of_lines {g : (Fin m → ℝ) → ℝ}
    (hg : ∀ a v (t : ℝ), g (a + t • v) = g a + t * (g (a + v) - g a)) (a : Fin m → ℝ) :
    g a = g 0 + ∑ k, a k * (g (Pi.single k 1) - g 0) := by
  have hsmul : ∀ (t : ℝ) x, g (t • x) - g 0 = t * (g x - g 0) := by
    intro t x
    have := hg 0 x t
    simp only [zero_add] at this
    rw [this]; ring
  have hadd : ∀ x y, g (x + y) - g 0 = (g x - g 0) + (g y - g 0) := by
    intro x y
    have e1 := hg x (y - x) (1 / 2)
    have e2 := hg 0 (x + y) (1 / 2)
    have e : x + (1 / 2 : ℝ) • (y - x) = 0 + (1 / 2 : ℝ) • (x + y) := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
      ring
    rw [e, e2, add_sub_cancel] at e1
    simp only [zero_add] at e1
    linarith
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => g x - g 0
      map_add' := hadd
      map_smul' := fun t x => by simp only [hsmul, smul_eq_mul, RingHom.id_apply] }
  have h := LinearMap.pi_apply_eq_sum_univ L a
  have hs : ∀ i : Fin m, (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    intro i; ext j; simp [Pi.single_apply, eq_comm]
  simp only [hs, smul_eq_mul] at h
  change g a - g 0 = ∑ i, a i * (g (Pi.single i 1) - g 0) at h
  linarith

/-- The function `χ (ξ′) = f (0; ξ′)` of (5.42). -/
private def minorsChi (f : Matrix (Fin (d + 1)) (Fin m) ℝ → ℝ) (ξ' : Matrix (Fin d) (Fin m) ℝ) :
    ℝ :=
  f (minorsRowCons 0 ξ')

/-- The function `ψ_l (ξ′) = f (e_l; ξ′) − f (0; ξ′)` of (5.42). -/
private def minorsPsi (f : Matrix (Fin (d + 1)) (Fin m) ℝ → ℝ) (l : Fin m)
    (ξ' : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  f (minorsRowCons (Pi.single l 1) ξ') - minorsChi f ξ'

/-- (5.42): `f` is affine in the first row, `f (a; ξ′) = χ (ξ′) + ∑_l a_l ψ_l (ξ′)`. -/
private lemma minors_rowAffine {f : Matrix (Fin (d + 1)) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    (a : Fin m → ℝ) (ξ' : Matrix (Fin d) (Fin m) ℝ) :
    f (minorsRowCons a ξ') = minorsChi f ξ' + ∑ l, a l * minorsPsi f l ξ' := by
  refine minors_affine_of_lines (g := fun a => f (minorsRowCons a ξ')) (fun a v t => ?_) a
  have h := hf (minorsRowCons a ξ') (Fin.cons 1 0) v t
  have e : ∀ s : ℝ, minorsRowCons a ξ' + s • vecMulVec (Fin.cons 1 0) v =
      minorsRowCons (a + s • v) ξ' := by
    intro s
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [vecMulVec_apply]
  have e1 := e 1
  rw [one_smul, one_smul] at e1
  rwa [e t, e1] at h

/-- For a fixed first row, `f` is affine along the rank-one lines in `ξ′`. -/
private lemma minors_rowCons_RA {f : Matrix (Fin (d + 1)) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    (w : Fin m → ℝ) : MinorsRA fun ξ' => f (minorsRowCons w ξ') := by
  refine minors_RA_comp (fun u v => ⟨Fin.cons 0 u, v, fun Y t => ?_⟩) hf
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [vecMulVec_apply]

private lemma minors_tail_RA {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f) :
    MinorsRA fun ξ : Matrix (Fin (d + 1)) (Fin m) ℝ => f (ξ.submatrix Fin.succ id) :=
  minors_RA_comp (fun u v => ⟨fun i => u i.succ, v, fun _ _ => rfl⟩) hf

/-- **The induction on the number of rows**, [D08], pp. 182–185: for `N ≤ n`, a function on
`ℝ^{N×n}` that is affine along the rank-one lines is a linear combination of minors. -/
private lemma minors_mem_span : ∀ d ≤ m, ∀ f : Matrix (Fin d) (Fin m) ℝ → ℝ, MinorsRA f →
    f ∈ minorsSpan d m := by
  intro d
  induction d with
  | zero =>
    intro _ f _
    let r0 : Fin 0 ↪o Fin 0 := OrderEmbedding.ofIsEmpty
    let c0 : Fin 0 ↪o Fin m := OrderEmbedding.ofIsEmpty
    have hf : f = f 0 • fun A : Matrix (Fin 0) (Fin m) ℝ => minor A r0 c0 := by
      ext A
      have hA : A = 0 := by ext i; exact i.elim0
      simp [minor, hA, det_isEmpty]
    rw [hf]
    exact Submodule.smul_mem _ _ (minors_minor_mem r0 c0)
  | succ N ih =>
    intro hN f hf
    -- (5.43): the induction hypothesis for `χ` and the `ψ_l`
    have hχ := ih (by omega) (minorsChi f) (minors_rowCons_RA hf 0)
    choose a ha using fun l => minors_exists_coeff (ih (by omega) (minorsPsi f l)
      (minors_RA_sub (minors_rowCons_RA hf _) (minors_rowCons_RA hf 0)))
    let γ : (k : ℕ) → (Fin k ↪o Fin N) → (Fin k ↪o Fin m) → Fin m → ℝ := fun k r c l => a l k r c
    -- (5.44)
    have h44 : ∀ ξ, f ξ = minorsChi f (ξ.submatrix Fin.succ id) +
        ∑ k ∈ Finset.range (min N m + 1), ∑ r, minorsPart r (γ k r) ξ := by
      intro ξ
      conv_lhs => rw [← minorsRowCons_eta ξ, minors_rowAffine hf]
      congr 1
      simp only [ha, Finset.mul_sum, minorsPart]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    -- `h = f − χ` is affine along the rank-one lines
    have hh : MinorsRA fun ξ => ∑ k ∈ Finset.range (min N m + 1), ∑ r, minorsPart r (γ k r) ξ := by
      have := minors_RA_sub hf (minors_tail_RA (minors_rowCons_RA hf 0))
      convert this using 2 with ξ
      rw [h44 ξ]
      simp [minorsChi]
    -- Lemma 5.24 for each part, with `s = k ≤ N < n`
    have hmem : ∀ k ∈ Finset.range (min N m + 1), ∀ r : Fin k ↪o Fin N,
        minorsPart r (γ k r) ∈ minorsSpan (N + 1) m := by
      intro k hk r
      rw [Finset.mem_range] at hk
      obtain ⟨δ, hδ⟩ := minors_part_eq_sum_minor (by omega) r (γ k r) (minors_part_RA hh k hk r)
      have e : minorsPart r (γ k r) = ∑ C, δ C • fun ξ => minor ξ (minorsRows r) C := by
        ext ξ
        simp [hδ]
      rw [e]
      exact Submodule.sum_mem _ fun C _ => Submodule.smul_mem _ _ (minors_minor_mem _ _)
    have e : f = (fun ξ => minorsChi f (ξ.submatrix Fin.succ id)) +
        ∑ k ∈ Finset.range (min N m + 1), ∑ r, minorsPart r (γ k r) := by
      ext ξ
      simp [h44 ξ]
    rw [e]
    exact Submodule.add_mem _ (minors_tail_mem hχ)
      (Submodule.sum_mem _ fun k hk => Submodule.sum_mem _ fun r _ => hmem k hk r)

end Induction

/-- **A rank-one affine function is an affine combination of minors**: [D08], Theorem 5.20
(p. 179), the implication (ii) ⇒ (iii′). For a rank-one affine `f : ℝ^{d×m} → ℝ` there are
coefficients `a k r c` with `f (A) = ∑_{k ≤ min d m} ∑_{r, c} a k r c · minor A r c` for every `A`
(the `0 × 0` minor is the constant `1`, and its coefficient is `f (0)`). As in [D08], `f` is not
assumed continuous.

The proof is that of [D08], pp. 181–191, repaired as listed in the module docstring. If `d ≤ m`:
induction on the number of rows (`minors_mem_span`), in which `f` is affine in its first row
(5.42), the coefficients are combinations of minors of the other rows by the induction hypothesis
(5.43), the parts of `f` with a given set of other rows (5.44) are rank-one affine
(`minors_part_RA`), and Lemma 5.24 (`minors_part_eq_sum_minor`) writes each part as a combination of
minors that contain the first row. Otherwise, the result for `ξ ↦ f (ξᵀ)`: the minors of `Aᵀ` are
the minors of `A`. -/
theorem RankOneAffine.exists_eq_sum_minor {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : RankOneAffine f) :
    ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
      ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c := by
  have hRA : MinorsRA f := hf.add_smul_vecMulVec
  rcases le_total d m with hdm | hmd
  · exact minors_exists_coeff (minors_mem_span d hdm f hRA)
  · obtain ⟨a, ha⟩ := minors_exists_coeff (minors_mem_span m hmd _ (minors_transpose_RA hRA))
    refine ⟨fun k r c => a k c r, fun A => ?_⟩
    have h := ha Aᵀ
    rw [transpose_transpose] at h
    rw [h, min_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun c _ => ?_
    rw [minor, minor, ← det_transpose, transpose_submatrix, transpose_transpose]

end CalculusOfVariations
