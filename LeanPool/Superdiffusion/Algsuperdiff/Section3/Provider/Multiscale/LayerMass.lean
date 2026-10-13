/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SubadditiveDecomposition

/-!
# LayerMass

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Whitney layer mass, and the simplex-to-layer regrouping of Step 3

This module discharges the explicit layer-mass A obligation of
`Provider.Multiscale.ConclusionAssembly`, `LayerMassBound`, and supplies the
composition statement that carries the `[0,∞]` simplex sum of
`Multiscale.sum_of_a_decomp` (SubadditiveDecomposition.lean) into the layer
series of Step 3 of `p.bfA.multiscalebound`.

## What is proved

1. **The boundary-collar count** (`card_descendantsAtDepth_filter_touchesBoundary_le`):
   at most `2 d 3^{j(d-1)}` of the `3^{jd}` depth-`j` triadic descendants of
   `□_m` touch `∂□_m`.  The proof is a union bound over the `2d` faces, reduced
   by `card_descendantsAtDepth_filter_index_le` to the one-coordinate **slice
   count** `#{R ∈ descendantsAtDepth Q j : R.index i = c} ≤ 3^{j(d-1)}`, itself an
   induction on `j` from the single-generation fact that prescribing one index
   coordinate of a child forces one triadic digit.
   The naive recursion "a boundary cube has at most `3^d - 2^d` boundary
   children" is *not* enough: it gives the decay `(1 - (2/3)^d)^j`, not the
   `3^{-j}` the manuscript needs.  The union bound over faces is what produces
   `3^{-j}`.

2. **The layer mass bound** (`sum_cubeMassRatio_whitneyLayer_le`,
   `layerMassBound_six_mul_dim`): `𝒲(□_m,n)` carries mass at most `6 d 3^{-n}`
   inside `□_m`, i.e. `LayerMassBound d m hn (6 d)`.  Route: a layer-`n` cube is
   a depth-`(1+h_n)` descendant of a *touching* depth-`(n-1)` descendant of
   `□_m` (`whitneyLayer_subset_collar`), so
   ```
   # 𝒲(□_m,n) ≤ (2 d 3^{(n-1)(d-1)}) · (3^d)^{1+h_n} ,
   ```
   and each layer cube carries mass `(3^d)^{-(n+h_n)}`; the two powers collapse
   to `2 d 3^{-(n-1)} = 6 d 3^{-n}` exactly (`three_pow_collar_identity`).
   The constant `6 d` is the one the `ConclusionAssembly` docstring predicts.
   It is not claimed sharp: keeping the extra factor `2/3` from "a touching
   cube has at most `2 · 3^{d-1}` non-touching children" would give `4 d`,
   which for `d = 1, n ≥ 2` is the exact layer mass `4 · 3^{-n}` (at `n = 1` it
   is `3^{-1}` — one touching ancestor, not two;).  That refinement is not
   proved here — nothing downstream distinguishes `4 d` from `6 d`, since
   `layerSumConst` carries `Cmass` as a parameter.

3. **The simplex-to-layer regrouping** (`tsum_simplexPartition_eq_tsum_layer`,
   `toReal_tsum_simplexPartition_le_tsum`,
   `toReal_tsum_simplexPartition_le_payload`, and its `[0,∞]`-valued twin
   `tsum_simplexPartition_le_ofReal_payload` at the identical binder list):
   `SW(□_m)` is the disjoint union
   over `n` of the finite cell families `layerCells m hn n`, so any `[0,∞]`-valued
   sum over `SW(□_m)` regroups as `∑'_n ∑_{□ ∈ 𝒲(□_m,n)} ∑_{𝔰 ∈ S(□)}`, with no
   summability hypothesis.  Composed with `toReal` and with
   `ConclusionAssembly.tsum_layerContrib_le_payload` this is the missing link
   between the right-hand side of `e.sum-of-a-decomp` and the Step-3 payload.

## What is *not* proved

The **exact** boundary-touching count `3^{dt} - (3^t - 2)^d` is not proved.  It
needs the surjectivity half of the index-box bijection (every `u` with `|u i| ≤
E_t` is attained by a depth-`t` descendant of `□_m`), which no consumer in this
repository asks for: the layer mass bound consumes only the upper bound `2 d
3^{t(d-1)}`.  The injective half *is* proved
(`Provider.Whitney.index_injOn_descendantsAtDepth`,
`Provider.Whitney.index_mem_cubeFinset_of_mem_descendantsAtDepth`) and the
cardinality `#descendantsAtDepth Q t = 3^{dt}` is CoarseGraining's
`Homogenization.descendantsAtDepth_card`, restated here as
`card_descendantsAtDepth_originCube`.

## References

* ABK26, `sss.whitney.partition`; `p.bfA.multiscalebound` Step 3; `e.SW.def`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Whitney

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The cardinality of a depth-`t` descendant family -/

/-- **`#{□ ⊆ □_m : |□| = 3^{m-t}} = 3^{dt}`**, CoarseGraining's
`Homogenization.descendantsAtDepth_card` in the manuscript's exponent form.
Together with `Provider.Whitney.index_injOn_descendantsAtDepth` and
`Provider.Whitney.index_mem_cubeFinset_of_mem_descendantsAtDepth` this says the
depth-`t` descendants of `□_m` inject into the index box `{|u i| ≤ E_t}`, which
has the same cardinality `3^{dt}`; the surjectivity half is not needed below
and is not proved (see the module docstring). -/
theorem card_descendantsAtDepth_originCube (m : ℤ) (t : ℕ) :
    (descendantsAtDepth (originCube d m) t).card = 3 ^ (d * t) := by
  rw [descendantsAtDepth_card, pow_mul]

/-! ## The one-generation slice count -/

/-- Prescribing one index coordinate of a triadic child forces one of the `d`
triadic digits, so at most `3^{d-1}` of the `3^d` children of a cube have a
prescribed value in coordinate `i`. -/
theorem card_childCubes_filter_index_le (Q : TriadicCube d) (i : Fin d) (c : ℤ) :
    ((childCubes Q).filter (fun R => R.index i = c)).card ≤ 3 ^ (d - 1) := by
  classical
  set T : Finset (Fin d → Fin 3) :=
    Finset.univ.filter (fun digits : Fin d → Fin 3 =>
      3 * Q.index i + (digits i : ℤ) - 1 = c) with hT
  have hsub : (childCubes Q).filter (fun R => R.index i = c) ⊆
      T.image (fun digits : Fin d → Fin 3 =>
        ({ scale := Q.scale - 1
           index := fun j => 3 * Q.index j + (digits j : ℤ) - 1 } : TriadicCube d)) := by
    intro R hR
    rw [Finset.mem_filter] at hR
    obtain ⟨digits, rfl⟩ := mem_childCubes_iff.mp hR.1
    exact Finset.mem_image.mpr ⟨digits, by
      rw [hT, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hR.2⟩, rfl⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
  have hconst : ∀ f ∈ T, ∀ g ∈ T, f i = g i := by
    intro f hf g hg
    rw [hT, Finset.mem_filter] at hf hg
    have hfg : ((f i : ℕ) : ℤ) = ((g i : ℕ) : ℤ) := by omega
    exact Fin.ext (by exact_mod_cast hfg)
  have hinj : Set.InjOn
      (fun f : Fin d → Fin 3 => fun j : {j : Fin d // j ≠ i} => f j.1)
      (T : Set (Fin d → Fin 3)) := by
    intro f hf g hg hfg
    funext j
    by_cases hj : j = i
    · subst hj; exact hconst f hf g hg
    · exact congrFun hfg ⟨j, hj⟩
  have hcard := Finset.card_le_card_of_injOn
    (f := fun f : Fin d → Fin 3 => fun j : {j : Fin d // j ≠ i} => f j.1)
    (s := T) (t := (Finset.univ : Finset ({j : Fin d // j ≠ i} → Fin 3)))
    (fun f _ => Finset.mem_univ _) hinj
  refine hcard.trans_eq ?_
  rw [Finset.card_univ]
  have hsubty : Fintype.card {j : Fin d // j ≠ i} = d - 1 := by
    have h := Fintype.card_subtype_compl (p := fun j : Fin d => j = i)
    rw [Fintype.card_subtype_eq i, Fintype.card_fin] at h
    exact h
  rw [Fintype.card_fun, hsubty]
  simp

/-! ## The depth-`j` slice count -/

/-- **The slice count.**  At most `(3^{d-1})^j` of the `(3^d)^j` depth-`j`
descendants of a cube have a prescribed value in a fixed index coordinate. -/
theorem card_descendantsAtDepth_filter_index_le (Q : TriadicCube d) (i : Fin d) :
    ∀ (j : ℕ) (c : ℤ),
      ((descendantsAtDepth Q j).filter (fun R => R.index i = c)).card
        ≤ (3 ^ (d - 1)) ^ j := by
  classical
  intro j
  induction j with
  | zero =>
      intro c
      simp only [descendantsAtDepth_zero, pow_zero]
      exact le_trans (Finset.card_filter_le _ _) (by simp)
  | succ j ih =>
      intro c
      set q : ℤ := (c + 1) / 3 with hq
      have hsub : (descendantsAtDepth Q (j + 1)).filter (fun R => R.index i = c) ⊆
          ((descendantsAtDepth Q j).filter (fun S => S.index i = q)).biUnion
            (fun S => (childCubes S).filter (fun R => R.index i = c)) := by
        intro R hR
        rw [Finset.mem_filter, descendantsAtDepth_succ, Finset.mem_biUnion] at hR
        obtain ⟨⟨S, hS, hRS⟩, hRc⟩ := hR
        obtain ⟨digits, rfl⟩ := mem_childCubes_iff.mp hRS
        have hd : ((digits i : ℕ) : ℤ) < 3 := by exact_mod_cast (digits i).is_lt
        have hd0 : (0 : ℤ) ≤ ((digits i : ℕ) : ℤ) := Int.natCast_nonneg _
        have hRc' : 3 * S.index i + ((digits i : ℕ) : ℤ) - 1 = c := hRc
        have hSq : S.index i = q := by rw [hq]; omega
        exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, hSq⟩,
          Finset.mem_filter.mpr ⟨mem_childCubes_iff.mpr ⟨digits, rfl⟩, hRc⟩⟩
      refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
      calc ∑ S ∈ (descendantsAtDepth Q j).filter (fun S => S.index i = q),
              ((childCubes S).filter (fun R => R.index i = c)).card
          ≤ ∑ _S ∈ (descendantsAtDepth Q j).filter (fun S => S.index i = q),
              3 ^ (d - 1) :=
            Finset.sum_le_sum fun S _ => card_childCubes_filter_index_le S i c
        _ = ((descendantsAtDepth Q j).filter (fun S => S.index i = q)).card *
              3 ^ (d - 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (3 ^ (d - 1)) ^ j * 3 ^ (d - 1) := Nat.mul_le_mul_right _ (ih q)
        _ = (3 ^ (d - 1)) ^ (j + 1) := by rw [pow_succ]

/-! ## The boundary-collar count -/

/-- **The boundary-collar count.**  At most `2 d 3^{j(d-1)}` of the `3^{jd}`
depth-`j` triadic descendants of `□_m` touch `∂□_m`; equivalently the boundary
collar of `□_m` at scale `3^{m-j}` occupies volume fraction at most `2 d 3^{-j}`
(`sum_cubeMassRatio_boundaryCollar_le`).  This is the geometric source of the
`3^{-n}` of Step 3. -/
theorem card_descendantsAtDepth_filter_touchesBoundary_le (m : ℤ) (j : ℕ) :
    ((descendantsAtDepth (originCube d m) j).filter (TouchesBoundary m)).card
      ≤ 2 * d * (3 ^ (d - 1)) ^ j := by
  classical
  have hscale : ∀ R ∈ descendantsAtDepth (originCube d m) j, R.scale = m - (j : ℤ) := by
    intro R hR
    have h := scale_eq_sub_of_mem_descendantsAtDepth (Q := originCube d m) (n := j) hR
    simpa only [originCube] using h
  have hsub : (descendantsAtDepth (originCube d m) j).filter (TouchesBoundary m) ⊆
      (Finset.univ : Finset (Fin d)).biUnion fun i =>
        ((descendantsAtDepth (originCube d m) j).filter
            (fun R => R.index i = extremeIdx j)) ∪
        ((descendantsAtDepth (originCube d m) j).filter
            (fun R => R.index i = -extremeIdx j)) := by
    intro R hR
    rw [Finset.mem_filter] at hR
    obtain ⟨i, hi⟩ := hR.2
    rw [hscale R hR.1, rootExtreme_sub_natCast] at hi
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rcases hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hR.1, hi⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hR.1, hi⟩)
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  calc ∑ i ∈ (Finset.univ : Finset (Fin d)),
          (((descendantsAtDepth (originCube d m) j).filter
              (fun R => R.index i = extremeIdx j)) ∪
            ((descendantsAtDepth (originCube d m) j).filter
              (fun R => R.index i = -extremeIdx j))).card
      ≤ ∑ _i ∈ (Finset.univ : Finset (Fin d)), 2 * (3 ^ (d - 1)) ^ j := by
        refine Finset.sum_le_sum fun i _ => le_trans (Finset.card_union_le _ _) ?_
        have h1 := card_descendantsAtDepth_filter_index_le (originCube d m) i j
          (extremeIdx j)
        have h2 := card_descendantsAtDepth_filter_index_le (originCube d m) i j
          (-extremeIdx j)
        omega
    _ = d * (2 * (3 ^ (d - 1)) ^ j) := by rw [Finset.sum_const, smul_eq_mul]; simp
    _ = 2 * d * (3 ^ (d - 1)) ^ j := by ring

/-! ## The collapse arithmetic -/

/-- The exponent collapse behind every collar mass estimate: a collar of
`2 d 3^{p(d-1)}` cubes, each refined `t` further generations, contains
`2 d (3^d)^{p+t} / 3^p` cubes of depth `p+t`.  Stated as an identity in `ℕ`; the
factor `2 d` is what makes it true at `d = 0` as well (both sides vanish). -/
private theorem three_pow_collar_identity (d p t : ℕ) :
    2 * d * (3 ^ (d - 1)) ^ p * (3 ^ d) ^ t * 3 ^ p = 2 * d * (3 ^ d) ^ (p + t) := by
  match d with
  | 0 => simp
  | e + 1 =>
      have hb : 3 ^ (e + 1 - 1) * 3 = 3 ^ (e + 1) := by
        rw [Nat.add_sub_cancel, ← pow_succ]
      calc 2 * (e + 1) * (3 ^ (e + 1 - 1)) ^ p * (3 ^ (e + 1)) ^ t * 3 ^ p
          = 2 * (e + 1) * ((3 ^ (e + 1 - 1) * 3) ^ p) * (3 ^ (e + 1)) ^ t := by
            rw [mul_pow]; ring
        _ = 2 * (e + 1) * (3 ^ (e + 1)) ^ p * (3 ^ (e + 1)) ^ t := by rw [hb]
        _ = 2 * (e + 1) * (3 ^ (e + 1)) ^ (p + t) := by rw [pow_add]; ring

/-- The real-arithmetic core: a family of `c` cubes of depth `s` inside `□_m`,
with `c 3^p ≤ 2 d (3^d)^s`, carries mass at most `2 d 3^{-p}`. -/
private theorem collar_mass_arith {c p s : ℕ}
    (hc : c * 3 ^ p ≤ 2 * d * (3 ^ d) ^ s) :
    (c : ℝ) * ((((3 : ℝ)) ^ d) ^ s)⁻¹ ≤ 2 * (d : ℝ) * (3 : ℝ) ^ (-(p : ℝ)) := by
  have hA : (0 : ℝ) < ((3 : ℝ) ^ d) ^ s := by positivity
  have hB : (0 : ℝ) < (3 : ℝ) ^ p := by positivity
  have hR : (c : ℝ) * (3 : ℝ) ^ p ≤ 2 * (d : ℝ) * ((3 : ℝ) ^ d) ^ s := by
    have h := (Nat.cast_le (α := ℝ)).2 hc
    push_cast at h
    linarith
  have hrpow : (3 : ℝ) ^ (-(p : ℝ)) = ((3 : ℝ) ^ p)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  rw [hrpow]
  refine le_of_mul_le_mul_right ?_ (mul_pos hA hB)
  have h1 : (c : ℝ) * (((3 : ℝ) ^ d) ^ s)⁻¹ * (((3 : ℝ) ^ d) ^ s * (3 : ℝ) ^ p)
      = (c : ℝ) * (3 : ℝ) ^ p := by
    field_simp
  have h2 : 2 * (d : ℝ) * ((3 : ℝ) ^ p)⁻¹ * (((3 : ℝ) ^ d) ^ s * (3 : ℝ) ^ p)
      = 2 * (d : ℝ) * ((3 : ℝ) ^ d) ^ s := by
    field_simp
  rw [h1, h2]
  exact hR

/-! ## The mass of the boundary collar -/


/-! ## The Whitney layer sits in the depth-`(n-1)` collar -/

/-- A layer-`n` Whitney cube is a depth-`(1+h_n)` descendant of a
boundary-touching depth-`(n-1)` descendant of `□_m`. -/
theorem whitneyLayer_subset_collar (m : ℤ) (hn : ℕ → ℕ) (n : ℕ) :
    whitneyLayer (d := d) m hn n ⊆
      ((descendantsAtDepth (originCube d m) (n - 1)).filter (TouchesBoundary m)).biUnion
        fun A => descendantsAtDepth A (1 + hn n) := by
  classical
  intro Q hQ
  obtain ⟨-, A, hA, hAt, C, hC, -, hQC⟩ := mem_whitneyLayer_iff.mp hQ
  refine Finset.mem_biUnion.mpr ⟨A, Finset.mem_filter.mpr ⟨hA, hAt⟩, ?_⟩
  exact mem_descendantsAtDepth_add
    (show C ∈ descendantsAtDepth A 1 by rwa [descendantsAtDepth_one]) hQC

/-- The layer-`n` cube count: at most `2 d 3^{(n-1)(d-1)} (3^d)^{1+h_n}`. -/
theorem card_whitneyLayer_le (m : ℤ) (hn : ℕ → ℕ) (n : ℕ) :
    (whitneyLayer (d := d) m hn n).card
      ≤ 2 * d * (3 ^ (d - 1)) ^ (n - 1) * (3 ^ d) ^ (1 + hn n) := by
  classical
  refine le_trans (Finset.card_le_card (whitneyLayer_subset_collar m hn n))
    (le_trans Finset.card_biUnion_le ?_)
  calc ∑ A ∈ (descendantsAtDepth (originCube d m) (n - 1)).filter (TouchesBoundary m),
          (descendantsAtDepth A (1 + hn n)).card
      = ∑ _A ∈ (descendantsAtDepth (originCube d m) (n - 1)).filter (TouchesBoundary m),
          (3 ^ d) ^ (1 + hn n) :=
        Finset.sum_congr rfl fun A _ => descendantsAtDepth_card A (1 + hn n)
    _ = ((descendantsAtDepth (originCube d m) (n - 1)).filter (TouchesBoundary m)).card *
          (3 ^ d) ^ (1 + hn n) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * d * (3 ^ (d - 1)) ^ (n - 1)) * (3 ^ d) ^ (1 + hn n) :=
        Nat.mul_le_mul_right _
          (card_descendantsAtDepth_filter_touchesBoundary_le m (n - 1))

/-! ## The layer mass bound -/

/-- **The Whitney layer mass estimate.**  The layer-`n` cubes of `𝒲(□_m)` occupy
mass at most `6 d 3^{-n}` inside `□_m`.  Layer `0` is empty, so the bound is
trivial there. -/
theorem sum_cubeMassRatio_whitneyLayer_le (m : ℤ) (hn : ℕ → ℕ) (n : ℕ) :
    ∑ Q ∈ whitneyLayer (d := d) m hn n, cubeMassRatio (originCube d m) Q
      ≤ 6 * (d : ℝ) * (3 : ℝ) ^ (-(n : ℝ)) := by
  classical
  match n, (rfl : n = n) with
  | 0, _ =>
      rw [whitneyLayer_zero, Finset.sum_empty]
      positivity
  | (p + 1), _ =>
      have hconst : ∀ Q ∈ whitneyLayer (d := d) m hn (p + 1),
          cubeMassRatio (originCube d m) Q
            = ((((3 : ℝ)) ^ d) ^ (p + 1 + hn (p + 1)))⁻¹ := fun Q hQ =>
        cubeMassRatio_of_mem_descendantsAtDepth
          (mem_descendantsAtDepth_of_mem_whitneyLayer hQ)
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcount : (whitneyLayer (d := d) m hn (p + 1)).card * 3 ^ p
          ≤ 2 * d * (3 ^ d) ^ (p + 1 + hn (p + 1)) := by
        have hid := three_pow_collar_identity d p (1 + hn (p + 1))
        have hstep := card_whitneyLayer_le (d := d) m hn (p + 1)
        simp only [Nat.add_sub_cancel] at hstep
        calc (whitneyLayer (d := d) m hn (p + 1)).card * 3 ^ p
            ≤ 2 * d * (3 ^ (d - 1)) ^ p * (3 ^ d) ^ (1 + hn (p + 1)) * 3 ^ p :=
              Nat.mul_le_mul_right _ hstep
          _ = 2 * d * (3 ^ d) ^ (p + (1 + hn (p + 1))) := hid
          _ = 2 * d * (3 ^ d) ^ (p + 1 + hn (p + 1)) := by
              rw [show p + (1 + hn (p + 1)) = p + 1 + hn (p + 1) from by omega]
      refine le_trans (collar_mass_arith hcount) (le_of_eq ?_)
      have hrp : (3 : ℝ) ^ (-(p : ℝ)) = ((3 : ℝ) ^ p)⁻¹ := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
      have hrn : (3 : ℝ) ^ (-((p + 1 : ℕ) : ℝ)) = ((3 : ℝ) ^ (p + 1))⁻¹ := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
      have h3 : ((3 : ℝ) ^ p) ≠ 0 := by positivity
      rw [hrp, hrn, pow_succ]
      field_simp
      ring


/-! ## Step 3 at the discharged layer-mass input -/


/-! ## The simplex-to-layer regrouping bridge -/

/-- **The layer-`n` cells of `SW(□_m)`**: the simplices of `e.SW.def` cut out of
the layer-`n` Whitney cubes.  `SW(□_m)` is the union of these finite families
over `n` (`simplexPartition_eq_iUnion_layerCells`). -/
def layerCells (m : ℤ) (hn : ℕ → ℕ) (n : ℕ) : Finset (KuhnCell d) :=
  (whitneyLayer m hn n).biUnion (whitneySimplexCells m hn n)

theorem mem_layerCells_iff {m : ℤ} {hn : ℕ → ℕ} {n : ℕ} {T : KuhnCell d} :
    T ∈ layerCells m hn n ↔
      ∃ Q ∈ whitneyLayer (d := d) m hn n, T ∈ whitneySimplexCells m hn n Q := by
  rw [layerCells, Finset.mem_biUnion]

theorem simplexPartition_eq_iUnion_layerCells (m : ℤ) (hn : ℕ → ℕ) :
    simplexPartition (d := d) m hn =
      ⋃ n : ℕ, ((layerCells m hn n : Finset (KuhnCell d)) : Set (KuhnCell d)) := by
  ext T
  simp only [Set.mem_iUnion, Finset.mem_coe, mem_layerCells_iff, mem_simplexPartition_iff]

/-- Within one layer the cell families of distinct Whitney cubes are disjoint:
a cell determines the Whitney cube containing it (`whitneyCubeOf`). -/
theorem pairwiseDisjoint_whitneySimplexCells (m : ℤ) (hn : ℕ → ℕ) (n : ℕ) :
    ((whitneyLayer (d := d) m hn n : Finset (TriadicCube d)) :
        Set (TriadicCube d)).PairwiseDisjoint (whitneySimplexCells m hn n) := by
  intro Q hQ Q' hQ' hne
  simp only [Function.onFun]
  refine Finset.disjoint_left.mpr fun T hT hT' => ?_
  have h1 := whitneyCubeOf_of_mem_whitneySimplexCells (Finset.mem_coe.mp hQ) hT
  have h2 := whitneyCubeOf_of_mem_whitneySimplexCells (Finset.mem_coe.mp hQ') hT'
  exact hne (by rw [← h1, h2])

/-- Distinct layers of `SW(□_m)` are disjoint.  A cell determines its Whitney cube,
and a Whitney cube determines its layer once the scale profile is monotone
(`Provider.Whitney.whitneyLayer_disjoint`). -/
theorem pairwiseDisjoint_layerCells {m : ℤ} {hn : ℕ → ℕ} (hmono : Monotone hn) :
    Set.univ.PairwiseDisjoint fun n : ℕ =>
      ((layerCells (d := d) m hn n : Finset (KuhnCell d)) : Set (KuhnCell d)) := by
  intro n _ n' _ hne
  simp only [Function.onFun]
  refine Set.disjoint_left.mpr fun T hT hT' => ?_
  obtain ⟨Q, hQ, hTQ⟩ := mem_layerCells_iff.mp (Finset.mem_coe.mp hT)
  obtain ⟨Q', hQ', hTQ'⟩ := mem_layerCells_iff.mp (Finset.mem_coe.mp hT')
  have h1 := whitneyCubeOf_of_mem_whitneySimplexCells hQ hTQ
  have h2 := whitneyCubeOf_of_mem_whitneySimplexCells hQ' hTQ'
  have hQQ : Q = Q' := by rw [← h1, h2]
  subst hQQ
  exact Finset.disjoint_left.mp (whitneyLayer_disjoint hmono hne) hQ hQ'

/-- **The regrouping of a `[0,∞]` sum over `SW(□_m)` into the Whitney layer
series.**  `SW(□_m)` is the *disjoint* union over `n` of the finite families
`layerCells m hn n`, so any `[0,∞]`-valued sum over it equals the iterated sum

```
∑'_n  ∑_{□ ∈ 𝒲(□_m,n)}  ∑_{𝔰 ∈ S_{m-(n+1)-h_{n+1}}(□)}  f 𝔰 ,
```

with no summability hypothesis: in `[0,∞]` every family is summable and
rearrangement is unconditional.  This is the composition statement between the
right-hand side of `Multiscale.sum_of_a_decomp` (SubadditiveDecomposition.lean)
and the layer series of Step 3. -/
theorem tsum_simplexPartition_eq_tsum_layer {m : ℤ} {hn : ℕ → ℕ}
    (hmono : Monotone hn) (f : KuhnCell d → ℝ≥0∞) :
    ∑' T : ↥(simplexPartition (d := d) m hn), f T
      = ∑' n : ℕ, ∑ Q ∈ whitneyLayer (d := d) m hn n,
          ∑ T ∈ whitneySimplexCells m hn n Q, f T := by
  classical
  calc ∑' T : ↥(simplexPartition (d := d) m hn), f T
      = ∑' T, Set.indicator (simplexPartition (d := d) m hn) f T := tsum_subtype _ _
    _ = ∑' T, Set.indicator
          (⋃ n : ℕ, ((layerCells (d := d) m hn n : Finset (KuhnCell d)) :
            Set (KuhnCell d))) f T := by
          rw [simplexPartition_eq_iUnion_layerCells]
    _ = ∑' T : ↥(⋃ n : ℕ, ((layerCells (d := d) m hn n : Finset (KuhnCell d)) :
            Set (KuhnCell d))), f T := (tsum_subtype _ _).symm
    _ = ∑' (n : ℕ) (T : ↥((layerCells (d := d) m hn n : Finset (KuhnCell d)) :
            Set (KuhnCell d))), f T :=
          ENNReal.tsum_biUnion (pairwiseDisjoint_layerCells hmono)
    _ = ∑' n : ℕ, ∑ T ∈ layerCells (d := d) m hn n, f T :=
          tsum_congr fun n => Finset.tsum_subtype' _ _
    _ = ∑' n : ℕ, ∑ Q ∈ whitneyLayer (d := d) m hn n,
          ∑ T ∈ whitneySimplexCells m hn n Q, f T :=
          tsum_congr fun n =>
            Finset.sum_biUnion (pairwiseDisjoint_whitneySimplexCells m hn n)

/-- **The regrouping bridge with `toReal`.**  A per-layer real majorant of the
`[0,∞]` cell sums controls the real value of the whole simplex sum by the real
layer series.  The finiteness needed for `toReal` is produced by the majorant,
not assumed. -/
theorem toReal_tsum_simplexPartition_le_tsum {m : ℤ} {hn : ℕ → ℕ}
    (hmono : Monotone hn) (f : KuhnCell d → ℝ≥0∞) {g : ℕ → ℝ}
    (hg0 : ∀ n : ℕ, 0 ≤ g n) (hgsum : Summable g)
    (hlayer : ∀ n : ℕ, ∑ Q ∈ whitneyLayer (d := d) m hn n,
        ∑ T ∈ whitneySimplexCells m hn n Q, f T ≤ ENNReal.ofReal (g n)) :
    (∑' T : ↥(simplexPartition (d := d) m hn), f T).toReal ≤ ∑' n : ℕ, g n := by
  refine ENNReal.toReal_le_of_le_ofReal (tsum_nonneg hg0) ?_
  rw [tsum_simplexPartition_eq_tsum_layer hmono f,
    ENNReal.ofReal_tsum_of_nonneg hg0 hgsum]
  exact ENNReal.tsum_le_tsum hlayer


/-- **The Step-3 composition in `[0,∞]`** --- the `ofReal` twin of
`toReal_tsum_simplexPartition_le_payload`, at the identical binder list. -/
theorem tsum_simplexPartition_le_ofReal_payload {m : ℤ} {hn : ℕ → ℕ}
    {b γ ε Cmass Ktot Ccol : ℝ} {hs k₀ : ℕ} {Mass Bad : ℕ → ℝ}
    (hmono : Monotone hn) (hb0 : 0 < b) (hb9 : 9 * b ≤ 1) (hγ0 : 0 ≤ γ)
    (hγ : 4 * γ ≤ 1 - b) (hK : 0 ≤ Ktot) (hC : 0 ≤ Ccol) (hCmass : 0 ≤ Cmass)
    (hε0 : 0 ≤ ε) (hεk0 : ε ≤ Real.exp (-(k₀ : ℝ)))
    (hMass0 : ∀ j : ℕ, 0 ≤ Mass j) (hBad0 : ∀ j : ℕ, 0 ≤ Bad j)
    (hMass : ∀ j : ℕ, Mass j ≤ Cmass * (3 : ℝ) ^ (-(j : ℝ)))
    (hBadMass : ∀ j : ℕ, Bad j ≤ Cmass * (3 : ℝ) ^ (-(j : ℝ)))
    (hBadDens : ∀ j : ℕ, Bad j ≤ ε + (3 : ℝ) ^ (-(layerQuantity b hs k₀ j / 2)))
    (f : KuhnCell d → ℝ≥0∞)
    (hlayer : ∀ n : ℕ, ∑ Q ∈ whitneyLayer (d := d) m hn n,
        ∑ T ∈ whitneySimplexCells m hn n Q, f T
      ≤ ENNReal.ofReal (layerContrib b γ hs k₀ Ktot Ccol Mass Bad n)) :
    ∑' T : ↥(simplexPartition (d := d) m hn), f T
      ≤ ENNReal.ofReal (layerSumConst b γ k₀ Ktot Ccol Cmass *
          ((3 : ℝ) ^ (γ * (hs : ℝ)) *
            (1 + (3 : ℝ) ^ (2 * b * (hs : ℝ)) * Real.exp (-((k₀ : ℝ) / 36))))) := by
  rw [tsum_simplexPartition_eq_tsum_layer hmono f]
  calc ∑' n : ℕ, ∑ Q ∈ whitneyLayer (d := d) m hn n,
        ∑ T ∈ whitneySimplexCells m hn n Q, f T
      ≤ ∑' n : ℕ, ENNReal.ofReal (layerContrib b γ hs k₀ Ktot Ccol Mass Bad n) :=
        ENNReal.tsum_le_tsum hlayer
    _ = ENNReal.ofReal (∑' n : ℕ, layerContrib b γ hs k₀ Ktot Ccol Mass Bad n) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun n => layerContrib_nonneg hK hC hMass0 hBad0 n)
          (summable_layerContrib hb0 hb9 hγ0 hγ hK hC hCmass hε0 hMass0 hBad0 hMass
            hBadMass hBadDens)).symm
    _ ≤ ENNReal.ofReal (layerSumConst b γ k₀ Ktot Ccol Cmass *
          ((3 : ℝ) ^ (γ * (hs : ℝ)) *
            (1 + (3 : ℝ) ^ (2 * b * (hs : ℝ)) * Real.exp (-((k₀ : ℝ) / 36))))) :=
        ENNReal.ofReal_le_ofReal
          (tsum_layerContrib_le_payload hb0 hb9 hγ0 hγ hK hC hCmass hε0 hεk0 hMass0
            hBad0 hMass hBadMass hBadDens)

end

end Algsuperdiff.Section3.Provider.Multiscale
