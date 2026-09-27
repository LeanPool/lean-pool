/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the coarse-cell reduction of the coupled residual to the box allocation

This file carries out the reduction announced in `Nibble.BoxAllocationSpec`:

  `Nibble.AX1.BoxAllocationResidual → Nibble.AX1.BlockCoverResidualCoupled`.

The construction, at a regularity scale `ε₁` and a relative block size `α` chosen by the residual:

* cut every cluster into coarse cells of length `l = ⌈2α·mmax⌉`, `P = ⌊mmin/l⌋` of them per cluster,
  and set the block scale to `τ = l·K/δ` with `K = ⌈64/ε⌉ + 1`;
* take a **sparse feasible point** `y` of the cluster-triple LP whose value dominates `ν₃*`
  (`Nibble.AX1.exists_sparse_clusterTripleLP_nu3star`) and discard the triples using a cluster pair
  of density below `δ` — that costs at most `δ|V|²/2 ≤ ε|V|²/2`
  (`Nibble.AX1.sum_sparse_triples_le`);
* make `⌊(1-ε/8)·y_th /(τ²·d₁d₂d₃)⌋` **copies** of every surviving cluster triple, each demanding
  `⌈K·d/δ⌉ ≤ ⌈K/δ⌉` coarse cells in each of its three clusters, the opposite density `d` deciding
  the size.  The pair capacities of the LP say exactly that the demand of every cluster pair is
  below `(1-ε/64)P²`, so `Nibble.AX1.BoxAllocationResidual` places all copies but a set of total
  area `≤ (ε/64)·(#clusters)²·P²`;
* `Nibble.AX1.exists_gridSubTriple_family_of_placement` turns the placement into the family of block
  sub-triples, and `Nibble.AX1.nu3star_le_cover_of_family_lp_value` compares its covering sum with
  the LP value.

* `Nibble.AX1.blockCoverResidualCoupled_of_boxAllocation` — the reduction;
* `Nibble.AX1.ax1_of_boxAllocation` — AX1 from the box allocation, through
  `Nibble.AX1.ax1_of_blockCoverCoupled`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BoxAllocationSpec
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoarseCellAssembly
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.ClusterTripleLPCount
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapBlockCoverCoupled
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BlockCoverUniformAux

/-! # CoarseCellCoupled -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE


namespace Nibble.AX1

/-! ### The three positions of a cluster triple -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every element of `ZMod 3` is `0`, `1` or `2`. -/
theorem zmod3_cases (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by revert a; decide

/-! ### Copies -/

/-- **The copies of the elements of `Gd`**: `n th` copies of `th`. -/
def copySet {ι : Type} [DecidableEq ι] (Gd : Finset ι) (n : ι → ℕ) : Finset (ι × ℕ) :=
  Gd.biUnion (fun th => (Finset.range (n th)).image (fun j => (th, j)))

theorem mem_copySet {ι : Type} [DecidableEq ι] {Gd : Finset ι} {n : ι → ℕ} {p : ι × ℕ} :
    p ∈ copySet Gd n ↔ p.1 ∈ Gd ∧ p.2 < n p.1 := by
  classical
  constructor
  · intro hp
    obtain ⟨th, hth, hp'⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hp'
    rw [← hEq]
    exact ⟨hth, Finset.mem_range.mp hj⟩
  · rintro ⟨h1, h2⟩
    refine Finset.mem_biUnion.mpr ⟨p.1, h1, Finset.mem_image.mpr ⟨p.2, Finset.mem_range.mpr h2, ?_⟩⟩
    rfl

theorem sum_copySet {ι : Type} [DecidableEq ι] {M : Type} [AddCommMonoid M] (Gd : Finset ι)
    (n : ι → ℕ) (f : ι → M) :
    ∑ p ∈ copySet Gd n, f p.1 = ∑ th ∈ Gd, (n th) • f th := by
  classical
  rw [copySet, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun th _ => ?_
    rw [Finset.sum_image (by intro i _ j _ h; exact (Prod.mk.injEq _ _ _ _ ▸ h).2)]
    simp
  · intro th _ th' _ hne
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_range]
    rintro p ⟨j, -, rfl⟩ ⟨j', -, hEq⟩
    exact hne (congrArg Prod.fst hEq).symm

theorem card_copySet {ι : Type} [DecidableEq ι] (Gd : Finset ι) (n : ι → ℕ) :
    #(copySet Gd n) = ∑ th ∈ Gd, n th := by
  have h := sum_copySet (M := ℕ) Gd n (fun _ => 1)
  simpa using h

variable (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
  [Nonempty {S : Finset V // S ∈ Pp.parts}]

/-- **The three positions of a cluster triple**, indexed by `ZMod 3`. -/
noncomputable def triPos (th : Finset {S : Finset V // S ∈ Pp.parts}) (a : ZMod 3) :
    {S : Finset V // S ∈ Pp.parts} :=
  if a = 0 then (pick3 th).1 else if a = 1 then (pick3 th).2.1 else (pick3 th).2.2

theorem triPos_mem {th : Finset {S : Finset V // S ∈ Pp.parts}} (h3 : #th = 3) (a : ZMod 3) :
    triPos Pp th a ∈ th := by
  obtain ⟨h0, h1, h2⟩ := pick3_mem h3
  rcases zmod3_cases a with rfl | rfl | rfl
  · simpa [triPos] using h0
  · simpa [triPos] using h1
  · have h20 : (2 : ZMod 3) ≠ 0 := by decide
    have h21 : (2 : ZMod 3) ≠ 1 := by decide
    simpa [triPos, h20, h21] using h2

theorem triPos_injective {th : Finset {S : Finset V // S ∈ Pp.parts}} (h3 : #th = 3) :
    Function.Injective (triPos Pp th) := by
  obtain ⟨hab, hac, hbc, -⟩ := pick3_spec h3
  intro a b hEq
  rcases zmod3_cases a with rfl | rfl | rfl <;> rcases zmod3_cases b with rfl | rfl | rfl <;>
    simp only [triPos, ite_eq_left, reduceIte] at hEq ⊢ <;> first
      | rfl
      | (exfalso; first
          | exact hab hEq | exact hab hEq.symm | exact hac hEq | exact hac hEq.symm
          | exact hbc hEq | exact hbc hEq.symm)

/-- **The density of the cluster pair opposite to the position `a`.** -/
noncomputable def dOpp (th : Finset {S : Finset V // S ∈ Pp.parts}) (a : ZMod 3) : ℝ :=
  (G.edgeDensity (triPos Pp th (a + 1) : Finset V) (triPos Pp th (a + 2) : Finset V) : ℝ)

/-- **The density product of a cluster triple.** -/
noncomputable def dProd (th : Finset {S : Finset V // S ∈ Pp.parts}) : ℝ :=
  dOpp G Pp th 0 * dOpp G Pp th 1 * dOpp G Pp th 2

theorem dOpp_nonneg (th : Finset {S : Finset V // S ∈ Pp.parts}) (a : ZMod 3) :
    0 ≤ dOpp G Pp th a := by
  rw [dOpp]
  exact_mod_cast G.edgeDensity_nonneg _ _

theorem dOpp_le_one (th : Finset {S : Finset V // S ∈ Pp.parts}) (a : ZMod 3) :
    dOpp G Pp th a ≤ 1 := by
  rw [dOpp]
  exact_mod_cast G.edgeDensity_le_one _ _

theorem dOpp_zero (th : Finset {S : Finset V // S ∈ Pp.parts}) :
    dOpp G Pp th 0
      = (G.edgeDensity (triPos Pp th 1 : Finset V) (triPos Pp th 2 : Finset V) : ℝ) := by
  rw [dOpp, show ((0 : ZMod 3) + 1) = 1 from by decide +kernel, show ((0 : ZMod 3) + 2) = 2 from by decide +kernel]

theorem dOpp_one (th : Finset {S : Finset V // S ∈ Pp.parts}) :
    dOpp G Pp th 1
      = (G.edgeDensity (triPos Pp th 2 : Finset V) (triPos Pp th 0 : Finset V) : ℝ) := by
  rw [dOpp, show ((1 : ZMod 3) + 1) = 2 from by decide +kernel, show ((1 : ZMod 3) + 2) = 0 from by decide +kernel]

theorem dOpp_two (th : Finset {S : Finset V // S ∈ Pp.parts}) :
    dOpp G Pp th 2
      = (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 1 : Finset V) : ℝ) := by
  rw [dOpp, show ((2 : ZMod 3) + 1) = 0 from by decide +kernel, show ((2 : ZMod 3) + 2) = 1 from by decide +kernel]

/-- The density product read off the three positions in their natural order. -/
theorem dProd_eq (th : Finset {S : Finset V // S ∈ Pp.parts}) :
    dProd G Pp th
      = (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 1 : Finset V) : ℝ)
        * (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 2 : Finset V) : ℝ)
        * (G.edgeDensity (triPos Pp th 1 : Finset V) (triPos Pp th 2 : Finset V) : ℝ) := by
  have h20 : (G.edgeDensity (triPos Pp th 2 : Finset V) (triPos Pp th 0 : Finset V) : ℝ)
      = (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 2 : Finset V) : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  rw [dProd, dOpp_zero, dOpp_one, dOpp_two, h20]
  ring

/-- **The three opposite densities of a triple, seen from two of its positions.**  For two distinct
positions `a`, `b` the density of the pair `(a, b)` is the density opposite to the third position,
so the three factors multiply out to the density product. -/
theorem dOpp_mul_dOpp_mul_dens (th : Finset {S : Finset V // S ∈ Pp.parts}) {a b : ZMod 3}
    (hab : a ≠ b) :
    dOpp G Pp th a * dOpp G Pp th b
        * (G.edgeDensity (triPos Pp th a : Finset V) (triPos Pp th b : Finset V) : ℝ)
      = dProd G Pp th := by
  have h10 : (G.edgeDensity (triPos Pp th 1 : Finset V) (triPos Pp th 0 : Finset V) : ℝ)
      = (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 1 : Finset V) : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  have h20 : (G.edgeDensity (triPos Pp th 2 : Finset V) (triPos Pp th 0 : Finset V) : ℝ)
      = (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 2 : Finset V) : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  have h21 : (G.edgeDensity (triPos Pp th 2 : Finset V) (triPos Pp th 1 : Finset V) : ℝ)
      = (G.edgeDensity (triPos Pp th 1 : Finset V) (triPos Pp th 2 : Finset V) : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  rcases zmod3_cases a with rfl | rfl | rfl <;> rcases zmod3_cases b with rfl | rfl | rfl <;>
      first
        | (exact absurd rfl hab)
        | (simp only [dProd, dOpp_zero, dOpp_one, dOpp_two, h10, h20, h21]; try ring)


/-! ### Arithmetic of the parameters -/

/-- The small-box restriction `s₀ ≤ θ·P`, from `α ≤ θδ/(16K)`. -/
private theorem small_box_bound {θ δ α Kr Pn s₀ : ℝ} (hθ0 : 0 < θ) (hδ0 : 0 < δ)
    (hα0 : 0 < α) (hK1 : 1 ≤ Kr) (hαθ : 16 * Kr * α ≤ θ * δ) (hPn : 1 / (4 * α) ≤ Pn)
    (hs₀ : s₀ ≤ 2 * (Kr / δ)) : s₀ ≤ θ * Pn := by
  have hPnα : (1 : ℝ) ≤ 4 * α * Pn := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * α)] at hPn
    linarith only [hPn]
  have h5 : 4 * α * (4 * Kr) ≤ 4 * α * (θ * δ * Pn) := by
    nlinarith [mul_le_mul_of_nonneg_left hPnα (mul_nonneg hθ0.le hδ0.le)]
  have h6 : 4 * Kr ≤ θ * δ * Pn := le_of_mul_le_mul_left h5 (by positivity)
  have h7 : 2 * (Kr / δ) ≤ θ * Pn := by
    have e : 2 * (Kr / δ) = 2 * Kr / δ := by ring
    rw [e, div_le_iff₀ hδ0]
    linarith only [hK1, h6]
  linarith only [hs₀, h7]

/-- The density product of three densities above `δ`. -/
private theorem prod_ge_cube {d a b c : ℝ} (hd : 0 < d) (ha : d ≤ a) (hb : d ≤ b) (hc : d ≤ c) :
    d ^ 3 ≤ a * b * c := by
  have hab : d * d ≤ a * b := mul_le_mul ha hb hd.le (hd.le.trans ha)
  have : d * d * d ≤ a * b * c :=
    mul_le_mul hab hc hd.le (mul_nonneg (hd.le.trans ha) (hd.le.trans hb))
  linarith only [this]

/-- The density product of three densities below `1`. -/
private theorem prod_le_one {a b c : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) : a * b * c ≤ 1 :=
  mul_le_one₀ (mul_le_one₀ ha hb0 hb) hc0 hc

/-- The block of a copy is at least `α` times the size of its cluster. -/
private theorem bs_ge_alpha {lr Kr al mmaxr t : ℝ} (hl : 2 * al * mmaxr ≤ lr) (hK : 1 ≤ Kr)
    (hlK : lr * Kr ≤ t) (hmmax : 0 ≤ mmaxr) (hal : 0 ≤ al) : al * mmaxr ≤ t := by
  have h0 : 0 ≤ al * mmaxr := mul_nonneg hal hmmax
  have hlr0 : 0 ≤ lr := by linarith only [hl, h0]
  have h1 : lr ≤ lr * Kr := le_mul_of_one_le_right hlr0 hK
  linarith only [hl, hlK, hlr0, h1]

/-- **The demand of one copy in one ordered cluster pair.**  A copy occupies the pair through at
most one pair of positions, so the double sum of the demand collapses to a single product. -/
private theorem sum_pair_indicator {ι : Type} [DecidableEq ι] {f : ZMod 3 → ι}
    (hf : Function.Injective f) {S T : ι} {w : ZMod 3 → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ a b : ZMod 3, f a = S → f b = T → w a * w b ≤ M) :
    ∑ a : ZMod 3, ∑ b : ZMod 3, (if f a = S ∧ f b = T then w a * w b else 0) ≤ M := by
  classical
  by_cases hS : ∃ a, f a = S
  · obtain ⟨a₀, ha₀⟩ := hS
    by_cases hT : ∃ b, f b = T
    · obtain ⟨b₀, hb₀⟩ := hT
      have hEq : ∑ a : ZMod 3, ∑ b : ZMod 3, (if f a = S ∧ f b = T then w a * w b else 0)
          = w a₀ * w b₀ := by
        rw [Finset.sum_eq_single a₀]
        · rw [Finset.sum_eq_single b₀]
          · rw [ite_eq_left ⟨ha₀, hb₀⟩]
          · intro b _ hb
            refine ite_eq_right ?_
            rintro ⟨-, h2⟩
            exact hb (hf (h2.trans hb₀.symm))
          · intro h; exact absurd (Finset.mem_univ b₀) h
        · intro a _ ha
          refine Finset.sum_eq_zero fun b _ => ite_eq_right ?_
          rintro ⟨h1, -⟩
          exact ha (hf (h1.trans ha₀.symm))
        · intro h; exact absurd (Finset.mem_univ a₀) h
      rw [hEq]
      exact hM a₀ b₀ ha₀ hb₀
    · push Not at hT
      have h0 : ∀ a : ZMod 3, ∑ b : ZMod 3, (if f a = S ∧ f b = T then w a * w b else 0) = 0 :=
        fun a => Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => hT b h.2)
      rw [Finset.sum_congr rfl (fun a _ => h0 a)]
      simpa using hM0
  · push Not at hS
    have h0 : ∀ a : ZMod 3, ∑ b : ZMod 3, (if f a = S ∧ f b = T then w a * w b else 0) = 0 :=
      fun a => Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => hS a h.1)
    rw [Finset.sum_congr rfl (fun a _ => h0 a)]
    simpa using hM0

/-- The demand of all the copies of one cluster triple in one ordered cluster pair, against the LP
weight of the triple. -/
private theorem copy_pair_bound {en Kr lr del dP cST ncr yv : ℝ}
    (hdel : 0 < del) (hl : 0 < lr) (hK : 0 < Kr) (hc : 0 < cST) (hdP : 0 < dP)
    (hnc : ncr ≤ (1 - en) * yv * del ^ 2 / (lr ^ 2 * Kr ^ 2 * dP)) :
    ncr * ((1 + 1 / Kr) ^ 2 * Kr ^ 2 * dP / (del ^ 2 * cST))
      ≤ (1 - en) * (1 + 1 / Kr) ^ 2 / (lr ^ 2 * cST) * yv := by
  have hM0 : 0 ≤ (1 + 1 / Kr) ^ 2 * Kr ^ 2 * dP / (del ^ 2 * cST) := by positivity
  refine (mul_le_mul_of_nonneg_right hnc hM0).trans_eq ?_
  field_simp

/-- Two prescribed sizes multiply out to at most `(1 + 1/K)²` times their ideal value. -/
private theorem sz_prod_bound {Kr del da db sa sb : ℝ} (hdel : 0 < del) (hK : 0 < Kr)
    (hda : del ≤ da) (hdb : del ≤ db) (hsa : sa < Kr * da / del + 1) (hsb : sb < Kr * db / del + 1)
    (hsb0 : 0 ≤ sb) :
    sa * sb ≤ (1 + 1 / Kr) ^ 2 * (Kr ^ 2 * (da * db) / del ^ 2) := by
  have hd1 : 1 ≤ da / del := (one_le_div hdel).mpr hda
  have hd2 : 1 ≤ db / del := (one_le_div hdel).mpr hdb
  have h1 : sa ≤ (1 + 1 / Kr) * (Kr * da / del) := by
    have he : (1 + 1 / Kr) * (Kr * da / del) = Kr * da / del + da / del := by field_simp
    rw [he]; linarith only [hsa, hd1]
  have h2 : sb ≤ (1 + 1 / Kr) * (Kr * db / del) := by
    have he : (1 + 1 / Kr) * (Kr * db / del) = Kr * db / del + db / del := by field_simp
    rw [he]; linarith only [hsb, hd2]
  calc sa * sb ≤ ((1 + 1 / Kr) * (Kr * da / del)) * ((1 + 1 / Kr) * (Kr * db / del)) := by
        refine mul_le_mul h1 h2 hsb0 ?_
        have : 0 ≤ da := le_trans hdel.le hda
        positivity
    _ = (1 + 1 / Kr) ^ 2 * (Kr ^ 2 * (da * db) / del ^ 2) := by field_simp

/-- The margin of the pair capacity: the two relative losses `1/K` and `2/P` are absorbed by the
factor `1 - e/8` of the number of copies. -/
private theorem capacity_core {en u v : ℝ} (he0 : 0 < en) (he1 : en ≤ 1) (hu0 : 0 ≤ u)
    (hu : u ≤ en / 640) (hv0 : 0 ≤ v) (hv : v ≤ en / 400) :
    (1 - en / 8) * ((1 + u) * (1 + v)) ^ 2 ≤ 1 - en / 64 := by
  have hs : (1 + u) * (1 + v) ≤ 1 + en / 200 := by nlinarith only [he1, hu, hv0, hv]
  have hs0 : (0:ℝ) ≤ (1 + u) * (1 + v) := by nlinarith only [hu0, hv0]
  have hsq : ((1 + u) * (1 + v)) ^ 2 ≤ (1 + en / 200) ^ 2 := by nlinarith only [hs, hs0]
  have h8 : (0:ℝ) ≤ 1 - en / 8 := by linarith only [he1]
  have hmul := mul_le_mul_of_nonneg_left hsq h8
  have hen2 : en ^ 2 ≤ en := by nlinarith only [he0, he1]
  have hen3 : (0:ℝ) ≤ en ^ 3 := by positivity
  have key : (1 - en / 8) * (1 + en / 200) ^ 2 ≤ 1 - en / 64 := by nlinarith only [hen2]
  linarith only [hmul, key]

/-- **The pair capacity of the coarse-cell grid.** -/
private theorem capacity_bound {en u Pnr lr mmaxr : ℝ} (he0 : 0 < en) (he1 : en ≤ 1)
    (hu0 : 0 ≤ u) (hu : u ≤ en / 640) (hP0 : 0 < Pnr) (hl0 : 0 < lr)
    (hv : 2 / Pnr ≤ en / 400) (hmm0 : 0 ≤ mmaxr) (hmm : mmaxr ≤ (Pnr + 2) * lr) :
    (1 - en / 8) * (1 + u) ^ 2 * mmaxr ^ 2 ≤ (1 - en / 64) * (Pnr * lr) ^ 2 := by
  have hv0 : (0:ℝ) ≤ 2 / Pnr := by positivity
  have hPv : Pnr * (1 + 2 / Pnr) = Pnr + 2 := by field_simp
  have hmm2 : mmaxr ^ 2 ≤ (Pnr * (1 + 2 / Pnr)) ^ 2 * lr ^ 2 := by
    rw [hPv]; nlinarith only [hmm0, hmm]
  have hcore := capacity_core he0 he1 hu0 hu hv0 hv
  have hnn : (0:ℝ) ≤ (1 - en / 8) * (1 + u) ^ 2 := by nlinarith only [he1]
  calc (1 - en / 8) * (1 + u) ^ 2 * mmaxr ^ 2
      ≤ (1 - en / 8) * (1 + u) ^ 2 * ((Pnr * (1 + 2 / Pnr)) ^ 2 * lr ^ 2) :=
        mul_le_mul_of_nonneg_left hmm2 hnn
    _ = ((1 - en / 8) * ((1 + u) * (1 + 2 / Pnr)) ^ 2) * (Pnr * lr) ^ 2 := by ring
    _ ≤ (1 - en / 64) * (Pnr * lr) ^ 2 := mul_le_mul_of_nonneg_right hcore (by positivity)

/-- **The pair capacity of the cluster pair, transported to the grid of the pair.** -/
private theorem cap_to_Pn {en Kr lr cST cardS cardT Pnr mmaxr : ℝ}
    (he0 : 0 < en) (he1 : en ≤ 1) (hK : 0 < Kr) (hl : 0 < lr) (hc : 0 < cST)
    (hu : 1 / Kr ≤ en / 640) (hP0 : 0 < Pnr) (hv : 2 / Pnr ≤ en / 400)
    (hmm0 : 0 ≤ mmaxr) (hmm : mmaxr ≤ (Pnr + 2) * lr)
    (hS : cardS ≤ mmaxr) (hT : cardT ≤ mmaxr) (hT0 : 0 ≤ cardT) :
    (1 - en / 8) * (1 + 1 / Kr) ^ 2 / (lr ^ 2 * cST) * (cST * cardS * cardT)
      ≤ (1 - en / 64) * Pnr ^ 2 := by
  have hprod : cardS * cardT ≤ mmaxr ^ 2 := by nlinarith only [hS, hT, hT0]
  have hbase := capacity_bound he0 he1 (by positivity : (0:ℝ) ≤ 1 / Kr) hu hP0 hl hv hmm0 hmm
  have hnn : (0:ℝ) ≤ (1 - en / 8) * (1 + 1 / Kr) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hA : (1 - en / 8) * (1 + 1 / Kr) ^ 2 / (lr ^ 2 * cST) * (cST * cardS * cardT)
      = (1 - en / 8) * (1 + 1 / Kr) ^ 2 * (cardS * cardT) / lr ^ 2 := by
    field_simp
  rw [hA]
  have h1 : (1 - en / 8) * (1 + 1 / Kr) ^ 2 * (cardS * cardT)
      ≤ (1 - en / 8) * (1 + 1 / Kr) ^ 2 * mmaxr ^ 2 := mul_le_mul_of_nonneg_left hprod hnn
  refine le_trans ((div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < lr ^ 2)).mpr
    (le_trans h1 hbase)) (le_of_eq ?_)
  field_simp

/-- The value of an unplaced copy against the cell area it demands. -/
private theorem bad_term_bound {lr Kr del d0 d1 d2 s0 s1 : ℝ} (hdel : 0 < del) (hK0 : 0 ≤ Kr)
    (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd2' : d2 ≤ 1)
    (h0 : Kr * d0 / del ≤ s0) (h1 : Kr * d1 / del ≤ s1) :
    lr ^ 2 * Kr ^ 2 / del ^ 2 * (d0 * d1 * d2) ≤ lr ^ 2 * (s0 * s1) := by
  have hnn0 : (0:ℝ) ≤ Kr * d0 / del := by positivity
  have hnn1 : (0:ℝ) ≤ Kr * d1 / del := by positivity
  have hprod : (Kr * d0 / del) * (Kr * d1 / del) ≤ s0 * s1 :=
    mul_le_mul h0 h1 hnn1 (le_trans hnn0 h0)
  have hs0 : (0:ℝ) ≤ s0 * s1 := le_trans (mul_nonneg hnn0 hnn1) hprod
  have key : lr ^ 2 * Kr ^ 2 / del ^ 2 * (d0 * d1 * d2)
      = lr ^ 2 * ((Kr * d0 / del) * (Kr * d1 / del) * d2) := by
    field_simp
  rw [key]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg lr)
  calc (Kr * d0 / del) * (Kr * d1 / del) * d2 ≤ (s0 * s1) * d2 :=
        mul_le_mul_of_nonneg_right hprod hd2
    _ ≤ s0 * s1 := by nlinarith only [hd2', hs0]

/-- The total block area of the construction is a small fraction of `|V|²`. -/
private theorem kp_tau_sq {kt en epsr nr : ℝ} (h0 : 0 ≤ kt) (h : kt ≤ 3 * en / 32 * nr)
    (he0 : 0 < en) (he1 : en ≤ 1) (heps : en ≤ epsr) :
    kt ^ 2 ≤ epsr * nr ^ 2 / 16 := by
  have h1 : kt ^ 2 ≤ (3 * en / 32 * nr) ^ 2 := pow_le_pow_left₀ h0 h 2
  have he2 : en ^ 2 ≤ epsr := le_trans (by nlinarith) heps
  nlinarith [mul_nonneg (sq_nonneg nr) (by linarith : (0:ℝ) ≤ 64 * epsr - 9 * en ^ 2)]

/-- The margin `k·(2τ + 1)` of the covering clause. -/
private theorem k_tau_bound {kr taur nr del epsr : ℝ} (hk0 : 0 ≤ kr) (htau1 : 1 ≤ taur)
    (hdel : 0 < del) (hk : kr * (6 * taur ^ 2 * del ^ 3) ≤ nr ^ 2)
    (htau : 192 / (epsr * del ^ 3) ≤ taur) (heps : 0 < epsr) :
    kr * (2 * taur + 1) ≤ epsr * nr ^ 2 / 8 := by
  have hde : (192:ℝ) ≤ taur * (epsr * del ^ 3) := by
    rw [div_le_iff₀ (by positivity)] at htau
    linarith only [htau]
  have hk' : kr ≤ nr ^ 2 / (6 * taur ^ 2 * del ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [hk]
  have h3 : kr * (2 * taur + 1) ≤ 3 * taur * kr := by nlinarith only [hk0, htau1]
  have h4 : 3 * taur * kr ≤ 3 * taur * (nr ^ 2 / (6 * taur ^ 2 * del ^ 3)) :=
    mul_le_mul_of_nonneg_left hk' (by positivity)
  have h5 : 3 * taur * (nr ^ 2 / (6 * taur ^ 2 * del ^ 3)) = nr ^ 2 / (2 * taur * del ^ 3) := by
    field_simp
    ring
  have h6 : nr ^ 2 / (2 * taur * del ^ 3) ≤ epsr * nr ^ 2 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [mul_nonneg (by linarith : (0:ℝ) ≤ taur * (epsr * del ^ 3) - 4) (sq_nonneg nr)]
  linarith only [h3, h4, h5, h6]

/-! ### The reduction -/
private theorem copied_mass_lower_bound {ι : Type} [DecidableEq ι]
    (Gd : Finset ι) (nc : ι → ℕ) (y d : ι → ℝ) (e τ : ℝ)
    (hτ : 0 < τ) (hdpos : ∀ th ∈ Gd, 0 < d th) (hdle : ∀ th, d th ≤ 1)
    (hfloor : ∀ th, nc th = ⌊(1 - e / 8) * y th / (τ ^ 2 * d th)⌋₊) :
    (1 - e / 8) * (∑ th ∈ Gd, y th) - (#Gd : ℝ) * τ ^ 2
      ≤ ∑ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * d c.1.1 := by
  classical
  have hall : ∑ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * d c.1.1
      = ∑ th ∈ Gd, nc th • (τ ^ 2 * d th) := by
    rw [Finset.sum_coe_sort (copySet Gd nc) (fun p => τ ^ 2 * d p.1)]
    exact sum_copySet Gd nc (fun th => τ ^ 2 * d th)
  have hallLB : (1 - e / 8) * (∑ th ∈ Gd, y th) - (#Gd : ℝ) * τ ^ 2
      ≤ ∑ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * d c.1.1 := by
    rw [hall]
    have hterm : ∀ th ∈ Gd, (1 - e / 8) * y th - τ ^ 2 ≤ nc th • (τ ^ 2 * d th) := by
      intro th hth
      rw [nsmul_eq_mul]
      have hdp := hdpos th hth
      have hpos : (0 : ℝ) < τ ^ 2 * d th := by positivity
      have hZ : (1 - e / 8) * y th / (τ ^ 2 * d th) - 1 ≤ (nc th : ℝ) := by
        rw [hfloor th]
        linarith only [Nat.lt_floor_add_one ((1 - e / 8) * y th / (τ ^ 2 * d th))]
      have hmul := mul_le_mul_of_nonneg_right hZ hpos.le
      have heq : ((1 - e / 8) * y th / (τ ^ 2 * d th) - 1) * (τ ^ 2 * d th)
          = (1 - e / 8) * y th - τ ^ 2 * d th := by
        field_simp
      rw [heq] at hmul
      have hdle : τ ^ 2 * d th ≤ τ ^ 2 := by
        have h1 : τ ^ 2 * d th ≤ τ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (hdle th) (sq_nonneg τ)
        linarith
      linarith
    have hexp : ∑ th ∈ Gd, ((1 - e / 8) * y th - τ ^ 2)
        = (1 - e / 8) * (∑ th ∈ Gd, y th) - (#Gd : ℝ) * τ ^ 2 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [← hexp]
    exact Finset.sum_le_sum hterm
  exact hallLB

private theorem dense_support_value_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    (δ : ℝ) (y : Finset {S : Finset V // S ∈ Pp.parts} → ℝ)
    (hy0 : ∀ th, 0 ≤ y th) :
    clusterLPValue y - ∑ th ∈ sparseTriples G Pp δ, y th
      ≤ ∑ th ∈ clusterLPSupport y \ sparseTriples G Pp δ, y th := by
  classical
  let Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}) :=
    clusterLPSupport y \ sparseTriples G Pp δ
  have hGdsum : clusterLPValue y - ∑ th ∈ sparseTriples G Pp δ, y th ≤ ∑ th ∈ Gd, y th := by
    have hsplit : ∑ th ∈ univ \ Gd, y th + ∑ th ∈ Gd, y th = clusterLPValue y :=
      Finset.sum_sdiff (Finset.subset_univ Gd)
    have hle : ∑ th ∈ univ \ Gd, y th ≤ ∑ th ∈ sparseTriples G Pp δ, y th := by
      have hpt : ∀ th ∈ univ \ Gd, y th ≤ (if th ∈ sparseTriples G Pp δ then y th else 0) := by
        intro th hth
        by_cases hs : th ∈ sparseTriples G Pp δ
        · rw [ite_eq_left hs]
        · rw [ite_eq_right hs]
          have hy0 : y th = 0 := by
            by_contra hne
            exact (Finset.mem_sdiff.mp hth).2 (Finset.mem_sdiff.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, hs⟩)
          rw [hy0]
      refine le_trans (Finset.sum_le_sum hpt) ?_
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun th _ _ => by split; exacts [hy0 th, le_refl 0])) ?_
      rw [← Finset.sum_filter]
      apply le_of_eq
      congr 1
      simp
    linarith
  exact hGdsum

private theorem pair_product_le_cyclic_sum (z : ZMod 3 → ℕ) :
    (z 0 : ℝ) * (z 1 : ℝ) ≤ ∑ a : ZMod 3, (z a : ℝ) * (z (a + 1) : ℝ) := by
  have h := Finset.single_le_sum
    (f := fun a : ZMod 3 => (z a : ℝ) * (z (a + 1) : ℝ))
    (fun a _ => by positivity) (Finset.mem_univ (0 : ZMod 3))
  simpa using h

private theorem box_demand_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (ε₁ δ e : ℝ) (K l Pn mmax : ℕ)
    (y : Finset {S : Finset V // S ∈ Pp.parts} → ℝ)
    (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}))
    (szf : Finset {S : Finset V // S ∈ Pp.parts} → ZMod 3 → ℕ)
    (nc : Finset {S : Finset V // S ∈ Pp.parts} → ℕ)
    (he0 : 0 < e) (he1 : e ≤ 1) (hδ0 : 0 < δ)
    (hyLP : IsClusterTripleLP G Pp (ε₁ / 8) (ε₁ / 4) y)
    (hGdcard : ∀ th ∈ Gd, #th = 3)
    (hGddense : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
      δ ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
    (hposne : ∀ (th : Finset {S : Finset V // S ∈ Pp.parts}), #th = 3 →
      ∀ a b : ZMod 3, a ≠ b → triPos Pp th a ≠ triPos Pp th b)
    (hdProd0 : ∀ th ∈ Gd, 0 < dProd G Pp th)
    (hdOppδ : ∀ th ∈ Gd, ∀ a : ZMod 3, δ ≤ dOpp G Pp th a)
    (hszUB : ∀ th a, (szf th a : ℝ) < (K : ℝ) * dOpp G Pp th a / δ + 1)
    (hncUB : ∀ th ∈ Gd, (nc th : ℝ)
      ≤ (1 - e / 8) * y th * δ ^ 2 /
        ((l : ℝ) ^ 2 * (K : ℝ) ^ 2 * dProd G Pp th))
    (hKpos : (0 : ℝ) < (K : ℝ)) (hl0R : (0 : ℝ) < (l : ℝ))
    (hKu : 1 / (K : ℝ) ≤ e / 640) (hPn0R : (0 : ℝ) < (Pn : ℝ))
    (hPv : 2 / (Pn : ℝ) ≤ e / 400) (hmmax0R : (0 : ℝ) < (mmax : ℝ))
    (hmmPn : (mmax : ℝ) ≤ ((Pn : ℝ) + 2) * (l : ℝ))
    (hcardle : ∀ S ∈ Pp.parts, #S ≤ mmax) :
    ∀ S T : {S : Finset V // S ∈ Pp.parts}, S ≠ T →
      boxDemand (fun (c : {p // p ∈ copySet Gd nc}) a => triPos Pp c.1.1 a)
        (fun (c : {p // p ∈ copySet Gd nc}) a => szf c.1.1 a) S T
        ≤ (1 - e / 64) * (Pn : ℝ) ^ 2 := by
  classical
  intro S T hST
  have hbd : boxDemand (fun (c : {p // p ∈ copySet Gd nc}) a => triPos Pp c.1.1 a) (fun (c : {p // p ∈ copySet Gd nc}) a => szf c.1.1 a) S T
      = ∑ th ∈ Gd, (nc th) • (∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp th a = S ∧ triPos Pp th b = T then
            (szf th a : ℝ) * (szf th b : ℝ) else 0) := by
    have h1 : boxDemand (fun (c : {p // p ∈ copySet Gd nc}) a => triPos Pp c.1.1 a) (fun (c : {p // p ∈ copySet Gd nc}) a => szf c.1.1 a) S T
        = ∑ p ∈ copySet Gd nc, (∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp p.1 a = S ∧ triPos Pp p.1 b = T then
            (szf p.1 a : ℝ) * (szf p.1 b : ℝ) else 0) := by
      simp only [boxDemand]
      exact Finset.sum_coe_sort (copySet Gd nc)
        (fun p => ∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp p.1 a = S ∧ triPos Pp p.1 b = T then
            (szf p.1 a : ℝ) * (szf p.1 b : ℝ) else 0)
    rw [h1]
    exact sum_copySet Gd nc (fun th => ∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp th a = S ∧ triPos Pp th b = T then
            (szf th a : ℝ) * (szf th b : ℝ) else 0)
  rw [hbd]
  have hPnnn : (0 : ℝ) ≤ (1 - e / 64) * (Pn : ℝ) ^ 2 :=
    mul_nonneg (by linarith) (by positivity)
  -- a copy of a triple through the pair forces the pair to be dense
  have hnotmem : ∀ th ∈ Gd, ∀ a b : ZMod 3, triPos Pp th a = S → triPos Pp th b = T →
      a ≠ b ∧ δ ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) := by
    intro th hth a b ha hb
    have hab : a ≠ b := by
      intro h
      exact hST (by rw [← ha, ← hb, h])
    refine ⟨hab, ?_⟩
    have hd := hGddense th hth (triPos Pp th a) (triPos_mem Pp (hGdcard th hth) a)
      (triPos Pp th b) (triPos_mem Pp (hGdcard th hth) b) (hposne th (hGdcard th hth) a b hab)
    rwa [ha, hb] at hd
  by_cases hcST : (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) < δ
  · -- no copy uses a sparse pair
    have hzero : ∀ th ∈ Gd, (nc th) • (∑ a : ZMod 3, ∑ b : ZMod 3,
        if triPos Pp th a = S ∧ triPos Pp th b = T then
          (szf th a : ℝ) * (szf th b : ℝ) else 0) = 0 := by
      intro th hth
      have : (∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp th a = S ∧ triPos Pp th b = T then
            (szf th a : ℝ) * (szf th b : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ite_eq_right ?_
        rintro ⟨ha, hb⟩
        exact absurd (hnotmem th hth a b ha hb).2 (not_le.mpr hcST)
      rw [this, smul_zero]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    exact hPnnn
  · push Not at hcST
    have hc0 : (0 : ℝ) < (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) :=
      lt_of_lt_of_le hδ0 hcST
    -- the bound of one triple
    have hterm : ∀ th ∈ Gd, (nc th) • (∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp th a = S ∧ triPos Pp th b = T then
            (szf th a : ℝ) * (szf th b : ℝ) else 0)
        ≤ (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
            / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
          * (if S ∈ th ∧ T ∈ th then y th else 0) := by
      intro th hth
      have hdp := hdProd0 th hth
      by_cases hmem : S ∈ th ∧ T ∈ th
      · rw [ite_eq_left hmem, nsmul_eq_mul]
        have hM0 : (0 : ℝ) ≤ (1 + 1 / (K : ℝ)) ^ 2 * (K : ℝ) ^ 2 * dProd G Pp th
            / (δ ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ)) := by positivity
        have hinner : (∑ a : ZMod 3, ∑ b : ZMod 3,
            if triPos Pp th a = S ∧ triPos Pp th b = T then
              (szf th a : ℝ) * (szf th b : ℝ) else 0)
            ≤ (1 + 1 / (K : ℝ)) ^ 2 * (K : ℝ) ^ 2 * dProd G Pp th
              / (δ ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ)) := by
          refine sum_pair_indicator (triPos_injective Pp (hGdcard th hth)) hM0 ?_
          intro a b ha hb
          have hab := (hnotmem th hth a b ha hb).1
          have hprod : dOpp G Pp th a * dOpp G Pp th b
              * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) = dProd G Pp th := by
            have h := dOpp_mul_dOpp_mul_dens G Pp th hab
            rwa [ha, hb] at h
          have h1 := sz_prod_bound hδ0 hKpos (hdOppδ th hth a) (hdOppδ th hth b)
            (hszUB th a) (hszUB th b) (Nat.cast_nonneg _)
          refine le_trans h1 (le_of_eq ?_)
          rw [← hprod]
          field_simp
        refine le_trans (mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)) ?_
        exact copy_pair_bound hδ0 hl0R hKpos hc0 hdp (hncUB th hth)
      · rw [ite_eq_right hmem]
        have hz : (∑ a : ZMod 3, ∑ b : ZMod 3,
            if triPos Pp th a = S ∧ triPos Pp th b = T then
              (szf th a : ℝ) * (szf th b : ℝ) else 0) = 0 := by
          refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ite_eq_right ?_
          rintro ⟨ha, hb⟩
          refine hmem ⟨?_, ?_⟩
          · rw [← ha]; exact triPos_mem Pp (hGdcard th hth) a
          · rw [← hb]; exact triPos_mem Pp (hGdcard th hth) b
        rw [hz, smul_zero, mul_zero]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    -- the LP capacity of the pair
    have hWc0 : (0 : ℝ) ≤ (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
        / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ)) := by
      have : (0:ℝ) ≤ 1 - e / 8 := by linarith
      positivity
    have hstep1 : ∑ th ∈ Gd, (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
          / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
          * (if S ∈ th ∧ T ∈ th then y th else 0)
        ≤ ∑ th, (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
          / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
          * (if S ∈ th ∧ T ∈ th then y th else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun th _ _ => ?_
      refine mul_nonneg hWc0 ?_
      split
      · exact hyLP.1 th
      · exact le_refl 0
    have hstep2 : ∑ th, (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
          / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
          * (if S ∈ th ∧ T ∈ th then y th else 0)
        = (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
          / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
          * ∑ th ∈ triplesThrough Pp S T, y th := by
      rw [← Finset.mul_sum]
      congr 1
      rw [triplesThrough, Finset.sum_filter]
    refine le_trans hstep1 (le_trans (le_of_eq hstep2) ?_)
    refine le_trans (mul_le_mul_of_nonneg_left (hyLP.2.2 S T hST) hWc0) ?_
    rw [clusterPairCap]
    have hcS : (#(S : Finset V) : ℝ) ≤ (mmax : ℝ) := by exact_mod_cast hcardle _ S.2
    have hcT : (#(T : Finset V) : ℝ) ≤ (mmax : ℝ) := by exact_mod_cast hcardle _ T.2
    exact cap_to_Pn he0 he1 hKpos hl0R hc0 hKu hPn0R hPv hmmax0R.le hmmPn hcS hcT
      (Nat.cast_nonneg _)


private theorem coarse_cover_clause {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (ε ε₁ δ e α τ : ℝ) (K kp mmin l Pn Cn k : ℕ)
    (y : Finset {S : Finset V // S ∈ Pp.parts} → ℝ)
    (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}))
    (nc : Finset {S : Finset V // S ∈ Pp.parts} → ℕ)
    (bad Good : Finset {p // p ∈ copySet Gd nc})
    (szc : {p // p ∈ copySet Gd nc} → ZMod 3 → ℕ)
    (U W X A B C : ℕ → Finset V)
    (hkpN : 0 < kp) (hkpdef : kp = #Pp.parts)
    (hmmin0 : 0 < mmin) (hnlo : kp * mmin ≤ Fintype.card V)
    (hyLP : IsClusterTripleLP G Pp (ε₁ / 8) (ε₁ / 4) y)
    (hysupp : #(clusterLPSupport y) ≤ kp ^ 2)
    (hynu : nu3star (G.regularityReduced Pp (ε₁ / 8) (ε₁ / 4))
      ≤ clusterLPValue y + 1)
    (hδ0 : 0 < δ)
    (hGddef : Gd = clusterLPSupport y \ sparseTriples G Pp δ)
    (hsumGood : (∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
        * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ)))
      = ∑ c ∈ Good, τ ^ 2 * dProd G Pp c.1.1)
    (hτ0 : 0 < τ)
    (hdProd0 : ∀ th ∈ Gd, 0 < dProd G Pp th)
    (hdProdUB : ∀ th, dProd G Pp th ≤ 1)
    (hncdef : nc = fun th => ⌊(1 - e / 8) * y th / (τ ^ 2 * dProd G Pp th)⌋₊)
    (hbadterm : ∀ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * dProd G Pp c.1.1
      ≤ (l : ℝ) ^ 2 * ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ))
    (hIbad : (∑ c ∈ bad, ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ))
      ≤ e / 64 * (Fintype.card {S : Finset V // S ∈ Pp.parts} : ℝ) ^ 2 * (Pn : ℝ) ^ 2)
    (hPnl : Pn * l ≤ mmin)
    (hGooddef : Good = (univ : Finset {p // p ∈ copySet Gd nc}) \ bad)
    (hkle : k ≤ #Good)
    (hdProdLB : ∀ th ∈ Gd, δ ^ 3 ≤ dProd G Pp th)
    (hτ1 : (1 : ℝ) ≤ τ) (hτ192 : 192 / (ε * δ ^ 3) ≤ τ)
    (hε : 0 < ε) (hτdef : τ = (l : ℝ) * (K : ℝ) / δ)
    (hl3 : (l : ℝ) ≤ 3 * α * (mmin : ℝ)) (hKpos : (0 : ℝ) < (K : ℝ))
    (hα0 : 0 < α)
    (hαδ : α ≤ δ * e / (32 * K))
    (he0 : 0 < e) (he1 : e ≤ 1) (heε : e ≤ ε)
    (hCndef : Cn = ⌈16 / ε⌉₊) (hnCn : Cn ≤ Fintype.card V) (hδε : δ ≤ ε)
    (hgrid : ∀ i < k, IsGridSubTriple G Pp (ε₁ / 8) δ α τ
      (U i) (W i) (X i) (A i) (B i) (C i)) :
    nu3star (G.regularityReduced Pp (ε₁ / 8) (ε₁ / 4))
      ≤ (∑ i ∈ Finset.range k,
          ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))) / 3
        + ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  -- ### the covering clause
  have hcardV0 : 0 < Fintype.card V := lt_of_lt_of_le (Nat.mul_pos hkpN hmmin0) hnlo
  have hn0R : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hcardV0
  have hLPle : 6 * clusterLPValue y ≤ (Fintype.card V : ℝ) ^ 2 :=
    clusterLPValue_le_sq G Pp (ε₁ / 8) (ε₁ / 4) hyLP
  have hLP0 : 0 ≤ clusterLPValue y := Finset.sum_nonneg fun th _ => hyLP.1 th
  have hSs0 : 0 ≤ ∑ th ∈ sparseTriples G Pp δ, y th :=
    Finset.sum_nonneg fun th _ => hyLP.1 th
  have hsparse : 2 * ∑ th ∈ sparseTriples G Pp δ, y th ≤ δ * (Fintype.card V : ℝ) ^ 2 :=
    sum_sparse_triples_le G Pp (ε₁ / 8) (ε₁ / 4) hδ0.le hyLP
  have hGdsum : clusterLPValue y - ∑ th ∈ sparseTriples G Pp δ, y th ≤ ∑ th ∈ Gd, y th := by
    simpa only [hGddef] using dense_support_value_le G Pp δ y hyLP.1
  -- the value of the placed copies
  have hallLB : (1 - e / 8) * (∑ th ∈ Gd, y th) - (#Gd : ℝ) * τ ^ 2
      ≤ ∑ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * dProd G Pp c.1.1 := by
    exact copied_mass_lower_bound Gd nc y (dProd G Pp) e τ hτ0 hdProd0 hdProdUB
      (fun th => hncdef ▸ rfl)
  -- the copies that could not be placed
  have hkpcard : (Fintype.card {S : Finset V // S ∈ Pp.parts} : ℝ) = (kp : ℝ) := by
    rw [Fintype.card_coe, hkpdef]
  have hbadsum : ∑ c ∈ bad, τ ^ 2 * dProd G Pp c.1.1 ≤ e / 64 * (Fintype.card V : ℝ) ^ 2 := by
    have h1 : ∑ c ∈ bad, τ ^ 2 * dProd G Pp c.1.1
        ≤ ∑ c ∈ bad, (l : ℝ) ^ 2 * ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ) :=
      Finset.sum_le_sum fun c _ => hbadterm c
    have h1' : ∑ c ∈ bad, (l : ℝ) ^ 2 * ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ)
        = (l : ℝ) ^ 2 * ∑ c ∈ bad, ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    rw [h1'] at h1
    have h2 : (l : ℝ) ^ 2 * (∑ c ∈ bad, ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ))
        ≤ (l : ℝ) ^ 2 * (e / 64 * (kp : ℝ) ^ 2 * (Pn : ℝ) ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [← hkpcard]
      exact hIbad
    have hkPl : (kp : ℝ) * ((Pn : ℝ) * (l : ℝ)) ≤ (Fintype.card V : ℝ) := by
      have h : kp * (Pn * l) ≤ Fintype.card V := le_trans (Nat.mul_le_mul_left kp hPnl) hnlo
      exact_mod_cast h
    have hsq : ((kp : ℝ) * ((Pn : ℝ) * (l : ℝ))) ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hkPl 2
    have heq : (l : ℝ) ^ 2 * (e / 64 * (kp : ℝ) ^ 2 * (Pn : ℝ) ^ 2)
        = e / 64 * ((kp : ℝ) * ((Pn : ℝ) * (l : ℝ))) ^ 2 := by ring
    rw [heq] at h2
    have h3 : e / 64 * ((kp : ℝ) * ((Pn : ℝ) * (l : ℝ))) ^ 2
        ≤ e / 64 * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith
  have hGoodsum : ∑ c ∈ Good, τ ^ 2 * dProd G Pp c.1.1
      = (∑ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * dProd G Pp c.1.1)
        - ∑ c ∈ bad, τ ^ 2 * dProd G Pp c.1.1 := by
    rw [hGooddef, Finset.sum_sdiff_eq_sub (Finset.subset_univ bad)]
  -- the feasible point is recovered by the family
  have hGdcardle : (#Gd : ℝ) ≤ (kp : ℝ) ^ 2 := by
    have h2 : #Gd ≤ #(clusterLPSupport y) := by
      rw [hGddef]
      exact Finset.card_le_card Finset.sdiff_subset
    have h3 : #Gd ≤ kp ^ 2 := le_trans h2 hysupp
    exact_mod_cast h3
  have hGdtau : (#Gd : ℝ) * τ ^ 2 ≤ (kp : ℝ) ^ 2 * τ ^ 2 :=
    mul_le_mul_of_nonneg_right hGdcardle (sq_nonneg _)
  have hA4 : e / 8 * clusterLPValue y ≤ e * (Fintype.card V : ℝ) ^ 2 / 48 := by
    have h1 : clusterLPValue y ≤ (Fintype.card V : ℝ) ^ 2 / 6 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ e / 8)
    linarith
  have hA1 : (1 - e / 8) * (clusterLPValue y - ∑ th ∈ sparseTriples G Pp δ, y th)
      ≤ (1 - e / 8) * (∑ th ∈ Gd, y th) := mul_le_mul_of_nonneg_left hGdsum (by linarith)
  have hA3 : 0 ≤ e / 8 * ∑ th ∈ sparseTriples G Pp δ, y th := mul_nonneg (by linarith) hSs0
  have hval : clusterLPValue y
      ≤ (∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
          * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ)))
        + (e * (Fintype.card V : ℝ) ^ 2 / 48 + δ * (Fintype.card V : ℝ) ^ 2 / 2
            + (kp : ℝ) ^ 2 * τ ^ 2 + e / 64 * (Fintype.card V : ℝ) ^ 2) := by
    rw [hsumGood, hGoodsum]
    linarith
  -- ### the error budget
  have hkκ : (k : ℝ) ≤ ∑ th ∈ Gd, (nc th : ℝ) := by
    have h2 : #Good ≤ #(copySet Gd nc) := by
      have h := Finset.card_le_univ Good
      rwa [Fintype.card_coe] at h
    have h3 : #(copySet Gd nc) = ∑ th ∈ Gd, nc th := card_copySet Gd nc
    have h4 : k ≤ ∑ th ∈ Gd, nc th := by omega
    calc (k : ℝ) ≤ ((∑ th ∈ Gd, nc th : ℕ) : ℝ) := by exact_mod_cast h4
      _ = ∑ th ∈ Gd, (nc th : ℝ) := by push_cast; rfl
  have hncy : ∀ th ∈ Gd, (nc th : ℝ) * (τ ^ 2 * δ ^ 3) ≤ y th := by
    intro th hth
    have hdp := hdProd0 th hth
    have hy0 : (0 : ℝ) ≤ y th := hyLP.1 th
    have hZ : (nc th : ℝ) ≤ (1 - e / 8) * y th / (τ ^ 2 * dProd G Pp th) := by
      rw [hncdef]
      refine Nat.floor_le ?_
      apply div_nonneg (mul_nonneg (by linarith) hy0)
      positivity
    have h1 : (nc th : ℝ) * (τ ^ 2 * dProd G Pp th) ≤ (1 - e / 8) * y th := by
      have h := mul_le_mul_of_nonneg_right hZ (by positivity : (0:ℝ) ≤ τ ^ 2 * dProd G Pp th)
      rwa [div_mul_cancel₀ _ (by positivity : (τ ^ 2 * dProd G Pp th) ≠ 0)] at h
    have h2 : (nc th : ℝ) * (τ ^ 2 * δ ^ 3) ≤ (nc th : ℝ) * (τ ^ 2 * dProd G Pp th) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (hdProdLB th hth) (sq_nonneg τ)
    have h3 : (1 - e / 8) * y th ≤ y th := by
      have h4 : (0:ℝ) ≤ e / 8 * y th := mul_nonneg (by linarith) hy0
      linarith
    linarith
  have hksum : (k : ℝ) * (6 * τ ^ 2 * δ ^ 3) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have h1 : (∑ th ∈ Gd, (nc th : ℝ)) * (τ ^ 2 * δ ^ 3) ≤ ∑ th ∈ Gd, y th := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hncy
    have h2 : ∑ th ∈ Gd, y th ≤ clusterLPValue y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun th _ _ => hyLP.1 th
    have h3 : (k : ℝ) * (τ ^ 2 * δ ^ 3) ≤ (∑ th ∈ Gd, (nc th : ℝ)) * (τ ^ 2 * δ ^ 3) :=
      mul_le_mul_of_nonneg_right hkκ (by positivity)
    linarith
  have hkbound : (k : ℝ) * (2 * τ + 1) ≤ ε * (Fintype.card V : ℝ) ^ 2 / 8 :=
    k_tau_bound (Nat.cast_nonneg _) hτ1 hδ0 hksum hτ192 hε
  have hτmmin : τ ≤ 3 * α * (K : ℝ) / δ * (mmin : ℝ) := by
    rw [hτdef, div_le_iff₀ hδ0]
    have h1 : (l : ℝ) * (K : ℝ) ≤ 3 * α * (mmin : ℝ) * (K : ℝ) :=
      mul_le_mul_of_nonneg_right hl3 hKpos.le
    have h2 : 3 * α * (K : ℝ) / δ * (mmin : ℝ) * δ = 3 * α * (mmin : ℝ) * (K : ℝ) := by
      field_simp
    rw [h2]
    exact h1
  have hkpτ : (kp : ℝ) * τ ≤ 3 * e / 32 * (Fintype.card V : ℝ) := by
    have hx0 : (0 : ℝ) ≤ 3 * α * (K : ℝ) / δ := by positivity
    have h1 : (kp : ℝ) * τ ≤ (kp : ℝ) * (3 * α * (K : ℝ) / δ * (mmin : ℝ)) :=
      mul_le_mul_of_nonneg_left hτmmin (Nat.cast_nonneg _)
    have h2 : (kp : ℝ) * (mmin : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hnlo
    have h3 : (kp : ℝ) * (3 * α * (K : ℝ) / δ * (mmin : ℝ))
        = (3 * α * (K : ℝ) / δ) * ((kp : ℝ) * (mmin : ℝ)) := by ring
    have h4 : (3 * α * (K : ℝ) / δ) * ((kp : ℝ) * (mmin : ℝ))
        ≤ (3 * α * (K : ℝ) / δ) * (Fintype.card V : ℝ) := mul_le_mul_of_nonneg_left h2 hx0
    have h5 : 3 * α * (K : ℝ) / δ ≤ 3 * e / 32 := by
      rw [div_le_iff₀ hδ0]
      have h6 := mul_le_mul_of_nonneg_left hαδ (by positivity : (0:ℝ) ≤ 3 * (K : ℝ))
      have h7 : 3 * (K : ℝ) * (δ * e / (32 * (K : ℝ))) = 3 * e / 32 * δ := by
        field_simp
      rw [h7] at h6
      linarith
    have h8 : (3 * α * (K : ℝ) / δ) * (Fintype.card V : ℝ)
        ≤ 3 * e / 32 * (Fintype.card V : ℝ) := mul_le_mul_of_nonneg_right h5 hn0R.le
    linarith
  have hkpsq : (kp : ℝ) ^ 2 * τ ^ 2 ≤ ε * (Fintype.card V : ℝ) ^ 2 / 16 := by
    have h := kp_tau_sq (by positivity : (0:ℝ) ≤ (kp : ℝ) * τ) hkpτ he0 he1 heε
    calc (kp : ℝ) ^ 2 * τ ^ 2 = ((kp : ℝ) * τ) ^ 2 := by ring
      _ ≤ ε * (Fintype.card V : ℝ) ^ 2 / 16 := h
  have hone : (1 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 / 16 := by
    have h1 : (16 : ℝ) / ε ≤ (Cn : ℝ) := by rw [hCndef]; exact Nat.le_ceil _
    have h2 : (Cn : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hnCn
    rw [div_le_iff₀ hε] at h1
    have h3 : (16 : ℝ) ≤ ε * (Fintype.card V : ℝ) := by
      have h := mul_le_mul_of_nonneg_right h2 hε.le
      linarith
    have h4 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hcardV0
    have h5 : (16 : ℝ) * 1 ≤ (ε * (Fintype.card V : ℝ)) * (Fintype.card V : ℝ) :=
      mul_le_mul h3 h4 zero_le_one (by linarith)
    linarith
  have hen : e * (Fintype.card V : ℝ) ^ 2 ≤ ε * (Fintype.card V : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right heε (sq_nonneg _)
  have hdn : δ * (Fintype.card V : ℝ) ^ 2 ≤ ε * (Fintype.card V : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hδε (sq_nonneg _)
  have hmain := nu3star_le_cover_of_family_lp_value G Pp U W X A B C hτ0.le hgrid hynu hval
  refine le_trans hmain ?_
  linarith

private structure CoarseClusterScales {V : Type} [Fintype V] [DecidableEq V]
    (Pp : Finpartition (univ : Finset V)) (T₀ ε δ θ : ℝ)
    (s₀ K KB Mmin Cn : ℕ) (α : ℝ) where
  kp : ℕ
  mmax : ℕ
  mmin : ℕ
  l : ℕ
  Pn : ℕ
  τ : ℝ
  hkpdef : kp = #Pp.parts
  hkpN : 0 < kp
  hcardle : ∀ S ∈ Pp.parts, #S ≤ mmax
  hnlo : kp * mmin ≤ Fintype.card V
  hnCn : Cn ≤ Fintype.card V
  hmmin0 : 0 < mmin
  hmmax0R : (0 : ℝ) < (mmax : ℝ)
  hlLB : 2 * α * (mmax : ℝ) ≤ (l : ℝ)
  hl0 : 0 < l
  hl0R : (0 : ℝ) < (l : ℝ)
  hl3 : (l : ℝ) ≤ 3 * α * (mmin : ℝ)
  hPnl : Pn * l ≤ mmin
  hPnltR : (mmin : ℝ) < ((Pn : ℝ) + 1) * (l : ℝ)
  hmmPn : (mmax : ℝ) ≤ ((Pn : ℝ) + 2) * (l : ℝ)
  hPnge : 1 / (4 * α) ≤ (Pn : ℝ)
  hPn0R : (0 : ℝ) < (Pn : ℝ)
  hPn0 : 0 < Pn
  hτdef : τ = (l : ℝ) * (K : ℝ) / δ
  hτ0 : 0 < τ
  hτT₀ : T₀ ≤ τ
  hτ192 : 192 / (ε * δ ^ 3) ≤ τ
  hτ1 : (1 : ℝ) ≤ τ
  hK1R : (1 : ℝ) ≤ (K : ℝ)
  hs₀θ : (s₀ : ℝ) ≤ θ * (Pn : ℝ)
  hfitS : ∀ S ∈ Pp.parts, Pn * l ≤ #S

private theorem coarse_cluster_scales {V : Type} [Fintype V] [DecidableEq V]
    (Pp : Finpartition (univ : Finset V)) (T₀ ε δ e θ α ε₁ : ℝ)
    (s₀ K KB Mmin Cn : ℕ)
    (hV : KB * (Mmin + 1) + Cn + 10 ≤ Fintype.card V)
    (hPeq : Pp.IsEquipartition)
    (hPl : 4 / ε₁ ≤ (#Pp.parts : ℝ))
    (hPb : (#Pp.parts : ℝ) ≤ (KB : ℝ))
    (hMdef : Mmin =
      ⌈2 / α + δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) + 800 / e⌉₊)
    (hs₀def : s₀ = ⌈(K : ℝ) / δ⌉₊)
    (hε : 0 < ε) (hε₁0 : 0 < ε₁) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (he0 : 0 < e)
    (hT₀0 : 0 < T₀) (hK1 : 1 ≤ K)
    (hα0 : 0 < α) (hα16 : α ≤ 1 / 16)
    (hαθ : α ≤ θ * δ / (16 * K)) (hθ0 : 0 < θ) :
    Nonempty (CoarseClusterScales Pp T₀ ε δ θ s₀ K KB Mmin Cn α) := by
  classical
  -- ### the clusters
  have hkpR : (0 : ℝ) < (#Pp.parts : ℝ) :=
    lt_of_lt_of_le (div_pos (by norm_num) hε₁0) hPl
  have hkpN : 0 < #Pp.parts := by exact_mod_cast hkpR
  have hpne : Pp.parts.Nonempty := Finset.card_pos.mp hkpN
  set kp : ℕ := #Pp.parts with hkpdef
  set mmax : ℕ := Pp.parts.sup' hpne Finset.card with hmmaxdef
  set mmin : ℕ := Pp.parts.inf' hpne Finset.card with hmmindef
  let Smin := Classical.choose (Finset.exists_mem_eq_inf' hpne Finset.card)
  have ⟨hSminmem, hSmineq⟩ :=
    Classical.choose_spec (Finset.exists_mem_eq_inf' hpne Finset.card)
  let Smax := Classical.choose (Finset.exists_mem_eq_sup' hpne Finset.card)
  have ⟨hSmaxmem, hSmaxeq⟩ :=
    Classical.choose_spec (Finset.exists_mem_eq_sup' hpne Finset.card)
  have hminmax : mmin ≤ mmax := by
    rw [hmmindef, hSmineq, hmmaxdef]; exact Finset.le_sup' _ hSminmem
  have hmm1 : mmax ≤ mmin + 1 := by
    rw [hmmaxdef, hSmaxeq, hmmindef, hSmineq]
    exact hPeq (Finset.mem_coe.mpr hSmaxmem) (Finset.mem_coe.mpr hSminmem)
  have hcardle : ∀ S ∈ Pp.parts, #S ≤ mmax := fun S hS => Finset.le_sup' _ hS
  have hcardge : ∀ S ∈ Pp.parts, mmin ≤ #S := fun S hS => Finset.inf'_le _ hS
  have hsumparts : ∑ S ∈ Pp.parts, #S = Fintype.card V := by
    rw [Pp.sum_card_parts, Finset.card_univ]
  have hnhi : Fintype.card V ≤ kp * mmax := by
    calc Fintype.card V = ∑ S ∈ Pp.parts, #S := hsumparts.symm
      _ ≤ ∑ _S ∈ Pp.parts, mmax := Finset.sum_le_sum (fun S hS => hcardle S hS)
      _ = kp * mmax := by rw [Finset.sum_const, smul_eq_mul]
  have hnlo : kp * mmin ≤ Fintype.card V := by
    calc kp * mmin = ∑ _S ∈ Pp.parts, mmin := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ S ∈ Pp.parts, #S := Finset.sum_le_sum (fun S hS => hcardge S hS)
      _ = Fintype.card V := hsumparts
  have hkpKB : kp ≤ KB := by exact_mod_cast hPb
  have hKB0 : 0 < KB := lt_of_lt_of_le hkpN hkpKB
  -- the two consequences of the size threshold
  have hmminN : Mmin ≤ mmin := by
    have h1 : KB * (Mmin + 1) ≤ Fintype.card V := le_trans (by omega) hV
    have h2 : Fintype.card V ≤ KB * (mmin + 1) :=
      le_trans hnhi (Nat.mul_le_mul hkpKB (by omega))
    have h3 := Nat.le_of_mul_le_mul_left (le_trans h1 h2) hKB0
    omega
  have hnCn : Cn ≤ Fintype.card V := le_trans (by omega) hV
  -- ### the coarse cells, the block scale and the box size
  have hmminR0 : (Mmin : ℝ) ≤ (mmin : ℝ) := by exact_mod_cast hmminN
  have hceil : 2 / α + δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) + 800 / e ≤ (Mmin : ℝ) :=
    by rw [hMdef]; exact Nat.le_ceil _
  have hA : 2 / α ≤ (mmin : ℝ) := by
    have h1 : (0:ℝ) ≤ δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) := by positivity
    have h2 : (0:ℝ) ≤ 800 / e := by positivity
    linarith
  have hB : δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) ≤ (mmin : ℝ) := by
    have h1 : (0:ℝ) ≤ 2 / α := by positivity
    have h2 : (0:ℝ) ≤ 800 / e := by positivity
    linarith
  have hC : 800 / e ≤ (mmin : ℝ) := by
    have h1 : (0:ℝ) ≤ 2 / α := by positivity
    have h2 : (0:ℝ) ≤ δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) := by positivity
    linarith
  have hαmmin : (2 : ℝ) ≤ α * (mmin : ℝ) := by
    rw [div_le_iff₀ hα0] at hA
    linarith
  have hmmin0R : (0 : ℝ) < (mmin : ℝ) := by nlinarith only [hαmmin, hα0]
  have hmmin0 : 0 < mmin := by exact_mod_cast hmmin0R
  have hmminmaxR : (mmin : ℝ) ≤ (mmax : ℝ) := by exact_mod_cast hminmax
  have hmmax0R : (0 : ℝ) < (mmax : ℝ) := lt_of_lt_of_le hmmin0R hmminmaxR
  have hmmaxR : (mmax : ℝ) ≤ (mmin : ℝ) + 1 := by exact_mod_cast hmm1
  set l : ℕ := ⌈2 * α * (mmax : ℝ)⌉₊ with hldef
  have hlLB : 2 * α * (mmax : ℝ) ≤ (l : ℝ) := Nat.le_ceil _
  have hlUB : (l : ℝ) ≤ 2 * α * (mmax : ℝ) + 1 := by
    have h := Nat.ceil_lt_add_one (le_of_lt (by positivity : (0:ℝ) < 2 * α * (mmax : ℝ)))
    rw [hldef]; linarith
  have hl0 : 0 < l := Nat.ceil_pos.mpr (by positivity)
  have hl0R : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hlmin : 2 * α * (mmin : ℝ) ≤ (l : ℝ) := by
    nlinarith only [hlLB, hmminmaxR, hα0]
  have hl3 : (l : ℝ) ≤ 3 * α * (mmin : ℝ) := by
    nlinarith only [hlUB, hmmaxR, hαmmin, hα16, hα0]
  set Pn : ℕ := mmin / l with hPndef
  have hPnl : Pn * l ≤ mmin := Nat.div_mul_le_self _ _
  have hPnlt : mmin < (Pn + 1) * l := by
    have h1 : l * Pn + mmin % l = mmin := Nat.div_add_mod mmin l
    have h2 : mmin % l < l := Nat.mod_lt _ hl0
    calc mmin = l * Pn + mmin % l := h1.symm
      _ < l * Pn + l := by omega
      _ = (Pn + 1) * l := by ring
  have hPnlR : (Pn : ℝ) * (l : ℝ) ≤ (mmin : ℝ) := by exact_mod_cast hPnl
  have hPnltR : (mmin : ℝ) < ((Pn : ℝ) + 1) * (l : ℝ) := by exact_mod_cast hPnlt
  have hl1R : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl0
  have hmmPn : (mmax : ℝ) ≤ ((Pn : ℝ) + 2) * (l : ℝ) := by
    have hexp : ((Pn : ℝ) + 2) * (l : ℝ) = ((Pn : ℝ) + 1) * (l : ℝ) + (l : ℝ) := by ring
    linarith
  have hPnge : 1 / (4 * α) ≤ (Pn : ℝ) := by
    have h1 : (mmin : ℝ) < ((Pn : ℝ) + 1) * (3 * α * (mmin : ℝ)) := by
      nlinarith only [hPnltR, hl3, (Nat.cast_nonneg Pn : (0:ℝ) ≤ (Pn : ℝ))]
    have h2 : 1 < ((Pn : ℝ) + 1) * (3 * α) := by
      by_contra hcon
      push Not at hcon
      nlinarith only [hcon, h1, hmmin0R]
    rw [div_le_iff₀ (by positivity)]
    linarith only [h2, hα16, hα0]
  have hPn0R : (0 : ℝ) < (Pn : ℝ) := lt_of_lt_of_le (by positivity) hPnge
  have hPn0 : 0 < Pn := by exact_mod_cast hPn0R
  set τ : ℝ := (l : ℝ) * (K : ℝ) / δ with hτdef
  have hτ0 : 0 < τ := by rw [hτdef]; positivity
  have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le zero_lt_one hK1R
  have hτbig : T₀ + 192 / (ε * δ ^ 3) + 1 ≤ τ := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * α * (K:ℝ))] at hB
    rw [hτdef, le_div_iff₀ hδ0]
    nlinarith only [hB, hlmin, hKpos]
  have hτT₀ : T₀ ≤ τ := by
    have h1 : (0:ℝ) < 192 / (ε * δ ^ 3) := by positivity
    linarith
  have hτ192 : 192 / (ε * δ ^ 3) ≤ τ := by linarith
  have hτ1 : (1 : ℝ) ≤ τ := by
    have h1 : (0:ℝ) < 192 / (ε * δ ^ 3) := by positivity
    linarith
  have hKδ1 : (1 : ℝ) ≤ (K : ℝ) / δ := by
    rw [le_div_iff₀ hδ0]
    linarith only [hδ1, hK1R]
  have hs₀le : (s₀ : ℝ) ≤ 2 * ((K : ℝ) / δ) := by
    have h2 : (s₀ : ℝ) ≤ (K : ℝ) / δ + 1 := by
      rw [hs₀def]
      exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
    linarith
  have hαθ' : 16 * (K : ℝ) * α ≤ θ * δ := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 16 * (K:ℝ))] at hαθ
    linarith
  have hs₀θ : (s₀ : ℝ) ≤ θ * (Pn : ℝ) :=
    small_box_bound hθ0 hδ0 hα0 hK1R hαθ' hPnge hs₀le
  have hfitS : ∀ S ∈ Pp.parts, Pn * l ≤ #S := fun S hS => le_trans hPnl (hcardge S hS)
  exact ⟨⟨kp, mmax, mmin, l, Pn, τ, hkpdef, hkpN, hcardle, hnlo, hnCn,
    hmmin0, hmmax0R, hlLB, hl0, hl0R, hl3, hPnl, hPnltR, hmmPn, hPnge,
    hPn0R, hPn0, hτdef, hτ0, hτT₀, hτ192, hτ1, hK1R, hs₀θ, hfitS⟩⟩

private structure DenseTripleGeometry {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (δ : ℝ) (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts})) : Prop where
  hGddense : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
    δ ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ)
  hposne : ∀ (th : Finset {S : Finset V // S ∈ Pp.parts}), #th = 3 →
    ∀ a b : ZMod 3, a ≠ b → triPos Pp th a ≠ triPos Pp th b
  hdOppδ : ∀ th ∈ Gd, ∀ a : ZMod 3, δ ≤ dOpp G Pp th a
  hdProdLB : ∀ th ∈ Gd, δ ^ 3 ≤ dProd G Pp th
  hdProdUB : ∀ th, dProd G Pp th ≤ 1
  hdProd0 : ∀ th ∈ Gd, 0 < dProd G Pp th

private theorem dense_triple_geometry {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (δ : ℝ) (y : Finset {S : Finset V // S ∈ Pp.parts} → ℝ)
    (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}))
    (hGddef : Gd = clusterLPSupport y \ sparseTriples G Pp δ)
    (hGdcard : ∀ th ∈ Gd, #th = 3) (hδ0 : 0 < δ) :
    DenseTripleGeometry G Pp δ Gd := by
  classical
  have hGddense : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
      δ ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) := by
    intro th hth S hS T hT hST
    by_contra hcon
    push Not at hcon
    rw [hGddef] at hth
    exact (Finset.mem_sdiff.mp hth).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, S, hS, T, hT, hST, hcon⟩)
  have hposne : ∀ (th : Finset {S : Finset V // S ∈ Pp.parts}), #th = 3 →
      ∀ a b : ZMod 3, a ≠ b → triPos Pp th a ≠ triPos Pp th b :=
    fun th h3 a b hab h => hab (triPos_injective Pp h3 h)
  have hdOppδ : ∀ th ∈ Gd, ∀ a : ZMod 3, δ ≤ dOpp G Pp th a := by
    intro th hth a
    rw [dOpp]
    refine hGddense th hth _ (triPos_mem Pp (hGdcard th hth) _) _
      (triPos_mem Pp (hGdcard th hth) _) (hposne th (hGdcard th hth) _ _ ?_)
    intro hEq
    have h12 : (1 : ZMod 3) = 2 := add_left_cancel hEq
    exact absurd h12 (by decide +kernel)
  have hdProdLB : ∀ th ∈ Gd, δ ^ 3 ≤ dProd G Pp th := by
    intro th hth
    exact prod_ge_cube hδ0 (hdOppδ th hth 0) (hdOppδ th hth 1) (hdOppδ th hth 2)
  have hdProdUB : ∀ th, dProd G Pp th ≤ 1 := fun th =>
    prod_le_one (dOpp_nonneg G Pp th 0) (dOpp_nonneg G Pp th 1)
      (dOpp_nonneg G Pp th 2) (dOpp_le_one G Pp th 0)
      (dOpp_le_one G Pp th 1) (dOpp_le_one G Pp th 2)
  have hdProd0 : ∀ th ∈ Gd, 0 < dProd G Pp th := fun th hth =>
    lt_of_lt_of_le (by positivity) (hdProdLB th hth)
  exact ⟨hGddense, hposne, hdOppδ, hdProdLB, hdProdUB, hdProd0⟩

private theorem good_copy_properties {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (ε₁ δ α τ : ℝ) (mmax : ℕ)
    (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}))
    (nc : Finset {S : Finset V // S ∈ Pp.parts} → ℕ)
    (clf : {p // p ∈ copySet Gd nc} → ZMod 3 → {S : Finset V // S ∈ Pp.parts})
    (bsc : {p // p ∈ copySet Gd nc} → ZMod 3 → ℕ)
    (bsf : Finset {S : Finset V // S ∈ Pp.parts} → ZMod 3 → ℕ)
    (hclfdef : clf = fun c a => triPos Pp c.1.1 a)
    (hbscdef : bsc = fun c a => bsf c.1.1 a)
    (hcGd : ∀ c : {p // p ∈ copySet Gd nc}, c.1.1 ∈ Gd)
    (hGdcard : ∀ th ∈ Gd, #th = 3)
    (hGdadj : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
      (hostGraph G Pp (ε₁ / 8) (ε₁ / 4)).Adj S T)
    (hGddense : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
      δ ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
    (hposne : ∀ (th : Finset {S : Finset V // S ∈ Pp.parts}), #th = 3 →
      ∀ a b : ZMod 3, a ≠ b → triPos Pp th a ≠ triPos Pp th b)
    (hcardle : ∀ S ∈ Pp.parts, #S ≤ mmax)
    (hα0 : 0 < α)
    (hbsrel : ∀ th ∈ Gd, ∀ a, α * (mmax : ℝ) ≤ (bsf th a : ℝ))
    (hbsLB : ∀ th a, τ * dOpp G Pp th a ≤ (bsf th a : ℝ))
    (hbsUB : ∀ th a, (bsf th a : ℝ) < τ * dOpp G Pp th a + 1) :
    (∀ c : {p // p ∈ copySet Gd nc}, GoodTriple G Pp (ε₁ / 8) δ
      (clf c 0 : Finset V) (clf c 1 : Finset V) (clf c 2 : Finset V)) ∧
    (∀ c : {p // p ∈ copySet Gd nc}, ∀ a,
      α * (#(clf c a : Finset V) : ℝ) ≤ (bsc c a : ℝ)) ∧
    (∀ c : {p // p ∈ copySet Gd nc}, ∀ a : ZMod 3,
      |(bsc c a : ℝ) - τ * (G.edgeDensity
        (clf c (a + 1) : Finset V) (clf c (a + 2) : Finset V) : ℝ)| ≤ 1) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro c
    have hth := hcGd c
    have h3 := hGdcard _ hth
    have hadj : ∀ a b : ZMod 3, a ≠ b →
        (hostGraph G Pp (ε₁ / 8) (ε₁ / 4)).Adj (clf c a) (clf c b) := by
      intro a b hab
      simp only [hclfdef]
      exact hGdadj _ hth _ (triPos_mem Pp h3 a) _ (triPos_mem Pp h3 b)
        (hposne _ h3 a b hab)
    have hdens : ∀ a b : ZMod 3, a ≠ b →
        δ ≤ (G.edgeDensity (clf c a : Finset V) (clf c b : Finset V) : ℝ) := by
      intro a b hab
      simp only [hclfdef]
      exact hGddense _ hth _ (triPos_mem Pp h3 a) _ (triPos_mem Pp h3 b)
        (hposne _ h3 a b hab)
    exact ⟨(clf c 0).2, (clf c 1).2, (clf c 2).2,
      (hadj 0 1 (by decide +kernel)).1, (hadj 0 2 (by decide +kernel)).1,
      (hadj 1 2 (by decide +kernel)).1,
      (hadj 0 1 (by decide +kernel)).2.1, hdens 0 1 (by decide +kernel),
      (hadj 0 2 (by decide +kernel)).2.1, hdens 0 2 (by decide +kernel),
      (hadj 1 2 (by decide +kernel)).2.1, hdens 1 2 (by decide +kernel)⟩
  · intro c a
    have h1 : (#(clf c a : Finset V) : ℝ) ≤ (mmax : ℝ) := by
      exact_mod_cast hcardle _ (clf c a).2
    have h2 : α * (#(clf c a : Finset V) : ℝ) ≤ α * (mmax : ℝ) :=
      mul_le_mul_of_nonneg_left h1 hα0.le
    simp only [hbscdef]
    exact le_trans h2 (hbsrel _ (hcGd c) a)
  · intro c a
    have hEq : (G.edgeDensity (clf c (a + 1) : Finset V)
        (clf c (a + 2) : Finset V) : ℝ) = dOpp G Pp c.1.1 a := by
      simp only [hclfdef, dOpp]
    simp only [hbscdef]
    rw [hEq, abs_le]
    exact ⟨by linarith only [hbsLB c.1.1 a], by linarith only [hbsUB c.1.1 a]⟩

private theorem bad_copy_mass_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (δ τ : ℝ) (K l : ℕ)
    (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}))
    (nc : Finset {S : Finset V // S ∈ Pp.parts} → ℕ)
    (szc : {p // p ∈ copySet Gd nc} → ZMod 3 → ℕ)
    (szf : Finset {S : Finset V // S ∈ Pp.parts} → ZMod 3 → ℕ)
    (hτsq : τ ^ 2 = (l : ℝ) ^ 2 * (K : ℝ) ^ 2 / δ ^ 2)
    (hszcdef : szc = fun c a => szf c.1.1 a)
    (hdnn : ∀ th a, (0 : ℝ) ≤ dOpp G Pp th a)
    (hszLB : ∀ th a, (K : ℝ) * dOpp G Pp th a / δ ≤ (szf th a : ℝ))
    (hδ0 : 0 < δ) (hKpos : (0 : ℝ) < (K : ℝ)) :
    ∀ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * dProd G Pp c.1.1
      ≤ (l : ℝ) ^ 2 * ∑ a : ZMod 3,
        (szc c a : ℝ) * (szc c (a + 1) : ℝ) := by
  classical
  intro c
  have h1 : τ ^ 2 * dProd G Pp c.1.1
      ≤ (l : ℝ) ^ 2 * ((szc c 0 : ℝ) * (szc c 1 : ℝ)) := by
    rw [hτsq]
    simp only [dProd, hszcdef]
    exact bad_term_bound hδ0 hKpos.le (hdnn _ 0) (hdnn _ 1) (hdnn _ 2)
      (dOpp_le_one G Pp _ 2) (hszLB _ 0) (hszLB _ 1)
  have h2 : (szc c 0 : ℝ) * (szc c 1 : ℝ)
      ≤ ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ) :=
    pair_product_le_cyclic_sum (szc c)
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))

/-- **The coarse-cell reduction**: the small-box allocation residual implies the coupled
block-allocation residual. -/
theorem blockCoverResidualCoupled_of_boxAllocation (hbox : BoxAllocationResidual) :
    BlockCoverResidualCoupled := by
  classical
  intro ε δ ε₂ T₀ hε hδ0 hδ1 hδε hε₂0 hT₀0
  set e : ℝ := min 1 ε with hedef
  have he0 : 0 < e := lt_min one_pos hε
  have he1 : e ≤ 1 := min_le_left _ _
  have heε : e ≤ ε := min_le_right _ _
  set K : ℕ := ⌈640 / e⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKR : (640 : ℝ) / e ≤ (K : ℝ) := by
    have h := Nat.le_ceil (640 / e)
    have : ((⌈640 / e⌉₊ : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.le_succ _
    linarith only [h, this]
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  -- the box bound is fixed *before* the smallness threshold `θ` is asked for
  set s₀ : ℕ := ⌈(K : ℝ) / δ⌉₊ with hs₀def
  obtain ⟨θ, hθ0, hθ1, hboxmain⟩ := hbox (e / 64) (by positivity) s₀
  set α : ℝ := min (1 / 16) (min (e / 3200) (min (θ * δ / (16 * K)) (δ * e / (32 * K)))) with hαdef
  have hα0 : 0 < α := by
    refine lt_min (by norm_num) (lt_min (by positivity) (lt_min ?_ ?_)) <;> positivity
  have hα16 : α ≤ 1 / 16 := min_le_left _ _
  have hαe : α ≤ e / 3200 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hαθ : α ≤ θ * δ / (16 * K) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hαδ : α ≤ δ * e / (32 * K) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨8 * α * min 1 ε₂, by positivity, ?_⟩
  intro ε₁ hε₁0 hε₁le hε₁1
  have hmin1 : min 1 ε₂ ≤ 1 := min_le_left _ _
  have hmin2 : min 1 ε₂ ≤ ε₂ := min_le_right _ _
  have hm10 : (0 : ℝ) < min 1 ε₂ := lt_min one_pos hε₂0
  have hε₁α : ε₁ / 8 ≤ α * min 1 ε₂ := by linarith only [hε₁le]
  refine ⟨α, ?_, by linarith, ?_, ?_⟩
  · have h : α * min 1 ε₂ ≤ α * 1 := mul_le_mul_of_nonneg_left hmin1 hα0.le
    rw [mul_one] at h
    linarith only [hε₁α, h]
  · rw [div_le_iff₀ hα0]
    have h : α * min 1 ε₂ ≤ α * ε₂ := mul_le_mul_of_nonneg_left hmin2 hα0.le
    linarith only [hε₁α, h]
  -- ### the size threshold
  set KB : ℕ := SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ with hKBdef
  set Mmin : ℕ := ⌈2 / α + δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) + 800 / e⌉₊ with hMdef
  set Cn : ℕ := ⌈16 / ε⌉₊ with hCndef
  refine ⟨KB * (Mmin + 1) + Cn + 10, ?_⟩
  intro V _ _ G _ Pp hV hPeq hPl hPb hPu
  obtain ⟨⟨kp, mmax, mmin, l, Pn, τ, hkpdef, hkpN, hcardle, hnlo, hnCn,
    hmmin0, hmmax0R, hlLB, hl0, hl0R, hl3, hPnl, hPnltR, hmmPn, hPnge,
    hPn0R, hPn0, hτdef, hτ0, hτT₀, hτ192, hτ1, hK1R, hs₀θ, hfitS⟩⟩ :=
    coarse_cluster_scales Pp T₀ ε δ e θ α ε₁ s₀ K KB Mmin Cn hV hPeq hPl
      (by simpa only [hKBdef] using hPb) hMdef hs₀def hε hε₁0 hδ0 hδ1 he0 hT₀0
      hK1 hα0 hα16 hαθ hθ0
  have hpne : Pp.parts.Nonempty := Finset.card_pos.mp (by simpa only [hkpdef] using hkpN)
  obtain ⟨Smin, hSminmem⟩ := hpne
  letI : Nonempty {S : Finset V // S ∈ Pp.parts} := ⟨⟨Smin, hSminmem⟩⟩
  -- ### the LP point and the dense triples
  obtain ⟨y, hyLP, hysupp, hynu⟩ :=
    exists_sparse_clusterTripleLP_nu3star G Pp (ε₁ / 8) (ε₁ / 4) (η := 1) one_pos
  set Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}) :=
    clusterLPSupport y \ sparseTriples G Pp δ with hGddef
  have hyne : ∀ th ∈ Gd, y th ≠ 0 := by
    intro th hth
    have h := (Finset.mem_sdiff.mp hth).1
    rw [clusterLPSupport, Finset.mem_filter] at h
    exact h.2
  have hGdcard : ∀ th ∈ Gd, #th = 3 := fun th hth =>
    (SimpleGraph.mem_cliqueFinset_iff.mp (hyLP.2.1 th (hyne th hth))).card_eq
  have hGdpos : ∀ th ∈ Gd, 0 < y th := fun th hth =>
    lt_of_le_of_ne (hyLP.1 th) (Ne.symm (hyne th hth))
  obtain ⟨hGddense, hposne, hdOppδ, hdProdLB, hdProdUB, hdProd0⟩ :=
    dense_triple_geometry G Pp δ y Gd hGddef hGdcard hδ0
  have hGdadj : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
      (hostGraph G Pp (ε₁ / 8) (ε₁ / 4)).Adj S T := fun th hth S hS T hT hST =>
    (SimpleGraph.mem_cliqueFinset_iff.mp (hyLP.2.1 th (hyne th hth))).1
      (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hT) hST
  -- ### the prescribed sizes, the block sizes and the number of copies
  obtain ⟨szf, hszfdef⟩ : ∃ f : Finset {S : Finset V // S ∈ Pp.parts} → ZMod 3 → ℕ,
      f = fun th a => ⌈(K : ℝ) * dOpp G Pp th a / δ⌉₊ := ⟨_, rfl⟩
  obtain ⟨bsf, hbsfdef⟩ : ∃ f : Finset {S : Finset V // S ∈ Pp.parts} → ZMod 3 → ℕ,
      f = fun th a => ⌈τ * dOpp G Pp th a⌉₊ := ⟨_, rfl⟩
  obtain ⟨nc, hncdef⟩ : ∃ f : Finset {S : Finset V // S ∈ Pp.parts} → ℕ,
      f = fun th => ⌊(1 - e / 8) * y th / (τ ^ 2 * dProd G Pp th)⌋₊ := ⟨_, rfl⟩
  have hdnn : ∀ th a, (0 : ℝ) ≤ dOpp G Pp th a := fun th a => dOpp_nonneg G Pp th a
  have hszLB : ∀ th a, (K : ℝ) * dOpp G Pp th a / δ ≤ (szf th a : ℝ) := by
    intro th a; rw [hszfdef]; exact Nat.le_ceil _
  have hszUB : ∀ th a, (szf th a : ℝ) < (K : ℝ) * dOpp G Pp th a / δ + 1 := by
    intro th a
    rw [hszfdef]
    exact Nat.ceil_lt_add_one (by have := hdnn th a; positivity)
  have hsz1 : ∀ th ∈ Gd, ∀ a, 1 ≤ szf th a := by
    intro th hth a
    rw [hszfdef]
    refine Nat.one_le_ceil_iff.mpr ?_
    exact div_pos (mul_pos hKpos (lt_of_lt_of_le hδ0 (hdOppδ th hth a))) hδ0
  have hszs₀ : ∀ th a, szf th a ≤ s₀ := by
    intro th a
    rw [hszfdef, hs₀def]
    refine Nat.ceil_le_ceil ?_
    rw [div_le_div_iff_of_pos_right hδ0]
    linarith only [mul_le_mul_of_nonneg_left (dOpp_le_one G Pp th a) hKpos.le]
  have hbsLB : ∀ th a, τ * dOpp G Pp th a ≤ (bsf th a : ℝ) := by
    intro th a; rw [hbsfdef]; exact Nat.le_ceil _
  have hbsUB : ∀ th a, (bsf th a : ℝ) < τ * dOpp G Pp th a + 1 := by
    intro th a
    rw [hbsfdef]
    exact Nat.ceil_lt_add_one (by have := hdnn th a; positivity)
  have hτd : ∀ th a, τ * dOpp G Pp th a = (l : ℝ) * ((K : ℝ) * dOpp G Pp th a / δ) := by
    intro th a
    rw [hτdef]
    field_simp
  have hbssz : ∀ th a, bsf th a ≤ szf th a * l := by
    intro th a
    rw [hbsfdef]
    refine Nat.ceil_le.mpr ?_
    push_cast
    rw [hτd th a]
    exact (mul_le_mul_of_nonneg_left (hszLB th a) hl0R.le).trans_eq (mul_comm _ _)
  have hτδ : τ * δ = (l : ℝ) * (K : ℝ) := by rw [hτdef]; field_simp
  have hbsrel : ∀ th ∈ Gd, ∀ a, α * (mmax : ℝ) ≤ (bsf th a : ℝ) := by
    intro th hth a
    have h1 : τ * δ ≤ τ * dOpp G Pp th a := mul_le_mul_of_nonneg_left (hdOppδ th hth a) hτ0.le
    have h2 := hbsLB th a
    exact bs_ge_alpha hlLB hK1R (by linarith [hτδ ▸ h1]) hmmax0R.le hα0.le
  -- ### the copies
  obtain ⟨clf, hclfdef⟩ :
      ∃ f : {p // p ∈ copySet Gd nc} → ZMod 3 → {S : Finset V // S ∈ Pp.parts},
      f = fun c a => triPos Pp c.1.1 a := ⟨_, rfl⟩
  obtain ⟨szc, hszcdef⟩ : ∃ f : {p // p ∈ copySet Gd nc} → ZMod 3 → ℕ,
      f = fun c a => szf c.1.1 a := ⟨_, rfl⟩
  obtain ⟨bsc, hbscdef⟩ : ∃ f : {p // p ∈ copySet Gd nc} → ZMod 3 → ℕ,
      f = fun c a => bsf c.1.1 a := ⟨_, rfl⟩
  have hcGd : ∀ c : {p // p ∈ copySet Gd nc}, c.1.1 ∈ Gd := fun c => (mem_copySet.mp c.2).1
  have hclinj : ∀ c, Function.Injective (clf c) := by
    intro c
    rw [hclfdef]
    exact triPos_injective Pp (hGdcard _ (hcGd c))
  have hszc1 : ∀ c a, 1 ≤ szc c a := by
    intro c a; rw [hszcdef]; exact hsz1 _ (hcGd c) a
  have hszcs₀ : ∀ c a, szc c a ≤ s₀ := by
    intro c a; rw [hszcdef]; exact hszs₀ _ a
  -- ### the three margins of the capacity
  have hKu : 1 / (K : ℝ) ≤ e / 640 := by
    have h1 : (640 : ℝ) ≤ (K : ℝ) * e := (div_le_iff₀ he0).mp hKR
    rw [div_le_div_iff₀ hKpos (by norm_num : (0:ℝ) < 640)]
    linarith
  have hPv : 2 / (Pn : ℝ) ≤ e / 400 := by
    have h1 : (1 : ℝ) ≤ (Pn : ℝ) * (4 * α) :=
      (div_le_iff₀ (by positivity : (0:ℝ) < 4 * α)).mp hPnge
    have h2 : α * (Pn : ℝ) ≤ e / 3200 * (Pn : ℝ) :=
      mul_le_mul_of_nonneg_right hαe hPn0R.le
    rw [div_le_div_iff₀ hPn0R (by norm_num : (0:ℝ) < 400)]
    linarith
  have hτsq : τ ^ 2 = (l : ℝ) ^ 2 * (K : ℝ) ^ 2 / δ ^ 2 := by
    rw [hτdef]; field_simp
  have hncUB : ∀ th ∈ Gd, (nc th : ℝ)
      ≤ (1 - e / 8) * y th * δ ^ 2 / ((l : ℝ) ^ 2 * (K : ℝ) ^ 2 * dProd G Pp th) := by
    intro th hth
    have hy0 : (0 : ℝ) ≤ y th := hyLP.1 th
    have hdp := hdProd0 th hth
    have h0 : (0 : ℝ) ≤ (1 - e / 8) * y th / (τ ^ 2 * dProd G Pp th) := by
      apply div_nonneg (mul_nonneg (by linarith) hy0)
      positivity
    rw [hncdef]
    refine le_trans (Nat.floor_le h0) (le_of_eq ?_)
    rw [hτsq]
    field_simp
  -- ### the demand of every ordered cluster pair
  have hdemand : ∀ S T : {S : Finset V // S ∈ Pp.parts}, S ≠ T →
      boxDemand clf szc S T ≤ (1 - e / 64) * (Pn : ℝ) ^ 2 := by
    simpa only [hclfdef, hszcdef] using
      (box_demand_bound G Pp ε₁ δ e K l Pn mmax y Gd szf nc he0 he1 hδ0
        hyLP hGdcard hGddense hposne hdProd0 hdOppδ hszUB hncUB hKpos
        hl0R hKu hPn0R hPv hmmax0R hmmPn hcardle)
  -- ### the placement
  obtain ⟨bad, I, hIcard, hIdisj, hIbad⟩ :=
    hboxmain Pn hPn0 hs₀θ {S : Finset V // S ∈ Pp.parts} {p // p ∈ copySet Gd nc}
      clf szc hclinj hszc1 hszcs₀ hdemand
  obtain ⟨Good, hGooddef⟩ : ∃ F : Finset {p // p ∈ copySet Gd nc},
      F = (univ : Finset {p // p ∈ copySet Gd nc}) \ bad := ⟨_, rfl⟩
  have hGoodmem : ∀ c ∈ Good, c ∉ bad := by
    intro c hc
    rw [hGooddef] at hc
    exact (Finset.mem_sdiff.mp hc).2
  have hbscsz : ∀ c a, bsc c a ≤ szc c a * l := by
    intro c a; simp only [hbscdef, hszcdef]; exact hbssz _ a
  obtain ⟨hgoodT, hrelG, hshapeG⟩ :=
    good_copy_properties G Pp ε₁ δ α τ mmax Gd nc clf bsc bsf hclfdef hbscdef
      hcGd hGdcard hGdadj hGddense hposne hcardle hα0 hbsrel hbsLB hbsUB
  obtain ⟨k, U, W, X, A, B, C, hkle, hgrid, hdisjF, hsumF⟩ :=
    exists_gridSubTriple_family_of_placement (ep := ε₁ / 8) (de := δ) (α := α) (τ := τ) (l := l)
      G Pp hl0 clf szc bsc I Good hIcard hfitS hbscsz
      (fun c hc c' hc' hne a b a' b' hab hab' h1 h2 =>
        hIdisj c (hGoodmem c hc) c' (hGoodmem c' hc') hne a b a' b' hab hab' h1 h2)
      (fun c _ => hgoodT c) (fun c _ => hrelG c) (fun c _ => hshapeG c)
  have hsumGood : ∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
        * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ))
      = ∑ c ∈ Good, τ ^ 2 * dProd G Pp c.1.1 := by
    rw [hsumF]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dProd_eq]
    simp only [hclfdef]
  have hbadterm :=
    bad_copy_mass_bound G Pp δ τ K l Gd nc szc szf hτsq hszcdef hdnn hszLB hδ0 hKpos
  refine ⟨τ, k, U, W, X, A, B, C, hτT₀, hgrid, hdisjF, ?_⟩
  exact coarse_cover_clause G Pp ε ε₁ δ e α τ K kp mmin l Pn Cn k y Gd nc bad Good szc U W X A B C
    hkpN hkpdef hmmin0 hnlo hyLP (by simpa only [hkpdef] using hysupp) hynu hδ0 hGddef hsumGood hτ0 hdProd0 hdProdUB
    hncdef hbadterm hIbad hPnl hGooddef hkle hdProdLB hτ1 hτ192 hε hτdef hl3
    hKpos hα0 hαδ he0 he1 heε hCndef hnCn hδε hgrid

/-- **AX1 from the small-box allocation residual.**  Composing the reduction of this file with
`Nibble.AX1.ax1_of_blockCoverCoupled`. -/
theorem ax1_of_boxAllocation (hbox : BoxAllocationResidual) : AX1Statement :=
  ax1_of_blockCoverCoupled (blockCoverResidualCoupled_of_boxAllocation hbox)




end Nibble.AX1
