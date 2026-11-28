/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.Quantile

/-!
# Copulas

A **copula** on `ℝ^ι` is a probability measure whose coordinates are all uniformly distributed on
`(0, 1)` (`IsCopula`). Its distribution function `u ↦ C.real (Iic u)` is what McNeil, Frey and
Embrechts (*Quantitative Risk Management*, 2015, Definition 7.1) call a copula. We take the
measure-first definition: grounding, uniform margins and `d`-increasingness of the distribution
function are then theorems about a measure rather than axioms on a function.

The central fact about copulas is Sklar's theorem (`Probability/Dependence/Sklar.lean`). This file
covers the structure every copula shares.

* **Fréchet–Hoeffding bounds.** On `[0, 1]^ι` every copula satisfies
  `max (∑ uᵢ − (d − 1)) 0 ≤ C(u) ≤ minᵢ uᵢ` (`IsCopula.sum_sub_le_measureReal_Iic`,
  `IsCopula.measureReal_Iic_le`). The upper bound is monotonicity of measure and the lower bound
  is the union bound on the complement.
* **The three fundamental copulas.** These are the independence copula `Π` (a product of uniform
  laws, `C(u) = ∏ uᵢ`), the comonotonicity copula `M` (the law of `(U, …, U)`, `C(u) = min uᵢ`),
  and in dimension two the countermonotonicity copula `W` (the law of `(U, 1 − U)`,
  `C(u) = max (u₀ + u₁ − 1) 0`). `M` attains the upper bound in every dimension and `W` attains
  the lower bound in dimension two.
* **The lower bound is not attained for `d ≥ 3`.** No copula has distribution function
  `max (∑ uᵢ − (d − 1)) 0` (`not_exists_isCopula_frechetLower`, QRM Exercise Book, Exercise 7.3).
  The events `{Uᵢ ≤ 1/2}` for three coordinates would be pairwise null while each carries mass
  `1/2`, for a total of `3/2 > 1`.
* **Distribution functions determine laws on `ℝ^ι`.** Two probability measures on `ℝ^ι` that agree
  on every lower orthant `Iic u` are equal (`ext_of_measure_Iic_pi`). This is the
  multidimensional version of `MeasureTheory.Measure.ext_of_Iic`, and it is what makes a copula
  unique in Sklar's theorem.

## Main definitions

* `IsCopula`: a probability measure on `ι → ℝ` whose every coordinate is uniform on `(0, 1)`.
* `independenceCopula`: the law `Π` of a vector of independent uniforms.
* `comonotoneCopula`: the law `M` of `(U, …, U)` for a single uniform `U`.
* `countermonotoneCopula`: the law `W` of `(U, 1 − U)`, in dimension two.

## Main results

* `IsCopula.measureReal_coord_le`: each coordinate is uniform, `C(vᵢ ≤ t) = t` on `[0, 1]`.
* `IsCopula.ae_mem_Ioo`: almost every point of a copula lies in the open cube `(0, 1)^ι`.
* `IsCopula.measureReal_Iic_le`, `IsCopula.sum_sub_le_measureReal_Iic`: the Fréchet–Hoeffding
  bounds.
* `ext_of_measure_Iic_pi`: joint distribution functions determine probability laws on `ℝ^ι`.
* `not_exists_isCopula_frechetLower`: for `d ≥ 3` the lower Fréchet bound is not a copula.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Section 7.1.2; Theorem 7.7
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 7.3

## Tags

Fréchet–Hoeffding bounds, comonotonicity, countermonotonicity, independence copula,
dependence modelling, MSC 62H05, MSC 91G70, JEL C02
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

/-! ### The uniform law on `(0, 1)` -/

/-- The uniform law on `(0, 1)` gives `(-∞, t]` mass `t` for `t ∈ [0, 1]`. -/
lemma uniformIoo_real_Iic {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (volume.restrict (Ioo (0 : ℝ) 1)).real (Iic t) = t := by
  rw [measureReal_def, uniformIoo_Iic h0 h1, ENNReal.toReal_ofReal h0]

/-- The uniform law on `(0, 1)` gives `(1, ∞)` no mass. -/
lemma uniformIoo_Ioi_one : volume.restrict (Ioo (0 : ℝ) 1) (Ioi 1) = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioi,
    show Ioi (1 : ℝ) ∩ Ioo 0 1 = ∅ from eq_empty_of_forall_notMem fun _ h ↦ h.2.2.not_gt h.1,
    measure_empty]

/-! ### Copulas -/

/-- A **copula** on `ℝ^ι`: a probability measure whose every coordinate is uniformly distributed on
`(0, 1)`. Its distribution function `u ↦ C.real (Iic u)` is a copula in the sense of
McNeil–Frey–Embrechts, Definition 7.1. -/
structure IsCopula {ι : Type*} (C : Measure (ι → ℝ)) : Prop where
  /-- A copula is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure C
  /-- Every coordinate of a copula is uniform on `(0, 1)`. -/
  map_eval (i : ι) : C.map (fun v ↦ v i) = volume.restrict (Ioo 0 1)

namespace IsCopula

variable {ι : Type*} {C : Measure (ι → ℝ)}

/-- Under a copula, each coordinate has the uniform law on `(0, 1)`. -/
lemma hasLaw_eval (hC : IsCopula C) (i : ι) :
    HasLaw (fun v : ι → ℝ ↦ v i) (volume.restrict (Ioo 0 1)) C :=
  ⟨(measurable_pi_apply i).aemeasurable, hC.map_eval i⟩

/-- The mass a copula gives to a condition on one coordinate is its uniform probability. -/
lemma measure_coord_preimage (hC : IsCopula C) (i : ι) {s : Set ℝ} (hs : MeasurableSet s) :
    C {v | v i ∈ s} = volume.restrict (Ioo 0 1) s := by
  rw [← hC.map_eval i, Measure.map_apply (measurable_pi_apply i) hs]
  rfl

/-- **Uniform margins**: `C(vᵢ ≤ t) = t` for `t ∈ [0, 1]`. -/
lemma measureReal_coord_le (hC : IsCopula C) (i : ι) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    C.real {v | v i ≤ t} = t := by
  rw [measureReal_def, show {v : ι → ℝ | v i ≤ t} = {v | v i ∈ Iic t} from rfl,
    hC.measure_coord_preimage i measurableSet_Iic, ← measureReal_def, uniformIoo_real_Iic h0 h1]

/-- Almost every point of a copula lies in the open cube `(0, 1)^ι`. -/
lemma ae_mem_Ioo [Countable ι] (hC : IsCopula C) : ∀ᵐ v ∂C, ∀ i, v i ∈ Ioo 0 1 := by
  refine ae_all_iff.2 fun i ↦ ?_
  have hmeas : MeasurableSet (Ioo (0 : ℝ) 1)ᶜ := measurableSet_Ioo.compl
  have h := hC.measure_coord_preimage i hmeas
  rw [Measure.restrict_apply hmeas, compl_inter_self, measure_empty] at h
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with v hv
  simpa using hv

/-- **Upper Fréchet–Hoeffding bound**: `C(u) ≤ uᵢ` for every coordinate with `uᵢ ∈ [0, 1]`,
i.e. `C(u) ≤ minᵢ uᵢ`. -/
theorem measureReal_Iic_le (hC : IsCopula C) (u : ι → ℝ) (i : ι) (hi : u i ∈ Icc 0 1) :
    C.real (Iic u) ≤ u i := by
  have := hC.isProbabilityMeasure
  calc C.real (Iic u) ≤ C.real {v | v i ≤ u i} := measureReal_mono fun v hv ↦ hv i
    _ = u i := hC.measureReal_coord_le i hi.1 hi.2

/-- **Lower Fréchet–Hoeffding bound**: `∑ uᵢ − (d − 1) ≤ C(u)` on `[0, 1]^ι`, the union bound on
the complement of the orthant. -/
theorem sum_sub_le_measureReal_Iic [Fintype ι] (hC : IsCopula C) (u : ι → ℝ)
    (hu : ∀ i, u i ∈ Icc 0 1) : ∑ i, u i - (Fintype.card ι - 1) ≤ C.real (Iic u) := by
  have := hC.isProbabilityMeasure
  have hcompl : (Iic u)ᶜ = ⋃ i, {v : ι → ℝ | u i < v i} := by
    ext v
    simp [Pi.le_def]
  have hcoord (i : ι) : C.real {v : ι → ℝ | u i < v i} = 1 - u i := by
    rw [show {v : ι → ℝ | u i < v i} = {v | v i ≤ u i}ᶜ by ext v; simp,
      probReal_compl_eq_one_sub (measurableSet_le (measurable_pi_apply i) measurable_const),
      hC.measureReal_coord_le i (hu i).1 (hu i).2]
  have hunion := measureReal_iUnion_fintype_le (μ := C) fun i ↦ {v : ι → ℝ | u i < v i}
  rw [← hcompl, probReal_compl_eq_one_sub measurableSet_Iic] at hunion
  simp only [hcoord, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hunion
  linarith

end IsCopula

/-! ### Joint distribution functions determine laws on `ℝ^ι` -/

/-- The lower half-lines are a countable spanning family of `ℝ`. -/
lemma isCountablySpanning_range_Iic : IsCountablySpanning (range (Iic : ℝ → Set ℝ)) :=
  ⟨fun n : ℕ ↦ Iic (n : ℝ), fun _ ↦ mem_range_self _,
    iUnion_eq_univ_iff.2 fun x ↦ ⟨⌈x⌉₊, Nat.le_ceil x⟩⟩

/-- **Joint distribution functions determine probability laws on `ℝ^ι`**: two probability measures
that agree on every lower orthant `Iic u` are equal. The orthants are the boxes built from the
π-system of half-lines, which generates the product σ-algebra. -/
theorem ext_of_measure_Iic_pi {ι : Type*} [Finite ι] {μ ν : Measure (ι → ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : ∀ u, μ (Iic u) = ν (Iic u)) :
    μ = ν := by
  refine ext_of_generate_finite (pi univ '' pi univ fun _ ↦ range Iic)
    (generateFrom_eq_pi (fun _ ↦ (borel_eq_generateFrom_Iic ℝ).symm.trans
      BorelSpace.measurable_eq.symm) fun _ ↦ isCountablySpanning_range_Iic).symm
    (IsPiSystem.pi fun _ ↦ isPiSystem_Iic) ?_ (by simp)
  rintro _ ⟨s, hs, rfl⟩
  choose u hu using fun i ↦ hs i (mem_univ i)
  rw [show pi univ s = Iic u by rw [← funext hu, pi_univ_Iic]]
  exact h u

/-! ### The independence, comonotonicity and countermonotonicity copulas -/

section Fundamental

variable (ι : Type*) [Fintype ι]

/-- The **independence copula** `Π`: the law of a vector of independent uniforms. -/
noncomputable def independenceCopula : Measure (ι → ℝ) :=
  Measure.pi fun _ ↦ volume.restrict (Ioo 0 1)

/-- The **comonotonicity copula** `M`: the law of `(U, …, U)` for a single uniform `U`. -/
noncomputable def comonotoneCopula : Measure (ι → ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).map fun t _ ↦ t

variable {ι}

/-- `Π` is a copula. -/
theorem isCopula_independenceCopula : IsCopula (independenceCopula ι) :=
  ⟨inferInstanceAs (IsProbabilityMeasure (Measure.pi _)),
    fun i ↦ (measurePreserving_eval _ i).map_eq⟩

/-- `Π(u) = ∏ uᵢ` on `[0, 1]^ι`. -/
theorem independenceCopula_real_Iic (u : ι → ℝ) (hu : ∀ i, u i ∈ Icc 0 1) :
    (independenceCopula ι).real (Iic u) = ∏ i, u i := by
  rw [independenceCopula, ← pi_univ_Iic, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun i _ ↦ uniformIoo_real_Iic (hu i).1 (hu i).2

omit [Fintype ι] in
/-- `M` is a copula. -/
theorem isCopula_comonotoneCopula : IsCopula (comonotoneCopula ι) where
  isProbabilityMeasure :=
    inferInstanceAs (IsProbabilityMeasure ((volume.restrict (Ioo (0 : ℝ) 1)).map fun t _ ↦ t))
  map_eval i := by
    rw [comonotoneCopula, Measure.map_map (measurable_pi_apply i) (by fun_prop)]
    exact Measure.map_id

/-- `M(u) = minᵢ uᵢ` on `[0, 1]^ι`: the comonotonicity copula attains the upper Fréchet–Hoeffding
bound. -/
theorem comonotoneCopula_real_Iic [Nonempty ι] (u : ι → ℝ) (hu : ∀ i, u i ∈ Icc 0 1) :
    (comonotoneCopula ι).real (Iic u) = Finset.univ.inf' Finset.univ_nonempty u := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty u
  rw [comonotoneCopula, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    show (fun t _ ↦ t) ⁻¹' Iic u = Iic (Finset.univ.inf' Finset.univ_nonempty u) by
      ext t; simp [Pi.le_def], hi]
  exact uniformIoo_real_Iic (hu i).1 (hu i).2

/-- The **countermonotonicity copula** `W` in dimension two: the law of `(U, 1 − U)`. -/
noncomputable def countermonotoneCopula : Measure (Fin 2 → ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).map fun t ↦ ![t, 1 - t]

/-- The reflection `t ↦ 1 − t` preserves the uniform law on `(0, 1)`. -/
lemma map_one_sub_uniformIoo :
    (volume.restrict (Ioo (0 : ℝ) 1)).map (fun t ↦ 1 - t) = volume.restrict (Ioo 0 1) := by
  have h := (volume.measurePreserving_sub_left (1 : ℝ)).restrict_preimage
    (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))
  rw [show (fun t : ℝ ↦ 1 - t) ⁻¹' Ioo 0 1 = Ioo 0 1 by
    ext t; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith
    [h.1, h.2]] at h
  exact h.map_eq

/-- `W` is a copula. -/
theorem isCopula_countermonotoneCopula : IsCopula countermonotoneCopula where
  isProbabilityMeasure :=
    inferInstanceAs (IsProbabilityMeasure
      ((volume.restrict (Ioo (0 : ℝ) 1)).map fun t ↦ ![t, 1 - t]))
  map_eval i := by
    rw [countermonotoneCopula, Measure.map_map (measurable_pi_apply i) (by fun_prop)]
    fin_cases i
    · exact Measure.map_id
    · exact map_one_sub_uniformIoo

/-- `W(u) = max (u₀ + u₁ − 1) 0` on `[0, 1]²`: in dimension two the countermonotonicity copula
attains the lower Fréchet–Hoeffding bound. -/
theorem countermonotoneCopula_real_Iic (u : Fin 2 → ℝ) (hu : ∀ i, u i ∈ Icc 0 1) :
    countermonotoneCopula.real (Iic u) = max (u 0 + u 1 - 1) 0 := by
  rw [countermonotoneCopula, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    show (fun t ↦ ![t, 1 - t]) ⁻¹' Iic u = Icc (1 - u 1) (u 0) by
      ext t
      simp only [mem_preimage, mem_Iic, Pi.le_def, Fin.forall_fin_two, mem_Icc]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2],
    measureReal_def, Measure.restrict_apply measurableSet_Icc]
  have hsub : Icc (1 - u 1) (u 0) ∩ Ioo 0 1 ⊆ Icc (1 - u 1) (u 0) := inter_subset_left
  have hsup : Ioo (1 - u 1) (u 0) ⊆ Icc (1 - u 1) (u 0) ∩ Ioo 0 1 := fun t ht ↦
    ⟨Ioo_subset_Icc_self ht, by linarith [ht.1, (hu 1).2], by linarith [ht.2, (hu 0).2]⟩
  rw [le_antisymm ((measure_mono hsub).trans_eq Real.volume_Icc)
    ((Real.volume_Ioo.symm.trans_le (measure_mono hsup))), ENNReal.toReal_ofReal',
        sub_sub_eq_add_sub]

end Fundamental

/-! ### The lower Fréchet–Hoeffding bound is not a copula in dimension `d ≥ 3` -/

/-- **The lower Fréchet–Hoeffding bound is not a copula for `d ≥ 3`** (QRM Exercise Book,
Exercise 7.3). No copula on `ℝ^ι` with `card ι ≥ 3` has distribution function
`max (∑ uᵢ − (d − 1)) 0` on `[0, 1]^ι`.

Suppose one did. For two coordinates `a ≠ b`, the point with `uₐ = u_b = 1/2` and all other
entries `1` gives `max (d − 1 − (d − 1)) 0 = 0`. The coordinates of a copula are almost surely
below `1`, so `{Uₐ ≤ 1/2} ∩ {U_b ≤ 1/2}` is null. Three such events are then pairwise almost
disjoint and each has mass `1/2`, so their union would have mass `3/2 > 1`. -/
theorem not_exists_isCopula_frechetLower {ι : Type*} [Fintype ι]
    (hι : 3 ≤ Fintype.card ι) :
    ¬ ∃ C : Measure (ι → ℝ), IsCopula C ∧ ∀ u : ι → ℝ, (∀ i, u i ∈ Icc 0 1) →
      C.real (Iic u) = max (∑ i, u i - (Fintype.card ι - 1)) 0 := by
  classical
  rintro ⟨C, hC, hW⟩
  have := hC.isProbabilityMeasure
  obtain ⟨e⟩ :=
      Function.Embedding.nonempty_of_card_le (by simpa using hι : Fintype.card (Fin 3) ≤ _)
  set A : ι → Set (ι → ℝ) := fun a ↦ {v | v a ≤ 1 / 2}
  have hA (a : ι) : C (A a) = ENNReal.ofReal (1 / 2) := by
    rw [← ofReal_measureReal, hC.measureReal_coord_le a (by norm_num) (by norm_num)]
  have hAmeas (a : ι) : MeasurableSet (A a) :=
    measurableSet_le (measurable_pi_apply a) measurable_const
  -- coordinates exceed `1` only on a null set
  have hbig : C {v : ι → ℝ | ∃ c, 1 < v c} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hC.ae_mem_Ioo] with v hv ⟨c, hc⟩
    exact lt_asymm (hv c).2 hc
  -- two distinct coordinates are almost never both at most `1/2`
  have hpair {a b : ι} (hab : a ≠ b) : AEDisjoint C (A a) (A b) := by
    set u : ι → ℝ := fun c ↦ 1 - (if c = a then 1 / 2 else 0) - (if c = b then 1 / 2 else 0)
    have hua : u a = 1 / 2 := by simp only [u, ite_eq_right hab]; norm_num
    have hub : u b = 1 / 2 := by simp only [u, ite_eq_right hab.symm]; norm_num
    have huc {c : ι} (hca : c ≠ a) (hcb : c ≠ b) : u c = 1 := by
      simp only [u, ite_eq_right hca, ite_eq_right hcb]; norm_num
    have hu : ∀ c, u c ∈ Icc 0 1 := fun c ↦ by
      by_cases hca : c = a
      · rw [hca, hua]; norm_num
      by_cases hcb : c = b
      · rw [hcb, hub]; norm_num
      rw [huc hca hcb]; norm_num
    have hsum : ∑ c, u c = Fintype.card ι - 1 := by
      simp only [u, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    have hIic : C (Iic u) = 0 := by
      rw [← ofReal_measureReal, hW u hu, hsum, sub_self, max_self, ENNReal.ofReal_zero]
    refine measure_mono_null (fun v hv ↦ ?_) (measure_union_null hIic hbig)
    by_contra hnot
    rw [mem_union, not_or] at hnot
    refine hnot.1 fun c ↦ ?_
    by_cases hca : c = a
    · rw [hca, hua]; exact hv.1
    by_cases hcb : c = b
    · rw [hcb, hub]; exact hv.2
    rw [huc hca hcb]
    exact not_lt.1 fun h ↦ hnot.2 ⟨c, h⟩
  have hne (i j : Fin 3) (hij : i ≠ j) : e i ≠ e j := e.injective.ne hij
  have hunion : C (A (e 0) ∪ A (e 1) ∪ A (e 2)) = ENNReal.ofReal (3 / 2) := by
    rw [measure_union₀ (hAmeas _).nullMeasurableSet
        (((hpair (hne 0 2 (by decide))).union_left (hpair (hne 1 2 (by decide))))),
      measure_union₀ (hAmeas _).nullMeasurableSet (hpair (hne 0 1 (by decide))), hA, hA, hA,
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hle := prob_le_one (μ := C) (s := A (e 0) ∪ A (e 1) ∪ A (e 2))
  rw [hunion, ENNReal.ofReal_le_one] at hle
  norm_num at hle

end MathFin
