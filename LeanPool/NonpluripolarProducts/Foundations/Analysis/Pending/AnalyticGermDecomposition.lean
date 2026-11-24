/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicGermNoetherian

/-!
# Decomposition of analytic germs into irreducible germs

For a complex normed space `E` we study germs at `0` of analytic subsets of `E`: a set `A`
is an *analytic germ* (`IsAnalyticGerm A`) if, near `0`, it is the common zero set of finitely
many functions complex differentiable near `0`.  Set germs are compared with `A =ᶠ[𝓝 0] B` and
`A ≤ᶠ[𝓝 0] B`.

To such a set we attach its vanishing ideal `vanishingIdeal A` in the ring `HolGerm E` of
holomorphic germs.  A weak form of the Nullstellensatz (`le_of_vanishingIdeal_le`) shows that
analytic germs are determined by their vanishing ideals, and irreducible germs correspond to
prime vanishing ideals (`isIrreducibleGerm_iff_isPrime`).  When `HolGerm E` is Noetherian
(e.g. `E = ℂⁿ`), every analytic germ is an irredundant finite union of irreducible analytic
germs (`exists_irreducible_decomposition`).

## Main declarations

* `IsAnalyticGerm A` : `A` is, near `0`, the zero set of finitely many holomorphic functions.
* `vanishingIdeal A` : the ideal of holomorphic germs vanishing on `A` near `0`.
* `le_of_vanishingIdeal_le` : Nullstellensatz-lite.
* `IsIrreducibleGerm A`, `isIrreducibleGerm_iff_isPrime`.
* `exists_irreducible_decomposition` : decomposition into irreducible germs.

## References

* R. C. Gunning, H. Rossi, *Analytic functions of several complex variables*, §II.E.
* E. M. Chirka, *Complex analytic sets*, §1.5.
* T. de Jong, G. Pfister, *Local analytic geometry*, §3.4.
-/

@[expose] public section

open Filter Topology

namespace SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Analytic germs -/

/-- A set `A` is an analytic germ at `0` if, near `0`, it is the common zero set of finitely
many functions which are complex differentiable near `0`. -/
def IsAnalyticGerm (A : Set E) : Prop :=
  ∃ (s : ℕ) (g : Fin s → E → ℂ), (∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (g j) z) ∧
    ∀ᶠ z in 𝓝 (0 : E), (z ∈ A ↔ ∀ j, g j z = 0)

/-- An analytic germ may be described by a family of functions indexed by any finite type. -/
theorem isAnalyticGerm_of_finite {ι : Type*} [Finite ι] {A : Set E} (g : ι → E → ℂ)
    (hg : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (g i) z)
    (hA : ∀ᶠ z in 𝓝 (0 : E), (z ∈ A ↔ ∀ i, g i z = 0)) : IsAnalyticGerm A := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine ⟨n, fun j => g (e.symm j), fun j => hg _, hA.mono fun z hz => hz.trans ?_⟩
  exact ⟨fun h j => h _, fun h i => by simpa using h (e i)⟩

/-- Being an analytic germ only depends on the germ of the set at `0`. -/
theorem IsAnalyticGerm.congr {A B : Set E} (hA : IsAnalyticGerm A) (hAB : A =ᶠ[𝓝 0] B) :
    IsAnalyticGerm B := by
  obtain ⟨s, g, hg, hAg⟩ := hA
  refine ⟨s, g, hg, (hAg.and (eventuallyEqSet_iff.1 hAB)).mono fun z hz => ?_⟩
  exact hz.2.symm.trans hz.1

/-- The whole space is an analytic germ. -/
theorem isAnalyticGerm_univ : IsAnalyticGerm (Set.univ : Set E) :=
  ⟨0, Fin.elim0, fun j => j.elim0, Eventually.of_forall fun _ => by simp⟩

/-- The empty set is an analytic germ. -/
theorem isAnalyticGerm_empty : IsAnalyticGerm (∅ : Set E) :=
  isAnalyticGerm_of_finite (ι := Unit) (fun _ _ => 1)
    (fun _ => eventually_differentiableAt_const 1) (Eventually.of_forall fun _ => by simp)

/-- The zero set of a function differentiable near `0` is an analytic germ. -/
theorem isAnalyticGerm_zeroSet {f : E → ℂ} (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    IsAnalyticGerm {z | f z = 0} :=
  isAnalyticGerm_of_finite (ι := Unit) (fun _ => f) (fun _ => hf)
    (Eventually.of_forall fun _ => by simp)

/-- The intersection of two analytic germs is an analytic germ. -/
theorem IsAnalyticGerm.inter {A B : Set E} (hA : IsAnalyticGerm A) (hB : IsAnalyticGerm B) :
    IsAnalyticGerm (A ∩ B) := by
  obtain ⟨s, g, hg, hAg⟩ := hA
  obtain ⟨t, h, hh, hBh⟩ := hB
  refine isAnalyticGerm_of_finite (Sum.elim g h) (fun i => ?_) ((hAg.and hBh).mono ?_)
  · cases i <;> simp [hg, hh]
  · intro z hz
    simp [Set.mem_inter_iff, hz.1, hz.2, Sum.forall]

/-- The union of two analytic germs is an analytic germ, cut out by the pairwise products of
the defining functions. -/
theorem IsAnalyticGerm.union {A B : Set E} (hA : IsAnalyticGerm A) (hB : IsAnalyticGerm B) :
    IsAnalyticGerm (A ∪ B) := by
  obtain ⟨s, g, hg, hAg⟩ := hA
  obtain ⟨t, h, hh, hBh⟩ := hB
  refine isAnalyticGerm_of_finite (fun p : Fin s × Fin t => fun z => g p.1 z * h p.2 z)
    (fun p => eventually_differentiableAt_mul (hg p.1) (hh p.2)) ((hAg.and hBh).mono ?_)
  intro z hz
  rw [Set.mem_union, hz.1, hz.2]
  constructor
  · rintro (H | H) p
    · simp [H p.1]
    · simp [H p.2]
  · intro H
    by_cases hg0 : ∀ i, g i z = 0
    · exact Or.inl hg0
    · push Not at hg0
      obtain ⟨i, hi⟩ := hg0
      exact Or.inr fun j => (mul_eq_zero.1 (H (i, j))).resolve_left hi

/-- Intersecting an analytic germ with the zero set of a function differentiable near `0`
gives an analytic germ. -/
theorem IsAnalyticGerm.inter_zeroSet {A : Set E} (hA : IsAnalyticGerm A) {f : E → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) : IsAnalyticGerm (A ∩ {z | f z = 0}) :=
  hA.inter (isAnalyticGerm_zeroSet hf)

/-! ### The vanishing ideal -/

/-- The ideal of holomorphic germs at `0` vanishing on `A` near `0`. -/
def vanishingIdeal (A : Set E) : Ideal (HolGerm E) where
  carrier := {φ | ∃ (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z),
    φ = HolGerm.mk f hf ∧ ∀ᶠ z in 𝓝 0, z ∈ A → f z = 0}
  zero_mem' := ⟨0, eventually_differentiableAt_zero, HolGerm.mk_zero.symm,
    Eventually.of_forall fun _ _ => rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl, hfA⟩ ⟨g, hg, rfl, hgA⟩
    refine ⟨_, _, (HolGerm.mk_add f g hf hg).symm, (hfA.and hgA).mono fun z hz hzA => ?_⟩
    simp [hz.1 hzA, hz.2 hzA]
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl, hfA⟩
    obtain ⟨g, hg, rfl⟩ := HolGerm.exists_eq_mk c
    refine ⟨_, _, (HolGerm.mk_mul g f hg hf).symm, hfA.mono fun z hz hzA => ?_⟩
    simp [hz hzA]

/-- Characterization of membership in the vanishing ideal via any representative. -/
theorem mem_vanishingIdeal_mk {A : Set E} {f : E → ℂ}
    {hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z} :
    HolGerm.mk f hf ∈ vanishingIdeal A ↔ ∀ᶠ z in 𝓝 0, z ∈ A → f z = 0 := by
  refine ⟨fun ⟨g, hg, hfg, hgA⟩ => ?_, fun h => ⟨f, hf, rfl, h⟩⟩
  exact ((HolGerm.mk_eq_mk_iff.1 hfg).and hgA).mono fun z hz hzA => hz.1.trans (hz.2 hzA)

/-- The vanishing ideal is antitone with respect to germ inclusion. -/
theorem vanishingIdeal_anti {A B : Set E} (hAB : A ≤ᶠ[𝓝 0] B) :
    vanishingIdeal B ≤ vanishingIdeal A := by
  intro φ hφ
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk φ
  exact mem_vanishingIdeal_mk.2 <|
    ((mem_vanishingIdeal_mk.1 hφ).and hAB).mono fun z hz hzA => hz.1 (hz.2 hzA)

/-- The vanishing ideal only depends on the germ of the set at `0`. -/
theorem vanishingIdeal_congr {A B : Set E} (hAB : A =ᶠ[𝓝 0] B) :
    vanishingIdeal A = vanishingIdeal B :=
  le_antisymm (vanishingIdeal_anti hAB.superset) (vanishingIdeal_anti hAB.subset)

/-- The vanishing ideal of `A` is the whole ring iff `A` is empty near `0`. -/
theorem vanishingIdeal_eq_top_iff {A : Set E} :
    vanishingIdeal A = ⊤ ↔ A =ᶠ[𝓝 0] (∅ : Set E) := by
  rw [Ideal.eq_top_iff_one, ← HolGerm.mk_one, mem_vanishingIdeal_mk, eventuallyEqSet_iff]
  simp

/-! ### Nullstellensatz-lite -/

/-- **Nullstellensatz-lite.** If `B` is an analytic germ and every holomorphic germ vanishing
on `B` vanishes on `A`, then `A` is contained in `B` near `0`. -/
theorem le_of_vanishingIdeal_le {A B : Set E} (hB : IsAnalyticGerm B)
    (h : vanishingIdeal B ≤ vanishingIdeal A) : A ≤ᶠ[𝓝 0] B := by
  obtain ⟨s, g, hg, hBg⟩ := hB
  have hgA : ∀ j, ∀ᶠ z in 𝓝 0, z ∈ A → g j z = 0 := fun j =>
    (mem_vanishingIdeal_mk (hf := hg j)).1 <| h <| (mem_vanishingIdeal_mk (hf := hg j)).2 <|
      hBg.mono fun z hz hzB => hz.1 hzB j
  exact ((eventually_all.2 hgA).and hBg).mono fun z hz hzA => hz.2.2 fun j => hz.1 j hzA

/-- For an analytic germ `B`, `I(B) ≤ I(A)` iff `A ≤ᶠ B`. -/
theorem vanishingIdeal_le_iff {A B : Set E} (hB : IsAnalyticGerm B) :
    vanishingIdeal B ≤ vanishingIdeal A ↔ A ≤ᶠ[𝓝 0] B :=
  ⟨le_of_vanishingIdeal_le hB, vanishingIdeal_anti⟩

/-- Two analytic germs coincide iff their vanishing ideals coincide. -/
theorem eventuallyEq_iff_vanishingIdeal_eq {A B : Set E} (hA : IsAnalyticGerm A)
    (hB : IsAnalyticGerm B) : A =ᶠ[𝓝 0] B ↔ vanishingIdeal A = vanishingIdeal B :=
  ⟨vanishingIdeal_congr, fun h =>
    (le_of_vanishingIdeal_le hB h.ge).antisymm (le_of_vanishingIdeal_le hA h.le)⟩

/-- A strict germ inclusion of analytic germs gives a strict inclusion of vanishing ideals. -/
theorem vanishingIdeal_lt_of_lt {A B : Set E} (hA : IsAnalyticGerm A) (hAB : A ≤ᶠ[𝓝 0] B)
    (hBA : ¬ B ≤ᶠ[𝓝 0] A) : vanishingIdeal B < vanishingIdeal A :=
  lt_of_le_not_ge (vanishingIdeal_anti hAB) fun h => hBA (le_of_vanishingIdeal_le hA h)

/-! ### Irreducible germs -/

/-- An analytic germ is irreducible if it is nonempty near `0` and, whenever it is (near `0`)
the union of two analytic germs, it coincides with one of them near `0`. -/
def IsIrreducibleGerm (A : Set E) : Prop :=
  IsAnalyticGerm A ∧ ¬ (A =ᶠ[𝓝 0] (∅ : Set E)) ∧
    ∀ B C : Set E, IsAnalyticGerm B → IsAnalyticGerm C → A =ᶠ[𝓝 0] (B ∪ C : Set E) →
      (A =ᶠ[𝓝 0] B ∨ A =ᶠ[𝓝 0] C)

omit [NormedSpace ℂ E] in
/-- If `f * g` vanishes on `A` near `0`, then near `0` the set `A` is the union of its
intersections with the zero sets of `f` and of `g`. -/
theorem eventuallyEq_inter_zeroSet_union {A : Set E} {f g : E → ℂ}
    (h : ∀ᶠ z in 𝓝 0, z ∈ A → f z * g z = 0) :
    A =ᶠ[𝓝 0] ((A ∩ {z | f z = 0}) ∪ (A ∩ {z | g z = 0}) : Set E) := by
  refine eventuallyEqSet_iff.2 (h.mono fun z hz => ?_)
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun hzA => (mul_eq_zero.1 (hz hzA)).imp (⟨hzA, ·⟩) (⟨hzA, ·⟩),
    fun h' => h'.elim And.left And.left⟩

/-- An analytic germ is irreducible iff its vanishing ideal is prime. -/
theorem isIrreducibleGerm_iff_isPrime {A : Set E} (hA : IsAnalyticGerm A) :
    IsIrreducibleGerm A ↔ (vanishingIdeal A).IsPrime := by
  constructor
  · rintro ⟨-, hne, hirr⟩
    refine Ideal.isPrime_iff.2 ⟨fun h => hne (vanishingIdeal_eq_top_iff.1 h), ?_⟩
    intro φ ψ hφψ
    obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk φ
    obtain ⟨g, hg, rfl⟩ := HolGerm.exists_eq_mk ψ
    rw [← HolGerm.mk_mul, mem_vanishingIdeal_mk] at hφψ
    rw [mem_vanishingIdeal_mk, mem_vanishingIdeal_mk]
    refine (hirr _ _ (hA.inter_zeroSet hf) (hA.inter_zeroSet hg)
      (eventuallyEq_inter_zeroSet_union hφψ)).imp (fun h => ?_) (fun h => ?_)
    · exact (eventuallyEqSet_iff.1 h).mono fun z hz hzA => (hz.1 hzA).2
    · exact (eventuallyEqSet_iff.1 h).mono fun z hz hzA => (hz.1 hzA).2
  · intro hP
    refine ⟨hA, fun h => hP.ne_top (vanishingIdeal_eq_top_iff.2 h), ?_⟩
    intro B C hB hC hABC
    have hBA : B ≤ᶠ[𝓝 0] A :=
      (Set.subset_union_left : B ⊆ B ∪ C).eventuallySubset.trans hABC.superset
    have hCA : C ≤ᶠ[𝓝 0] A :=
      (Set.subset_union_right : C ⊆ B ∪ C).eventuallySubset.trans hABC.superset
    by_contra hcon
    push Not at hcon
    have hB' : ¬ vanishingIdeal B ≤ vanishingIdeal A := fun h =>
      hcon.1 (hBA.antisymm (le_of_vanishingIdeal_le hB h)).symm
    have hC' : ¬ vanishingIdeal C ≤ vanishingIdeal A := fun h =>
      hcon.2 (hCA.antisymm (le_of_vanishingIdeal_le hC h)).symm
    obtain ⟨φ, hφB, hφA⟩ := Set.not_subset.1 hB'
    obtain ⟨ψ, hψC, hψA⟩ := Set.not_subset.1 hC'
    have hmul : φ * ψ ∈ vanishingIdeal A := by
      rw [vanishingIdeal_congr hABC]
      obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk φ
      obtain ⟨g, hg, rfl⟩ := HolGerm.exists_eq_mk ψ
      rw [← HolGerm.mk_mul, mem_vanishingIdeal_mk]
      rw [SetLike.mem_coe, mem_vanishingIdeal_mk] at hφB hψC
      refine (hφB.and hψC).mono fun z hz hzBC => ?_
      rcases hzBC with hzB | hzC
      · simp [hz.1 hzB]
      · simp [hz.2 hzC]
    exact (hP.mem_or_mem hmul).elim hφA hψA

/-! ### Decomposition into irreducible germs -/

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- The union of a family indexed by `Fin (m + n)` built with `Fin.append`. -/
theorem iUnion_fin_append {m n : ℕ} (B : Fin m → Set E) (C : Fin n → Set E) :
    (⋃ i, Fin.append B C i) = (⋃ i, B i) ∪ ⋃ i, C i := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    exact Fin.addCases (motive := fun i => z ∈ Fin.append B C i → _)
      (fun i hi => Or.inl ⟨i, by simpa using hi⟩) (fun i hi => Or.inr ⟨i, by simpa using hi⟩) i hi
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨Fin.castAdd n i, by simpa using hi⟩
    · exact ⟨Fin.natAdd m i, by simpa using hi⟩

/-- Existence of a (possibly redundant) decomposition of an analytic germ into finitely many
irreducible germs, when `HolGerm E` is Noetherian. -/
theorem exists_irreducible_cover [IsNoetherianRing (HolGerm E)] {A : Set E}
    (hA : IsAnalyticGerm A) :
    ∃ (r : ℕ) (B : Fin r → Set E), (∀ i, IsIrreducibleGerm (B i)) ∧
      (∀ i, B i ≤ᶠ[𝓝 0] A) ∧ A =ᶠ[𝓝 0] (⋃ i, B i) := by
  suffices H : ∀ I : Ideal (HolGerm E), ∀ A : Set E, vanishingIdeal A = I →
      IsAnalyticGerm A → ∃ (r : ℕ) (B : Fin r → Set E), (∀ i, IsIrreducibleGerm (B i)) ∧
        (∀ i, B i ≤ᶠ[𝓝 0] A) ∧ A =ᶠ[𝓝 0] (⋃ i, B i) from H _ A rfl hA
  intro I
  induction I using WellFoundedGT.induction with
  | _ I ih =>
  rintro A rfl hA
  by_cases hempty : A =ᶠ[𝓝 0] (∅ : Set E)
  · exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simpa using hempty⟩
  by_cases hprime : (vanishingIdeal A).IsPrime
  · refine ⟨1, fun _ => A, fun _ => (isIrreducibleGerm_iff_isPrime hA).2 hprime,
      fun _ => EventuallySubset.rfl, ?_⟩
    rw [Set.iUnion_const]
  obtain ⟨φ, ψ, hφψ, hφ, hψ⟩ : ∃ φ ψ, φ * ψ ∈ vanishingIdeal A ∧ φ ∉ vanishingIdeal A ∧
      ψ ∉ vanishingIdeal A := by
    rw [Ideal.isPrime_iff] at hprime
    push Not at hprime
    obtain ⟨φ, ψ, h1, h2, h3⟩ := hprime (fun h => hempty (vanishingIdeal_eq_top_iff.1 h))
    exact ⟨φ, ψ, h1, h2, h3⟩
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk φ
  obtain ⟨g, hg, rfl⟩ := HolGerm.exists_eq_mk ψ
  rw [← HolGerm.mk_mul, mem_vanishingIdeal_mk] at hφψ
  have hlt : ∀ {h : E → ℂ} (hh : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ h z),
      HolGerm.mk h hh ∉ vanishingIdeal A →
        vanishingIdeal A < vanishingIdeal (A ∩ {z | h z = 0}) := fun hh hnot =>
    lt_of_le_of_ne (vanishingIdeal_anti (Set.inter_subset_left : A ∩ _ ⊆ A).eventuallySubset)
      fun heq => hnot (heq ▸ mem_vanishingIdeal_mk.2 (Eventually.of_forall fun _ hz => hz.2))
  obtain ⟨r₁, B₁, hB₁, hB₁A, hA₁⟩ :=
    ih _ (hlt hf hφ) _ rfl (hA.inter_zeroSet hf)
  obtain ⟨r₂, B₂, hB₂, hB₂A, hA₂⟩ :=
    ih _ (hlt hg hψ) _ rfl (hA.inter_zeroSet hg)
  refine ⟨r₁ + r₂, Fin.append B₁ B₂, fun i => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using hB₁ i
    · simpa using hB₂ i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using (hB₁A i).trans (Set.inter_subset_left : A ∩ _ ⊆ A).eventuallySubset
    · simpa using (hB₂A i).trans (Set.inter_subset_left : A ∩ _ ⊆ A).eventuallySubset
  · rw [iUnion_fin_append]
    exact (eventuallyEq_inter_zeroSet_union hφψ).trans (hA₁.union hA₂)

omit [NormedSpace ℂ E] in
/-- Any finite family of sets can be replaced by a subfamily with the same union near `0` in
which no member is contained near `0` in another member. -/
theorem exists_irredundant (r : ℕ) (B : Fin r → Set E) :
    ∃ (r' : ℕ) (B' : Fin r' → Set E), (∀ i, ∃ j, B' i = B j) ∧
      (⋃ i, B' i) =ᶠ[𝓝 (0 : E)] (⋃ i, B i) ∧
      Pairwise (fun i j => ¬ (B' i ≤ᶠ[𝓝 (0 : E)] B' j)) := by
  induction r with
  | zero => exact ⟨0, B, fun i => ⟨i, rfl⟩, EventuallyEqSet.rfl, fun i => i.elim0⟩
  | succ m ih =>
    by_cases hpw : Pairwise (fun i j => ¬ (B i ≤ᶠ[𝓝 (0 : E)] B j))
    · exact ⟨m + 1, B, fun i => ⟨i, rfl⟩, EventuallyEqSet.rfl, hpw⟩
    simp only [Pairwise, not_forall, not_not] at hpw
    obtain ⟨i, j, hij, hle⟩ := hpw
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    obtain ⟨r', B', hB', hU, hpw'⟩ := ih (fun l => B (i.succAbove l))
    refine ⟨r', B', fun l => ?_, hU.trans ?_, hpw'⟩
    · obtain ⟨l', hl'⟩ := hB' l
      exact ⟨_, hl'⟩
    · refine eventuallyEqSet_iff.2 (hle.mono fun z hz => ?_)
      simp only [Set.mem_iUnion]
      refine ⟨fun ⟨l, hl⟩ => ⟨_, hl⟩, fun ⟨l, hl⟩ => ?_⟩
      rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨l', rfl⟩
      · exact ⟨k, hk ▸ hz hl⟩
      · exact ⟨l', hl⟩

/-- **Decomposition of analytic germs.** If `HolGerm E` is Noetherian, every analytic germ
at `0` is, near `0`, a finite irredundant union of irreducible analytic germs contained in it. -/
theorem exists_irreducible_decomposition [IsNoetherianRing (HolGerm E)] {A : Set E}
    (hA : IsAnalyticGerm A) :
    ∃ (r : ℕ) (B : Fin r → Set E), (∀ i, IsIrreducibleGerm (B i)) ∧
      (∀ i, B i ≤ᶠ[𝓝 0] A) ∧ A =ᶠ[𝓝 0] (⋃ i, B i) ∧
      Pairwise (fun i j => ¬ (B i ≤ᶠ[𝓝 0] B j)) := by
  obtain ⟨r, B, hB, hBA, hAB⟩ := exists_irreducible_cover hA
  obtain ⟨r', B', hB', hU, hpw⟩ := exists_irredundant r B
  refine ⟨r', B', fun i => ?_, fun i => ?_, hAB.trans hU.symm, hpw⟩
  · obtain ⟨j, hj⟩ := hB' i
    exact hj ▸ hB j
  · obtain ⟨j, hj⟩ := hB' i
    exact hj ▸ hBA j

/-- Every analytic germ in `ℂⁿ` is a finite irredundant union of irreducible analytic germs. -/
theorem exists_irreducible_decomposition_euclidean {n : ℕ}
    {A : Set (EuclideanSpace ℂ (Fin n))} (hA : IsAnalyticGerm A) :
    ∃ (r : ℕ) (B : Fin r → Set (EuclideanSpace ℂ (Fin n))), (∀ i, IsIrreducibleGerm (B i)) ∧
      (∀ i, B i ≤ᶠ[𝓝 0] A) ∧ A =ᶠ[𝓝 0] (⋃ i, B i) ∧
      Pairwise (fun i j => ¬ (B i ≤ᶠ[𝓝 0] B j)) :=
  haveI := isNoetherianRing_holGerm_euclidean n
  exists_irreducible_decomposition hA

end SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition
