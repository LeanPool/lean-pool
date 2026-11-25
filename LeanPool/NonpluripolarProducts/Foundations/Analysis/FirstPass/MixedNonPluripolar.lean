/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BTTruncations
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MixedMongeAmpere

/-!
# Componentwise truncations and their common strict loci

The maximum is taken in EReal before `toReal`, in every component.
The common locus retains Ω even for the empty tuple. Its exhaustion omits
exactly the union of component pole sets. No BT existence is imported.
Sources: BEGZ `equ:nonpp`; revised `sec:npp`. The inherited density convention
is `ddC = i ∂∂bar / (2π)`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar

open MongeAmpere MixedMongeAmpere

variable {n : ℕ} {Ω : Opens (ComplexModel n)}
variable {u : Fin n → ComplexModel n → EReal}

/-- The tuple of potentials truncated below at the same level. -/
def mixedTruncation (u : Fin n → ComplexModel n → EReal) (k : ℕ) :
    Fin n → ComplexModel n → EReal := fun i => truncation (u i) k

/-- The real-valued representatives of the truncated potentials. -/
def mixedTruncationReal (u : Fin n → ComplexModel n → EReal) (k : ℕ) :
    Fin n → ComplexModel n → ℝ := fun i => truncationReal (u i) k

/-- The part of the domain where all potentials exceed the truncation level. -/
def commonStrictLocus (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → EReal) (k : ℕ) : Set (ComplexModel n) :=
  {z | z ∈ Ω ∧ ∀ i, ((-(k : ℝ) : ℝ) : EReal) < u i z}

/-- The points where at least one potential takes the value `⊥`. -/
def componentPoleSet (u : Fin n → ComplexModel n → EReal) : Set (ComplexModel n) :=
  {z | ∃ i, u i z = ⊥}

theorem componentPoleSet_eq_iUnion (u : Fin n → ComplexModel n → EReal) :
    componentPoleSet u = ⋃ i, {z | u i z = ⊥} := by
  ext z
  simp [componentPoleSet]

theorem mixedTruncationReal_at_pole (k : ℕ) (i : Fin n) {z : ComplexModel n}
    (hz : u i z = ⊥) : mixedTruncationReal u k i z = -(k : ℝ) :=
  truncationReal_at_pole k hz

theorem coe_mixedTruncationReal (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (k : ℕ) (i : Fin n) {z : ComplexModel n} (hz : z ∈ Ω) :
    (mixedTruncationReal u k i z : EReal) = mixedTruncation u k i z :=
  coe_truncationReal (hu i) k hz

theorem mixedTruncation_plurisubharmonicOn (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (k : ℕ) (i : Fin n) : PlurisubharmonicOn (mixedTruncation u k i) Ω :=
  truncation_plurisubharmonicOn (hu i) k

theorem mixedTruncationReal_isLocallyBounded (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (k : ℕ) : IsLocallyBoundedMixedPshOn Ω (mixedTruncationReal u k) :=
  fun i => truncationReal_isLocallyBoundedPshOn (hu i) k

theorem commonStrictLocus_subset (k : ℕ) : commonStrictLocus Ω u k ⊆ Ω :=
  fun _ hz => hz.1

theorem commonStrictLocus_subset_component (k : ℕ) (i : Fin n) :
    commonStrictLocus Ω u k ⊆ strictTruncationLocus Ω (u i) k :=
  fun _ hz => ⟨hz.1, hz.2 i⟩

theorem mixedTruncation_eq_on_commonStrictLocus (k : ℕ) (i : Fin n) :
    EqOn (mixedTruncation u k i) (u i) (commonStrictLocus Ω u k) :=
  fun _ hz => truncation_eq_on_strictLocus k (commonStrictLocus_subset_component k i hz)

theorem mixedTruncationReal_eq_on_commonStrictLocus (k : ℕ) (i : Fin n) :
    EqOn (mixedTruncationReal u k i) (fun z => (u i z).toReal)
      (commonStrictLocus Ω u k) :=
  fun _ hz => congrArg EReal.toReal (mixedTruncation_eq_on_commonStrictLocus k i hz)

theorem commonStrictLocus_mono (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → EReal) : Monotone (commonStrictLocus Ω u) := by
  intro k l hkl z hz
  exact ⟨hz.1, fun i => (strictTruncationLocus_mono Ω (u i) hkl ⟨hz.1, hz.2 i⟩).2⟩

theorem mixedTruncation_nested {k l : ℕ} (hkl : k ≤ l) :
    mixedTruncation (mixedTruncation u l) k = mixedTruncation u k := by
  funext i
  exact truncation_truncation (u i) hkl

theorem mixedTruncationReal_nested (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {k l : ℕ} (hkl : k ≤ l) (i : Fin n) :
    EqOn (mixedTruncationReal u k i)
      (fun z => max (mixedTruncationReal u l i z) (-(k : ℝ))) Ω :=
  fun _ hz => (truncationReal_nested (hu i) hkl hz).symm

theorem commonStrictLocus_eq_real_superlevel (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {k l : ℕ} (hkl : k ≤ l) :
    commonStrictLocus Ω u k =
      {z | z ∈ Ω ∧ ∀ i, -(k : ℝ) < mixedTruncationReal u l i z} := by
  ext z
  constructor
  · intro hz
    refine ⟨hz.1, fun i => ?_⟩
    have hi := commonStrictLocus_subset_component k i hz
    rw [strictLocus_eq_truncationReal_superlevel (hu i) hkl] at hi
    exact hi.2
  · intro hz
    refine ⟨hz.1, fun i => ?_⟩
    have hi : z ∈ strictTruncationLocus Ω (u i) k := by
      rw [strictLocus_eq_truncationReal_superlevel (hu i) hkl]
      exact ⟨hz.1, hz.2 i⟩
    exact hi.2

theorem commonStrictLocus_eq_inter_iInter (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → EReal) (k : ℕ) :
    commonStrictLocus Ω u k = (Ω : Set (ComplexModel n)) ∩
      ⋂ i, strictTruncationLocus Ω (u i) k := by
  ext z
  simp only [commonStrictLocus, strictTruncationLocus, mem_inter_iff, mem_iInter,
    mem_ofPred_eq]
  exact ⟨fun hz => ⟨hz.1, fun i => ⟨hz.1, hz.2 i⟩⟩,
    fun hz => ⟨hz.1, fun i => (hz.2 i).2⟩⟩

theorem measurableSet_commonStrictLocus (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (k : ℕ) : MeasurableSet (commonStrictLocus Ω u k) := by
  rw [commonStrictLocus_eq_inter_iInter]
  exact Ω.isOpen.measurableSet.inter
    (MeasurableSet.iInter (fun i => measurableSet_strictTruncationLocus (hu i) k))

theorem pole_not_mem_commonStrictLocus (k : ℕ) {z : ComplexModel n}
    (hz : z ∈ componentPoleSet u) : z ∉ commonStrictLocus Ω u k := by
  obtain ⟨i, hi⟩ := hz
  exact fun h => pole_not_mem_strictLocus k hi (commonStrictLocus_subset_component k i h)

/-- Finite choice of levels is synchronized by their maximum, including n=0. -/
theorem iUnion_commonStrictLocus (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → EReal) :
    (⋃ k, commonStrictLocus Ω u k) = {z | z ∈ Ω ∧ ∀ i, u i z ≠ ⊥} := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    exact ⟨hk.1, fun i => ne_of_gt ((EReal.bot_lt_coe _).trans (hk.2 i))⟩
  · rintro ⟨hz, hu⟩
    have hex : ∀ i, ∃ k, z ∈ strictTruncationLocus Ω (u i) k := by
      intro i
      apply mem_iUnion.mp
      rw [iUnion_strictTruncationLocus]
      exact ⟨hz, hu i⟩
    choose f hf using hex
    refine mem_iUnion.mpr ⟨Finset.univ.sup f, hz, fun i => ?_⟩
    exact (strictTruncationLocus_mono Ω (u i)
      (Finset.le_sup (Finset.mem_univ i)) (hf i)).2

theorem compl_iUnion_commonStrictLocus (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → EReal) :
    (⋃ k, commonStrictLocus Ω u k)ᶜ = (Ω : Set (ComplexModel n))ᶜ ∪ componentPoleSet u := by
  rw [iUnion_commonStrictLocus]
  ext z
  simp only [mem_compl_iff, mem_ofPred_eq, mem_union, componentPoleSet,
    not_and_or, not_forall, not_not]
  rfl

theorem commonStrictLocus_diagonal (hn : 0 < n) (Ω : Opens (ComplexModel n))
    (v : ComplexModel n → EReal) (k : ℕ) :
    commonStrictLocus Ω (fun _ => v) k = strictTruncationLocus Ω v k := by
  ext z
  exact ⟨fun hz => ⟨hz.1, hz.2 ⟨0, hn⟩⟩, fun hz => ⟨hz.1, fun _ => hz.2⟩⟩

@[simp] theorem commonStrictLocus_zero (Ω : Opens (ComplexModel 0))
    (u : Fin 0 → ComplexModel 0 → EReal) (k : ℕ) :
    commonStrictLocus Ω u k = (Ω : Set (ComplexModel 0)) := by
  ext z
  simp [commonStrictLocus]

@[simp] theorem componentPoleSet_zero (u : Fin 0 → ComplexModel 0 → EReal) :
    componentPoleSet u = ∅ := by
  ext z
  simp [componentPoleSet]

end SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
