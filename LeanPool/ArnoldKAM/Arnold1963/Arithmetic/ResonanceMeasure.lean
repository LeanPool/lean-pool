/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.TypeD
public import LeanPool.ArnoldKAM.Arnold1963.Step.Nonresonance

/-!
Measure estimates for newly excluded lattice shells, using the strict mode cutoff. Previously
excluded shells are charged once.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

/-- The frequencies where a given Fourier pairing violates the prescribed small-divisor bound. -/
def resonanceSet {n : ℕ} (Ω : Set (ComplexSpace n)) (K : ℝ)
    (k : FourierIndex n) : Set (ComplexSpace n) :=
  Ω ∩ {ω | ‖indexPairing k ω‖ < K / indexLength k ^ (n + 1)}

/-- The union of resonances associated with one lattice shell. -/
def resonantShell {n : ℕ} (Ω : Set (ComplexSpace n)) (K : ℝ) (m : ℕ) :=
  ⋃ k ∈ latticeShell n m, resonanceSet Ω K k

/-- The integer shell radii introduced when the real Fourier cutoff increases. -/
def newShells (N₀ N₁ : ℝ) : Finset ℕ := Finset.Ico ⌈N₀⌉₊ ⌈N₁⌉₊

/-- The reciprocal-square sum budgeting the newly introduced resonance shells. -/
def newShellBudget (N₀ N₁ : ℝ) : ℝ := ∑ m ∈ newShells N₀ N₁, 1 / (m : ℝ) ^ 2

theorem FiniteNonresonant.mono_cutoff {n : ℕ} {ω : ComplexSpace n} {K N₀ N₁ : ℝ}
    (h : FiniteNonresonant ω K N₁) (hN : N₀ ≤ N₁) : FiniteNonresonant ω K N₀ := by
  intro k hk
  exact h k (mem_lowModes.mpr ⟨(mem_lowModes.mp hk).1, (mem_lowModes.mp hk).2.trans_le hN⟩)

theorem isClosed_finiteNonresonant {n : ℕ} (K N : ℝ) :
    IsClosed {ω : ComplexSpace n | FiniteNonresonant ω K N} := by
  simp only [FiniteNonresonant, ofPred_forall]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const ((continuous_iff_continuousAt.mpr
    fun ω => (analyticAt_indexPairing k ω).continuousAt).norm)

theorem isCompact_nonresonant_frequency_domain {n : ℕ} {Ω : Set (ComplexSpace n)}
    (hΩ : IsCompact Ω) (K N : ℝ) : IsCompact (nonresonantDomain Ω id K N) :=
  hΩ.inter_right (isClosed_finiteNonresonant K N)

theorem nonresonant_on_erosion {n : ℕ} {Ω : Set (ComplexSpace n)} {K N : ℝ}
    (d : ℝ≥0) {ω : ComplexSpace n} (hω : ω ∈ erosion (nonresonantDomain Ω id K N) d) :
    FiniteNonresonant ω K N := (erosion_subset _ _ hω).2

theorem mem_newShells {N₀ N₁ : ℝ} {m : ℕ} :
    m ∈ newShells N₀ N₁ ↔ N₀ ≤ (m : ℝ) ∧ (m : ℝ) < N₁ := by
  simp only [newShells, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil]

theorem nonresonant_removed_subset_new_shells {n : ℕ}
    {Ω E : Set (ComplexSpace n)} {K N₀ N₁ : ℝ}
    (hE : E ⊆ Ω) (hold : ∀ ω ∈ E, FiniteNonresonant ω K N₀) :
    E \ nonresonantDomain E id K N₁ ⊆
      ⋃ m ∈ newShells N₀ N₁, resonantShell Ω K m := by
  classical
  intro ω hω
  have hbad : ¬ FiniteNonresonant ω K N₁ := fun h => hω.2 ⟨hω.1, h⟩
  simp only [FiniteNonresonant, not_forall, not_le] at hbad
  obtain ⟨k, hk, hres⟩ := hbad
  have hlow : N₀ ≤ indexLength k := by
    by_contra! h
    exact (not_lt_of_ge (hold ω hω.1 k
      (mem_lowModes.mpr ⟨(mem_lowModes.mp hk).1, h⟩))) hres
  refine mem_iUnion.2 ⟨latticeLength k, mem_iUnion.2 ⟨?_, ?_⟩⟩
  · exact mem_newShells.mpr (by
      simpa only [← indexLength_eq_latticeLength] using ⟨hlow, (mem_lowModes.mp hk).2⟩)
  · exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨mem_latticeShell.mpr rfl, hE hω.1, hres⟩⟩

theorem TypeD.resonance_le {n : ℕ} {Ω : Set (ComplexSpace n)} {D K : ℝ}
    (d : TypeD Ω D) (hK : 0 ≤ K) {k : FourierIndex n} (hk : 0 < latticeLength k) :
    realVolume (resonanceSet Ω K k) ≤
      ENNReal.ofReal (2 * D * n * K / indexLength k ^ (n + 1)) * realVolume Ω := by
  let ℓ : RealSpace n := fun j => (k j : ℝ)
  have hlen : 1 ≤ indexLength k := by
    rw [indexLength_eq_latticeLength]
    exact_mod_cast hk
  have hpair : realCovectorPairing ℓ = indexPairing k := by
    funext z
    simp [realCovectorPairing, indexPairing, ℓ]
  have hl : covectorLength ℓ = indexLength k := rfl
  have ha : 0 ≤ K / indexLength k ^ (n + 1) := by positivity
  have hs := d.slab ℓ 0 (K / indexLength k ^ (n + 1)) (by rw [hl]; linarith) ha
  simp only [complexSlab, hpair, Complex.ofReal_zero, sub_zero] at hs
  apply hs.trans
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  rw [hl]
  have hh : 2 * (K / indexLength k ^ (n + 1)) / indexLength k ≤
      2 * (K / indexLength k ^ (n + 1)) := div_le_self (by positivity) hlen
  calc
    _ ≤ D * n * (2 * (K / indexLength k ^ (n + 1))) :=
      mul_le_mul_of_nonneg_left hh (by positivity [d.constant_pos])
    _ = _ := by ring

theorem TypeD.resonantShell_le {n m : ℕ} {Ω : Set (ComplexSpace n)} {D K : ℝ}
    (d : TypeD Ω D) (hn : 0 < n) (hm : 0 < m) (hK : 0 ≤ K) :
    realVolume (resonantShell Ω K m) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (n + 1) * n * D * K / (m : ℝ) ^ 2) * realVolume Ω := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let C := 2 * D * n * K / (m : ℝ) ^ (n + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity [d.constant_pos]
  have hcount : ((latticeShell n m).card : ℝ) ≤ 2 ^ n * (m : ℝ) ^ (n - 1) := by
    exact_mod_cast card_latticeShell_le n m hn hm
  have hpow : (m : ℝ) ^ (n + 1) = (m : ℝ) ^ (n - 1) * (m : ℝ) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ ∑ k ∈ latticeShell n m, realVolume (resonanceSet Ω K k) :=
      realVolume_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ latticeShell n m, ENNReal.ofReal C * realVolume Ω := by
      apply Finset.sum_le_sum
      intro k hk
      have he : indexLength k = (m : ℝ) := by
        rw [indexLength_eq_latticeLength, mem_latticeShell.mp hk]
      simpa only [he] using d.resonance_le (k := k) hK
        (by rw [mem_latticeShell.mp hk]; exact hm)
    _ = ENNReal.ofReal (((latticeShell n m).card : ℝ) * C) * realVolume Ω := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hC)]
      simp
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n * (m : ℝ) ^ (n - 1) * C) * realVolume Ω :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcount hC)) le_rfl
    _ = _ := by
      have he : (2 : ℝ) ^ n * (m : ℝ) ^ (n - 1) * C =
          (2 : ℝ) ^ (n + 1) * n * D * K / (m : ℝ) ^ 2 := by
        dsimp [C]
        rw [hpow, pow_succ]
        field_simp [ne_of_gt hmR]
        ring
      rw [he]

theorem TypeD.new_resonance_loss_le {n : ℕ} {Ω E : Set (ComplexSpace n)}
    {D K N₀ N₁ : ℝ} (d : TypeD Ω D) (hn : 0 < n) (hK : 0 ≤ K)
    (hN₀ : 1 ≤ N₀) (hE : E ⊆ Ω) (hold : ∀ ω ∈ E, FiniteNonresonant ω K N₀) :
    realVolume (E \ nonresonantDomain E id K N₁) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (n + 1) * n * D * K * newShellBudget N₀ N₁) *
        realVolume Ω := by
  calc
    _ ≤ realVolume (⋃ m ∈ newShells N₀ N₁, resonantShell Ω K m) :=
      realVolume_mono (nonresonant_removed_subset_new_shells hE hold)
    _ ≤ ∑ m ∈ newShells N₀ N₁, realVolume (resonantShell Ω K m) :=
      realVolume_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ newShells N₀ N₁,
        ENNReal.ofReal ((2 : ℝ) ^ (n + 1) * n * D * K / (m : ℝ) ^ 2) * realVolume Ω := by
      apply Finset.sum_le_sum
      intro m hm
      have hmR := (mem_newShells.mp hm).1
      exact d.resonantShell_le hn (by exact_mod_cast (show (0 : ℝ) < m by linarith)) hK
    _ = _ := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by
        positivity [d.constant_pos])]
      simp only [newShellBudget, Finset.mul_sum, div_eq_mul_inv, one_mul]

end KamProject.Arnold1963
