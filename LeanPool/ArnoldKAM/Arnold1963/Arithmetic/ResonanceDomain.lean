/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.FiniteTubes
public import LeanPool.ArnoldKAM.Arnold1963.Arithmetic.ResonanceMeasure

/-!
Finite-tube representations of iterated frequency domains. Each integer direction retains one
threshold, avoiding repeated tube counts as the cutoff grows and the domain is eroded.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

/-- An integer Fourier covector regarded as a real coordinate vector. -/
def integerCovector {n} (k : FourierIndex n) : RealSpace n := fun j => (k j : ℝ)

@[simp] theorem integerCovector_length {n} (k : FourierIndex n) :
    covectorLength (integerCovector k) = indexLength k := rfl

@[simp] theorem integerCovector_pairing {n} (k : FourierIndex n) (z : ComplexSpace n) :
    realCovectorPairing (integerCovector k) z = indexPairing k z := by
  simp [integerCovector, realCovectorPairing, indexPairing]

/-- Accumulated geometric erosion and resonance exclusions for a finite Fourier cutoff. -/
structure ResonanceDomainState (n : ℕ) (K N : ℝ) where
  /-- The accumulated erosion radius of the ambient frequency domain. -/
  radius : ℝ≥0
  /-- The exclusion width assigned to each Fourier index. -/
  width : FourierIndex n → ℝ
  width_pos : ∀ k ∈ lowModes n N, 0 < width k
  width_lower : ∀ k ∈ lowModes n N, K / indexLength k ^ (n + 1) ≤ width k

namespace ResonanceDomainState
variable {n : ℕ} {K N : ℝ} (s : ResonanceDomainState n K N)

/-- The frequency domain satisfying the state's erosion and finite resonance constraints. -/
def domain (Ω : Set (ComplexSpace n)) : Set (ComplexSpace n) :=
  finiteTubeDomain Ω (lowModes n N) integerCovector (fun _ => 0) s.width s.radius

theorem mem_domain {Ω : Set (ComplexSpace n)} {z : ComplexSpace n} :
    z ∈ s.domain Ω ↔ z ∈ erosion Ω s.radius ∧
      ∀ k ∈ lowModes n N, s.width k ≤ ‖indexPairing k z‖ := by
  simp only [domain, finiteTubeDomain, mem_ofPred_eq, integerCovector_pairing,
    Complex.ofReal_zero, sub_zero]

theorem subset (Ω : Set (ComplexSpace n)) : s.domain Ω ⊆ Ω :=
  finiteTubeDomain_subset _ _ _ _ _ _

theorem nonresonant {Ω : Set (ComplexSpace n)} {z} (hz : z ∈ s.domain Ω) :
    FiniteNonresonant z K N := fun k hk =>
  (s.width_lower k hk).trans ((s.mem_domain.mp hz).2 k hk)

theorem compact {Ω : Set (ComplexSpace n)} (hc : IsCompact Ω) : IsCompact (s.domain Ω) := by
  have he : s.domain Ω = erosion Ω s.radius ∩
      ⋂ k ∈ lowModes n N, {z | s.width k ≤ ‖indexPairing k z‖} := by
    ext z
    simp only [s.mem_domain, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [he]
  apply (isCompact_erosion hc _).inter_right
  exact isClosed_iInter fun k => isClosed_iInter fun _ =>
    isClosed_le continuous_const ((continuous_iff_continuousAt.mpr
      fun z => (analyticAt_indexPairing k z).continuousAt).norm)

theorem conj {Ω : Set (ComplexSpace n)} (hj : ConjInvariant Ω) : ConjInvariant (s.domain Ω) := by
  intro z hz
  obtain ⟨hzΩ, hz⟩ := s.mem_domain.mp hz
  apply s.mem_domain.mpr
  refine ⟨star_mem_erosion hj hzΩ, ?_⟩
  intro k hk
  simpa only [indexPairing_conj, norm_star] using hz k hk

/-- Increasing geometric erosion and widening each resonance exclusion accordingly. -/
def erode (d : ℝ≥0) : ResonanceDomainState n K N where
  radius := s.radius + d
  width := fun k => s.width k + (d : ℝ) * indexLength k
  width_pos := fun k hk => (s.width_pos k hk).trans_le (le_add_of_nonneg_right (by
    positivity [indexLength_nonneg k]))
  width_lower := fun k hk => (s.width_lower k hk).trans (le_add_of_nonneg_right (by
    positivity [indexLength_nonneg k]))

theorem erode_domain (Ω : Set (ComplexSpace n)) (d : ℝ≥0) :
    (s.erode d).domain Ω = erosion (s.domain Ω) d := by
  symm
  exact erosion_finiteTubeDomain Ω (lowModes n N) integerCovector (fun _ => 0) s.width
    s.radius d (fun k hk => (mem_lowModes.mp hk).1) s.width_pos

/-- Extending the Fourier cutoff while preserving old exclusions and initializing new ones. -/
def cut {N' : ℝ} (hK : 0 < K) (_hNN : N ≤ N') : ResonanceDomainState n K N' where
  radius := s.radius
  width := fun k => if k ∈ lowModes n N then s.width k else K / indexLength k ^ (n + 1)
  width_pos := by
    intro k hk
    split_ifs with hkold
    · exact s.width_pos k hkold
    · exact div_pos hK (pow_pos (mem_lowModes.mp hk).1 _)
  width_lower := by
    intro k hk
    split_ifs with hkold
    · exact s.width_lower k hkold
    · exact le_rfl

theorem cut_domain {N' : ℝ} (hK : 0 < K) (hNN : N ≤ N') (Ω : Set (ComplexSpace n)) :
    (s.cut hK hNN).domain Ω = nonresonantDomain (s.domain Ω) id K N' := by
  classical
  have hsub : lowModes n N ⊆ lowModes n N' := fun k hk => mem_lowModes.mpr
    ⟨(mem_lowModes.mp hk).1, (mem_lowModes.mp hk).2.trans_le hNN⟩
  ext z
  rw [(s.cut hK hNN).mem_domain]
  constructor
  · rintro ⟨hzΩ, hz⟩
    refine ⟨s.mem_domain.mpr ⟨hzΩ, ?_⟩, ?_⟩
    · intro k hk
      simpa only [cut, ite_eq_left hk] using hz k (hsub hk)
    · intro k hk
      by_cases hkold : k ∈ lowModes n N
      · exact (s.width_lower k hkold).trans (by
          simpa only [cut, ite_eq_left hkold, id_eq] using hz k hk)
      · simpa only [cut, ite_eq_right hkold, id_eq] using hz k hk
  · rintro ⟨hz, hnr⟩
    obtain ⟨hzΩ, hz⟩ := s.mem_domain.mp hz
    refine ⟨hzΩ, ?_⟩
    intro k hk
    dsimp only [cut]
    split_ifs with hkold
    · exact hz k hkold
    · exact hnr k hk

/-- The next resonance state after extending the cutoff and applying geometric erosion. -/
def next {N' : ℝ} (hK : 0 < K) (hNN : N ≤ N') (d : ℝ≥0) : ResonanceDomainState n K N' :=
  (s.cut hK hNN).erode d

theorem next_domain {N' : ℝ} (hK : 0 < K) (hNN : N ≤ N') (d : ℝ≥0)
    (Ω : Set (ComplexSpace n)) :
    (s.next hK hNN d).domain Ω = erosion (nonresonantDomain (s.domain Ω) id K N') d := by
  rw [next, erode_domain, cut_domain]

/-- The initial resonance state at cutoff one, with no nonzero modes to exclude. -/
def initial (n : ℕ) (K : ℝ) : ResonanceDomainState n K 1 where
  radius := 0
  width := fun _ => 1
  width_pos := by intros; norm_num
  width_lower := by
    intro k hk
    have hh := mem_lowModes.mp hk
    rw [indexLength_eq_latticeLength] at hh
    have hpos : 0 < latticeLength k := by exact_mod_cast hh.1
    have hlt : latticeLength k < 1 := by exact_mod_cast hh.2
    omega

theorem initial_domain (n : ℕ) (K : ℝ) (Ω : Set (ComplexSpace n)) :
    (initial n K).domain Ω = Ω := by
  ext z
  rw [mem_domain]
  simp only [initial, erosion_zero, and_iff_left_iff_imp]
  intro _ k hk
  have hh := mem_lowModes.mp hk
  rw [indexLength_eq_latticeLength] at hh
  have hpos : 0 < latticeLength k := by exact_mod_cast hh.1
  have hlt : latticeLength k < 1 := by exact_mod_cast hh.2
  omega

end ResonanceDomainState
end KamProject.Arnold1963
