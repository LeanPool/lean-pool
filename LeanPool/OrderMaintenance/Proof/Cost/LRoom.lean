/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.LPop


/-!
# Room for group labels (from Lemma C3)

A group split start needs a label on each side of the splitting group; a chunk-split move needs
room for the pushed labels (proved with the move, `push_room`). Both follow from the label
invariant, given that the chunk's arrivals stay within `3·M_u` and its insertions within `I_C`.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem labBefore_ok {s : Core} {g : Nat}
    (h1 : g = cF s (gC s g) → s.P.groupSpacing ≤ gL s g ∧ s.P.groupSpacing ≠ 0)
    (h2 : g ≠ cF s (gC s g) → gL s (gP s g) + 1 < gL s g) :
    ∃ lab, (labBefore g).run s = .ok lab s := by
  unfold labBefore
  simp only [run_getP_bind, run_getG_bind, run_getC_bind]
  by_cases hf : g = (s.C.getX (s.Gs.getX g).chk).first
  · rw [ite_eq_left (beq_iff_eq.mpr hf), run_before]
    have := h1 hf
    simp only [gL] at this
    rw [ite_eq_right (by omega)]; exact ⟨_, rfl⟩
  · rw [ite_eq_right (fun e => hf (beq_iff_eq.mp e))]
    simp only [run_getG_bind, run_between]
    have := h2 hf
    rw [ite_eq_right (by simp only [gL, gP] at this; omega)]; exact ⟨_, rfl⟩

theorem labAfter_ok {s : Core} {g : Nat}
    (h1 : g = cLs s (gC s g) → gL s g + s.P.groupSpacing < 1 <<< s.P.groupBits ∧
      s.P.groupSpacing ≠ 0)
    (h2 : g ≠ cLs s (gC s g) → gL s g + 1 < gL s (gN s g)) :
    ∃ lab, (labAfter g).run s = .ok lab s := by
  unfold labAfter
  simp only [run_getP_bind, run_getG_bind, run_getC_bind]
  by_cases hf : g = (s.C.getX (s.Gs.getX g).chk).last
  · rw [ite_eq_left (beq_iff_eq.mpr hf), run_after]
    have := h1 hf
    simp only [gL] at this
    rw [ite_eq_right (by omega)]; exact ⟨_, rfl⟩
  · rw [ite_eq_right (fun e => hf (beq_iff_eq.mp e))]
    simp only [run_getG_bind, run_between]
    have := h2 hf
    rw [ite_eq_right (by simp only [gL, gN] at this; omega)]; exact ⟨_, rfl⟩

/-- A single charge term is at most the chunk's charge. -/
theorem chTerm_le_charge {s : Core} {lg : LGh} {c g : Nat} (hg : g ∈ GrpsC s c) :
    chTerm s lg g ≤ charge s lg c := by
  rw [charge_eq]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg

/-- **Room for a group split start**, from Lemma C3. -/
theorem split_room {s : Core} {A : Abs} {lg : LGh} {s₀ δ δu : Nat → Nat} (hI : INV s A)
    (hL : LInv s lg s₀ δ δu) (hLP : LParams s.P) (hP : GParams s.P) {g : Nat} (hg : LiveG s g)
    (hq : gSt s g = .quiet) (hsz : gSz s g = s.P.G) (hcL : LiveC s (gC s g))
    (harr : lg.arB (gC s g) + lg.arF (gC s g) ≤ 3 * Mu s.P) (hins : lg.ins (gC s g) ≤ IC s.P) :
    SplitRoom s g := by
  have hgm : 0 < gmin s.P := by unfold gmin; have := hP.G4; omega
  have hgG : gmin s.P ≤ s.P.G := by unfold gmin; omega
  have hgC : g ∈ GrpsC s (gC s g) := mem_GrpsC.mpr ⟨hg, rfl⟩
  have hR := hL.roots _ hcL
  have hQ := hL.claim2 _ hcL
  -- one more split fits in the chunk's budget
  have hcr : lg.cs (gC s g) + lg.rs (gC s g) + 1 ≤ csB s.P + rsB s.P := by
    cases hch : lg.child g
    · have hpen : 1 ≤ pending s lg (gC s g) := by
        unfold pending
        exact Finset.card_pos.mpr ⟨g, Finset.mem_filter.mpr ⟨hgC, hch, by rw [hq]; simp⟩⟩
      have hcs : lg.cs (gC s g) ≤ csB s.P := by
        unfold csB; rw [Nat.le_div_iff_mul_le hgm]; omega
      unfold rsB; omega
    · have ht : chTerm s lg g = gmin s.P := by
        unfold chTerm; rw [hq, hsz]; simp [hch]
      have := chTerm_le_charge (lg := lg) hgC
      have hcs : lg.cs (gC s g) + 1 ≤ csB s.P := by
        unfold csB; rw [Nat.le_div_iff_mul_le hgm, Nat.add_mul, Nat.one_mul]; omega
      unfold rsB; omega
  -- halvings leave gaps of at least 2
  have hhv : lg.hv (gC s g) + 1 ≤ HC s.P := by have := hL.hv (gC s g); unfold HC; omega
  have hgap2 : 2 ≤ s.P.groupSpacing / 2 ^ lg.hv (gC s g) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have : 2 * 2 ^ lg.hv (gC s g) ≤ 2 ^ HC s.P := by
      rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans this hLP.halve
  -- pushes leave room at both ends
  have hpbm := hL.pb (gC s g)
  have hpfm := hL.pf (gC s g)
  have hpb : lg.pb (gC s g) + 1 ≤ PC s.P := by unfold PC; omega
  have hpf : lg.pf (gC s g) + 1 ≤ PC s.P := by unfold PC; omega
  have hD := hLP.Dg
  have hpush := hLP.push
  have e1 : (lg.pb (gC s g) + 1) * s.P.groupSpacing ≤ PC s.P * s.P.groupSpacing :=
    Nat.mul_le_mul_right _ hpb
  have e2 : (lg.pf (gC s g) + 1) * s.P.groupSpacing ≤ PC s.P * s.P.groupSpacing :=
    Nat.mul_le_mul_right _ hpf
  rw [Nat.add_mul, Nat.one_mul] at e1 e2
  have hrg := hL.range g hg
  obtain ⟨labL, hL1⟩ := labBefore_ok (s := s) (g := g) (fun _ => ⟨by omega, by omega⟩) (fun hf => by
    obtain ⟨hpL, hpc, hpn, hpl⟩ := hI.prev_in_chunk hg hf
    have := hL.gaps _ hpL (by rw [hpc]; exact hpl)
    rw [hpn, hpc] at this; omega)
  obtain ⟨labR, hR1⟩ := labAfter_ok (s := s) (g := g) (fun _ => ⟨by rw [cG_two _ hLP.Bg]; omega,
    by omega⟩) (fun hl => by have := hL.gaps g hg hl; omega)
  exact ⟨labL, labR, hL1, hR1⟩

end OrderMaintenance.Proof
