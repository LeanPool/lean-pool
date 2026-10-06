/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Certificates.IntervalCover
public import LeanPool.ConwaySoifer.Simplified.Certificates.AllChecked
import Mathlib.Tactic

/-! Exact half-open interval cover for the third-pass selection only. -/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates

/-- Certificates belonging to the specified geometric contact case. -/
def caseCerts (c : Case) : List CertData := allData.filter fun C => decide (C.case = c)

/-- The endpoint where each case passes from a geometric proof to certificates. -/
def caseStart : Case → Rat
  | .Across => 1 / 80
  | _ => 1 / 10

/-- The upper endpoint of each case's certificate chain. -/
def caseStop : Case → Rat
  | .Sext => 17 / 50
  | .Sint => 9 / 25
  | .Aown => 7 / 20
  | .Across => 49 / 400

theorem chain (c : Case) : coverChain (caseStop c) (caseStart c) (caseCerts c) = true := by
  cases c <;> decide +kernel

theorem count_certificates : allData.length = 100 := by
  decide
theorem count_assignments : (allData.map fun C => C.steps.length).sum = 3188 := by
  decide
theorem counts_by_case :
    (caseCerts .Sext).length = 26 ∧ (caseCerts .Sint).length = 26 ∧
    (caseCerts .Aown).length = 26 ∧ (caseCerts .Across).length = 22 := by
      decide
theorem assignments_by_case :
    ((caseCerts .Sext).map fun C => C.steps.length).sum = 1226 ∧
    ((caseCerts .Sint).map fun C => C.steps.length).sum = 1165 ∧
    ((caseCerts .Aown).map fun C => C.steps.length).sum = 688 ∧
    ((caseCerts .Across).map fun C => C.steps.length).sum = 109 := by
      decide

theorem no_small_nonAcross :
    allData.all (fun C => decide (C.case = .Across) || !smallHi C.hi) = true := by
      decide +kernel

/-- Each point in the retained interval is excluded by a checked shortened trace.
No small-case geometric strengthening is required for these traces. -/
theorem caseExcluded (c : Case) {T : Configuration} {r s : ℝ}
    (H : Canonical c.toContact T r s) (hlo : (caseStart c : ℝ) < s)
    (hhi : s ≤ caseStop c) : False := by
  obtain ⟨C, hC, hClo, hChi⟩ := coverChain_sound _ _ _ (chain c) s hlo hhi
  obtain ⟨hCall, hCc⟩ : C ∈ allData ∧ C.case = c := by
    simpa only [caseCerts, List.mem_filter, decide_eq_true_eq] using hC
  obtain ⟨hden, -, -, hhi25, M, hM, hex⟩ := (all_checked C hCall)
  have hhi1 : (C.hi : ℝ) ≤ 1 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hhi25
    push_cast at hh
    linarith
  refine hex T (s - C.lo) (by linarith) (by push_cast; linarith) ?_
  subst c
  refine initModel_holds hM hden hhi1 H hChi ?_
  intro hsm
  have hd := List.all_eq_true.mp no_small_nonAcross C hCall
  have hc : C.case = .Across := by
    simpa [hsm] using hd
  rw [hc]
  exact ⟨fun _ _ _ _ h => absurd rfl h, fun _ _ _ _ _ h => absurd rfl h⟩

/-- Closed geometric ranges join the original half-open intervals, including all
overlaps. This arithmetic theorem is independent of the certificate evaluations. -/
theorem ranges_complete (c : Case) {s : ℝ} (hs : 0 < s) :
    s ≤ (caseStart c : ℝ) ∨
    ((caseStart c : ℝ) < s ∧ s ≤ (caseStop c : ℝ)) ∨
    (match c with
      | .Sext => (1 / 3 : ℝ) ≤ s
      | .Sint => (9 / 25 : ℝ) ≤ s
      | .Aown => (7 / 20 : ℝ) ≤ s
      | .Across => (3 / 25 : ℝ) ≤ s) := by
  by_cases hlo : s ≤ (caseStart c : ℝ)
  · exact Or.inl hlo
  · right
    by_cases hhi : s ≤ (caseStop c : ℝ)
    · exact Or.inl ⟨lt_of_not_ge hlo, hhi⟩
    · right
      cases c <;> norm_num [caseStop] at hhi ⊢ <;> linarith

end ConwaySoifer.Simplified.Certificates
