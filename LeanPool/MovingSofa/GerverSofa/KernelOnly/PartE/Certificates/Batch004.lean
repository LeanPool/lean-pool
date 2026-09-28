/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5FrontierBatchF96LR00464`.
* `KernelOnly.PartE.E24KC5FrontierBatchF96R00465`.
-/

@[expose] public section

noncomputable section

namespace GerverSofa.PartE.CoverCertificate446b5129d2

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childHH (childHH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate446b5129d2

namespace GerverSofa.PartE.CoverCertificate3d29d6c185

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHH (childHH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate3d29d6c185

namespace GerverSofa.PartE.CoverCertificate5443a01fd5

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHH (childHH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate5443a01fd5

namespace GerverSofa.PartE.CoverCertificateef75f67166

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childHH (childHH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateef75f67166

namespace GerverSofa.PartE.CoverCertificate77769ce963

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHH (childHH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate77769ce963

namespace GerverSofa.PartE.CoverCertificateaaf4f15552

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHH (childHH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateaaf4f15552

section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5c0c39e876

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3330` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3330 : AngleCell :=
  childLL (childHH (childHH (childHH e24PhiBelowRoot)))

end CertificateCells5c0c39e876

open CertificateCells5c0c39e876
namespace CoverCertificate446b5129d2






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate446b5129d2

theorem e24KC2PhiBelowLeaf33301 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3330) = true := by
  exact CoverCertificate446b5129d2.checkedRoot
namespace CoverCertificate3d29d6c185


















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3d29d6c185

theorem e24KC2PhiBelowLeaf33302 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3330) = true := by
  exact CoverCertificate3d29d6c185.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa1414ae513

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3330` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3330 : AngleCell :=
  childLL (childHH (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3331` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3331 : AngleCell :=
  childLH (childHH (childHH (childHH e24PhiBelowRoot)))

end CertificateCellsa1414ae513

open CertificateCellsa1414ae513
namespace CoverCertificate5443a01fd5






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5443a01fd5

theorem e24KC2PhiBelowLeaf33303 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3330) = true := by
  exact CoverCertificate5443a01fd5.checkedRoot
namespace CoverCertificateef75f67166






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateef75f67166

theorem e24KC2PhiBelowLeaf33310 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3331) = true := by
  exact CoverCertificateef75f67166.checkedRoot
namespace CoverCertificate77769ce963






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate77769ce963

theorem e24KC2PhiBelowLeaf33311 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3331) = true := by
  exact CoverCertificate77769ce963.checkedRoot
namespace CoverCertificateaaf4f15552






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateaaf4f15552

theorem e24KC2PhiBelowLeaf33312 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3331) = true := by
  exact CoverCertificateaaf4f15552.checkedRoot

end PartE
end GerverSofa

end

end

end
