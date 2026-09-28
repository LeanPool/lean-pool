/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5FrontierBatchF3200227`.
* `KernelOnly.PartE.E24KC5FrontierBatchF4000228`.
* `KernelOnly.PartE.E24KC5FrontierBatchF4800229`.
* `KernelOnly.PartE.E24KC5FrontierBatchF5600230`.
* `KernelOnly.PartE.E24KC5FrontierBatchF6400231`.
* `KernelOnly.PartE.E24KC5FrontierBatchF7200232`.
* `KernelOnly.PartE.E24KC5FrontierBatchF80LL00235`.
* `KernelOnly.PartE.E24KC5FrontierBatchF80LRL00237`.
* `KernelOnly.PartE.E24KC5FrontierBatchF80LRR00238`.
* `KernelOnly.PartE.E24KC5FrontierBatchF80RLR00247`.
* `KernelOnly.PartE.E24KC5FrontierBatchF80RRL00249`.
* `KernelOnly.PartE.E24KC5FrontierBatchF80RRR00250`.
* `KernelOnly.PartE.E24KC5FrontierBatchF88LL00253`.
* `KernelOnly.PartE.E24KC5FrontierBatchF88LRR00261`.
* `KernelOnly.PartE.E24KC5FrontierBatchF88RRL00287`.
* `KernelOnly.PartE.E24KC5FrontierBatchF8LLR00192`.
* `KernelOnly.PartE.E24KC5FrontierBatchF8LRL00194`.
* `KernelOnly.PartE.E24KC5FrontierBatchF8RLR00209`.
* `KernelOnly.PartE.E24KC5FrontierBatchF8RR00210`.
* `KernelOnly.PartE.E24KC5FrontierBatchF96LLR00463`.
-/

@[expose] public section

noncomputable section

namespace GerverSofa.PartE.CoverCertificate12be39bbad

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLH phiAboveCell1111)))


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31

end GerverSofa.PartE.CoverCertificate12be39bbad

namespace GerverSofa.PartE.CoverCertificatec4afef5d19

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLH phiAboveCell1111)))


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10

end GerverSofa.PartE.CoverCertificatec4afef5d19

namespace GerverSofa.PartE.CoverCertificate62151508e5

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLH phiAboveCell1111)))


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1

end GerverSofa.PartE.CoverCertificate62151508e5

namespace GerverSofa.PartE.CoverCertificate2dddad520f

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLH phiAboveCell1111)))


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02

end GerverSofa.PartE.CoverCertificate2dddad520f

namespace GerverSofa.PartE.CoverCertificate4f8bf27ed0

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLH phiAboveCell1111)))


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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

end GerverSofa.PartE.CoverCertificate4f8bf27ed0

namespace GerverSofa.PartE.CoverCertificate60aadf3941

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLH phiAboveCell1111)))


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1

end GerverSofa.PartE.CoverCertificate60aadf3941

namespace GerverSofa.PartE.CoverCertificate19be7723d5

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLH phiAboveCell1111)))


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1

end GerverSofa.PartE.CoverCertificate19be7723d5

namespace GerverSofa.PartE.CoverCertificatea0740027fc

private abbrev cellRoot : AngleCell :=
  (childLH (childHH (childLH phiAboveCell1111)))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea0740027fc

namespace GerverSofa.PartE.CoverCertificate069fa78a71

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3221)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate069fa78a71

namespace GerverSofa.PartE.CoverCertificate1d00d9f69c

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell3221)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate1d00d9f69c

namespace GerverSofa.PartE.CoverCertificate01063797cc

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3223)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate01063797cc

namespace GerverSofa.PartE.CoverCertificatef842354b5b

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3230)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatef842354b5b

namespace GerverSofa.PartE.CoverCertificate0e9db7bf30

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3230)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate0e9db7bf30

namespace GerverSofa.PartE.CoverCertificate1dc6ae7126

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3230)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate1dc6ae7126

namespace GerverSofa.PartE.CoverCertificate3c9114c82d

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell3230)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate3c9114c82d

namespace GerverSofa.PartE.CoverCertificateec279abdfe

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3231)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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

end GerverSofa.PartE.CoverCertificateec279abdfe

namespace GerverSofa.PartE.CoverCertificate4e21575659

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3231)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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

end GerverSofa.PartE.CoverCertificate4e21575659

namespace GerverSofa.PartE.CoverCertificated2df3f1b8b

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3231)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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

end GerverSofa.PartE.CoverCertificated2df3f1b8b

namespace GerverSofa.PartE.CoverCertificatefd72248a13

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell3231)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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

end GerverSofa.PartE.CoverCertificatefd72248a13

namespace GerverSofa.PartE.CoverCertificate182948158b

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3232)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate182948158b

namespace GerverSofa.PartE.CoverCertificate2c60bab4c6

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3232)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate2c60bab4c6

namespace GerverSofa.PartE.CoverCertificatefc5d468444

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3232)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatefc5d468444

namespace GerverSofa.PartE.CoverCertificatee3c94e2667

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell3232)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatee3c94e2667

namespace GerverSofa.PartE.CoverCertificatee175b9aa59

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3233)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificatee175b9aa59

namespace GerverSofa.PartE.CoverCertificate1efa344902

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3233)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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

end GerverSofa.PartE.CoverCertificate1efa344902

namespace GerverSofa.PartE.CoverCertificatea932254ffe

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3233)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea932254ffe

namespace GerverSofa.PartE.CoverCertificate4b644f2af3

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell3233)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate4b644f2af3

namespace GerverSofa.PartE.CoverCertificate27ea8c6704

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3300)


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

end GerverSofa.PartE.CoverCertificate27ea8c6704

namespace GerverSofa.PartE.CoverCertificate7519fa3e77

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3300)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate7519fa3e77

namespace GerverSofa.PartE.CoverCertificate79beaf8121

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3300)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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

end GerverSofa.PartE.CoverCertificate79beaf8121

namespace GerverSofa.PartE.CoverCertificatef1c8d80a5e

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell3300)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2

end GerverSofa.PartE.CoverCertificatef1c8d80a5e

namespace GerverSofa.PartE.CoverCertificateffa95a2bce

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3301)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateffa95a2bce

namespace GerverSofa.PartE.CoverCertificatea622d1d6d8

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3301)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea622d1d6d8

namespace GerverSofa.PartE.CoverCertificate6808a28f96

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3301)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate6808a28f96

namespace GerverSofa.PartE.CoverCertificate64b5caf113

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell3301)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate64b5caf113

namespace GerverSofa.PartE.CoverCertificate8d399165ed

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3302)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32

end GerverSofa.PartE.CoverCertificate8d399165ed

namespace GerverSofa.PartE.CoverCertificateb129667c78

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3302)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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

end GerverSofa.PartE.CoverCertificateb129667c78

namespace GerverSofa.PartE.CoverCertificatee5db5e1b6d

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3302)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificatee5db5e1b6d

namespace GerverSofa.PartE.CoverCertificatee9fa971b95

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell3302)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23

end GerverSofa.PartE.CoverCertificatee9fa971b95

namespace GerverSofa.PartE.CoverCertificated4cb65cefa

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3303)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2

end GerverSofa.PartE.CoverCertificated4cb65cefa

namespace GerverSofa.PartE.CoverCertificate75e4a1640f

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3303)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate75e4a1640f

namespace GerverSofa.PartE.CoverCertificateb422ba7d7a

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3303)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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

end GerverSofa.PartE.CoverCertificateb422ba7d7a

namespace GerverSofa.PartE.CoverCertificate348be683b7

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell3303)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2

end GerverSofa.PartE.CoverCertificate348be683b7

namespace GerverSofa.PartE.CoverCertificatee69a3e135e

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3310)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatee69a3e135e

namespace GerverSofa.PartE.CoverCertificate7cfce934a3

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3312)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate7cfce934a3

namespace GerverSofa.PartE.CoverCertificatee6e5d7b950

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3312)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatee6e5d7b950

namespace GerverSofa.PartE.CoverCertificatedbde18308c

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3312)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatedbde18308c

namespace GerverSofa.PartE.CoverCertificate78624e9f2e

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell3312)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate78624e9f2e

namespace GerverSofa.PartE.CoverCertificate86b7e57f5c

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3313)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate86b7e57f5c

namespace GerverSofa.PartE.CoverCertificate81d94c7da5

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3320)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate81d94c7da5

namespace GerverSofa.PartE.CoverCertificatecaeab30c1b

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3320)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificatecaeab30c1b

namespace GerverSofa.PartE.CoverCertificatecee0fdb8c5

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3320)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificatecee0fdb8c5

namespace GerverSofa.PartE.CoverCertificate92301c5291

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3321)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23

end GerverSofa.PartE.CoverCertificate92301c5291

namespace GerverSofa.PartE.CoverCertificate16ba550865

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3321)


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

end GerverSofa.PartE.CoverCertificate16ba550865

namespace GerverSofa.PartE.CoverCertificatebb39ac0110

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3321)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33


private abbrev cell2020 : AngleCell :=
  childLL cell202


private abbrev cell2021 : AngleCell :=
  childLH cell202


private abbrev cell2022 : AngleCell :=
  childHL cell202


private abbrev cell2023 : AngleCell :=
  childHH cell202


private abbrev cell2200 : AngleCell :=
  childLL cell220


private abbrev cell2201 : AngleCell :=
  childLH cell220


private abbrev cell2202 : AngleCell :=
  childHL cell220


private abbrev cell2203 : AngleCell :=
  childHH cell220


private abbrev cell2210 : AngleCell :=
  childLL cell221


private abbrev cell2211 : AngleCell :=
  childLH cell221


private abbrev cell2212 : AngleCell :=
  childHL cell221


private abbrev cell2213 : AngleCell :=
  childHH cell221


private abbrev cell2220 : AngleCell :=
  childLL cell222


private abbrev cell2221 : AngleCell :=
  childLH cell222


private abbrev cell2222 : AngleCell :=
  childHL cell222


private abbrev cell2223 : AngleCell :=
  childHH cell222


private abbrev cell2230 : AngleCell :=
  childLL cell223


private abbrev cell2231 : AngleCell :=
  childLH cell223


private abbrev cell2232 : AngleCell :=
  childHL cell223


private abbrev cell2233 : AngleCell :=
  childHH cell223


private abbrev cell2320 : AngleCell :=
  childLL cell232


private abbrev cell2321 : AngleCell :=
  childLH cell232


private abbrev cell2322 : AngleCell :=
  childHL cell232


private abbrev cell2323 : AngleCell :=
  childHH cell232

end GerverSofa.PartE.CoverCertificatebb39ac0110

namespace GerverSofa.PartE.CoverCertificatef2ad9b0e27

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell3321)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22

end GerverSofa.PartE.CoverCertificatef2ad9b0e27

namespace GerverSofa.PartE.CoverCertificate73093b0a81

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3322)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate73093b0a81

namespace GerverSofa.PartE.CoverCertificate74c1ca1637

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell3322)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificate74c1ca1637

namespace GerverSofa.PartE.CoverCertificateec9c3e1faf

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell3323)


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33


private abbrev cell2200 : AngleCell :=
  childLL cell220


private abbrev cell2201 : AngleCell :=
  childLH cell220


private abbrev cell2202 : AngleCell :=
  childHL cell220


private abbrev cell2203 : AngleCell :=
  childHH cell220


private abbrev cell2220 : AngleCell :=
  childLL cell222


private abbrev cell2221 : AngleCell :=
  childLH cell222


private abbrev cell2222 : AngleCell :=
  childHL cell222


private abbrev cell2223 : AngleCell :=
  childHH cell222


private abbrev cell2230 : AngleCell :=
  childLL cell223


private abbrev cell2231 : AngleCell :=
  childLH cell223


private abbrev cell2232 : AngleCell :=
  childHL cell223


private abbrev cell2233 : AngleCell :=
  childHH cell223

end GerverSofa.PartE.CoverCertificateec9c3e1faf

namespace GerverSofa.PartE.CoverCertificate144616495b

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLL phiAboveCell1110)))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate144616495b

namespace GerverSofa.PartE.CoverCertificatef96351225f

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLL phiAboveCell1110)))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatef96351225f

namespace GerverSofa.PartE.CoverCertificateed7fe84102

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLL phiAboveCell1110)))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateed7fe84102

namespace GerverSofa.PartE.CoverCertificateb1ce232ebf

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLL phiAboveCell1110)))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateb1ce232ebf

namespace GerverSofa.PartE.CoverCertificate3e6f5d1050

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLH phiAboveCell1110)))


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


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


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


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31

end GerverSofa.PartE.CoverCertificate3e6f5d1050

namespace GerverSofa.PartE.CoverCertificate3c635b07e8

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell3330)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate3c635b07e8

section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells976ad3f816

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24PhiAboveRoot)))

end CertificateCells976ad3f816

open CertificateCells976ad3f816
namespace CoverCertificate12be39bbad


























































private theorem checked020 : adaptiveCoverCheck 6 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 6 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 6 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 6 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 6 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 6 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 6 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 6 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell033 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 6 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 6 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 6 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 6 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 6 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 6 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 6 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 6 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 6 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 6 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 6 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 6 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 6 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 6 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 6 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 6 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 6 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 6 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 6 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 6 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell223 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 6 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 6 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 6 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 6 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 6 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 6 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 6 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 6 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell313 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate12be39bbad

theorem e24KC2PhiAboveLeaf1111101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH phiAboveCell1111))) = true := by
  exact CoverCertificate12be39bbad.checkedRoot
namespace CoverCertificatec4afef5d19


























private theorem checked000 : adaptiveCoverCheck 6 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 6 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 6 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 6 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 6 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 6 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 6 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 6 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 6 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 6 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 6 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 6 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell103 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec4afef5d19

theorem e24KC2PhiAboveLeaf1111102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH phiAboveCell1111))) = true := by
  exact CoverCertificatec4afef5d19.checkedRoot
namespace CoverCertificate62151508e5














private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate62151508e5

theorem e24KC2PhiAboveLeaf1111103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH phiAboveCell1111))) = true := by
  exact CoverCertificate62151508e5.checkedRoot
namespace CoverCertificate2dddad520f


























private theorem checked020 : adaptiveCoverCheck 6 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 6 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 6 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 6 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell023 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate2dddad520f

theorem e24KC2PhiAboveLeaf1111110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH phiAboveCell1111))) = true := by
  exact CoverCertificate2dddad520f.checkedRoot
namespace CoverCertificate4f8bf27ed0






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4f8bf27ed0

theorem e24KC2PhiAboveLeaf1111111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH phiAboveCell1111))) = true := by
  exact CoverCertificate4f8bf27ed0.checkedRoot
namespace CoverCertificate60aadf3941














private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate60aadf3941

theorem e24KC2PhiAboveLeaf1111112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH phiAboveCell1111))) = true := by
  exact CoverCertificate60aadf3941.checkedRoot
namespace CoverCertificate19be7723d5














private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate19be7723d5

theorem e24KC2PhiAboveLeaf1111113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH phiAboveCell1111))) = true := by
  exact CoverCertificate19be7723d5.checkedRoot
namespace CoverCertificatea0740027fc






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

end CoverCertificatea0740027fc

theorem e24KC2PhiAboveLeaf1111131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH phiAboveCell1111))) = true := by
  exact CoverCertificatea0740027fc.checkedRoot

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

namespace CertificateCells83c065d08f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3221` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3221 : AngleCell :=
  childLH (childHL (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3223 : AngleCell :=
  childHH (childHL (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3230` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3230 : AngleCell :=
  childLL (childHH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3231` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3231 : AngleCell :=
  childLH (childHH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells83c065d08f

open CertificateCells83c065d08f
namespace CoverCertificate069fa78a71






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

end CoverCertificate069fa78a71

theorem e24KC2PhiBelowLeaf32211 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3221) = true := by
  exact CoverCertificate069fa78a71.checkedRoot
namespace CoverCertificate1d00d9f69c






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

end CoverCertificate1d00d9f69c

theorem e24KC2PhiBelowLeaf32213 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3221) = true := by
  exact CoverCertificate1d00d9f69c.checkedRoot
namespace CoverCertificate01063797cc






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

end CoverCertificate01063797cc

theorem e24KC2PhiBelowLeaf32231 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3223) = true := by
  exact CoverCertificate01063797cc.checkedRoot
namespace CoverCertificatef842354b5b






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

end CoverCertificatef842354b5b

theorem e24KC2PhiBelowLeaf32300 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3230) = true := by
  exact CoverCertificatef842354b5b.checkedRoot
namespace CoverCertificate0e9db7bf30






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

end CoverCertificate0e9db7bf30

theorem e24KC2PhiBelowLeaf32301 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3230) = true := by
  exact CoverCertificate0e9db7bf30.checkedRoot
namespace CoverCertificate1dc6ae7126






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

end CoverCertificate1dc6ae7126

theorem e24KC2PhiBelowLeaf32302 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3230) = true := by
  exact CoverCertificate1dc6ae7126.checkedRoot
namespace CoverCertificate3c9114c82d






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

end CoverCertificate3c9114c82d

theorem e24KC2PhiBelowLeaf32303 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3230) = true := by
  exact CoverCertificate3c9114c82d.checkedRoot
namespace CoverCertificateec279abdfe






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateec279abdfe

theorem e24KC2PhiBelowLeaf32310 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3231) = true := by
  exact CoverCertificateec279abdfe.checkedRoot

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

namespace CertificateCells9044f599c8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3231` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3231 : AngleCell :=
  childLH (childHH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3232` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3232 : AngleCell :=
  childHL (childHH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3233` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3233 : AngleCell :=
  childHH (childHH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells9044f599c8

open CertificateCells9044f599c8
namespace CoverCertificate4e21575659






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4e21575659

theorem e24KC2PhiBelowLeaf32311 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3231) = true := by
  exact CoverCertificate4e21575659.checkedRoot
namespace CoverCertificated2df3f1b8b






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated2df3f1b8b

theorem e24KC2PhiBelowLeaf32312 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3231) = true := by
  exact CoverCertificated2df3f1b8b.checkedRoot
namespace CoverCertificatefd72248a13






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatefd72248a13

theorem e24KC2PhiBelowLeaf32313 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3231) = true := by
  exact CoverCertificatefd72248a13.checkedRoot
namespace CoverCertificate182948158b






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

end CoverCertificate182948158b

theorem e24KC2PhiBelowLeaf32320 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3232) = true := by
  exact CoverCertificate182948158b.checkedRoot
namespace CoverCertificate2c60bab4c6






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

end CoverCertificate2c60bab4c6

theorem e24KC2PhiBelowLeaf32321 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3232) = true := by
  exact CoverCertificate2c60bab4c6.checkedRoot
namespace CoverCertificatefc5d468444






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

end CoverCertificatefc5d468444

theorem e24KC2PhiBelowLeaf32322 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3232) = true := by
  exact CoverCertificatefc5d468444.checkedRoot
namespace CoverCertificatee3c94e2667






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

end CoverCertificatee3c94e2667

theorem e24KC2PhiBelowLeaf32323 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3232) = true := by
  exact CoverCertificatee3c94e2667.checkedRoot
namespace CoverCertificatee175b9aa59














private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatee175b9aa59

theorem e24KC2PhiBelowLeaf32330 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3233) = true := by
  exact CoverCertificatee175b9aa59.checkedRoot

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

namespace CertificateCellse87459d2a7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3233` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3233 : AngleCell :=
  childHH (childHH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3300` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3300 : AngleCell :=
  childLL (childLL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3301` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3301 : AngleCell :=
  childLH (childLL (childHH (childHH e24PhiBelowRoot)))

end CertificateCellse87459d2a7

open CertificateCellse87459d2a7
namespace CoverCertificate1efa344902






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate1efa344902

theorem e24KC2PhiBelowLeaf32331 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3233) = true := by
  exact CoverCertificate1efa344902.checkedRoot
namespace CoverCertificatea932254ffe






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

end CoverCertificatea932254ffe

theorem e24KC2PhiBelowLeaf32332 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3233) = true := by
  exact CoverCertificatea932254ffe.checkedRoot
namespace CoverCertificate4b644f2af3


















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4b644f2af3

theorem e24KC2PhiBelowLeaf32333 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3233) = true := by
  exact CoverCertificate4b644f2af3.checkedRoot
namespace CoverCertificate27ea8c6704


















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

end CoverCertificate27ea8c6704

theorem e24KC2PhiBelowLeaf33000 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3300) = true := by
  exact CoverCertificate27ea8c6704.checkedRoot
namespace CoverCertificate7519fa3e77






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

end CoverCertificate7519fa3e77

theorem e24KC2PhiBelowLeaf33001 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3300) = true := by
  exact CoverCertificate7519fa3e77.checkedRoot
namespace CoverCertificate79beaf8121






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate79beaf8121

theorem e24KC2PhiBelowLeaf33002 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3300) = true := by
  exact CoverCertificate79beaf8121.checkedRoot
namespace CoverCertificatef1c8d80a5e










private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatef1c8d80a5e

theorem e24KC2PhiBelowLeaf33003 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3300) = true := by
  exact CoverCertificatef1c8d80a5e.checkedRoot
namespace CoverCertificateffa95a2bce






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

end CoverCertificateffa95a2bce

theorem e24KC2PhiBelowLeaf33010 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3301) = true := by
  exact CoverCertificateffa95a2bce.checkedRoot

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

namespace CertificateCells5c2e184d25

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3301` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3301 : AngleCell :=
  childLH (childLL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3302` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3302 : AngleCell :=
  childHL (childLL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3303` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3303 : AngleCell :=
  childHH (childLL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells5c2e184d25

open CertificateCells5c2e184d25
namespace CoverCertificatea622d1d6d8






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

end CoverCertificatea622d1d6d8

theorem e24KC2PhiBelowLeaf33011 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3301) = true := by
  exact CoverCertificatea622d1d6d8.checkedRoot
namespace CoverCertificate6808a28f96






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

end CoverCertificate6808a28f96

theorem e24KC2PhiBelowLeaf33012 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3301) = true := by
  exact CoverCertificate6808a28f96.checkedRoot
namespace CoverCertificate64b5caf113






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

end CoverCertificate64b5caf113

theorem e24KC2PhiBelowLeaf33013 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3301) = true := by
  exact CoverCertificate64b5caf113.checkedRoot
namespace CoverCertificate8d399165ed


























private theorem checked320 : adaptiveCoverCheck 6 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 6 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 6 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 6 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell323 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 6 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate8d399165ed

theorem e24KC2PhiBelowLeaf33020 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3302) = true := by
  exact CoverCertificate8d399165ed.checkedRoot
namespace CoverCertificateb129667c78






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateb129667c78

theorem e24KC2PhiBelowLeaf33021 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3302) = true := by
  exact CoverCertificateb129667c78.checkedRoot
namespace CoverCertificatee5db5e1b6d






















































private theorem checked100 : adaptiveCoverCheck 6 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 6 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 6 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 6 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 6 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 6 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 6 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 6 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 6 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 6 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 6 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 6 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 6 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 6 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 6 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 6 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell133 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 6 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 6 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 6 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 6 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 6 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 6 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 6 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 6 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 6 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 6 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 6 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 6 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 6 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 6 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 6 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 6 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatee5db5e1b6d

theorem e24KC2PhiBelowLeaf33022 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3302) = true := by
  exact CoverCertificatee5db5e1b6d.checkedRoot
namespace CoverCertificatee9fa971b95










































private theorem checked020 : adaptiveCoverCheck 6 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 6 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 6 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 6 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell023 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 6 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 6 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 6 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 6 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 6 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 6 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 6 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 6 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 6 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 6 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 6 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 6 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 6 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 6 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 6 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 6 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell233 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell23
    checked230 checked231 checked232 checked233

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatee9fa971b95

theorem e24KC2PhiBelowLeaf33023 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3302) = true := by
  exact CoverCertificatee9fa971b95.checkedRoot
namespace CoverCertificated4cb65cefa










private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated4cb65cefa

theorem e24KC2PhiBelowLeaf33030 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3303) = true := by
  exact CoverCertificated4cb65cefa.checkedRoot

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

namespace CertificateCells32f77991dd

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3303` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3303 : AngleCell :=
  childHH (childLL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3310` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3310 : AngleCell :=
  childLL (childLH (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3312` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3312 : AngleCell :=
  childHL (childLH (childHH (childHH e24PhiBelowRoot)))

end CertificateCells32f77991dd

open CertificateCells32f77991dd
namespace CoverCertificate75e4a1640f






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

end CoverCertificate75e4a1640f

theorem e24KC2PhiBelowLeaf33031 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3303) = true := by
  exact CoverCertificate75e4a1640f.checkedRoot
namespace CoverCertificateb422ba7d7a






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateb422ba7d7a

theorem e24KC2PhiBelowLeaf33032 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3303) = true := by
  exact CoverCertificateb422ba7d7a.checkedRoot
namespace CoverCertificate348be683b7










private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate348be683b7

theorem e24KC2PhiBelowLeaf33033 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3303) = true := by
  exact CoverCertificate348be683b7.checkedRoot
namespace CoverCertificatee69a3e135e






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

end CoverCertificatee69a3e135e

theorem e24KC2PhiBelowLeaf33102 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3310) = true := by
  exact CoverCertificatee69a3e135e.checkedRoot
namespace CoverCertificate7cfce934a3






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

end CoverCertificate7cfce934a3

theorem e24KC2PhiBelowLeaf33120 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3312) = true := by
  exact CoverCertificate7cfce934a3.checkedRoot
namespace CoverCertificatee6e5d7b950






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

end CoverCertificatee6e5d7b950

theorem e24KC2PhiBelowLeaf33121 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3312) = true := by
  exact CoverCertificatee6e5d7b950.checkedRoot
namespace CoverCertificatedbde18308c






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

end CoverCertificatedbde18308c

theorem e24KC2PhiBelowLeaf33122 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3312) = true := by
  exact CoverCertificatedbde18308c.checkedRoot
namespace CoverCertificate78624e9f2e






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

end CoverCertificate78624e9f2e

theorem e24KC2PhiBelowLeaf33123 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3312) = true := by
  exact CoverCertificate78624e9f2e.checkedRoot

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

namespace CertificateCells6c9e156424

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3313` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3313 : AngleCell :=
  childHH (childLH (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3320` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3320 : AngleCell :=
  childLL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells6c9e156424

open CertificateCells6c9e156424
namespace CoverCertificate86b7e57f5c






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

end CoverCertificate86b7e57f5c

theorem e24KC2PhiBelowLeaf33132 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3313) = true := by
  exact CoverCertificate86b7e57f5c.checkedRoot
namespace CoverCertificate81d94c7da5






















































private theorem checked100 : adaptiveCoverCheck 6 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 6 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 6 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 6 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 6 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 6 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 6 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 6 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 6 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 6 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 6 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 6 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 6 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 6 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 6 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 6 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell133 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 6 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 6 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 6 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 6 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 6 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 6 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 6 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 6 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 6 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 6 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 6 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 6 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 6 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 6 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 6 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 6 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate81d94c7da5

theorem e24KC2PhiBelowLeaf33200 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3320) = true := by
  exact CoverCertificate81d94c7da5.checkedRoot

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

namespace CertificateCells613b88d08f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3320` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3320 : AngleCell :=
  childLL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells613b88d08f

open CertificateCells613b88d08f
namespace CoverCertificatecaeab30c1b


















































































private theorem checked000 : adaptiveCoverCheck 6 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 6 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 6 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 6 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 6 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 6 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 6 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 6 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 6 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 6 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 6 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 6 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 6 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 6 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 6 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 6 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 6 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 6 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 6 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 6 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell103 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 6 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 6 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 6 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 6 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 6 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 6 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 6 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 6 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 6 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 6 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 6 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 6 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 6 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 6 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 6 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 6 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 6 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 6 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 6 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 6 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 6 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 6 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 6 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 6 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 6 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 6 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 6 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 6 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 6 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 6 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 6 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 6 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 6 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 6 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 6 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 6 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 6 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 6 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 6 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 6 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatecaeab30c1b

theorem e24KC2PhiBelowLeaf33201 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3320) = true := by
  exact CoverCertificatecaeab30c1b.checkedRoot

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

namespace CertificateCells14a7ef0a1a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3320` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3320 : AngleCell :=
  childLL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells14a7ef0a1a

open CertificateCells14a7ef0a1a
namespace CoverCertificatecee0fdb8c5


































































private theorem checked030 : adaptiveCoverCheck 6 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 6 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 6 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 6 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 6 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 6 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 6 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 6 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 6 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 6 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 6 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 6 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 6 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 6 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 6 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 6 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 6 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 6 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 6 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 6 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell133 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 6 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 6 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 6 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 6 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell213 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 6 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 6 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 6 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 6 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 6 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 6 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 6 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 6 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 6 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 6 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 6 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 6 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 6 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 6 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 6 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 6 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 6 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 6 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 6 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 6 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatecee0fdb8c5

theorem e24KC2PhiBelowLeaf33202 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3320) = true := by
  exact CoverCertificatecee0fdb8c5.checkedRoot

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

namespace CertificateCells756d9e6827

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3321` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3321 : AngleCell :=
  childLH (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells756d9e6827

open CertificateCells756d9e6827
namespace CoverCertificate92301c5291


































private theorem checked200 : adaptiveCoverCheck 6 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 6 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 6 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 6 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell203 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 6 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 6 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 6 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 6 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 6 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 6 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 6 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 6 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell233 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell23
    checked230 checked231 checked232 checked233

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate92301c5291

theorem e24KC2PhiBelowLeaf33210 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3321) = true := by
  exact CoverCertificate92301c5291.checkedRoot

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

namespace CertificateCells9052ca8de4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3321` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3321 : AngleCell :=
  childLH (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells9052ca8de4

open CertificateCells9052ca8de4
namespace CoverCertificate16ba550865


















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

end CoverCertificate16ba550865

theorem e24KC2PhiBelowLeaf33211 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3321) = true := by
  exact CoverCertificate16ba550865.checkedRoot

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

namespace CertificateCells8466e30288

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3321` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3321 : AngleCell :=
  childLH (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells8466e30288

open CertificateCells8466e30288
namespace CoverCertificatebb39ac0110


































































































private theorem checked2020 : adaptiveCoverCheck 5 cell2020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2020 (by decide +kernel)

private theorem checked2021 : adaptiveCoverCheck 5 cell2021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2021 (by decide +kernel)

private theorem checked2022 : adaptiveCoverCheck 5 cell2022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2022 (by decide +kernel)

private theorem checked2023 : adaptiveCoverCheck 5 cell2023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2023 (by decide +kernel)

private theorem checked2200 : adaptiveCoverCheck 5 cell2200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2200 (by decide +kernel)

private theorem checked2201 : adaptiveCoverCheck 5 cell2201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2201 (by decide +kernel)

private theorem checked2202 : adaptiveCoverCheck 5 cell2202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2202 (by decide +kernel)

private theorem checked2203 : adaptiveCoverCheck 5 cell2203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2203 (by decide +kernel)

private theorem checked2210 : adaptiveCoverCheck 5 cell2210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2210 (by decide +kernel)

private theorem checked2211 : adaptiveCoverCheck 5 cell2211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2211 (by decide +kernel)

private theorem checked2212 : adaptiveCoverCheck 5 cell2212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2212 (by decide +kernel)

private theorem checked2213 : adaptiveCoverCheck 5 cell2213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2213 (by decide +kernel)

private theorem checked2220 : adaptiveCoverCheck 5 cell2220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2220 (by decide +kernel)

private theorem checked2221 : adaptiveCoverCheck 5 cell2221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2221 (by decide +kernel)

private theorem checked2222 : adaptiveCoverCheck 5 cell2222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2222 (by decide +kernel)

private theorem checked2223 : adaptiveCoverCheck 5 cell2223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2223 (by decide +kernel)

private theorem checked2230 : adaptiveCoverCheck 5 cell2230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2230 (by decide +kernel)

private theorem checked2231 : adaptiveCoverCheck 5 cell2231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2231 (by decide +kernel)

private theorem checked2232 : adaptiveCoverCheck 5 cell2232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2232 (by decide +kernel)

private theorem checked2233 : adaptiveCoverCheck 5 cell2233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2233 (by decide +kernel)

private theorem checked2320 : adaptiveCoverCheck 5 cell2320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2320 (by decide +kernel)

private theorem checked2321 : adaptiveCoverCheck 5 cell2321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2321 (by decide +kernel)

private theorem checked2322 : adaptiveCoverCheck 5 cell2322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2322 (by decide +kernel)

private theorem checked2323 : adaptiveCoverCheck 5 cell2323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2323 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 6 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 6 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 6 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 6 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 6 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 6 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 6 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 6 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 6 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 6 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 6 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 6 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 6 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 6 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 6 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 6 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell033 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 6 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 6 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 6 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 6 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell123 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 6 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 6 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 6 cell202 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell202
    checked2020 checked2021 checked2022 checked2023

private theorem checked203 : adaptiveCoverCheck 6 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 6 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 6 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 6 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 6 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 6 cell220 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell220
    checked2200 checked2201 checked2202 checked2203

private theorem checked221 : adaptiveCoverCheck 6 cell221 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell221
    checked2210 checked2211 checked2212 checked2213

private theorem checked222 : adaptiveCoverCheck 6 cell222 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell222
    checked2220 checked2221 checked2222 checked2223

private theorem checked223 : adaptiveCoverCheck 6 cell223 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell223
    checked2230 checked2231 checked2232 checked2233

private theorem checked230 : adaptiveCoverCheck 6 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 6 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 6 cell232 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell232
    checked2320 checked2321 checked2322 checked2323

private theorem checked233 : adaptiveCoverCheck 6 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 6 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 6 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 6 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 6 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 6 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 6 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 6 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 6 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 6 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 6 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 6 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 6 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 6 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 6 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 6 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 6 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatebb39ac0110

theorem e24KC2PhiBelowLeaf33212 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3321) = true := by
  exact CoverCertificatebb39ac0110.checkedRoot

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

namespace CertificateCells960370a0be

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3321` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3321 : AngleCell :=
  childLH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3322` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3322 : AngleCell :=
  childHL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells960370a0be

open CertificateCells960370a0be
namespace CoverCertificatef2ad9b0e27


























private theorem checked220 : adaptiveCoverCheck 6 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 6 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 6 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 6 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell223 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell22
    checked220 checked221 checked222 checked223

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatef2ad9b0e27

theorem e24KC2PhiBelowLeaf33213 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3321) = true := by
  exact CoverCertificatef2ad9b0e27.checkedRoot
namespace CoverCertificate73093b0a81


































































private theorem checked010 : adaptiveCoverCheck 6 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 6 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 6 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 6 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell013 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 6 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 6 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 6 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 6 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 6 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 6 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 6 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 6 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 6 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 6 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 6 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 6 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 6 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 6 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 6 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 6 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 6 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 6 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 6 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 6 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell133 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 6 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 6 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 6 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 6 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell213 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 6 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 6 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 6 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 6 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 6 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 6 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 6 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 6 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 6 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 6 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 6 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 6 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 6 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 6 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 6 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 6 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate73093b0a81

theorem e24KC2PhiBelowLeaf33220 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3322) = true := by
  exact CoverCertificate73093b0a81.checkedRoot

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

namespace CertificateCellsd434aeb685

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3322` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3322 : AngleCell :=
  childHL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCellsd434aeb685

open CertificateCellsd434aeb685
namespace CoverCertificate74c1ca1637






























private theorem checked110 : adaptiveCoverCheck 6 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 6 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 6 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 6 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell113 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 6 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 6 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 6 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 6 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell13
    checked130 checked131 checked132 checked133

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
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate74c1ca1637

theorem e24KC2PhiBelowLeaf33222 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3322) = true := by
  exact CoverCertificate74c1ca1637.checkedRoot

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

namespace CertificateCells720ec0d149

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells720ec0d149

open CertificateCells720ec0d149
namespace CoverCertificateec9c3e1faf






















































































private theorem checked2200 : adaptiveCoverCheck 5 cell2200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2200 (by decide +kernel)

private theorem checked2201 : adaptiveCoverCheck 5 cell2201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2201 (by decide +kernel)

private theorem checked2202 : adaptiveCoverCheck 5 cell2202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2202 (by decide +kernel)

private theorem checked2203 : adaptiveCoverCheck 5 cell2203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2203 (by decide +kernel)

private theorem checked2220 : adaptiveCoverCheck 5 cell2220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2220 (by decide +kernel)

private theorem checked2221 : adaptiveCoverCheck 5 cell2221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2221 (by decide +kernel)

private theorem checked2222 : adaptiveCoverCheck 5 cell2222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2222 (by decide +kernel)

private theorem checked2223 : adaptiveCoverCheck 5 cell2223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2223 (by decide +kernel)

private theorem checked2230 : adaptiveCoverCheck 5 cell2230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2230 (by decide +kernel)

private theorem checked2231 : adaptiveCoverCheck 5 cell2231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2231 (by decide +kernel)

private theorem checked2232 : adaptiveCoverCheck 5 cell2232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2232 (by decide +kernel)

private theorem checked2233 : adaptiveCoverCheck 5 cell2233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2233 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 6 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 6 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 6 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 6 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 6 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 6 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 6 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 6 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 6 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 6 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 6 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 6 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 6 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 6 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 6 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 6 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell033 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 6 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 6 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 6 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 6 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell123 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 6 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 6 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 6 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 6 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 6 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 6 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 6 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 6 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 6 cell220 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell220
    checked2200 checked2201 checked2202 checked2203

private theorem checked221 : adaptiveCoverCheck 6 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 6 cell222 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell222
    checked2220 checked2221 checked2222 checked2223

private theorem checked223 : adaptiveCoverCheck 6 cell223 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell223
    checked2230 checked2231 checked2232 checked2233

private theorem checked230 : adaptiveCoverCheck 6 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 6 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 6 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 6 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 6 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 6 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 6 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 6 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 6 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 6 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 6 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 6 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 6 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 6 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 6 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 6 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 6 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 6 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 6 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 6 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateec9c3e1faf

theorem e24KC2PhiBelowLeaf33231 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3323) = true := by
  exact CoverCertificateec9c3e1faf.checkedRoot

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

namespace CertificateCells9005545168

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end CertificateCells9005545168

open CertificateCells9005545168
namespace CoverCertificate144616495b






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

end CoverCertificate144616495b

theorem e24KC2PhiAboveLeaf1110002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL phiAboveCell1110))) = true := by
  exact CoverCertificate144616495b.checkedRoot

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

namespace CertificateCellse586487728

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end CertificateCellse586487728

open CertificateCellse586487728
namespace CoverCertificatef96351225f






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

end CoverCertificatef96351225f

theorem e24KC2PhiAboveLeaf1110003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL phiAboveCell1110))) = true := by
  exact CoverCertificatef96351225f.checkedRoot

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

namespace CertificateCellsce87a9d03d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end CertificateCellsce87a9d03d

open CertificateCellsce87a9d03d
namespace CoverCertificateed7fe84102






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

end CoverCertificateed7fe84102

theorem e24KC2PhiAboveLeaf1110012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL phiAboveCell1110))) = true := by
  exact CoverCertificateed7fe84102.checkedRoot

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

namespace CertificateCellsce3c5151af

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end CertificateCellsce3c5151af

open CertificateCellsce3c5151af
namespace CoverCertificateb1ce232ebf






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

end CoverCertificateb1ce232ebf

theorem e24KC2PhiAboveLeaf1110013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL phiAboveCell1110))) = true := by
  exact CoverCertificateb1ce232ebf.checkedRoot
namespace CoverCertificate3e6f5d1050






































































private theorem checked000 : adaptiveCoverCheck 6 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 6 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 6 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 6 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 6 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 6 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 6 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 6 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 6 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 6 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 6 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 6 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 6 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 6 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 6 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 6 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 6 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 6 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 6 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 6 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 6 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 6 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 6 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 6 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 6 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 6 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 6 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 6 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 6 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 6 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 6 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 6 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 6 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 6 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 6 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 6 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 6 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 6 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 6 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 6 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell213 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 6 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 6 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 6 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 6 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 6 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 6 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 6 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 6 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell313 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3e6f5d1050

theorem e24KC2PhiAboveLeaf1110100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH phiAboveCell1110))) = true := by
  exact CoverCertificate3e6f5d1050.checkedRoot

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

namespace CertificateCells7c64a780f8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3330` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3330 : AngleCell :=
  childLL (childHH (childHH (childHH e24PhiBelowRoot)))

end CertificateCells7c64a780f8

open CertificateCells7c64a780f8
namespace CoverCertificate3c635b07e8






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

end CoverCertificate3c635b07e8

theorem e24KC2PhiBelowLeaf33300 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3330) = true := by
  exact CoverCertificate3c635b07e8.checkedRoot

end PartE
end GerverSofa

end

end

end
