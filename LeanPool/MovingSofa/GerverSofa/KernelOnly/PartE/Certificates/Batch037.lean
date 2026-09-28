/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch001

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch002














public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch003




public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch005
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch036


/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.PhiAbove.Leaf00161`.
* `KernelOnly.PartE.PhiAbove.Leaf00162`.
* `KernelOnly.PartE.PhiAbove.Leaf00163`.
* `KernelOnly.PartE.PhiAbove.Leaf00164`.
* `KernelOnly.PartE.PhiAbove.Join00165`.
* `KernelOnly.PartE.PhiAbove.Leaf00166`.
* `KernelOnly.PartE.PhiAbove.Leaf00167`.
* `KernelOnly.PartE.PhiAbove.Join00168`.
* `KernelOnly.PartE.PhiAbove.Leaf00174`.
* `KernelOnly.PartE.PhiAbove.Leaf00175`.
* `KernelOnly.PartE.PhiAbove.Leaf00176`.
* `KernelOnly.PartE.PhiAbove.Leaf00177`.
* `KernelOnly.PartE.PhiAbove.Join00178`.
* `KernelOnly.PartE.PhiAbove.Leaf00179`.
* `KernelOnly.PartE.PhiAbove.Leaf00180`.
* `KernelOnly.PartE.PhiAbove.Leaf00181`.
* `KernelOnly.PartE.PhiAbove.Join00182`.
* `KernelOnly.PartE.PhiAbove.Leaf00187`.
* `KernelOnly.PartE.PhiAbove.Leaf00188`.
* `KernelOnly.PartE.PhiAbove.Leaf00189`.
* `KernelOnly.PartE.PhiAbove.Leaf00190`.
* `KernelOnly.PartE.PhiAbove.Join00191`.
* `KernelOnly.PartE.PhiAbove.Leaf00196`.
* `KernelOnly.PartE.PhiAbove.Leaf00197`.
* `KernelOnly.PartE.PhiAbove.Leaf00198`.
* `KernelOnly.PartE.PhiAbove.Leaf00199`.
* `KernelOnly.PartE.PhiAbove.Join00200`.
* `KernelOnly.PartE.PhiAbove.Leaf00204`.
* `KernelOnly.PartE.PhiAbove.Leaf00205`.
* `KernelOnly.PartE.PhiAbove.Leaf00206`.
* `KernelOnly.PartE.PhiAbove.Leaf00207`.
* `KernelOnly.PartE.PhiAbove.Join00208`.
* `KernelOnly.PartE.E24KC6PhiAboveReconstruct`.
* `KernelOnly.PartE.PhiBelow.Leaf00242`.
* `KernelOnly.PartE.PhiBelow.Leaf00243`.
* `KernelOnly.PartE.PhiBelow.Leaf00244`.
* `KernelOnly.PartE.PhiBelow.Leaf00245`.
* `KernelOnly.PartE.PhiBelow.Join00246`.
* `KernelOnly.PartE.PhiBelow.Leaf00256`.
* `KernelOnly.PartE.PhiBelow.Leaf00257`.
* `KernelOnly.PartE.PhiBelow.Leaf00258`.
* `KernelOnly.PartE.PhiBelow.Leaf00259`.
* `KernelOnly.PartE.PhiBelow.Join00260`.
-/

@[expose] public section

noncomputable section

namespace GerverSofa.PartE.CoverCertificate276a139af5

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLH (childLH (childLH (childLH (childLL (childLH (childLH
    (e24PhiAboveRoot))))))))))


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

end GerverSofa.PartE.CoverCertificate276a139af5

namespace GerverSofa.PartE.CoverCertificatee02eecb06a

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLH (childLH (childLH (childLH (childLL (childLH (childLH
    (e24PhiAboveRoot))))))))))


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

end GerverSofa.PartE.CoverCertificatee02eecb06a

namespace GerverSofa.PartE.CoverCertificate783b4cee82

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLH (childLH (childLH (childLH (childLL (childLH (childLH
    (e24PhiAboveRoot))))))))))


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

end GerverSofa.PartE.CoverCertificate783b4cee82

namespace GerverSofa.PartE.CoverCertificate90fa7d5883

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLH (childLH (childLH (childLH (childLL (childLH (childLH
    (e24PhiAboveRoot))))))))))


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

end GerverSofa.PartE.CoverCertificate90fa7d5883

namespace GerverSofa.PartE.CoverCertificate0133fea31e

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLH (childLH (childLH (childLL (childLH (childLH (e24PhiAboveRoot)))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate0133fea31e

namespace GerverSofa.PartE.CoverCertificate3a1ac6bacd

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLH (childLH (childLH (childLL (childLH (childLH (e24PhiAboveRoot)))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate3a1ac6bacd

namespace GerverSofa.PartE.CoverCertificateff206b6a85

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLL (childLL (childLL (childLL (childLH (childLH (childLH
    (e24PhiAboveRoot))))))))))


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

end GerverSofa.PartE.CoverCertificateff206b6a85

namespace GerverSofa.PartE.CoverCertificate71299415d1

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLL (childLL (childLL (childLL (childLH (childLH (childLH
    (e24PhiAboveRoot))))))))))


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

end GerverSofa.PartE.CoverCertificate71299415d1

namespace GerverSofa.PartE.CoverCertificate176775891f

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLL (childLL (childLL (childLL (childLH (childLH (childLH
    (e24PhiAboveRoot))))))))))


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

end GerverSofa.PartE.CoverCertificate176775891f

namespace GerverSofa.PartE.CoverCertificate09737eefc3

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLL (childLL (childLL (childLL (childLH (childLH (childLH
    (e24PhiAboveRoot))))))))))


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

end GerverSofa.PartE.CoverCertificate09737eefc3

namespace GerverSofa.PartE.CoverCertificatea812690e7e

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLL (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificatea812690e7e

namespace GerverSofa.PartE.CoverCertificate35de9fca65

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLL (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate35de9fca65

namespace GerverSofa.PartE.CoverCertificatee6cd0593fa

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLL (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatee6cd0593fa

namespace GerverSofa.PartE.CoverCertificate30c4e37720

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLL (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate30c4e37720

namespace GerverSofa.PartE.CoverCertificatedfaf53edbb

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLL (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificatedfaf53edbb

namespace GerverSofa.PartE.CoverCertificatea7d865eaeb

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLL (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificatea7d865eaeb

namespace GerverSofa.PartE.CoverCertificate59a502ab21

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLL (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificate59a502ab21

namespace GerverSofa.PartE.CoverCertificatedb9da39caf

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLH (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificatedb9da39caf

namespace GerverSofa.PartE.CoverCertificateefd199c221

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLH (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificateefd199c221

namespace GerverSofa.PartE.CoverCertificatedb27ad4afe

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLH (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificatedb27ad4afe

namespace GerverSofa.PartE.CoverCertificate05565992a9

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLH (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificate05565992a9

namespace GerverSofa.PartE.CoverCertificatec7fa9ff5d0

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLH (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificatec7fa9ff5d0

namespace GerverSofa.PartE.CoverCertificatef60369d605

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLH (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificatef60369d605

namespace GerverSofa.PartE.CoverCertificate5759c94c52

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLH (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificate5759c94c52

namespace GerverSofa.PartE.CoverCertificate03a553a361

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLH (childLL (childLL (childLH (childLH (childLH (e24PhiAboveRoot)))))))))


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

end GerverSofa.PartE.CoverCertificate03a553a361

namespace GerverSofa.PartE.CoverCertificated3212f4a8b

private abbrev cellRoot : AngleCell :=
  (childLL (childHH (childLL (childHL (childHH (childHH (e24PhiBelowRoot)))))))


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

end GerverSofa.PartE.CoverCertificated3212f4a8b

namespace GerverSofa.PartE.CoverCertificate92ae3ca2d2

private abbrev cellRoot : AngleCell :=
  (childLH (childHH (childLL (childHL (childHH (childHH (e24PhiBelowRoot)))))))


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


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


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

end GerverSofa.PartE.CoverCertificate92ae3ca2d2

namespace GerverSofa.PartE.CoverCertificate126af0396e

private abbrev cellRoot : AngleCell :=
  (childHL (childHH (childLL (childHL (childHH (childHH (e24PhiBelowRoot)))))))


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

end GerverSofa.PartE.CoverCertificate126af0396e

namespace GerverSofa.PartE.CoverCertificate7a0799a8ec

private abbrev cellRoot : AngleCell :=
  (childHH (childHH (childLL (childHL (childHH (childHH (e24PhiBelowRoot)))))))


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

end GerverSofa.PartE.CoverCertificate7a0799a8ec

namespace GerverSofa.PartE.CoverCertificate0c897fb4ca

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childHL (childHL (childHH (childHH (e24PhiBelowRoot)))))))


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

end GerverSofa.PartE.CoverCertificate0c897fb4ca

namespace GerverSofa.PartE.CoverCertificateac87260947

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHL (childHL (childHH (childHH (e24PhiBelowRoot)))))))


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

end GerverSofa.PartE.CoverCertificateac87260947

namespace GerverSofa.PartE.CoverCertificatee4e72882c5

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHL (childHL (childHH (childHH (e24PhiBelowRoot)))))))


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

end GerverSofa.PartE.CoverCertificatee4e72882c5

namespace GerverSofa.PartE.CoverCertificateeab8fed9d7

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHL (childHL (childHH (childHH (e24PhiBelowRoot)))))))


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

end GerverSofa.PartE.CoverCertificateeab8fed9d7

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101111_c1_c0_7_00161
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells018fd5e668

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011111 : AngleCell :=
  childLH (childLH (childLH (childLH phiAboveCell1101)))

end CertificateCells018fd5e668

open CertificateCells018fd5e668
namespace CoverCertificate276a139af5


















































































private theorem checked000 : adaptiveCoverCheck 4 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 4 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 4 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 4 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 4 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 4 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 4 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 4 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 4 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 4 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 4 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 4 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 4 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 4 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 4 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 4 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 4 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 4 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 4 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 4 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell103 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 4 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 4 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 4 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 4 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 4 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 4 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 4 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 4 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 4 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 4 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 4 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 4 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 4 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 4 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 4 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 4 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 4 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 4 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 4 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 4 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 4 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 4 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 4 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 4 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 4 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 4 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 4 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 4 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 4 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 4 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 4 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 4 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 4 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 4 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 4 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 4 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 4 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 4 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 4 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 4 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 5 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 5 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 5 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 5 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 5 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 5 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 5 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 5 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate276a139af5

theorem e24KC2PhiAboveLeaf1101111_c1_c0 :
    adaptiveCoverCheck 7 (childLL phiAboveCell11011111) = true := by
  exact CoverCertificate276a139af5.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101111_c1_c1_7_00162
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells63f0679649

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011111 : AngleCell :=
  childLH (childLH (childLH (childLH phiAboveCell1101)))

end CertificateCells63f0679649

open CertificateCells63f0679649
namespace CoverCertificatee02eecb06a






































































private theorem checked020 : adaptiveCoverCheck 4 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 4 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 4 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 4 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 4 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 4 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 4 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 4 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell033 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 4 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 4 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 4 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 4 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 4 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 4 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 4 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 4 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 4 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 4 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 4 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 4 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 4 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 4 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 4 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 4 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 4 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 4 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 4 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 4 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 4 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 4 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 4 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 4 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 4 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 4 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 4 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 4 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 4 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 4 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 4 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 4 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 4 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 4 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 4 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 4 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 4 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 4 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 4 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 4 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 5 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 5 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 5 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 5 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 5 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 5 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 5 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 5 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatee02eecb06a

theorem e24KC2PhiAboveLeaf1101111_c1_c1 :
    adaptiveCoverCheck 7 (childLH phiAboveCell11011111) = true := by
  exact CoverCertificatee02eecb06a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101111_c1_c2_7_00163
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa5edf5ee06

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011111 : AngleCell :=
  childLH (childLH (childLH (childLH phiAboveCell1101)))

end CertificateCellsa5edf5ee06

open CertificateCellsa5edf5ee06
namespace CoverCertificate783b4cee82














private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate783b4cee82

theorem e24KC2PhiAboveLeaf1101111_c1_c2 :
    adaptiveCoverCheck 7 (childHL phiAboveCell11011111) = true := by
  exact CoverCertificate783b4cee82.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101111_c1_c3_7_00164
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd0bb651e18

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011111 : AngleCell :=
  childLH (childLH (childLH (childLH phiAboveCell1101)))

end CertificateCellsd0bb651e18

open CertificateCellsd0bb651e18
namespace CoverCertificate90fa7d5883














private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate90fa7d5883

theorem e24KC2PhiAboveLeaf1101111_c1_c3 :
    adaptiveCoverCheck 7 (childHH phiAboveCell11011111) = true := by
  exact CoverCertificate90fa7d5883.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101111_c1_8_00165
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsac583a159d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011111 : AngleCell :=
  childLH (childLH (childLH (childLH phiAboveCell1101)))

end CertificateCellsac583a159d

open CertificateCellsac583a159d

theorem e24KC2PhiAboveLeaf1101111_c1 :
    adaptiveCoverCheck 8 phiAboveCell11011111 = true :=
  adaptiveCoverCheck_succ_of_children 7 phiAboveCell11011111
    e24KC2PhiAboveLeaf1101111_c1_c0 e24KC2PhiAboveLeaf1101111_c1_c1
      e24KC2PhiAboveLeaf1101111_c1_c2 e24KC2PhiAboveLeaf1101111_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101111_c2_8_00166
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells347e84a45d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011112` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011112 : AngleCell :=
  childHL (childLH (childLH (childLH phiAboveCell1101)))

end CertificateCells347e84a45d

open CertificateCells347e84a45d
namespace CoverCertificate0133fea31e






private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate0133fea31e

theorem e24KC2PhiAboveLeaf1101111_c2 :
    adaptiveCoverCheck 8 phiAboveCell11011112 = true := by
  exact CoverCertificate0133fea31e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101111_c3_8_00167
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells06372696b5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011113` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011113 : AngleCell :=
  childHH (childLH (childLH (childLH phiAboveCell1101)))

end CertificateCells06372696b5

open CertificateCells06372696b5
namespace CoverCertificate3a1ac6bacd






private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3a1ac6bacd

theorem e24KC2PhiAboveLeaf1101111_c3 :
    adaptiveCoverCheck 8 phiAboveCell11011113 = true := by
  exact CoverCertificate3a1ac6bacd.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101111_9_00168
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf317a94cb3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

end CertificateCellsf317a94cb3

open CertificateCellsf317a94cb3

theorem e24KC2PhiAboveLeaf1101111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH phiAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLH phiAboveCell1101)))
    e24KC2PhiAboveLeaf1101111_c0 e24KC2PhiAboveLeaf1101111_c1 e24KC2PhiAboveLeaf1101111_c2
      e24KC2PhiAboveLeaf1101111_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110000_c0_c0_7_00174
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdc3bb009fb

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100000 : AngleCell :=
  childLL (childLL (childLL (childLL phiAboveCell1110)))

end CertificateCellsdc3bb009fb

open CertificateCellsdc3bb009fb
namespace CoverCertificateff206b6a85














































private theorem checked020 : adaptiveCoverCheck 4 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 4 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 4 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 4 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 4 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 4 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 4 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 4 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell033 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 4 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 4 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 4 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 4 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 4 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 4 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 4 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 4 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 4 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 4 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 4 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 4 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 4 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 4 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 4 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 4 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell213 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 5 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 5 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 5 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 5 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 5 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 5 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 5 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 5 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateff206b6a85

theorem e24KC2PhiAboveLeaf1110000_c0_c0 :
    adaptiveCoverCheck 7 (childLL phiAboveCell11100000) = true := by
  exact CoverCertificateff206b6a85.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110000_c0_c1_7_00175
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa17c45a931

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100000 : AngleCell :=
  childLL (childLL (childLL (childLL phiAboveCell1110)))

end CertificateCellsa17c45a931

open CertificateCellsa17c45a931
namespace CoverCertificate71299415d1






















private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 5 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 5 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 5 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 5 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 5 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 5 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 5 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 5 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate71299415d1

theorem e24KC2PhiAboveLeaf1110000_c0_c1 :
    adaptiveCoverCheck 7 (childLH phiAboveCell11100000) = true := by
  exact CoverCertificate71299415d1.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110000_c0_c2_7_00176
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells11ac46d6b2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100000 : AngleCell :=
  childLL (childLL (childLL (childLL phiAboveCell1110)))

end CertificateCells11ac46d6b2

open CertificateCells11ac46d6b2
namespace CoverCertificate176775891f














private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate176775891f

theorem e24KC2PhiAboveLeaf1110000_c0_c2 :
    adaptiveCoverCheck 7 (childHL phiAboveCell11100000) = true := by
  exact CoverCertificate176775891f.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110000_c0_c3_7_00177
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4bb3cae3bb

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100000 : AngleCell :=
  childLL (childLL (childLL (childLL phiAboveCell1110)))

end CertificateCells4bb3cae3bb

open CertificateCells4bb3cae3bb
namespace CoverCertificate09737eefc3














private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate09737eefc3

theorem e24KC2PhiAboveLeaf1110000_c0_c3 :
    adaptiveCoverCheck 7 (childHH phiAboveCell11100000) = true := by
  exact CoverCertificate09737eefc3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1110000_c0_8_00178
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf7dce840c8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100000 : AngleCell :=
  childLL (childLL (childLL (childLL phiAboveCell1110)))

end CertificateCellsf7dce840c8

open CertificateCellsf7dce840c8

theorem e24KC2PhiAboveLeaf1110000_c0 :
    adaptiveCoverCheck 8 phiAboveCell11100000 = true :=
  adaptiveCoverCheck_succ_of_children 7 phiAboveCell11100000
    e24KC2PhiAboveLeaf1110000_c0_c0 e24KC2PhiAboveLeaf1110000_c0_c1
      e24KC2PhiAboveLeaf1110000_c0_c2 e24KC2PhiAboveLeaf1110000_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110000_c1_8_00179
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells517a8caf86

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100001` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100001 : AngleCell :=
  childLH (childLL (childLL (childLL phiAboveCell1110)))

end CertificateCells517a8caf86

open CertificateCells517a8caf86
namespace CoverCertificatea812690e7e






































































private theorem checked000 : adaptiveCoverCheck 5 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 5 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 5 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 5 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 5 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 5 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 5 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 5 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 5 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 5 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 5 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 5 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 5 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 5 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 5 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 5 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 5 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 5 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 5 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 5 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 5 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 5 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 5 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 5 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 5 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 5 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 5 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 5 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 5 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 5 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 5 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 5 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 5 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 5 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 5 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 5 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 5 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 5 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 5 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 5 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell213 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 5 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 5 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 5 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 5 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 5 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 5 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 5 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 5 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell313 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea812690e7e

theorem e24KC2PhiAboveLeaf1110000_c1 :
    adaptiveCoverCheck 8 phiAboveCell11100001 = true := by
  exact CoverCertificatea812690e7e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110000_c2_8_00180
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5795a3d5ea

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100002` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100002 : AngleCell :=
  childHL (childLL (childLL (childLL phiAboveCell1110)))

end CertificateCells5795a3d5ea

open CertificateCells5795a3d5ea
namespace CoverCertificate35de9fca65






private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate35de9fca65

theorem e24KC2PhiAboveLeaf1110000_c2 :
    adaptiveCoverCheck 8 phiAboveCell11100002 = true := by
  exact CoverCertificate35de9fca65.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110000_c3_8_00181
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa32d189193

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100003` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100003 : AngleCell :=
  childHH (childLL (childLL (childLL phiAboveCell1110)))

end CertificateCellsa32d189193

open CertificateCellsa32d189193
namespace CoverCertificatee6cd0593fa






private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatee6cd0593fa

theorem e24KC2PhiAboveLeaf1110000_c3 :
    adaptiveCoverCheck 8 phiAboveCell11100003 = true := by
  exact CoverCertificatee6cd0593fa.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1110000_9_00182
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5fe660c4fc

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end CertificateCells5fe660c4fc

open CertificateCells5fe660c4fc

theorem e24KC2PhiAboveLeaf1110000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL phiAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLL phiAboveCell1110)))
    e24KC2PhiAboveLeaf1110000_c0 e24KC2PhiAboveLeaf1110000_c1 e24KC2PhiAboveLeaf1110000_c2
      e24KC2PhiAboveLeaf1110000_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110001_c0_8_00187
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf628113fc1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100010 : AngleCell :=
  childLL (childLH (childLL (childLL phiAboveCell1110)))

end CertificateCellsf628113fc1

open CertificateCellsf628113fc1
namespace CoverCertificate30c4e37720










































































private theorem checked000 : adaptiveCoverCheck 5 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 5 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 5 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 5 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 5 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 5 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 5 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 5 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 5 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 5 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 5 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 5 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 5 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 5 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 5 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 5 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 5 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 5 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 5 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 5 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 5 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 5 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 5 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 5 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 5 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 5 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 5 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 5 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 5 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 5 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 5 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 5 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 5 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 5 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 5 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 5 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 5 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 5 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 5 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 5 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell213 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 5 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 5 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 5 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 5 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 5 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 5 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 5 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 5 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell313 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 5 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 5 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 5 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 5 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate30c4e37720

theorem e24KC2PhiAboveLeaf1110001_c0 :
    adaptiveCoverCheck 8 phiAboveCell11100010 = true := by
  exact CoverCertificate30c4e37720.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110001_c1_8_00188
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells740eeaba32

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100011 : AngleCell :=
  childLH (childLH (childLL (childLL phiAboveCell1110)))

end CertificateCells740eeaba32

open CertificateCells740eeaba32
namespace CoverCertificatedfaf53edbb






















































































private theorem checked000 : adaptiveCoverCheck 5 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 5 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 5 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 5 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 5 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 5 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 5 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 5 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 5 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 5 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 5 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 5 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 5 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 5 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 5 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 5 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 5 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 5 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 5 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 5 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 5 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 5 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 5 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 5 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 5 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 5 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 5 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 5 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 5 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 5 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 5 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 5 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 5 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 5 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 5 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 5 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 5 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 5 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 5 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 5 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 5 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 5 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 5 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 5 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 5 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 5 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 5 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 5 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 5 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 5 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 5 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 5 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 5 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 5 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 5 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 5 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 5 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 5 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 5 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 5 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 5 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 5 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 5 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 5 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatedfaf53edbb

theorem e24KC2PhiAboveLeaf1110001_c1 :
    adaptiveCoverCheck 8 phiAboveCell11100011 = true := by
  exact CoverCertificatedfaf53edbb.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110001_c2_8_00189
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells626f3fc028

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100012` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100012 : AngleCell :=
  childHL (childLH (childLL (childLL phiAboveCell1110)))

end CertificateCells626f3fc028

open CertificateCells626f3fc028
namespace CoverCertificatea7d865eaeb














private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea7d865eaeb

theorem e24KC2PhiAboveLeaf1110001_c2 :
    adaptiveCoverCheck 8 phiAboveCell11100012 = true := by
  exact CoverCertificatea7d865eaeb.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110001_c3_8_00190
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells15f9582e4b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100013` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100013 : AngleCell :=
  childHH (childLH (childLL (childLL phiAboveCell1110)))

end CertificateCells15f9582e4b

open CertificateCells15f9582e4b
namespace CoverCertificate59a502ab21














private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate59a502ab21

theorem e24KC2PhiAboveLeaf1110001_c3 :
    adaptiveCoverCheck 8 phiAboveCell11100013 = true := by
  exact CoverCertificate59a502ab21.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1110001_9_00191
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7e3a6c7b6b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end CertificateCells7e3a6c7b6b

open CertificateCells7e3a6c7b6b

theorem e24KC2PhiAboveLeaf1110001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL phiAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLL phiAboveCell1110)))
    e24KC2PhiAboveLeaf1110001_c0 e24KC2PhiAboveLeaf1110001_c1 e24KC2PhiAboveLeaf1110001_c2
      e24KC2PhiAboveLeaf1110001_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110010_c0_8_00196
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc156062d1b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100100 : AngleCell :=
  childLL (childLL (childLH (childLL phiAboveCell1110)))

end CertificateCellsc156062d1b

open CertificateCellsc156062d1b
namespace CoverCertificatedb9da39caf














































































private theorem checked000 : adaptiveCoverCheck 5 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 5 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 5 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 5 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 5 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 5 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 5 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 5 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 5 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 5 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 5 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 5 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 5 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 5 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 5 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 5 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell033 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 5 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 5 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 5 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 5 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 5 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 5 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 5 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 5 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 5 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 5 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 5 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 5 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 5 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 5 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 5 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 5 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 5 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 5 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 5 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 5 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 5 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 5 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 5 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 5 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 5 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 5 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 5 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 5 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 5 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 5 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 5 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 5 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 5 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 5 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 5 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 5 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 5 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 5 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 5 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 5 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatedb9da39caf

theorem e24KC2PhiAboveLeaf1110010_c0 :
    adaptiveCoverCheck 8 phiAboveCell11100100 = true := by
  exact CoverCertificatedb9da39caf.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110010_c1_8_00197
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdb4a23ce5a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100101 : AngleCell :=
  childLH (childLL (childLH (childLL phiAboveCell1110)))

end CertificateCellsdb4a23ce5a

open CertificateCellsdb4a23ce5a
namespace CoverCertificateefd199c221






































































private theorem checked020 : adaptiveCoverCheck 5 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 5 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 5 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 5 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 5 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 5 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 5 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 5 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell033 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 5 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 5 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 5 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 5 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 5 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 5 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 5 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 5 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 5 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 5 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 5 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 5 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 5 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 5 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 5 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 5 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 5 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 5 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 5 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 5 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 5 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 5 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 5 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 5 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 5 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 5 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 5 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 5 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 5 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 5 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 5 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 5 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 5 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 5 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 5 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 5 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 5 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 5 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 5 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 5 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateefd199c221

theorem e24KC2PhiAboveLeaf1110010_c1 :
    adaptiveCoverCheck 8 phiAboveCell11100101 = true := by
  exact CoverCertificateefd199c221.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110010_c2_8_00198
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8ced9a3143

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100102` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100102 : AngleCell :=
  childHL (childLL (childLH (childLL phiAboveCell1110)))

end CertificateCells8ced9a3143

open CertificateCells8ced9a3143
namespace CoverCertificatedb27ad4afe














private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatedb27ad4afe

theorem e24KC2PhiAboveLeaf1110010_c2 :
    adaptiveCoverCheck 8 phiAboveCell11100102 = true := by
  exact CoverCertificatedb27ad4afe.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110010_c3_8_00199
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1c46ec9a00

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100103` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100103 : AngleCell :=
  childHH (childLL (childLH (childLL phiAboveCell1110)))

end CertificateCells1c46ec9a00

open CertificateCells1c46ec9a00
namespace CoverCertificate05565992a9














private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate05565992a9

theorem e24KC2PhiAboveLeaf1110010_c3 :
    adaptiveCoverCheck 8 phiAboveCell11100103 = true := by
  exact CoverCertificate05565992a9.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1110010_9_00200
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa5efdb03f3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end CertificateCellsa5efdb03f3

open CertificateCellsa5efdb03f3

theorem e24KC2PhiAboveLeaf1110010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL phiAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLL phiAboveCell1110)))
    e24KC2PhiAboveLeaf1110010_c0 e24KC2PhiAboveLeaf1110010_c1 e24KC2PhiAboveLeaf1110010_c2
      e24KC2PhiAboveLeaf1110010_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110011_c0_8_00204
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc9ea34c02b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100110 : AngleCell :=
  childLL (childLH (childLH (childLL phiAboveCell1110)))

end CertificateCellsc9ea34c02b

open CertificateCellsc9ea34c02b
namespace CoverCertificatec7fa9ff5d0






































































private theorem checked020 : adaptiveCoverCheck 5 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 5 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 5 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 5 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 5 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 5 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 5 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 5 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell033 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 5 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 5 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 5 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 5 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 5 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 5 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 5 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 5 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 5 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 5 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 5 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 5 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 5 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 5 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 5 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 5 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 5 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 5 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 5 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 5 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 5 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 5 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 5 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 5 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 5 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 5 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 5 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 5 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 5 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 5 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 5 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 5 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 5 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 5 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 5 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 5 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 5 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 5 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 5 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 5 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec7fa9ff5d0

theorem e24KC2PhiAboveLeaf1110011_c0 :
    adaptiveCoverCheck 8 phiAboveCell11100110 = true := by
  exact CoverCertificatec7fa9ff5d0.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110011_c1_8_00205
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7575776df3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100111 : AngleCell :=
  childLH (childLH (childLH (childLL phiAboveCell1110)))

end CertificateCells7575776df3

open CertificateCells7575776df3
namespace CoverCertificatef60369d605














































private theorem checked020 : adaptiveCoverCheck 5 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 5 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 5 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 5 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 5 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 5 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 5 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 5 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell033 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 5 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 5 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 5 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 5 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 5 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 5 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 5 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 5 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 5 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 5 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 5 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 5 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 5 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 5 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 5 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 5 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell213 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatef60369d605

theorem e24KC2PhiAboveLeaf1110011_c1 :
    adaptiveCoverCheck 8 phiAboveCell11100111 = true := by
  exact CoverCertificatef60369d605.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110011_c2_8_00206
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8b638b7054

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100112` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100112 : AngleCell :=
  childHL (childLH (childLH (childLL phiAboveCell1110)))

end CertificateCells8b638b7054

open CertificateCells8b638b7054
namespace CoverCertificate5759c94c52














private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5759c94c52

theorem e24KC2PhiAboveLeaf1110011_c2 :
    adaptiveCoverCheck 8 phiAboveCell11100112 = true := by
  exact CoverCertificate5759c94c52.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1110011_c3_8_00207
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3bd9cbb8df

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11100113` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11100113 : AngleCell :=
  childHH (childLH (childLH (childLL phiAboveCell1110)))

end CertificateCells3bd9cbb8df

open CertificateCells3bd9cbb8df
namespace CoverCertificate03a553a361














private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate03a553a361

theorem e24KC2PhiAboveLeaf1110011_c3 :
    adaptiveCoverCheck 8 phiAboveCell11100113 = true := by
  exact CoverCertificate03a553a361.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1110011_9_00208
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4f05b2093e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

end CertificateCells4f05b2093e

open CertificateCells4f05b2093e

theorem e24KC2PhiAboveLeaf1110011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL phiAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLL phiAboveCell1110)))
    e24KC2PhiAboveLeaf1110011_c0 e24KC2PhiAboveLeaf1110011_c1 e24KC2PhiAboveLeaf1110011_c2
      e24KC2PhiAboveLeaf1110011_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC6Phi Above Reconstruct
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa15368d7db

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1001` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1001 : AngleCell :=
  childLH (childLL (childLL (childLH e24PhiAboveRoot)))
/-- Subcell `1010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1010 : AngleCell :=
  childLL (childLH (childLL (childLH e24PhiAboveRoot)))
/-- Subcell `1011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1011 : AngleCell :=
  childLH (childLH (childLL (childLH e24PhiAboveRoot)))
/-- Subcell `1100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1100 : AngleCell :=
  childLL (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `1111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `0101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0101 : AngleCell :=
  childLH (childLL (childLH (childLL e24PhiAboveRoot)))
/-- Subcell `0110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0110 : AngleCell :=
  childLL (childLH (childLH (childLL e24PhiAboveRoot)))
/-- Subcell `0111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0111 : AngleCell :=
  childLH (childLH (childLH (childLL e24PhiAboveRoot)))
/-- Subcell `1000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1000 : AngleCell :=
  childLL (childLL (childLL (childLH e24PhiAboveRoot)))
/-- Subcell `0000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24PhiAboveRoot)))
/-- Subcell `0001` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0001 : AngleCell :=
  childLH (childLL (childLL (childLL e24PhiAboveRoot)))
/-- Subcell `0010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0010 : AngleCell :=
  childLL (childLH (childLL (childLL e24PhiAboveRoot)))
/-- Subcell `0011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0011 : AngleCell :=
  childLH (childLH (childLL (childLL e24PhiAboveRoot)))
/-- Subcell `0100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0100 : AngleCell :=
  childLL (childLL (childLH (childLL e24PhiAboveRoot)))
/-- Subcell `1002` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1002 : AngleCell :=
  childHL (childLL (childLL (childLH e24PhiAboveRoot)))
/-- Subcell `1003` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1003 : AngleCell :=
  childHH (childLL (childLL (childLH e24PhiAboveRoot)))
/-- Subcell `1012` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1012 : AngleCell :=
  childHL (childLH (childLL (childLH e24PhiAboveRoot)))
/-- Subcell `1013` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1013 : AngleCell :=
  childHH (childLH (childLL (childLH e24PhiAboveRoot)))
/-- Subcell `1102` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1102 : AngleCell :=
  childHL (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `1103` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1103 : AngleCell :=
  childHH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `1112` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1112 : AngleCell :=
  childHL (childLH (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `1113` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1113 : AngleCell :=
  childHH (childLH (childLH (childLH e24PhiAboveRoot)))

end CertificateCellsa15368d7db

open CertificateCellsa15368d7db

theorem e24KC2PhiAboveNode100101 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1001))
    e24KC2PhiAboveLeaf1001010 e24KC2PhiAboveLeaf1001011 e24KC2PhiAboveLeaf1001012
      e24KC2PhiAboveLeaf1001013

theorem e24KC2PhiAboveNode100110 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1001))
    e24KC2PhiAboveLeaf1001100 e24KC2PhiAboveLeaf1001101 e24KC2PhiAboveLeaf1001102
      e24KC2PhiAboveLeaf1001103

theorem e24KC2PhiAboveNode100111 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1001))
    e24KC2PhiAboveLeaf1001110 e24KC2PhiAboveLeaf1001111 e24KC2PhiAboveLeaf1001112
      e24KC2PhiAboveLeaf1001113

theorem e24KC2PhiAboveNode101000 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1010))
    e24KC2PhiAboveLeaf1010000 e24KC2PhiAboveLeaf1010001 e24KC2PhiAboveLeaf1010002
      e24KC2PhiAboveLeaf1010003

theorem e24KC2PhiAboveNode101001 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1010))
    e24KC2PhiAboveLeaf1010010 e24KC2PhiAboveLeaf1010011 e24KC2PhiAboveLeaf1010012
      e24KC2PhiAboveLeaf1010013

theorem e24KC2PhiAboveNode101010 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1010))
    e24KC2PhiAboveLeaf1010100 e24KC2PhiAboveLeaf1010101 e24KC2PhiAboveLeaf1010102
      e24KC2PhiAboveLeaf1010103

theorem e24KC2PhiAboveNode101011 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1010))
    e24KC2PhiAboveLeaf1010110 e24KC2PhiAboveLeaf1010111 e24KC2PhiAboveLeaf1010112
      e24KC2PhiAboveLeaf1010113

theorem e24KC2PhiAboveNode101100 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1011))
    e24KC2PhiAboveLeaf1011000 e24KC2PhiAboveLeaf1011001 e24KC2PhiAboveLeaf1011002
      e24KC2PhiAboveLeaf1011003

theorem e24KC2PhiAboveNode101101 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1011))
    e24KC2PhiAboveLeaf1011010 e24KC2PhiAboveLeaf1011011 e24KC2PhiAboveLeaf1011012
      e24KC2PhiAboveLeaf1011013

theorem e24KC2PhiAboveNode101110 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1011))
    e24KC2PhiAboveLeaf1011100 e24KC2PhiAboveLeaf1011101 e24KC2PhiAboveLeaf1011102
      e24KC2PhiAboveLeaf1011103

theorem e24KC2PhiAboveNode101111 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1011))
    e24KC2PhiAboveLeaf1011110 e24KC2PhiAboveLeaf1011111 e24KC2PhiAboveLeaf1011112
      e24KC2PhiAboveLeaf1011113

theorem e24KC2PhiAboveNode110000 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1100))
    e24KC2PhiAboveLeaf1100000 e24KC2PhiAboveLeaf1100001 e24KC2PhiAboveLeaf1100002
      e24KC2PhiAboveLeaf1100003

theorem e24KC2PhiAboveNode110001 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1100))
    e24KC2PhiAboveLeaf1100010 e24KC2PhiAboveLeaf1100011 e24KC2PhiAboveLeaf1100012
      e24KC2PhiAboveLeaf1100013

theorem e24KC2PhiAboveNode110010 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1100))
    e24KC2PhiAboveLeaf1100100 e24KC2PhiAboveLeaf1100101 e24KC2PhiAboveLeaf1100102
      e24KC2PhiAboveLeaf1100103

theorem e24KC2PhiAboveNode110011 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1100))
    e24KC2PhiAboveLeaf1100110 e24KC2PhiAboveLeaf1100111 e24KC2PhiAboveLeaf1100112
      e24KC2PhiAboveLeaf1100113

theorem e24KC2PhiAboveNode110013 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH phiAboveCell1100))
    e24KC2PhiAboveLeaf1100130 e24KC2PhiAboveLeaf1100131 e24KC2PhiAboveLeaf1100132
      e24KC2PhiAboveLeaf1100133

theorem e24KC2PhiAboveNode110100 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1101))
    e24KC2PhiAboveLeaf1101000 e24KC2PhiAboveLeaf1101001 e24KC2PhiAboveLeaf1101002
      e24KC2PhiAboveLeaf1101003

theorem e24KC2PhiAboveNode110101 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1101))
    e24KC2PhiAboveLeaf1101010 e24KC2PhiAboveLeaf1101011 e24KC2PhiAboveLeaf1101012
      e24KC2PhiAboveLeaf1101013

theorem e24KC2PhiAboveNode110102 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLL phiAboveCell1101))
    e24KC2PhiAboveLeaf1101020 e24KC2PhiAboveLeaf1101021 e24KC2PhiAboveLeaf1101022
      e24KC2PhiAboveLeaf1101023

theorem e24KC2PhiAboveNode110103 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLL phiAboveCell1101))
    e24KC2PhiAboveLeaf1101030 e24KC2PhiAboveLeaf1101031 e24KC2PhiAboveLeaf1101032
      e24KC2PhiAboveLeaf1101033

theorem e24KC2PhiAboveNode110110 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1101))
    e24KC2PhiAboveLeaf1101100 e24KC2PhiAboveLeaf1101101 e24KC2PhiAboveLeaf1101102
      e24KC2PhiAboveLeaf1101103

theorem e24KC2PhiAboveNode110111 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1101))
    e24KC2PhiAboveLeaf1101110 e24KC2PhiAboveLeaf1101111 e24KC2PhiAboveLeaf1101112
      e24KC2PhiAboveLeaf1101113

theorem e24KC2PhiAboveNode110112 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLH phiAboveCell1101))
    e24KC2PhiAboveLeaf1101120 e24KC2PhiAboveLeaf1101121 e24KC2PhiAboveLeaf1101122
      e24KC2PhiAboveLeaf1101123

theorem e24KC2PhiAboveNode110113 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH phiAboveCell1101))
    e24KC2PhiAboveLeaf1101130 e24KC2PhiAboveLeaf1101131 e24KC2PhiAboveLeaf1101132
      e24KC2PhiAboveLeaf1101133

theorem e24KC2PhiAboveNode111000 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1110))
    e24KC2PhiAboveLeaf1110000 e24KC2PhiAboveLeaf1110001 e24KC2PhiAboveLeaf1110002
      e24KC2PhiAboveLeaf1110003

theorem e24KC2PhiAboveNode111001 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1110))
    e24KC2PhiAboveLeaf1110010 e24KC2PhiAboveLeaf1110011 e24KC2PhiAboveLeaf1110012
      e24KC2PhiAboveLeaf1110013

theorem e24KC2PhiAboveNode111002 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLL phiAboveCell1110))
    e24KC2PhiAboveLeaf1110020 e24KC2PhiAboveLeaf1110021 e24KC2PhiAboveLeaf1110022
      e24KC2PhiAboveLeaf1110023

theorem e24KC2PhiAboveNode111003 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLL phiAboveCell1110))
    e24KC2PhiAboveLeaf1110030 e24KC2PhiAboveLeaf1110031 e24KC2PhiAboveLeaf1110032
      e24KC2PhiAboveLeaf1110033

theorem e24KC2PhiAboveNode111010 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1110))
    e24KC2PhiAboveLeaf1110100 e24KC2PhiAboveLeaf1110101 e24KC2PhiAboveLeaf1110102
      e24KC2PhiAboveLeaf1110103

theorem e24KC2PhiAboveNode111011 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1110))
    e24KC2PhiAboveLeaf1110110 e24KC2PhiAboveLeaf1110111 e24KC2PhiAboveLeaf1110112
      e24KC2PhiAboveLeaf1110113

theorem e24KC2PhiAboveNode111012 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLH phiAboveCell1110))
    e24KC2PhiAboveLeaf1110120 e24KC2PhiAboveLeaf1110121 e24KC2PhiAboveLeaf1110122
      e24KC2PhiAboveLeaf1110123

theorem e24KC2PhiAboveNode111013 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH phiAboveCell1110))
    e24KC2PhiAboveLeaf1110130 e24KC2PhiAboveLeaf1110131 e24KC2PhiAboveLeaf1110132
      e24KC2PhiAboveLeaf1110133

theorem e24KC2PhiAboveNode111100 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL phiAboveCell1111))
    e24KC2PhiAboveLeaf1111000 e24KC2PhiAboveLeaf1111001 e24KC2PhiAboveLeaf1111002
      e24KC2PhiAboveLeaf1111003

theorem e24KC2PhiAboveNode111101 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL phiAboveCell1111))
    e24KC2PhiAboveLeaf1111010 e24KC2PhiAboveLeaf1111011 e24KC2PhiAboveLeaf1111012
      e24KC2PhiAboveLeaf1111013

theorem e24KC2PhiAboveNode111102 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLL phiAboveCell1111))
    e24KC2PhiAboveLeaf1111020 e24KC2PhiAboveLeaf1111021 e24KC2PhiAboveLeaf1111022
      e24KC2PhiAboveLeaf1111023

theorem e24KC2PhiAboveNode111103 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLL phiAboveCell1111))
    e24KC2PhiAboveLeaf1111030 e24KC2PhiAboveLeaf1111031 e24KC2PhiAboveLeaf1111032
      e24KC2PhiAboveLeaf1111033

theorem e24KC2PhiAboveNode111110 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH phiAboveCell1111))
    e24KC2PhiAboveLeaf1111100 e24KC2PhiAboveLeaf1111101 e24KC2PhiAboveLeaf1111102
      e24KC2PhiAboveLeaf1111103

theorem e24KC2PhiAboveNode111111 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH phiAboveCell1111))
    e24KC2PhiAboveLeaf1111110 e24KC2PhiAboveLeaf1111111 e24KC2PhiAboveLeaf1111112
      e24KC2PhiAboveLeaf1111113

theorem e24KC2PhiAboveNode111112 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLH phiAboveCell1111))
    e24KC2PhiAboveLeaf1111120 e24KC2PhiAboveLeaf1111121 e24KC2PhiAboveLeaf1111122
      e24KC2PhiAboveLeaf1111123

theorem e24KC2PhiAboveNode111113 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH phiAboveCell1111))
    e24KC2PhiAboveLeaf1111130 e24KC2PhiAboveLeaf1111131 e24KC2PhiAboveLeaf1111132
      e24KC2PhiAboveLeaf1111133

theorem e24KC2PhiAboveNode01011 :
    adaptiveCoverCheck 11 (childLH phiAboveCell0101) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell0101)
    e24KC2PhiAboveLeaf010110 e24KC2PhiAboveLeaf010111 e24KC2PhiAboveLeaf010112
      e24KC2PhiAboveLeaf010113

theorem e24KC2PhiAboveNode01100 :
    adaptiveCoverCheck 11 (childLL phiAboveCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell0110)
    e24KC2PhiAboveLeaf011000 e24KC2PhiAboveLeaf011001 e24KC2PhiAboveLeaf011002
      e24KC2PhiAboveLeaf011003

theorem e24KC2PhiAboveNode01101 :
    adaptiveCoverCheck 11 (childLH phiAboveCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell0110)
    e24KC2PhiAboveLeaf011010 e24KC2PhiAboveLeaf011011 e24KC2PhiAboveLeaf011012
      e24KC2PhiAboveLeaf011013

theorem e24KC2PhiAboveNode01110 :
    adaptiveCoverCheck 11 (childLL phiAboveCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell0111)
    e24KC2PhiAboveLeaf011100 e24KC2PhiAboveLeaf011101 e24KC2PhiAboveLeaf011102
      e24KC2PhiAboveLeaf011103

theorem e24KC2PhiAboveNode01111 :
    adaptiveCoverCheck 11 (childLH phiAboveCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell0111)
    e24KC2PhiAboveLeaf011110 e24KC2PhiAboveLeaf011111 e24KC2PhiAboveLeaf011112
      e24KC2PhiAboveLeaf011113

theorem e24KC2PhiAboveNode10000 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1000)
    e24KC2PhiAboveLeaf100000 e24KC2PhiAboveLeaf100001 e24KC2PhiAboveLeaf100002
      e24KC2PhiAboveLeaf100003

theorem e24KC2PhiAboveNode10001 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1000)
    e24KC2PhiAboveLeaf100010 e24KC2PhiAboveLeaf100011 e24KC2PhiAboveLeaf100012
      e24KC2PhiAboveLeaf100013

theorem e24KC2PhiAboveNode10010 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1001)
    e24KC2PhiAboveLeaf100100 e24KC2PhiAboveNode100101 e24KC2PhiAboveLeaf100102
      e24KC2PhiAboveLeaf100103

theorem e24KC2PhiAboveNode10011 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1001)
    e24KC2PhiAboveNode100110 e24KC2PhiAboveNode100111 e24KC2PhiAboveLeaf100112
      e24KC2PhiAboveLeaf100113

theorem e24KC2PhiAboveNode10100 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1010)
    e24KC2PhiAboveNode101000 e24KC2PhiAboveNode101001 e24KC2PhiAboveLeaf101002
      e24KC2PhiAboveLeaf101003

theorem e24KC2PhiAboveNode10101 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1010)
    e24KC2PhiAboveNode101010 e24KC2PhiAboveNode101011 e24KC2PhiAboveLeaf101012
      e24KC2PhiAboveLeaf101013

theorem e24KC2PhiAboveNode10110 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1011)
    e24KC2PhiAboveNode101100 e24KC2PhiAboveNode101101 e24KC2PhiAboveLeaf101102
      e24KC2PhiAboveLeaf101103

theorem e24KC2PhiAboveNode10111 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1011)
    e24KC2PhiAboveNode101110 e24KC2PhiAboveNode101111 e24KC2PhiAboveLeaf101112
      e24KC2PhiAboveLeaf101113

theorem e24KC2PhiAboveNode10113 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH phiAboveCell1011)
    e24KC2PhiAboveLeaf101130 e24KC2PhiAboveLeaf101131 e24KC2PhiAboveLeaf101132
      e24KC2PhiAboveLeaf101133

theorem e24KC2PhiAboveNode11000 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1100)
    e24KC2PhiAboveNode110000 e24KC2PhiAboveNode110001 e24KC2PhiAboveLeaf110002
      e24KC2PhiAboveLeaf110003

theorem e24KC2PhiAboveNode11001 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1100)
    e24KC2PhiAboveNode110010 e24KC2PhiAboveNode110011 e24KC2PhiAboveLeaf110012
      e24KC2PhiAboveNode110013

theorem e24KC2PhiAboveNode11002 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL phiAboveCell1100)
    e24KC2PhiAboveLeaf110020 e24KC2PhiAboveLeaf110021 e24KC2PhiAboveLeaf110022
      e24KC2PhiAboveLeaf110023

theorem e24KC2PhiAboveNode11003 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH phiAboveCell1100)
    e24KC2PhiAboveLeaf110030 e24KC2PhiAboveLeaf110031 e24KC2PhiAboveLeaf110032
      e24KC2PhiAboveLeaf110033

theorem e24KC2PhiAboveNode11010 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1101)
    e24KC2PhiAboveNode110100 e24KC2PhiAboveNode110101 e24KC2PhiAboveNode110102
      e24KC2PhiAboveNode110103

theorem e24KC2PhiAboveNode11011 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1101)
    e24KC2PhiAboveNode110110 e24KC2PhiAboveNode110111 e24KC2PhiAboveNode110112
      e24KC2PhiAboveNode110113

theorem e24KC2PhiAboveNode11012 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL phiAboveCell1101)
    e24KC2PhiAboveLeaf110120 e24KC2PhiAboveLeaf110121 e24KC2PhiAboveLeaf110122
      e24KC2PhiAboveLeaf110123

theorem e24KC2PhiAboveNode11013 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH phiAboveCell1101)
    e24KC2PhiAboveLeaf110130 e24KC2PhiAboveLeaf110131 e24KC2PhiAboveLeaf110132
      e24KC2PhiAboveLeaf110133

theorem e24KC2PhiAboveNode11100 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1110)
    e24KC2PhiAboveNode111000 e24KC2PhiAboveNode111001 e24KC2PhiAboveNode111002
      e24KC2PhiAboveNode111003

theorem e24KC2PhiAboveNode11101 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1110)
    e24KC2PhiAboveNode111010 e24KC2PhiAboveNode111011 e24KC2PhiAboveNode111012
      e24KC2PhiAboveNode111013

theorem e24KC2PhiAboveNode11102 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL phiAboveCell1110)
    e24KC2PhiAboveLeaf111020 e24KC2PhiAboveLeaf111021 e24KC2PhiAboveLeaf111022
      e24KC2PhiAboveLeaf111023

theorem e24KC2PhiAboveNode11103 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH phiAboveCell1110)
    e24KC2PhiAboveLeaf111030 e24KC2PhiAboveLeaf111031 e24KC2PhiAboveLeaf111032
      e24KC2PhiAboveLeaf111033

theorem e24KC2PhiAboveNode11110 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL phiAboveCell1111)
    e24KC2PhiAboveNode111100 e24KC2PhiAboveNode111101 e24KC2PhiAboveNode111102
      e24KC2PhiAboveNode111103

theorem e24KC2PhiAboveNode11111 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH phiAboveCell1111)
    e24KC2PhiAboveNode111110 e24KC2PhiAboveNode111111 e24KC2PhiAboveNode111112
      e24KC2PhiAboveNode111113

theorem e24KC2PhiAboveNode11112 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL phiAboveCell1111)
    e24KC2PhiAboveLeaf111120 e24KC2PhiAboveLeaf111121 e24KC2PhiAboveLeaf111122
      e24KC2PhiAboveLeaf111123

theorem e24KC2PhiAboveNode11113 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH phiAboveCell1111)
    e24KC2PhiAboveLeaf111130 e24KC2PhiAboveLeaf111131 e24KC2PhiAboveLeaf111132
      e24KC2PhiAboveLeaf111133

theorem e24KC2PhiAboveNode0000 :
    adaptiveCoverCheck 12 phiAboveCell0000 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0000
    e24KC2PhiAboveLeaf00000 e24KC2PhiAboveLeaf00001 e24KC2PhiAboveLeaf00002 e24KC2PhiAboveLeaf00003

theorem e24KC2PhiAboveNode0001 :
    adaptiveCoverCheck 12 phiAboveCell0001 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0001
    e24KC2PhiAboveLeaf00010 e24KC2PhiAboveLeaf00011 e24KC2PhiAboveLeaf00012 e24KC2PhiAboveLeaf00013

theorem e24KC2PhiAboveNode0010 :
    adaptiveCoverCheck 12 phiAboveCell0010 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0010
    e24KC2PhiAboveLeaf00100 e24KC2PhiAboveLeaf00101 e24KC2PhiAboveLeaf00102 e24KC2PhiAboveLeaf00103

theorem e24KC2PhiAboveNode0011 :
    adaptiveCoverCheck 12 phiAboveCell0011 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0011
    e24KC2PhiAboveLeaf00110 e24KC2PhiAboveLeaf00111 e24KC2PhiAboveLeaf00112 e24KC2PhiAboveLeaf00113

theorem e24KC2PhiAboveNode0100 :
    adaptiveCoverCheck 12 phiAboveCell0100 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0100
    e24KC2PhiAboveLeaf01000 e24KC2PhiAboveLeaf01001 e24KC2PhiAboveLeaf01002 e24KC2PhiAboveLeaf01003

theorem e24KC2PhiAboveNode0101 :
    adaptiveCoverCheck 12 phiAboveCell0101 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0101
    e24KC2PhiAboveLeaf01010 e24KC2PhiAboveNode01011 e24KC2PhiAboveLeaf01012 e24KC2PhiAboveLeaf01013

theorem e24KC2PhiAboveNode0110 :
    adaptiveCoverCheck 12 phiAboveCell0110 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0110
    e24KC2PhiAboveNode01100 e24KC2PhiAboveNode01101 e24KC2PhiAboveLeaf01102 e24KC2PhiAboveLeaf01103

theorem e24KC2PhiAboveNode0111 :
    adaptiveCoverCheck 12 phiAboveCell0111 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell0111
    e24KC2PhiAboveNode01110 e24KC2PhiAboveNode01111 e24KC2PhiAboveLeaf01112 e24KC2PhiAboveLeaf01113

theorem e24KC2PhiAboveNode1000 :
    adaptiveCoverCheck 12 phiAboveCell1000 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1000
    e24KC2PhiAboveNode10000 e24KC2PhiAboveNode10001 e24KC2PhiAboveLeaf10002 e24KC2PhiAboveLeaf10003

theorem e24KC2PhiAboveNode1001 :
    adaptiveCoverCheck 12 phiAboveCell1001 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1001
    e24KC2PhiAboveNode10010 e24KC2PhiAboveNode10011 e24KC2PhiAboveLeaf10012 e24KC2PhiAboveLeaf10013

theorem e24KC2PhiAboveNode1002 :
    adaptiveCoverCheck 12 phiAboveCell1002 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1002
    e24KC2PhiAboveLeaf10020 e24KC2PhiAboveLeaf10021 e24KC2PhiAboveLeaf10022 e24KC2PhiAboveLeaf10023

theorem e24KC2PhiAboveNode1003 :
    adaptiveCoverCheck 12 phiAboveCell1003 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1003
    e24KC2PhiAboveLeaf10030 e24KC2PhiAboveLeaf10031 e24KC2PhiAboveLeaf10032 e24KC2PhiAboveLeaf10033

theorem e24KC2PhiAboveNode1010 :
    adaptiveCoverCheck 12 phiAboveCell1010 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1010
    e24KC2PhiAboveNode10100 e24KC2PhiAboveNode10101 e24KC2PhiAboveLeaf10102 e24KC2PhiAboveLeaf10103

theorem e24KC2PhiAboveNode1011 :
    adaptiveCoverCheck 12 phiAboveCell1011 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1011
    e24KC2PhiAboveNode10110 e24KC2PhiAboveNode10111 e24KC2PhiAboveLeaf10112 e24KC2PhiAboveNode10113

theorem e24KC2PhiAboveNode1012 :
    adaptiveCoverCheck 12 phiAboveCell1012 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1012
    e24KC2PhiAboveLeaf10120 e24KC2PhiAboveLeaf10121 e24KC2PhiAboveLeaf10122 e24KC2PhiAboveLeaf10123

theorem e24KC2PhiAboveNode1013 :
    adaptiveCoverCheck 12 phiAboveCell1013 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1013
    e24KC2PhiAboveLeaf10130 e24KC2PhiAboveLeaf10131 e24KC2PhiAboveLeaf10132 e24KC2PhiAboveLeaf10133

theorem e24KC2PhiAboveNode1100 :
    adaptiveCoverCheck 12 phiAboveCell1100 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1100
    e24KC2PhiAboveNode11000 e24KC2PhiAboveNode11001 e24KC2PhiAboveNode11002 e24KC2PhiAboveNode11003

theorem e24KC2PhiAboveNode1101 :
    adaptiveCoverCheck 12 phiAboveCell1101 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1101
    e24KC2PhiAboveNode11010 e24KC2PhiAboveNode11011 e24KC2PhiAboveNode11012 e24KC2PhiAboveNode11013

theorem e24KC2PhiAboveNode1102 :
    adaptiveCoverCheck 12 phiAboveCell1102 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1102
    e24KC2PhiAboveLeaf11020 e24KC2PhiAboveLeaf11021 e24KC2PhiAboveLeaf11022 e24KC2PhiAboveLeaf11023

theorem e24KC2PhiAboveNode1103 :
    adaptiveCoverCheck 12 phiAboveCell1103 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1103
    e24KC2PhiAboveLeaf11030 e24KC2PhiAboveLeaf11031 e24KC2PhiAboveLeaf11032 e24KC2PhiAboveLeaf11033

theorem e24KC2PhiAboveNode1110 :
    adaptiveCoverCheck 12 phiAboveCell1110 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1110
    e24KC2PhiAboveNode11100 e24KC2PhiAboveNode11101 e24KC2PhiAboveNode11102 e24KC2PhiAboveNode11103

theorem e24KC2PhiAboveNode1111 :
    adaptiveCoverCheck 12 phiAboveCell1111 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1111
    e24KC2PhiAboveNode11110 e24KC2PhiAboveNode11111 e24KC2PhiAboveNode11112 e24KC2PhiAboveNode11113

theorem e24KC2PhiAboveNode1112 :
    adaptiveCoverCheck 12 phiAboveCell1112 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1112
    e24KC2PhiAboveLeaf11120 e24KC2PhiAboveLeaf11121 e24KC2PhiAboveLeaf11122 e24KC2PhiAboveLeaf11123

theorem e24KC2PhiAboveNode1113 :
    adaptiveCoverCheck 12 phiAboveCell1113 = true :=
  adaptiveCoverCheck_succ_of_children 11 phiAboveCell1113
    e24KC2PhiAboveLeaf11130 e24KC2PhiAboveLeaf11131 e24KC2PhiAboveLeaf11132 e24KC2PhiAboveLeaf11133

theorem e24KC2PhiAboveNode000 :
    adaptiveCoverCheck 13 (childLL (childLL (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0000 e24KC2PhiAboveNode0001 e24KC2PhiAboveLeaf0002 e24KC2PhiAboveLeaf0003

theorem e24KC2PhiAboveNode001 :
    adaptiveCoverCheck 13 (childLH (childLL (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0010 e24KC2PhiAboveNode0011 e24KC2PhiAboveLeaf0012 e24KC2PhiAboveLeaf0013

theorem e24KC2PhiAboveNode003 :
    adaptiveCoverCheck 13 (childHH (childLL (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLL (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf0030 e24KC2PhiAboveLeaf0031 e24KC2PhiAboveLeaf0032 e24KC2PhiAboveLeaf0033

theorem e24KC2PhiAboveNode010 :
    adaptiveCoverCheck 13 (childLL (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0100 e24KC2PhiAboveNode0101 e24KC2PhiAboveLeaf0102 e24KC2PhiAboveLeaf0103

theorem e24KC2PhiAboveNode011 :
    adaptiveCoverCheck 13 (childLH (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0110 e24KC2PhiAboveNode0111 e24KC2PhiAboveLeaf0112 e24KC2PhiAboveLeaf0113

theorem e24KC2PhiAboveNode012 :
    adaptiveCoverCheck 13 (childHL (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf0120 e24KC2PhiAboveLeaf0121 e24KC2PhiAboveLeaf0122 e24KC2PhiAboveLeaf0123

theorem e24KC2PhiAboveNode013 :
    adaptiveCoverCheck 13 (childHH (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf0130 e24KC2PhiAboveLeaf0131 e24KC2PhiAboveLeaf0132 e24KC2PhiAboveLeaf0133

theorem e24KC2PhiAboveNode100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1000 e24KC2PhiAboveNode1001 e24KC2PhiAboveNode1002 e24KC2PhiAboveNode1003

theorem e24KC2PhiAboveNode101 :
    adaptiveCoverCheck 13 (childLH (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1010 e24KC2PhiAboveNode1011 e24KC2PhiAboveNode1012 e24KC2PhiAboveNode1013

theorem e24KC2PhiAboveNode102 :
    adaptiveCoverCheck 13 (childHL (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1020 e24KC2PhiAboveLeaf1021 e24KC2PhiAboveLeaf1022 e24KC2PhiAboveLeaf1023

theorem e24KC2PhiAboveNode103 :
    adaptiveCoverCheck 13 (childHH (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1030 e24KC2PhiAboveLeaf1031 e24KC2PhiAboveLeaf1032 e24KC2PhiAboveLeaf1033

theorem e24KC2PhiAboveNode110 :
    adaptiveCoverCheck 13 (childLL (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1100 e24KC2PhiAboveNode1101 e24KC2PhiAboveNode1102 e24KC2PhiAboveNode1103

theorem e24KC2PhiAboveNode111 :
    adaptiveCoverCheck 13 (childLH (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1110 e24KC2PhiAboveNode1111 e24KC2PhiAboveNode1112 e24KC2PhiAboveNode1113

theorem e24KC2PhiAboveNode112 :
    adaptiveCoverCheck 13 (childHL (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1120 e24KC2PhiAboveLeaf1121 e24KC2PhiAboveLeaf1122 e24KC2PhiAboveLeaf1123

theorem e24KC2PhiAboveNode113 :
    adaptiveCoverCheck 13 (childHH (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1130 e24KC2PhiAboveLeaf1131 e24KC2PhiAboveLeaf1132 e24KC2PhiAboveLeaf1133

theorem e24KC2PhiAboveNode00 :
    adaptiveCoverCheck 14 (childLL (childLL e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL (childLL e24PhiAboveRoot))
    e24KC2PhiAboveNode000 e24KC2PhiAboveNode001 e24KC2PhiAboveLeaf002 e24KC2PhiAboveNode003

theorem e24KC2PhiAboveNode01 :
    adaptiveCoverCheck 14 (childLH (childLL e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH (childLL e24PhiAboveRoot))
    e24KC2PhiAboveNode010 e24KC2PhiAboveNode011 e24KC2PhiAboveNode012 e24KC2PhiAboveNode013

theorem e24KC2PhiAboveNode03 :
    adaptiveCoverCheck 14 (childHH (childLL e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH (childLL e24PhiAboveRoot))
    e24KC2PhiAboveLeaf030 e24KC2PhiAboveLeaf031 e24KC2PhiAboveLeaf032 e24KC2PhiAboveLeaf033

theorem e24KC2PhiAboveNode10 :
    adaptiveCoverCheck 14 (childLL (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL (childLH e24PhiAboveRoot))
    e24KC2PhiAboveNode100 e24KC2PhiAboveNode101 e24KC2PhiAboveNode102 e24KC2PhiAboveNode103

theorem e24KC2PhiAboveNode11 :
    adaptiveCoverCheck 14 (childLH (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH (childLH e24PhiAboveRoot))
    e24KC2PhiAboveNode110 e24KC2PhiAboveNode111 e24KC2PhiAboveNode112 e24KC2PhiAboveNode113

theorem e24KC2PhiAboveNode12 :
    adaptiveCoverCheck 14 (childHL (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL (childLH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf120 e24KC2PhiAboveLeaf121 e24KC2PhiAboveLeaf122 e24KC2PhiAboveLeaf123

theorem e24KC2PhiAboveNode13 :
    adaptiveCoverCheck 14 (childHH (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH (childLH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf130 e24KC2PhiAboveLeaf131 e24KC2PhiAboveLeaf132 e24KC2PhiAboveLeaf133

theorem e24KC2PhiAboveNode30 :
    adaptiveCoverCheck 14 (childLL (childHH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL (childHH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf300 e24KC2PhiAboveLeaf301 e24KC2PhiAboveLeaf302 e24KC2PhiAboveLeaf303

theorem e24KC2PhiAboveNode31 :
    adaptiveCoverCheck 14 (childLH (childHH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH (childHH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf310 e24KC2PhiAboveLeaf311 e24KC2PhiAboveLeaf312 e24KC2PhiAboveLeaf313

theorem e24KC2PhiAboveNode33 :
    adaptiveCoverCheck 14 (childHH (childHH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH (childHH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf330 e24KC2PhiAboveLeaf331 e24KC2PhiAboveLeaf332 e24KC2PhiAboveLeaf333

theorem e24KC2PhiAboveNode0 :
    adaptiveCoverCheck 15 (childLL e24PhiAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL e24PhiAboveRoot)
    e24KC2PhiAboveNode00 e24KC2PhiAboveNode01 e24KC2PhiAboveLeaf02 e24KC2PhiAboveNode03

theorem e24KC2PhiAboveNode1 :
    adaptiveCoverCheck 15 (childLH e24PhiAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH e24PhiAboveRoot)
    e24KC2PhiAboveNode10 e24KC2PhiAboveNode11 e24KC2PhiAboveNode12 e24KC2PhiAboveNode13

theorem e24KC2PhiAboveNode3 :
    adaptiveCoverCheck 15 (childHH e24PhiAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHH e24PhiAboveRoot)
    e24KC2PhiAboveNode30 e24KC2PhiAboveNode31 e24KC2PhiAboveLeaf32 e24KC2PhiAboveNode33

theorem e24KC2PhiAboveNodeROOT :
    adaptiveCoverCheck 16 e24PhiAboveRoot = true :=
  adaptiveCoverCheck_succ_of_children 15 e24PhiAboveRoot
    e24KC2PhiAboveNode0 e24KC2PhiAboveNode1 e24KC2PhiAboveLeaf2 e24KC2PhiAboveNode3

theorem e24PhiAboveKernelCheck :
    adaptiveCoverCheck 16 e24PhiAboveRoot = true :=
  e24KC2PhiAboveNodeROOT

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33203_c0_8_00242
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells41c704a1f1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3320` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3320 : AngleCell :=
  childLL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells41c704a1f1

open CertificateCells41c704a1f1
namespace CoverCertificated3212f4a8b






















private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated3212f4a8b

theorem e24KC2PhiBelowLeaf33203_c0 :
    adaptiveCoverCheck 8 (childLL (childHH phiBelowCell3320)) = true := by
  exact CoverCertificated3212f4a8b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33203_c1_8_00243
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells67d940c92a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3320` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3320 : AngleCell :=
  childLL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells67d940c92a

open CertificateCells67d940c92a
namespace CoverCertificate92ae3ca2d2


































private theorem checked300 : adaptiveCoverCheck 5 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 5 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 5 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 5 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell303 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 5 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 5 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 5 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 5 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 5 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 5 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 5 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 5 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate92ae3ca2d2

theorem e24KC2PhiBelowLeaf33203_c1 :
    adaptiveCoverCheck 8 (childLH (childHH phiBelowCell3320)) = true := by
  exact CoverCertificate92ae3ca2d2.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33203_c2_8_00244
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8d68909634

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3320` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3320 : AngleCell :=
  childLL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells8d68909634

open CertificateCells8d68909634
namespace CoverCertificate126af0396e






















private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate126af0396e

theorem e24KC2PhiBelowLeaf33203_c2 :
    adaptiveCoverCheck 8 (childHL (childHH phiBelowCell3320)) = true := by
  exact CoverCertificate126af0396e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33203_c3_8_00245
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc208943a95

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3320` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3320 : AngleCell :=
  childLL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCellsc208943a95

open CertificateCellsc208943a95
namespace CoverCertificate7a0799a8ec






















































private theorem checked100 : adaptiveCoverCheck 5 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 5 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 5 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 5 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 5 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 5 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 5 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 5 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 5 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 5 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 5 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 5 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 5 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 5 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 5 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 5 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell133 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 5 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 5 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 5 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 5 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 5 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 5 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 5 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 5 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 5 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 5 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 5 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 5 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 5 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 5 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 5 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 5 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate7a0799a8ec

theorem e24KC2PhiBelowLeaf33203_c3 :
    adaptiveCoverCheck 8 (childHH (childHH phiBelowCell3320)) = true := by
  exact CoverCertificate7a0799a8ec.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33203_9_00246
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells12ecbb1984

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3320` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3320 : AngleCell :=
  childLL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells12ecbb1984

open CertificateCells12ecbb1984

theorem e24KC2PhiBelowLeaf33203 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3320) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childHH phiBelowCell3320)
    e24KC2PhiBelowLeaf33203_c0 e24KC2PhiBelowLeaf33203_c1 e24KC2PhiBelowLeaf33203_c2
      e24KC2PhiBelowLeaf33203_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33221_c0_8_00256
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells42a66228ec

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3322` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3322 : AngleCell :=
  childHL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells42a66228ec

open CertificateCells42a66228ec
namespace CoverCertificate0c897fb4ca






















private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate0c897fb4ca

theorem e24KC2PhiBelowLeaf33221_c0 :
    adaptiveCoverCheck 8 (childLL (childLH phiBelowCell3322)) = true := by
  exact CoverCertificate0c897fb4ca.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33221_c1_8_00257
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells67af310b24

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3322` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3322 : AngleCell :=
  childHL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells67af310b24

open CertificateCells67af310b24
namespace CoverCertificateac87260947






























































private theorem checked100 : adaptiveCoverCheck 5 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 5 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 5 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 5 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 5 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 5 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 5 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 5 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 5 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 5 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 5 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 5 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 5 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 5 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 5 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 5 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell133 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 5 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 5 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 5 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 5 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell213 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 5 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 5 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 5 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 5 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 5 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 5 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 5 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 5 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 5 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 5 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 5 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 5 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 5 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 5 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 5 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 5 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 5 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 5 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 5 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 5 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateac87260947

theorem e24KC2PhiBelowLeaf33221_c1 :
    adaptiveCoverCheck 8 (childLH (childLH phiBelowCell3322)) = true := by
  exact CoverCertificateac87260947.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33221_c2_8_00258
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9b91503b21

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3322` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3322 : AngleCell :=
  childHL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells9b91503b21

open CertificateCells9b91503b21
namespace CoverCertificatee4e72882c5






















private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatee4e72882c5

theorem e24KC2PhiBelowLeaf33221_c2 :
    adaptiveCoverCheck 8 (childHL (childLH phiBelowCell3322)) = true := by
  exact CoverCertificatee4e72882c5.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33221_c3_8_00259
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb36cfca8f0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3322` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3322 : AngleCell :=
  childHL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCellsb36cfca8f0

open CertificateCellsb36cfca8f0
namespace CoverCertificateeab8fed9d7






































































private theorem checked010 : adaptiveCoverCheck 5 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 5 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 5 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 5 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell013 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 5 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 5 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 5 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 5 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 5 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 5 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 5 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 5 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 5 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 5 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 5 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 5 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 5 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 5 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 5 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 5 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 5 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 5 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 5 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 5 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell133 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 5 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 5 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 5 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 5 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell213 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 5 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 5 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 5 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 5 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 5 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 5 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 5 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 5 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 5 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 5 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 5 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 5 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 5 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 5 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 5 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 5 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 5 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 5 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 5 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 5 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateeab8fed9d7

theorem e24KC2PhiBelowLeaf33221_c3 :
    adaptiveCoverCheck 8 (childHH (childLH phiBelowCell3322)) = true := by
  exact CoverCertificateeab8fed9d7.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33221_9_00260
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf9b1d22c2c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3322` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3322 : AngleCell :=
  childHL (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCellsf9b1d22c2c

open CertificateCellsf9b1d22c2c

theorem e24KC2PhiBelowLeaf33221 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3322) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH phiBelowCell3322)
    e24KC2PhiBelowLeaf33221_c0 e24KC2PhiBelowLeaf33221_c1 e24KC2PhiBelowLeaf33221_c2
      e24KC2PhiBelowLeaf33221_c3

end PartE
end GerverSofa

end

end

end
