import FleetSignUncertaintyData

/-! Descartes-leaf positivity certificates for `Q`, part 1 (kernel evaluation, natural numbers only). -/

namespace FleetSignUncertainty

theorem sigLeaves0 : leavesOK (scaleUpN 4096 sigP) (scaleUpN 4096 sigN) 7887
    [(7887, 1176)]
    9063 = true := by decide +kernel

theorem sigLeaves1 : leavesOK (scaleUpN 4096 sigP) (scaleUpN 4096 sigN) 9063
    [(9063, 588)]
    9651 = true := by decide +kernel

theorem sigLeaves2 : leavesOK (scaleUpN 4096 sigP) (scaleUpN 4096 sigN) 9651
    [(9651, 589)]
    10240 = true := by decide +kernel

theorem sigLeaves3 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 40
    [(40, 7)]
    47 = true := by decide +kernel

theorem sigLeaves4 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 47
    [(47, 8)]
    55 = true := by decide +kernel

theorem sigLeaves5 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 55
    [(55, 16)]
    71 = true := by decide +kernel

theorem sigLeaves6 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 71
    [(71, 16)]
    87 = true := by decide +kernel

theorem sigLeaves7 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 87
    [(87, 16)]
    103 = true := by decide +kernel

theorem sigLeaves8 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 103
    [(103, 3)]
    106 = true := by decide +kernel

theorem sigLeaves9 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 106
    [(106, 4)]
    110 = true := by decide +kernel

theorem sigLeaves10 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 110
    [(110, 8)]
    118 = true := by decide +kernel

theorem sigLeaves11 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 118
    [(118, 16)]
    134 = true := by decide +kernel

theorem sigLeaves12 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 134
    [(134, 32)]
    166 = true := by decide +kernel

theorem sigLeaves13 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 166
    [(166, 126)]
    292 = true := by decide +kernel

theorem sigLeaves14 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 292
    [(292, 126)]
    418 = true := by decide +kernel

theorem sigLeaves15 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 418
    [(418, 31)]
    449 = true := by decide +kernel

end FleetSignUncertainty
