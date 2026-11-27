import FleetSignUncertaintyData

/-! Descartes-leaf positivity certificates for `Q`, part 2 (kernel evaluation, natural numbers only). -/

namespace FleetSignUncertainty

theorem sigLeaves16 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 449
    [(449, 16)]
    465 = true := by decide +kernel

theorem sigLeaves17 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 465
    [(465, 8)]
    473 = true := by decide +kernel

theorem sigLeaves18 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 473
    [(473, 8)]
    481 = true := by decide +kernel

theorem sigLeaves19 : leavesOK (scaleUpN 16 sigP) (scaleUpN 16 sigN) 481
    [(481, 63)]
    544 = true := by decide +kernel

theorem sigLeaves20 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 34
    [(34, 15)]
    49 = true := by decide +kernel

theorem sigLeaves21 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 49
    [(49, 8)]
    57 = true := by decide +kernel

theorem sigLeaves22 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 57
    [(57, 8)]
    65 = true := by decide +kernel

theorem sigLeaves23 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 65
    [(65, 16)]
    81 = true := by decide +kernel

theorem sigLeaves24 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 81
    [(81, 16)]
    97 = true := by decide +kernel

theorem sigLeaves25 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 97
    [(97, 16)]
    113 = true := by decide +kernel

theorem sigLeaves26 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 113
    [(113, 16)]
    129 = true := by decide +kernel

theorem sigLeaves27 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 129
    [(129, 16)]
    145 = true := by decide +kernel

theorem sigLeaves28 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 145
    [(145, 8)]
    153 = true := by decide +kernel

theorem sigLeaves29 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 153
    [(153, 8)]
    161 = true := by decide +kernel

theorem sigLeaves30 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 161
    [(161, 32)]
    193 = true := by decide +kernel

theorem sigLeaves31 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 193
    [(193, 32)]
    225 = true := by decide +kernel

end FleetSignUncertainty
